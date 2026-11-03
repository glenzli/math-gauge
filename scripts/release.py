#!/usr/bin/env python3
"""Deterministic downloadable task releases; never invokes candidate models.

The shared harness owns candidate projection and runtime freezing. This module
owns only the archive boundary, source provenance and reproducible release
anchor. A source checkout and evaluator sidecars are never release payloads.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import unicodedata
import zipfile


ROOT = Path(__file__).resolve().parents[1]
VERSION = "0.3.0"
LEGACY_VERSION = "0.1.0"
ARCHIVE_SCHEMA = "math-gauge.release-archive/v1"
PROVENANCE_SCHEMA = "math-gauge.release-provenance/v2"
WRAPPERS = {"README.md", "LICENSE", "THIRD_PARTY_NOTICES.md"}
ARCHIVE_KEYS = {
    "schema", "release_version", "suite", "dataset_sha256", "base_plan_sha256",
    "source", "public_development_suite", "case_count", "slot_count",
    "candidate_calls", "runtime_frozen", "input_bindings", "source_files_sha256",
    "files_sha256",
}
ZIP_TIME = (1980, 1, 1, 0, 0, 0)


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _digest(raw):
    return hashlib.sha256(raw).hexdigest()


def _json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2,
                       allow_nan=False) + "\n").encode("utf-8")


def _read_json(raw):
    def pairs(items):
        value = {}
        for key, item in items:
            _require(key not in value, "Duplicate JSON field")
            value[key] = item
        return value

    def invalid(_):
        raise ValueError("Non-finite JSON number")

    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                      parse_constant=invalid)


def _relative(name):
    _require(isinstance(name, str) and name and "\\" not in name
             and "\0" not in name and ":" not in name, "Unsafe release path")
    name.encode("utf-8", "strict")
    path = PurePosixPath(name)
    _require(path.parts and not path.is_absolute() and str(path) == name
             and all(p not in {".", "..", ""} for p in path.parts),
             "Unsafe release path")
    _require(all(not p.endswith((".", " "))
                 and not any(ord(c) < 32 or c in '<>"|?*' for c in p)
                 and re.fullmatch(r"CON|PRN|AUX|NUL|CONIN\$|CONOUT\$|COM[1-9¹²³]|LPT[1-9¹²³]",
                                  p.split(".", 1)[0].rstrip(" ."), re.IGNORECASE) is None
                 for p in path.parts),
             "Unsafe cross-platform release path")
    return path


def _real_path(value):
    path = Path(value).expanduser().absolute()
    for name in ("tmp", "var"):
        alias = Path("/") / name
        if (path.is_relative_to(alias) and alias.is_symlink()
                and alias.resolve() == Path("/private") / name):
            path = Path("/private") / name / path.relative_to(alias)
    _require(all(not p.is_symlink() for p in (path, *path.parents)),
             "Release paths cannot pass through symlinks")
    return path.resolve()


def _file(root, name):
    path = root.joinpath(*_relative(name).parts)
    _require(all(not p.is_symlink() for p in (path, *path.parents)),
             "Symlinks are not permitted in a release")
    _require(path.is_file() and path.resolve().is_relative_to(root),
             "Missing release file: " + name)
    return path


def load_config(root=ROOT, version=VERSION):
    _require(re.fullmatch(r"\d+\.\d+\.\d+", version) is not None,
             "Invalid release version")
    root = _real_path(root)
    config = _read_json(_file(root, f"releases/v{version}/config.json").read_bytes())
    _require(set(config) == {"schema", "release_version", "suite_version", "repository",
                            "case_count", "slot_count", "plan_id", "created_at",
                            "readme", "third_party_notices"}
             and config["schema"] in {"math-gauge.release-config/v1", "math-gauge.release-config/v2",
                                      "math-gauge.release-config/v3"}
             and config["release_version"] == version,
             "Unsupported release configuration")
    if config["schema"] != "math-gauge.release-config/v1":
        _require(config["release_version"] == config["suite_version"],
                 "Release version must equal the suite version")
    _require(type(config["case_count"]) is int and config["case_count"] > 0
             and type(config["slot_count"]) is int and config["slot_count"] > 0
             and re.fullmatch(r"[0-9a-f]{32}", config["plan_id"]) is not None
             and isinstance(config["created_at"], str) and config["created_at"],
             "Invalid release anchor")
    for name in (config["readme"], config["third_party_notices"]):
        _relative(name)
    return config


def release_plan(root=ROOT, version=VERSION):
    """Reconstruct the evaluator-only preparation plan from committed inputs."""
    from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, validate_plan
    from math_gauge.catalog import Suite

    root = _real_path(root)
    config = load_config(root, version)
    suite = Suite.load(root / "cases")
    _require(suite.metadata["visibility"] == "public"
             and suite.metadata["version"] == config["suite_version"]
             and len(suite.cases) == config["case_count"], "Release suite changed")
    profile = BenchmarkProfile.load(root / "protocol/benchmark-profile.json", suite)
    plan = build_plan(profile, suite, ["all"])
    if config["schema"] == "math-gauge.release-config/v3":
        from math_gauge.catalog import candidate_message
        from math_gauge.release_projection import CANDIDATE_PROJECTION, project_candidate_request
        plan["candidate_projection"] = CANDIDATE_PROJECTION
        for row in plan["case_index"]:
            request = project_candidate_request(suite.request(suite.cases[row["case_id"]]))
            row["request_sha256"] = _digest(json.dumps(request, ensure_ascii=False, sort_keys=True).encode("utf-8"))
            row["candidate_message_sha256"] = _digest(candidate_message(request).encode("utf-8"))
    # These identify release preparation, never an actual candidate execution.
    plan["plan_id"] = config["plan_id"]
    plan["created_at"] = config["created_at"]
    plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
    validate_plan(plan)
    _require(plan["planned"]["all_slots"] == config["slot_count"]
             and not plan["runtime_frozen"] and plan["candidate_calls"] == 0,
             "Release plan must contain the complete unfrozen dataset")
    return plan, suite


def _git(root, *args):
    result = subprocess.run(["git", "-C", str(root), *args], check=True,
                            capture_output=True)
    return result.stdout.decode("utf-8").strip()


def source_identity(root, source_commit, config):
    """Require the exact clean source identity before producing publishable bytes."""
    root = _real_path(root)
    _require(re.fullmatch(r"[0-9a-f]{40}", source_commit or "") is not None,
             "A full source commit SHA is required")
    _require(_real_path(_git(root, "rev-parse", "--show-toplevel")) == root,
             "Release source must be the Git root")
    _require(_git(root, "rev-parse", "HEAD") == source_commit,
             "Source commit is not the checked-out revision")
    _require(not _git(root, "status", "--porcelain", "--untracked-files=all"),
             "Publishable releases require a clean source checkout")
    origin = _git(root, "remote", "get-url", "origin")
    repository = config["repository"]
    expected_ssh = "git@github.com:" + repository.removeprefix("https://github.com/") + ".git"
    _require(origin in {repository, repository + ".git", expected_ssh},
             "Release repository identity differs from origin")
    return {"repository": repository, "commit": source_commit,
            "tree": _git(root, "rev-parse", "HEAD^{tree}")}


def _input_bindings(root, dataset_root, dataset, suite):
    bindings = []
    indexed = {c["case_id"]: c for c in dataset["cases"]}
    for cid, case in suite.cases.items():
        projected = indexed[cid]
        pairs = [(case["task"], projected["task_path"])]
        files = {f["name"]: f["path"] for f in projected["files"]}
        pairs += [(f["source"], files[f["target"]]) for f in case["solver_files"]]
        for source, target in pairs:
            source_path = suite.root / source
            raw = _file(dataset_root, target).read_bytes()
            _require(source_path.read_bytes() == raw, "Original candidate input bytes changed")
            bindings.append({"source": source_path.relative_to(root).as_posix(),
                             "path": "payload/" + target, "sha256": _digest(raw)})
    return sorted(bindings, key=lambda b: (b["path"], b["source"]))


def package_dataset(dataset_root, archive, *, config, source, wrappers,
                    input_bindings, source_files_sha256, plan=None, suite=None):
    """Package an already exported dataset using one explicit output allowlist."""
    from math_gauge.harness import inspect_release_dataset

    dataset_root = _real_path(dataset_root)
    dataset = inspect_release_dataset(dataset_root, plan=plan, suite=suite)
    _require(dataset["release_version"] == config["release_version"]
             and dataset["suite"]["version"] == config["suite_version"]
             and len(dataset["cases"]) == config["case_count"]
             and dataset["exported_slots"] == config["slot_count"]
             and dataset["planned"]["all_slots"] == config["slot_count"],
             "Release case or slot count changed")
    _require(set(wrappers) == WRAPPERS and all(isinstance(v, bytes) for v in wrappers.values()),
             "Release wrapper allowlist changed")
    payload_names = {"manifest.json", *dataset["files_sha256"]}
    files = dict(wrappers)
    files.update({"payload/" + name: _file(dataset_root, name).read_bytes()
                  for name in sorted(payload_names)})
    manifest = {
        "schema": ARCHIVE_SCHEMA, "release_version": config["release_version"],
        "suite": dataset["suite"], "dataset_sha256": dataset["dataset_sha256"],
        "base_plan_sha256": dataset["base_plan_sha256"], "source": source,
        "public_development_suite": True, "case_count": config["case_count"],
        "slot_count": config["slot_count"], "candidate_calls": 0,
        "runtime_frozen": False, "input_bindings": input_bindings,
        "source_files_sha256": source_files_sha256,
        "files_sha256": {name: _digest(raw) for name, raw in sorted(files.items())},
    }
    files["RELEASE.json"] = _json_bytes(manifest)
    archive = _real_path(archive)
    _require(not archive.exists(), "Release archives cannot be overwritten")
    prefix = "math-gauge-tasks-v" + config["release_version"] + "/"
    with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_STORED) as output:
        for name, raw in sorted(files.items()):
            _relative(name)
            info = zipfile.ZipInfo(prefix + name, ZIP_TIME)
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | 0o644) << 16
            info.compress_type = zipfile.ZIP_STORED
            output.writestr(info, raw)
    return manifest


def _archive_files(archive, prefix):
    """Read only the allowlisted regular-file ZIP representation, before extraction."""
    files = {}
    aliases = set()
    with zipfile.ZipFile(archive) as source:
        _require(not source.comment, "ZIP comments are not release content")
        for member in source.infolist():
            name = member.filename
            _relative(name)
            _require(member.orig_filename == name and name.startswith(prefix),
                     "Unexpected release archive root")
            relative = name[len(prefix):]
            _relative(relative)
            alias = unicodedata.normalize("NFC", name).casefold()
            _require(alias not in aliases and relative not in files,
                     "Duplicate or aliased UTF-8 ZIP filename")
            aliases.add(alias)
            _require(name.isascii() or member.flag_bits & 0x800,
                     "Non-ASCII ZIP filenames must be UTF-8")
            mode = member.external_attr >> 16
            _require(stat.S_IFMT(mode) == stat.S_IFREG and not member.is_dir(),
                     "Only regular files are permitted in a release ZIP")
            _require(not member.extra and not member.comment and not member.flag_bits & 1
                     and member.compress_type == zipfile.ZIP_STORED
                     and member.date_time == ZIP_TIME,
                     "Unexpected release ZIP metadata")
            files[relative] = source.read(member)
    return files


def _check_legacy_release_archive(archive, *, checksums=None, version=LEGACY_VERSION,
                                  source_commit=None):
    """Keep the historical v1 payload contract available without rewriting it."""
    from math_gauge.harness import inspect_release_dataset

    config = load_config(version=version)
    archive = _real_path(archive)
    if checksums is not None:
        _require(_real_path(checksums).read_bytes()
                 == f"{_digest(archive.read_bytes())}  {archive.name}\n".encode("ascii"),
                 "Archive checksum differs from SHA256SUMS")
    files = _archive_files(archive, "math-gauge-tasks-v" + version + "/")
    _require("RELEASE.json" in files and "payload/manifest.json" in files,
             "Missing release or dataset manifest")
    manifest = _read_json(files["RELEASE.json"])
    _require(set(manifest) == ARCHIVE_KEYS and manifest["schema"] == ARCHIVE_SCHEMA
             and manifest["release_version"] == version,
             "Unsupported release archive manifest")
    _require(set(manifest["source"]) == {"repository", "commit", "tree"}
             and manifest["source"]["repository"] == config["repository"]
             and all(re.fullmatch(r"[0-9a-f]{40}", manifest["source"][key]) is not None
                     for key in ("commit", "tree")), "Invalid release source identity")
    if source_commit is not None:
        _require(manifest["source"]["commit"] == source_commit,
                 "Release source commit differs from the expected commit")
    _require(manifest["public_development_suite"] is True
             and manifest["candidate_calls"] == 0 and manifest["runtime_frozen"] is False,
             "Release preparation cannot claim a candidate execution")
    dataset = _read_json(files["payload/manifest.json"])
    expected = WRAPPERS | {"RELEASE.json", "payload/manifest.json"} | {
        "payload/" + name for name in dataset["files_sha256"]}
    _require(set(files) == expected
             and set(manifest["files_sha256"]) == expected - {"RELEASE.json"},
             "Unlisted or missing release files")
    for name, digest in manifest["files_sha256"].items():
        _require(_digest(files[name]) == digest, "Release content changed: " + name)
    bindings = manifest["input_bindings"]
    _require(isinstance(bindings, list), "Missing original input bindings")
    bound = set()
    for binding in bindings:
        _require(set(binding) == {"source", "path", "sha256"}, "Unexpected input binding")
        _relative(binding["source"])
        path = binding["path"]
        _require(path.startswith("payload/cases/") and path in files and path not in bound
                 and _digest(files[path]) == binding["sha256"], "Invalid original input binding")
        bound.add(path)
    required_inputs = {"payload/" + case["task_path"] for case in dataset["cases"]}
    required_inputs.update("payload/" + item["path"] for case in dataset["cases"]
                           for item in case["files"])
    _require(bound == required_inputs, "Incomplete original input hash bindings")
    _require(isinstance(manifest["source_files_sha256"], dict)
             and manifest["source_files_sha256"], "Missing release code hashes")
    for name, digest in manifest["source_files_sha256"].items():
        _relative(name)
        _require(re.fullmatch(r"[0-9a-f]{64}", digest) is not None, "Invalid source file hash")
    with tempfile.TemporaryDirectory(prefix="math-gauge-release-check-") as temporary:
        root = _real_path(temporary)
        for name, raw in files.items():
            target = root.joinpath(*_relative(name).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        inspected = inspect_release_dataset(root / "payload")
    _require(manifest["suite"] == inspected["suite"]
             and inspected["suite"]["version"] == config["suite_version"]
             and inspected["release_version"] == version
             and manifest["dataset_sha256"] == inspected["dataset_sha256"]
             and manifest["base_plan_sha256"] == inspected["base_plan_sha256"]
             and manifest["case_count"] == len(inspected["cases"]) == config["case_count"]
             and manifest["slot_count"] == inspected["exported_slots"] == config["slot_count"]
             and inspected["planned"]["all_slots"] == config["slot_count"],
             "Release dataset identity or fixed counts changed")
    return manifest


def _build_legacy_release(destination, *, source_commit, root=ROOT, version=LEGACY_VERSION):
    from math_gauge.harness import export_release_dataset

    root = _real_path(root)
    config = load_config(root, version)
    source = source_identity(root, source_commit, config)
    plan, suite = release_plan(root, version)
    destination = _real_path(destination)
    _require(not destination.exists() and not destination.is_relative_to(root / "cases"),
             "Release output must be a new directory outside the suite")
    wrappers = {"README.md": _file(root, config["readme"]).read_bytes(),
                "LICENSE": _file(root, "LICENSE").read_bytes(),
                "THIRD_PARTY_NOTICES.md": _file(root, config["third_party_notices"]).read_bytes()}
    code_names = [p.relative_to(root).as_posix() for p in sorted((root / "math_gauge").glob("*.py"))]
    code_names += ["scripts/release.py", f"releases/v{version}/config.json", "LICENSE",
                   config["readme"], config["third_party_notices"]]
    code_hashes = {name: _digest(_file(root, name).read_bytes()) for name in sorted(code_names)}
    destination.mkdir(parents=True)
    try:
        with tempfile.TemporaryDirectory(prefix="math-gauge-release-build-") as temporary:
            temporary = _real_path(temporary)
            dataset_root = temporary / "payload"
            dataset = export_release_dataset(plan, suite, dataset_root, release_version=version)
            archive = destination / f"math-gauge-tasks-v{version}.zip"
            manifest = package_dataset(
                dataset_root, archive, config=config, source=source, wrappers=wrappers,
                input_bindings=_input_bindings(root, dataset_root, dataset, suite),
                source_files_sha256=code_hashes, plan=plan, suite=suite)
        checksum = destination / "SHA256SUMS"
        checksum.write_bytes(f"{_digest(archive.read_bytes())}  {archive.name}\n".encode("ascii"))
        evaluator = destination / "evaluator"
        evaluator.mkdir()
        (evaluator / "plan.json").write_bytes(_json_bytes(plan))
        check_release_archive(archive, checksums=checksum, version=version,
                              source_commit=source_commit)
        _require(source_identity(root, source_commit, config) == source,
                 "Source changed while building release assets")
        return {"archive": str(archive), "sha256": _digest(archive.read_bytes()),
                "checksums": str(checksum), "evaluator_plan": str(evaluator / "plan.json"),
                "dataset_sha256": manifest["dataset_sha256"],
                "base_plan_sha256": manifest["base_plan_sha256"],
                "source_commit": source_commit, "candidate_calls": 0}
    except BaseException:
        shutil.rmtree(destination)
        raise


def _simple_input_bindings(root, suite, *, projection=None):
    bindings = []
    for cid, case in suite.cases.items():
        pairs = [(case["task"], f"cases/{cid}/task.md")]
        pairs += [(item["source"], f"cases/{cid}/files/{item['target']}")
                  for item in case["solver_files"]]
        for name, target in pairs:
            path = _file(suite.root, name)
            binding = {"source": path.relative_to(root).as_posix(),
                       "path": target, "sha256": _digest(path.read_bytes())}
            if projection is not None:
                from math_gauge.release_projection import CANDIDATE_PROJECTION, project_candidate_text
                _require(projection == CANDIDATE_PROJECTION, "Unknown release candidate projection")
                binding["projected_sha256"] = _digest(project_candidate_text(
                    Path(target).name, path.read_bytes().decode("utf-8")).encode("utf-8"))
            bindings.append(binding)
    return sorted(bindings, key=lambda binding: (binding["path"], binding["source"]))


def _release_source_files(root, config, bindings):
    """Hash the consumed release sources; no evaluator contents are exported."""
    names = {p.relative_to(root).as_posix() for p in (root / "math_gauge").glob("*.py")}
    names.update({"scripts/release.py", f"releases/v{config['release_version']}/config.json",
                  "protocol/benchmark-profile.json", "LICENSE", config["readme"],
                  config["third_party_notices"]})
    names.update(binding["source"] for binding in bindings)
    return {name: _digest(_file(root, name).read_bytes()) for name in sorted(names)}


def _source_digest(files_sha256, suite, base_plan_sha256):
    return _digest(_json_bytes({"files_sha256": files_sha256, "suite": suite,
                                "base_plan_sha256": base_plan_sha256}))


def _preview_source(root, config):
    _require(_real_path(_git(root, "rev-parse", "--show-toplevel")) == root,
             "Release source must be the Git root")
    repository = config["repository"]
    origin = _git(root, "remote", "get-url", "origin")
    expected_ssh = "git@github.com:" + repository.removeprefix("https://github.com/") + ".git"
    _require(origin in {repository, repository + ".git", expected_ssh},
             "Release repository identity differs from origin")
    parent = _git(root, "rev-parse", "HEAD")
    _require(re.fullmatch(r"[0-9a-f]{40}", parent) is not None, "Invalid preview parent commit")
    return {"repository": repository, "parent_commit": parent}


def _public_provenance(provenance, plan):
    """Keep source paths, repository and source revision on the evaluator side."""
    if "candidate_projection" not in plan:
        return provenance
    source = provenance["source"]
    return {"schema": "benchmark.release-provenance/v1", "kind": provenance["kind"],
            "candidate_projection": plan["candidate_projection"],
            "source_sha256": source["source_sha256"],
            "source_revision_sha256": _digest(source.get("commit", source.get("parent_commit")).encode("ascii")),
            "input_bindings": [{"path": b["path"], "sha256": b["projected_sha256"]}
                               for b in provenance["input_bindings"]]}


def _check_simple_provenance(manifest, files, config, source_commit=None):
    provenance = manifest.get("release_provenance")
    if config["schema"] == "math-gauge.external-release-config/v1":
        _require(source_commit is None, "Local datasets do not claim an exact clean source commit")
        _require(isinstance(provenance, dict) and set(provenance) == {
            "schema", "kind", "source_sha256", "source_revision_sha256", "input_bindings"}
            and provenance["schema"] == "math-gauge.local-dataset-provenance/v1"
            and provenance["kind"] == "local_dataset", "Invalid local dataset provenance")
        _require(all(isinstance(provenance[k], str) and re.fullmatch(r"[0-9a-f]{64}", provenance[k])
                     for k in ("source_sha256", "source_revision_sha256")), "Invalid local source identity")
        expected = {case["task_path"] for case in manifest["cases"]}
        expected.update(item["path"] for case in manifest["cases"] for item in case["files"])
        bindings = provenance["input_bindings"]
        _require(isinstance(bindings, list) and len(bindings) == len(expected)
                 and all(isinstance(b, dict) and set(b) == {"path", "sha256"} for b in bindings)
                 and {b["path"] for b in bindings} == expected
                 and all(b["sha256"] == _digest(files[b["path"]]) for b in bindings),
                 "Local dataset input bindings changed")
        return provenance
    if config["schema"] == "math-gauge.release-config/v3":
        from math_gauge.release_projection import CANDIDATE_PROJECTION
        _require(isinstance(provenance, dict) and set(provenance) == {
            "schema", "kind", "candidate_projection", "source_sha256", "source_revision_sha256", "input_bindings"}
            and provenance["schema"] == "benchmark.release-provenance/v1"
            and provenance["candidate_projection"] == CANDIDATE_PROJECTION
            and provenance["kind"] in {"local_preview", "clean_source"},
            "Missing or unsupported neutral release provenance")
        _require(all(isinstance(provenance[k], str) and re.fullmatch(r"[0-9a-f]{64}", provenance[k])
                     for k in ("source_sha256", "source_revision_sha256")), "Invalid opaque source identity")
        if source_commit is not None:
            _require(provenance["kind"] == "clean_source", "Local preview has a parent commit, not an exact source commit")
            _require(provenance["source_revision_sha256"] == _digest(source_commit.encode("ascii")),
                     "Release source commit differs from the expected commit")
        expected = {case["task_path"] for case in manifest["cases"]}
        expected.update(item["path"] for case in manifest["cases"] for item in case["files"])
        bindings = provenance["input_bindings"]
        _require(isinstance(bindings, list) and len(bindings) == len(expected)
                 and all(isinstance(b, dict) and set(b) == {"path", "sha256"} for b in bindings)
                 and {b["path"] for b in bindings} == expected
                 and all(b["sha256"] == _digest(files[b["path"]]) for b in bindings),
                 "Incomplete original projected input hash bindings")
        return provenance
    _require(isinstance(provenance, dict)
             and set(provenance) == {"schema", "kind", "source", "input_bindings", "source_files_sha256"}
             and provenance["schema"] == PROVENANCE_SCHEMA
             and provenance["kind"] in {"local_preview", "clean_source"},
             "Missing or unsupported release provenance")
    source = provenance["source"]
    identity_keys = {"parent_commit"} if provenance["kind"] == "local_preview" else {"commit", "tree"}
    _require(isinstance(source, dict)
             and set(source) == {"repository", "source_sha256"} | identity_keys
             and source["repository"] == config["repository"]
             and all(isinstance(source[key], str)
                     and re.fullmatch(r"[0-9a-f]{40}", source[key]) is not None for key in identity_keys),
             "Invalid release source identity")
    if source_commit is not None:
        _require(provenance["kind"] == "clean_source",
                 "Local preview has a parent commit, not an exact source commit")
        _require(source["commit"] == source_commit,
                 "Release source commit differs from the expected commit")
    hashes = provenance["source_files_sha256"]
    _require(isinstance(hashes, dict) and hashes, "Missing release source hashes")
    for name, digest in hashes.items():
        _relative(name)
        _require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
                 "Invalid source file hash")
    required_sources = {"scripts/release.py", "math_gauge/harness.py", "math_gauge/catalog.py",
                        "math_gauge/execution.py", "protocol/benchmark-profile.json", "LICENSE",
                        config["readme"], config["third_party_notices"],
                        f"releases/v{config['release_version']}/config.json"}
    _require(required_sources <= set(hashes), "Incomplete release source hashes")
    _require(source["source_sha256"] == _source_digest(
        hashes, manifest["suite"], manifest["base_plan_sha256"]),
        "Release source input identity changed")
    bindings = provenance["input_bindings"]
    _require(isinstance(bindings, list), "Missing original input bindings")
    bound = set()
    for binding in bindings:
        _require(isinstance(binding, dict) and set(binding) == {"source", "path", "sha256"},
                 "Unexpected input binding")
        _relative(binding["source"])
        path = str(_relative(binding["path"]))
        _require(path.startswith("cases/") and path in files and path not in bound
                 and hashes.get(binding["source"]) == binding["sha256"] == _digest(files[path]),
                 "Invalid original input binding")
        bound.add(path)
    required_inputs = {case["task_path"] for case in manifest["cases"]}
    required_inputs.update(item["path"] for case in manifest["cases"] for item in case["files"])
    _require(bound == required_inputs, "Incomplete original input hash bindings")
    for target, original in (("README.md", config["readme"]), ("LICENSE", "LICENSE"),
                             ("THIRD_PARTY_NOTICES.md", config["third_party_notices"])):
        _require(hashes[original] == _digest(files[target]), "Release wrapper source changed: " + target)
    return provenance


def _check_simple_contents(manifest, files, config, source_commit=None):
    expected_schema = ("benchmark.release-dataset/v2" if config["schema"] == "math-gauge.release-config/v3"
                       else "math-gauge.release-dataset/v2")
    _require(manifest.get("schema") == expected_schema
             and manifest.get("release_version") == config["release_version"]
             == config["suite_version"] == manifest.get("suite", {}).get("version"),
             "Release version must equal the suite version")
    _require(len(manifest["cases"]) == config["case_count"]
             and manifest["exported_slots"] == manifest["planned"]["all_slots"] == config["slot_count"],
             "Release dataset fixed counts changed")
    expected = WRAPPERS | {"manifest.json", "tools/benchmark.py"}
    expected.update(case["task_path"] for case in manifest["cases"])
    expected.update(item["path"] for case in manifest["cases"] for item in case["files"])
    _require(set(files) == expected and set(manifest["files_sha256"]) == expected - {"manifest.json"},
             "Unlisted or missing release files")
    for name, digest in manifest["files_sha256"].items():
        _relative(name)
        _require(_digest(files[name]) == digest, "Release content changed: " + name)
    if config["schema"] == "math-gauge.release-config/v3":
        for name, raw in files.items():
            surface = name.encode("utf-8").lower() + b"\n" + raw.lower()
            _require(not any(marker in surface for marker in (
                b"math-gauge", b"math_gauge", b"mathgauge", b"math gauge", b"github.com")),
                "Neutral release contains a source identity marker: " + name)
    _check_simple_provenance(manifest, files, config, source_commit)


def package_simple_dataset(dataset_root, archive, *, config, plan=None, suite=None):
    """Archive the flat v2 dataset without adding a second guide or manifest."""
    from math_gauge.harness import inspect_release_dataset

    dataset_root = _real_path(dataset_root)
    manifest = inspect_release_dataset(dataset_root, plan=plan, suite=suite)
    files = {name: _file(dataset_root, name).read_bytes()
             for name in {"manifest.json", *manifest["files_sha256"]}}
    _check_simple_contents(manifest, files, config)
    archive = _real_path(archive)
    _require(not archive.exists(), "Release archives cannot be overwritten")
    prefix = ("benchmark" if config["schema"] in {"math-gauge.release-config/v3", "math-gauge.external-release-config/v1"}
              else "math-gauge") + f"-v{config['release_version']}/"
    with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_STORED) as output:
        for name, raw in sorted(files.items()):
            _relative(name)
            member = zipfile.ZipInfo(prefix + name, ZIP_TIME)
            member.create_system = 3
            member.external_attr = (stat.S_IFREG | 0o644) << 16
            member.compress_type = zipfile.ZIP_STORED
            output.writestr(member, raw)
    return manifest


def check_release_archive(archive, *, checksums=None, version=None, source_commit=None, external=False):
    """Check v1 and flat v2 ZIPs using trusted code before writing any member."""
    from math_gauge.harness import inspect_release_dataset

    archive = _real_path(archive)
    if checksums is not None:
        _require(_real_path(checksums).read_bytes()
                 == f"{_digest(archive.read_bytes())}  {archive.name}\n".encode("ascii"),
                 "Archive checksum differs from SHA256SUMS")
    with zipfile.ZipFile(archive) as source:
        roots = {_relative(member.filename).parts[0] for member in source.infolist()}
    _require(len(roots) == 1, "Unexpected release archive root")
    top = next(iter(roots))
    matched = re.fullmatch(r"(math-gauge-tasks|math-gauge|benchmark)-v(\d+\.\d+\.\d+)", top)
    _require(matched is not None, "Unexpected release archive root")
    detected_version = matched.group(2)
    _require(version is None or version == detected_version,
             "Release archive version differs from the expected version")
    version = detected_version
    if external:
        _require(matched.group(1) == "benchmark" and source_commit is None,
                 "Local dataset checks cannot assert a clean source release")
        files = _archive_files(archive, top + "/")
        _require("manifest.json" in files, "Missing release dataset manifest")
        metadata = _read_json(files["manifest.json"])
        config = {"schema": "math-gauge.external-release-config/v1", "release_version": version,
                  "suite_version": version, "case_count": len(metadata.get("cases", [])),
                  "slot_count": metadata.get("exported_slots")}
    else:
        config = load_config(version=version)
    if matched.group(1) == "math-gauge-tasks":
        _require(config["schema"] == "math-gauge.release-config/v1", "Unexpected legacy archive version")
        return _check_legacy_release_archive(archive, version=version, source_commit=source_commit)
    _require(config["schema"] in {"math-gauge.release-config/v2", "math-gauge.release-config/v3", "math-gauge.external-release-config/v1"}
             and (matched.group(1) == "benchmark") == (config["schema"] in {"math-gauge.release-config/v3", "math-gauge.external-release-config/v1"}),
             "Unexpected simple archive version")
    files = _archive_files(archive, top + "/")
    _require("manifest.json" in files, "Missing release dataset manifest")
    try:
        manifest = _read_json(files["manifest.json"])
        _check_simple_contents(manifest, files, config, source_commit)
        with tempfile.TemporaryDirectory(prefix="math-gauge-simple-release-check-") as temporary:
            extracted = _real_path(temporary)
            for name, raw in files.items():
                target = extracted.joinpath(*_relative(name).parts)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
            inspect_release_dataset(extracted)
    except (KeyError, TypeError, AttributeError, UnicodeError, json.JSONDecodeError) as error:
        raise ValueError("Malformed release dataset manifest") from error
    return manifest


def build_release(destination, *, source_commit=None, local_preview=False, root=ROOT, version=VERSION):
    """Build from exact clean source or an explicitly identified local preview."""
    from math_gauge.harness import export_simple_release_dataset, make_release_anchor

    root = _real_path(root)
    config = load_config(root, version)
    if config["schema"] == "math-gauge.release-config/v1":
        _require(not local_preview, "Historical v1 releases require their exact clean source commit")
        return _build_legacy_release(destination, source_commit=source_commit, root=root, version=version)
    _require(not local_preview or source_commit is None,
             "Local previews use actual source hashes; do not supply a source commit")
    source = _preview_source(root, config) if local_preview else source_identity(root, source_commit, config)
    plan, suite = release_plan(root, version)
    bindings = _simple_input_bindings(root, suite, projection=plan.get("candidate_projection"))
    hashes = _release_source_files(root, config, bindings)
    source["source_sha256"] = _source_digest(hashes, plan["suite"], plan["plan_sha256"])
    provenance = {"schema": PROVENANCE_SCHEMA,
                  "kind": "local_preview" if local_preview else "clean_source", "source": source,
                  "input_bindings": bindings, "source_files_sha256": hashes}
    destination = _real_path(destination)
    _require(not destination.exists() and not destination.is_relative_to(suite.root),
             "Release output must be a new directory outside the suite")
    destination.mkdir(parents=True)
    try:
        with tempfile.TemporaryDirectory(prefix="math-gauge-simple-release-build-") as temporary:
            dataset_root = _real_path(temporary) / "dataset"
            dataset = export_simple_release_dataset(
                plan, suite, dataset_root, release_version=version,
                readme=_file(root, config["readme"]).read_bytes(),
                extra_files={"LICENSE": _file(root, "LICENSE").read_bytes(),
                             "THIRD_PARTY_NOTICES.md": _file(root, config["third_party_notices"]).read_bytes()},
                release_provenance=_public_provenance(provenance, plan))
            prefix = "benchmark" if config["schema"] == "math-gauge.release-config/v3" else "math-gauge"
            archive = destination / f"{prefix}-v{version}.zip"
            manifest = package_simple_dataset(dataset_root, archive, config=config, plan=plan, suite=suite)
        checksum = destination / "SHA256SUMS"
        checksum.write_bytes(f"{_digest(archive.read_bytes())}  {archive.name}\n".encode("ascii"))
        evaluator_plan = destination / "evaluator-plan.json"
        evaluator_plan.write_bytes(_json_bytes(make_release_anchor(plan, dataset,
            release_provenance=provenance if "candidate_projection" in plan else None)))
        check_release_archive(archive, checksums=checksum, version=version,
                              source_commit=None if local_preview else source_commit)
        final_plan, final_suite = release_plan(root, version)
        final_bindings = _simple_input_bindings(root, final_suite, projection=final_plan.get("candidate_projection"))
        _require(config == load_config(root, version) and final_plan == plan
                 and final_bindings == bindings
                 and _release_source_files(root, config, final_bindings) == hashes,
                 "Source changed while building release assets")
        final_source = _preview_source(root, config) if local_preview else source_identity(root, source_commit, config)
        _require(final_source == {k: v for k, v in source.items() if k != "source_sha256"},
                 "Source changed while building release assets")
        return {"archive": str(archive), "sha256": _digest(archive.read_bytes()),
                "checksums": str(checksum), "evaluator_plan": str(evaluator_plan),
                "release_version": version, "suite_version": suite.metadata["version"],
                "dataset_sha256": dataset["dataset_sha256"], "base_plan_sha256": manifest["base_plan_sha256"],
                "provenance_kind": provenance["kind"], "source": source, "candidate_calls": 0}
    except BaseException:
        shutil.rmtree(destination)
        raise


def _external_readme(version, plan):
    first = plan["slots"][0]["slot_id"]
    targets = ", ".join(plan["profile"]["data"]["components"][i]["id"]
                        for i in range(len(plan["profile"]["data"]["components"])))
    return f"""# Benchmark {version}

This package contains {plan['planned']['papers']} complete tasks and {plan['planned']['all_slots']} planned answer slots.
Python 3.10+ is sufficient; no installation or third-party packages are required.
The optional controller tool prepares and records requests. It never calls a model.

README.md, manifest.json, tools and runtime settings are controller-only.
The candidate receives only the complete generated messages, their explicit attachments,
frozen generation parameters and permitted history from its own branch.
Do not give the candidate this directory, evaluation material, other answers,
controller memory or project instructions.

Create runtime.json outside this package with the actual model_label,
adapter_identity, candidate_parameters.model, budget.timeout_seconds and
fresh_context=true. Supply output_tokens only when the transport enforces it;
preserve unknown usage and unsupported limits as unknown. Freeze the mapping
to the provider's real settings before executing. The default condition allows
no candidate tools or external retrieval. A separately declared local-tools
condition still forbids external search and tool network access.

```sh
python3 tools/benchmark.py check
python3 tools/benchmark.py prepare --runtime ../runtime.json --target all --out ../new-run
python3 tools/benchmark.py request --run ../new-run --responses ../new-answers --slot '{first}' --out ../request.json
```

Read selected_slot_ids in the new run manifest. Independent candidate calls
may run in parallel with isolated contexts and workspaces. Serialize controller
writes to shared output and retain the manifest order for shared request/record
operations. A followup waits for its own branch's recorded predecessor and
receives only its exact branch history generated by the controller. The harness
must implement file, process, memory, tool and network isolation. If the actual
model or isolation cannot be supplied, retain an unexecuted slot and explain why.
Targets include all, core, repeat, neutral, stance and {targets}; some optional
targets may have no slots in this dataset. Never substitute another model.

Send the whole generated messages array and frozen parameters without adding
solver hints. Save the complete original answer bytes, all request/response
events, tool feedback, failures, timeouts and known usage. Do not repair answers.

```sh
python3 tools/benchmark.py record --run ../new-run --responses ../new-answers --slot '{first}' --request ../request.json --response ../raw-answer.md --status ok
python3 tools/benchmark.py pack --run ../new-run --responses ../new-answers --out ../answers.zip --origin external --declared-external-calls N
```

Replace N with every actual call, including retries and failed calls. Offline
fixtures retain the default fixture origin and zero external calls. A first
readable answer locks its slot regardless of correctness. Only an unreadable
temporary failure may be retried under the frozen retry limits, preserving each
attempt. Use skip only for calls that never happened. Record usage and metadata
with the tool's --usage and --metadata options; preserve original external logs.
For followups, obey the supplied KEEP/FULL format and never synthesize history.
All outputs use new paths outside the immutable dataset. Return answers.zip and
preserve the original dataset plus all local execution evidence.

Hashes bind files; they do not authenticate a backend, execution chronology,
isolation, mathematical correctness or human approval. Import and mathematical
review are separate evaluator operations. This is a local dataset snapshot and
does not claim a clean committed release.
""".encode("utf-8")


def _local_repository_snapshot(path):
    """Observe dirty or unborn repositories without requiring or changing Git state."""
    def read(*args):
        result = subprocess.run(["git", "-C", str(path), *args], capture_output=True)
        return result.stdout if result.returncode == 0 else None
    head = read("rev-parse", "--verify", "HEAD")
    status = read("status", "--porcelain=v1", "--untracked-files=all")
    return {"root": str(path), "head": head.decode().strip() if head else None,
            "dirty": bool(status) if status is not None else None,
            "status_sha256": _digest(status) if status is not None else None}


def build_external_release(destination, *, suite_paths, profile_path, version=None,
                           readme_path=None, license_path=None, notices_path=None):
    """Package independently stored public/private data using the installed shared runner.

    Dirty and unborn source repositories are permitted. Full source identities,
    evaluator contracts and the profile remain in the evaluator anchor, not ZIP.
    Candidate tasks and attachment bytes are copied exactly, without rewriting.
    """
    from math_gauge.benchmarks import BenchmarkProfile, build_plan, identity, validate_plan
    from math_gauge.catalog import Suite
    from math_gauge.execution import runner_fingerprint
    from math_gauge.harness import export_simple_release_dataset, make_release_anchor

    suite = Suite.load(suite_paths)
    profile = BenchmarkProfile.load(profile_path, suite)
    version = version or suite.metadata["version"]
    _require(re.fullmatch(r"\d+\.\d+\.\d+", version) is not None
             and version == suite.metadata["version"], "Release version must equal the suite version")
    plan = build_plan(profile, suite)
    stable = {"suite": plan["suite"], "profile_sha256": profile.sha256,
              "runner_sha256": plan["runner_sha256"],
              "reliability_files_sha256": plan["reliability"]["files_sha256"]}
    plan.update(plan_id=identity(stable)[:32], created_at="local-dataset-snapshot")
    plan["plan_sha256"] = identity({k: v for k, v in plan.items() if k != "plan_sha256"})
    validate_plan(plan)
    wrappers = {"README.md": Path(readme_path).read_bytes() if readme_path else _external_readme(version, plan),
                "LICENSE": Path(license_path).read_bytes() if license_path else
                    b"This dataset grants no additional permissions. Consult its owner for applicable terms.\n",
                "THIRD_PARTY_NOTICES.md": Path(notices_path).read_bytes() if notices_path else
                    b"Source attribution and applicable permissions must be retained with the supplied materials.\n"}
    bindings = []
    for cid, case in suite.cases.items():
        pairs = [(case["task"], f"cases/{cid}/task.md"), *(
            (row["source"], f"cases/{cid}/files/{row['target']}") for row in case["solver_files"])]
        for name, target in pairs:
            raw = suite.case_file(cid, name).read_bytes()
            bindings.append({"case_id": cid, "source_suite": suite.source_binding(cid),
                             "source": name, "path": target, "sha256": _digest(raw)})
    consumed = dict(stable, input_bindings=bindings,
                    wrappers_sha256={k: _digest(v) for k, v in wrappers.items()})
    source_sha256 = identity(consumed)
    repositories = [_local_repository_snapshot(member.root)
                    for member in suite.members or (suite,)]
    provenance = {"schema": "math-gauge.external-release-provenance/v1", "kind": "local_dataset",
                  "source_sha256": source_sha256, "source_revision_sha256": identity(repositories),
                  "source_suites": [{"manifest": str(member.manifest_path),
                                     **suite.source_binding(next(iter(member.cases)))}
                                    for member in suite.members or (suite,)],
                  "repositories": repositories, "consumed": consumed}
    public_provenance = {k: provenance[k] for k in ("kind", "source_sha256", "source_revision_sha256")}
    public_provenance.update(schema="math-gauge.local-dataset-provenance/v1",
        input_bindings=[{k: row[k] for k in ("path", "sha256")} for row in bindings])
    config = {"schema": "math-gauge.external-release-config/v1", "release_version": version,
              "suite_version": version, "case_count": len(suite.cases), "slot_count": plan["planned"]["all_slots"]}
    destination = _real_path(destination)
    _require(not destination.exists() and not suite.overlaps(destination, bidirectional=True),
             "Release output must be a new directory outside every source suite")
    destination.mkdir(parents=True)
    try:
        with tempfile.TemporaryDirectory(prefix="math-gauge-external-release-") as temporary:
            dataset_root = _real_path(temporary) / "dataset"
            dataset = export_simple_release_dataset(plan, suite, dataset_root, release_version=version,
                readme=wrappers["README.md"], extra_files={k: wrappers[k] for k in ("LICENSE", "THIRD_PARTY_NOTICES.md")},
                release_provenance=public_provenance)
            archive = destination / f"benchmark-v{version}.zip"
            package_simple_dataset(dataset_root, archive, config=config, plan=plan, suite=suite)
        checksums = destination / "SHA256SUMS"
        checksums.write_bytes(f"{_digest(archive.read_bytes())}  {archive.name}\n".encode("ascii"))
        evaluator_plan = destination / "evaluator-plan.json"
        evaluator_plan.write_bytes(_json_bytes(make_release_anchor(plan, dataset, release_provenance=provenance)))
        check_release_archive(archive, checksums=checksums, version=version, external=True)
        _require(suite.reload().sha256 == suite.sha256
                 and _digest(Path(profile_path).read_bytes()) == profile.sha256
                 and profile.packet()["files_sha256"] == stable["reliability_files_sha256"]
                 and runner_fingerprint() == stable["runner_sha256"],
                 "Source changed while building local dataset assets")
        for key, path in (("README.md", readme_path), ("LICENSE", license_path), ("THIRD_PARTY_NOTICES.md", notices_path)):
            _require(path is None or Path(path).read_bytes() == wrappers[key], "Release wrapper changed while building")
        return {"archive": str(archive), "sha256": _digest(archive.read_bytes()),
                "checksums": str(checksums), "evaluator_plan": str(evaluator_plan),
                "release_version": version, "suite_version": suite.metadata["version"],
                "dataset_sha256": dataset["dataset_sha256"], "source_sha256": source_sha256,
                "provenance_kind": "local_dataset", "candidate_calls": 0}
    except BaseException:
        shutil.rmtree(destination)
        raise


def recover_evaluator_plan(destination, *, source_commit=None, local_preview=False, root=ROOT, version=VERSION):
    """Recover the exact external anchor by rebuilding the same source-mode dataset."""
    destination = _real_path(destination)
    _require(not destination.exists(), "Evaluator plan output must be a new file")
    config = load_config(root, version)
    if config["schema"] == "math-gauge.release-config/v1":
        _require(not local_preview, "Historical v1 plans require their exact clean source commit")
        source_identity(root, source_commit, config)
        plan, _ = release_plan(root, version)
        raw = _json_bytes(plan)
        result = {"plan_sha256": plan["plan_sha256"], "candidate_calls": 0}
    else:
        # The dataset carries only the base-plan hash. The external wrapper is
        # created afterwards, so reproducing it introduces no identity cycle.
        with tempfile.TemporaryDirectory(prefix="math-gauge-evaluator-recovery-") as temporary:
            receipt = build_release(_real_path(temporary) / "assets", source_commit=source_commit,
                                    local_preview=local_preview, root=root, version=version)
            raw = Path(receipt["evaluator_plan"]).read_bytes()
        result = {key: receipt[key] for key in ("dataset_sha256", "base_plan_sha256", "provenance_kind",
                                                "source", "candidate_calls")}
    with destination.open("xb") as output:
        output.write(raw)
    return dict(result, out=str(destination))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build", help="Build a version-aligned ZIP or an explicitly local preview")
    build.add_argument("--out", required=True)
    build_source = build.add_mutually_exclusive_group(required=True)
    build_source.add_argument("--source-commit")
    build_source.add_argument("--local-preview", action="store_true")
    build.add_argument("--version")
    build.add_argument("--suite", action="append", help="External suite directory or composition manifest; repeat to compose.")
    build.add_argument("--profile", help="Evaluator-only profile for an external dataset.")
    build.add_argument("--readme", help="Optional controller guide for an external dataset.")
    build.add_argument("--license", dest="license_path", help="Dataset distribution terms, when supplied by its owner.")
    build.add_argument("--third-party-notices", dest="notices_path")
    check = sub.add_parser("check", help="Validate checksums, safe ZIP inventory and dataset")
    check.add_argument("--archive", required=True)
    check.add_argument("--checksums", required=True)
    check.add_argument("--source-commit")
    check.add_argument("--version", help="Require this version; otherwise detect the archive version")
    check.add_argument("--external", action="store_true", help="Check a local external dataset, without asserting a named public release.")
    evaluator = sub.add_parser("evaluator-plan", help="Recover the operator-only release anchor")
    evaluator.add_argument("--out", required=True)
    evaluator_source = evaluator.add_mutually_exclusive_group(required=True)
    evaluator_source.add_argument("--source-commit")
    evaluator_source.add_argument("--local-preview", action="store_true")
    evaluator.add_argument("--version", default=VERSION)
    args = parser.parse_args(argv)
    try:
        if args.command == "build":
            if args.suite:
                _require(args.local_preview and args.profile,
                         "External datasets require --local-preview and --profile; no commit is required")
                result = build_external_release(args.out, suite_paths=args.suite, profile_path=args.profile,
                    version=args.version, readme_path=args.readme, license_path=args.license_path,
                    notices_path=args.notices_path)
            else:
                _require(not any((args.profile, args.readme, args.license_path, args.notices_path)),
                         "External dataset options require --suite")
                result = build_release(args.out, source_commit=args.source_commit,
                                       local_preview=args.local_preview, version=args.version or VERSION)
        elif args.command == "check":
            value = check_release_archive(args.archive, checksums=args.checksums,
                                          version=args.version, source_commit=args.source_commit, external=args.external)
            result = {"release_version": value["release_version"],
                      "dataset_sha256": value["dataset_sha256"], "candidate_calls": 0}
            if value["schema"] == ARCHIVE_SCHEMA:
                result.update(source=value["source"], cases=value["case_count"], slots=value["slot_count"])
            else:
                result.update(source=value["release_provenance"].get("source"),
                              provenance_kind=value["release_provenance"]["kind"],
                              cases=len(value["cases"]), slots=value["exported_slots"])
        else:
            result = recover_evaluator_plan(args.out, source_commit=args.source_commit,
                                             local_preview=args.local_preview, version=args.version)
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
        return 0
    except (ValueError, OSError, KeyError, TypeError, zipfile.BadZipFile,
            subprocess.CalledProcessError) as error:
        print("Release error: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    # Running a source script must use this checkout's shared implementation.
    sys.path.insert(0, str(ROOT))
    raise SystemExit(main())
