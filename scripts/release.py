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
VERSION = "0.1.0"
ARCHIVE_SCHEMA = "math-gauge.release-archive/v1"
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
             and config["schema"] == "math-gauge.release-config/v1"
             and config["release_version"] == version,
             "Unsupported release configuration")
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


def check_release_archive(archive, *, checksums=None, version=VERSION, source_commit=None):
    """Reject unsafe or unlisted ZIP content before trusted-library inspection."""
    from math_gauge.harness import inspect_release_dataset

    config = load_config(version=version)
    archive = _real_path(archive)
    archive_raw = archive.read_bytes()
    if checksums is not None:
        checksum_raw = _real_path(checksums).read_bytes()
        _require(checksum_raw == f"{_digest(archive_raw)}  {archive.name}\n".encode("ascii"),
                 "Archive checksum differs from SHA256SUMS")
    prefix = "math-gauge-tasks-v" + version + "/"
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


def build_release(destination, *, source_commit, root=ROOT, version=VERSION):
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build", help="Build named assets from an exact clean commit")
    build.add_argument("--out", required=True)
    build.add_argument("--source-commit", required=True)
    build.add_argument("--version", default=VERSION)
    check = sub.add_parser("check", help="Validate checksums, safe ZIP inventory and dataset")
    check.add_argument("--archive", required=True)
    check.add_argument("--checksums", required=True)
    check.add_argument("--source-commit")
    check.add_argument("--version", default=VERSION)
    evaluator = sub.add_parser("evaluator-plan", help="Recover the operator-only release anchor")
    evaluator.add_argument("--out", required=True)
    evaluator.add_argument("--source-commit", required=True)
    evaluator.add_argument("--version", default=VERSION)
    args = parser.parse_args(argv)
    try:
        if args.command == "build":
            result = build_release(args.out, source_commit=args.source_commit, version=args.version)
        elif args.command == "check":
            value = check_release_archive(args.archive, checksums=args.checksums,
                                          version=args.version, source_commit=args.source_commit)
            result = {"release_version": value["release_version"],
                      "dataset_sha256": value["dataset_sha256"],
                      "source_commit": value["source"]["commit"],
                      "cases": value["case_count"], "slots": value["slot_count"],
                      "candidate_calls": 0}
        else:
            config = load_config(version=args.version)
            source_identity(ROOT, args.source_commit, config)
            plan, _ = release_plan(version=args.version)
            out = _real_path(args.out)
            _require(not out.exists(), "Evaluator plan output must be a new file")
            with out.open("xb") as output:
                output.write(_json_bytes(plan))
            result = {"plan_sha256": plan["plan_sha256"], "out": str(out), "candidate_calls": 0}
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
