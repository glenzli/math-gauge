"""Source-bound neutral revision packages and offline answer returns.

Selection and arithmetic belong to neutral_revision/scoring. This module only
projects supplied sources, constructs requests, and preserves external returns.
The exported stdlib helper is generated from these same portable functions.
"""

import copy
import hashlib
import inspect
import json
import re
import shutil
import zipfile
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

from .catalog import candidate_message, relative_name

BUNDLE_SCHEMA = "benchmark.neutral-revision-bundle/v1"
REQUEST_SCHEMA = "benchmark.neutral-revision-request/v1"
RETURN_SCHEMA = "benchmark.neutral-revision-return/v1"
IMPORT_SCHEMA = "benchmark.neutral-revision-import/v1"
CONTROLLER_VERSION = "0.1.0"
STANDARDS_PATH = "protocol/neutral-revision-candidate-standards.md"
INVITATION_PATH = "protocol/neutral-revision-candidate-invitation.md"
EFFECTIVE_STATUSES = ("normal_final", "cutoff_without_final", "maximum_output_exhausted")


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")


def _digest(raw):
    return hashlib.sha256(raw).hexdigest()


def _identity(value):
    return _digest(json.dumps(value, ensure_ascii=False, sort_keys=True,
        separators=(",", ":"), allow_nan=False).encode("utf-8"))


def _descriptor(name, raw):
    relative_name(name)
    return {"path": name, "bytes": len(raw), "sha256": _digest(raw)}


def _read(root, descriptor):
    relative_name(descriptor["path"])
    path = Path(root) / descriptor["path"]
    _require(path.is_file() and not path.is_symlink(), "Missing regular source file: " + descriptor["path"])
    raw = path.read_bytes()
    _require(len(raw) == descriptor["bytes"] and _digest(raw) == descriptor["sha256"],
        "Source bytes changed: " + descriptor["path"])
    return raw


def _write_new(path, raw):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


def inspect_revision_bundle(root):
    root = Path(root).resolve()
    manifest = json.loads((root / "operator/manifest.json").read_bytes())
    _require(manifest.get("schema") == BUNDLE_SCHEMA, "Unsupported neutral revision package")
    _require(manifest["bundle_sha256"] == _identity({k: v for k, v in manifest.items()
        if k != "bundle_sha256"}), "Package manifest changed")
    for descriptor in manifest["files"]:
        _read(root, descriptor)
    task_ids = [row["task_id"] for row in manifest["tasks"]]
    _require(len(task_ids) == len(set(task_ids)), "Repeated task alias")
    _require(all(re.fullmatch(r"R[0-9]{3}", sid) for sid in task_ids), "Invalid task alias")
    return manifest


def _original_request(root, row):
    request = {"task": _read(root, row["task"]).decode("utf-8"),
        "instruction": _read(root, row["instruction"]).decode("utf-8"),
        "files": [{"name": item["name"], "content": _read(root, item["source"]).decode("utf-8")}
            for item in row["provided_files"]]}
    return candidate_message(request)


def _file_section(label, name, raw):
    content = raw.decode("utf-8")
    fence = "`" * (max([2, *(len(value) for value in re.findall(r"`+", content))]) + 1)
    return "\n\n# " + label + "：`" + name + "`\n\n" + fence + "text\n" + content + (
        "" if content.endswith("\n") else "\n") + fence + "\n"


def build_revision_request(root, task_id, *, runtime=None, context_mode="source-bound-replay",
                           source_session_id=None):
    """Build one request; this function never starts a model or resumes a session."""
    root = Path(root).resolve()
    manifest = inspect_revision_bundle(root)
    row = next((row for row in manifest["tasks"] if row["task_id"] == task_id), None)
    _require(row is not None and row["status"] == "ready", "Task is not ready for a new revision")
    _require(context_mode in {"source-bound-replay", "native-session-continuation"}, "Unknown context mode")
    runtime = {} if runtime is None else copy.deepcopy(runtime)
    _require(isinstance(runtime, dict), "Runtime declaration must be an object")
    _require(runtime.get("timeout_seconds", 2700) == 2700, "One revision has a 2700 second limit")
    common = _read(root, manifest["standards"]).decode("utf-8") + "\n\n" + _read(
        root, manifest["invitation"]).decode("utf-8")
    if row.get("previous_answer") is None:
        common += ("\n\n# 原请求的实际状态\n\n此前请求没有正常最终交卷，"
            "没有可提供的原答正文。此状态不判定原数学问题的对错；本轮从完整原题和材料继续。\n")
    if context_mode == "native-session-continuation":
        _require(isinstance(source_session_id, str) and bool(source_session_id.strip()),
            "Native continuation requires the actual source session identifier")
        content = common
    else:
        _require(source_session_id is None, "A replay cannot claim native session continuation")
        content = common + "\n\n---\n\n# 来源绑定的历史材料重放\n\n" + (
            "以下是本题原始材料和你自己的历史作答。这是保留原字节的材料重放，"
            "不是原生会话续接；不得继承其他会话或评审上下文。\n\n# 原题及全部提供材料\n\n")
        content += _original_request(root, row)
        previous = row.get("previous_answer")
        if previous:
            if row["original_submission_status"] in {"normal_final", "active_final"}:
                label = "你此前的完整最终答复（原文，含全部自评）"
            elif row["original_submission_status"] in {"forced_content", "delivery_failure", "cutoff_without_final", "maximum_output_exhausted"}:
                label = "你原请求截止前保留的内容（原请求没有正常最终交卷）"
            else:
                label = "你此前留档的原文（原交付状态未知）"
            content += _file_section(label, "previous-answer.md", _read(root, previous))
        for item in row["previous_files"]:
            content += _file_section("你此前明确交付的附件", item["name"], _read(root, item["source"]))
    request = {"schema": REQUEST_SCHEMA, "bundle_sha256": manifest["bundle_sha256"],
        "task_id": task_id, "context_mode": context_mode, "source_session_id": source_session_id,
        "original_submission_status": row["original_submission_status"],
        "source_response_sha256": row["source_selection"].get("response_sha256"),
        "source_original_text_sha256": (row.get("previous_answer") or {}).get("sha256"),
        "runtime_declaration": runtime, "timeout_seconds": 2700,
        "tool_policy": "local-tools-preinstalled-public-dependencies-no-external-retrieval-no-tool-network",
        "messages": [{"role": "user", "content": content}],
        "parameters": copy.deepcopy(runtime.get("parameters", {})),
        "candidate_directory": row["candidate_directory"],
        "preparation_only": not bool(runtime), "candidate_calls": 0}
    request["request_sha256"] = _identity(request)
    return request


def inspect_revision_collection(bundle_root, collection_root):
    manifest = inspect_revision_bundle(bundle_root)
    root = Path(collection_root).resolve()
    result = json.loads((root / "return.json").read_bytes())
    _require(result.get("schema") == RETURN_SCHEMA and result.get("bundle_sha256") == manifest["bundle_sha256"],
        "Return belongs to a different package")
    tasks = {row["task_id"]: row for row in manifest["tasks"] if row["status"] == "ready"}
    seen = set()
    for row in result["tasks"]:
        _require(row["task_id"] in tasks and row["task_id"] not in seen, "Unknown or repeated returned task")
        seen.add(row["task_id"])
        effective = 0
        for number, attempt in enumerate(row["attempts"], 1):
            _require(effective == 0 and attempt["physical_request_number"] == number,
                "A task continued after its first effective delivery or cutoff")
            status = attempt["status"]
            _require(status in EFFECTIVE_STATUSES + ("system_only_failure",), "Unknown actual delivery status")
            request = json.loads(_read(root, attempt["request"]))
            digest = request.pop("request_sha256")
            _require(digest == _identity(request) and request["bundle_sha256"] == manifest["bundle_sha256"]
                and request["task_id"] == row["task_id"], "Returned request binding changed")
            if status == "system_only_failure":
                _require(attempt["operator_metadata"].get("pure_system_failure_confirmed") is True
                    and bool(attempt["evidence"]), "System-only exclusion requires explicit confirmation and native evidence")
                _require(attempt["effective_attempt_number"] is None, "A system-only failure is not a model attempt")
            else:
                effective += 1
                _require(attempt["effective_attempt_number"] == 1, "Only one effective neutral revision is permitted")
            if attempt["response"] is not None:
                response = _read(root, attempt["response"])
                if status == "normal_final":
                    _require(bool(response.strip()), "A normal final must contain the complete actual reply")
                response.decode("utf-8")
            else:
                _require(status != "normal_final", "A normal final cannot be invented from missing text")
            for item in attempt["attachments"] + attempt["evidence"]:
                _read(root, item["source"])
    return result


def collect_revision_attempt(bundle_root, collection_root, request_path, *, status,
                             response_path=None, attachments=(), evidence=(), metadata=None):
    """Append actual raw output. Transport and isolation fields remain declarations."""
    manifest = inspect_revision_bundle(bundle_root)
    root = Path(collection_root).resolve()
    _require(not root.is_relative_to(Path(bundle_root).resolve()), "Keep returns outside the immutable package")
    request_raw = Path(request_path).read_bytes()
    request = json.loads(request_raw)
    digest = request.pop("request_sha256")
    _require(digest == _identity(request) and request["bundle_sha256"] == manifest["bundle_sha256"],
        "Request was not issued from this package")
    ready = {row["task_id"] for row in manifest["tasks"] if row["status"] == "ready"}
    _require(request["task_id"] in ready and request.get("preparation_only") is False,
        "Collect only an actual request with its runtime declaration")
    metadata = {} if metadata is None else copy.deepcopy(metadata)
    _require(isinstance(metadata, dict), "Operator metadata must be an object")
    _require(status in EFFECTIVE_STATUSES + ("system_only_failure",), "Unknown actual delivery status")
    if status == "system_only_failure":
        _require(metadata.get("pure_system_failure_confirmed") is True and bool(evidence),
            "System-only exclusion requires explicit confirmation and native evidence")
    header = root / "return.json"
    if header.exists():
        result = inspect_revision_collection(bundle_root, root)
    else:
        result = {"schema": RETURN_SCHEMA, "bundle_sha256": manifest["bundle_sha256"],
            "model_id": manifest["model_id"], "created_at": datetime.now(timezone.utc).isoformat(),
            "operator_declarations_not_runtime_certification": True, "tasks": []}
    task = next((row for row in result["tasks"] if row["task_id"] == request["task_id"]), None)
    if task is None:
        task = {"task_id": request["task_id"], "attempts": []}
        result["tasks"].append(task)
    _require(not any(row["status"] in EFFECTIVE_STATUSES for row in task["attempts"]),
        "Stop after the first effective attempt; no quality or maximum-output retry")
    number = len(task["attempts"]) + 1
    prefix = request["task_id"] + "/physical-" + str(number) + "/"
    files = {prefix + "request.json": request_raw}
    response = None
    if response_path is not None:
        raw = Path(response_path).read_bytes()
        raw.decode("utf-8")
        _require(status != "normal_final" or bool(raw.strip()), "A normal final cannot be empty")
        files[prefix + "response.md"] = raw
        response = _descriptor(prefix + "response.md", raw)
    _require(status != "normal_final" or response is not None, "A normal final requires its full actual text")
    inventories = []
    for kind, paths in (("attachments", attachments), ("evidence", evidence)):
        inventory = []
        for path in paths:
            path = Path(path)
            name = path.name
            relative_name(name)
            destination = prefix + kind + "/" + name
            _require(destination not in files, "Repeated returned filename")
            raw = path.read_bytes()
            files[destination] = raw
            inventory.append({"name": name, "source": _descriptor(destination, raw)})
        inventories.append(inventory)
    attempt = {"physical_request_number": number,
        "effective_attempt_number": None if status == "system_only_failure" else 1,
        "status": status, "response": response, "request": _descriptor(prefix + "request.json", request_raw),
        "attachments": inventories[0], "evidence": inventories[1], "operator_metadata": metadata,
        "collected_at": datetime.now(timezone.utc).isoformat()}
    for name, raw in files.items():
        _write_new(root / name, raw)
    task["attempts"].append(attempt)
    root.mkdir(parents=True, exist_ok=True)
    header.write_bytes(_json_bytes(result))
    inspect_revision_collection(bundle_root, root)
    return attempt


def pack_revision_return(bundle_root, collection_root, archive_path):
    result = inspect_revision_collection(bundle_root, collection_root)
    root, destination = Path(collection_root).resolve(), Path(archive_path).resolve()
    _require(not destination.is_relative_to(root), "Return archive must be outside the collection")
    names = {"return.json"}
    for row in result["tasks"]:
        for attempt in row["attempts"]:
            names.add(attempt["request"]["path"])
            if attempt["response"]:
                names.add(attempt["response"]["path"])
            names.update(item["source"]["path"] for item in attempt["attachments"] + attempt["evidence"])
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(destination, "x", compression=zipfile.ZIP_DEFLATED) as archive:
        for name in sorted(names):
            archive.writestr(name, (root / name).read_bytes())
    return _descriptor(destination.name, destination.read_bytes())


def import_revision_return(bundle_root, archive_path, destination):
    """Import as pending review evidence, never as authenticated CLI or a score."""
    manifest = inspect_revision_bundle(bundle_root)
    destination = Path(destination).resolve()
    _require(not destination.exists(), "Import destination already exists")
    destination.mkdir(parents=True)
    try:
        with zipfile.ZipFile(archive_path) as archive:
            names = archive.namelist()
            _require(len(names) == len(set(names)), "Repeated return archive entry")
            for name in names:
                relative_name(name)
                _write_new(destination / "original-return" / name, archive.read(name))
        result = inspect_revision_collection(bundle_root, destination / "original-return")
        selected = {row["task_id"]: row for row in manifest["tasks"]}
        records = []
        for row in result["tasks"]:
            source = selected[row["task_id"]]
            records.append({"task_id": row["task_id"], "case_id": source["case_id"],
                "source_selection": source["source_selection"], "attempts": copy.deepcopy(row["attempts"]),
                "normal_final": next((item["response"] for item in row["attempts"]
                    if item["status"] == "normal_final"), None),
                "review_status": "pending_mathematical_and_operational_review"})
        imported = {"schema": IMPORT_SCHEMA, "bundle_sha256": manifest["bundle_sha256"],
            "model_id": manifest["model_id"], "archive": _descriptor(Path(archive_path).name, Path(archive_path).read_bytes()),
            "returned_tasks": len(records), "records": records, "candidate_calls": 0,
            "scores_changed": False, "human_mathematical_approval": False,
            "runtime_certification": False, "original_return_directory": "original-return"}
        _write_new(destination / "import.json", _json_bytes(imported))
        return imported
    except BaseException:
        shutil.rmtree(destination)
        raise


def _controller_main():
    import argparse
    parser = argparse.ArgumentParser(description="Offline neutral revision requests and source-bound answer returns")
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("check", "request", "collect", "pack", "import"):
        sub = commands.add_parser(name)
        sub.add_argument("--bundle", default=str(Path(__file__).resolve().parents[1]))
        if name == "request":
            sub.add_argument("--task", required=True)
            sub.add_argument("--runtime")
            sub.add_argument("--mode", choices=("source-bound-replay", "native-session-continuation"), default="source-bound-replay")
            sub.add_argument("--source-session")
            sub.add_argument("--out", required=True)
        if name in {"collect", "pack"}:
            sub.add_argument("--returns", required=True)
        if name == "collect":
            sub.add_argument("--request", required=True)
            sub.add_argument("--status", choices=EFFECTIVE_STATUSES + ("system_only_failure",), required=True)
            sub.add_argument("--response")
            sub.add_argument("--attachment", action="append", default=[])
            sub.add_argument("--evidence", action="append", default=[])
            sub.add_argument("--metadata")
        if name == "pack":
            sub.add_argument("--out", required=True)
        if name == "import":
            sub.add_argument("--archive", required=True)
            sub.add_argument("--out", required=True)
    args = parser.parse_args()
    try:
        if args.command == "check":
            manifest = inspect_revision_bundle(args.bundle)
            result = {"bundle_sha256": manifest["bundle_sha256"], "model_id": manifest["model_id"],
                "counts": manifest["counts"], "candidate_calls": 0}
        elif args.command == "request":
            runtime = json.loads(Path(args.runtime).read_bytes()) if args.runtime else None
            result = build_revision_request(args.bundle, args.task, runtime=runtime,
                context_mode=args.mode, source_session_id=args.source_session)
            _require(not Path(args.out).resolve().is_relative_to(Path(args.bundle).resolve()),
                "Keep issued requests outside the immutable package")
            _write_new(args.out, _json_bytes(result))
            result = {"task_id": result["task_id"], "request_sha256": result["request_sha256"],
                "preparation_only": result["preparation_only"], "out": str(Path(args.out).resolve())}
        elif args.command == "collect":
            metadata = json.loads(Path(args.metadata).read_bytes()) if args.metadata else None
            result = collect_revision_attempt(args.bundle, args.returns, args.request, status=args.status,
                response_path=args.response, attachments=args.attachment, evidence=args.evidence, metadata=metadata)
        elif args.command == "pack":
            result = pack_revision_return(args.bundle, args.returns, args.out)
        else:
            result = import_revision_return(args.bundle, args.archive, args.out)
        print(json.dumps(result, ensure_ascii=False, indent=2))
    except (ValueError, OSError, KeyError, TypeError, zipfile.BadZipFile) as error:
        parser.error(str(error))


def portable_revision_source():
    functions = (relative_name, candidate_message, _require, _json_bytes, _digest, _identity, _descriptor,
        _read, _write_new, inspect_revision_bundle, _original_request, _file_section, build_revision_request,
        inspect_revision_collection, collect_revision_attempt, pack_revision_return, import_revision_return,
        _controller_main)
    header = ('#!/usr/bin/env python3\n"""Offline operator helper. Never calls models. Generated from the shared source."""\n'
        'import copy, hashlib, json, re, shutil, zipfile\nfrom pathlib import Path, PurePosixPath\n'
        'from datetime import datetime, timezone\n')
    constants = "\n".join(name + " = " + repr(globals()[name]) for name in
        ("BUNDLE_SCHEMA", "REQUEST_SCHEMA", "RETURN_SCHEMA", "IMPORT_SCHEMA", "EFFECTIVE_STATUSES"))
    return (header + constants + "\n\n" + "\n\n".join(inspect.getsource(function).rstrip()
        for function in functions) + '\n\nif __name__ == "__main__":\n    _controller_main()\n').encode("utf-8")


def export_revision_bundle(selection, public_root, private_root, destination, *, exclude=False):
    """Materialize only candidate sources and keep selection details operator-side."""
    from .catalog import Suite
    from .records import evidence_bytes
    roots = {"public": Path(public_root).resolve(), "private": Path(private_root).resolve()}
    destination = Path(destination).resolve()
    _require(not destination.exists(), "Package destination already exists")
    _require(not destination.is_relative_to(roots["public"]), "Combined private packages cannot be placed in the public repository")
    destination.mkdir(parents=True)
    contents = {}

    def put(name, raw):
        _require(name not in contents, "Repeated package path")
        contents[name] = raw
        return _descriptor(name, raw)

    def source(item):
        _require(item.get("scope") in roots, "Source requires its explicit public/private scope")
        return evidence_bytes(roots[item["scope"]], {k: item[k] for k in ("path", "bytes", "sha256")})

    standards = put("candidate/common-standards.md", (roots["public"] / STANDARDS_PATH).read_bytes())
    invitation = put("candidate/common-invitation.md", (roots["public"] / INVITATION_PATH).read_bytes())
    put("tools/revision.py", portable_revision_source())
    put("README.md", _OPERATOR_GUIDE.encode("utf-8"))
    put("operator/runtime-template.json", _json_bytes({"timeout_seconds": 2700, "model_label": selection["model_id"],
        "backend_sku": None, "backend_identity_evidence": None, "parameters": {},
        "note": "Fill the actual native model/effort and limits; preserve unknowns. No invocation is performed by these tools."}))
    rows, suites = [], {}
    for number, selected in enumerate(selection["selection"], 1):
        selected = copy.deepcopy(selected)
        task_id = f"R{number:03d}"
        # The complete source paths/grades remain in the non-exported evaluator
        # index. A portable operator needs only opaque identities and aliases.
        source_binding = {key: selected.get(key) for key in
            ("response_sha256", "review_sha256", "family_id", "subcategory")}
        source_binding["original_text_sha256"] = (selected.get("original_answer") or {}).get("sha256")
        row = {"task_id": task_id, "case_id": selected["case_id"], "source_selection": source_binding,
            "status": "excluded_partial" if exclude else "completed_reused" if selected.get("completed_adoption") else "ready"}
        rows.append(row)
        if row["status"] != "ready":
            continue
        known_blank_failure = selected.get("original_submission_status") == "blank" and selected.get("response_sha256") is None
        if not selected.get("original_answer") and not known_blank_failure:
            row["status"] = "source_unavailable"
            row["source_note"] = "Missing original text is not a mathematical error; no replacement final was created."
            continue
        scope = selected["source_case"]["scope"]
        if scope not in suites:
            suites[scope] = Suite.load(roots[scope] / "cases")
        suite = suites[scope]
        case = suite.cases[selected["case_id"]]
        request = suite.request(case)
        _require(source(selected["source_case"]) == request["task"].encode("utf-8"),
            "Source selection and current mathematical task differ")
        _require(not str(selected.get("subcategory", "")).startswith("lean")
            and selected["case_id"] != "MG-C003", "Neutral non-Lean revision excludes all Lean and C003 tasks")
        try:
            previous_raw = source(selected["original_answer"]) if selected.get("original_answer") else None
            previous_files = []
            for item in selected.get("original_answer_attachments", []):
                descriptor = item.get("source", item)
                name = item.get("name", PurePosixPath(descriptor["path"]).name)
                relative_name(name)
                previous_files.append((name, source(descriptor)))
        except (ValueError, FileNotFoundError):
            row["status"] = "source_unavailable"
            row["source_note"] = "An original answer or explicitly delivered attachment is unavailable; no partial input was exported."
            continue
        if previous_raw is not None and selected.get("response_sha256") is not None:
            _require(_digest(previous_raw) == selected["response_sha256"],
                "Selection and original reply differ")
        base = f"candidate/tasks/{task_id}/"
        row.update(candidate_directory=base.rstrip("/"),
            task=put(base + "task.md", request["task"].encode("utf-8")),
            instruction=put(base + "instruction.txt", request["instruction"].encode("utf-8")),
            provided_files=[], previous_files=[], original_submission_status=selected.get("original_submission_status") or "unknown")
        for item in request["files"]:
            row["provided_files"].append({"name": item["name"],
                "source": put(base + "materials/" + item["name"], item["content"].encode("utf-8"))})
        row["previous_answer"] = put(base + "previous-answer.md", previous_raw) if previous_raw is not None else None
        for name, raw in previous_files:
            row["previous_files"].append({"name": name,
                "source": put(base + "previous-files/" + name, raw)})
        context = {key: row[key] for key in ("task_id", "task", "instruction", "provided_files", "previous_answer",
            "previous_files", "original_submission_status")}
        put(base + "context.json", _json_bytes(context))
    counts = {status: sum(row["status"] == status for row in rows)
        for status in ("ready", "completed_reused", "source_unavailable", "excluded_partial")}
    put("operator/return-template.json", _json_bytes({"schema": RETURN_SCHEMA, "bundle_sha256": None,
        "model_id": selection["model_id"], "tasks": [{"task_id": row["task_id"], "attempts": []}
            for row in rows if row["status"] == "ready"]}))
    manifest = {"schema": BUNDLE_SCHEMA, "controller_version": CONTROLLER_VERSION,
        "model_id": selection["model_id"], "record_id": selection.get("record_id"),
        "local_only": True, "candidate_calls": 0, "timeout_seconds": 2700,
        "source_record_sha256": (selection.get("source_record") or {}).get("sha256"),
        "standards": standards, "invitation": invitation,
        "tasks": rows, "counts": counts, "files": [_descriptor(name, raw) for name, raw in sorted(contents.items())]}
    manifest["bundle_sha256"] = _identity(manifest)
    for name, raw in contents.items():
        _write_new(destination / name, raw)
    _write_new(destination / "operator/manifest.json", _json_bytes(manifest))
    inspect_revision_bundle(destination)
    return manifest


_OPERATOR_GUIDE = """# Neutral revision: local operator package

This package contains private benchmark material. Keep it local or transfer it
privately to the chosen execution environment. The candidate receives one task
directory and the two common candidate texts, or only that task's constructed
request. Keep operator/, tools/, selection details, grades, reviews, references,
other candidates' answers and unrelated session history outside its context.

Every task is independent. Use its actual source native session when a clean
continuation is possible; record that session identifier and its exact context.
Otherwise use the explicitly marked source-bound replay. The original complete
reply includes its self-assessment. Explicitly delivered files are included;
unsubmitted workspace drafts do not supplement it. Cutoff content retains its
actual nonfinal state. Missing original text is left unavailable.

Allow local tools and preinstalled public dependencies. Forbid external retrieval
and tool networking. Model-service/authentication traffic is separate. Do not
require Lean. Freeze actual model/effort, native/broker/outer limits and unknowns
in a runtime JSON before invocation. Dot's unknown backend remains unknown.
The helper never calls a model or reads credentials.

```
python3 tools/revision.py check
python3 tools/revision.py request --task R001 --runtime ACTUAL-RUNTIME.json --out REQUEST.json
# Or add --mode native-session-continuation --source-session ACTUAL-SOURCE-SESSION
```

Submit that request with your existing native interface/controller, outside this
package. Each task has one effective revision and a 2700 second limit. Stop at
the first normal final or cutoff; never retry mathematical quality or maximum
output exhaustion. A proven pure system failure can be excluded only under the
current rule, retaining its physical request and original native evidence.

Preserve the complete final reply including all self-assessment, plus every file
it explicitly submits. Record actual status and timing, unknown fields as null.
Files in --attachment are actual delivered components; --evidence preserves
native events, request/terminal receipts and other operational sources.

```
python3 tools/revision.py collect --returns RETURNS --request REQUEST.json --status normal_final --response COMPLETE-RAW-REPLY.md --attachment DELIVERED-FILE.md --metadata ACTUAL-METADATA.json
python3 tools/revision.py pack --returns RETURNS --out RETURN.zip
python3 tools/revision.py import --archive RETURN.zip --out IMPORTED
```

For cutoff use cutoff_without_final or maximum_output_exhausted and preserve any
actual cutoff text. Never label it a normal final. For a proven system-only
failure use system_only_failure, --evidence, and metadata with
pure_system_failure_confirmed=true. All supplied metadata remains an operator
declaration pending source review; collection/import does not authenticate a
backend, isolation, mathematical correctness or human approval. Import produces
neutral-revision-import/v1 with exact raw files and pending-review records; it
does not fabricate an old CLI record, grade an answer, or change a score.

The common standards and invitation are byte-identical to the new-call recovery
study texts. Reused historical neutral-pilot calls retain their actual different
prompts and provenance in the adoption record; do not rerun completed cells.
"""
