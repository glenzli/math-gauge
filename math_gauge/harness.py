"""Portable, immutable controller bundles; never invokes a candidate model.

Only the explicit solver projection crosses this boundary.  The complete plan
is retained in a separate evaluator directory, never nested inside the bundle.
The small portable functions below are also the source of the bundled stdlib
controller, so its conversation construction shares one implementation.
"""

import copy
import hashlib
import inspect
import json
import math
import re
import shutil
import uuid
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

from .benchmarks import identity, select_slots, validate_plan
from .catalog import Suite, candidate_message, digest_bytes, relative_name, write_json

BUNDLE_SCHEMA = "math-gauge.harness-bundle/v1"
CONTROLLER_VERSION = "math-gauge.portable-controller/v1"
PARAMETER_NAMES = ("model", "reasoning_effort", "temperature", "top_p", "seed",
                   "max_output_tokens", "max_completion_tokens")
_MANIFEST_KEYS = {
    "schema", "controller_version", "bundle_sha256", "plan_id", "plan_sha256",
    "suite", "runner_sha256", "runtime_sha256", "protocol_version", "runtime_frozen",
    "preparation_only", "targets", "planned", "exported_slots", "selected_slot_ids",
    "slots", "cases", "prompts", "execution", "files_sha256",
}
DATASET_SCHEMA = "math-gauge.release-dataset/v1"
RUN_SCHEMA = "math-gauge.harness-run/v2"
RELEASE_CONTROLLER = "math-gauge.release-controller/v1"
RELEASE_SUBMISSION = "math-gauge.harness-submission/v2"
_RELEASE_TARGETS = ("proofs", "lean-audit", "lean-construction", "chapters",
                    "repeat", "neutral", "stance", "core", "all")
_DATASET_KEYS = {"schema", "controller_version", "release_version", "dataset_sha256",
                 "base_plan_sha256", "suite", "runner_sha256", "protocol_version", "planned",
                 "exported_slots", "selected_slot_ids", "slots", "cases", "prompts",
                 "target_slot_ids", "files_sha256"}
_RUN_KEYS = {"schema", "controller_version", "run_sha256", "run_id", "created_at",
             "dataset_sha256", "base_plan_sha256", "runtime", "runtime_sha256",
             "runtime_frozen", "preparation_only", "targets", "selected_slot_ids",
             "planned", "execution", "files_sha256"}
_RELEASE_CONTEXT = {"independent": "fresh", "followup": "branch-history-only",
                    "external_correctness_feedback": False, "tools_allowed": []}


def _h_require(condition, message):
    if not condition:
        raise ValueError(message)


def _h_digest(raw):
    return hashlib.sha256(raw).hexdigest()


def _h_identity(value):
    return _h_digest(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                separators=(",", ":"), allow_nan=False).encode("utf-8"))


def _h_hash(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _h_object(value, keys, description):
    _h_require(isinstance(value, dict) and set(value) == set(keys),
               "Unexpected fields in " + description)


def _h_relative(value):
    _h_require(isinstance(value, str) and value and "\\" not in value
               and "\0" not in value, "Unsafe bundle path")
    path = PurePosixPath(value)
    _h_require(path.parts and not path.is_absolute() and ".." not in path.parts
               and str(path) == value, "Unsafe bundle path")
    return path


def _h_path(value):
    path = Path(value).expanduser().absolute()
    # Only the two exact macOS system aliases are canonicalized. User-created
    # symlinks at any other root or ancestor remain forbidden.
    for alias in ("var", "tmp"):
        prefix = Path("/") / alias
        if (path.is_relative_to(prefix) and prefix.is_symlink()
                and prefix.resolve() == Path("/private") / alias):
            path = Path("/private") / alias / path.relative_to(prefix)
    _h_require(all(not part.is_symlink() for part in (path, *path.parents)),
               "Harness paths cannot pass through a symlink")
    return path.resolve()


def _h_root(root):
    root = _h_path(root)
    _h_require(root.is_dir(),
               "Bundle root must be a real directory")
    return root


def _h_file(root, name):
    relative = _h_relative(name)
    current = root
    for part in relative.parts:
        current = current / part
        _h_require(not current.is_symlink(), "Symlinks are not permitted in a bundle")
    _h_require(current.is_file() and current.resolve().is_relative_to(root),
               "Missing or escaping bundle file: " + name)
    return current


def _h_parameters(value):
    _h_require(isinstance(value, dict) and set(value) <= set(PARAMETER_NAMES),
               "Only explicit generation parameters may be exported")
    for key, item in value.items():
        if key in {"model", "reasoning_effort"}:
            valid = isinstance(item, str) and bool(item)
        elif key in {"max_output_tokens", "max_completion_tokens"}:
            valid = type(item) is int and item > 0
        elif key == "seed":
            valid = type(item) is int
        else:
            valid = type(item) in (int, float) and math.isfinite(item)
        _h_require(valid, "Generation parameters must have scalar values of the declared type")
    return dict(value)


def _h_execution(value, case_ids):
    _h_object(value, {"parameters", "case_parameters", "budget", "retry", "system_prompt",
                      "context_policy", "model_label"}, "execution projection")
    _h_parameters(value["parameters"])
    _h_require(isinstance(value["case_parameters"], dict)
               and set(value["case_parameters"]) <= set(case_ids),
               "Unknown case in generation parameters")
    for item in value["case_parameters"].values():
        _h_parameters(item)
    budget = value["budget"]
    _h_require(isinstance(budget, dict) and set(budget) <= {
        "timeout_seconds", "output_tokens", "max_transport_attempts", "max_total_tokens"},
        "Unexpected fields in budget projection")
    for key, item in budget.items():
        valid = type(item) in (int, float) and math.isfinite(item)
        if key in {"output_tokens", "max_transport_attempts"}:
            valid = valid and type(item) is int
        valid = valid and (item > 0 if key in {"timeout_seconds", "output_tokens"} else item >= 0)
        _h_require(valid, "Invalid frozen execution budget")
    if "output_tokens" in budget:
        _h_require(value["parameters"].get("max_output_tokens") == budget["output_tokens"],
                   "Generation output limit differs from the frozen budget")
    retry = value["retry"]
    _h_object(retry, {"max_attempts", "wait_seconds", "retryable_exit_codes"}, "retry projection")
    _h_require(retry["max_attempts"] == 2 and type(retry["max_attempts"]) is int
               and type(retry["wait_seconds"]) in (int, float)
               and math.isfinite(retry["wait_seconds"]) and 0 <= retry["wait_seconds"] <= 60
               and isinstance(retry["retryable_exit_codes"], list)
               and all(type(x) is int for x in retry["retryable_exit_codes"]),
               "Invalid frozen retry policy")
    _h_require(value["system_prompt"] is None or isinstance(value["system_prompt"], str),
               "System prompt must be frozen text")
    _h_require(value["model_label"] is None or isinstance(value["model_label"], str),
               "Model label must be text")
    _h_require(value["context_policy"] == {
        "independent": "fresh", "followup": "branch-history-only",
        "external_correctness_feedback": False, "tools_allowed": []},
        "Unexpected candidate context policy")


def _h_message(request):
    """Validate the projection, then use the canonical shared message builder."""
    _h_object(request, {"schema", "case_id", "case_version", "track", "instruction",
                        "task", "files"}, "case request")
    _h_require(request["schema"] == "math-gauge.request/v1"
               and request["track"] in {"determinate", "alignment", "exploration"}
               and all(isinstance(request[k], str) for k in
                       ("case_id", "case_version", "task", "instruction"))
               and isinstance(request["files"], list), "Invalid case request")
    for item in request["files"]:
        _h_object(item, {"name", "content"}, "candidate attachment")
        _h_relative(item["name"])
    return candidate_message(request)


def _inspect_bundle_contents(root):
    """Check a relocated bundle without reading any repository or evaluator files.

    Hashes establish internal integrity, not provider authentication or origin.
    An evaluator must additionally bind this manifest to its frozen plan.
    """
    root = _h_root(root)
    value = json.loads(_h_file(root, "manifest.json").read_bytes())
    _h_object(value, _MANIFEST_KEYS, "bundle manifest")
    _h_require(value["schema"] == BUNDLE_SCHEMA
               and value["controller_version"] == CONTROLLER_VERSION,
               "Unsupported harness bundle version")
    _h_require(_h_hash(value["bundle_sha256"]) and value["bundle_sha256"] == _h_identity(
        {k: v for k, v in value.items() if k != "bundle_sha256"}),
        "Frozen harness manifest changed")
    for key in ("plan_sha256", "runner_sha256", "runtime_sha256"):
        _h_require(_h_hash(value[key]), "Invalid frozen identity: " + key)
    _h_object(value["suite"], {"id", "version", "sha256"}, "suite binding")
    _h_require(_h_hash(value["suite"]["sha256"])
               and all(isinstance(value["suite"][k], str) and value["suite"][k]
                       for k in ("id", "version"))
               and isinstance(value["plan_id"], str) and value["plan_id"]
               and isinstance(value["protocol_version"], str) and value["protocol_version"],
               "Invalid frozen plan or suite binding")
    _h_require(type(value["runtime_frozen"]) is bool
               and type(value["preparation_only"]) is bool
               and value["preparation_only"] == (not value["runtime_frozen"]),
               "Preparation-only status changed")
    _h_require(isinstance(value["targets"], list) and value["targets"]
               and len(value["targets"]) == len(set(value["targets"]))
               and set(value["targets"]) <= {"proofs", "lean-audit", "lean-construction", "chapters",
                                             "repeat", "neutral", "stance", "core", "all"},
               "Invalid export target projection")
    _h_projection(root, value, {"CONTROLLER.md", "controller.py", "submission-template.json"})
    template = json.loads(_h_file(root, "submission-template.json").read_bytes())
    _h_object(template, {"schema", "bundle_sha256", "plan_sha256", "runtime_sha256", "origin",
                         "fixture_only", "declared_external_calls", "slots"}, "submission template")
    _h_require(template == {"schema": "math-gauge.harness-submission/v1",
        "bundle_sha256": None, "plan_sha256": value["plan_sha256"],
        "runtime_sha256": value["runtime_sha256"], "origin": "fixture", "fixture_only": True,
        "declared_external_calls": 0, "slots": []}, "Submission template changed")
    return value


def _h_projection(root, value, expected_files):
    """Shared candidate/schedule allowlist for generic releases and v1 bundles."""
    expected_files = set(expected_files)
    _h_object(value["planned"], {"papers", "independent_slots", "neutral_slots", "stance_slots",
                                "all_slots", "selected_slots"}, "fixed denominator")
    planned = value["planned"]
    _h_require(all(type(x) is int and x >= 0 for x in planned.values())
               and planned["papers"] > 0 and planned["independent_slots"] == 3 * planned["papers"]
               and planned["all_slots"] == planned["independent_slots"] + planned["neutral_slots"]
                                               + planned["stance_slots"]
               and planned["selected_slots"] <= planned["all_slots"],
               "Invalid fixed benchmark denominator")
    _h_require(isinstance(value["cases"], list) and value["cases"]
               and isinstance(value["slots"], list) and value["slots"]
               and isinstance(value["prompts"], list), "Missing bundle projection")
    case_ids = []
    for case in value["cases"]:
        _h_object(case, {"case_id", "case_version", "request_sha256", "candidate_message_sha256",
                         "request_path", "candidate_message_path", "task_path", "instruction_path",
                         "files"}, "case projection")
        cid = case["case_id"]
        _h_require(isinstance(cid, str) and re.fullmatch(r"[A-Za-z0-9_-]+", cid)
                   and cid not in case_ids and isinstance(case["case_version"], str)
                   and case["case_version"], "Invalid projected case identity")
        case_ids.append(cid)
        base = "cases/" + cid + "/"
        for key, suffix in (("request_path", "request.json"),
                            ("candidate_message_path", "candidate-message.md"),
                            ("task_path", "task.md"), ("instruction_path", "instruction.txt")):
            _h_require(case[key] == base + suffix, "Case projection path changed")
            expected_files.add(case[key])
        request = json.loads(_h_file(root, case["request_path"]).read_bytes())
        message = _h_message(request)
        _h_require(request["case_id"] == cid and request["case_version"] == case["case_version"]
                   and _h_hash(case["request_sha256"])
                   and _h_digest(json.dumps(request, ensure_ascii=False, sort_keys=True).encode("utf-8"))
                   == case["request_sha256"], "Frozen candidate request changed")
        _h_require(_h_hash(case["candidate_message_sha256"])
                   and _h_file(root, case["candidate_message_path"]).read_bytes() == message.encode("utf-8")
                   and _h_digest(message.encode("utf-8")) == case["candidate_message_sha256"]
                   and _h_file(root, case["task_path"]).read_bytes() == request["task"].encode("utf-8")
                   and _h_file(root, case["instruction_path"]).read_bytes() == request["instruction"].encode("utf-8"),
                   "Candidate message, task or instruction changed")
        _h_require(isinstance(case["files"], list) and len(case["files"]) == len(request["files"]),
                   "Candidate attachment inventory changed")
        for descriptor, attachment in zip(case["files"], request["files"]):
            _h_object(descriptor, {"name", "path", "sha256", "bytes"}, "attachment descriptor")
            _h_require(descriptor["name"] == attachment["name"]
                       and descriptor["path"] == base + "files/" + attachment["name"],
                       "Attachment target changed")
            raw = _h_file(root, descriptor["path"]).read_bytes()
            _h_require(raw == attachment["content"].encode("utf-8")
                       and type(descriptor["bytes"]) is int and len(raw) == descriptor["bytes"]
                       and _h_digest(raw) == descriptor["sha256"], "Candidate attachment bytes changed")
            expected_files.add(descriptor["path"])
    slots, earlier, ordinals = {}, set(), []
    for slot in value["slots"]:
        common = {"slot_id", "case_id", "kind", "context", "parent_slot", "message_id", "ordinal_per_model"}
        _h_require(isinstance(slot, dict), "Invalid projected slot")
        independent = slot.get("kind") == "independent"
        _h_object(slot, common | ({"attempt_label"} if independent else {"arm", "round"}), "slot projection")
        sid, cid = slot["slot_id"], slot["case_id"]
        _h_require(isinstance(sid, str) and sid not in earlier and cid in case_ids
                   and type(slot["ordinal_per_model"]) is int and slot["ordinal_per_model"] > 0,
                   "Invalid projected slot identity")
        if independent:
            _h_require(slot["attempt_label"] in {"A1", "A2", "A3"}
                       and sid == cid + ":" + slot["attempt_label"] and slot["context"] == "fresh"
                       and slot["parent_slot"] is None and slot["message_id"] is None,
                       "Independent slots require fresh, unrelated contexts")
        else:
            arm, rnd = slot["arm"], slot["round"]
            parent = cid + ":A1" if rnd == 1 else cid + ":" + str(arm) + ":1"
            _h_require(slot["kind"] == "followup" and arm in {"neutral", "affirm", "deny"}
                       and type(rnd) is int and rnd in (1, 2) and sid == f"{cid}:{arm}:{rnd}"
                       and slot["context"] == "branch-history-only" and slot["parent_slot"] == parent
                       and parent in earlier and slot["message_id"] == sid,
                       "Followup dependency crosses its frozen branch")
        slots[sid] = slot
        earlier.add(sid)
        ordinals.append(slot["ordinal_per_model"])
    _h_require(ordinals == sorted(set(ordinals))
               and value["selected_slot_ids"] == list(slots)
               and type(value["exported_slots"]) is int and value["exported_slots"] == len(slots)
               and len(slots) <= planned["selected_slots"]
               and set(case_ids) == {s["case_id"] for s in slots.values()},
               "Export slot order, inventory or fixed denominator changed")
    prompt_ids = set()
    for prompt in value["prompts"]:
        _h_object(prompt, {"message_id", "content", "content_sha256"}, "followup prompt")
        sid = prompt["message_id"]
        _h_require(isinstance(sid, str) and sid not in prompt_ids and sid in slots
                   and slots[sid]["kind"] == "followup" and isinstance(prompt["content"], str)
                   and _h_digest(prompt["content"].encode("utf-8")) == prompt["content_sha256"],
                   "Frozen followup prompt changed")
        prompt_ids.add(sid)
    _h_require(prompt_ids == {sid for sid, slot in slots.items() if slot["kind"] == "followup"},
               "Frozen followup prompt coverage changed")
    _h_execution(value["execution"], case_ids)
    inventory = value["files_sha256"]
    _h_require(isinstance(inventory, dict) and set(inventory) == expected_files,
               "Bundle file allowlist changed")
    _h_require(len({name.casefold() for name in inventory}) == len(inventory),
               "Bundle paths must be unique on case-insensitive filesystems")
    expected_dirs = set()
    for name, digest in inventory.items():
        _h_relative(name)
        _h_require(_h_hash(digest) and _h_digest(_h_file(root, name).read_bytes()) == digest,
                   "Frozen bundle file changed: " + name)
        expected_dirs.update(str(p) for p in PurePosixPath(name).parents if str(p) != ".")
    for path in root.rglob("*"):
        _h_require(not path.is_symlink(), "Symlinks are not permitted in a bundle")
        name = path.relative_to(root).as_posix()
        _h_require((path.is_file() and (name == "manifest.json" or name in inventory))
                   or (path.is_dir() and name in expected_dirs),
                   "Unlisted file or directory in bundle: " + name)
    return value


def inspect_bundle(root):
    """Validate portable contents without loading code from the supplied bundle."""
    try:
        return _inspect_bundle_contents(root)
    except (KeyError, TypeError, UnicodeError, json.JSONDecodeError) as error:
        raise ValueError("Malformed portable harness bundle") from error


def build_request(root, slot_id, answers=None):
    """Build one exact conversation; answers contain only this slot's ancestors.

    The caller submits this object to its chosen model. This function performs
    no transport and never substitutes composed KEEP/FULL material for raw text.
    """
    bundle = inspect_bundle(root)
    return _h_build_request(_h_root(root), bundle, slot_id, answers)


def _h_build_request(root, bundle, slot_id, answers=None):
    """One conversation renderer, shared by every portable export version."""
    slots = {s["slot_id"]: s for s in bundle["slots"]}
    _h_require(slot_id in slots, "Slot is outside this exported projection")
    slot = slots[slot_id]
    ancestors, parent = [], slot["parent_slot"]
    while parent is not None:
        ancestors.insert(0, parent)
        parent = slots[parent]["parent_slot"]
    answers = {} if answers is None else answers
    _h_require(isinstance(answers, dict) and set(answers) == set(ancestors),
               "Provide exactly the required ancestor answers; unrelated histories are forbidden")
    raw_answers = {}
    for sid, content in answers.items():
        if isinstance(content, bytes):
            try:
                content = content.decode("utf-8")
            except UnicodeDecodeError as error:
                raise ValueError("Ancestor answer must be readable UTF-8") from error
        _h_require(isinstance(content, str) and content.strip(),
                   "Ancestor answer must be readable UTF-8")
        raw_answers[sid] = content
    case = next(c for c in bundle["cases"] if c["case_id"] == slot["case_id"])
    initial = _h_file(root, case["candidate_message_path"]).read_bytes().decode("utf-8")
    execution = bundle["execution"]
    messages = []
    if execution["system_prompt"] is not None:
        messages.append({"role": "system", "content": execution["system_prompt"]})
    messages.append({"role": "user", "content": initial})
    prompts = {p["message_id"]: p["content"] for p in bundle["prompts"]}
    for sid in ancestors:
        if slots[sid]["kind"] == "followup":
            messages.append({"role": "user", "content": prompts[sid]})
        messages.append({"role": "assistant", "content": raw_answers[sid]})
    if slot["kind"] == "followup":
        messages.append({"role": "user", "content": prompts[slot_id]})
    parameters = dict(execution["parameters"], **execution["case_parameters"].get(slot["case_id"], {}))
    return {"schema": "math-gauge.conversation/v1", "messages": messages, "parameters": parameters}


def _controller_main():
    import argparse
    import sys
    parser = argparse.ArgumentParser(description="Offline Math Gauge bundle checks and exact request construction")
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("check", "request"):
        sub = commands.add_parser(name)
        sub.add_argument("--bundle", default=str(Path(__file__).resolve().parent))
        if name == "request":
            sub.add_argument("--slot", required=True)
            sub.add_argument("--answers", help="JSON object of exact ancestor response strings")
            sub.add_argument("--out", help="New JSON file outside the immutable bundle; default stdout")
    args = parser.parse_args()
    try:
        if args.command == "check":
            manifest = inspect_bundle(args.bundle)
            result = {k: manifest[k] for k in ("bundle_sha256", "plan_sha256", "exported_slots", "preparation_only")}
        else:
            answers = json.loads(Path(args.answers).read_bytes()) if args.answers else None
            result = build_request(args.bundle, args.slot, answers)
        output = json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n"
        if args.command == "request" and args.out:
            target = _h_path(args.out)
            _h_require(not target.is_symlink() and not target.exists()
                       and not target.resolve().is_relative_to(_h_root(args.bundle)),
                       "Request output must be a new file outside the immutable bundle")
            with target.open("x", encoding="utf-8", newline="\n") as stream:
                stream.write(output)
        else:
            sys.stdout.write(output)
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.error(str(error))


def _controller_source():
    functions = (_h_require, _h_digest, _h_identity, _h_hash, _h_object, _h_relative, _h_path, _h_root,
                 _h_file, _h_parameters, _h_execution, relative_name, candidate_message,
                 _h_message, _h_projection, _inspect_bundle_contents,
                 inspect_bundle, _h_build_request, build_request,
                 _controller_main)
    header = ('"""Portable Math Gauge controller. Python 3.10+, standard library only.\n'
              'This program never calls a model. Keep it outside candidate workspaces.\n"""\n\n'
              'import hashlib\nimport json\nimport math\nimport re\nfrom pathlib import Path, PurePosixPath\n\n')
    constants = f"BUNDLE_SCHEMA = {BUNDLE_SCHEMA!r}\nCONTROLLER_VERSION = {CONTROLLER_VERSION!r}\n"
    constants += f"PARAMETER_NAMES = {PARAMETER_NAMES!r}\n_MANIFEST_KEYS = {tuple(sorted(_MANIFEST_KEYS))!r}\n\n"
    return (header + constants + "\n\n".join(inspect.getsource(f).rstrip() for f in functions)
            + '\n\n\nif __name__ == "__main__":\n    _controller_main()\n').encode("utf-8")


_GUIDE = """# Math Gauge external harness controller

This is a portable controller package for Python 3.10 or newer. It needs no
repository, Codex installation, account, or third-party Python package. Export
and validation never call a model. The repository default suite is a public
development benchmark; exporting another suite does not assert its exposure
status. Preparing this package establishes neither a model trial nor formal eligibility.
`preparation_only: true` means runtime and budgets have not been frozen: obtain
a newly frozen export before a real trial. Do not edit this immutable package.

## Controller and candidate boundary

This document, manifest, all schedules, submission template, and controller.py
are for the operator. They are not candidate prompts. For each invocation expose
only its exact constructed conversation and that case's files/ attachments in
a fresh case workspace. The initial user message already includes every file,
including chapter source proofs and intentionally unchanged supplied Lean inputs.
Do not pass only task.md. Do not give the candidate the controller directory,
other cases, followup schedules, the evaluator sidecar, repository, answer keys,
reviews, correctness feedback, or earlier independent answers. The separate
evaluator directory must stay with the evaluator; never give it to the harness.

## Construct exact requests without running a model

Run `python3 controller.py check --bundle /path/to/bundle` after moving the
package. For an initial slot run
`python3 controller.py request --bundle /path/to/bundle --slot CASE:A1`.
For a followup, add `--answers /path/to/answers.json`; this JSON object maps
exactly the required ancestor slot IDs to unmodified assistant response text.
Round 1 needs CASE:A1. Round 2 needs CASE:A1 and CASE:ARM:1 from its own branch.
CRLF, leading/trailing whitespace, FULL/KEEP mode lines and all source blocks
must remain unchanged. The helper rejects missing and unrelated answers. Use
`--out /path/to/new-request.json` to save outside this immutable package.

The result is `{schema: math-gauge.conversation/v1, messages, parameters}`.
Send only its messages and parameters to your chosen model in a fresh session.
The helper does not execute that call or authenticate the provider. Follow the
frozen slot order, budget, retry, context and tool rules in manifest.json. A1,
A2 and A3 are independent. Every branch starts from the same raw A1, and R2
contains only that branch's raw R1. Do not replace history with composed material.
Retain missing, failed and blocked slots, every transport attempt, and every
readable original response; never select a better answer or silently rerun it.
Only retry a declared transient failure when no readable response was delivered,
at most twice, with identical request and frozen parameters. A readable response
locks its slot even when transport reports an error. Unknown token usage cannot
be invented to satisfy a total token budget. All denominators stay fixed.

## Return a separate submission directory

Copy submission-template.json outside the bundle as submission.json. Replace
its null bundle_sha256 with manifest.json's bundle_sha256. For an actual external
trial set origin to external, fixture_only to false and declare the actual call
count; offline fixtures/replay must remain explicitly labelled and cannot gain
formal eligibility. Keep plan_sha256 and runtime_sha256 exactly as exported.
An empty template contains no answer and is not a trial.

For each executed selected slot append an object with slot_id, projected_request
(the exact helper output), and ordered attempts. An attempt has number (1 or 2),
status (ok, transient_error, permanent_error, timeout, or budget_exhausted),
response and stderr descriptors `{path, bytes, sha256}`, usage (only observed
nonnegative numeric values), and projected_request_sha256 (SHA-256 of UTF-8 JSON
with sorted keys, compact separators, ensure_ascii=false). Store exact response
and stderr bytes in safe relative paths inside the submission directory. An
empty response/stderr is still an explicit zero-byte file. Optional exit_code,
started_at, finished_at, elapsed_seconds and metadata are external declarations,
not independent provider evidence. Return every attempt in order. Omitted slots
remain missing or blocked; the importer never invents candidate output.

Optionally preserve generated_files as `{name, path, bytes, sha256, extraction:
{response_sha256, start_byte, end_byte}}` whose source span is in the original
response, and ancillary artifacts as `{path, bytes, sha256}`. Never rewrite raw
responses to repair source. UTF-8 response text with source code blocks is the
normal delivery; candidate Lean verification is a later evaluator operation.
All paths are relative to the returned submission directory, with no traversal
or symlinks. Provider/configuration declarations may be recorded as metadata;
credentials and secrets must not be included.

The evaluator imports the return against its original frozen plan and suite,
then performs separate execution-evidence and mathematical reviews. File hashes
bind bytes and detect changes; they do not authenticate a provider, prove fresh
hidden context, or establish human approval. A local source check, mathematical
review, candidate Lean compilation and human approval remain separate evidence.
"""


def _execution_projection(plan, case_ids):
    runtime = plan.get("runtime") or {}
    parameters = _h_parameters(runtime.get("candidate_parameters", {}))
    raw_budget = runtime.get("budget", {})
    _h_require(isinstance(raw_budget, dict), "Frozen budget must be an object")
    budget = {k: raw_budget[k] for k in ("timeout_seconds", "output_tokens",
              "max_transport_attempts", "max_total_tokens") if k in raw_budget}
    if "output_tokens" in budget:
        output = budget["output_tokens"]
        _h_require("max_output_tokens" not in parameters or parameters["max_output_tokens"] == output,
                   "Generation parameters contradict the frozen output budget")
        parameters["max_output_tokens"] = output
    raw_cases = raw_budget.get("case_parameters", {})
    _h_require(isinstance(raw_cases, dict)
               and set(raw_cases) <= {x["case_id"] for x in plan["case_index"]},
               "Case generation parameters name an unknown case")
    case_parameters = {cid: _h_parameters(value) for cid, value in raw_cases.items() if cid in case_ids}
    raw_retry = runtime.get("retry", {})
    _h_require(isinstance(raw_retry, dict), "Retry policy must be an object")
    retry = {"max_attempts": raw_retry.get("max_attempts", 2),
             "wait_seconds": raw_retry.get("wait_seconds", 0),
             "retryable_exit_codes": raw_retry.get("retryable_exit_codes", [75])}
    result = {"parameters": parameters, "case_parameters": case_parameters, "budget": budget,
              "retry": retry, "system_prompt": runtime.get("system_prompt"),
              "model_label": runtime.get("model_label"),
              "context_policy": copy.deepcopy(plan["context_policy"])}
    _h_execution(result, case_ids)
    return copy.deepcopy(result)


def _source_suite(plan, suite):
    validate_plan(plan)
    fresh = Suite.load(suite.root)
    _h_require(fresh.sha256 == suite.sha256 and plan["suite"] == {
        "id": fresh.metadata["id"], "version": fresh.metadata["version"], "sha256": fresh.sha256},
        "Frozen plan or loaded suite differs from its current source")
    from .reliability import _bind_suite, _validate_schedule
    _bind_suite(plan, fresh)
    _validate_schedule(plan)
    return fresh


def _projection(plan, suite, targets):
    selected = select_slots(plan, targets)
    selected_ids = {s["slot_id"] for s in selected}
    wanted_cases = {s["case_id"] for s in selected}
    cases, contents = [], {}
    case_index = {c["case_id"]: c for c in plan["case_index"]}
    for cid in suite.cases:
        if cid not in wanted_cases:
            continue
        request = suite.request(suite.cases[cid])
        base = "cases/" + cid + "/"
        message = candidate_message(request).encode("utf-8")
        row = {"case_id": cid, "case_version": request["case_version"],
               "request_sha256": case_index[cid]["request_sha256"],
               "candidate_message_sha256": case_index[cid]["candidate_message_sha256"],
               "request_path": base + "request.json", "candidate_message_path": base + "candidate-message.md",
               "task_path": base + "task.md", "instruction_path": base + "instruction.txt", "files": []}
        contents[row["request_path"]] = (json.dumps(request, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
        contents[row["candidate_message_path"]] = message
        contents[row["task_path"]] = request["task"].encode("utf-8")
        contents[row["instruction_path"]] = request["instruction"].encode("utf-8")
        for item in request["files"]:
            raw = item["content"].encode("utf-8")
            name = base + "files/" + item["name"]
            _h_relative(name)
            contents[name] = raw
            row["files"].append({"name": item["name"], "path": name,
                                  "sha256": digest_bytes(raw), "bytes": len(raw)})
        cases.append(row)
    slots = []
    for slot in selected:
        keys = ("slot_id", "case_id", "kind", "context", "parent_slot", "message_id", "ordinal_per_model")
        row = {k: slot[k] for k in keys}
        row.update({k: slot[k] for k in (("attempt_label",) if slot["kind"] == "independent" else ("arm", "round"))})
        slots.append(row)
    prompts = [{k: row[k] for k in ("message_id", "content", "content_sha256")}
               for row in plan["reliability"]["prompts"]["messages"] if row["message_id"] in selected_ids]
    manifest = {"schema": BUNDLE_SCHEMA, "controller_version": CONTROLLER_VERSION,
                "plan_id": plan["plan_id"], "plan_sha256": plan["plan_sha256"],
                "suite": copy.deepcopy(plan["suite"]), "runner_sha256": plan["runner_sha256"],
                "runtime_sha256": plan["runtime_sha256"],
                "protocol_version": plan["reliability"]["protocol_version"],
                "runtime_frozen": plan["runtime_frozen"], "preparation_only": not plan["runtime_frozen"],
                "targets": list(plan["targets"] if targets is None else targets),
                "planned": copy.deepcopy(plan["planned"]), "exported_slots": len(slots),
                "selected_slot_ids": [s["slot_id"] for s in slots], "slots": slots, "cases": cases,
                "prompts": prompts, "execution": _execution_projection(plan, wanted_cases)}
    return manifest, contents


def _new_destination(path):
    path = _h_path(path)
    _h_require(not path.exists(), "Harness output already exists")
    return path


def export_harness_bundle(plan, suite, destination, *, evaluator_destination=None, targets=None):
    """Export a fresh controller package plus an isolated complete-plan receipt."""
    suite = _source_suite(plan, suite)
    from .execution import runner_fingerprint
    _h_require(plan["runner_sha256"] == runner_fingerprint(),
               "Runner source changed after the benchmark plan was frozen")
    dest = _new_destination(destination)
    evaluator = _new_destination(str(destination) + ".evaluator" if evaluator_destination is None
                                 else evaluator_destination)
    _h_require(not dest.is_relative_to(suite.root) and not suite.root.is_relative_to(dest)
               and not evaluator.is_relative_to(suite.root) and not suite.root.is_relative_to(evaluator),
               "Harness outputs must not overlap the question suite")
    _h_require(not dest.is_relative_to(evaluator) and not evaluator.is_relative_to(dest),
               "Evaluator directory must be separate from the controller bundle")
    manifest, contents = _projection(plan, suite, targets)
    template = {"schema": "math-gauge.harness-submission/v1", "bundle_sha256": None,
                "plan_sha256": plan["plan_sha256"], "runtime_sha256": plan["runtime_sha256"],
                "origin": "fixture", "fixture_only": True, "declared_external_calls": 0, "slots": []}
    contents.update({"CONTROLLER.md": _GUIDE.encode("utf-8"), "controller.py": _controller_source(),
                     "submission-template.json": (json.dumps(template, ensure_ascii=False, indent=2) + "\n").encode("utf-8")})
    manifest["files_sha256"] = {name: digest_bytes(raw) for name, raw in sorted(contents.items())}
    manifest["bundle_sha256"] = identity(manifest)
    created = []
    try:
        for root in (dest, evaluator):
            root.mkdir(parents=True, exist_ok=False)
            created.append(root)
        for name, raw in contents.items():
            target = dest / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        write_json(dest / "manifest.json", manifest)
        write_json(evaluator / "plan.json", plan)
        receipt = {"schema": "math-gauge.harness-export-receipt/v1", "operator_only": True,
                   "bundle_sha256": manifest["bundle_sha256"], "plan_sha256": plan["plan_sha256"],
                   "runtime_sha256": plan["runtime_sha256"],
                   "manifest_file_sha256": digest_bytes((dest / "manifest.json").read_bytes()),
                   "plan_file_sha256": digest_bytes((evaluator / "plan.json").read_bytes()),
                   "selected_slot_ids": manifest["selected_slot_ids"], "candidate_calls": 0}
        write_json(evaluator / "receipt.json", receipt)
        inspect_harness_bundle(dest, plan=plan, suite=suite)
    except Exception:
        for root in reversed(created):
            shutil.rmtree(root)
        raise
    return manifest


def inspect_harness_bundle(root, *, plan=None, suite=None):
    """Check a portable bundle, optionally binding it to evaluator source evidence."""
    schema = _r_json(_h_file(_h_root(root), "manifest.json").read_bytes()).get("schema")
    if schema == DATASET_SCHEMA:
        return inspect_release_dataset(root, plan=plan, suite=suite)
    if schema == RUN_SCHEMA:
        manifest = inspect_release_run(root)
        if plan is not None:
            reconstruct_release_plan(root, plan, suite=suite)
        elif suite is not None:
            inspect_release_dataset(_h_root(root) / "dataset", suite=suite)
        return manifest
    manifest = inspect_bundle(root)
    root = _h_root(root)
    if plan is not None:
        validate_plan(plan)
        _h_require(manifest["plan_sha256"] == plan["plan_sha256"]
                   and manifest["plan_id"] == plan["plan_id"]
                   and manifest["suite"] == plan["suite"]
                   and manifest["runner_sha256"] == plan["runner_sha256"]
                   and manifest["runtime_sha256"] == plan["runtime_sha256"]
                   and manifest["runtime_frozen"] == plan["runtime_frozen"]
                   and manifest["planned"] == plan["planned"]
                   and manifest["protocol_version"] == plan["reliability"]["protocol_version"],
                   "Harness bundle binds a different frozen plan")
        selected = select_slots(plan, manifest["targets"])
        keys = {"slot_id", "case_id", "kind", "context", "parent_slot", "message_id", "ordinal_per_model",
                "attempt_label", "arm", "round"}
        _h_require(manifest["slots"] == [{k: v for k, v in s.items() if k in keys} for s in selected]
                   and manifest["execution"] == _execution_projection(plan, {s["case_id"] for s in selected}),
                   "Harness execution projection differs from its frozen plan")
        prompts = [{k: p[k] for k in ("message_id", "content", "content_sha256")}
                   for p in plan["reliability"]["prompts"]["messages"]
                   if p["message_id"] in manifest["selected_slot_ids"]]
        _h_require(manifest["prompts"] == prompts, "Harness prompts differ from the frozen plan")
        index = {c["case_id"]: c for c in plan["case_index"]}
        for case in manifest["cases"]:
            expected = index[case["case_id"]]
            _h_require(case["case_version"] == expected["version"]
                       and case["request_sha256"] == expected["request_sha256"]
                       and case["candidate_message_sha256"] == expected["candidate_message_sha256"],
                       "Harness candidate input differs from the frozen plan")
    if suite is not None:
        suite = _source_suite(plan, suite) if plan is not None else Suite.load(suite.root)
        _h_require(manifest["suite"] == {"id": suite.metadata["id"], "version": suite.metadata["version"],
                                        "sha256": suite.sha256}, "Harness bundle binds a different suite")
        for case in manifest["cases"]:
            request = suite.request(suite.cases[case["case_id"]])
            _h_require(json.loads(_h_file(root, case["request_path"]).read_bytes()) == request,
                       "Harness candidate projection differs from the source suite")
    return manifest


def candidate_request_from_bundle(root, slot_id, answers=None):
    """Shared external-harness request builder; exact raw ancestor answers only."""
    manifest = inspect_harness_bundle(root)
    if manifest["schema"] == RUN_SCHEMA:
        return release_candidate_request(root, slot_id, answers)
    _h_require(manifest["schema"] != DATASET_SCHEMA, "Freeze a runtime before constructing release requests")
    return build_request(root, slot_id, answers)


def _r_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            _h_require(key not in result, "Duplicate JSON key in release evidence")
            result[key] = value
        return result
    try:
        result = json.loads(raw, object_pairs_hook=pairs)
        _h_identity(result)
        return result
    except (UnicodeError, json.JSONDecodeError, TypeError, OverflowError) as error:
        raise ValueError("Malformed release JSON") from error


def _r_write(path, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")
    with path.open("xb") as stream:
        stream.write(raw)


def _r_execution(runtime, case_ids):
    """Freeze only explicitly supported runtime conditions, without transport."""
    _h_require(isinstance(runtime, dict) and set(runtime) <= {
        "model_label", "adapter_identity", "budget", "candidate_parameters", "fresh_context",
        "system_prompt", "retry"}, "Unsupported fields in release runtime")
    _h_require(isinstance(runtime.get("model_label"), str) and runtime["model_label"].strip()
               and isinstance(runtime.get("adapter_identity"), (str, dict))
               and runtime["adapter_identity"] and runtime.get("fresh_context") is True,
               "Runtime requires a model label, adapter identity and fresh_context true")
    _h_require(isinstance(runtime.get("candidate_parameters"), dict)
               and isinstance(runtime["candidate_parameters"].get("model"), str)
               and runtime["candidate_parameters"]["model"].strip(),
               "Runtime requires an explicit candidate_parameters.model identifier")
    _h_identity(runtime)
    budget = runtime.get("budget")
    _h_require(isinstance(budget, dict) and set(budget) <= {
        "timeout_seconds", "output_tokens", "max_transport_attempts", "max_total_tokens", "case_parameters"},
        "Unsupported fields in release budget")
    _h_require(type(budget.get("timeout_seconds")) in (int, float)
               and math.isfinite(budget["timeout_seconds"]) and budget["timeout_seconds"] > 0
               and type(budget.get("output_tokens")) is int and budget["output_tokens"] > 0,
               "Freeze a positive timeout and output token budget before execution")
    _h_require("retry" not in runtime or isinstance(runtime["retry"], dict)
               and set(runtime["retry"]) <= {"max_attempts", "wait_seconds", "retryable_exit_codes"},
               "Unsupported fields in release retry policy")
    projection = _execution_projection({"runtime": runtime,
        "case_index": [{"case_id": cid} for cid in case_ids],
        "context_policy": _RELEASE_CONTEXT}, set(case_ids))
    return projection


def _r_targets(dataset, targets):
    targets = list(["all"] if targets is None else targets)
    _h_require(targets and len(targets) == len(set(targets))
               and all(isinstance(t, str) and t in _RELEASE_TARGETS for t in targets),
               "Unknown or repeated release target")
    wanted = {sid for target in targets for sid in dataset["target_slot_ids"][target]}
    return targets, [sid for sid in dataset["selected_slot_ids"] if sid in wanted]


def _inspect_release_dataset_contents(root):
    """Validate the complete generic download without any evaluator dependency."""
    try:
        root = _h_root(root)
        value = _r_json(_h_file(root, "manifest.json").read_bytes())
        _h_object(value, _DATASET_KEYS, "release dataset manifest")
        _h_require(value["schema"] == DATASET_SCHEMA and value["controller_version"] == RELEASE_CONTROLLER,
                   "Unsupported release dataset")
        _h_require(_h_hash(value["dataset_sha256"]) and value["dataset_sha256"] == _h_identity(
            {k: v for k, v in value.items() if k != "dataset_sha256"}), "Frozen release dataset changed")
        _h_require(all(_h_hash(value[k]) for k in ("base_plan_sha256", "runner_sha256")),
                   "Invalid release base identity")
        _h_object(value["suite"], {"id", "version", "sha256"}, "release suite binding")
        _h_require(_h_hash(value["suite"]["sha256"])
                   and all(isinstance(value["suite"][k], str) and value["suite"][k] for k in ("id", "version"))
                   and isinstance(value["release_version"], str) and value["release_version"]
                   and isinstance(value["protocol_version"], str) and value["protocol_version"],
                   "Invalid release version or suite binding")
        view = dict(value, execution={"parameters": {}, "case_parameters": {}, "budget": {},
                    "retry": {"max_attempts": 2, "wait_seconds": 0, "retryable_exit_codes": [75]},
                    "system_prompt": None, "model_label": None, "context_policy": _RELEASE_CONTEXT})
        _h_projection(root, view, {"CONTROLLER.md", "controller.py", "runtime-template.json"})
        _h_require(value["exported_slots"] == value["planned"]["all_slots"]
                   == value["planned"]["selected_slots"], "A generic release must retain the full denominator")
        selections = value["target_slot_ids"]
        _h_object(selections, _RELEASE_TARGETS, "release target map")
        all_ids = value["selected_slot_ids"]
        slots = {s["slot_id"]: s for s in value["slots"]}
        for target, ids in selections.items():
            _h_require(isinstance(ids, list) and ids and len(ids) == len(set(ids))
                       and ids == [sid for sid in all_ids if sid in ids], "Invalid release target order")
            _h_require(all(slots[sid]["parent_slot"] is None or slots[sid]["parent_slot"] in ids for sid in ids),
                       "Release target lacks its dependency closure")
        independent = [sid for sid, s in slots.items() if s["kind"] == "independent"]
        _h_require(selections["all"] == all_ids and selections["core"] == selections["repeat"] == independent,
                   "Release independent target inventory changed")
        partition = [sid for component in _RELEASE_TARGETS[:4] for sid in selections[component]]
        _h_require(len(partition) == len(set(partition)) and set(partition) == set(independent),
                   "Release component targets must partition independent slots")
        for component in _RELEASE_TARGETS[:4]:
            for sid in selections[component]:
                cid = slots[sid]["case_id"]
                _h_require(all(cid + ":" + label in selections[component] for label in ("A1", "A2", "A3")),
                           "Release component omitted an independent repeat")
        for target, arms in (("neutral", {"neutral"}), ("stance", {"affirm", "deny"})):
            wanted = {sid for sid, s in slots.items() if s["kind"] == "followup" and s["arm"] in arms}
            wanted.update(slots[sid]["case_id"] + ":A1" for sid in list(wanted))
            _h_require(selections[target] == [sid for sid in all_ids if sid in wanted],
                       "Release branch target inventory changed")
        _r_execution(_r_json(_h_file(root, "runtime-template.json").read_bytes()),
                     [c["case_id"] for c in value["cases"]])
        return value
    except (KeyError, TypeError, AttributeError, UnicodeError, json.JSONDecodeError) as error:
        raise ValueError("Malformed release dataset") from error


def inspect_release_dataset(root, *, plan=None, suite=None):
    """Inspect using installed code, optionally binding the trusted evaluator anchor."""
    value = _inspect_release_dataset_contents(root)
    root = _h_root(root)
    if plan is not None:
        _r_bind_dataset(value, root, plan, suite)
    elif suite is not None:
        fresh = Suite.load(suite.root)
        _h_require(value["suite"] == {"id": fresh.metadata["id"], "version": fresh.metadata["version"],
                                      "sha256": fresh.sha256}, "Release suite changed")
        for row in value["cases"]:
            _h_require(_r_json(_h_file(root, row["request_path"]).read_bytes())
                       == fresh.request(fresh.cases[row["case_id"]]), "Release candidate projection changed")
    return value


def _r_bind_dataset(value, root, plan, suite=None):
    validate_plan(plan)
    _h_require(not plan["runtime_frozen"] and plan["targets"] == ["all"]
               and plan["planned"]["selected_slots"] == plan["planned"]["all_slots"],
               "Release anchor must be a complete preparation-only plan")
    _h_require(value["base_plan_sha256"] == plan["plan_sha256"]
               and value["suite"] == plan["suite"] and value["runner_sha256"] == plan["runner_sha256"]
               and value["planned"] == plan["planned"]
               and value["protocol_version"] == plan["reliability"]["protocol_version"],
               "Release binds a different trusted base plan")
    keys = {"slot_id", "case_id", "kind", "context", "parent_slot", "message_id", "ordinal_per_model",
            "attempt_label", "arm", "round"}
    _h_require(value["slots"] == [{k: v for k, v in s.items() if k in keys} for s in select_slots(plan)]
               and value["target_slot_ids"] == {t: [s["slot_id"] for s in select_slots(plan, [t])]
                                                  for t in _RELEASE_TARGETS},
               "Release scheduling differs from the trusted base plan")
    prompts = [{k: p[k] for k in ("message_id", "content", "content_sha256")}
               for p in plan["reliability"]["prompts"]["messages"]]
    _h_require(value["prompts"] == prompts, "Release followup prompts changed")
    _h_require([r["case_id"] for r in value["cases"]] == [r["case_id"] for r in plan["case_index"]],
               "Release candidate inventory changed")
    for row, expected in zip(value["cases"], plan["case_index"]):
        _h_require(row["case_version"] == expected["version"]
                   and row["request_sha256"] == expected["request_sha256"]
                   and row["candidate_message_sha256"] == expected["candidate_message_sha256"],
                   "Release input differs from the trusted base plan")
    if suite is not None:
        fresh = _source_suite(plan, suite)
        for row in value["cases"]:
            _h_require(_r_json(_h_file(root, row["request_path"]).read_bytes())
                       == fresh.request(fresh.cases[row["case_id"]]), "Release candidate projection changed")


def _r_template(manifest, *, bound):
    return {"schema": RELEASE_SUBMISSION, "dataset_sha256": manifest["dataset_sha256"],
            "run_sha256": manifest["run_sha256"] if bound else None,
            "runtime_sha256": manifest["runtime_sha256"], "origin": "fixture", "fixture_only": True,
            "declared_external_calls": 0, "slots": []}


def inspect_release_run(root):
    """Check a frozen per-run declaration and its unchanged release copy offline."""
    try:
        root = _h_root(root)
        value = _r_json(_h_file(root, "manifest.json").read_bytes())
        _h_object(value, _RUN_KEYS, "release run manifest")
        _h_require(value["schema"] == RUN_SCHEMA and value["controller_version"] == RELEASE_CONTROLLER,
                   "Unsupported frozen release run")
        _h_require(_h_hash(value["run_sha256"]) and value["run_sha256"] == _h_identity(
            {k: v for k, v in value.items() if k != "run_sha256"}), "Frozen release run changed")
        _h_require(isinstance(value["run_id"], str) and re.fullmatch(r"[0-9a-f]{32}", value["run_id"])
                   and isinstance(value["created_at"], str), "Invalid frozen run identity")
        timestamp = datetime.fromisoformat(value["created_at"].replace("Z", "+00:00"))
        _h_require(timestamp.tzinfo is not None and timestamp.utcoffset() is not None,
                   "Frozen run time must include a timezone")
        dataset = _inspect_release_dataset_contents(root / "dataset")
        _h_require(value["dataset_sha256"] == dataset["dataset_sha256"]
                   and value["base_plan_sha256"] == dataset["base_plan_sha256"],
                   "Frozen run binds a different release")
        _h_require(value["runtime_frozen"] is True and value["preparation_only"] is False
                   and value["runtime_sha256"] == _h_identity(value["runtime"]),
                   "Release execution requires a frozen runtime")
        execution = _r_execution(value["runtime"], [c["case_id"] for c in dataset["cases"]])
        targets, ids = _r_targets(dataset, value["targets"])
        _h_require(value["targets"] == targets and value["selected_slot_ids"] == ids,
                   "Frozen runtime target projection changed")
        selected_cases = {s["case_id"] for s in dataset["slots"] if s["slot_id"] in ids}
        execution["case_parameters"] = {c: p for c, p in execution["case_parameters"].items() if c in selected_cases}
        _h_require(value["execution"] == execution
                   and value["planned"] == dict(dataset["planned"], selected_slots=len(ids)),
                   "Frozen runtime execution or denominator changed")
        _h_object(value["files_sha256"], {"controller.py", "submission-template.json"}, "run file inventory")
        for name, digest in value["files_sha256"].items():
            _h_require(_h_hash(digest) and _h_digest(_h_file(root, name).read_bytes()) == digest,
                       "Frozen run file changed: " + name)
        _h_require(_h_file(root, "controller.py").read_bytes() == _h_file(root / "dataset", "controller.py").read_bytes(),
                   "Frozen run controller differs from release")
        _h_require(_r_json(_h_file(root, "submission-template.json").read_bytes()) == _r_template(value, bound=False),
                   "Frozen run submission template changed")
        _h_require({p.name for p in root.iterdir()} == {"manifest.json", "controller.py", "submission-template.json", "dataset"}
                   and all(not p.is_symlink() for p in root.iterdir()), "Unlisted file in frozen run workspace")
        return value
    except (KeyError, TypeError, AttributeError, UnicodeError, json.JSONDecodeError) as error:
        raise ValueError("Malformed frozen release run") from error


def freeze_release_runtime(dataset_root, runtime, destination, *, targets=None):
    """Create one new independent run workspace; never modify the download."""
    root = _h_root(dataset_root)
    dataset = _inspect_release_dataset_contents(root)
    execution = _r_execution(runtime, [c["case_id"] for c in dataset["cases"]])
    targets, ids = _r_targets(dataset, targets)
    selected_cases = {s["case_id"] for s in dataset["slots"] if s["slot_id"] in ids}
    execution["case_parameters"] = {c: p for c, p in execution["case_parameters"].items() if c in selected_cases}
    dest = _h_path(destination)
    _h_require(not dest.exists() and not dest.is_relative_to(root) and not root.is_relative_to(dest),
               "Run output must be a new directory separate from the immutable dataset")
    manifest = {"schema": RUN_SCHEMA, "controller_version": RELEASE_CONTROLLER,
                "run_id": uuid.uuid4().hex, "created_at": datetime.now(timezone.utc).isoformat(),
                "dataset_sha256": dataset["dataset_sha256"], "base_plan_sha256": dataset["base_plan_sha256"],
                "runtime": copy.deepcopy(runtime), "runtime_sha256": _h_identity(runtime),
                "runtime_frozen": True, "preparation_only": False, "targets": targets,
                "selected_slot_ids": ids, "planned": dict(dataset["planned"], selected_slots=len(ids)),
                "execution": execution}
    controller = _h_file(root, "controller.py").read_bytes()
    template = (json.dumps(_r_template(dict(manifest, run_sha256=None), bound=False),
                           ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    manifest["files_sha256"] = {"controller.py": _h_digest(controller),
                                "submission-template.json": _h_digest(template)}
    manifest["run_sha256"] = _h_identity(manifest)
    created = False
    try:
        dest.mkdir(parents=True, exist_ok=False)
        created = True
        shutil.copytree(root, dest / "dataset", symlinks=True)
        (dest / "controller.py").write_bytes(controller)
        (dest / "submission-template.json").write_bytes(template)
        _r_write(dest / "manifest.json", manifest)
        inspect_release_run(dest)
        return manifest
    except BaseException:
        if created:
            shutil.rmtree(dest)
        raise


def release_candidate_request(root, slot_id, answers=None):
    manifest = inspect_release_run(root)
    dataset_root = _h_root(root) / "dataset"
    dataset = _inspect_release_dataset_contents(dataset_root)
    ids = set(manifest["selected_slot_ids"])
    view = dict(dataset, execution=manifest["execution"], slots=[s for s in dataset["slots"] if s["slot_id"] in ids])
    return _h_build_request(dataset_root, view, slot_id, answers)


def reconstruct_release_plan(root, base_plan, *, suite=None):
    """Bind the original declaration to its trusted evaluator anchor, without rewriting it."""
    manifest = inspect_release_run(root)
    inspect_release_dataset(_h_root(root) / "dataset", plan=base_plan, suite=suite)
    result = copy.deepcopy(base_plan)
    result.update(plan_id=manifest["run_id"], created_at=manifest["created_at"],
                  runtime=copy.deepcopy(manifest["runtime"]), runtime_frozen=True,
                  runtime_sha256=manifest["runtime_sha256"], model_label=manifest["runtime"]["model_label"],
                  targets=list(manifest["targets"]), planned=copy.deepcopy(manifest["planned"]))
    selected = set(manifest["selected_slot_ids"])
    for slot in result["slots"]:
        slot["selected"] = slot["slot_id"] in selected
    result["external_release"] = {"dataset_sha256": manifest["dataset_sha256"],
        "run_sha256": manifest["run_sha256"], "base_plan_sha256": base_plan["plan_sha256"]}
    result.pop("plan_sha256")
    result["plan_sha256"] = identity(result)
    validate_plan(result)
    _h_require([s["slot_id"] for s in select_slots(result)] == manifest["selected_slot_ids"]
               and _execution_projection(result, {s["case_id"] for s in select_slots(result)}) == manifest["execution"],
               "Runtime declaration differs from reconstructed evaluator plan")
    return result


def release_submission_template(root):
    return _r_template(inspect_release_run(root), bound=True)


def _release_controller_main():
    import argparse
    import sys
    parser = argparse.ArgumentParser(description="Offline Math Gauge release checks, runtime freezing and exact requests; no model calls")
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("check", "freeze", "request", "template"):
        sub = commands.add_parser(name)
        sub.add_argument("--bundle", default=str(Path(__file__).resolve().parent))
        if name != "check":
            sub.add_argument("--out", required=name in {"freeze", "template"})
        if name == "freeze":
            sub.add_argument("--runtime", required=True)
            sub.add_argument("--target", action="append", dest="targets")
        if name == "request":
            sub.add_argument("--slot", required=True)
            sub.add_argument("--answers", help="JSON object containing exactly this branch's raw ancestor replies")
    args = parser.parse_args()
    try:
        root = _h_root(args.bundle)
        if args.command == "check":
            schema = _r_json(_h_file(root, "manifest.json").read_bytes()).get("schema")
            value = _inspect_release_dataset_contents(root) if schema == DATASET_SCHEMA else inspect_release_run(root)
            result = {k: value[k] for k in ("schema", "dataset_sha256", "base_plan_sha256", "planned")}
            if schema == DATASET_SCHEMA:
                result.update(runtime_frozen=False, preparation_only=True)
            else:
                result.update(run_sha256=value["run_sha256"], runtime_frozen=True, preparation_only=False)
        elif args.command == "freeze":
            result = freeze_release_runtime(root, _r_json(_h_path(args.runtime).read_bytes()), args.out, targets=args.targets)
            result = {k: result[k] for k in ("run_sha256", "dataset_sha256", "runtime_sha256", "planned")}
        elif args.command == "template":
            result = release_submission_template(root)
        else:
            answers = _r_json(_h_path(args.answers).read_bytes()) if args.answers else None
            result = release_candidate_request(root, args.slot, answers)
        if args.command in {"request", "template"} and args.out:
            path = _h_path(args.out)
            _h_require(not path.exists() and not path.is_relative_to(root) and not root.is_relative_to(path),
                       "Output must be a new file outside the immutable run workspace")
            _r_write(path, result)
        else:
            sys.stdout.write(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n")
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.error(str(error))


def _release_controller_source():
    functions = (_h_require, _h_digest, _h_identity, _h_hash, _h_object, _h_relative, _h_path,
                 _h_root, _h_file, _h_parameters, _h_execution, relative_name, candidate_message,
                 _h_message, _h_projection, _h_build_request, _execution_projection,
                 _r_json, _r_write, _r_execution, _r_targets, _inspect_release_dataset_contents,
                 _r_template, inspect_release_run, freeze_release_runtime, release_candidate_request,
                 release_submission_template, _release_controller_main)
    header = ('"""Portable Math Gauge release helper. Python 3.10+, stdlib only.\n'
              'Controller-side only. This program never calls a candidate model.\n"""\n\n'
              'import copy\nimport hashlib\nimport json\nimport math\nimport re\nimport shutil\nimport uuid\n'
              'from datetime import datetime, timezone\nfrom pathlib import Path, PurePosixPath\n\n')
    constants = {"DATASET_SCHEMA": DATASET_SCHEMA, "RUN_SCHEMA": RUN_SCHEMA,
                 "RELEASE_CONTROLLER": RELEASE_CONTROLLER, "RELEASE_SUBMISSION": RELEASE_SUBMISSION,
                 "PARAMETER_NAMES": PARAMETER_NAMES, "_DATASET_KEYS": tuple(sorted(_DATASET_KEYS)),
                 "_RUN_KEYS": tuple(sorted(_RUN_KEYS)), "_RELEASE_TARGETS": _RELEASE_TARGETS,
                 "_RELEASE_CONTEXT": _RELEASE_CONTEXT}
    return (header + "\n".join(k + " = " + repr(v) for k, v in constants.items()) + "\n\n"
            + "\n\n".join(inspect.getsource(f).rstrip() for f in functions)
            + '\n\n\nif __name__ == "__main__":\n    _release_controller_main()\n').encode("utf-8")


_RELEASE_GUIDE = """# Math Gauge standalone release controller

This immutable generic dataset is a public development suite, not a hidden holdout.
It contains complete candidate tasks, declared attachments and controller-only
scheduling. Reference answers, rubrics, expected truth and the full benchmark plan
are excluded. Chapter source proofs and intentionally supplied Lean remain inputs.
Python 3.10+ and its standard library are sufficient; no repository is needed.
All helper commands make zero model calls. Keep the entire package and schedules
outside candidate workspaces; send only the constructed messages and parameters.

1. Run `python3 controller.py check --bundle /path/to/dataset` after download.
2. Copy runtime-template.json outside this dataset, choose the actual backend/model,
   timeout, output-token and cumulative budgets. Do not include credentials. Freeze
   before execution: `python3 controller.py freeze --bundle /path/to/dataset
   --runtime /path/to/runtime.json --target all --out /path/to/NEW_RUN`.
   Targets may be repeated; default all. proofs, lean-audit, lean-construction,
   chapters, repeat, neutral, stance, core and all are supported. Followup targets
   include their A1 parents. Full denominators remain fixed even for partial runs.
3. Use NEW_RUN/controller.py request --bundle /path/to/NEW_RUN --slot CASE:A1
   --out /path/to/new-request.json. A1/A2/A3 each require a fresh independent model
   context. Only the exact messages and parameters are model input. No tools,
   retrieval, compilation or correctness feedback are allowed in this version.
4. For round 1 pass --answers /path/to/answers.json containing exactly CASE:A1's
   raw response string. Round 2 additionally requires only its own CASE:ARM:1 raw
   response. neutral, affirm and deny are isolated branches of the same locked A1.
   Preserve raw whitespace, FULL/KEEP lines and source blocks. Never use a composed
   answer as history. The helper rejects absent and unrelated ancestors.
5. Run `python3 NEW_RUN/controller.py template --bundle /path/to/NEW_RUN
   --out /path/to/new-submission.json`. The emitted v2 template binds the dataset,
   frozen run and runtime hashes. It defaults to origin fixture, fixture_only true,
   declared_external_calls 0. For actual execution explicitly use origin external,
   fixture_only false and the observed call count. Keep the frozen run unchanged.

Execute slots in manifest order. Record missing slots, failures, every ordered
transport attempt, exact projected_request, original response/stderr bytes and their
path/bytes/SHA-256 descriptors, observable usage and timing. A slot row has slot_id,
projected_request and attempts. Attempt fields are number (1 or 2), status (ok,
transient_error, timeout, permanent_error or budget_exhausted),
projected_request_sha256, response, stderr and usage. Response and stderr are
{path,bytes,sha256}; paths are relative to the separate submission directory.
Request hashes use SHA-256 of sorted compact UTF-8 JSON (ensure_ascii false).
Unknown usage/timing remains unknown; preserve even empty response files. Only an
unreadable transient failure or timeout may be retried once with the same request;
the first readable reply locks the slot regardless of correctness or exit state.
KEEP inherits the immediate parent's complete material; FULL must supply the full
new answer. No selection of better answers, cross-branch history or answer repair.

Return the unchanged NEW_RUN directory plus the separate submission directory to
the evaluator. The evaluator regenerates the trusted base plan from the tagged
release source and imports using benchmark-import --bundle NEW_RUN --input
submission.json --plan evaluator-plan.json --out NEW_IMPORTED_RUN. This does not
invoke a model. Original v2 declarations, submissions and response bytes are kept
unchanged, while evaluation uses the shared review and fixed-denominator scoring.
Generic external declarations remain provisional: hashes are integrity bindings,
not proof of provider identity, isolation, mathematical correctness, human approval
or formal comparison eligibility. Fixture submissions are software tests only.
"""


def export_release_dataset(plan, suite, destination, *, evaluator_destination=None, release_version="0.1.0"):
    """Export a deterministic generic download and a separate evaluator anchor."""
    suite = _source_suite(plan, suite)
    from .execution import runner_fingerprint
    _h_require(plan["runner_sha256"] == runner_fingerprint(), "Runner changed after release anchor freezing")
    _h_require(not plan["runtime_frozen"] and plan["targets"] == ["all"],
               "Release dataset requires a full preparation-only base plan")
    dest = _new_destination(destination)
    evaluator = _new_destination(str(destination) + ".evaluator" if evaluator_destination is None else evaluator_destination)
    _h_require(not dest.is_relative_to(evaluator) and not evaluator.is_relative_to(dest)
               and not dest.is_relative_to(suite.root) and not suite.root.is_relative_to(dest)
               and not evaluator.is_relative_to(suite.root) and not suite.root.is_relative_to(evaluator),
               "Release, evaluator and suite directories must be separate")
    projection, contents = _projection(plan, suite, ["all"])
    keys = ("suite", "runner_sha256", "protocol_version", "planned", "exported_slots",
            "selected_slot_ids", "slots", "cases", "prompts")
    manifest = {k: projection[k] for k in keys}
    manifest.update(schema=DATASET_SCHEMA, controller_version=RELEASE_CONTROLLER, release_version=release_version,
                    base_plan_sha256=plan["plan_sha256"],
                    target_slot_ids={t: [s["slot_id"] for s in select_slots(plan, [t])] for t in _RELEASE_TARGETS})
    template = {"model_label": "replace-with-requested-model", "adapter_identity": {"kind": "external-harness",
                "provider": "replace-with-actual-backend"}, "candidate_parameters": {"model": "replace-with-model-id"},
                "budget": {"timeout_seconds": 120, "output_tokens": 16000}, "fresh_context": True}
    contents.update({"controller.py": _release_controller_source(), "CONTROLLER.md": _RELEASE_GUIDE.encode("utf-8"),
                     "runtime-template.json": (json.dumps(template, ensure_ascii=False, indent=2) + "\n").encode("utf-8")})
    manifest["files_sha256"] = {name: digest_bytes(raw) for name, raw in sorted(contents.items())}
    manifest["dataset_sha256"] = identity(manifest)
    created = []
    try:
        for root in (dest, evaluator):
            root.mkdir(parents=True, exist_ok=False)
            created.append(root)
        for name, raw in contents.items():
            target = dest / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        write_json(dest / "manifest.json", manifest)
        write_json(evaluator / "plan.json", plan)
        write_json(evaluator / "receipt.json", {"schema": "math-gauge.release-export-receipt/v1",
            "operator_only": True, "dataset_sha256": manifest["dataset_sha256"],
            "base_plan_sha256": plan["plan_sha256"], "candidate_calls": 0,
            "manifest_file_sha256": digest_bytes((dest / "manifest.json").read_bytes()),
            "plan_file_sha256": digest_bytes((evaluator / "plan.json").read_bytes())})
        inspect_release_dataset(dest, plan=plan, suite=suite)
    except BaseException:
        for root in reversed(created):
            shutil.rmtree(root)
        raise
    return manifest
