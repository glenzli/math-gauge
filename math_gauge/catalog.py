"""Case ownership: validation, provenance, fingerprints and solver-visible projection."""

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

TRACKS = {"determinate", "alignment", "exploration"}
LEGACY_CANDIDATE_INSTRUCTION = (
    "使用题面实际给定的条件。区分已证明的结论、附加假设下的结果和未证猜想。给出可审核的论证。"
)


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )


def digest_bytes(value):
    return hashlib.sha256(value).hexdigest()


def candidate_message(request):
    """Neutral transport of the explicit projection; no evaluator metadata.

    The original task/instruction prefix is unchanged. A longer fence prevents
    source backticks from terminating an attachment. A framing newline after a
    non-newline-terminated file is not part of that file's request content.
    """
    task = request["task"]
    instruction = request.get("instruction", "")
    if not isinstance(task, str) or not isinstance(instruction, str):
        raise ValueError("Task and instruction must be text")
    message = instruction + "\n\n" + task if instruction else task
    seen = set()
    for item in request.get("files", []):
        name, content = item["name"], item["content"]
        path = relative_name(name)
        if name.casefold() in seen or not isinstance(content, str):
            raise ValueError("Attachment must have a unique filename and text content")
        seen.add(name.casefold())
        length = max([2, *(len(x) for x in re.findall(r"`+", content))]) + 1
        fence = "`" * length
        language = "lean" if name.endswith(".lean") else "text"
        separator = "" if content.endswith("\n") else "\n"
        message += f"\n\nFile: `{name}`\n{fence}{language}\n{content}{separator}{fence}\n"
    return message


def relative_name(value):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError(f"Invalid relative path: {value!r}")
    p = PurePosixPath(value)
    if not p.parts or p.is_absolute() or ".." in p.parts or value != str(p):
        raise ValueError(f"Unsafe relative path: {value!r}")
    return p


def safe_file(root, name):
    relative_name(name)
    root = Path(root).resolve()
    path = root / name
    if not path.resolve().is_relative_to(root) or not path.is_file():
        raise ValueError(f"Missing or escaping file: {name}")
    return path


def fingerprint(root, names):
    h = hashlib.sha256()
    for name in sorted(set(names)):
        content = safe_file(root, name).read_bytes()
        h.update(name.encode() + b"\0" + len(content).to_bytes(8, "big") + content)
    return h.hexdigest()


def case_paths(root, manifest, case):
    """Keep manifest-local storage paths suite-relative inside the runner.

    Candidate target names are workspace paths and never use this base. Checking
    the local file before joining also prevents a case-local symlink from
    reaching a neighbouring case, even when that file is inside the suite.
    """
    path_base = case.get("path_base", "suite")
    if not isinstance(path_base, str) or path_base not in {"suite", "case"}:
        raise ValueError(f"{case['id']}: path_base must be suite or case")
    if path_base == "suite":
        return case
    prefix = relative_name(manifest).parent
    base = root / prefix

    def local(name):
        safe_file(base, name)
        return str(prefix / name)

    normalized = dict(case)
    for key in ("task", "reference", "rubric"):
        normalized[key] = local(case[key])
    if case.get("group_contract"):
        normalized["group_contract"] = local(case["group_contract"])
    normalized["solver_files"] = [dict(item, source=local(item["source"]))
                                  for item in case["solver_files"]]
    normalized["lean_checks"] = [local(name) for name in case["lean_checks"]]
    normalized["evaluator_files"] = [local(name) for name in case.get("evaluator_files", [])]
    return normalized


def validate_group_contract(contract):
    """Validate evaluator-only stage contracts, never supply their truth labels."""
    if not isinstance(contract, dict) or contract.get("schema") != "math-gauge.group-contract/v1":
        raise ValueError("Unsupported group contract")
    if contract.get("kind") not in {"progressive", "chapter_formalization"}:
        raise ValueError("Invalid group kind")
    if contract.get("all_stages_mandatory", True) is not True:
        raise ValueError("Group stages cannot be optional")
    if type(contract.get("alignment_manifest_required", False)) is not bool:
        raise ValueError("Alignment manifest requirement must be boolean")
    if contract.get("alignment_manifest_required") and not all(
        isinstance(contract.get(key), str) and contract[key].strip() for key in ("id", "version")
    ):
        raise ValueError("Alignment manifest requires a versioned case identity")
    stages = contract.get("stages")
    if not isinstance(stages, list) or len(stages) < 2:
        raise ValueError("A group requires at least two stages")
    if contract["kind"] == "progressive" and len(stages) < 5:
        raise ValueError("A progressive group requires at least five stages")
    seen = set()
    for stage in stages:
        if not isinstance(stage, dict):
            raise ValueError("Each stage must be an object")
        if stage.get("mandatory", True) is not True:
            raise ValueError("Group stages cannot be optional")
        sid = stage.get("id")
        if not isinstance(sid, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", sid) or sid in seen:
            raise ValueError("Invalid or duplicate stage id")
        deps = stage.get("depends_on")
        if not isinstance(deps, list) or not all(isinstance(x, str) for x in deps) or len(set(deps)) != len(deps) or not set(deps) <= seen:
            raise ValueError(f"{sid}: dependencies must name earlier stages")
        if stage.get("kind") not in {"prove", "decide", "construct", "synthesize", "formalize", "audit"}:
            raise ValueError(f"{sid}: invalid stage kind")
        if stage.get("expected") not in {"true", "false", "construction", "classification", "aligned", "misaligned"}:
            raise ValueError(f"{sid}: missing expected result")
        for field in ("assumptions", "required_evidence", "critical_errors"):
            value = stage.get(field)
            if not isinstance(value, list) or not value or not all(isinstance(x, str) and x.strip() for x in value):
                raise ValueError(f"{sid}: {field} must contain specific criteria")
        if type(stage.get("points")) is not int or stage["points"] <= 0:
            raise ValueError(f"{sid}: positive integral weight required")
        if type(stage.get("lean_required")) is not bool:
            raise ValueError(f"{sid}: explicit Lean requirement needed")
        seen.add(sid)
    turns = contract.get("turns", [])
    if not isinstance(turns, list) or (contract["kind"] == "progressive" and not turns):
        raise ValueError("Progressive groups require a reviewed condition transition")
    by_id = {s["id"]: s for s in stages}
    positions = {s["id"]: i for i, s in enumerate(stages)}
    for turn in turns:
        if not isinstance(turn, dict):
            raise ValueError("Each condition transition must be an object")
        sid = turn.get("stage_id")
        earlier = turn.get("earlier_stage_ids")
        if not isinstance(sid, str) or sid not in seen or not isinstance(earlier, list) or not earlier or not all(isinstance(x, str) for x in earlier) or any(
            x not in seen or positions[x] >= positions[sid] for x in earlier
        ):
            raise ValueError("Condition transition must refer to earlier stages")
        scope = turn.get("scope", "stage")
        if scope not in {"stage", "subclaim"}:
            raise ValueError("Condition transition scope must be stage or subclaim")
        if scope == "subclaim" and (not isinstance(turn.get("target_claim"), str) or not turn["target_claim"].strip()):
            raise ValueError("Subclaim transition requires its explicit target claim")
        if turn.get("expected_truth") not in {"true", "false"} or (scope == "stage" and by_id[sid]["expected"] != turn["expected_truth"]):
            raise ValueError("Condition transition truth differs from stage contract")
        for key in ("mechanism", "changed_assumptions", "tempting_invalid_transfer", "correct_boundary"):
            if not isinstance(turn.get(key), str) or not turn[key].strip():
                raise ValueError(f"Condition transition requires {key}")
    return contract


def validate_alignment_manifest(manifest, contract):
    """Validate candidate coverage without prescribing its proof route."""
    if (not isinstance(manifest, dict) or manifest.get("case_id") != contract["id"]
            or manifest.get("version") != contract["version"]):
        raise ValueError("alignment.json case_id/version differs from the frozen contract")
    items = manifest.get("items")
    expected = {s["id"] for s in contract["stages"]}
    if (not isinstance(items, list) or not all(isinstance(x, dict) for x in items)
            or not all(isinstance(x.get("id"), str) for x in items)
            or len(items) != len(expected) or {x["id"] for x in items} != expected):
        raise ValueError("alignment.json must cover every obligation exactly once")
    for item in items:
        sid = item["id"]
        if item.get("status") not in {"complete", "incomplete"}:
            raise ValueError(f"{sid}: invalid alignment completion status")
        if not isinstance(item.get("representation"), str) or not item["representation"].strip():
            raise ValueError(f"{sid}: alignment representation is required")
        deps = item.get("dependencies")
        if (not isinstance(deps, list) or not all(isinstance(x, str) for x in deps)
                or len(set(deps)) != len(deps) or not set(deps) <= expected):
            raise ValueError(f"{sid}: alignment dependencies must name delivered obligations")
        declarations = item.get("declarations")
        if not isinstance(declarations, list) or (item["status"] == "complete" and not declarations):
            raise ValueError(f"{sid}: complete alignment requires declarations")
        seen = set()
        for declaration in declarations:
            if not isinstance(declaration, dict) or set(declaration) != {"file", "name"}:
                raise ValueError(f"{sid}: alignment declaration requires file and name")
            file, name = declaration["file"], declaration["name"]
            relative_name(file)
            if not file.endswith(".lean") or not isinstance(name, str) or not name.strip():
                raise ValueError(f"{sid}: invalid alignment declaration")
            if (file, name) in seen:
                raise ValueError(f"{sid}: duplicate alignment declaration")
            seen.add((file, name))
    return manifest


@dataclass
class Suite:
    root: Path
    metadata: dict
    cases: dict
    sha256: str

    @classmethod
    def load(cls, root):
        root = Path(root).resolve()
        meta = read_json(root / "suite.json")
        if meta.get("schema") != "math-gauge.suite/v1":
            raise ValueError("Unsupported suite schema")
        if meta.get("visibility") not in {"public", "private"}:
            raise ValueError("Suite visibility must be public or private")
        if not isinstance(meta.get("cases"), list) or not meta["cases"]:
            raise ValueError("Suite must contain cases")
        sources = read_json(root / "sources.json")
        cases = {}
        names = ["suite.json", "sources.json"]
        for manifest in meta["cases"]:
            case = read_json(safe_file(root, manifest))
            cid = case.get("id", "")
            if (
                not isinstance(cid, str)
                or not cid
                or any(
                    c
                    not in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
                    for c in cid
                )
            ):
                raise ValueError("Invalid case id")
            if cid in cases:
                raise ValueError(f"Duplicate case: {cid}")
            if (
                case.get("schema") != "math-gauge.case/v1"
                or case.get("track") not in TRACKS
            ):
                raise ValueError(f"{cid}: invalid schema or track")
            if case.get("visibility") != meta["visibility"]:
                raise ValueError(f"{cid}: visibility differs from suite")
            if case.get("status") not in {"draft", "approved", "retired"}:
                raise ValueError(f"{cid}: invalid lifecycle status")
            if case.get("review", {}).get("human") not in {
                "pending",
                "approved",
                "rejected",
            }:
                raise ValueError(f"{cid}: missing human review status")
            if case["status"] == "approved" and case["review"]["human"] != "approved":
                raise ValueError(f"{cid}: approval requires a human review record")
            for key in ("version", "title", "language"):
                if not isinstance(case.get(key), str) or not case[key]:
                    raise ValueError(f"{cid}: missing {key}")
            if "candidate_instruction" in case and not isinstance(
                case["candidate_instruction"], str
            ):
                raise ValueError(f"{cid}: candidate_instruction must be a string")
            if not case.get("sources") or any(
                s not in sources for s in case["sources"]
            ):
                raise ValueError(f"{cid}: unknown or absent provenance")
            if not isinstance(case.get("solver_files"), list) or not isinstance(
                case.get("lean_checks"), list
            ):
                raise ValueError(f"{cid}: input/check lists required")
            if not isinstance(case.get("evaluator_files", []), list):
                raise ValueError(f"{cid}: evaluator files must be a list")
            case = case_paths(root, manifest, case)
            paths = [
                manifest,
                case["task"],
                case["reference"],
                case["rubric"],
            ] + case.get("evaluator_files", [])
            if case.get("group_contract"):
                paths.append(case["group_contract"])
                contract = validate_group_contract(read_json(safe_file(root, case["group_contract"])))
                if contract.get("id") != cid:
                    raise ValueError(f"{cid}: group contract identity mismatch")
                if contract.get("alignment_manifest_required") and contract["version"] != case["version"]:
                    raise ValueError(f"{cid}: alignment contract version mismatch")
            protected = {
                safe_file(root, p).resolve()
                for p in [case["reference"], case["rubric"]]
                + case.get("evaluator_files", [])
                + ([case["group_contract"]] if case.get("group_contract") else [])
            }
            targets = {"prompt.md", "request.json"}
            for item in case["solver_files"]:
                target = relative_name(item["target"])
                if any(str(target).casefold() == t.casefold() or str(target).casefold().startswith(t.casefold() + "/")
                       or t.casefold().startswith(str(target).casefold() + "/") for t in targets):
                    raise ValueError(
                        f"{cid}: solver target must be unique and cannot shadow another file"
                    )
                targets.add(str(target))
                if safe_file(root, item["source"]).resolve() in protected:
                    raise ValueError(
                        f"{cid}: answer/rubric cannot be a solver attachment"
                    )
                paths.append(item["source"])
            if case.get("group_contract"):
                immutable = contract.get("immutable_input_files", [])
                input_targets = {x["target"] for x in case["solver_files"]}
                if not isinstance(immutable, list) or any(not isinstance(x, str) or x not in input_targets for x in immutable):
                    raise ValueError(f"{cid}: immutable inputs must be declared solver files")
                outputs = contract.get("required_output_files", [])
                if not isinstance(outputs, list) or not all(isinstance(x, str) for x in outputs):
                    raise ValueError(f"{cid}: required output files must be a list")
                for name in outputs:
                    relative_name(name)
                    if not name.endswith(".lean") or name in immutable:
                        raise ValueError(f"{cid}: invalid required output file")
            paths += case["lean_checks"]
            for p in paths:
                safe_file(root, p)
            rubric = read_json(safe_file(root, case["rubric"]))
            allowed = {
                "determinate": {"true", "false", "mixed"},
                "alignment": {"aligned", "misaligned"},
                "exploration": {"open"},
            }
            if (
                rubric.get("schema") != "math-gauge.rubric/v1"
                or rubric.get("expected") not in allowed[case["track"]]
            ):
                raise ValueError(f"{cid}: invalid rubric")
            if not rubric.get("required_evidence") or not rubric.get("critical_errors"):
                raise ValueError(f"{cid}: incomplete rubric")
            names.extend(paths)
            cases[cid] = case
        # No other case's reference/rubric may be smuggled in as an attachment.
        all_hidden = {
            safe_file(root, p).resolve()
            for c in cases.values()
            for p in [c["reference"], c["rubric"]] + c.get("evaluator_files", [])
            + ([c["group_contract"]] if c.get("group_contract") else [])
        }
        for c in cases.values():
            if safe_file(root, c["task"]).resolve() in all_hidden:
                raise ValueError(f"{c['id']}: task aliases evaluator material")
            if any(
                safe_file(root, f["source"]).resolve() in all_hidden
                for f in c["solver_files"]
            ):
                raise ValueError(f"{c['id']}: cross-case evaluator material in input")
        return cls(root, meta, cases, fingerprint(root, names))

    def select(self, ids=None):
        selected = list(ids or self.cases)
        if len(selected) != len(set(selected)):
            raise ValueError("Duplicate selected case")
        if any(cid not in self.cases for cid in selected):
            raise ValueError("Unknown selected case")
        return [self.cases[cid] for cid in selected]

    def request(self, case):
        return {
            "schema": "math-gauge.request/v1",
            "case_id": case["id"],
            "case_version": case["version"],
            "track": case["track"],
            "instruction": case.get(
                "candidate_instruction", LEGACY_CANDIDATE_INSTRUCTION
            ),
            "task": safe_file(self.root, case["task"]).read_bytes().decode("utf-8"),
            "files": [
                {
                    "name": x["target"],
                    "content": safe_file(self.root, x["source"]).read_bytes().decode("utf-8"),
                }
                for x in case["solver_files"]
            ],
        }

    def prepare(self, case, destination):
        dest = Path(destination)
        if dest.resolve().is_relative_to(self.root):
            raise ValueError("Solver workspace must be outside the question suite")
        dest.mkdir(parents=True, exist_ok=False)
        request = self.request(case)
        prompt = request["task"]
        if request["instruction"]:
            prompt = request["instruction"] + "\n\n" + prompt
        (dest / "prompt.md").write_bytes(prompt.encode("utf-8"))
        for item in request["files"]:
            target = dest / item["name"]
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(item["content"].encode("utf-8"))
        write_json(dest / "request.json", request)
        return request
