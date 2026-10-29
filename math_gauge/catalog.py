"""Case ownership: validation, provenance, fingerprints and solver-visible projection."""

import hashlib
import json
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


def relative_name(value):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError(f"Invalid relative path: {value!r}")
    p = PurePosixPath(value)
    if p.is_absolute() or ".." in p.parts or value != str(p):
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
            paths = [
                manifest,
                case["task"],
                case["reference"],
                case["rubric"],
            ] + case.get("evaluator_files", [])
            protected = {
                safe_file(root, p).resolve()
                for p in [case["reference"], case["rubric"]]
                + case.get("evaluator_files", [])
            }
            targets = {"prompt.md", "request.json"}
            for item in case["solver_files"]:
                target = relative_name(item["target"])
                if len(target.parts) != 1 or str(target) in targets:
                    raise ValueError(
                        f"{cid}: solver target must be a unique flat filename"
                    )
                targets.add(str(target))
                if safe_file(root, item["source"]).resolve() in protected:
                    raise ValueError(
                        f"{cid}: answer/rubric cannot be a solver attachment"
                    )
                paths.append(item["source"])
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
                    "content": safe_file(self.root, x["source"]).read_text(
                        encoding="utf-8"
                    ),
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
            (dest / item["name"]).write_text(item["content"], encoding="utf-8")
        write_json(dest / "request.json", request)
        return request
