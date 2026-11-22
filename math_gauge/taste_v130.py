"""Offline, unranked 1.3.0 private-case protocol; does not call a solver."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat


EDITION = "1.3.0"
ROUNDS = ("R1", "R2", "R3")
AXES = ("autonomy", "taste", "capacity")
POLICY_FILE = Path(__file__).resolve().parents[1] / "protocol/mathematical-taste/v1.3.0/policy.json"
SCHEMA = "math-gauge.taste-preview-registration/v1"
REVIEW = "math-gauge.taste-preview-review/v1"


def _need(condition, message):
    if not condition:
        raise ValueError(message)


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _json(data):
    return (json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode()


def _load(p):
    return json.loads(Path(p).read_bytes())


def _new(p, data):
    with p.open("xb") as f:
        f.write(data)


def _contained(root, name):
    _need(isinstance(name, str) and not set(name) & {"\\", "\0"}, "Invalid path")
    rel = PurePosixPath(name)
    _need(not rel.is_absolute() and rel.as_posix() == name and
          bool(rel.parts) and all(p not in {".", ".."} for p in rel.parts), "Not a relative file")
    target = root
    for part in rel.parts:
        target = target / part
        _need(not target.is_symlink(), "Symlink in evidence path")
    return target


def _read(root, ref):
    _need(set(ref) == {"path", "bytes", "sha256"}, "Invalid descriptor")
    p = _contained(root, ref["path"])
    _need(p.is_file() and stat.S_ISREG(p.stat().st_mode), "Missing regular source file")
    raw = p.read_bytes()
    _need(type(ref["bytes"]) is int and len(raw) == ref["bytes"] and
          _sha(raw) == ref["sha256"], "Source hash mismatch")
    return raw


def load_case(registration):
    p = _safe_absolute(registration)
    data = _load(p)
    _need(set(data) == {"schema", "edition", "status", "category", "case_id", "case_root",
        "visibility", "rounds", "rules", "packet", "review_contract", "rubric", "provenance", "runner"}
        and data["schema"] == SCHEMA and data["edition"] == EDITION
        and data["status"] == "local_pending" and data["category"] == "open-research"
        and data["visibility"] == "private", "Not a private v1.3 pending registration")
    _need(isinstance(data["case_id"], str) and re.fullmatch(r"[A-Z][A-Z0-9-]{2,63}", data["case_id"])
        and data["case_root"] == data["case_id"], "Invalid private registration ID")
    root = _contained(p.parent, data["case_root"])
    _need(set(data["rounds"]) == set(ROUNDS) and all(
        data["rounds"][rid]["path"] == f"candidate/{rid}.md" for rid in ROUNDS), "Rounds must be fixed")
    _need(data["rules"]["path"] == "candidate/rules.md", "Invalid rules path")
    paths = [r["path"] for r in data["packet"]]
    _need(paths and len(set(paths)) == len(paths) and "packet/body.md" in paths and all(
        x == "packet/body.md" or re.fullmatch(r"packet/figures/[a-z0-9-]+\.png", x)
        for x in paths), "Unexpected participant file")
    for key, name in [("review_contract", "review-contract.json"), ("rubric", "rubric.md"),
                      ("provenance", "provenance.json")]:
        _need(data[key]["path"] == f"evaluator/{name}", "Wrong private evaluator path")
        _read(root, data[key])
    contract = json.loads(_read(root, data["review_contract"]))
    _need(contract.get("schema") == "math-gauge.taste-preview-private-contract/v1"
        and contract.get("case_id") == data["case_id"] and set(contract["gates"]) == set(AXES)
        and set(contract["round_coverage"]) == set(AXES), "Invalid private review contract")
    for axis, rows in contract["gates"].items():
        _need(rows and len({x["id"] for x in rows}) == len(rows)
            and all(type(x["required"]) is bool and set(x["rounds"]) <= set(ROUNDS)
                    and x["rounds"] for x in rows), "Invalid review gates")
        _need(set(contract["round_coverage"][axis]) <= set(ROUNDS), "Invalid round coverage")
    _need(sum(x["required"] for x in contract["gates"]["capacity"]) == 5,
          "Capacity has five noncompensating required directions")
    runner = data["runner"]
    _need(set(runner) == {"binding", "files"} and runner["binding"] == "local-file-sha256"
        and {r["path"] for r in runner["files"]} == {
            "math_gauge/taste_v130.py", "math_gauge/scoring.py",
            "protocol/mathematical-taste/v1.3.0/policy.json"}, "Shared local runner binding required")
    for ref in runner["files"]:
        _read(POLICY_FILE.parents[3], ref)
    for ref in contract["supporting_references"]:
        _read(root, ref)
    for ref in [data["rules"], *data["rounds"].values(), *data["packet"]]:
        _read(root, ref)
    body = _read(root, next(r for r in data["packet"] if r["path"] == "packet/body.md")).decode()
    _need(not any(word in body for word in contract["packet_forbidden_literals"]),
          "Participant body contains private identity or excluded references")
    _need(not re.search(r"https?://|<script|<iframe|\]\((?!\./figures/[a-z0-9-]+\.png\))", body),
          "Body may reference only the fixed local figures")
    for name in re.findall(r"\]\(\./(figures/[a-z0-9-]+\.png)\)", body):
        _need("packet/" + name in paths, "Unbound figure")
    return p, root, data


def _safe_absolute(path):
    p = Path(path).absolute()
    for part in (p, *p.parents):
        _need(not part.is_symlink(), "Symlink in absolute path")
    return p.resolve()


def _source_tree(registration):
    # Keep the participant and evaluator archives outside the entire source repo.
    for parent in registration.parents:
        if (parent / ".git").exists():
            return parent
    return registration.parent


def _seals(state, binding):
    result, previous = {}, None
    if not state.exists():
        return result
    session = _load(_contained(state, "session.json"))
    _need(session["registration_sha256"] == binding, "Session source binding changed")
    for rid in ROUNDS:
        p = _contained(state, f"{rid}.seal.json")
        if not p.exists():
            continue
        seal = _load(p)
        _need(seal["round"] == rid and seal["previous"] == previous
            and seal["registration_sha256"] == binding and len(result) == ROUNDS.index(rid),
            "Broken round chain")
        issued = _load(_contained(state, f"{rid}.issued.json"))
        _need(issued["registration_sha256"] == binding and issued["context_id"] == session["context_id"]
            and issued["workspace"] == session["workspace"] and issued["round"] == rid
            and issued["prompt_sha256"] == seal["prompt_sha256"], "Broken issue/session binding")
        observation = json.loads(_read(state, seal["observation"]))
        _need(observation["delivery"] == seal["delivery"] and observation["round"] == rid
            and observation["context_id"] == session["context_id"],
              "Observation differs from sealed outcome")
        if seal["raw"] is not None:
            raw = _read(state, seal["raw"])
            _need(seal["raw"]["path"] == f"{rid}.md" and raw.decode().strip()
                and all(observation["raw"][k] == seal["raw"][k] for k in ("bytes", "sha256")),
                "Missing or substituted original bytes")
        for ref in seal["files"]:
            _read(state, ref)
        previous = _sha(p.read_bytes())
        result[rid] = seal
    return result


def _layout(registration, state, workspace):
    p, root, data = load_case(registration)
    state, work = _safe_absolute(state), _safe_absolute(workspace)
    def overlap(a, b):
        return a == b or a.is_relative_to(b) or b.is_relative_to(a)
    _need(not overlap(state,work) and not overlap(work,_source_tree(p)) and not overlap(state,_source_tree(p))
          and not overlap(work,Path(__file__).resolve().parents[1])
          and not overlap(state,Path(__file__).resolve().parents[1]),
          "Participant workspace, evaluator state, and sources must be separate trees")
    return p, root, data, state, work


def _issued(state, rid, work, token, binding, data):
    p = state / f"{rid}.issued.json"
    value = _load(p)
    _need(value == {"round": rid, "workspace": str(work), "context_id": token,
                    "registration_sha256": binding,
                    "prompt_sha256": data["rounds"][rid]["sha256"]}, "Round not issued here")
    prompt = _contained(work, f"rounds/{rid}.md")
    _need(prompt.is_file() and _sha(prompt.read_bytes()) == value["prompt_sha256"],
          "Issued prompt bytes changed")
    return value


def reveal(registration, state, workspace, rid, context_id):
    """Export only the packet/rules and the requested, currently open round."""
    p, root, data, state, work = _layout(registration, state, workspace)
    _need(rid in ROUNDS and isinstance(context_id,str) and context_id.strip(), "Invalid round/context")
    binding = _sha(p.read_bytes())
    seals = _seals(state, binding)
    index = ROUNDS.index(rid)
    _need(tuple(seals) == ROUNDS[:index] and all(
        s["delivery"] == "normal-final" for s in seals.values()), "Previous normal final must be frozen first")
    if index == 0:
        _need(not state.exists() and not work.exists(), "R1 needs fresh empty trees")
        state.mkdir(mode=0o700)
        work.mkdir(mode=0o700)
        (work / "rounds").mkdir()
        _new(state / "session.json", _json({"context_id": context_id,
            "registration_sha256": binding, "workspace": str(work),
            "isolation": "not-provided-by-this-offline-tool",
            "native_context_freshness": "operator-must-establish-separately"}))
        for ref in [data["rules"], *data["packet"]]:
            name = "rules.md" if ref == data["rules"] else ref["path"]
            path = _contained(work, name)
            path.parent.mkdir(parents=True, exist_ok=True)
            _new(path, _read(root, ref))
    else:
        _issued(state, "R1", work, context_id, binding, data)
        for ref in data["packet"]:
            _read(work, ref)
        _read(work, {**data["rules"], "path": "rules.md"})
    _need({f.name for f in (work / "rounds").iterdir()} == set(f"{r}.md" for r in ROUNDS[:index]),
          "Unexpected or prematurely exposed round prompt")
    prompt = _contained(work, f"rounds/{rid}.md")
    _new(prompt, _read(root, data["rounds"][rid]))
    _new(state/f"{rid}.issued.json", _json({"round":rid, "workspace":str(work),
        "context_id":context_id, "registration_sha256":binding,
        "prompt_sha256":data["rounds"][rid]["sha256"]}))
    return prompt


def _candidate_inputs(work, data, through):
    for ref in data["packet"]:
        _read(work, ref)
    _read(work, {**data["rules"], "path": "rules.md"})
    for rid in ROUNDS[:through]:
        _read(work, {**data["rounds"][rid], "path": f"rounds/{rid}.md"})
    _need({p.name for p in (work/"rounds").iterdir()} == {f"{r}.md" for r in ROUNDS[:through]},
          "Unexpected or prematurely exposed prompt")


def seal_final(registration, state, workspace, rid, context_id, answer, observation):
    """Freeze an operator-collected first final or explicit failed/unresolved boundary.

    Observation is an original operator sidecar, never a fabricated CLI/native receipt.
    This function neither launches a process nor certifies the operator's assertions.
    """
    p, _, data, state, work = _layout(registration, state, workspace)
    _need(rid in ROUNDS, "Invalid round")
    binding = _sha(p.read_bytes())
    seals = _seals(state, binding)
    index = ROUNDS.index(rid)
    _need(tuple(seals) == ROUNDS[:index], "Round already sealed or out of order")
    _issued(state, rid, work, context_id, binding, data)
    _candidate_inputs(work, data, index + 1)
    observation_path = _safe_absolute(observation)
    _need(not observation_path.is_relative_to(work), "Operator observation must stay outside candidate tree")
    original_observation = observation_path.read_bytes()
    obs = json.loads(original_observation)
    _need(set(obs) == {"schema", "round", "context_id", "request_id", "kind", "delivery",
        "first_normal_final", "boundary", "native_terminal", "raw", "delivered_files"}
        and obs["schema"] == "math-gauge.research-round-observation/v1"
        and obs["round"] == rid and obs["context_id"] == context_id
        and isinstance(obs["request_id"], str) and obs["request_id"].strip()
        and obs["kind"] in {"operator-attestation", "fixture"}
        and obs["delivery"] in {"normal-final", "delivery-failed", "unresolved"}, "Invalid operator observation")
    _need(set(obs["boundary"]) == {"kind", "at"}
        and obs["boundary"]["kind"] in {"first-normal-final", "deadline", "native-terminal", "unavailable"}
        and (obs["boundary"]["at"] is None or isinstance(obs["boundary"]["at"], str))
        and (obs["native_terminal"] is None or isinstance(obs["native_terminal"], str)), "Invalid boundary")
    normal = obs["delivery"] == "normal-final"
    _need((normal and obs["first_normal_final"] is True and answer is not None
        and obs["boundary"]["kind"] == "first-normal-final"
        and (obs["native_terminal"] is None or obs["native_terminal"].upper() != "ERROR")) or (not normal and obs["first_normal_final"] is None
        and answer is None and obs["raw"] is None and obs["delivered_files"] == []),
        "Only the first normal final may become a normal delivery; missing evidence is not success")
    snapshots = []
    if normal:
        supplied = _safe_absolute(answer)
        _need(supplied.is_relative_to(work) and supplied.is_file() and supplied.suffix == ".md"
            and not supplied.is_relative_to(work/"packet") and not supplied.is_relative_to(work/"rounds")
            and supplied != work/"rules.md", "Final must be a distinct current-workspace Markdown file")
        _need(obs["raw"]["path"] == supplied.relative_to(work).as_posix(), "Observation binds another answer")
        raw = _read(work, obs["raw"])
        _need(raw.decode().strip(), "Empty normal final")
        snapshots.append((f"{rid}.md", raw))
        seen = {obs["raw"]["path"]}
        for ref in obs["delivered_files"]:
            name = ref["path"]
            _need(name not in seen and name.split('/')[0] not in {"packet", "rounds"}
                and name != "rules.md", "Duplicate or supplied input is not a delivered artifact")
            seen.add(name)
            snapshots.append((f"{rid}.files/{name}", _read(work, ref)))
    else:
        raw = None
    # Validate every input before writing the immutable seal marker last.
    for name, payload in snapshots:
        target = _contained(state, name)
        target.parent.mkdir(parents=True, exist_ok=True)
        _new(target, payload)
    observation_name = f"{rid}.observation.json"
    _new(state/observation_name, original_observation)
    def descriptor(name, payload):
        return {"path": name, "bytes": len(payload), "sha256": _sha(payload)}
    prior = _sha((state/f"{ROUNDS[index-1]}.seal.json").read_bytes()) if index else None
    _new(state/f"{rid}.seal.json", _json({"round": rid, "previous": prior,
        "registration_sha256": binding, "prompt_sha256": data["rounds"][rid]["sha256"],
        "delivery": obs["delivery"], "raw": descriptor(f"{rid}.md", raw) if normal else None,
        "files": [descriptor(n, b) for n, b in snapshots[1:]],
        "observation": descriptor(observation_name, original_observation)}))
    return _sha(raw) if normal else obs["delivery"]


def _evidence(value, state, seals, permitted):
    _need(isinstance(value, list) and value, "Need evidence from original delivered bytes")
    for ref in value:
        _need(set(ref) == {"round", "file", "start", "end", "quote"}
            and ref["round"] in permitted, "Invalid evidence citation")
        seal = seals[ref["round"]]
        files = {r["path"]: r for r in [seal["raw"], *seal["files"]] if r is not None}
        _need(ref["file"] in files, "Evidence must cite that round's actual delivery")
        raw = _read(state, files[ref["file"]])
        a, z = ref["start"], ref["end"]
        _need(type(a) is int and type(z) is int and 0 <= a < z <= len(raw)
            and raw[a:z].decode().strip() and raw[a:z].decode() == ref["quote"], "Bad UTF-8 quotation")


def _gate(values):
    return False if False in values else True if all(v is True for v in values) else None


def validate_review(registration, state, output):
    """Check binding/coverage and noncompensating gates, never judge mathematical truth."""
    p, root, data = load_case(registration)
    state = _safe_absolute(state)
    _need(not state.is_relative_to(_source_tree(p)), "Use an independent evaluator archive")
    binding = _sha(p.read_bytes())
    seals = _seals(state, binding)
    _need(tuple(seals) == ROUNDS and all(s["delivery"] == "normal-final" for s in seals.values()),
          "A complete review requires all three original normal finals")
    review_path = _safe_absolute(output)
    _need(not review_path.is_relative_to(Path(_load(state/"session.json")["workspace"])),
          "Evaluator review must stay outside participant tree")
    out = _load(review_path)
    contract = json.loads(_read(root, data["review_contract"]))
    _need(set(out) == {"schema", "edition", "case_id", "registration_sha256", "sealed_finals",
        "reviewer_id", "reviewer_context_id", "reviewer_kind", "human_review", "axes", "gates",
        "round_reviews", "selection_audit", "error_roots"}
        and out["schema"] == REVIEW and out["edition"] == EDITION and out["case_id"] == data["case_id"]
        and out["registration_sha256"] == binding and out["reviewer_kind"] in {"human", "ai", "fixture"}
        and out["human_review"] in {"pending", "approved"}
        and (out["human_review"] != "approved" or out["reviewer_kind"] == "human")
        and isinstance(out["reviewer_id"], str) and out["reviewer_id"].strip()
        and isinstance(out["reviewer_context_id"], str) and out["reviewer_context_id"].strip()
        and out["reviewer_context_id"] != _load(state/"session.json")["context_id"]
        and out["sealed_finals"] == {rid: _sha((state/f"{rid}.seal.json").read_bytes()) for rid in ROUNDS}
        and set(out["axes"]) == set(AXES) and set(out["gates"]) == set(AXES)
        and set(out["round_reviews"]) == set(AXES), "Unbound or nonindependent private review")
    def judgment(row, allowed, fields):
        _need(set(row) == set(fields) | {"reason", "evidence"}
            and isinstance(row["reason"], str) and row["reason"].strip(), "Invalid judgment")
        active = False
        for field in fields:
            v = row[field]
            _need(v is None or (type(v) is bool if field in {"strict", "verdict"} else
                type(v) in (int, float) and 0 <= v <= 100), "Invalid score or flag")
            active |= v is not None
        if active:
            _evidence(row["evidence"], state, seals, allowed)
        else:
            _need(row["evidence"] == [], "Unassessed is unknown, without invented evidence")
    for axis in AXES:
        value = out["axes"][axis]
        judgment(value, set(ROUNDS), ("score", "strict"))
        coverage = set(contract["round_coverage"][axis])
        rounds = out["round_reviews"][axis]
        _need(set(rounds) == coverage, "Missing per-manuscript review")
        for rid, row in rounds.items():
            judgment(row, {rid}, ("score", "strict"))
        if value["score"] is not None or value["strict"] is True:
            _need(all(row["score"] is not None for row in rounds.values()), "Missing manuscript assessment")
        gates = out["gates"][axis]
        _need(set(gates) == {g["id"] for g in contract["gates"][axis]}, "Wrong private gate set")
        for spec in contract["gates"][axis]:
            judgment(gates[spec["id"]], set(spec["rounds"]), ("verdict",))
            if gates[spec["id"]]["verdict"] is True:
                _need(set(spec["rounds"]) <= {r["round"] for r in gates[spec["id"]]["evidence"]},
                      "Strict gate needs evidence across all specified manuscripts")
        _need(value["strict"] is _gate([gates[g["id"]]["verdict"]
            for g in contract["gates"][axis] if g["required"]]), "Strict must equal all required gates")
    selection = out["selection_audit"]
    _need(set(selection) == {"sufficient_choices", "reason", "kept", "removed"}
        and (selection["sufficient_choices"] is None or type(selection["sufficient_choices"]) is bool)
        and isinstance(selection["reason"], str) and selection["reason"].strip(), "Invalid selection audit")
    for key, allowed in [("kept", {"R3"}), ("removed", {"R1", "R2"})]:
        if selection[key]:
            _evidence(selection[key], state, seals, allowed)
    _need(out["axes"]["taste"]["strict"] is not True or
        (selection["sufficient_choices"] is True and selection["kept"]),
        "No high taste verdict merely for producing no selectable mathematics")
    if selection["sufficient_choices"] is not True:
        _need(out["axes"]["taste"]["score"] is None, "Insufficient choices require unknown taste grade")
    if any(json.loads(_read(state, seal["observation"]))["kind"] == "fixture" for seal in seals.values()):
        _need(out["reviewer_kind"] == "fixture", "Fixture deliveries must never become actual model reviews")
    roots = out["error_roots"]
    _need(isinstance(roots, list) and len({r["id"] for r in roots}) == len(roots), "Duplicate error root")
    for row in roots:
        _need(set(row) == {"id", "effects", "reason", "evidence"} and row["effects"]
            and set(row["effects"]) <= set(AXES) and all(isinstance(v, str) and v.strip()
                for v in row["effects"].values()) and row["reason"].strip(), "Explain each distinct axis effect")
        _evidence(row["evidence"], state, seals, set(ROUNDS))
    return out["axes"]


def review_template(registration, state, reviewer_id, reviewer_context_id):
    p, root, data = load_case(registration)
    state = _safe_absolute(state)
    seals = _seals(state, _sha(p.read_bytes()))
    _need(tuple(seals) == ROUNDS and all(s["delivery"] == "normal-final" for s in seals.values()),
          "Template requires three normal finals")
    contract = json.loads(_read(root, data["review_contract"]))
    def blank(*fields):
        return {**dict.fromkeys(fields), "reason": "Pending independent assessment", "evidence": []}
    return dict(schema=REVIEW, edition=EDITION, case_id=data["case_id"],
        registration_sha256=_sha(p.read_bytes()),
        sealed_finals={r: _sha((state/f"{r}.seal.json").read_bytes()) for r in ROUNDS},
        reviewer_id=reviewer_id, reviewer_context_id=reviewer_context_id,
        reviewer_kind="fixture" if any(json.loads(_read(state, s["observation"]))["kind"] == "fixture"
            for s in seals.values()) else "ai", human_review="pending",
        axes={axis: blank("score", "strict") for axis in AXES},
        gates={axis: {g["id"]: blank("verdict") for g in contract["gates"][axis]} for axis in AXES},
        round_reviews={axis: {r: blank("score", "strict") for r in contract["round_coverage"][axis]}
            for axis in AXES}, selection_audit=dict(sufficient_choices=None,
                reason="Pending availability and selection audit", kept=[], removed=[]), error_roots=[])


def preview(base, base_axes, *, status, review=None, policy_path=POLICY_FILE, base_groups=None):
    """Delegate all arithmetic to the shared scoring owner; no legacy score rewrite."""
    from .scoring import score_research_preview
    return score_research_preview(base, base_axes, status=status, review=review,
                                  policy=_load(policy_path), base_groups=base_groups)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    cmd=parser.add_subparsers(dest="command",required=True)
    info=cmd.add_parser("check-case");info.add_argument("registration")
    for name in ("reveal","seal"):
        c=cmd.add_parser(name)
        for key in ("registration","state","workspace"): c.add_argument(key)
        c.add_argument("round",choices=ROUNDS);c.add_argument("context_id")
        if name=="seal":
            c.add_argument("answer", help="Final Markdown path, or - for failed/unresolved delivery")
            c.add_argument("observation")
    for name in ("check-review","score"):
        c=cmd.add_parser(name)
        for key in ("registration","state","review"): c.add_argument(key)
        if name=="score":c.add_argument("base")
    t=cmd.add_parser("review-template")
    for key in ("registration", "state", "reviewer_id", "reviewer_context_id", "output"):
        t.add_argument(key)
    a=parser.parse_args()
    if a.command=="check-case":
        _,_,registration=load_case(a.registration)
        print(json.dumps({"edition":EDITION,"rounds":len(registration["rounds"]),"candidate_calls":0}))
    if a.command=="reveal": print(reveal(a.registration,a.state,a.workspace,a.round,a.context_id))
    if a.command=="seal": print(seal_final(a.registration,a.state,a.workspace,a.round,a.context_id,None if a.answer == "-" else a.answer,a.observation))
    if a.command == "review-template":
        _new(_safe_absolute(a.output), _json(review_template(a.registration, a.state,
            a.reviewer_id, a.reviewer_context_id)))
    if a.command in {"check-review","score"}:
        review=validate_review(a.registration,a.state,a.review)
        if a.command=="check-review": print("Validated evaluator evidence and score structure.")
        else:
            base=_load(a.base);print(_json(preview(base["scores"],base["abilities"],status="reviewed",review=review,base_groups=base.get("groups"))).decode(),end="")


if __name__ == "__main__":
    main()
