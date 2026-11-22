"""Evaluator-only review of all three sealed independent-research manuscripts."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from . import taste_v130 as flow


POLICY = "math-gauge.independent-research-review-policy/v1"
REVIEW = "math-gauge.independent-research-trajectory-review/v1"
POLICY_NAME = "trajectory-review-policy.json"
CAPACITY_PENDING = "Pending independent cross-round assessment"


def _policy_binding(registration_path, case_root, registration, review_policy):
    path = flow._safe_absolute(review_policy)
    flow._need(path == case_root / "evaluator" / POLICY_NAME,
               "Use the case's private trajectory review policy")
    raw = path.read_bytes()
    data = json.loads(raw)
    expected = {
        "schema": POLICY, "edition": flow.EDITION,
        "registration_sha256": flow._sha(registration_path.read_bytes()),
        "base_review_contract_sha256": registration["review_contract"]["sha256"],
        "capacity_aggregation": "whole-three-round-trajectory",
    }
    flow._need(isinstance(data, dict) and set(data) == set(expected) | {"rubric", "provenance"}
               and all(data[key] == value for key, value in expected.items()),
               "Trajectory review policy does not bind the original case and review contract")
    for key, name in (("rubric", "rubric-trajectory.md"),
                      ("provenance", "review-correction-provenance.json")):
        ref = data[key]
        flow._need(isinstance(ref, dict) and ref.get("path") == name,
                   "Invalid private trajectory policy companion")
        flow._read(path.parent, ref)
    return flow._sha(raw)


def policy_sha256(registration, review_policy):
    """Verify the supplement and its original case and companion bytes."""
    registration_path, case_root, data = flow.load_case(registration)
    return _policy_binding(registration_path, case_root, data, review_policy)


def review_template(registration, state, reviewer_id, reviewer_context_id, review_policy):
    binding = policy_sha256(registration, review_policy)
    draft = flow.review_template(registration, state, reviewer_id, reviewer_context_id)
    draft.update(schema=REVIEW, review_policy_sha256=binding)
    draft["round_reviews"]["capacity"] = {
        rid: deepcopy(draft["axes"]["capacity"]) for rid in flow.ROUNDS
    }
    for gate in draft["gates"]["capacity"].values():
        gate["reason"] = CAPACITY_PENDING
    return draft


def _judgment(row, state, seals, permitted, fields):
    flow._need(isinstance(row, dict) and set(row) == set(fields) | {"reason", "evidence"}
               and isinstance(row.get("reason"), str) and row["reason"].strip(),
               "Invalid judgment")
    active = False
    for field in fields:
        value = row[field]
        flow._need(value is None or (type(value) is bool if field in {"strict", "verdict"}
                   else type(value) in (int, float) and 0 <= value <= 100),
                   "Invalid score or flag")
        active |= value is not None
    if active:
        flow._evidence(row["evidence"], state, seals, permitted)
        return {ref["round"] for ref in row["evidence"]}
    flow._need(row["evidence"] == [], "Unassessed is unknown, without invented evidence")
    return set()


def validate_review(registration, state, output, review_policy):
    """Validate review binding, coverage and flags. Mathematical findings remain reviewer judgments."""
    registration_path, case_root, data = flow.load_case(registration)
    state = flow._safe_absolute(state)
    flow._need(not state.is_relative_to(flow._source_tree(registration_path)),
               "Use an independent evaluator archive")
    binding = flow._sha(registration_path.read_bytes())
    seals = flow._seals(state, binding)
    rounds = set(flow.ROUNDS)
    flow._need(tuple(seals) == flow.ROUNDS and all(s["delivery"] == "normal-final" for s in seals.values()),
               "A complete review requires all three original normal finals")
    session = flow._load(state / "session.json")
    review_path = flow._safe_absolute(output)
    flow._need(not review_path.is_relative_to(Path(session["workspace"])),
               "Evaluator review must stay outside participant tree")
    out = flow._load(review_path)
    flow._need(isinstance(out, dict) and out.get("schema") == REVIEW,
               "A whole-trajectory review is required; legacy R3-only reviews are archived")
    immutable = {
        "schema": REVIEW, "edition": flow.EDITION, "case_id": data["case_id"],
        "registration_sha256": binding,
        "review_policy_sha256": _policy_binding(registration_path, case_root, data, review_policy),
        "sealed_finals": {rid: flow._sha((state / f"{rid}.seal.json").read_bytes()) for rid in flow.ROUNDS},
    }
    axes = set(flow.AXES)
    flow._need(set(out) == set(immutable) | {"reviewer_id", "reviewer_context_id", "reviewer_kind",
               "human_review", "axes", "gates", "round_reviews", "selection_audit", "error_roots"}
               and all(out[key] == value for key, value in immutable.items())
               and out["reviewer_kind"] in {"human", "ai", "fixture"}
               and out["human_review"] in {"pending", "approved"}
               and (out["human_review"] != "approved" or out["reviewer_kind"] == "human")
               and all(isinstance(out[key], str) and out[key].strip()
                       for key in ("reviewer_id", "reviewer_context_id"))
               and out["reviewer_context_id"] != session["context_id"]
               and all(isinstance(out[key], dict) and set(out[key]) == axes
                       for key in ("axes", "gates", "round_reviews")),
               "Unbound or nonindependent private trajectory review")
    contract = json.loads(flow._read(case_root, data["review_contract"]))
    for axis in flow.AXES:
        capacity = axis == "capacity"
        value = out["axes"][axis]
        cited = _judgment(value, state, seals, rounds, ("score", "strict"))
        if capacity and cited:
            flow._need(cited == rounds, "Capacity assessment must cite all three manuscripts")
        coverage = rounds if capacity else set(contract["round_coverage"][axis])
        by_round = out["round_reviews"][axis]
        flow._need(isinstance(by_round, dict) and set(by_round) == coverage,
                   "Missing per-manuscript review")
        for rid, judgment in by_round.items():
            _judgment(judgment, state, seals, {rid}, ("score", "strict"))
        if value["score"] is not None or value["strict"] is True:
            flow._need(all(row["score"] is not None for row in by_round.values()),
                       "Missing manuscript assessment")
        gates = out["gates"][axis]
        specs = contract["gates"][axis]
        flow._need(isinstance(gates, dict) and set(gates) == {spec["id"] for spec in specs},
                   "Wrong private gate set")
        for spec in specs:
            gate = gates[spec["id"]]
            permitted = rounds if capacity else set(spec["rounds"])
            evidence = _judgment(gate, state, seals, permitted, ("verdict",))
            if capacity and gate["verdict"] is not None:
                flow._need(gate["reason"].strip() != CAPACITY_PENDING,
                           "Explain the capacity gate's cross-round state")
            if not capacity and gate["verdict"] is True:
                flow._need(permitted <= evidence,
                           "Strict gate needs evidence across all specified manuscripts")
        flow._need(value["strict"] is flow._gate([gates[spec["id"]]["verdict"]
                   for spec in specs if spec["required"]]),
                   "Strict must equal all required gates")

    selection = out["selection_audit"]
    flow._need(isinstance(selection, dict) and set(selection) == {"sufficient_choices", "reason", "kept", "removed"}
               and (selection["sufficient_choices"] is None or type(selection["sufficient_choices"]) is bool)
               and isinstance(selection["reason"], str) and selection["reason"].strip(), "Invalid selection audit")
    for key, allowed in (("kept", {"R3"}), ("removed", {"R1", "R2"})):
        if selection[key]:
            flow._evidence(selection[key], state, seals, allowed)
    taste = out["axes"]["taste"]
    flow._need(taste["strict"] is not True or (selection["sufficient_choices"] is True and selection["kept"]),
               "No high taste verdict merely for producing no selectable mathematics")
    if selection["sufficient_choices"] is not True:
        flow._need(taste["score"] is None, "Insufficient choices require unknown taste grade")
    if any(json.loads(flow._read(state, seal["observation"]))["kind"] == "fixture" for seal in seals.values()):
        flow._need(out["reviewer_kind"] == "fixture", "Fixture deliveries must never become actual model reviews")
    roots = out["error_roots"]
    flow._need(isinstance(roots, list) and len({row["id"] for row in roots}) == len(roots),
               "Duplicate error root")
    for row in roots:
        flow._need(set(row) == {"id", "effects", "reason", "evidence"} and row["effects"]
                   and set(row["effects"]) <= axes and all(isinstance(value, str) and value.strip()
                   for value in row["effects"].values()) and row["reason"].strip(),
                   "Explain each distinct axis effect")
        flow._evidence(row["evidence"], state, seals, rounds)
    return out["axes"]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="mode", required=True)
    for mode in ("template", "check"):
        command = commands.add_parser(mode)
        command.add_argument("registration")
        command.add_argument("state")
        command.add_argument("review_policy")
        if mode == "template":
            command.add_argument("reviewer_id")
            command.add_argument("reviewer_context_id")
        command.add_argument("output" if mode == "template" else "review")
    args = parser.parse_args(argv)
    try:
        if args.mode == "template":
            state = flow._safe_absolute(args.state)
            output = flow._safe_absolute(args.output)
            workspace = Path(flow._load(state / "session.json")["workspace"])
            flow._need(not output.is_relative_to(workspace), "Evaluator review must stay outside participant tree")
            template = review_template(args.registration, state, args.reviewer_id,
                                       args.reviewer_context_id, args.review_policy)
            flow._new(output, flow._json(template))
        else:
            validate_review(args.registration, args.state, args.review, args.review_policy)
            print(json.dumps({"status": "checked", "schema": REVIEW}))
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"trajectory-review: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
