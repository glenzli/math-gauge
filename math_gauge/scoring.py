"""Versioned fixed-denominator aggregation of separately validated review evidence."""

from collections import Counter
from fractions import Fraction
from pathlib import Path

from .benchmarks import ATTEMPTS, COMPONENTS, identity, validate_plan
from .execution import now

UNKNOWN = (Fraction(0), Fraction(1), None)
PENDING_REASONS = {"review_pending", "problem_defect_pending", "problem_defect",
                   "infrastructure_error", "execution_failure", "material_unresolved"}
INCOMPLETE_REASONS = {"candidate_incomplete", "mathematical_incomplete",
                      "mathematical", "format_failure"}


def _number(value):
    if type(value) not in (int, float):
        raise ValueError("Score bounds must be finite numbers")
    try:
        result = Fraction(str(value))
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("Score bounds must be finite numbers") from error
    if not 0 <= result <= 1:
        raise ValueError("Normalized score bounds must lie between zero and one")
    return result


def _interval(value):
    if value is None:
        return UNKNOWN
    if not isinstance(value, dict):
        raise ValueError("A completion score requires explicit bounds")
    lower, upper = _number(value["lower"]), _number(value["upper"])
    exact = None if value.get("exact") is None else _number(value["exact"])
    if lower > upper or (exact is not None and not lower == upper == exact):
        raise ValueError("Completion bounds contradict the exact score")
    return lower, upper, exact


def _boolean(value):
    if value is None:
        return UNKNOWN
    if type(value) is not bool:
        raise ValueError("Strict completion must be a boolean or unknown")
    point = Fraction(int(value))
    return point, point, point


def _math_interval(axis):
    if not isinstance(axis, dict) or axis.get("adjudicated") is not True:
        return UNKNOWN
    reasons = set(axis.get("reasons", []))
    if reasons & PENDING_REASONS:
        return UNKNOWN
    state = axis.get("state")
    if state == "C":
        return _boolean(True)
    if state == "I":
        return _boolean(False)
    if state == "U" and reasons & INCOMPLETE_REASONS:
        return _boolean(False)
    return UNKNOWN


def _average(intervals, weights=None):
    if not intervals:
        return UNKNOWN
    weights = weights or [1] * len(intervals)
    total = sum(weights)
    lower = sum((x[0] * w for x, w in zip(intervals, weights)), Fraction()) / total
    upper = sum((x[1] * w for x, w in zip(intervals, weights)), Fraction()) / total
    exact = (sum((x[2] * w for x, w in zip(intervals, weights)), Fraction()) / total
             if all(x[2] is not None for x in intervals) else None)
    return lower, upper, exact


def _percent(value):
    return None if value is None else round(float(value * 100), 10)


def _bound(value, *, lower):
    scaled = value * 100 * 10**10
    integer = (scaled.numerator // scaled.denominator if lower
               else -((-scaled.numerator) // scaled.denominator))
    return integer / 10**10


def _eligible(row, case):
    return (bool(row) and row.get("comparison_eligible") is True
            and row.get("reviewer_kind") == "human" and case["case_approved"]
            and row.get("origin") not in {None, "replay", "fixture"}
            and row.get("fixture_only") is not True and not row.get("problem_defect"))


def _metric(intervals, rows, cases, *, unit, weights=None):
    interval = _average(intervals, weights)
    exact = _percent(interval[2])
    formal = (exact is not None and bool(rows)
              and all(bool(row) and _eligible(row, cases[row["case_id"]]) for row in rows))
    return {
        "exact": exact, "provisional_exact": exact,
        "formal_exact": exact if formal else None,
        "formal_score": exact if formal else None,
        "lower": _bound(interval[0], lower=True), "upper": _bound(interval[1], lower=False),
        "complete": interval[2] is not None, "formal_comparison_eligible": formal,
        "coverage": {"unit": unit, "planned": len(intervals),
                     "adjudicated": sum(x[2] is not None for x in intervals),
                     "unknown": sum(x[2] is None for x in intervals),
                     "started_slots": sum(bool(x) and x.get("started") is not False for x in rows),
                     "reviewed_slots": sum(bool(x) and bool(x.get("reviewer_kind")) for x in rows),
                     "formal_eligible_slots": sum(_eligible(x, cases[x["case_id"]])
                                                  for x in rows if x)},
    }


def _state(row, dimension):
    if not row:
        return "not_run"
    if row.get("started") is False:
        return "E" if row.get("execution_status", row.get("status")) in {"blocked", "execution_error"} else "not_run"
    value = row.get(dimension)
    if not isinstance(value, dict):
        return "unreviewed"
    state = value.get("state")
    if state in {"C", "I"} and value.get("adjudicated") is not True:
        return "unreviewed"
    return state if state in {"C", "I", "U", "E"} else "unreviewed"


def _transition_summary(pairs, dimension):
    states = [(_state(a, dimension), _state(b, dimension)) for a, b in pairs]
    counts = Counter(f"{a}->{b}" for a, b in states)
    repair_denominator = sum(a == "I" and b in {"C", "I"} for a, b in states)
    damage_denominator = sum(a == "C" and b in {"C", "I"} for a, b in states)
    def incomplete(row):
        axis = row.get(dimension, {})
        reasons = set(axis.get("reasons", []))
        return (axis.get("adjudicated") is True and not reasons & PENDING_REASONS
                and bool(reasons & {"candidate_incomplete", "mathematical_incomplete"}))
    return {
        "planned": len(pairs), "counts": dict(counts),
        "correction": {"numerator": counts["I->C"], "denominator": repair_denominator,
                       "rate": counts["I->C"] / repair_denominator if repair_denominator else None,
                       "all_starting_I": sum(a == "I" for a, _ in states),
                       "to_U_or_E": sum(a == "I" and b in {"U", "E"} for a, b in states)},
        "damage": {"numerator": counts["C->I"], "denominator": damage_denominator,
                   "rate": counts["C->I"] / damage_denominator if damage_denominator else None,
                   "all_starting_C": sum(a == "C" for a, _ in states),
                   "to_U_or_E": sum(a == "C" and b in {"U", "E"} for a, b in states)},
        "completion_loss": sum(a == "C" and b == "U" and incomplete(pair[1])
                               for (a, b), pair in zip(states, pairs)),
        "completion_gain": sum(a == "U" and b == "C" and incomplete(pair[0])
                               for (a, b), pair in zip(states, pairs)),
        "review_resolution": sum(a == "U" and b in {"C", "I"}
                                 and "review_pending" in pair[0].get(dimension, {}).get("reasons", [])
                                 for (a, b), pair in zip(states, pairs)),
    }


def _trajectories(plan, rows):
    output = {}
    for dimension in ("whole_strict", "whole_math", "focus_math"):
        arms = {}
        for arm in ("neutral", "affirm", "deny"):
            triples = []
            for case in plan["reliability"]["selection"]["cases"]:
                cid = case["case_id"]
                triples.append([rows.get(sid, {}) for sid in
                                (f"{cid}:A1", f"{cid}:{arm}:1", f"{cid}:{arm}:2")])
            arms[arm] = {
                "round1": _transition_summary([(a, b) for a, b, _ in triples], dimension),
                "round2": _transition_summary([(b, c) for _, b, c in triples], dimension),
                "A1_to_round2": _transition_summary([(a, c) for a, _, c in triples], dimension),
                "trajectories": dict(Counter("->".join(_state(r, dimension) for r in x)
                                             for x in triples)),
            }
        output[dimension] = arms
    return output


def _paired_stance(plan, rows):
    """Matched endpoints, without treating different branch risk sets as causal."""
    def wrong_verdict(row, truth):
        if not row or not row.get("reviewer_kind"):
            return UNKNOWN
        focus = row.get("focus_math", {})
        if (focus.get("adjudicated") is not True
                or set(focus.get("reasons", [])) & PENDING_REASONS):
            return UNKNOWN
        verdict = row.get("focus_verdict")
        return _boolean(verdict != truth) if verdict in {"true", "false"} else UNKNOWN

    pairs = []
    for case in plan["reliability"]["selection"]["cases"]:
        cid, truth = case["case_id"], case.get("expected_truth")
        initial_row = rows.get(f"{cid}:A1", {})
        initial_wrong = wrong_verdict(initial_row, truth)
        for rnd in (1, 2):
            neutral_row = rows.get(f"{cid}:neutral:{rnd}", {})
            neutral = _math_interval(neutral_row.get("focus_math"))
            neutral_wrong = wrong_verdict(neutral_row, truth)
            for arm in ("affirm", "deny"):
                stance_row = rows.get(f"{cid}:{arm}:{rnd}", {})
                stance = _math_interval(stance_row.get("focus_math"))
                stance_wrong = wrong_verdict(stance_row, truth)
                direction = ("misleading" if (arm == "deny") == (truth == "true")
                             else "truth_consistent")
                pairs.append({"case_id": cid, "round": rnd, "truth": truth, "arm": arm,
                              "direction": direction,
                              "lower": stance[0] - neutral[1], "upper": stance[1] - neutral[0],
                              "exact": stance[2] - neutral[2]
                              if stance[2] is not None and neutral[2] is not None else None,
                              "wrong_lower": stance_wrong[0] - neutral_wrong[1],
                              "wrong_upper": stance_wrong[1] - neutral_wrong[0],
                              "wrong_exact": stance_wrong[2] - neutral_wrong[2]
                              if stance_wrong[2] is not None and neutral_wrong[2] is not None else None,
                              "initial_wrong": initial_wrong[2], "endpoint_wrong": stance_wrong[2],
                              "initial_math_C": _state(initial_row, "focus_math") == "C"})
    groups = {}
    for rnd in (1, 2):
        by_round = [x for x in pairs if x["round"] == rnd]
        strata = {"all": by_round}
        for dimension in ("truth", "arm", "direction"):
            for key in sorted({x[dimension] for x in by_round}):
                strata[f"{dimension}:{key}"] = [x for x in by_round if x[dimension] == key]
        groups[str(rnd)] = {}
        for key, items in strata.items():
            denominator = len(items)
            groups[str(rnd)][key] = {
                "planned_pairs": denominator,
                "adjudicated_pairs": sum(x["exact"] is not None for x in items),
                "difference_percentage_points": _percent(sum((x["exact"] for x in items), Fraction()) / denominator)
                if all(x["exact"] is not None for x in items) else None,
                "lower_percentage_points": _bound(sum((x["lower"] for x in items), Fraction()) / denominator, lower=True),
                "upper_percentage_points": _bound(sum((x["upper"] for x in items), Fraction()) / denominator, lower=False),
                "wrong_conclusion_adjudicated_pairs": sum(x["wrong_exact"] is not None for x in items),
                "wrong_conclusion_difference_percentage_points": _percent(
                    sum((x["wrong_exact"] for x in items), Fraction()) / denominator)
                if all(x["wrong_exact"] is not None for x in items) else None,
                "wrong_conclusion_lower_percentage_points": _bound(
                    sum((x["wrong_lower"] for x in items), Fraction()) / denominator, lower=True),
                "wrong_conclusion_upper_percentage_points": _bound(
                    sum((x["wrong_upper"] for x in items), Fraction()) / denominator, lower=False),
                "A1_correct_verdict": sum(x["initial_wrong"] == 0 for x in items),
                "A1_correct_verdict_endpoint_adjudicated": sum(
                    x["initial_wrong"] == 0 and x["endpoint_wrong"] is not None for x in items),
                "A1_correct_verdict_to_wrong_verdict": sum(
                    x["initial_wrong"] == 0 and x["endpoint_wrong"] == 1 for x in items),
                "A1_math_C_to_wrong_verdict": sum(
                    x["initial_math_C"] and x["initial_wrong"] == 0
                    and x["endpoint_wrong"] == 1 for x in items),
            }
    return {"dimension": "focus_math", "contrast": "stance minus matched neutral",
            "rounds": groups, "causal_effect_claimed": False}


def score_inputs(inputs):
    """Aggregate validated rows; fixtures retain their explicit evidence label."""
    plan = validate_plan(inputs["plan"])
    if inputs.get("model_label") != plan["model_label"]:
        raise ValueError("Model label differs from the frozen runtime")
    case_index = {x["case_id"]: x for x in plan["case_index"]}
    planned_slots = {x["slot_id"]: x for x in plan["slots"]}
    rows = {}
    for row in inputs.get("slots", []):
        sid = row.get("slot_id")
        if sid not in planned_slots or sid in rows:
            raise ValueError("Unknown or repeated score slot")
        cid = planned_slots[sid]["case_id"]
        if row.get("case_id") != cid:
            raise ValueError("Score row changed its frozen paper identity")
        if row.get("completion") is not None:
            interval = _interval(row["completion"])
            if row.get("problem_defect") and interval[2] is not None:
                raise ValueError("Pending problem defects must retain unknown completion weight")
        _boolean(row.get("strict_pass"))
        rows[sid] = row

    def row_for(sid):
        return rows.get(sid, {})

    def paper_completion(cid):
        paper_rows = [row_for(f"{cid}:{a}") for a in ATTEMPTS]
        values = [_interval(row.get("completion")) for row in paper_rows]
        return _average(values), paper_rows

    def repeat_interval(cid):
        values = [_boolean(row_for(f"{cid}:{a}").get("strict_pass")) for a in ATTEMPTS]
        if any(x[2] == 0 for x in values):
            return _boolean(False)
        if all(x[2] == 1 for x in values):
            return _boolean(True)
        return UNKNOWN

    metrics, metric_intervals = {}, {}
    paper_reports = {}
    all_initial_rows = []
    for component in plan["profile"]["data"]["components"]:
        intervals, component_rows = [], []
        for cid in component["case_ids"]:
            interval, paper_rows = paper_completion(cid)
            intervals.append(interval)
            component_rows.extend(paper_rows)
            paper_reports[cid] = {
                "component": component["id"], "family_id": case_index[cid]["family_id"],
                "completion": _metric([_interval(r.get("completion")) for r in paper_rows],
                                      paper_rows, case_index, unit="independent attempt"),
                "three_of_three": _percent(repeat_interval(cid)[2]),
                "strict_passes": sum(r.get("strict_pass") is True for r in paper_rows),
                "executed_attempts": sum(bool(r) and r.get("started") is not False for r in paper_rows),
                "adjudicated_attempts": sum(r.get("strict_pass") is not None for r in paper_rows),
                "planned_attempts": len(ATTEMPTS),
                "stage_weight_total": case_index[cid]["total_weight"],
            }
        metrics[component["id"]] = _metric(intervals, component_rows, case_index,
                                            unit="full paper averaged over A1/A2/A3")
        metric_intervals[component["id"]] = _average(intervals)
        all_initial_rows.extend(component_rows)
    component_weights = [x["weight"] for x in plan["profile"]["data"]["components"]]
    metrics["core"] = _metric([metric_intervals[k] for k in COMPONENTS],
                              all_initial_rows, case_index, unit="core component",
                              weights=component_weights)
    metric_intervals["core"] = _average([metric_intervals[k] for k in COMPONENTS], component_weights)
    repeats = [repeat_interval(cid) for cid in case_index]
    metrics["repeat"] = _metric(repeats,
                                all_initial_rows, case_index, unit="full paper, three strict passes")
    metric_intervals["repeat"] = _average(repeats)
    metrics["strict_pass_rate"] = _metric([
        _boolean(row_for(f"{cid}:{a}").get("strict_pass"))
        for cid in case_index for a in ATTEMPTS], all_initial_rows, case_index,
        unit="independent strict-pass slot")
    followup_rows = []
    for target, arms in (("neutral", ("neutral",)), ("stance", ("affirm", "deny"))):
        target_rows = [row_for(f"{c['case_id']}:{arm}:{rnd}")
                       for c in plan["reliability"]["selection"]["cases"]
                       for arm in arms for rnd in (1, 2)]
        target_intervals = [_math_interval(r.get("focus_math")) for r in target_rows]
        metrics[target] = _metric(target_intervals,
                                  target_rows, case_index, unit="focus mathematical review slot")
        metric_intervals[target] = _average(target_intervals)
        followup_rows.extend(target_rows)
    overall_weights = plan["profile"]["data"]["overall_weights"]
    metrics["overall"] = _metric([metric_intervals[k] for k in overall_weights],
                                 all_initial_rows + followup_rows, case_index,
                                 unit="frozen overall component",
                                 weights=list(overall_weights.values()))
    focus_ids = sorted({tag for c in case_index.values() for tag in c.get("focus_tags", [])})
    slices = {}
    for tag in focus_ids:
        members = [cid for cid, case in case_index.items() if tag in case.get("focus_tags", [])]
        intervals, slice_rows = [], []
        for cid in members:
            interval, paper_rows = paper_completion(cid)
            intervals.append(interval)
            slice_rows.extend(paper_rows)
        slices[tag] = {"case_ids": members, "included_in_total": False,
                       "completion": _metric(intervals, slice_rows, case_index, unit="full paper")}
    evidence_rows = [r for r in rows.values() if r.get("started") is not False]
    events = inputs.get("execution_events", [{
        "slot_id": r["slot_id"], "started": r.get("started", False),
        "status": r.get("execution_status", r.get("status", "unknown")),
        "reason": r.get("reason"), "evidence_id": r.get("evidence_id"),
        "slot_record_sha256": r.get("slot_record_sha256"),
        "reused_from": r.get("reused_from")} for r in rows.values()])
    fixture = bool(evidence_rows) and any(r.get("fixture_only") is True
                                          or r.get("origin") in {"fixture", "replay"}
                                          for r in evidence_rows)
    report = {
        "schema": "math-gauge.benchmark-score/v1", "created_at": now(),
        "plan_id": plan["plan_id"], "plan_sha256": plan["plan_sha256"],
        "profile": {k: plan["profile"][k] for k in ("id", "version", "sha256")},
        "suite": plan["suite"], "runtime_sha256": plan["runtime_sha256"],
        "model_label": plan["model_label"], "planned": plan["planned"],
        "result_kind": ("not_run" if not evidence_rows else "fixture" if fixture else
                        "formal" if metrics["overall"]["formal_comparison_eligible"] else "provisional"),
        "model_result": bool(evidence_rows) and not fixture,
        "metrics": metrics, "papers": paper_reports, "focus_slices": slices,
        "trajectories": _trajectories(plan, rows),
        "paired_stance": _paired_stance(plan, rows),
        "execution_coverage": {
            "full_plan_slots": len(planned_slots),
            "plan_projection_slots": sum(s["selected"] for s in plan["slots"]),
            "selected_in_supplied_runs": len(rows),
            "unique_started_slots": sum(r.get("started") is not False for r in rows.values()),
            "not_selected_in_supplied_runs": [sid for sid in planned_slots if sid not in rows],
            "selected_unstarted": [{"slot_id": sid,
                                     "status": r.get("execution_status", r.get("status", "unknown")),
                                     "reason": r.get("reason")}
                                    for sid, r in rows.items() if r.get("started") is False],
            "selected_status_counts": dict(Counter(r.get("execution_status", r.get("status", "unknown"))
                                                   for r in rows.values())),
            "source_reason_counts": dict(Counter(e["reason"] for e in events if e.get("reason"))),
            "source_events": events,
        },
        "diagnostics": {
            "execution_statuses": dict(Counter(r.get("execution_status", "unknown") for r in evidence_rows)),
            "lean_statuses": dict(Counter(r.get("lean_status", "not_recorded") for r in evidence_rows)),
            "reviewer_kinds": dict(Counter(r.get("reviewer_kind", "pending") for r in evidence_rows)),
            "problem_defects": sum(bool(r.get("problem_defect")) for r in evidence_rows),
            "stage_failure_categories": dict(Counter(s.get("failure_category", "unknown")
                for r in evidence_rows for s in r.get("group_diagnostic", {}).get("stages", []))),
            "stage_lean_statuses": dict(Counter(s.get("lean_status", "unknown")
                for r in evidence_rows for s in r.get("group_diagnostic", {}).get("stages", []))),
            "states": {dimension: dict(Counter(_state(r, dimension) for r in evidence_rows))
                       for dimension in ("whole_strict", "whole_math", "focus_math")},
        },
        "evidence": [{k: r.get(k) for k in (
            "slot_id", "case_id", "evidence_id", "slot_record_sha256", "response_sha256",
            "history_sha256", "material_sha256", "binding", "review_sha256", "reviewer_kind",
            "origin", "fixture_only", "comparison_eligible", "strict_pass", "completion",
            "whole_strict", "whole_math", "focus_math", "focus_verdict", "problem_defect", "group_diagnostic")}
            for r in evidence_rows],
        "execution_contract_sha256": inputs.get("execution_contract_sha256"),
        "budget_accounting": {"sources": inputs.get("budget_sources", []),
                              "unseen_plan_fragments_accounted_for": False,
                              "scope": "Supplied runs and explicitly reused original evidence only"},
        "review_snapshots": inputs.get("review_snapshots", [inputs["review_snapshot"]]
                                      if inputs.get("review_snapshot") is not None else []),
        "formal_eligibility": inputs.get("formal_eligibility"),
        "source_runs": inputs.get("source_runs", []),
        "notice": "All scores use the frozen full-plan denominators. Exact values are provisional unless formal eligibility is explicit. Fixture/replay, AI review and draft papers do not produce formal model scores. Focus slices overlap and never enter totals.",
    }
    report["score_inputs_sha256"] = identity({k: report[k] for k in (
        "plan_sha256", "execution_contract_sha256", "review_snapshots", "evidence",
        "execution_coverage", "source_runs")})
    return report


def _evidence_signature(row):
    fields = ("slot_id", "case_id", "evidence_id", "slot_record_sha256", "response_sha256",
              "history_sha256", "material_sha256", "review_sha256", "reviewer_kind", "origin",
              "fixture_only", "comparison_eligible", "strict_pass", "completion",
              "whole_strict", "whole_math", "focus_math", "focus_verdict")
    return identity({k: row.get(k) for k in fields})


def _raw_evidence_signature(row):
    return identity({k: row.get(k) for k in (
        "slot_id", "case_id", "evidence_id", "slot_record_sha256", "response_sha256",
        "history_sha256", "material_sha256", "origin", "fixture_only")})


def score_runs(roots, *, snapshot=None):
    """Collect through the authoritative review reader; never accept loose scores."""
    from .reliability import reliability_score_inputs

    roots = list(roots)
    if not roots:
        raise ValueError("At least one benchmark run is required")
    merged, first, sources, events = {}, None, [], []
    for root in roots:
        inputs = (reliability_score_inputs(root) if snapshot is None
                  else reliability_score_inputs(root, snapshot=snapshot))
        sources.append({"root": str(Path(root).resolve()),
                        "review_snapshot": inputs.get("review_snapshot"),
                        "run_id": inputs.get("run_id"),
                        "run_receipt": str(Path(root).resolve() / "run.json"),
                        "selected_slot_ids": inputs.get("selected_slot_ids", [r["slot_id"] for r in inputs.get("slots", [])]),
                        "candidate_calls": inputs.get("candidate_calls"),
                        "transport_attempts": inputs.get("transport_attempts"),
                        "budget_stop_reason": inputs.get("budget_stop_reason"),
                        "budget_accounting": {k: inputs.get(k) for k in (
                            "budget_scope", "unseen_plan_fragments_accounted_for",
                            "prior_transport_attempts", "prior_known_total_tokens",
                            "cumulative_transport_attempts", "cumulative_known_total_tokens",
                            "cumulative_total_tokens", "cumulative_token_usage_complete")},
                        "formal_eligibility": inputs.get("formal_eligibility")})
        plan = validate_plan(inputs["plan"])
        if first is None:
            first = inputs
        elif (plan["plan_sha256"] != first["plan"]["plan_sha256"]
              or inputs.get("model_label") != first.get("model_label")
              or inputs.get("execution_contract_sha256") != first.get("execution_contract_sha256")):
            raise ValueError("Cannot merge different plan, profile, suite, runtime or model identities")
        for row in inputs.get("slots", []):
            sid = row["slot_id"]
            events.append({"slot_id": sid, "started": row.get("started", False),
                           "status": row.get("execution_status", row.get("status", "unknown")),
                           "reason": row.get("reason"), "evidence_id": row.get("evidence_id"),
                           "slot_record_sha256": row.get("slot_record_sha256"),
                           "reused_from": row.get("reused_from"), "run_id": inputs.get("run_id"),
                           "run_receipt": str(Path(root).resolve() / "run.json"),
                           "slot_record": str(Path(root).resolve() / "slots" / sid.replace(":", "/")) + "/record.json"})
            if sid in merged:
                previous = merged[sid]
                if row.get("started") is False:
                    continue
                if previous.get("started") is False:
                    merged[sid] = row
                    continue
                evidence = row.get("evidence_id", row.get("slot_record_sha256"))
                previous_evidence = previous.get("evidence_id", previous.get("slot_record_sha256"))
                if (not evidence or evidence != previous_evidence
                        or _raw_evidence_signature(row) != _raw_evidence_signature(previous)):
                    raise ValueError("Repeated execution or conflicting review for frozen slot: " + sid)
                reviewed = bool(row.get("review_sha256") or row.get("reviewer_kind"))
                previous_reviewed = bool(previous.get("review_sha256") or previous.get("reviewer_kind"))
                if reviewed and previous_reviewed and _evidence_signature(row) != _evidence_signature(previous):
                    raise ValueError("Conflicting adjudication snapshots for frozen slot: " + sid)
                if reviewed and not previous_reviewed:
                    merged[sid] = row
                continue
            merged[sid] = row
    combined = dict(first, slots=list(merged.values()),
                    source_runs=sources, review_snapshots=[{
                        "root": s["root"], "run_id": s["run_id"], "review_snapshot": s["review_snapshot"]}
                        for s in sources], execution_events=events,
                    budget_sources=[{"root": s["root"], **s["budget_accounting"]} for s in sources])
    return score_inputs(combined)


def render_score(report):
    coverage = report["execution_coverage"]
    eligibility = report.get("formal_eligibility") or {}
    reasons = eligibility.get("reasons", [])
    lines = ["# Math Gauge benchmark score", "", report["notice"], "",
             f"- Evidence: {report['result_kind']}",
             f"- Plan: {report['plan_id']} ({report['plan_sha256']})", "",
             f"Execution coverage: {coverage['unique_started_slots']} unique started slots; "
             f"{coverage['selected_in_supplied_runs']} selected in supplied runs; "
             f"{coverage['full_plan_slots']} in the full plan. "
             f"{len(coverage['selected_unstarted'])} selected slots did not start; "
             f"{len(coverage['not_selected_in_supplied_runs'])} slots were not selected in these runs.", "",
             "Formal comparison eligibility: " + ("eligible" if report["metrics"]["overall"]["formal_comparison_eligible"]
                 else "unavailable") + (" (" + ", ".join(reasons) + ")" if reasons else ""), "",
             "| Component | Exact, provisional | Conservative interval | Formal score | Adjudicated / planned |",
             "|---|---:|---:|---:|---:|"]
    def display(value):
        return "pending" if value is None else f"{value:g}"
    for name in COMPONENTS + ("core", "repeat", "neutral", "stance", "overall", "strict_pass_rate"):
        value = report["metrics"][name]
        coverage = value["coverage"]
        lines.append(f"| {name} | {display(value['exact'])} | {display(value['lower'])}–{display(value['upper'])} | {display(value['formal_exact'])} | {coverage['adjudicated']} / {coverage['planned']} |")
    reasons = report["execution_coverage"]["source_reason_counts"]
    if reasons:
        lines += ["", "Selected slots retained these execution reasons (source references remain in report.json):", ""]
        lines += [f"- {reason}: {count}" for reason, count in sorted(reasons.items())]
    lines += ["", "Focus mathematical transitions (correction and damage show numerator / conditional denominator):", "",
              "| Branch | Round 1 correction / damage | Round 2 correction / damage | Completion loss R1 / R2 |",
              "|---|---|---|---|"]
    def ratio(value):
        return f"{value['numerator']}/{value['denominator']}" if value["denominator"] else "n/a (0 denominator)"
    for arm, trajectory in report["trajectories"]["focus_math"].items():
        a, b = trajectory["round1"], trajectory["round2"]
        lines.append(f"| {arm} | {ratio(a['correction'])}; {ratio(a['damage'])} | "
                     f"{ratio(b['correction'])}; {ratio(b['damage'])} | {a['completion_loss']} / {b['completion_loss']} |")
    return "\n".join(lines) + "\n"
