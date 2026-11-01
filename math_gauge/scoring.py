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


def _eligibility_reasons(row, case, *, current=True):
    """Explain execution and content gates without turning labels into proof."""
    if not row or row.get("selected") is False:
        return ["slot_not_run", "execution_evidence_missing", "answer_review_missing"] + (
            ["case_human_approval_missing"] if not case["case_approved"] else [])
    reasons = []
    if row.get("started") is False:
        reasons.append("slot_not_started")
    execution = row.get("execution_eligibility") or {}
    if not row.get("execution_receipt_sha256"):
        reasons.append("execution_evidence_missing")
    elif not row.get("execution_audit_sha256"):
        reasons.append("execution_audit_missing")
    if execution.get("eligible") is not True or row.get("comparison_eligible") is not True:
        reasons.extend(execution.get("reasons") or ["execution_eligibility_unverified"])
    if row.get("origin") != "command" or row.get("fixture_only") is True:
        reasons.append("fixture_or_replay_execution" if row.get("origin") in {"fixture", "replay"}
                       or row.get("fixture_only") is True else "external_origin_unverified"
                       if row.get("origin") == "external_import" else "execution_origin_unverified")
    if not case["case_approved"]:
        reasons.append("case_human_approval_missing")
    elif row.get("case_approval_evidence_verified") is not True:
        reasons.append("case_approval_evidence_missing")
    if not row.get("reviewer_kind"):
        reasons.append("answer_review_missing")
    elif row.get("reviewer_kind") != "human":
        reasons.append("answer_human_review_missing")
    if row.get("problem_defect"):
        reasons.append("problem_defect_pending")
    if current and row.get("historical_audit_selection") is True:
        reasons.append("execution_audit_superseded")
    return sorted(set(reasons))


def _eligible(row, case, *, current=True):
    return not _eligibility_reasons(row, case, current=current)


def _metric(intervals, rows, cases, *, unit, weights=None):
    interval = _average(intervals, weights)
    exact = _percent(interval[2])
    historical = any(row.get("historical_audit_selection") is True for row in rows)
    selected_formal = (exact is not None and bool(rows) and all(
        bool(row) and _eligible(row, cases[row["case_id"]], current=False) for row in rows))
    formal = selected_formal and not historical
    failures = [{"slot_id": row.get("slot_id"),
                 "reasons": _eligibility_reasons(row, cases[row["case_id"]]) if row else
                            ["slot_not_run", "execution_evidence_missing", "answer_review_missing"]}
                for row in rows]
    failures = [item for item in failures if item["reasons"]]
    reasons = {reason for item in failures for reason in item["reasons"]}
    if exact is None:
        reasons.add("score_coverage_incomplete")
        for row in rows:
            for dimension in ("whole_strict", "whole_math", "focus_math"):
                axis = row.get(dimension, {})
                reasons.update(set(axis.get("reasons", [])) & PENDING_REASONS)
    return {
        "exact": exact, "provisional_exact": exact,
        "formal_exact": exact if formal else None,
        "formal_score": exact if formal else None,
        "historical_formal_score": exact if historical and selected_formal else None,
        "lower": _bound(interval[0], lower=True), "upper": _bound(interval[1], lower=False),
        "complete": interval[2] is not None, "formal_comparison_eligible": formal,
        "formal_eligibility": {"eligible": formal, "reasons": sorted(reasons),
                               "selected_audit_eligible": selected_formal,
                               "historical": historical,
                               "reason_counts": dict(Counter(reason for item in failures
                                                              for reason in item["reasons"])),
                               "slot_failures": failures},
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
    audit_selections = inputs.get("execution_audit_snapshots", [{"audit_snapshot": inputs.get("audit_snapshot")}])
    historical = any((item.get("audit_snapshot") or {}).get("historical") is True
                     for item in audit_selections)
    rows = {}
    for row in inputs.get("slots", []):
        if historical:
            row = dict(row, historical_audit_selection=True)
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
        return rows.get(sid, {"slot_id": sid, "case_id": planned_slots[sid]["case_id"],
                              "started": False, "selected": False})

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
    formal_eligibility = dict(metrics["overall"]["formal_eligibility"], slot_failures=[
        {"slot_id": sid, "reasons": reasons}
        for sid, slot in planned_slots.items()
        if (reasons := _eligibility_reasons(rows.get(sid), case_index[slot["case_id"]]))])
    report = {
        "schema": "math-gauge.benchmark-score/v1", "created_at": now(),
        "plan_id": plan["plan_id"], "plan_sha256": plan["plan_sha256"],
        "profile": {k: plan["profile"][k] for k in ("id", "version", "sha256")},
        "suite": plan["suite"], "runtime_sha256": plan["runtime_sha256"],
        "model_label": plan["model_label"], "planned": plan["planned"],
        "result_kind": ("not_run" if not evidence_rows else "fixture" if fixture else "historical" if historical else
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
            "case_approval_evidence_verified", "case_approval_source",
            "origin", "source_origin", "fixture_only", "comparison_eligible", "execution_eligibility",
            "execution_receipt_sha256", "execution_audit_sha256", "historical_audit_selection", "strict_pass", "completion",
            "whole_strict", "whole_math", "focus_math", "focus_verdict", "problem_defect", "group_diagnostic")}
            for r in evidence_rows],
        "execution_contract_sha256": inputs.get("execution_contract_sha256"),
        "execution_eligibility": inputs.get("execution_eligibility"),
        "budget_accounting": {"sources": inputs.get("budget_sources", []),
                              "unseen_plan_fragments_accounted_for": False,
                              "scope": "Supplied runs and explicitly reused original evidence only"},
        "review_snapshots": inputs.get("review_snapshots", [inputs["review_snapshot"]]
                                      if inputs.get("review_snapshot") is not None else []),
        "execution_audit_snapshots": inputs.get("execution_audit_snapshots", [{
            "root": inputs.get("root"), "run_id": inputs.get("run_id"), "audit_snapshot": inputs["audit_snapshot"]}]
                                               if inputs.get("audit_snapshot") is not None else []),
        "historical_audit_selection": historical,
        "formal_eligibility": formal_eligibility,
        "source_runs": inputs.get("source_runs", []),
        "notice": "All scores use the frozen full-plan denominators. Exact values are provisional unless formal eligibility is explicit. Fixture/replay, AI review and draft papers do not produce formal model scores. Focus slices overlap and never enter totals.",
    }
    report["score_inputs_sha256"] = identity({k: report[k] for k in (
        "plan_sha256", "execution_contract_sha256", "execution_eligibility", "review_snapshots", "execution_audit_snapshots", "evidence",
        "execution_coverage", "source_runs")})
    return report


def _evidence_signature(row):
    fields = ("slot_id", "case_id", "evidence_id", "slot_record_sha256", "response_sha256",
              "history_sha256", "material_sha256", "review_sha256", "reviewer_kind", "origin",
              "fixture_only", "strict_pass", "completion",
              "whole_strict", "whole_math", "focus_math", "focus_verdict")
    return identity({k: row.get(k) for k in fields})


def _raw_evidence_signature(row):
    return identity({k: row.get(k) for k in (
        "slot_id", "case_id", "evidence_id", "slot_record_sha256", "response_sha256",
        "history_sha256", "material_sha256", "origin", "fixture_only")})


def _audit_signature(row):
    """Run-local snapshot paths do not change an original execution audit."""
    if not row.get("execution_receipt_sha256"):
        return None
    return identity({"receipt_sha256": row["execution_receipt_sha256"],
                     "audit_sha256": row.get("execution_audit_sha256"),
                     "qualification": {key: value for key, value in
                         (row.get("execution_eligibility") or {}).items()
                         if key not in {"receipt_path", "audit_snapshot", "eligible", "reasons"}}})


def _compose_execution_qualification(plan, rows):
    """Recompute only ancestry after union; preserve verified self judgments."""
    for slot in plan["slots"]:
        sid = slot["slot_id"]
        if sid not in rows or not rows[sid].get("execution_receipt_sha256"):
            continue
        row = rows[sid]
        execution = row.get("execution_eligibility") or {}
        own = execution.get("integrity_eligible")
        reasons = execution.get("integrity_reasons")
        if type(own) is not bool or not isinstance(reasons, list) or own != (not reasons):
            raise ValueError("Execution audit lacks its verified independent self qualification: " + sid)
        reasons = list(reasons)
        parent = slot.get("parent_slot")
        ancestor_audits = []
        if parent is not None:
            previous = rows.get(parent, {})
            previous_execution = previous.get("execution_eligibility") or {}
            ancestor_audits = list(previous_execution.get("ancestor_audits", [])) + [{
                "slot_id": parent, "evidence_id": previous.get("evidence_id"),
                "receipt_sha256": previous.get("execution_receipt_sha256"),
                "audit_sha256": previous.get("execution_audit_sha256"),
                "eligible": previous_execution.get("eligible") is True}]
            if (not previous.get("execution_receipt_sha256")
                    or previous_execution.get("eligible") is not True):
                reasons.append("ancestor_execution_ineligible")
        qualified = dict(execution, eligible=own and not reasons, reasons=sorted(set(reasons)),
                         ancestor_audits=ancestor_audits)
        rows[sid] = dict(row, execution_eligibility=qualified, comparison_eligible=qualified["eligible"])


def score_runs(roots, *, snapshot=None, audit_snapshot=None, audit_snapshots=None):
    """Collect through the authoritative review reader; never accept loose scores."""
    from .reliability import reliability_score_inputs

    roots = list(roots)
    if not roots:
        raise ValueError("At least one benchmark run is required")
    if audit_snapshot is not None and audit_snapshots is not None:
        raise ValueError("Choose one audit snapshot or an exact per-run audit snapshot map")
    if audit_snapshot is not None and len(roots) != 1:
        raise ValueError("A single audit snapshot selector requires exactly one run; use a per-run map")
    if audit_snapshots is not None:
        canonical = [str(Path(root).resolve()) for root in roots]
        if (not isinstance(audit_snapshots, dict) or len(set(canonical)) != len(canonical)
                or set(audit_snapshots) != set(canonical)
                or any(not isinstance(key, str) or not Path(key).is_absolute()
                       or str(Path(key).resolve()) != key for key in audit_snapshots)
                or any(not isinstance(value, str) or len(value) != 64
                       or any(c not in "0123456789abcdef" for c in value)
                       for value in audit_snapshots.values())):
            raise ValueError("Audit snapshot map must exactly match every unique resolved run root and SHA-256")
    merged, first, sources, events = {}, None, [], []
    observed = {"observed_sessions": {}, "observed_states": {}, "observed_request_ids": {}}
    for root in roots:
        selectors = {}
        if snapshot is not None:
            selectors["snapshot"] = snapshot
        selected_audit = (audit_snapshots[str(Path(root).resolve())]
                          if audit_snapshots is not None else audit_snapshot)
        if selected_audit is not None:
            selectors["audit_snapshot"] = selected_audit
        inputs = reliability_score_inputs(root, **selectors)
        sources.append({"root": str(Path(root).resolve()),
                        "review_snapshot": inputs.get("review_snapshot"),
                        "audit_snapshot": inputs.get("audit_snapshot"),
                        "run_id": inputs.get("run_id"),
                        "run_receipt": str(Path(root).resolve() / "run.json"),
                        "selected_slot_ids": inputs.get("selected_slot_ids", [r["slot_id"] for r in inputs.get("slots", [])]),
                        "candidate_calls": inputs.get("candidate_calls"),
                        "external_candidate_calls_declared": inputs.get("external_candidate_calls_declared"),
                        "source_origin": inputs.get("source_origin"),
                        "fixture_only": inputs.get("fixture_only"),
                        "import_limits": inputs.get("import_limits"),
                        "transport_attempts": inputs.get("transport_attempts"),
                        "budget_stop_reason": inputs.get("budget_stop_reason"),
                        "budget_accounting": {k: inputs.get(k) for k in (
                            "budget_scope", "unseen_plan_fragments_accounted_for",
                            "prior_transport_attempts", "prior_known_total_tokens",
                            "cumulative_transport_attempts", "cumulative_known_total_tokens",
                            "cumulative_total_tokens", "cumulative_token_usage_complete")},
                        "execution_eligibility": inputs.get("execution_eligibility")})
        plan = validate_plan(inputs["plan"])
        if first is None:
            first = inputs
        elif (plan["plan_sha256"] != first["plan"]["plan_sha256"]
              or inputs.get("model_label") != first.get("model_label")
              or inputs.get("execution_contract_sha256") != first.get("execution_contract_sha256")):
            raise ValueError("Cannot merge different plan, profile, suite, runtime or model identities")
        for row in inputs.get("slots", []):
            sid = row["slot_id"]
            execution = row.get("execution_eligibility") or {}
            for key, index in observed.items():
                for value in execution.get(key, []):
                    eid = row.get("evidence_id")
                    if value in index and index[value] != eid:
                        raise ValueError("Merged independent executions reused candidate " + key + ": " + sid)
                    index[value] = eid
            events.append({"slot_id": sid, "started": row.get("started", False),
                           "status": row.get("execution_status", row.get("status", "unknown")),
                           "reason": row.get("reason"), "evidence_id": row.get("evidence_id"),
                           "slot_record_sha256": row.get("slot_record_sha256"),
                           "execution_eligibility": row.get("execution_eligibility"),
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
                audit = _audit_signature(row)
                previous_audit = _audit_signature(previous)
                if audit is not None and previous_audit is not None and audit != previous_audit:
                    raise ValueError("Conflicting execution audit snapshots for frozen slot: " + sid)
                reviewed = bool(row.get("review_sha256") or row.get("reviewer_kind"))
                previous_reviewed = bool(previous.get("review_sha256") or previous.get("reviewer_kind"))
                if reviewed and previous_reviewed and _evidence_signature(row) != _evidence_signature(previous):
                    raise ValueError("Conflicting adjudication snapshots for frozen slot: " + sid)
                selected = dict(row if reviewed and not previous_reviewed else previous)
                audit_source = row if audit is not None else previous
                for key in ("execution_eligibility", "execution_receipt_sha256",
                            "execution_audit_sha256", "comparison_eligible"):
                    if key in audit_source:
                        selected[key] = audit_source[key]
                merged[sid] = selected
                continue
            merged[sid] = row
    _compose_execution_qualification(first["plan"], merged)
    execution_eligibility = {
        "schema": "math-gauge.execution-eligibility-composition/v1",
        "eligible": bool(merged) and all((row.get("execution_eligibility") or {}).get("eligible") is True
                                         for row in merged.values()),
        "reasons": sorted({reason for row in merged.values()
                           for reason in (row.get("execution_eligibility") or {}).get("reasons", [])}),
        "verifier_sha256s": sorted({summary["verifier_sha256"] for source in sources
                                   if (summary := source.get("execution_eligibility"))
                                   and summary.get("verifier_sha256")}),
        "sources": [{"root": source["root"], "run_id": source["run_id"],
                     "verification": source["execution_eligibility"]} for source in sources],
    }
    combined = dict(first, slots=list(merged.values()),
                    execution_eligibility=execution_eligibility,
                    source_runs=sources, review_snapshots=[{
                        "root": s["root"], "run_id": s["run_id"], "review_snapshot": s["review_snapshot"]}
                        for s in sources], execution_events=events,
                    execution_audit_snapshots=[{
                        "root": s["root"], "run_id": s["run_id"], "audit_snapshot": s["audit_snapshot"]}
                        for s in sources],
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
             "| Component | Exact, provisional | Conservative interval | Formal score | Historical formal score | Adjudicated / planned | Formal gate failures |",
             "|---|---:|---:|---:|---:|---:|---|"]
    if report.get("historical_audit_selection"):
        lines[4:4] = ["Historical execution-audit selection: retained judgments are reproduced; current formal comparison is unavailable. Selected and latest audit hashes remain in report.json.", ""]
    def display(value):
        return "pending" if value is None else f"{value:g}"
    for name in COMPONENTS + ("core", "repeat", "neutral", "stance", "overall", "strict_pass_rate"):
        value = report["metrics"][name]
        coverage = value["coverage"]
        blockers = ", ".join(value.get("formal_eligibility", {}).get("reasons", [])) or (
            "none" if value["formal_comparison_eligible"] else "not recorded")
        lines.append(f"| {name} | {display(value['exact'])} | {display(value['lower'])}–{display(value['upper'])} | {display(value['formal_exact'])} | {display(value.get('historical_formal_score'))} | {coverage['adjudicated']} / {coverage['planned']} | {blockers} |")
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
