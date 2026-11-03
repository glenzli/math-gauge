"""Versioned fixed-denominator aggregation of separately validated review evidence."""

from collections import Counter
from fractions import Fraction
from pathlib import Path

from .benchmarks import (ATTEMPTS, COMPONENTS, component_ids, identity, independent_attempts,
                         scoring_policy, validate_plan)
from .execution import now
from .execution_policy import execution_condition

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
    weights = [Fraction(1)] * len(intervals) if weights is None else [Fraction(str(w)) for w in weights]
    if any(weight == 0 for weight in weights):
        included = [(interval, weight) for interval, weight in zip(intervals, weights) if weight]
        return _average([x[0] for x in included], [x[1] for x in included])
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
    if not pairs:
        return {"dimension": "focus_math", "contrast": "stance minus matched neutral",
                "rounds": {}, "causal_effect_claimed": False}
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
    attempts = independent_attempts(plan["profile"]["data"], case_index)
    policy = scoring_policy(plan["profile"]["data"], case_index)
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
        if case_index[cid].get("contract_kind") == "answer_review":
            _boolean(row.get("major_error"))
        rows[sid] = row

    def row_for(sid):
        return rows.get(sid, {"slot_id": sid, "case_id": planned_slots[sid]["case_id"],
                              "started": False, "selected": False})

    def paper_completion(cid):
        paper_rows = [row_for(f"{cid}:{a}") for a in policy["core_attempt_labels"]]
        values = [_interval(row.get("completion")) for row in paper_rows]
        return _average(values), paper_rows

    def repeat_interval(cid):
        values = [_boolean(row_for(f"{cid}:{a}").get("strict_pass"))
                  for a in policy["repeat_attempt_labels"]]
        if any(x[2] == 0 for x in values):
            return _boolean(False)
        if all(x[2] == 1 for x in values):
            return _boolean(True)
        return UNKNOWN

    metrics, metric_intervals = {}, {}
    paper_reports = {}
    all_initial_rows = []
    all_core_rows = []
    for component in plan["profile"]["data"]["components"]:
        intervals, component_rows = [], []
        for cid in component["case_ids"]:
            interval, paper_rows = paper_completion(cid)
            attempt_rows = [row_for(f"{cid}:{a}") for a in attempts[cid]]
            intervals.append(interval)
            component_rows.extend(paper_rows)
            paper_reports[cid] = {
                "component": component["id"], "family_id": case_index[cid]["family_id"],
                "completion": _metric([_interval(r.get("completion")) for r in paper_rows],
                                      paper_rows, case_index, unit="independent attempt"),
                "three_of_three": (_percent(repeat_interval(cid)[2])
                                    if cid in policy["repeat_case_ids"] else None),
                "strict_passes": sum(r.get("strict_pass") is True for r in attempt_rows),
                "executed_attempts": sum(bool(r) and r.get("started") is not False for r in attempt_rows),
                "adjudicated_attempts": sum(r.get("strict_pass") is not None for r in attempt_rows),
                "planned_attempts": len(attempts[cid]),
                ("dimension_weight_total" if case_index[cid].get("contract_kind") == "answer_review"
                 else "stage_weight_total"): case_index[cid]["total_weight"],
            }
            all_initial_rows.extend(attempt_rows)
        if component["id"] == "answer-review":
            families = {}
            for cid, interval in zip(component["case_ids"], intervals):
                family = case_index[cid]["parent_family_id"]
                families.setdefault(family, []).append((cid, interval))
                paper_reports[cid]["parent_family_id"] = family
            intervals = [_average([item[1] for item in items]) for items in families.values()]
            major = [_average([_boolean(row_for(f"{cid}:A1").get("major_error"))
                               for cid, _ in items]) for items in families.values()]
            strict = [_average([_boolean(row_for(f"{cid}:A1").get("strict_pass"))
                                for cid, _ in items]) for items in families.values()]
            metrics["answer_review_major_error_rate"] = _metric(major, component_rows, case_index,
                unit="answer-review parent family")
            metrics["answer_review_strict_pass_rate"] = _metric(strict, component_rows, case_index,
                unit="answer-review parent family")
            answer_review_families = {family: {"case_ids": [cid for cid, _ in items],
                "variant_count": len(items), "completion": {"lower": _percent(value[0]),
                    "upper": _percent(value[1]), "exact": _percent(value[2])}}
                for (family, items), value in zip(families.items(), intervals)}
        metrics[component["id"]] = _metric(intervals, component_rows, case_index,
            unit=("answer-review parent family" if component["id"] == "answer-review" else
                  "full paper A1" if policy["core_attempt_labels"] == ["A1"]
                  else "full paper averaged over A1/A2/A3"))
        metric_intervals[component["id"]] = _average(intervals)
        all_core_rows.extend(component_rows)
    component_weights = [x["weight"] for x in plan["profile"]["data"]["components"]]
    components = component_ids(plan["profile"]["data"])
    metrics["core"] = _metric([metric_intervals[k] for k in components],
                              all_core_rows, case_index, unit="core component",
                              weights=component_weights)
    metric_intervals["core"] = _average([metric_intervals[k] for k in components], component_weights)
    repeats = [repeat_interval(cid) for cid in policy["repeat_case_ids"]]
    repeat_rows = [row_for(f"{cid}:{a}") for cid in policy["repeat_case_ids"]
                   for a in policy["repeat_attempt_labels"]]
    if plan["profile"]["data"]["schema"] == "math-gauge.benchmark-profile/v1":
        repeat_rows = all_initial_rows
    metrics["repeat"] = _metric(repeats,
                                repeat_rows, case_index, unit="full paper, three strict passes")
    metric_intervals["repeat"] = _average(repeats)
    metrics["strict_pass_rate"] = _metric([
        _boolean(row_for(f"{cid}:{a}").get("strict_pass"))
        for cid in case_index for a in attempts[cid]], all_initial_rows, case_index,
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
        "execution_condition": execution_condition(plan["context_policy"]),
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
            | ({k: r.get(k) for k in ("major_error", "answer_review_rescoring")}
               if case_index[r["case_id"]].get("contract_kind") == "answer_review" else {})
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
    if "answer-review" in metrics:
        report["answer_review"] = {"assessment_unit": "review_dimension",
            "aggregation_unit": "parent_family_id", "families": answer_review_families,
            "major_error_rate": metrics["answer_review_major_error_rate"],
            "strict_pass_rate": metrics["answer_review_strict_pass_rate"],
            "raw_counts": {"papers": sum(c.get("contract_kind") == "answer_review" for c in case_index.values()),
                "major_error_adjudicated": sum(type(r.get("major_error")) is bool for r in evidence_rows
                    if case_index[r["case_id"]].get("contract_kind") == "answer_review"),
                "major_errors": sum(r.get("major_error") is True for r in evidence_rows
                    if case_index[r["case_id"]].get("contract_kind") == "answer_review")}}
    report["score_inputs_sha256"] = identity({k: report[k] for k in (
        "plan_sha256", "execution_contract_sha256", "execution_eligibility", "review_snapshots", "execution_audit_snapshots", "evidence",
        "execution_coverage", "source_runs")})
    return report


def _evidence_signature(row):
    fields = ("slot_id", "case_id", "evidence_id", "slot_record_sha256", "response_sha256",
              "history_sha256", "material_sha256", "review_sha256", "reviewer_kind", "origin",
              "fixture_only", "strict_pass", "completion",
              "whole_strict", "whole_math", "focus_math", "focus_verdict")
    value = {k: row.get(k) for k in fields}
    if "major_error" in row:
        value.update(major_error=row["major_error"], answer_review_rescoring=row.get("answer_review_rescoring"))
    return identity(value)


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


def _execution_semantics(plan, cid):
    runtime = plan.get("runtime") or {}
    budget = runtime.get("budget", {})
    parameters = dict(runtime.get("candidate_parameters", {}))
    if "output_tokens" in budget:
        parameters["max_output_tokens"] = budget["output_tokens"]
    parameters.update(budget.get("case_parameters", {}).get(cid, {}))
    return {"context_policy": plan["context_policy"], "system_prompt": runtime.get("system_prompt"),
            "parameters": parameters, "timeout_seconds": budget.get("timeout_seconds", 120)}


def _compose_score_sources(plan, sources, *, model_aliases=None, budget_policy="require_matching",
                           answer_reviews=()):
    """Re-evaluate unchanged source answers; never fabricate a new execution run."""
    plan = validate_plan(plan)
    if budget_policy not in {"require_matching", "retain_source_budgets"}:
        raise ValueError("Unknown composition budget policy")
    target_cases = {case["case_id"]: case for case in plan["case_index"]}
    target_slots = {slot["slot_id"]: slot for slot in plan["slots"]}
    target_prompts = {row["message_id"]: row["content_sha256"]
                      for row in plan["reliability"]["prompts"]["messages"]}
    target_focus = {row["case_id"]: row for row in plan["reliability"]["selection"]["cases"]}
    compared_fields = ("version", "track", "task_kind", "contract_kind", "request_sha256",
                       "candidate_message_sha256", "group_contract_sha256", "stages", "total_weight")
    model_aliases = model_aliases or {}
    if (not isinstance(model_aliases, dict) or not all(isinstance(k, str) and isinstance(v, str)
                                                      for k, v in model_aliases.items())):
        raise ValueError("Model label aliases must be an explicit evaluator declaration")
    rows, receipts, labels = {}, [], set()
    for source in sources:
        original = validate_plan(source["plan"])
        if source.get("model_label") != original.get("model_label"):
            raise ValueError("Source model label differs from its frozen plan")
        labels.add(source.get("model_label"))
        source_cases = {case["case_id"]: case for case in original["case_index"]}
        source_slots = {slot["slot_id"]: slot for slot in original["slots"]}
        source_prompts = {row["message_id"]: row["content_sha256"]
                          for row in original["reliability"]["prompts"]["messages"]}
        source_focus = {row["case_id"]: row for row in original["reliability"]["selection"]["cases"]}
        selected = []
        for row in source.get("slots", []):
            sid, cid = row["slot_id"], row["case_id"]
            if sid not in target_slots:
                continue
            before, after = source_cases[cid], target_cases[cid]
            if any(before.get(k) != after.get(k) for k in compared_fields):
                raise ValueError("Composition changed source candidate input or review contract: " + sid)
            old_slot, new_slot = source_slots[sid], target_slots[sid]
            keys = ("case_id", "kind", "context", "parent_slot", "message_id", "attempt_label", "arm", "round")
            if any(old_slot.get(k) != new_slot.get(k) for k in keys):
                raise ValueError("Composition changed source branch or attempt identity: " + sid)
            if (new_slot["kind"] == "followup"
                    and source_prompts.get(old_slot["message_id"]) != target_prompts.get(new_slot["message_id"])):
                raise ValueError("Composition changed the original followup prompt: " + sid)
            if new_slot["kind"] == "followup" and any(
                source_focus.get(cid, {}).get(key) != target_focus.get(cid, {}).get(key)
                for key in ("stage_id", "expected_truth", "scope", "target_claim")):
                raise ValueError("Composition changed the independently reviewed followup target: " + sid)
            old_conditions, new_conditions = _execution_semantics(original, cid), _execution_semantics(plan, cid)
            if any(old_conditions[k] != new_conditions[k] for k in ("context_policy", "system_prompt", "parameters")):
                raise ValueError("Composition changed the execution condition, system prompt or model generation parameters: " + sid)
            if old_conditions["timeout_seconds"] != new_conditions["timeout_seconds"] and budget_policy == "require_matching":
                raise ValueError("Composition changed the source time budget; explicitly retain its budget stratum: " + sid)
            if sid in rows and _evidence_signature(rows[sid]) != _evidence_signature(row):
                raise ValueError("Conflicting source evidence for composed slot: " + sid)
            rows[sid] = dict(row)
            selected.append(sid)
        receipts.append({"run_id": source.get("run_id"), "root": source.get("root"),
                         "plan_sha256": original["plan_sha256"],
                         "suite": original["suite"], "runtime_sha256": original["runtime_sha256"],
                         "model_label": source.get("model_label"),
                         "budget": (original.get("runtime") or {}).get("budget", {}),
                         "review_snapshot": source.get("review_snapshot"),
                         "audit_snapshot": source.get("audit_snapshot"),
                         "frozen_report_reuse": source.get("frozen_report_reuse"),
                         "selected_slot_ids": selected})
    for extra in answer_reviews:
        receipt = extra["receipt"]
        labels.add(receipt["model_label"])
        for row in extra["rows"]:
            sid = row["slot_id"]
            if sid not in target_slots or target_cases[row["case_id"]].get("contract_kind") != "answer_review":
                raise ValueError("Rescoring references an unknown answer-review slot")
            if sid in rows:
                raise ValueError("Repeated answer-review evidence source")
            rows[sid] = dict(row)
        receipts.append(receipt)
    normalized = {model_aliases.get(label, label) for label in labels}
    if (not set(model_aliases) <= labels or len(normalized) > 1
            or normalized and plan["model_label"] not in {None, next(iter(normalized))}):
        raise ValueError("Composition cannot silently combine different model labels")
    for row in rows.values():
        original = dict(row.get("execution_eligibility") or {})
        row["execution_eligibility"] = dict(original, eligible=False,
            reasons=sorted(set(original.get("reasons", [])) | {"posthoc_cross_plan_composition"}))
        row["comparison_eligible"] = False
    report = score_inputs({"plan": plan, "model_label": plan["model_label"],
                           "slots": list(rows.values()), "source_runs": receipts})
    report["result_kind"] = "posthoc_composition"
    report["composition"] = {"schema": "math-gauge.score-composition/v1",
                             "new_candidate_calls": 0, "independent_run": False,
                             "source_runs": receipts, "source_model_labels": list(labels),
                             "declared_model_label_aliases": model_aliases,
                             "budget_policy": budget_policy,
                             "budget_conditions_shared": len({identity(r["budget"]) for r in receipts}) <= 1,
                             "runtime_identity_shared": len({r["runtime_sha256"] for r in receipts}) <= 1,
                             "notice": "Original responses and reviews are reused under a new evaluator plan. This is not a new independent benchmark execution or a formal comparison score."}
    return report


def frozen_report_inputs(root, reference):
    """Retain a trusted old score/engine identity without current Lean revalidation.

    This deliberately narrower path is only for posthoc composition. The caller
    supplies trusted report and review-snapshot hashes; the run, response,
    history, material and saved review bindings are checked again. It does not
    claim that the current mathematical or Lean verifier reproduced that review.
    """
    from .catalog import digest_bytes, read_json, safe_file
    from .reliability import inspect_reliability_run

    if (not isinstance(reference, dict) or set(reference) != {"path", "sha256", "review_snapshot_sha256"}
            or not all(isinstance(reference[key], str) and len(reference[key]) == 64
                       and all(c in "0123456789abcdef" for c in reference[key])
                       for key in ("sha256", "review_snapshot_sha256"))):
        raise ValueError("Frozen score reuse needs a trusted report and review-snapshot SHA-256")
    root = Path(root).resolve()
    raw = Path(reference["path"]).read_bytes()
    if digest_bytes(raw) != reference["sha256"]:
        raise ValueError("Frozen score report changed")
    report = read_json(reference["path"])
    meta, records = inspect_reliability_run(root)
    plan = meta["plan"]
    if (report.get("schema") != "math-gauge.benchmark-score/v1"
            or any(report.get(key) != plan.get(key) for key in (
                "plan_sha256", "plan_id", "suite", "runtime_sha256", "model_label"))):
        raise ValueError("Frozen score report binds a different original plan or runtime")
    index = read_json(safe_file(root, "reliability-reviews.json"))
    descriptors = [row for row in index.get("snapshots", [])
                   if row.get("snapshot_sha256") == reference["review_snapshot_sha256"]]
    if len(descriptors) != 1:
        raise ValueError("Frozen score review snapshot is not retained in its original run")
    descriptor = descriptors[0]
    path = safe_file(root, descriptor["path"])
    snapshot = read_json(path)
    if (digest_bytes(path.read_bytes()) != descriptor["file_sha256"]
            or snapshot.get("snapshot_sha256") != reference["review_snapshot_sha256"]
            or snapshot["snapshot_sha256"] != identity({k: v for k, v in snapshot.items() if k != "snapshot_sha256"})
            or snapshot.get("plan_sha256") != plan["plan_sha256"] or snapshot.get("run_id") != meta["run_id"]):
        raise ValueError("Frozen score review snapshot changed")
    rows, seen = [], set()
    for row in report.get("evidence", []):
        sid = row.get("slot_id")
        if sid not in records or sid in seen:
            raise ValueError("Frozen score contains unknown or repeated evidence")
        record = records[sid]
        review = snapshot["reviews"].get(sid)
        if (not isinstance(review, dict) or row.get("slot_record_sha256") != meta["slot_record_sha256"][sid]
                or any(row.get(key) != record.get(key) for key in (
                    "case_id", "evidence_id", "response_sha256", "history_sha256", "material_sha256"))
                or row.get("review_sha256") != review.get("review_sha256")
                or review["review_sha256"] != identity({k: v for k, v in review.items() if k != "review_sha256"})
                or row.get("binding") != review.get("binding")):
            raise ValueError("Frozen score answer/history/review binding changed: " + sid)
        seen.add(sid)
        rows.append(dict(row, started=record["started"], selected=True))
    return {"plan": plan, "model_label": plan["model_label"], "root": str(root),
            "run_id": meta["run_id"], "slots": rows, "review_snapshot": descriptor,
            "frozen_report_reuse": {"report_sha256": reference["sha256"],
                "review_snapshot_sha256": reference["review_snapshot_sha256"],
                "current_engine_reverification_claimed": False, "execution_audit_reverified": False,
                "lean_recompiled": False}}


def score_composed_runs(plan, roots, *, snapshots=None, model_aliases=None,
                        budget_policy="require_matching", frozen_reports=None,
                        answer_review_sources=(), suite=None):
    """Read authoritative retained reviews before a cross-plan development analysis."""
    from .reliability import reliability_score_inputs

    roots = [Path(root).resolve() for root in roots]
    if (not roots and not answer_review_sources) or len(roots) != len(set(roots)):
        raise ValueError("Composition requires distinct existing source runs")
    snapshots = snapshots or {}
    frozen_reports = frozen_reports or {}
    if not set(snapshots) <= {str(root) for root in roots}:
        raise ValueError("Composition snapshot selection names an unknown source run")
    if not set(frozen_reports) <= {str(root) for root in roots}:
        raise ValueError("Frozen score reference names an unknown source run")
    sources = []
    for root in roots:
        selectors = snapshots.get(str(root), {})
        if not isinstance(selectors, dict) or set(selectors) - {"snapshot", "audit_snapshot"}:
            raise ValueError("Invalid source review/audit snapshot selector")
        if str(root) in frozen_reports:
            if selectors:
                raise ValueError("Frozen score reuse already binds its original review/audit selection")
            sources.append(frozen_report_inputs(root, frozen_reports[str(root)]))
        else:
            sources.append(reliability_score_inputs(root, **selectors))
    from .review import rescored_answer_inputs
    if answer_review_sources and suite is None:
        raise ValueError("Answer-review rescoring requires the trusted target suite")
    rescored = [rescored_answer_inputs(plan, suite, source) for source in answer_review_sources]
    return _compose_score_sources(plan, sources, model_aliases=model_aliases,
                                  budget_policy=budget_policy, answer_reviews=rescored)


def public_score_projection(report, plan, *, private_aliases, metadata=None, source_kinds=None,
                            public_subset=None, public_subset_sha256=None):
    """Explicit score-only publication boundary; never serialize evaluator case data."""
    import re

    plan = validate_plan(plan)
    if report.get("plan_sha256") != plan["plan_sha256"]:
        raise ValueError("Public score projection binds a different plan")
    cases = {case["case_id"]: case for case in plan["case_index"]}
    if (not isinstance(private_aliases, dict) or not set(private_aliases) <= set(cases)
            or len(set(private_aliases.values())) != len(private_aliases)
            or any(not re.fullmatch(r"Private-[0-9]{2,}", value) for value in private_aliases.values())
            or any(case.get("source_visibility") == "private" and cid not in private_aliases
                   for cid, case in cases.items())):
        raise ValueError("Every private paper needs one unique neutral public alias")
    evidence = {row["slot_id"]: row for row in report.get("evidence", [])}
    source_kinds = source_kinds or {}
    allowed_sources = {"historical_public", "existing_private", "new_private", "answer_review_rescored"}
    if not set(source_kinds) <= set(cases) or not set(source_kinds.values()) <= allowed_sources:
        raise ValueError("Invalid public source classification")
    metric_keys = ("exact", "lower", "upper", "complete", "coverage", "formal_comparison_eligible")
    titles = {"proofs": "Written mathematics", "lean-audit": "Lean semantic audit",
              "lean-construction": "Lean construction", "chapters": "Chapter formalization",
              "exploration": "Research exploration", "answer-review": "Mathematical answer review"}
    metrics = {name: {key: value[key] for key in metric_keys if key in value}
               for name, value in report["metrics"].items() if name in titles or name in {
                   "core", "repeat", "neutral", "stance", "overall", "strict_pass_rate",
                   "answer_review_major_error_rate", "answer_review_strict_pass_rate"}}
    slots, private_records = [], []
    for slot in plan["slots"]:
        cid, sid = slot["case_id"], slot["slot_id"]
        row = evidence.get(sid, {})
        public_id = private_aliases.get(cid, cid)
        completion = row.get("completion") or {"lower": 0, "upper": 1, "exact": None}
        reviewed = bool(row.get("review_sha256"))
        reasons = {reason for key in ("whole_math", "whole_strict", "focus_math")
                   for reason in (row.get(key) or {}).get("reasons", [])}
        if reasons & {"execution_error", "execution_failure", "infrastructure_error"}:
            status = "execution_failed"
        elif reviewed and completion.get("exact") is None or reasons & {"material_unresolved", "problem_defect_pending"}:
            status = "unresolved"
        else:
            status = "reviewed" if reviewed and completion.get("exact") is not None else (
                "review_pending" if row.get("response_sha256") else "pending")
        item = {"slot_id": public_id + sid[len(cid):], "public_id": public_id,
                "source_kind": source_kinds.get(cid, "new_private" if cid in private_aliases else "historical_public"),
                "completion": {k: completion[k] for k in ("exact", "lower", "upper")},
                "strict_pass": row.get("strict_pass"), "status": status,
                "response_sha256": row.get("response_sha256"), "review_sha256": row.get("review_sha256"),
                "human_status": "reviewed" if row.get("reviewer_kind") == "human" else "pending"}
        if cases[cid].get("contract_kind") == "answer_review":
            item["major_error"] = row.get("major_error")
            if cid not in private_aliases:
                item["parent_family_id"] = cases[cid]["parent_family_id"]
            item["dimensions"] = [{k: value[k] for k in ("dimension_id", "score")}
                                  for value in (row.get("group_diagnostic") or {}).get("dimensions", [])]
        slots.append(item)
        if cid in private_aliases and slot.get("attempt_label") == "A1":
            private_records.append(dict(item))
    initial = [row for row in slots if row["slot_id"].endswith(":A1")]
    result = {"schema": "math-gauge.public-composite-score/v1", "id": "combined-development-analysis",
              "title": "Combined development analysis", "status": report.get("result_kind", "provisional"),
              "score_units": {"metrics": "percent", "completion": "fraction"},
              "plan_sha256": plan["plan_sha256"],
              "profile": {"components": [{"id": row["id"], "title": titles[row["id"]],
                  "weight": row["weight"], "case_count": len(row["case_ids"])}
                  for row in plan["profile"]["data"]["components"]],
                  "overall_weights": plan["profile"]["data"]["overall_weights"],
                  "classification": "development_analysis", "selection_timing": "after_source_runs"},
              "metrics": metrics, "private_records": private_records, "slot_evidence": slots,
              "coverage": {"papers_planned": len(cases), "a1_planned": len(initial),
                  "a1_reviewed": sum(row["completion"]["exact"] is not None for row in initial),
                  "slots_planned": len(slots), "slots_reviewed": sum(row["review_sha256"] is not None for row in slots)},
              "strict_passes": {"core_A1": {"passed": sum(row["strict_pass"] is True for row in initial),
                  "total": len(initial), "adjudicated": sum(row["strict_pass"] is not None for row in initial)}},
              "evidence_status": {"human_approval": "pending", "formal_comparison_eligible": False,
                  "backend_identity_independently_verified": False,
                  "composition_new_candidate_calls": 0 if report.get("composition") else None,
                  "new_private_a1_planned": sum(row["source_kind"] == "new_private" for row in initial),
                  "new_private_answers_present": sum(row["source_kind"] == "new_private" and
                                                       row["response_sha256"] is not None for row in initial)}}
    if public_subset is not None:
        if public_subset.get("schema") != "math-gauge.posthoc-summary/v1":
            raise ValueError("Unsupported frozen public subset summary")
        source = public_subset.get("source", {})
        subset_metrics = {}
        for name, row in public_subset.get("metrics", {}).items():
            if name in titles or name in {"core", "repeat", "neutral", "stance", "overall"}:
                value = row.get("value")
                if type(value) not in (int, float) or not 0 <= value <= 100:
                    raise ValueError("Invalid frozen public subset percentage")
                subset_metrics[name] = {"exact": value, "lower": value, "upper": value}
        result["public_subset"] = {"metrics": subset_metrics,
            "strict_passes": {name: {k: row[k] for k in ("passed", "total")}
                              for name, row in public_subset.get("strict_passes", {}).items()
                              if name in {"core_A1", "independent_attempts", "all_selected_slots"}},
            "source": {k: source[k] for k in ("run_id", "plan_sha256", "report_sha256", "review_snapshot_sha256") if k in source}}
        if public_subset_sha256 is not None:
            if not isinstance(public_subset_sha256, str) or not re.fullmatch(r"[a-f0-9]{64}", public_subset_sha256):
                raise ValueError("Invalid frozen public subset file hash")
            result["public_subset"]["summary_sha256"] = public_subset_sha256
    if metadata:
        allowed = {"id", "title", "date", "requested_model", "requested_reasoning_effort"}
        if not set(metadata) <= allowed:
            raise ValueError("Unexpected public score metadata")
        result.update(metadata)
    if report.get("composition"):
        composition = report["composition"]
        result["composition"] = {"independent_run": False, "new_candidate_calls": 0,
            "budget_policy": composition["budget_policy"],
            "budget_conditions_shared": composition["budget_conditions_shared"],
            "source_timeout_seconds": sorted({source["budget"].get("timeout_seconds", 120)
                                               for source in composition["source_runs"]}),
            "same_context_and_generation_conditions_checked": True,
            "frozen_source_reports": [source["frozen_report_reuse"] for source in composition["source_runs"]
                                      if source.get("frozen_report_reuse") is not None]}
    return result


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
    if report.get("execution_condition"):
        condition = report["execution_condition"]
        lines[4:4] = [f"Execution condition: {condition['label']} ({condition['track']}).", ""]
    def display(value):
        return "pending" if value is None else f"{value:g}"
    components = tuple(name for name in report["metrics"] if name in COMPONENTS + ("exploration",))
    for name in components + ("core", "repeat", "neutral", "stance", "overall", "strict_pass_rate"):
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
