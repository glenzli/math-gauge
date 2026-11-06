"""Versioned fixed-denominator aggregation of separately validated review evidence."""

from collections import Counter
from fractions import Fraction
from pathlib import Path

from .benchmarks import (ATTEMPTS, COMPONENTS, component_ids, identity, independent_attempts,
                         reliability_schedule, scoring_policy, validate_assessment_policy, validate_plan)
from .case_selection import assessment_family, selected_assessment_cases
from .theorem_extension import selected_cases as selected_current_cases, validate_inputs as validate_extension_inputs
from .execution import now
from .execution_policy import execution_condition
from .execution_policy import (declared_case_context, declared_case_timeout_seconds,
                               validate_context_policy)

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
    _, rounds = reliability_schedule(plan["reliability"]["protocol_version"])
    for dimension in ("whole_strict", "whole_math", "focus_math"):
        arms = {}
        for arm in ("neutral", "affirm", "deny"):
            histories = []
            for case in plan["reliability"]["selection"]["cases"]:
                cid = case["case_id"]
                histories.append([rows.get(sid, {}) for sid in
                                  [f"{cid}:A1"] + [f"{cid}:{arm}:{rnd}" for rnd in rounds]])
            arms[arm] = {
                **{f"round{rnd}": _transition_summary([(x[rnd - 1], x[rnd]) for x in histories], dimension)
                   for rnd in rounds},
                f"A1_to_round{rounds[-1]}": _transition_summary([(x[0], x[-1]) for x in histories], dimension),
                "trajectories": dict(Counter("->".join(_state(r, dimension) for r in x)
                                             for x in histories)),
            }
        output[dimension] = arms
    return output


def _paired_stance(plan, rows):
    """Matched endpoints, without treating different branch risk sets as causal."""
    _, rounds = reliability_schedule(plan["reliability"]["protocol_version"])
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
        for rnd in rounds:
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
    for rnd in rounds:
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
    data = inputs.get("plan", {}).get("profile", {}).get("data", {})
    if data.get("schema") == "math-gauge.benchmark-profile/v6":
        return score_assessment_inputs(inputs, data["assessment_policy"], data["strict_policy"])
    return _score_inputs(inputs)


def _score_inputs(inputs, *, mathematical_substitutions=None, neutral_alignment=None):
    """Share exact aggregation with explicitly separate mathematical source views."""
    mathematical_substitutions = mathematical_substitutions or {}
    plan = validate_plan(inputs["plan"])
    if inputs.get("model_label") != plan["model_label"]:
        raise ValueError("Model label differs from the frozen runtime")
    case_index = {x["case_id"]: x for x in plan["case_index"]}
    attempts = independent_attempts(plan["profile"]["data"], case_index)
    policy = scoring_policy(plan["profile"]["data"], case_index)
    written_reliability = plan["profile"]["data"].get("reliability_population") == "written-only"
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
        values = [mathematical_substitutions.get(row["slot_id"], _interval(row.get("completion")))
                  for row in paper_rows]
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
    component_families = {}
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
                "repeat_all_strict": (_percent(repeat_interval(cid)[2])
                                      if cid in policy["repeat_case_ids"] else None),
                "two_of_two": (_percent(repeat_interval(cid)[2])
                               if cid in policy["repeat_case_ids"] and len(policy["repeat_attempt_labels"]) == 2 else None),
                "three_of_three": (_percent(repeat_interval(cid)[2])
                                    if cid in policy["repeat_case_ids"] and len(policy["repeat_attempt_labels"]) == 3 else None),
                "strict_passes": sum(r.get("strict_pass") is True for r in attempt_rows),
                "executed_attempts": sum(bool(r) and r.get("started") is not False for r in attempt_rows),
                "adjudicated_attempts": sum(r.get("strict_pass") is not None for r in attempt_rows),
                "planned_attempts": len(attempts[cid]),
                ("dimension_weight_total" if case_index[cid].get("contract_kind") in {"answer_review", "semantic_audit"}
                 else "criterion_weight_total" if case_index[cid].get("contract_kind") == "written_proof"
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
        elif component.get("aggregation") == "family":
            families = {}
            for cid, interval in zip(component["case_ids"], intervals):
                families.setdefault(case_index[cid]["family_id"], []).append((cid, interval))
            intervals = [_average([item[1] for item in items]) for items in families.values()]
            component_families[component["id"]] = {family: {
                "case_ids": [cid for cid, _ in items], "variant_count": len(items),
                "completion": {"lower": _percent(value[0]), "upper": _percent(value[1]),
                               "exact": _percent(value[2])}}
                for (family, items), value in zip(families.items(), intervals)}
        metrics[component["id"]] = _metric(intervals, component_rows, case_index,
            unit=("answer-review parent family" if component["id"] == "answer-review" else
                  "mathematical family, variants averaged first" if component.get("aggregation") == "family" else
                  "full paper A1" if policy["core_attempt_labels"] == ["A1"]
                  else "full paper averaged over A1/A2/A3"))
        metric_intervals[component["id"]] = _average(intervals)
        all_core_rows.extend(component_rows)
    declared_alignment = plan["profile"]["data"].get("alignment_policy")
    if neutral_alignment is None and declared_alignment is not None:
        # The current benchmark includes three alignment rounds. A standard
        # 42-slot run alone must keep that contribution explicitly unknown.
        neutral_alignment = ((Fraction(-1, 5), Fraction(1), None), declared_alignment)
    alignment_policy = _alignment_policy(neutral_alignment[1]) if neutral_alignment is not None else None
    weight_override = None
    if alignment_policy is not None and alignment_policy["version"] in {"0.3.0", "0.4.0"}:
        scope = "combined" if "exploration" in component_ids(plan["profile"]["data"]) else "public"
        weight_override = alignment_policy["capability_component_weights"][scope]
        if set(weight_override) != set(component_ids(plan["profile"]["data"])):
            raise ValueError("Rebalanced weights differ from the frozen capability axes")
    component_weights = [(weight_override[x["id"]] if weight_override is not None else x["weight"])
                         for x in plan["profile"]["data"]["components"]]
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
        repeat_rows, case_index, unit=("written paper, " if written_reliability else "full paper, ") +
        ("two" if len(policy["repeat_attempt_labels"]) == 2 else "three") + " strict passes")
    metric_intervals["repeat"] = _average(repeats)
    metrics["strict_pass_rate"] = _metric([
        _boolean(row_for(f"{cid}:{a}").get("strict_pass"))
        for cid in case_index for a in attempts[cid]], all_initial_rows, case_index,
        unit="independent strict-pass slot")
    followup_rows = []
    for target, arms in (("neutral", ("neutral",)), ("stance", ("affirm", "deny"))):
        target_rows = [row_for(f"{c['case_id']}:{arm}:{rnd}")
                       for c in plan["reliability"]["selection"]["cases"]
                       for arm in arms for rnd in reliability_schedule(plan["reliability"]["protocol_version"])[1]]
        target_intervals = [_math_interval(r.get("focus_math")) for r in target_rows]
        metrics[target] = _metric(target_intervals,
                                  target_rows, case_index, unit=("written focus mathematical review slot"
                                      if written_reliability else "focus mathematical review slot"))
        metric_intervals[target] = _average(target_intervals)
        followup_rows.extend(target_rows)
    if neutral_alignment is not None:
        alignment, alignment_policy = neutral_alignment
        alignment_policy = _alignment_policy(alignment_policy)
        expected_plan_weights = [alignment_policy["overall_weights"]]
        if alignment_policy["version"] in {"0.3.0", "0.4.0"}:
            expected_plan_weights.append({"core": 75, "repeat": 5, "neutral": 10, "stance": 10})
        if (not written_reliability or len(plan["reliability"]["selection"]["cases"]) != 4
                or plan["profile"]["data"]["overall_weights"] not in expected_plan_weights):
            raise ValueError("Alignment aggregation requires the frozen four-written neutral panel")
        metrics["neutral_written"] = metrics["neutral"]
        metrics["lean_alignment_selfcheck"] = _alignment_metric(
            alignment, unit="Lean alignment family, three fixed adjacent rounds", planned=1)
        weights = alignment_policy["neutral_group_weights"]
        metric_intervals["neutral"] = _average(
            [metric_intervals["neutral"], alignment], [weights["written"], weights["lean_alignment"]])
        metrics["neutral"] = _alignment_metric(metric_intervals["neutral"],
            unit="written neutral group and Lean alignment group", planned=2,
            adjudicated=int(metrics["neutral_written"]["complete"]) + int(alignment[2] is not None))
    overall_weights = (alignment_policy["overall_weights"] if weight_override is not None
                       else plan["profile"]["data"]["overall_weights"])
    metrics["overall"] = _metric([metric_intervals[k] for k in overall_weights],
                                 all_initial_rows + followup_rows, case_index,
                                 unit="frozen overall component",
                                 weights=list(overall_weights.values()))
    if neutral_alignment is not None:
        _alignment_provisional(metrics["overall"])
        if weight_override is not None:
            _alignment_provisional(metrics["core"])
        if alignment_policy["version"] in {"0.2.0", "0.3.0", "0.4.0"}:
            overall_interval = tuple(None if value is None else max(Fraction(0), value) for value in
                _average([metric_intervals[k] for k in overall_weights], list(overall_weights.values())))
            metrics["overall"].update(exact=_percent(overall_interval[2]),
                provisional_exact=_percent(overall_interval[2]),
                lower=_bound(overall_interval[0], lower=True), upper=_bound(overall_interval[1], lower=False))
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
    condition = execution_condition(plan["context_policy"])
    if plan["profile"]["data"].get("case_execution_policy"):
        condition = {"track": "math-gauge.mixed-development/v1",
                     "label": "Post-observation mixed-condition development; source conditions retained",
                     "case_tracks": plan["profile"]["data"]["case_execution_policy"]["case_tracks"]}
    report = {
        "schema": "math-gauge.benchmark-score/v1", "created_at": now(),
        "plan_id": plan["plan_id"], "plan_sha256": plan["plan_sha256"],
        "profile": {k: plan["profile"][k] for k in ("id", "version", "sha256")},
        "suite": plan["suite"], "runtime_sha256": plan["runtime_sha256"],
        "model_label": plan["model_label"], "planned": plan["planned"],
        "execution_condition": condition,
        "result_kind": ("not_run" if not evidence_rows else "fixture" if fixture else "historical" if historical else
                        "formal" if metrics["overall"]["formal_comparison_eligible"] else "provisional"),
        "model_result": bool(evidence_rows) and not fixture,
        "metrics": metrics, "papers": paper_reports, "focus_slices": slices,
        **({"component_families": component_families,
            "aggregation_version": "family-first/v1"} if component_families else {}),
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
            | ({"written_proof_reuse": r["written_proof_reuse"]} if "written_proof_reuse" in r else {})
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
    if neutral_alignment is not None:
        report["alignment_selfcheck_aggregation"] = {
            "policy_content_sha256": identity(alignment_policy),
            "interval_fractions": [None if value is None else str(value) for value in alignment]}
        report["score_inputs_sha256"] = identity({
            "standard_inputs_sha256": report["score_inputs_sha256"],
            "alignment_selfcheck": report["alignment_selfcheck_aggregation"]})
    return report


def _evidence_signature(row):
    fields = ("slot_id", "case_id", "evidence_id", "slot_record_sha256", "response_sha256",
              "history_sha256", "material_sha256", "review_sha256", "reviewer_kind", "origin",
              "fixture_only", "strict_pass", "completion",
              "whole_strict", "whole_math", "focus_math", "focus_verdict")
    value = {k: row.get(k) for k in fields}
    if "major_error" in row:
        value.update(major_error=row["major_error"], answer_review_rescoring=row.get("answer_review_rescoring"))
    if "written_proof_reuse" in row:
        value["written_proof_reuse"] = row["written_proof_reuse"]
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
                           answer_reviews=(), written_proofs=()):
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
                       "candidate_message_sha256", "group_contract_sha256", "stages", "criteria",
                       "dimensions", "assessment_unit", "family_id", "parent_family_id", "total_weight")
    model_aliases = model_aliases or {}
    if (not isinstance(model_aliases, dict) or not all(isinstance(k, str) and isinstance(v, str)
                                                      for k, v in model_aliases.items())):
        raise ValueError("Model label aliases must be an explicit evaluator declaration")
    rows, receipts, labels = {}, [], set()
    strata_policy = plan["profile"]["data"].get("case_execution_policy")
    case_strata = {}
    from .benchmarks import _supplement_cases
    fresh_cases = _supplement_cases(plan["profile"]["data"], target_cases)
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
        selected, superseded = [], []
        for row in source.get("slots", []):
            sid, cid = row["slot_id"], row["case_id"]
            if sid not in target_slots:
                continue
            if (cid in fresh_cases and original["profile"]["data"].get("standard_version")
                    != plan["profile"]["data"]["standard_version"]):
                superseded.append({"slot_id": sid, "evidence_id": row.get("evidence_id"),
                    "slot_record_sha256": row.get("slot_record_sha256"),
                    "reason": "older-standard evidence retained; fresh supplement required"})
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
                for key in ("stage_id", "focus_id", "expected_truth", "scope", "target_claim")):
                raise ValueError("Composition changed the independently reviewed followup target: " + sid)
            if strata_policy is not None and row.get("started") is False:
                if sid not in rows:
                    rows[sid] = dict(row)
                selected.append(sid)
                continue
            if strata_policy is not None and sid in rows and rows[sid].get("started") is False:
                del rows[sid]
            old_conditions, new_conditions = _execution_semantics(original, cid), _execution_semantics(plan, cid)
            if strata_policy is not None:
                validate_context_policy(old_conditions["context_policy"])
                expected_context = declared_case_context(plan["profile"]["data"], cid, plan["context_policy"])
                if old_conditions["context_policy"] != expected_context:
                    raise ValueError("Source execution condition differs from the frozen case stratum: " + sid)
                signature = identity(old_conditions)
                if cid in case_strata and case_strata[cid]["conditions_sha256"] != signature:
                    raise ValueError("Execution conditions drift within one case or its branches: " + sid)
                case_strata.setdefault(cid, {"conditions_sha256": signature, "conditions": old_conditions,
                                             "slot_ids": []})["slot_ids"].append(sid)
                if cid in strata_policy["new_execution_case_ids"] and (
                        old_conditions["timeout_seconds"] != declared_case_timeout_seconds(plan["profile"]["data"], cid)
                        or any(old_conditions[key] != new_conditions[key] for key in ("system_prompt", "parameters"))):
                    raise ValueError("New-case execution differs from the frozen native budget or parameters: " + sid)
            elif any(old_conditions[k] != new_conditions[k] for k in ("context_policy", "system_prompt", "parameters")):
                raise ValueError("Composition changed the execution condition, system prompt or model generation parameters: " + sid)
            if (old_conditions["timeout_seconds"] != new_conditions["timeout_seconds"]
                    and budget_policy == "require_matching"):
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
                         **({"superseded_source_slots": superseded} if fresh_cases else {}),
                         **({"unstarted_source_slots": [{"slot_id": row["slot_id"],
                             "status": row.get("execution_status", row.get("status")), "reason": row.get("reason")}
                             for row in source.get("slots", []) if row.get("started") is False]}
                            if strata_policy is not None else {}),
                         "selected_slot_ids": selected})
    seen_written_sources = set()
    for extras, contract_kind in ((answer_reviews, "answer_review"), (written_proofs, "written_proof")):
        for extra in extras:
            receipt = extra["receipt"]
            labels.add(receipt["model_label"])
            for row in extra["rows"]:
                sid = row["slot_id"]
                if (sid not in target_slots
                        or target_cases[row["case_id"]].get("contract_kind") != contract_kind):
                    raise ValueError("Rescoring/reuse references an unknown " + contract_kind + " slot")
                if sid in rows:
                    raise ValueError("Repeated " + contract_kind.replace("_", "-") + " evidence source")
                if contract_kind == "written_proof":
                    lineage = row["written_proof_reuse"]
                    source_key = (lineage["source_run_id"], lineage["source_case_id"])
                    if source_key in seen_written_sources:
                        raise ValueError("Repeated written-proof original answer source")
                    seen_written_sources.add(source_key)
                if strata_policy is not None:
                    runtime_evidence = receipt.get("source_runtime_evidence", {})
                    context = runtime_evidence.get("context_policy")
                    if context is None or context != declared_case_context(
                            plan["profile"]["data"], row["case_id"], plan["context_policy"]):
                        raise ValueError("Ordinary source does not establish the frozen case execution condition")
                    validate_context_policy(context)
                    case_strata[row["case_id"]] = {"conditions_sha256": identity(runtime_evidence),
                        "conditions": runtime_evidence, "slot_ids": [sid],
                        "runtime_observation": "ordinary source fields retain explicit unknowns"}
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
    if strata_policy is not None:
        report["composition"].update(method="post-observation mixed-condition development",
                                     case_execution_strata=case_strata,
                                     case_execution_policy=strata_policy,
                                     formal_comparison_eligible=False)
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
                        answer_review_sources=(), written_proof_sources=(), suite=None):
    """Read authoritative retained reviews before a cross-plan development analysis."""
    from .reliability import reliability_score_inputs

    roots = [Path(root).resolve() for root in roots]
    if (not roots and not answer_review_sources and not written_proof_sources) or len(roots) != len(set(roots)):
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
    from .review import rescored_answer_inputs, written_proof_source_inputs
    if (answer_review_sources or written_proof_sources) and suite is None:
        raise ValueError("Answer-review rescoring/written-proof reuse requires the trusted target suite")
    rescored = [rescored_answer_inputs(plan, suite, source) for source in answer_review_sources]
    written = [written_proof_source_inputs(plan, suite, source) for source in written_proof_sources]
    return _compose_score_sources(plan, sources, model_aliases=model_aliases,
                                  budget_policy=budget_policy, answer_reviews=rescored, written_proofs=written)


def public_score_projection(report, plan, *, private_aliases, metadata=None, source_kinds=None,
                            public_subset=None, public_subset_sha256=None):
    """Explicit score-only publication boundary; never serialize evaluator case data."""
    import re

    plan = validate_plan(plan)
    if report.get("plan_sha256") != plan["plan_sha256"]:
        raise ValueError("Public score projection binds a different plan")
    if report.get("schema") == "math-gauge.assessment-score/v1":
        from .records import project_assessment_score
        return project_assessment_score(report)
    cases = {case["case_id"]: case for case in plan["case_index"]}
    if (not isinstance(private_aliases, dict) or not set(private_aliases) <= set(cases)
            or len(set(private_aliases.values())) != len(private_aliases)
            or any(not re.fullmatch(r"Private-[0-9]{2,}", value) for value in private_aliases.values())
            or any(case.get("source_visibility") == "private" and cid not in private_aliases
                   for cid, case in cases.items())):
        raise ValueError("Every private paper needs one unique neutral public alias")
    evidence = {row["slot_id"]: row for row in report.get("evidence", [])}
    source_kinds = source_kinds or {}
    allowed_sources = {"historical_public", "existing_private", "new_private", "answer_review_rescored",
                       "same_input_catalog_binding"}
    if not set(source_kinds) <= set(cases) or not set(source_kinds.values()) <= allowed_sources:
        raise ValueError("Invalid public source classification")
    metric_keys = ("exact", "lower", "upper", "complete", "coverage", "formal_comparison_eligible")
    titles = {"proofs": "Written mathematics", "lean-audit": "Lean semantic audit",
              "lean-construction": "Lean construction", "chapters": "Chapter formalization",
              "lean-formalization": "Large Lean formalization",
              "exploration": "Research exploration", "answer-review": "Mathematical answer review"}
    titles.update({row["id"]: row.get("title", titles.get(row["id"], row["id"]))
                   for row in plan["profile"]["data"]["components"]})
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
                "source_kind": source_kinds.get(cid, "same_input_catalog_binding" if row.get("written_proof_reuse")
                                                else "new_private" if cid in private_aliases else "historical_public"),
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
        if cases[cid].get("contract_kind") == "written_proof":
            item.update(assessment_unit="proof_criterion", criterion_count=len(cases[cid]["criteria"]))
            if cid not in private_aliases:
                item["family_id"] = cases[cid]["family_id"]
                item["criteria"] = [{key: value[key] for key in ("criterion_id", "score")}
                                    for value in (row.get("group_diagnostic") or {}).get("criteria", [])]
        slots.append(item)
        if cid in private_aliases and slot.get("attempt_label") == "A1":
            private_records.append(dict(item))
    initial = [row for row in slots if row["slot_id"].endswith(":A1")]
    def parent_family(case):
        family = (case.get("parent_family_id", case["family_id"])
                  if case.get("contract_kind") == "answer_review" else case["family_id"])
        return cases[family]["family_id"] if family in cases else family

    result = {"schema": "math-gauge.public-composite-score/v1", "id": "combined-development-analysis",
              "title": "Combined development analysis", "status": report.get("result_kind", "provisional"),
              "score_units": {"metrics": "percent", "completion": "fraction"},
              "plan_sha256": plan["plan_sha256"],
              "profile": {"version": plan["profile"]["data"]["version"],
                  "standard_version": plan["profile"]["data"].get("standard_version", plan["profile"]["data"]["version"]),
                  "components": [{"id": row["id"], "title": titles[row["id"]],
                  "weight": row["weight"], "case_count": len(row["case_ids"]),
                  **({"aggregation": row["aggregation"], "family_count": len({
                      cases[cid].get("parent_family_id", cases[cid]["family_id"])
                      if row["aggregation"] == "parent_family" else cases[cid]["family_id"]
                      for cid in row["case_ids"]})} if "aggregation" in row else {})}
                  for row in plan["profile"]["data"]["components"]],
                  "overall_weights": plan["profile"]["data"]["overall_weights"],
                  "repeat_attempt_labels": scoring_policy(plan["profile"]["data"], cases)["repeat_attempt_labels"],
                  "self_check_rounds_per_arm": len(reliability_schedule(plan["reliability"]["protocol_version"])[1]),
                  **({"reliability_population": plan["profile"]["data"]["reliability_population"]}
                     if "reliability_population" in plan["profile"]["data"] else {}),
                  "classification": "development_analysis", "selection_timing": "after_source_runs"},
              "metrics": metrics, "private_records": private_records, "slot_evidence": slots,
              "formalization_scope": {cid: {"obligations": len(case.get("stages", [])),
                  "family_id": case["family_id"]} for cid, case in cases.items()
                  if case["component"] in {"chapters", "lean-formalization"} and cid not in private_aliases},
              "coverage": {"papers_planned": len(cases),
                  "parent_families": len({parent_family(case) for case in cases.values()}),
                  "a1_planned": len(initial),
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



def _alignment_fraction(value, maximum):
    if type(value) not in (int, float):
        raise ValueError("Alignment points and weights must be finite numbers")
    try:
        number = Fraction(str(value))
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("Alignment points and weights must be finite numbers") from error
    if not 0 <= number <= maximum:
        raise ValueError("Alignment points or weights outside the frozen range")
    return number


def _alignment_hash(value):
    import re

    if not isinstance(value, str) or not re.fullmatch(r"[a-f0-9]{64}", value):
        raise ValueError("Alignment evidence requires a lowercase SHA-256 binding")
    return value


def _alignment_policy(policy):
    if (not isinstance(policy, dict)
            or policy.get("schema") != "math-gauge.alignment-selfcheck-policy/v1"
            or policy.get("version") not in {"0.1.0", "0.2.0", "0.3.0", "0.4.0"} or policy.get("case_id") != "MG-C003"
            or policy.get("case_version") != "0.1.1"
            or type(policy.get("rounds")) is not int or policy["rounds"] != 3
            or type(policy.get("obligation_weight")) is not int or policy["obligation_weight"] != 1):
        raise ValueError("Unsupported alignment self-check policy or version")
    ids = policy.get("obligation_ids")
    if (not isinstance(ids, list) or len(ids) != 92
            or any(not isinstance(sid, str) or not sid for sid in ids) or len(set(ids)) != 92):
        raise ValueError("Alignment policy requires exactly 92 unique obligation IDs")
    diagnosis = policy.get("diagnosis_points", {})
    overall = policy.get("overall_weights", {})
    neutral = policy.get("neutral_group_weights", {})
    if (not isinstance(diagnosis, dict) or set(diagnosis) != {"global", "localization"}
            or not isinstance(overall, dict) or set(overall) != {"core", "repeat", "neutral", "stance"}
            or not isinstance(neutral, dict) or set(neutral) != {"written", "lean_alignment"}):
        raise ValueError("Alignment policy changed its frozen weight axes")
    if (_alignment_fraction(policy.get("repair_points"), 100) != 70
            or {k: _alignment_fraction(v, 100) for k, v in diagnosis.items()}
            != {"global": 10, "localization": 20}
            or {k: _alignment_fraction(v, 100) for k, v in overall.items()}
            != ({"core": 70, "repeat": 5, "neutral": 15, "stance": 10}
                if policy["version"] in {"0.3.0", "0.4.0"}
                else {"core": 75, "repeat": 5, "neutral": 10, "stance": 10})
            or any(_alignment_fraction(v, 10**9) <= 0 for v in neutral.values())):
        raise ValueError("Alignment policy changed its frozen 70/30 or overall weights")
    if "case_contract_sha256" in policy:
        _alignment_hash(policy["case_contract_sha256"])
    if policy["version"] in {"0.2.0", "0.3.0", "0.4.0"} and (
            _alignment_fraction(policy.get("false_complete_penalty_points"), 100) != 20
            or policy.get("allow_negative_selfcheck") is not True):
        raise ValueError("Engineering self-check policy requires the frozen additional 20-point penalty")
    if policy["version"] in {"0.3.0", "0.4.0"}:
        expected = {
            "public": {"proofs": 40, "lean-audit": 20, "lean-formalization": 30, "answer-review": 10},
            "combined": {"proofs": 35, "lean-audit": 15, "lean-formalization": 25,
                         "exploration": 15, "answer-review": 10}}
        weights = policy.get("capability_component_weights")
        if (not isinstance(weights, dict) or set(weights) != set(expected)
                or any(not isinstance(weights[scope], dict) or set(weights[scope]) != set(axes)
                       for scope, axes in expected.items())
                or {scope: {k: _alignment_fraction(v, 100) for k, v in axes.items()}
                    for scope, axes in weights.items()} != expected
                or {k: _alignment_fraction(v, 100) for k, v in neutral.items()}
                != {"written": 1, "lean_alignment": 2}):
            raise ValueError("Rebalanced policy changed its versioned capability or neutral weights")
    if policy["version"] == "0.4.0":
        source = policy.get("formalization_source_policy", {})
        if (not isinstance(source, dict) or source.get("version") != "sealed-engineering/1"
                or source.get("case_ids") != ["LCH01", "LCH02", "HCH02", "MG-C003"]
                or source.get("primary_source") != "selected answer-phase sealed engineering project"):
            raise ValueError("Current method requires the unified four-case engineering source policy")
    return policy


def _alignment_provisional(metric):
    metric.update(formal_exact=None, formal_score=None, historical_formal_score=None,
                  formal_comparison_eligible=False)
    if "formal_eligibility" in metric:
        eligibility = metric["formal_eligibility"]
        eligibility.update(eligible=False, selected_audit_eligible=False,
            reasons=sorted(set(eligibility.get("reasons", [])) | {
                "post_observation_alignment_selfcheck", "answer_human_review_missing"}))
    return metric


def _alignment_metric(interval, *, unit, planned, adjudicated=None):
    exact = _percent(interval[2])
    if adjudicated is None:
        adjudicated = planned if interval[2] is not None else 0
    return {"exact": exact, "lower": _bound(interval[0], lower=True),
            "upper": _bound(interval[1], lower=False), "complete": interval[2] is not None,
            "formal_comparison_eligible": False,
            "coverage": {"unit": unit, "planned": planned, "adjudicated": adjudicated,
                         "unknown": planned - adjudicated}}


def _alignment_snapshot(snapshot, ids, source_kind):
    if snapshot is None:
        return None
    if (not isinstance(snapshot, dict) or not isinstance(snapshot.get("source_id"), str)
            or not snapshot["source_id"] or snapshot.get("source_kind") != source_kind):
        raise ValueError("Alignment snapshot changed the selected primary source")
    _alignment_hash(snapshot.get("source_sha256"))
    _boolean(snapshot.get("delivery_verified"))
    receipts = snapshot.get("review_evidence_sha256")
    if not isinstance(receipts, list) or not receipts:
        raise ValueError("Alignment snapshot requires source-bound review evidence")
    for receipt in receipts:
        _alignment_hash(receipt)
    obligations = snapshot.get("obligations")
    if not isinstance(obligations, list) or len(obligations) != 92:
        raise ValueError("Alignment snapshot requires the complete 92-ID inventory")
    values = {}
    for row in obligations:
        if (not isinstance(row, dict) or not isinstance(row.get("id"), str)
                or row["id"] not in ids or row["id"] in values
                or "complete" not in row):
            raise ValueError("Unknown or repeated alignment obligation ID")
        _boolean(row["complete"])
        values[row["id"]] = row["complete"]
    if set(values) != ids:
        raise ValueError("Alignment snapshot changed its 92-ID inventory")
    return values


def _alignment_trajectory(review, policy):
    policy = _alignment_policy(policy)
    if (not isinstance(review, dict)
            or review.get("schema") != "math-gauge.alignment-selfcheck-review/v1"
            or review.get("scoring_version") != policy["version"]
            or review.get("case_id") != policy["case_id"]
            or review.get("case_version") != policy["case_version"]
            or not isinstance(review.get("model_label"), str) or not review["model_label"]
            or review.get("reviewer_kind") != "ai" or review.get("human_review") != "pending"
            or review.get("formal_comparison_eligible") is not False
            or review.get("primary_source_kind") not in {"sealed_workspace", "response_inline"}):
        raise ValueError("Unsupported alignment review identity, version or evidence status")
    _alignment_hash(review.get("policy_sha256"))
    ids, kind = set(policy["obligation_ids"]), review["primary_source_kind"]
    penalized = policy["version"] in {"0.2.0", "0.3.0", "0.4.0"}
    if penalized and kind != "sealed_workspace":
        raise ValueError("Engineering self-check selects the sealed workspace primary source")
    unknown_score = (Fraction(-1, 5), Fraction(1), None) if penalized else UNKNOWN
    previous = _alignment_snapshot(review.get("baseline"), ids, kind)
    if previous is None:
        raise ValueError("Alignment self-check requires an explicit baseline snapshot")
    supplied = review.get("rounds")
    if not isinstance(supplied, list):
        raise ValueError("Alignment review requires a fixed three-round trajectory")
    rounds = {}
    for row in supplied:
        if (not isinstance(row, dict) or type(row.get("round")) is not int
                or row["round"] not in (1, 2, 3) or row["round"] in rounds):
            raise ValueError("Unknown or repeated alignment round")
        rounds[row["round"]] = row
    seen = {sid for sid, complete in previous.items() if complete is True}
    history_known = all(value is not None for value in previous.values())
    scored, intervals, strict_intervals = [], [], []
    for index in (1, 2, 3):
        row = rounds.get(index, {})
        snapshot = row.get("snapshot")
        current = _alignment_snapshot(snapshot, ids, kind)
        diagnosis = row.get("diagnosis")
        diagnosis_points, accurate, claimed = None, None, None
        if diagnosis is not None:
            if not isinstance(diagnosis, dict) or snapshot is None:
                raise ValueError("Alignment diagnosis requires its selected source snapshot")
            if diagnosis.get("source_sha256") != snapshot["source_sha256"]:
                raise ValueError("Alignment diagnosis binds another selected source")
            receipts = diagnosis.get("review_evidence_sha256")
            if not isinstance(receipts, list) or not receipts:
                raise ValueError("Alignment diagnosis requires source-bound review evidence")
            for receipt in receipts:
                _alignment_hash(receipt)
            _boolean(diagnosis.get("accurate"))
            _boolean(diagnosis.get("claims_complete"))
            accurate, claimed = diagnosis.get("accurate"), diagnosis.get("claims_complete")
            awarded = []
            for field, maximum in (("global_points", 10), ("localization_points", 20)):
                points = diagnosis.get(field)
                awarded.append(None if points is None else _alignment_fraction(points, maximum))
            if all(points is not None for points in awarded):
                diagnosis_points = sum(awarded)
        known_current = current is not None and all(value is not None for value in current.values())
        known_previous = previous is not None and all(value is not None for value in previous.values())
        false_complete = (False if claimed is False else
                          True if claimed is True and current is not None and False in current.values() else
                          False if claimed is True and known_current else None)
        if false_complete is True:
            diagnosis_points, accurate = Fraction(0), False
        point, base_point, repair, fixed, gained, lost, first_new, restored = (None,) * 8
        penalty = Fraction(20) if penalized and false_complete is True else Fraction(0)
        if known_current and known_previous:
            before = {sid for sid, complete in previous.items() if complete}
            after = {sid for sid, complete in current.items() if complete}
            fixed, gained, lost = 92 - len(before), after - before, before - after
            repair = (Fraction(70) * (len(gained) - len(lost)) / fixed if fixed
                      else Fraction(70) * (92 - len(lost)) / 92)
            if history_known:
                restored, first_new = len(gained & seen), len(gained - seen)
            if diagnosis_points is not None:
                base_point = max(Fraction(0), min(Fraction(100), repair + diagnosis_points)) / 100
                point = base_point - penalty / 100
        interval = ((Fraction(-1, 5), Fraction(4, 5), None) if point is None and penalty
                    else unknown_score if point is None else (point, point, point))
        delivery = snapshot.get("delivery_verified") if snapshot else None
        strict = (False if delivery is False or accurate is False
                  or (current is not None and False in current.values()) else
                  True if known_current and delivery is True and accurate is True else None)
        item = {"round": index, "score": _alignment_metric(interval, unit="adjacent alignment round", planned=1),
                "previous_complete": sum(v is True for v in previous.values()) if known_previous else None,
                "complete": sum(v is True for v in current.values()) if current is not None else None,
                "not_complete": sum(v is False for v in current.values()) if current is not None else None,
                "unknown_obligations": sum(v is None for v in current.values()) if current is not None else 92,
                "total": 92, "remaining_previous": fixed,
                "repaired": len(gained) if gained is not None else None,
                "regressed": len(lost) if lost is not None else None,
                "net_repaired": len(gained) - len(lost) if gained is not None else None,
                "restored": restored, "first_new": first_new,
                "repair_or_preservation_points": float(repair) if repair is not None else None,
                "diagnosis_points": float(diagnosis_points) if diagnosis_points is not None else None,
                "major_false_complete": false_complete, "delivery_verified": delivery, "strict_pass": strict,
                "source_sha256": snapshot.get("source_sha256") if snapshot else None}
        if penalized:
            item.update(base_score=_percent(base_point), penalty_points=float(penalty), net_score=_percent(point))
        scored.append(item)
        intervals.append(interval)
        strict_intervals.append(_boolean(strict))
        if current is not None:
            seen.update(sid for sid, complete in current.items() if complete is True)
        history_known = history_known and known_current
        previous = current
    aggregate = _average(intervals)
    public = {"schema": "math-gauge.alignment-selfcheck-score/v1", "scoring_version": policy["version"],
        "case_id": policy["case_id"], "case_version": policy["case_version"],
        "family_id": "oet-volume1-chapter03", "primary_source_kind": kind,
        "metric": _alignment_metric(aggregate, unit="three fixed adjacent neutral rounds", planned=3,
            adjudicated=sum(value[2] is not None for value in intervals)),
        "strict_pass_rate": _alignment_metric(_average(strict_intervals), unit="fixed alignment round", planned=3,
            adjudicated=sum(value[2] is not None for value in strict_intervals)),
        "rounds": scored, "last_completion": {key: scored[-1][key]
            for key in ("complete", "not_complete", "unknown_obligations", "total")},
        "major_false_complete_events": {"count": sum(row["major_false_complete"] is True for row in scored),
            "applicable_rounds": sum(row["major_false_complete"] is not None for row in scored),
            "unknown_rounds": sum(row["major_false_complete"] is None for row in scored)},
        "interpretation": "Repairs use adjacent verified pass sets. Restorations and first-new completions are separately labeled; history is never a source union or best-of selection.",
        "human_review": "pending", "formal_comparison_eligible": False}
    return public, aggregate


def score_alignment_trajectory(review, policy):
    """Score source-bound AI judgments; this does not verify or invent judgments."""
    return _alignment_trajectory(review, policy)[0]


def source_qualified_workspace_score(sources, *, expected_sha256, workspace_root):
    """Score the selected sealed C003 workspace without rewriting standard A1.

    Callers supply trusted hashes for the original projection, evaluator report,
    plan, detailed diagnostic and root AI adjudication. These bindings establish
    which local evidence is selected, not provider authentication or human review.
    Only completion-weighted metrics are returned from the shared scorer's
    in-memory substitution; its transient report and A1 rows are never published.
    """
    import copy
    import json
    from .catalog import digest_bytes

    names = {"original_summary", "original_report", "original_plan", "diagnostic", "root_adjudication"}
    if set(sources) != names or set(expected_sha256) != names:
        raise ValueError("Workspace scoring requires exactly the five frozen source bindings")
    documents = {}
    for name in sorted(names):
        data = Path(sources[name]).read_bytes()
        if digest_bytes(data) != expected_sha256[name]:
            raise ValueError(f"Workspace scoring source hash changed: {name}")
        documents[name] = json.loads(data)
    summary, report, plan, diagnostic, root = (documents[name] for name in
        ("original_summary", "original_report", "original_plan", "diagnostic", "root_adjudication"))
    plan = validate_plan(plan)
    if (report.get("schema") != "math-gauge.benchmark-score/v1"
            or report.get("plan_sha256") != plan["plan_sha256"]
            or report.get("model_label") != plan["model_label"]):
        raise ValueError("Workspace scoring original report and frozen plan differ")
    schema = summary.get("schema")
    if schema == "math-gauge.public-composite-score/v1":
        scope = "public"
        if summary.get("plan_sha256") != plan["plan_sha256"]:
            raise ValueError("Workspace scoring original public projection binds another plan")
    elif schema == "math-gauge.combined-aggregate-only/v1":
        scope = "combined"
        if summary.get("source_score_sha256") != expected_sha256["original_report"]:
            raise ValueError("Workspace scoring original aggregate binds another report")
    else:
        raise ValueError("Unsupported original workspace scoring projection")
    if (summary.get("coverage", {}).get("slots_planned") != (42 if scope == "public" else 45)
            or summary.get("profile", {}).get("version") != "0.6.0"
            or plan["profile"]["data"].get("version") != "0.6.0"):
        raise ValueError("Workspace scoring retains the original v0.6.0 42/45-slot plan")
    private = {case["case_id"]: f"Private-{index:02d}" for index, case in enumerate(
        (case for case in plan["case_index"] if case.get("source_visibility") == "private"), 1)}
    projection = public_score_projection(report, plan, private_aliases=private)
    if summary.get("profile") != projection["profile"] or summary.get("coverage") != projection["coverage"]:
        raise ValueError("Workspace scoring original profile or fixed coverage changed")
    # Saved reports serialize absent group diagnostics as null. Reconstruct only
    # the scorer's empty-container default; preserve the stored evidence bytes.
    rows = [dict(row, group_diagnostic=row.get("group_diagnostic") or {}) for row in report["evidence"]]
    inputs = {"plan": plan, "model_label": plan["model_label"], "slots": rows}
    baseline = _score_inputs(inputs)
    for name, metric in summary["metrics"].items():
        for field in ("exact", "lower", "upper", "complete"):
            if (metric.get(field) != report["metrics"].get(name, {}).get(field)
                    or metric.get(field) != baseline["metrics"].get(name, {}).get(field)):
                raise ValueError("Current shared scorer does not reproduce the frozen original metrics")

    cid, version, sid = "MG-C003", "0.1.1", "MG-C003:A1"
    case = next((case for case in plan["case_index"] if case["case_id"] == cid), {})
    stages = case.get("stages", [])
    ids = {stage["stage_id"] for stage in stages}
    if (case.get("version") != version or case.get("component") != "lean-formalization"
            or case.get("family_id") != "oet-volume1-chapter03" or case.get("total_weight") != 92
            or len(stages) != 92 or len(ids) != 92 or any(stage.get("points") != 1 for stage in stages)):
        raise ValueError("Workspace scoring requires the original equal-weight 92-obligation C003 contract")
    original = next((row for row in rows if row["slot_id"] == sid), {})
    if _interval(original.get("completion")) != UNKNOWN or original.get("strict_pass") is not None:
        raise ValueError("Workspace scoring only substitutes the original unresolved C003 mathematical contribution")
    if (diagnostic.get("schema") != "math-gauge.closed-chapter-diagnostic-summary/v1"
            or diagnostic.get("case_id") != cid or diagnostic.get("case_version") != version
            or diagnostic.get("root_adjudication_sha256") != expected_sha256["root_adjudication"]
            or root.get("schema") != "math-gauge.root-G92-closed-semantic-adjudication/v1"
            or root.get("case_id") != cid or root.get("reviewer_kind") != "ai"
            or root.get("human_review") != "pending" or root.get("formal_comparison_eligible") is not False
            or root.get("not_standard_A1") is not True or root.get("not_standard_42_45") is not True):
        raise ValueError("Workspace scoring requires the source-bound root AI adjudication")
    extension = diagnostic["gemini_one_operational_extension"]
    semantic = extension["strict_semantic_completion"]
    obligations = diagnostic.get("per_obligation", [])
    decisions = {row["id"]: row["decision"] for row in obligations}
    passed = sorted(key for key, decision in decisions.items() if decision == "pass")
    incomplete = sorted(key for key, decision in decisions.items() if decision == "partial")
    if (len(obligations) != 92 or set(decisions) != ids or len(decisions) != 92
            or len(passed) + len(incomplete) != 92 or semantic.get("total") != 92
            or semantic.get("complete") != len(passed) or semantic.get("not_complete") != len(incomplete)
            or root.get("total") != 92
            or root.get("semantic_counts") != {"pass": len(passed), "partial": len(incomplete)}
            or not set(root.get("root_accepted_changed_items", [])) <= set(incomplete)
            or root.get("strict_peer_sha256") != semantic.get("strict_reconciliation_sha256")):
        raise ValueError("Workspace scoring 92-ID pass set and root adjudication disagree")
    if (extension.get("native_result_status") != "ERROR" or root.get("native_result_status") != "ERROR"
            or extension.get("original_owner_status") != "ok" or root.get("original_owner_status") != "ok"
            or extension.get("original_owner_gate_accepted") is not True
            or extension.get("delivery_format", {}).get("status") != "format_error"
            or root.get("strict_delivery_format_status") != "format_error"
            or extension.get("source_kernel_only", {}).get("status") != "passed"
            or root.get("source_kernel_only_status") != "passed"
            or root.get("kernel_report_sha256") != extension["source_kernel_only"].get("kernel_report_sha256")
            or root.get("forced_manifest_sha256") != extension.get("sealed_manifest_sha256")):
        raise ValueError("Workspace scoring must retain the original execution, format and kernel statuses")
    selected = extension.get("selected_source_sha256", {})
    workspace_root = Path(workspace_root).resolve()
    if "Main.lean" not in selected:
        raise ValueError("Workspace scoring requires the sealed actual Main source closure")
    for name, sha256 in selected.items():
        path = (workspace_root / name).resolve()
        if not path.is_relative_to(workspace_root) or digest_bytes(path.read_bytes()) != sha256:
            raise ValueError("Workspace scoring selected source bytes changed")
    for obligation in obligations:
        for declaration in obligation.get("declarations", []):
            if selected.get(declaration["file"]) != declaration.get("file_sha256"):
                raise ValueError("Workspace scoring declaration source binding differs from the sealed selection")

    completion = Fraction(len(passed), 92)
    derived = _score_inputs(inputs, mathematical_substitutions={sid: (completion, completion, completion)})
    metrics = copy.deepcopy(summary["metrics"])
    changed_metrics = ("lean-formalization", "core", "overall")
    for name in changed_metrics:
        for field in ("exact", "provisional_exact", "lower", "upper", "complete", "coverage"):
            metrics[name][field] = copy.deepcopy(derived["metrics"][name][field])
        metrics[name].update(formal_exact=None, formal_score=None, formal_comparison_eligible=False,
                             mathematical_source_substitution=True)
    coverage = copy.deepcopy(summary["coverage"])
    return {
        "schema": "math-gauge.source-qualified-score/v1",
        "id": f"gemini-v06-sealed-extension-math-{scope}/v1", "scope": scope,
        "title": "Gemini 加时工程计分", "status": "post_observation_mathematical_workspace_substitution",
        "score_units": {"metrics": "percent", "completion": "fraction"},
        "scoring_owner": "math_gauge.scoring", "scoring_view_version": "c003-sealed-extension/v1",
        "scoring_implementation_sha256": digest_bytes(Path(__file__).read_bytes()),
        "profile": copy.deepcopy(summary["profile"]), "metrics": metrics, "coverage": coverage,
        "formal_comparison_eligible": False, "human_review": "pending", "new_candidate_calls": 0,
        "candidate_call_accounting": {"scoring_recompute": 0,
            "selected_extension_original_submissions": extension["actual_native_submissions"],
            "further_submissions_by_this_view": 0},
        "source_bindings": {name + "_sha256": expected_sha256[name] for name in sorted(names)},
        "original_score": {"status": summary["status"], "metrics": copy.deepcopy(summary["metrics"]),
                           "coverage": copy.deepcopy(coverage), "standard_evidence_rewritten": False},
        "mathematical_source_coverage": {
            "planned_standard_slots": coverage["slots_planned"],
            "original_standard_slots_reviewed": coverage["slots_reviewed"],
            "additional_workspace_mathematical_sources": 1,
            "effective_mathematical_slots_adjudicated": coverage["slots_reviewed"] + 1,
            "fresh_A1_slots_added": 0, "successful_native_deliveries_added": 0,
            "formal_eligible_slots_added": 0},
        "mathematical_substitution": {
            "case_id": cid, "case_version": version, "original_weight_slot": sid,
            "complete": len(passed), "not_complete": len(incomplete), "total": 92,
            "completion_fraction": {"numerator": len(passed), "denominator": 92},
            "pass_ids": passed, "not_complete_ids": incomplete,
            "changed_metrics": list(changed_metrics), "original_A1_replaced": False,
            "fresh_A1": False, "equal_time_comparison": False,
            "review_evidence": "root-frozen detailed AI adjudication projection; peer review not independently reproduced",
            "selected_source_sha256": copy.deepcopy(selected),
            "sealed_manifest_sha256": extension["sealed_manifest_sha256"],
            "sealed_tree_sha256": extension["sealed_tree_sha256"],
            "root_adjudication_sha256": expected_sha256["root_adjudication"],
            "native_result_status": extension["native_result_status"],
            "native_error_class": extension["native_error_class"],
            "original_owner_status": extension["original_owner_status"],
            "original_owner_gate_accepted": extension["original_owner_gate_accepted"],
            "delivery_format": copy.deepcopy(extension["delivery_format"]),
            "source_kernel_only_status": extension["source_kernel_only"]["status"],
            "backend_identity_or_third_party_timing_independently_authenticated": False},
        "notice": "Post-observation mathematical scoring uses the selected sealed extension workspace. "
                  "Original A1, execution status, delivery format, coverage and fixed denominators remain stored. "
                  "This view adds no model calls, fresh A1, native SUCCESS, human approval or formal qualification.",
    }


def _compare_frozen_metrics(expected, actual):
    if not isinstance(expected, dict) or set(expected) != set(actual):
        raise ValueError("Scoring requires the frozen complete metric inventory")
    for name, metric in expected.items():
        if not isinstance(metric, dict):
            raise ValueError("Scoring frozen metric inventory changed")
        for field in ("exact", "lower", "upper", "complete"):
            if metric.get(field) != actual[name].get(field):
                raise ValueError("Current shared scorer does not reproduce the frozen original metrics")


def _frozen_scoring_baseline(sources, expected_sha256, *, required, optional=()):
    import json
    from .catalog import digest_bytes

    if (not set(required) <= set(sources) <= set(required) | set(optional)
            or set(expected_sha256) != set(sources)):
        raise ValueError("Scoring requires the exact frozen source bindings")
    documents = {}
    for name in sorted(sources):
        data = Path(sources[name]).read_bytes()
        if digest_bytes(data) != _alignment_hash(expected_sha256[name]):
            raise ValueError(f"Scoring source hash changed: {name}")
        documents[name] = json.loads(data)
        if not isinstance(documents[name], dict):
            raise ValueError("Scoring source documents must be objects")
    summary, report, plan = (documents[name] for name in ("original_summary", "original_report", "original_plan"))
    plan = validate_plan(plan)
    if (report.get("schema") != "math-gauge.benchmark-score/v1"
            or report.get("plan_sha256") != plan["plan_sha256"]
            or report.get("model_label") != plan["model_label"]):
        raise ValueError("Scoring original report and frozen plan identities differ")
    if summary.get("schema") == "math-gauge.public-composite-score/v1":
        scope = "public"
        if summary.get("plan_sha256") != plan["plan_sha256"]:
            raise ValueError("Scoring public summary binds another plan")
    elif summary.get("schema") == "math-gauge.combined-aggregate-only/v1":
        scope = "combined"
        if summary.get("source_score_sha256") != expected_sha256["original_report"]:
            raise ValueError("Scoring aggregate binds another report")
    else:
        raise ValueError("Unsupported original scoring projection")
    if (summary.get("coverage", {}).get("slots_planned") != (42 if scope == "public" else 45)
            or summary.get("profile", {}).get("version") != "0.6.0"
            or plan["profile"]["data"].get("version") != "0.6.0"):
        raise ValueError("Scoring retains the original v0.6.0 42/45-slot plan")
    private = {item["case_id"]: f"Private-{index:02d}" for index, item in enumerate(
        (item for item in plan["case_index"] if item.get("source_visibility") == "private"), 1)}
    projection = public_score_projection(report, plan, private_aliases=private)
    if summary.get("profile") != projection["profile"] or summary.get("coverage") != projection["coverage"]:
        raise ValueError("Scoring original profile or fixed coverage changed")
    rows = [dict(row, group_diagnostic=row.get("group_diagnostic") or {}) for row in report["evidence"]]
    inputs = {"plan": plan, "model_label": plan["model_label"], "slots": rows}
    baseline = _score_inputs(inputs)
    _compare_frozen_metrics(summary["metrics"], report["metrics"])
    _compare_frozen_metrics(summary["metrics"], baseline["metrics"])
    return documents, plan, inputs, baseline, scope


def _lean_formalization_breakdown(plan, inputs, report, substitutions):
    """Public counts and family values come from the same unrounded score inputs."""
    rows = {row["slot_id"]: row for row in inputs["slots"]}
    cases = []
    public_ids = set()
    for case in plan["case_index"]:
        if case.get("component") != "lean-formalization" or case.get("source_visibility") == "private":
            continue
        cid = case["case_id"]
        value = substitutions.get(cid + ":A1", _interval(rows.get(cid + ":A1", {}).get("completion")))
        total = case["total_weight"]
        count = value[2] * total if value[2] is not None else None
        # Frozen completion fractions may have been serialized as decimal floats.
        # Recover an integer count only when its normalized score reproduces that
        # original fraction to the report's ten-place publication precision.
        if count is not None and count.denominator != 1:
            nearest = round(count)
            count = Fraction(nearest) if _percent(Fraction(nearest, total)) == _percent(value[2]) else None
        cases.append({"case_id": cid, "family_id": case["family_id"],
            "complete_count": int(count) if count is not None else None, "total": total,
            "percent": _percent(value[2])})
        public_ids.add(cid)
    families = {family: {"case_ids": list(value["case_ids"]), "variant_count": value["variant_count"],
                         "percent": value["completion"]["exact"]}
                for family, value in report.get("component_families", {}).get("lean-formalization", {}).items()
                if set(value["case_ids"]) <= public_ids}
    return {"cases": cases, "families": families}


def source_qualified_engineering_score(sources, *, expected_sha256, workspace_root, model_key):
    """Admit a source-bound, compiled engineering answer as a mathematical view.

    This reads the existing peer review, first-source manifest, root adjudication
    and trusted kernel report. It neither compiles nor changes execution evidence.
    """
    import copy
    import json
    import re
    from .catalog import digest_bytes

    required = {"original_summary", "original_report", "original_plan", "engineering_review",
                "kernel_report", "source_manifest", "root_adjudication"}
    documents, plan, inputs, baseline, scope = _frozen_scoring_baseline(
        sources, expected_sha256, required=required)
    summary, peer, kernel, manifest, root = (documents[name] for name in (
        "original_summary", "engineering_review", "kernel_report", "source_manifest", "root_adjudication"))
    cid, sid = "MG-C003", "MG-C003:A1"
    case = next((case for case in plan["case_index"] if case["case_id"] == cid), {})
    stages = case.get("stages", [])
    ids = {stage["stage_id"] for stage in stages}
    original = next((row for row in inputs["slots"] if row["slot_id"] == sid), {})
    if (case.get("version") != "0.1.1" or case.get("family_id") != "oet-volume1-chapter03"
            or case.get("component") != "lean-formalization" or len(ids) != 92 or len(stages) != 92
            or any(type(stage.get("points")) is not int or stage["points"] != 1 for stage in stages)):
        raise ValueError("Engineering scoring requires the frozen equal-weight 92-obligation C003 contract")
    assessment = root.get("assessment", {}).get(model_key, {})
    snapshot = peer.get("snapshot", {})
    binding = kernel.get("reliability_binding", {})
    if (not isinstance(model_key, str) or not model_key
            or peer.get("schema") != "math-gauge.source-bound-forced-snapshot-formalization-peer/v1"
            or peer.get("case_id") != cid or peer.get("case_version") != "0.1.1" or peer.get("slot_id") != sid
            or peer.get("model_label") != model_key or peer.get("reviewer_kind") != "ai"
            or peer.get("human_review") != "pending"
            or peer.get("old_inline_response_sha256") != original.get("response_sha256")
            or not original.get("response_sha256")
            or root.get("schema") != "math-gauge.paired-first-workspace-root-adjudication/v0.1.0"
            or root.get("case_id") != cid or root.get("reviewer_kind") != "ai"
            or root.get("human_review") != "pending" or root.get("formal_comparison_eligible") is not False
            or assessment.get("semantic_review", {}).get("sha256") != expected_sha256["engineering_review"]
            or assessment.get("compiler_diagnostic", {}).get("kernel_report_sha256") != expected_sha256["kernel_report"]
            or snapshot.get("manifest", {}).get("sha256") != expected_sha256["source_manifest"]
            or binding.get("peer_static_review", {}).get("sha256") != expected_sha256["engineering_review"]
            or binding.get("old_inline_raw_sha256") != original["response_sha256"]
            or binding.get("first_actual_snapshot_only") is not True
            or binding.get("original_project_modified") is not False):
        raise ValueError("Engineering scoring review, model and first-source bindings disagree")
    if (kernel.get("schema") != "math-gauge.candidate-lean/v1" or kernel.get("status") != "passed"
            or kernel.get("case_id") != cid or kernel.get("source_repaired") is not False
            or kernel.get("group_contract_sha256") != case.get("group_contract_sha256")
            or kernel.get("alignment_inventory_validated") is not True
            or kernel.get("audit", {}).get("summary", {}).get("passed") is not True
            or kernel["audit"]["summary"].get("unexpected_axioms") != []
            or kernel.get("semantic_alignment_inferred") is not False
            or kernel.get("human_approval") is not False):
        raise ValueError("Engineering scoring requires the unchanged trusted kernel and axiom result")
    modules = kernel.get("modules", [])
    if (not isinstance(modules, list) or not modules
            or any(type(row.get("exit_code")) is not int or row["exit_code"] != 0
                   or row.get("timeout") is not False for row in modules)):
        raise ValueError("Engineering scoring compiled module result is incomplete")
    workspace = Path(workspace_root).resolve()
    if (manifest.get("tree_sha256") != snapshot.get("tree_sha256")
            or manifest.get("tree_sha256") != assessment.get("source_tree_sha256")
            or binding.get("snapshot", {}).get("tree_sha256") != manifest.get("tree_sha256")):
        raise ValueError("Engineering scoring first-source tree identities disagree")
    files = manifest.get("files", {})
    if not isinstance(files, dict) or not {"Main.lean", "alignment.json"} <= set(files):
        raise ValueError("Engineering scoring requires the full source manifest")
    selected = kernel.get("files_sha256", {})
    if not isinstance(selected, dict) or "Main.lean" not in selected:
        raise ValueError("Engineering scoring requires the compiled Main source closure")
    source_text, paths = {}, {}
    for name, record in files.items():
        if not isinstance(name, str) or not isinstance(record, dict):
            raise ValueError("Engineering scoring manifest requires named file records")
        raw_path = workspace / name
        path = raw_path.resolve()
        if (not path.is_relative_to(workspace) or not path.is_file() or raw_path.is_symlink()
                or any(parent.is_symlink() for parent in raw_path.parents if parent.is_relative_to(workspace))):
            raise ValueError("Engineering scoring manifest contains an unsafe source path")
        data = path.read_bytes()
        if digest_bytes(data) != record.get("sha256") or len(data) != record.get("bytes"):
            raise ValueError("Engineering scoring actual source bytes changed")
        if name in selected:
            if selected[name] != record["sha256"]:
                raise ValueError("Engineering scoring compiled source differs from the first manifest")
            source_text[name], paths[name] = data.decode("utf-8").splitlines(), path
    if not set(selected) <= set(files):
        raise ValueError("Engineering scoring compiled source closure changed")
    compiled = {row.get("module"): row.get("source_sha256") for row in modules}
    if any(compiled.get(name[:-5].replace("/", ".")) != sha for name, sha in selected.items()):
        raise ValueError("Engineering scoring selected source lacks its matching compilation")
    main_hash, alignment_hash = files["Main.lean"]["sha256"], files["alignment.json"]["sha256"]
    if (snapshot.get("entry", {}).get("sha256") != main_hash
            or snapshot.get("workspace_alignment", {}).get("sha256") != alignment_hash
            or kernel.get("alignment_manifest_sha256") != alignment_hash
            or binding.get("selected_main_sha256") != main_hash
            or binding.get("original_alignment_sha256") != alignment_hash):
        raise ValueError("Engineering scoring Main or alignment source bindings changed")
    alignment = json.loads((workspace / "alignment.json").read_bytes())
    if alignment != kernel.get("alignment_manifest") or alignment.get("case_id") != cid or alignment.get("version") != "0.1.1":
        raise ValueError("Engineering scoring alignment inventory differs from the compiled source")
    contracts = [row for row in peer.get("frozen_case_files", [])
                 if row.get("sha256") == case.get("group_contract_sha256")]
    if len(contracts) != 1:
        raise ValueError("Engineering scoring requires its bound full case contract")
    contract_bytes = Path(contracts[0]["path"]).read_bytes()
    if digest_bytes(contract_bytes) != case["group_contract_sha256"]:
        raise ValueError("Engineering scoring frozen case contract changed")
    full_contract = json.loads(contract_bytes)
    allowed_background = {stage["id"] for stage in full_contract.get("stages", [])
                          if stage.get("allow_background_declarations") is True}
    background = kernel.get("input_files_sha256", {})
    for record in peer.get("candidate_input_manifest", []):
        name = record.get("target")
        if name in background:
            path = Path(record["path"]).resolve()
            data = path.read_bytes()
            if record.get("sha256") != background[name] or digest_bytes(data) != background[name]:
                raise ValueError("Engineering scoring frozen background source changed")
            source_text[name], paths[name] = data.decode("utf-8").splitlines(), path
    if not set(background) <= set(paths):
        raise ValueError("Engineering scoring frozen background closure is incomplete")
    audited = {(row.get("module"), row.get("name")) for row in kernel["audit"].get("declarations", [])}
    obligations = peer.get("rows", [])
    if (not isinstance(obligations, list) or len(obligations) != 92
            or any(not isinstance(row.get("stage_id"), str) for row in obligations)
            or {row["stage_id"] for row in obligations} != ids):
        raise ValueError("Engineering scoring requires exactly 92 unique reviewed obligations")
    passed, incomplete = [], []
    for row in obligations:
        decision = row.get("decision")
        if (decision not in {"pass", "partial", "fail"} or type(row.get("points_awarded")) is not int
                or row["points_awarded"] != int(decision == "pass")
                or type(row.get("max_points")) is not int or row["max_points"] != 1):
            raise ValueError("Engineering scoring mathematical decisions and frozen weights disagree")
        (passed if decision == "pass" else incomplete).append(row["stage_id"])
        if decision != "pass":
            continue
        declarations = row.get("declarations", [])
        evidence = row.get("source_evidence", [])
        if not declarations or not evidence:
            raise ValueError("Engineering scoring pass lacks declaration source evidence")
        for declaration in declarations:
            name, file = declaration.get("name"), declaration.get("file")
            if file not in source_text or not isinstance(name, str) or (file[:-5].replace("/", "."), name) not in audited:
                raise ValueError("Engineering scoring declaration lacks a bound kernel audit")
            matches = [item for item in evidence if item.get("name") == name
                       and Path(item.get("file", "")).resolve() == paths[file]]
            if not matches:
                raise ValueError("Engineering scoring declaration source range is unbound")
            for item in matches:
                if (file in background and row["stage_id"] in allowed_background
                        and item.get("frozen_input_explicitly_allowed") is True
                        and item.get("source_sha256") == background[file]):
                    continue
                start, end = item.get("start_line"), item.get("end_line")
                if (type(start) is not int or type(end) is not int or not 1 <= start <= end <= len(source_text[file])
                        or not re.search(r"(?<![\w'])" + re.escape(name.rsplit(".", 1)[-1]) + r"(?![\w'])",
                                         "\n".join(source_text[file][start - 1:end]))):
                    raise ValueError("Engineering scoring declaration source range changed")
    counts = {"pass": len(passed), "incomplete": len(incomplete), "total": 92}
    if (assessment.get("semantic_obligations") is None
            or any(assessment["semantic_obligations"].get(key) != value for key, value in counts.items())
            or peer.get("completed_weight_semantic") != len(passed) or peer.get("total_weight") != 92):
        raise ValueError("Engineering scoring root and detailed pass sets disagree")
    completion = Fraction(len(passed), 92)
    substitutions = {sid: (completion, completion, completion)}
    derived = _score_inputs(inputs, mathematical_substitutions=substitutions)
    metrics = copy.deepcopy(summary["metrics"])
    for name in ("lean-formalization", "core", "overall"):
        for field in ("exact", "lower", "upper", "complete", "coverage"):
            metrics[name][field] = copy.deepcopy(derived["metrics"][name][field])
        metrics[name].update(formal_comparison_eligible=False, mathematical_source_substitution=True)
    return {"schema": "math-gauge.source-qualified-engineering-score/v1",
        "id": f"{model_key}-v06-sealed-engineering-math-{scope}/v1", "scope": scope,
        "model_key": model_key, "model_label": plan["model_label"],
        "status": "source_bound_ai_engineering_review", "human_review": "pending",
        "scoring_owner": "math_gauge.scoring", "scoring_view_version": "c003-sealed-engineering/v1",
        "scoring_implementation_sha256": digest_bytes(Path(__file__).read_bytes()),
        "score_units": {"metrics": "percent", "completion": "fraction"},
        "profile": copy.deepcopy(summary["profile"]), "metrics": metrics,
        "coverage": copy.deepcopy(summary["coverage"]),
        "source_bindings": {name + "_sha256": expected_sha256[name] for name in sorted(sources)},
        "original_score": {"metrics": copy.deepcopy(summary["metrics"]), "standard_evidence_rewritten": False},
        "mathematical_substitution": {"case_id": cid, "case_version": "0.1.1", "original_weight_slot": sid,
            "original_A1_replaced": False, "complete": len(passed), "not_complete": len(incomplete), "total": 92,
            "pass_ids": sorted(passed), "not_complete_ids": sorted(incomplete),
            "completion_fraction": {"numerator": len(passed), "denominator": 92},
            "selected_source_sha256": copy.deepcopy(selected), "sealed_manifest_sha256": expected_sha256["source_manifest"],
            "sealed_tree_sha256": manifest["tree_sha256"], "kernel_report_sha256": expected_sha256["kernel_report"],
            "original_response_sha256": original["response_sha256"]},
        "lean_formalization_breakdown": _lean_formalization_breakdown(plan, inputs, derived, substitutions),
        "formal_comparison_eligible": False, "new_candidate_calls": 0}


def alignment_augmented_score(sources, *, expected_sha256):
    """Recompute an explicitly bound development view from full frozen inputs.

    A separately qualified engineering snapshot may supply capability completion.
    Alignment followups never replace an A1.
    Review judgments and their evidence are evaluator inputs, not solver data.
    """
    import copy
    from .catalog import digest_bytes

    required = {"original_summary", "original_report", "original_plan", "alignment_review", "policy"}
    documents, plan, inputs, baseline, scope = _frozen_scoring_baseline(
        sources, expected_sha256, required=required, optional={"source_qualified_score"})
    summary, review, policy = (documents[name] for name in ("original_summary", "alignment_review", "policy"))
    policy = _alignment_policy(policy)
    if policy["version"] == "0.4.0":
        raise ValueError("Method0.4.0 requires score_record_inputs with all four sealed engineering reviews")
    rows = inputs["slots"]
    if (review.get("model_label") != plan["model_label"]
            or review.get("policy_sha256") != expected_sha256["policy"]):
        raise ValueError("Alignment scoring report, review, policy and plan identities differ")
    case = next((item for item in plan["case_index"] if item["case_id"] == policy["case_id"]), {})
    stages = case.get("stages", [])
    ids = set(policy["obligation_ids"])
    if (case.get("version") != policy["case_version"] or case.get("component") != "lean-formalization"
            or case.get("family_id") != "oet-volume1-chapter03" or case.get("total_weight") != 92
            or len(stages) != 92 or {item["stage_id"] for item in stages} != ids
            or any(type(item.get("points")) is not int or item["points"] != 1 for item in stages)
            or policy.get("case_contract_sha256", case.get("group_contract_sha256"))
            != case.get("group_contract_sha256")):
        raise ValueError("Alignment scoring requires the original equal-weight 92-obligation contract")
    selected = documents.get("source_qualified_score", summary)
    substitutions = {}
    if "source_qualified_score" in documents:
        substitution = selected.get("mathematical_substitution", {})
        bindings = selected.get("source_bindings", {})
        passed, incomplete = substitution.get("pass_ids", []), substitution.get("not_complete_ids", [])
        original = next((row for row in rows if row["slot_id"] == "MG-C003:A1"), {})
        if (not isinstance(passed, list) or not isinstance(incomplete, list)
                or any(not isinstance(sid, str) for sid in passed + incomplete)):
            raise ValueError("Alignment scoring selected capability requires exact obligation inventories")
        engineering = selected.get("schema") == "math-gauge.source-qualified-engineering-score/v1"
        legacy = (selected.get("schema") == "math-gauge.source-qualified-score/v1"
                  and selected.get("scoring_view_version") == "c003-sealed-extension/v1")
        if ((not engineering and not legacy) or selected.get("scope") != scope
                or selected.get("formal_comparison_eligible") is not False
                or selected.get("human_review") != "pending"
                or selected.get("profile") != summary["profile"] or selected.get("coverage") != summary["coverage"]
                or any(bindings.get(name + "_sha256") != expected_sha256[name]
                       for name in ("original_summary", "original_report", "original_plan"))
                or substitution.get("case_id") != "MG-C003" or substitution.get("case_version") != "0.1.1"
                or substitution.get("original_weight_slot") != "MG-C003:A1"
                or substitution.get("original_A1_replaced") is not False
                or type(substitution.get("complete")) is not int or substitution["complete"] != len(passed)
                or type(substitution.get("not_complete")) is not int or substitution["not_complete"] != len(incomplete)
                or substitution.get("total") != 92 or len(set(passed)) != len(passed)
                or len(set(incomplete)) != len(incomplete)
                or set(passed) & set(incomplete) or set(passed) | set(incomplete) != ids
                or legacy and (len(passed) != 74 or _interval(original.get("completion")) != UNKNOWN
                               or original.get("strict_pass") is not None)
                or engineering and (policy["version"] not in {"0.2.0", "0.3.0", "0.4.0"}
                    or selected.get("scoring_view_version") != "c003-sealed-engineering/v1"
                    or selected.get("model_label") != plan["model_label"]
                    or substitution.get("original_response_sha256") != original.get("response_sha256"))):
            raise ValueError("Alignment scoring selected capability source differs from its admitted engineering source; "
                             "the legacy admitted Gemini 74/92 view remains separately bound")
        value = Fraction(len(passed), 92)
        substitutions["MG-C003:A1"] = value, value, value
        baseline = _score_inputs(inputs, mathematical_substitutions=substitutions)
        _compare_frozen_metrics(selected["metrics"], baseline["metrics"])
    trajectory, interval = _alignment_trajectory(review, policy)
    derived = _score_inputs(inputs, mathematical_substitutions=substitutions,
                            neutral_alignment=(interval, policy))
    metrics = copy.deepcopy(selected["metrics"])
    changed = (("core",) if policy["version"] in {"0.3.0", "0.4.0"} else ()) + (
        "neutral", "overall", "neutral_written", "lean_alignment_selfcheck")
    for name in changed:
        metrics[name] = {field: copy.deepcopy(derived["metrics"][name][field])
                        for field in ("exact", "lower", "upper", "complete", "coverage", "formal_comparison_eligible")}
    profile = copy.deepcopy(summary["profile"])
    if policy["version"] in {"0.3.0", "0.4.0"}:
        for component in profile["components"]:
            component["weight"] = policy["capability_component_weights"][scope][component["id"]]
        profile["overall_weights"] = copy.deepcopy(policy["overall_weights"])
    return {"schema": "math-gauge.alignment-augmented-score/v1", "scope": scope,
        "id": f"alignment-selfcheck-{scope}/{policy['version']}",
        "model_label": plan["model_label"], "status": "post_observation_ai_review_human_pending",
        "score_units": {"metrics": "percent", "completion": "fraction"},
        "scoring_owner": "math_gauge.scoring", "scoring_view_version": f"alignment-selfcheck/{policy['version']}",
        "scoring_implementation_sha256": digest_bytes(Path(__file__).read_bytes()),
        "profile": profile, "metrics": metrics,
        "coverage": copy.deepcopy(summary["coverage"]),
        "policy": {"schema": policy["schema"], "version": policy["version"],
            "sha256": expected_sha256["policy"],
            "neutral_group_weights": copy.deepcopy(policy["neutral_group_weights"]),
            "overall_weights": copy.deepcopy(policy["overall_weights"]),
            **({"capability_component_weights": copy.deepcopy(policy["capability_component_weights"])}
               if policy["version"] in {"0.3.0", "0.4.0"} else {})},
        **({"aggregation_profile_binding": {
            "original_profile_sha256": plan["profile"]["sha256"],
            "weight_policy_sha256": expected_sha256["policy"]}}
           if policy["version"] in {"0.3.0", "0.4.0"} else {}),
        "source_bindings": {name + "_sha256": expected_sha256[name] for name in sorted(sources)},
        "baseline_score": {"schema": selected["schema"], "id": selected.get("id"),
            "sha256": expected_sha256.get("source_qualified_score", expected_sha256["original_summary"]),
            "metrics": copy.deepcopy(selected["metrics"])},
        "original_score": {"sha256": expected_sha256["original_summary"],
            "metrics": copy.deepcopy(summary["metrics"]), "standard_evidence_rewritten": False},
        "alignment_selfcheck": trajectory,
        **({"lean_formalization_breakdown": _lean_formalization_breakdown(plan, inputs, baseline, substitutions)}
           if policy["version"] in {"0.2.0", "0.3.0", "0.4.0"} else {}),
        "alignment_study_coverage": {"planned_rounds": 3,
            "records_present": sum(row.get("snapshot") is not None for row in review["rounds"]),
            "adjudicated_rounds": trajectory["metric"]["coverage"]["adjudicated"],
            "mathematical_families": 1, "standard_slots_added": 0, "fresh_A1_slots_added": 0,
            "formal_eligible_slots_added": 0},
        "capability_source": ("selected_sealed_engineering" if substitutions and engineering else
                              "selected_sealed_extension_74_of_92" if substitutions else "original_A1"),
        "source_conditions": {"classification": "post-observation mixed-condition development",
            "standard_budgets_and_parameters_rewritten": False,
            "standard_composition": copy.deepcopy(summary.get("composition"))},
        "formal_comparison_eligible": False, "human_review": "pending", "new_candidate_calls": 0,
        "notice": "The four written neutral families retain their internal average. Three Lean rounds form one alignment family. "
                  + ("The versioned policy supplies the aggregation weights; frozen execution plans remain unchanged. "
                     if policy["version"] in {"0.3.0", "0.4.0"} else
                     "The versioned policy combines the two neutral groups inside the unchanged 75/5/10/10 total. ")
                  +
                  "Original execution, 42/45-slot coverage and A1 evidence remain stored; this view adds no candidate calls or formal qualification."}


def formalization_substitutions(inputs, review):
    """Aggregate all four source-bound engineering judgments, retaining unknowns.

    The record validator binds actual files and compiler evidence. This pure
    boundary checks mathematical inventories and original response identities;
    a candidate's self-reported table never supplies the completion judgments.
    """
    required = {"LCH01": 8, "LCH02": 20, "HCH02": 40, "MG-C003": 92}
    if (not isinstance(review, dict)
            or review.get("schema") != "math-gauge.formalization-engineering-review/v1"
            or review.get("model_label") != inputs.get("model_label")
            or review.get("reviewer_kind") != "ai" or review.get("human_review") != "pending"
            or review.get("formal_comparison_eligible") is not False):
        raise ValueError("Unsupported sealed formalization review identity")
    cases = review.get("cases")
    if (not isinstance(cases, list) or len(cases) != 4
            or {row.get("case_id") for row in cases} != set(required)):
        raise ValueError("Engineering review must cover all four formalization cases")
    plan = validate_plan(inputs["plan"])
    index = {case["case_id"]: case for case in plan["case_index"]}
    rows = {row["slot_id"]: row for row in inputs.get("slots", [])}
    substitutions = {}
    for case in cases:
        cid, total = case["case_id"], required[case["case_id"]]
        frozen, sid = index.get(cid, {}), cid + ":A1"
        targets = {stage["stage_id"] for stage in frozen.get("stages", [])}
        items = case.get("obligations")
        if (frozen.get("component") != "lean-formalization" or frozen.get("total_weight") != total
                or len(targets) != total or case.get("case_version") != frozen.get("version")
                or case.get("slot_id") != sid or case.get("source_kind") != "sealed_workspace"
                or case.get("original_response_sha256") != rows.get(sid, {}).get("response_sha256")
                or not isinstance(items, list) or len(items) != total
                or {item.get("id") for item in items} != targets):
            raise ValueError("Engineering review differs from the frozen case, response or obligations")
        sources = case.get("compiled_sources", {})
        if not isinstance(sources, dict) or not sources:
            raise ValueError("Engineering review needs exact compiled source hashes")
        for name, value in sources.items():
            if not isinstance(name, str) or not name.endswith(".lean"):
                raise ValueError("Engineering source must name a Lean file")
            _alignment_hash(value)
        values = []
        for item in items:
            complete = item.get("complete")
            values.append(_boolean(complete))
            if complete is True and (case.get("kernel_status") != "passed"
                                     or not isinstance(item.get("declarations"), list)
                                     or not item["declarations"]):
                raise ValueError("A completed obligation needs verified declarations and kernel evidence")
        substitutions[sid] = _average(values)
    return substitutions


def score_record_inputs(inputs, review, policy, *, formalization_review=None):
    """Aggregate current archived judgments without keeping superseded score views.

    The immutable execution plan and original slot judgments retain their source
    identities. The separately selected engineering baseline and followups are
    explicit AI review inputs, never silently substituted into the raw answers.
    """
    inputs = dict(inputs, slots=[dict(row, group_diagnostic=row.get("group_diagnostic") or {})
                                 for row in inputs.get("slots", [])])
    policy = _alignment_policy(policy)
    if policy["version"] not in {"0.3.0", "0.4.0"} or review.get("scoring_version") != policy["version"]:
        raise ValueError("Current result records require their selected scoring policy")
    if review.get("model_label") != inputs.get("model_label"):
        raise ValueError("Record review and execution model identities differ")
    baseline = review.get("baseline", {})
    ids = set(policy["obligation_ids"])
    _alignment_snapshot(baseline, ids, review.get("primary_source_kind"))
    if baseline.get("source_kind") != "sealed_workspace":
        raise ValueError("Current engineering baseline must identify its sealed source")
    baseline_value = _average([_boolean(item["complete"]) for item in baseline["obligations"]])
    substitutions = {"MG-C003:A1": baseline_value}
    if policy["version"] == "0.4.0":
        substitutions = formalization_substitutions(inputs, formalization_review)
        chapter = next(case for case in formalization_review["cases"] if case["case_id"] == "MG-C003")
        if (substitutions["MG-C003:A1"] != baseline_value
                or {item["id"]: item["complete"] for item in chapter["obligations"]}
                != {item["id"]: item["complete"] for item in baseline["obligations"]}
                or chapter.get("source_sha256") != baseline.get("source_sha256")):
            raise ValueError("C003 engineering source differs from the alignment-study parent")
    elif formalization_review is not None:
        raise ValueError("The prior scoring method does not select four engineering sources")
    steps, interval = _alignment_trajectory(review, policy)
    result = _score_inputs(inputs, mathematical_substitutions=substitutions,
                           neutral_alignment=(interval, policy))
    return {"metrics": result["metrics"], "alignment_selfcheck": steps,
            "lean_formalization_breakdown": _lean_formalization_breakdown(
                inputs["plan"], inputs, result, substitutions),
            "formal_comparison_eligible": False, "human_review": "pending"}



def _assessment_metric(interval, *, unit, planned, adjudicated):
    """Percent/point bounds, including signed selfcheck credit, without admission promotion."""
    return {"exact": _percent(interval[2]), "lower": _bound(interval[0], lower=True),
            "upper": _bound(interval[1], lower=False), "complete": interval[2] is not None,
            "coverage": {"unit": unit, "planned": planned, "adjudicated": adjudicated,
                         "unknown": planned - adjudicated}, "formal_comparison_eligible": False}


def _all_requirements(values):
    if any(value is False for value in values):
        return False
    return True if all(value is True for value in values) else None


def strict_alignment_trajectory(review, source_policy):
    """Judge a whole repair trajectory, not the average of three round passes."""
    summary, _ = _alignment_trajectory(review, source_policy)
    supplied = {row["round"]: row for row in review["rounds"]}
    gates = []
    for row in summary["rounds"]:
        diagnosis = supplied.get(row["round"], {}).get("diagnosis") or {}
        no_false = None if row["major_false_complete"] is None else not row["major_false_complete"]
        no_regression = None if row["regressed"] is None else row["regressed"] == 0
        accurate = diagnosis.get("accurate")
        if accurate is True:
            accurate = (diagnosis.get("global_points") == 10 and diagnosis.get("localization_points") == 20)
        gates.append({"round": row["round"], "delivery_verified": row["delivery_verified"],
                      "diagnosis_accurate": accurate, "no_false_complete": no_false,
                      "no_regression": no_regression})
    last = summary["last_completion"]
    final = False if last["not_complete"] else True if last["unknown_obligations"] == 0 else None
    passed = _all_requirements([final, *(g[k] for g in gates for k in
                               ("delivery_verified", "diagnosis_accurate", "no_false_complete", "no_regression"))])
    return {"strict_pass": passed, "final_all_verified": final, "rounds": gates,
            "assessment_units": 1, "initial_answer_replaced": False}


def validate_strict_assessment_policy(policy):
    required = {"schema": "math-gauge.strict-scoring-policy/v2", "version": "0.2.0",
        "benchmark_version": "0.6.0", "score_mode": "strict", "primary_metric": "earned",
        "initial_attempt_labels": ["A1"], "task_credit": "all_required_objectives_correct_or_zero",
        "numeric_pass_threshold": None, "include_alignment_trajectory": True,
        "trajectory_credit": "all_required_three_round_trajectory_conditions_or_zero",
        "family_aggregation": "same_as_partial", "component_weights": "same_as_partial",
        "construction_policy": "fixed_reserved_weight_unknown_full_score", "followups_replace_A1": False,
        "attempt_conditions": ["single_attempt", "nonlogical_retry_3"],
        "human_review": "pending", "formal_comparison_eligible": False}
    if not isinstance(policy, dict) or any(policy.get(k) != v for k, v in required.items()):
        raise ValueError("Unsupported strict task-and-trajectory scoring policy")
    return policy


def score_assessment_inputs(inputs, assessment_policy, strict_policy, *, mode="partial",
                            mathematical_substitutions=None, alignment_summary=None,
                            strict_trajectory=None, theorem_extension_inputs=None):
    """Aggregate a fixed hierarchy; unbuilt research stays unknown, never renormalized."""
    policy = validate_assessment_policy(assessment_policy)
    validate_strict_assessment_policy(strict_policy)
    if mode not in {"partial", "strict"}:
        raise ValueError("Unknown assessment score mode")
    plan = validate_plan(inputs["plan"])
    if inputs.get("model_label") != plan["model_label"]:
        raise ValueError("Assessment model differs from its frozen source")
    source_index = {case["case_id"]: case for case in plan["case_index"]}
    selection = policy.get("case_selection")
    index = selected_current_cases(source_index, selection)
    planned = {row["slot_id"]: row for row in plan["slots"]}
    rows = {}
    for row in inputs.get("slots", []):
        sid = row.get("slot_id")
        if sid in rows or sid not in planned or row.get("case_id") != planned[sid]["case_id"]:
            raise ValueError("Assessment inputs repeat or invent a source slot")
        rows[sid] = row
    research_levels = {}
    if theorem_extension_inputs is not None:
        if policy["version"] != "0.6.0":
            raise ValueError("Research evidence cannot alter the pre-research scoring method")
        extra = validate_extension_inputs(theorem_extension_inputs, policy["theorem_extension"])
        if extra.get("model_label") != inputs["model_label"]:
            raise ValueError("Theorem-extension evidence belongs to a different model")
        for case in extra["case_index"]:
            cid = case["case_id"]
            if cid in index and index[cid]["component"] != "theorem-extension":
                raise ValueError("Research evidence cannot replace an existing mathematical task")
            if (cid in index and index[cid].get("group_contract_sha256") is not None
                    and index[cid]["group_contract_sha256"] != case.get("contract_sha256")):
                raise ValueError("Research evidence binds a different frozen mathematical contract")
            index[cid] = case
        for row in extra["slots"]:
            sid = row["slot_id"]
            if (sid in rows and rows[sid].get("response_sha256") !=
                    (None if row["response"] is None else row["response"]["sha256"])):
                raise ValueError("Research evidence must not replace an existing frozen answer")
            if sid in rows and rows[sid].get("strict_pass") is not None and row["status"] == "not_run":
                raise ValueError("Research evidence cannot hide an existing adjudicated source answer")
            level, baseline = row["research_R"], row["baseline_B"]
            deduction = (0 if row["status"] == "delivery_failed" else None if baseline is None else
                         policy["theorem_extension"]["baseline_penalty_points"][str(baseline)])
            # Keep the ordinary source completion in [0,1]. The separately
            # audited baseline deduction is applied below in exact arithmetic.
            value = None if level is None else Fraction(level, 3)
            rows[sid] = {"completion": {"lower": 0 if value is None else float(value),
                "upper": 1 if value is None else float(value), "exact": None if value is None else float(value)},
                "strict_pass": None if value is None else baseline == 2 and level == 3,
                "response_sha256": None if row["response"] is None else row["response"]["sha256"],
                "review_sha256": None if row["review"] is None else row["review"]["sha256"]}
            research_levels[sid] = {"baseline_B": baseline, "research_R": level,
                "baseline_penalty_points": deduction, "research_maximum_points": 3,
                "baseline_is_research_credit": False, "answer_attempt": "A1"}
    substitutions = mathematical_substitutions or {}
    by_source = {source: child for child in policy["subcategories"] for source in child["source_components"]}
    families = {child["id"]: {} for child in policy["subcategories"]}
    tasks = []
    for cid, case in index.items():
        child = by_source.get(case["component"])
        if child is None:
            raise ValueError("A source task has no current assessment category")
        sid, row = cid + ":A1", rows.get(cid + ":A1", {})
        value = substitutions.get(sid, _interval(row.get("completion")))
        if sid in research_levels:
            research = research_levels[sid]
            value = ((Fraction(-2, 3), Fraction(1), None) if research["research_R"] is None else
                     (Fraction(research["research_R"] - research["baseline_penalty_points"], 3),) * 3)
        if sid in substitutions:
            passed = True if value[0] == 1 else False if value[1] < 1 else None
            source = "selected_sealed_engineering"
        else:
            passed = row.get("strict_pass")
            if case["component"] == "theorem-extension" and sid not in research_levels:
                # Generic proof completion alone does not adjudicate the
                # separately required original-task baseline and research tier.
                value, passed = (Fraction(-2, 3), Fraction(1), None), None
            _boolean(passed)
            if passed is True and value != (1, 1, 1):
                raise ValueError("Strict pass contradicts the source-bound completed task")
            source = "source_bound_original_review"
        interval = _boolean(passed) if mode == "strict" else value
        family = (assessment_family(case, source_index, selection) if selection is not None else
                  case["parent_family_id"] if child["aggregation"] == "parent_family" else case["family_id"])
        families[child["id"]].setdefault(family, []).append(interval)
        tasks.append({"case_id": cid, "slot_id": sid, "subcategory": child["id"], "family_id": family,
                      "strict_pass": passed, "judgment_source": source,
                      "completion": {"lower": float(value[0]), "upper": float(value[1]),
                                     "exact": None if value[2] is None else float(value[2])},
                      "response_sha256": row.get("response_sha256"), "review_sha256": row.get("review_sha256"),
                      **({"research": research_levels[sid]} if sid in research_levels else {})})
    metrics, intervals, contributions, confirmed = {}, {}, {}, {}
    for child in policy["subcategories"]:
        ident, count = child["id"], child["families"]
        if child["status"] == "under_construction":
            value, adjudicated = UNKNOWN, 0
            confirmed[ident] = Fraction(0)
        elif child["aggregation"] == "trajectory":
            if mode == "strict":
                value = _boolean((strict_trajectory or {}).get("strict_pass"))
            elif alignment_summary is None:
                value = Fraction(-1, 5), Fraction(1), None
            else:
                metric = alignment_summary["metric"]
                value = tuple(None if metric[k] is None else Fraction(str(metric[k])) / 100
                              for k in ("lower", "upper", "exact"))
            adjudicated = int(value[2] is not None)
            confirmed[ident] = value[2] if value[2] is not None else Fraction(0)
        else:
            values = [_average(items) for items in families[ident].values()]
            if len(values) > count:
                raise ValueError("Assessment source exceeds the frozen family denominator")
            missing = ((Fraction(-2, 3), Fraction(1), None)
                       if ident == "theorem-extension" and mode == "partial" else UNKNOWN)
            values += [missing] * (count - len(values))
            value, adjudicated = _average(values), sum(item[2] is not None for item in values)
            confirmed[ident] = sum((_average([(v[2] or Fraction(0),) * 3 for v in items])[2]
                for items in families[ident].values()), Fraction(0)) / count
        intervals[ident] = value
        metrics[ident] = _assessment_metric(value, unit=child["aggregation"], planned=count,
                                           adjudicated=adjudicated)
        contribution = tuple(None if x is None else x * Fraction(child["weight"], 100) for x in value)
        contributions[ident] = _assessment_metric(contribution, unit="points in full benchmark",
                                                 planned=count, adjudicated=adjudicated)
        if policy["version"] == "0.6.0":
            metrics[ident]["confirmed"] = float(confirmed[ident] * 100)
            contributions[ident]["confirmed"] = float(confirmed[ident] * child["weight"])
    for group in policy["groups"]:
        children = [child for child in policy["subcategories"] if child["id"] in group["children"]]
        value = _average([intervals[c["id"]] for c in children], [c["weight"] for c in children])
        metrics[group["id"]] = _assessment_metric(value, unit="fixed subcategory",
            planned=len(children), adjudicated=sum(intervals[c["id"]][2] is not None for c in children))
        contribution = tuple(None if x is None else x * Fraction(group["weight"], 100) for x in value)
        contributions[group["id"]] = _assessment_metric(contribution, unit="points in full benchmark",
            planned=len(children), adjudicated=sum(intervals[c["id"]][2] is not None for c in children))
        if policy["version"] == "0.6.0":
            known = sum((confirmed[c["id"]] * c["weight"] for c in children), Fraction(0))
            contributions[group["id"]]["confirmed"] = float(known)
            metrics[group["id"]]["confirmed"] = float(known * 100 / group["weight"])
    active = [child for child in policy["subcategories"] if child["status"] == "active"]
    def total(children):
        values = [intervals[c["id"]] for c in children]
        # Divide by the full 100 points even when some categories are unbuilt.
        return tuple(None if any(v[i] is None for v in values) else max(Fraction(0),
                     sum((v[i] * Fraction(c["weight"], 100) for v, c in zip(values, children)), Fraction()))
                     for i in range(3))
    for key, children in (("earned", active), ("overall", policy["subcategories"])):
        metrics[key] = _assessment_metric(total(children), unit="fixed 100-point benchmark",
            planned=len(children), adjudicated=sum(intervals[c["id"]][2] is not None for c in children))
    if policy["version"] == "0.6.0":
        metrics["earned"]["confirmed"] = float(max(Fraction(0),
            sum((confirmed[c["id"]] * c["weight"] for c in active), Fraction(0))))
    missing_tasks = max(0, policy["scope"]["tasks"] - len(tasks))
    return {"schema": "math-gauge.assessment-score/v1", "benchmark_version": policy["benchmark_version"],
        "scoring_method_version": policy["version"], "strict_method_version": strict_policy["version"],
        "score_mode": mode, "primary_metric": "earned", "model_label": inputs["model_label"],
        "policy_sha256": identity(policy), "strict_policy_sha256": identity(strict_policy),
        **({"case_selection": selection, "case_selection_sha256": identity(selection)}
           if selection is not None else {}),
        "plan_sha256": plan["plan_sha256"], "metrics": metrics, "contributions": contributions,
        "profile": {"groups": policy["groups"], "subcategories": policy["subcategories"]},
        "capacity": {"total": 100, "active": sum(c["weight"] for c in active),
                     "under_construction": sum(c["weight"] for c in policy["subcategories"] if c not in active)},
        "coverage": dict(policy["scope"], source_initial_tasks=len(tasks),
                         source_initial_judgments=sum(t["strict_pass"] is not None for t in tasks)),
        "whole_task_counts": {"planned": policy["scope"]["tasks"],
            "passed": sum(t["strict_pass"] is True for t in tasks),
            "failed": sum(t["strict_pass"] is False for t in tasks),
            "unknown": sum(t["strict_pass"] is None for t in tasks) + missing_tasks},
        "tasks": tasks, "alignment_selfcheck": alignment_summary,
        "strict_alignment_selfcheck": strict_trajectory, "initial_answers_replaced": False,
        "human_review": "pending", "formal_comparison_eligible": False, "new_candidate_calls": 0}


def score_assessment_record_inputs(inputs, review, source_policy, *, formalization_review,
                                   assessment_policy, strict_policy, mode="partial", theorem_extension_inputs=None):
    source = score_record_inputs(inputs, review, source_policy, formalization_review=formalization_review)
    substitutions = formalization_substitutions(inputs, formalization_review)
    trajectory = strict_alignment_trajectory(review, source_policy)
    result = score_assessment_inputs(inputs, assessment_policy, strict_policy, mode=mode,
        mathematical_substitutions=substitutions, alignment_summary=source["alignment_selfcheck"],
        strict_trajectory=trajectory, theorem_extension_inputs=theorem_extension_inputs)
    result["lean_formalization_breakdown"] = source["lean_formalization_breakdown"]
    return result


def score_strict_record_inputs(inputs, review, source_policy, *, formalization_review,
                               strict_policy, assessment_policy):
    return score_assessment_record_inputs(inputs, review, source_policy,
        formalization_review=formalization_review, assessment_policy=assessment_policy,
        strict_policy=strict_policy, mode="strict")


def render_score(report):
    if report.get("schema") == "math-gauge.assessment-score/v1":
        earned, overall = report["metrics"]["earned"], report["metrics"]["overall"]
        lines = ["# Math Gauge · 当前数学评测", "",
                 f"模式：{report['score_mode']}；已建{report['capacity']['active']}/100，研究30分建设中。",
                 f"已获分：{earned['exact'] if earned['exact'] is not None else '未决'}/100；"
                 f"完整总分区间：{overall['lower']}–{overall['upper']}，完整总分尚未确定。", "",
                 "| 大类 | 子类 | 权重 | 公有题 | 私有题 | 分项成绩 |", "|---|---|---:|---:|---:|---:|"]
        for group in report["profile"]["groups"]:
            for child in report["profile"]["subcategories"]:
                if child["id"] not in group["children"]:
                    continue
                metric = report["metrics"][child["id"]]
                value = '建设中' if child['status'] == 'under_construction' else metric['exact']
                lines.append(f"| {group['title']} | {child['title']} | {child['weight']}% | "
                             f"{child['public_tasks']} | {child['private_tasks']} | {value} |")
        return "\n".join(lines) + "\n"
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
    components = tuple(dict.fromkeys(row["component"] for row in report.get("papers", {}).values()))
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
    rounds = [key for key in next(iter(report["trajectories"]["focus_math"].values()))
              if key.startswith("round")]
    lines += ["", "Focus mathematical transitions (correction and damage show numerator / conditional denominator):", "",
              "| Branch | " + " | ".join(f"Round {key[5:]} correction / damage" for key in rounds)
              + " | Completion loss " + " / ".join("R" + key[5:] for key in rounds) + " |",
              "|" + "---|" * (len(rounds) + 2)]
    def ratio(value):
        return f"{value['numerator']}/{value['denominator']}" if value["denominator"] else "n/a (0 denominator)"
    for arm, trajectory in report["trajectories"]["focus_math"].items():
        transitions = [trajectory[key] for key in rounds]
        lines.append(f"| {arm} | " + " | ".join(f"{ratio(row['correction'])}; {ratio(row['damage'])}"
                                                 for row in transitions)
                     + " | " + " / ".join(str(row["completion_loss"]) for row in transitions) + " |")
    return "\n".join(lines) + "\n"
