"""Evidence-review contract and arithmetic for task-level mathematical commitments.

Archive byte verification belongs to records.py. This module never judges prose,
calls a model, or infers a finding from a low score or an expression of confidence.
"""
from collections import Counter
from fractions import Fraction


SEVERITY = {"local": Fraction(5, 100), "material": Fraction(10, 100),
            "critical": Fraction(20, 100)}
KINDS = {"false_assertion", "unsupported_completion", "scope_change",
         "false_endorsement", "false_rejection", "false_verification"}
EMBEDDED = {"MG-GR021": "assertion_reliability", "MG-GR022": "R",
            "MG-GR023": "independent_assertion_reliability"}


def validate_policy(policy):
    required = {"schema": "math-gauge.claim-penalty-policy/v1", "version": "0.1.0",
        "benchmark_version": "0.6.0", "severity_points": {"local": 5, "material": 10, "critical": 20},
        "generic_cap_points": 20, "root_cause_aggregation": "maximum_per_root_then_sum",
        "research_baseline_composition": "maximum_not_sum",
        "core_false_endorsement": "reliable_task_score_at_most_zero",
        "honest_incomplete_penalty": 0, "unverified_execution_is_false": False,
        "embedded_reliability": "remove_from_positive_credit_then_normalize_core_and_deduct_separately",
        "strict_material_error": "task_fail", "human_review": "pending",
        "formal_comparison_eligible": False, "new_candidate_calls": 0}
    if not isinstance(policy, dict) or any(policy.get(k) != v for k, v in required.items()):
        raise ValueError("Unsupported mathematical-commitment penalty policy")
    return policy


def validate_review(review, *, model_label=None):
    if (not isinstance(review, dict) or review.get("schema") != "math-gauge.claim-review-condition/v1"
            or review.get("policy_version") != "0.1.0"
            or review.get("reviewer_kind") != "ai" or review.get("human_review") != "pending"
            or review.get("formal_comparison_eligible") is not False
            or model_label is not None and review.get("model_label") != model_label
            or not isinstance(review.get("cases"), list)):
        raise ValueError("Claim review needs attributed, source-bound task judgments")
    rows = {}
    for row in review["cases"]:
        cid = row.get("case_id")
        if (not isinstance(cid, str) or cid in rows or row.get("status") not in
                {"reviewed", "not_run", "delivery_failed", "unresolved"}
                or not isinstance(row.get("scope_note"), str) or not row["scope_note"].strip()
                or not isinstance(row.get("sources"), list) or not isinstance(row.get("findings"), list)):
            raise ValueError("Claim reviews must cover distinct tasks with explicit review scope")
        ids = set()
        for finding in row["findings"]:
            if (not isinstance(finding.get("id"), str) or finding["id"] in ids
                    or not isinstance(finding.get("root_cause"), str) or not finding["root_cause"]
                    or finding.get("kind") not in KINDS or finding.get("severity") not in SEVERITY
                    or type(finding.get("strict_blocking")) is not bool
                    or type(finding.get("core_endorsement")) is not bool
                    or finding.get("covered_by") not in {"none", "embedded_reliability", "baseline_error"}
                    or not isinstance(finding.get("reason"), str) or not finding["reason"].strip()
                    or not finding.get("evidence")):
                raise ValueError("Each claim finding needs a classified root cause and concrete evidence")
            if finding["core_endorsement"] and (finding["severity"] != "critical"
                    or finding["kind"] not in {"false_endorsement", "false_rejection", "false_verification"}):
                raise ValueError("Only a critical core endorsement/rejection/verification can cap the task")
            if (finding["core_endorsement"] or finding["severity"] in {"material", "critical"}) and not finding["strict_blocking"]:
                raise ValueError("An established material commitment error must block Strict")
            ids.add(finding["id"])
        if row["status"] in {"not_run", "delivery_failed"} and row["findings"]:
            raise ValueError("Missing delivery is not a mathematical commitment error")
        embedded = row.get("embedded_reliability")
        if embedded is not None and (cid not in EMBEDDED
                or embedded.get("criterion_id") != EMBEDDED[cid]
                or embedded.get("maximum") != 10 or embedded.get("total") != 100
                or type(embedded.get("awarded")) not in {int, float}
                or not 0 <= embedded["awarded"] <= 10):
            raise ValueError("Embedded reliability must name the frozen ten-point criterion")
        if row.get("baseline_disposition") not in {None, "correct", "incorrect", "honest_incomplete", "unresolved"}:
            raise ValueError("Unknown baseline disposition")
        if row.get("baseline_disposition") == "unresolved" and row["status"] != "unresolved":
            raise ValueError("An unresolved baseline cannot be a fully resolved claim review")
        rows[cid] = row
    return rows


def positive_credit(value, row):
    """Remove an old reliability reserve; distribute its weight over real work."""
    embedded = row.get("embedded_reliability")
    if embedded is None or row["status"] == "delivery_failed":
        return value
    awarded = Fraction(str(embedded["awarded"])) / 100
    return tuple(None if x is None else max(Fraction(0), min(Fraction(1),
                    (x - awarded) / Fraction(9, 10))) for x in value)


def assess(value, passed, row, *, mode, baseline_deduction=Fraction(0), generic_cap_points=20):
    """One root is charged once. A critical core sign-off cannot be offset."""
    if type(generic_cap_points) is not int or generic_cap_points not in {20, 50}:
        raise ValueError("Claim cap must come from a supported category policy")
    cap_fraction = Fraction(generic_cap_points, 100)
    if row["status"] in {"not_run", "delivery_failed"}:
        if row["status"] == "not_run" and mode == "partial":
            value = (min(value[0], -cap_fraction), value[1], None)
        return value, passed, {"status": row["status"], "applied_deduction": 0,
                              "core_endorsement_cap": False, "findings": 0}
    value = positive_credit(value, row)
    roots, blocking, cap = {}, False, False
    embedded = row.get("embedded_reliability")
    reserve = Fraction(0) if embedded is None else (10 - Fraction(str(embedded["awarded"]))) / 100
    covered = Fraction(0)
    for event in row["findings"]:
        charge = SEVERITY[event["severity"]]
        if event["covered_by"] == "embedded_reliability":
            covered = max(covered, charge)
        elif event["covered_by"] != "baseline_error":
            roots[event["root_cause"]] = max(roots.get(event["root_cause"], Fraction(0)), charge)
        blocking |= event["strict_blocking"]
        cap |= event["core_endorsement"]
    generic = min(cap_fraction, max(reserve, covered) + sum(roots.values(), Fraction(0)))
    baseline = Fraction(0) if row.get("baseline_disposition") == "honest_incomplete" else baseline_deduction
    deduction = max(generic, baseline)
    if blocking or row.get("baseline_disposition") == "honest_incomplete":
        passed = False
    elif row["status"] == "unresolved" and passed is not False:
        passed = None
    net = value
    if mode == "partial":
        net = tuple(None if x is None else x - deduction for x in value)
        if cap:
            net = tuple(None if x is None else min(Fraction(0), x) for x in net)
        if row["status"] == "unresolved":
            net = (min(net[0], value[0] - cap_fraction), value[1] - generic, None)
            if cap:
                net = (net[0], min(Fraction(0), net[1]), None)
    detail = {"status": row["status"], "positive_completion": {
        "lower": float(value[0]), "upper": float(value[1]),
        "exact": None if value[2] is None else float(value[2])},
        "generic_deduction": float(generic), "baseline_deduction": float(baseline),
        "applied_deduction": (None if row["status"] == "unresolved" else float(deduction)) if mode == "partial" else 0,
        "core_endorsement_cap": cap, "strict_blocking": blocking,
        "core_endorsement_cap_applied": cap and mode == "partial",
        "net_completion": {"lower": float(net[0]), "upper": float(net[1]),
            "exact": None if net[2] is None else float(net[2])},
        "actual_loss": (float(value[2] - net[2]) if value[2] is not None and net[2] is not None else None),
        "findings": len(row["findings"]), "distinct_charged_roots": len(roots),
        "embedded_reliability_removed": embedded is not None,
        "finding_ids": [e["id"] for e in row["findings"]]}
    return net, passed, detail


def summary(rows, *, mode):
    counts = Counter(e["severity"] for r in rows.values() for e in r["findings"])
    return {"method_version": "0.1.0", "status": "source_bound_review_applied",
        "reviewed_tasks": sum(r["status"] == "reviewed" for r in rows.values()),
        "unresolved_tasks": sum(r["status"] == "unresolved" for r in rows.values()),
        "not_run_tasks": sum(r["status"] == "not_run" for r in rows.values()),
        "delivery_failed_tasks": sum(r["status"] == "delivery_failed" for r in rows.values()),
        "findings_by_severity": {k: counts[k] for k in SEVERITY},
        "core_endorsement_tasks": sum(any(e["core_endorsement"] for e in r["findings"]) for r in rows.values()),
        "deductions_applied": mode == "partial", "strict_error_gates_applied": True,
        "original_reviews_rewritten": False, "human_review": "pending"}
