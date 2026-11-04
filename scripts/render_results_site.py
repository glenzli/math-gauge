#!/usr/bin/env python3
"""Own the portable results projection and HTML; read frozen scores, never rescore.

Inputs are four original public results, two source-qualified mathematical
snapshots and four versioned alignment-augmented results. Only allowed aggregates, source status and
the four public written panels enter the output. No runner or scorer is invoked.
"""

import argparse
import copy
import hashlib
import html
import json
import math
from pathlib import Path
from string import Template


ROOT = Path(__file__).resolve().parents[1]
GITHUB = "https://github.com/glenzli/math-gauge"
ARTICLE = "https://glenzli.com/notes/ai-mathematical-ability-and-the-future/"
MODELS = (("terra", "Terra 6.1 Max"), ("gemini", "Gemini 3.8 Flash High"))
COMPONENTS = {
    "proofs": "书面论证",
    "lean-audit": "Lean 语义审计",
    "lean-formalization": "大 Lean 形式化",
    "exploration": "私有研究探索",
    "answer-review": "真实答卷审阅",
}
OVERALL = {
    "core": "数学完成分",
    "repeat": "独立复答",
    "neutral": "中性自查",
    "stance": "立场压力自查",
}
METRICS = tuple(COMPONENTS) + tuple(OVERALL) + (
    "overall", "answer_review_major_error_rate", "answer_review_strict_pass_rate",
)
COVERAGE = (
    "papers_planned", "parent_families", "a1_planned", "a1_reviewed",
    "slots_planned", "slots_reviewed",
)
METRIC_COVERAGE = (
    "planned", "adjudicated", "unknown", "started_slots", "reviewed_slots",
)
PUBLIC_PANEL = ("MG-GR002", "MG-GR014", "MG-GP001", "MG-GP002")
PANEL_SLOTS = (":A1", ":A2", ":neutral:1", ":affirm:1", ":deny:1")
WORKSPACE_METRICS = ("lean-formalization", "core", "overall")
ALIGNMENT_METRICS = ("neutral", "overall", "neutral_written", "lean_alignment_selfcheck")
SOURCE_COVERAGE = (
    "planned_standard_slots", "original_standard_slots_reviewed",
    "additional_workspace_mathematical_sources", "effective_mathematical_slots_adjudicated",
    "fresh_A1_slots_added", "successful_native_deliveries_added", "formal_eligible_slots_added",
)


def count(value):
    if type(value) is not int or value < 0:
        raise ValueError("Expected a nonnegative frozen coverage count")
    return value


def number(value, maximum=100, minimum=0):
    if (type(value) not in (int, float) or not math.isfinite(value)
            or not minimum <= value <= maximum):
        raise ValueError("Expected a finite frozen score in range")
    return value


def metric_projection(metric, *, execution_counts=True, minimum=0):
    """Copy a metric, including null, without deriving any score or denominator."""
    exact = metric["exact"]
    lower, upper = number(metric["lower"], minimum=minimum), number(metric["upper"], minimum=minimum)
    if lower > upper or type(metric["complete"]) is not bool:
        raise ValueError("Invalid frozen metric bounds or completion status")
    if exact is not None:
        number(exact, minimum=minimum)
        if exact < lower - 1e-8 or exact > upper + 1e-8:
            raise ValueError("Frozen exact score is outside its bounds")
    return {
        "exact": exact, "lower": lower, "upper": upper,
        "complete": metric["complete"],
        "coverage": {key: count(metric["coverage"][key])
                     for key in (METRIC_COVERAGE if execution_counts
                                 else ("planned", "adjudicated", "unknown"))},
    }


def profile_projection(profile, scope):
    if profile["version"] != "0.6.0" or profile["standard_version"] != "0.6.0":
        raise ValueError("This editorial page is bound to the v0.6.0 draft")
    expected = set(COMPONENTS) - ({"exploration"} if scope == "public" else set())
    if {row["id"] for row in profile["components"]} != expected:
        raise ValueError("Unexpected frozen capability directions")
    if any(row["aggregation"] not in ("family", "parent_family")
           for row in profile["components"]):
        raise ValueError("Unexpected frozen family aggregation")
    if (profile.get("reliability_population") != "written-only"
            or profile.get("repeat_attempt_labels") != ["A1", "A2"]
            or profile.get("self_check_rounds_per_arm") != 1):
        raise ValueError("Unexpected written reliability panel contract")
    return {
        "version": profile["version"],
        "standard_version": profile["standard_version"],
        "components": [
            {"id": row["id"], "weight": number(row["weight"]),
             "case_count": count(row["case_count"]),
             "family_count": count(row["family_count"]),
             "aggregation": row["aggregation"]}
            for row in profile["components"]
        ],
        "overall_weights": {key: number(profile["overall_weights"][key])
                            for key in OVERALL},
        "repeat_attempt_labels": ["A1", "A2"],
        "self_check_rounds_per_arm": 1,
        "reliability_population": "written-only",
    }


def aggregate_projection(source, scope):
    schema = ("math-gauge.public-composite-score/v1" if scope == "public"
              else "math-gauge.combined-aggregate-only/v1")
    if source.get("schema") != schema:
        raise ValueError("Only explicit public and combined aggregate projections are allowed")
    if scope == "public":
        if source.get("score_units") != {"metrics": "percent", "completion": "fraction"}:
            raise ValueError("Unexpected public result units")
        evidence = source["evidence_status"]
        human = evidence["human_approval"]
        eligible = evidence["formal_comparison_eligible"]
        if evidence["backend_identity_independently_verified"] is not False:
            raise ValueError("Review the backend identity wording before changing this page")
    else:
        human = source["human_review"]
        eligible = source["formal_comparison_eligible"]
        if source.get("suite_version") != "0.6.0" or source.get("scope") != "combined":
            raise ValueError("Unexpected combined result identity")
    if human != "pending" or eligible is not False:
        raise ValueError("Review the human-pending wording before changing this page")
    profile = profile_projection(source["profile"], scope)
    allowed = [key for key in METRICS if key != "exploration" or scope == "combined"]
    result = {
        "profile": profile,
        "metrics": {key: metric_projection(source["metrics"][key]) for key in allowed},
        "coverage": {key: count(source["coverage"][key]) for key in COVERAGE},
        "human_review": human,
        "formal_comparison_eligible": eligible,
    }
    if scope == "combined":
        result["private_coverage_counts"] = {
            key: count(source["private_coverage_counts"][key])
            for key in ("planned", "responses_present", "reviews_present", "adjudicated")
        }
    return result


def written_panel_projection(source):
    """Select only known public case IDs and whole-answer completion fractions."""
    wanted = {case + suffix for case in PUBLIC_PANEL for suffix in PANEL_SLOTS}
    selected = [row for row in source["slot_evidence"] if row.get("slot_id") in wanted]
    rows = {row["slot_id"]: row for row in selected}
    if len(selected) != len(wanted) or set(rows) != wanted:
        raise ValueError("The four public written panels must be complete and unique")
    panels = []
    for case in PUBLIC_PANEL:
        values = []
        for suffix in PANEL_SLOTS:
            value = rows[case + suffix]["completion"]["exact"]
            values.append(None if value is None else number(value, 1))
        panels.append({"public_case_id": case, "whole_answer_completion": values})
    return panels


def chapter_source_projection(source):
    """Express the frozen public C003 fraction in obligation units."""
    total = count(source["formalization_scope"]["MG-C003"]["obligations"])
    if total != 92:
        raise ValueError("Review the C003 obligation unit before changing this page")
    rows = [row for row in source["slot_evidence"] if row.get("slot_id") == "MG-C003:A1"]
    if len(rows) != 1:
        raise ValueError("The C003 capability source must be unique")
    value = rows[0]["completion"]["exact"]
    complete = None
    if value is not None:
        in_units = number(value, 1) * total
        complete = round(in_units)
        if not math.isclose(in_units, complete, rel_tol=0, abs_tol=1e-8):
            raise ValueError("C003 completion does not express an integer obligation count")
    return {"public_case_id": "MG-C003", "complete": complete, "total": total,
            "extra_time_source": False}


def workspace_projection(source, original, original_hash, scope):
    """Validate a source-bound snapshot, then copy only its three scored metrics."""
    if (source.get("schema") != "math-gauge.source-qualified-score/v1"
            or source.get("scope") != scope
            or source.get("scoring_owner") != "math_gauge.scoring"
            or source.get("scoring_view_version") != "c003-sealed-extension/v1"
            or source.get("score_units") != {"metrics": "percent", "completion": "fraction"}):
        raise ValueError("Unexpected source-qualified mathematical snapshot")
    if source["source_bindings"]["original_summary_sha256"] != original_hash:
        raise ValueError("Workspace snapshot is bound to a different original summary hash")
    if source["profile"] != original["profile"] or source["coverage"] != original["coverage"]:
        raise ValueError("Workspace snapshot changed the original profile or coverage")
    prior = source["original_score"]
    if (prior["metrics"] != original["metrics"]
            or prior["coverage"] != original["coverage"]
            or prior["status"] != original["status"]
            or prior["standard_evidence_rewritten"] is not False):
        raise ValueError("Workspace snapshot does not preserve the original score and evidence")
    if set(source["metrics"]) != set(original["metrics"]):
        raise ValueError("Workspace snapshot changed the metric inventory")
    for key in set(original["metrics"]) - set(WORKSPACE_METRICS):
        if source["metrics"][key] != original["metrics"][key]:
            raise ValueError("Workspace snapshot changed an unrelated metric")
    if (source["human_review"] != "pending"
            or source["formal_comparison_eligible"] is not False
            or type(source["new_candidate_calls"]) is not int
            or source["new_candidate_calls"] != 0):
        raise ValueError("Workspace mathematics cannot add execution or human qualification")
    coverage = {key: count(source["mathematical_source_coverage"][key])
                for key in SOURCE_COVERAGE}
    expected_coverage = {
        "planned_standard_slots": original["coverage"]["slots_planned"],
        "original_standard_slots_reviewed": original["coverage"]["slots_reviewed"],
        "additional_workspace_mathematical_sources": 1,
        "effective_mathematical_slots_adjudicated": original["coverage"]["slots_planned"],
        "fresh_A1_slots_added": 0, "successful_native_deliveries_added": 0,
        "formal_eligible_slots_added": 0,
    }
    if coverage != expected_coverage:
        raise ValueError("Unexpected workspace mathematical source coverage")
    substitution = source["mathematical_substitution"]
    expected_status = {
        "case_id": "MG-C003", "case_version": "0.1.1",
        "original_weight_slot": "MG-C003:A1", "complete": 74,
        "not_complete": 18, "total": 92,
        "completion_fraction": {"numerator": 74, "denominator": 92},
        "changed_metrics": list(WORKSPACE_METRICS),
        "original_A1_replaced": False, "fresh_A1": False, "equal_time_comparison": False,
        "native_result_status": "ERROR",
        "native_error_class": "output/token limit exceeded; not deadline expiry",
        "original_owner_status": "ok", "original_owner_gate_accepted": True,
        "delivery_format": {"status": "format_error", "original_version": "v0.1.1",
                            "required_version": "0.1.1", "original_json_repaired": False},
        "source_kernel_only_status": "passed",
        "backend_identity_or_third_party_timing_independently_authenticated": False,
    }
    for key, expected in expected_status.items():
        if (substitution[key] != expected
                or (type(expected) is bool and substitution[key] is not expected)):
            raise ValueError("Review the selected workspace mathematics and status wording")
    for key, expected in (("pass_ids", 74), ("not_complete_ids", 18)):
        if len(substitution[key]) != expected or len(set(substitution[key])) != expected:
            raise ValueError("Unexpected selected workspace obligation inventory")
    if set(substitution["pass_ids"]) & set(substitution["not_complete_ids"]):
        raise ValueError("Workspace obligation outcomes overlap")
    accounting = {key: count(source["candidate_call_accounting"][key]) for key in (
        "scoring_recompute", "selected_extension_original_submissions", "further_submissions_by_this_view",
    )}
    if accounting != {"scoring_recompute": 0, "selected_extension_original_submissions": 1,
                      "further_submissions_by_this_view": 0}:
        raise ValueError("Unexpected selected-workspace candidate call accounting")
    scorer_hash = source["scoring_implementation_sha256"]
    if (not isinstance(scorer_hash, str) or len(scorer_hash) != 64
            or any(char not in "0123456789abcdef" for char in scorer_hash)):
        raise ValueError("Expected a frozen shared-scorer implementation hash")
    metrics = {key: metric_projection(source["metrics"][key]) for key in WORKSPACE_METRICS}
    for key in WORKSPACE_METRICS:
        frozen = source["metrics"][key]
        if (frozen["exact"] is None or not frozen["complete"]
                or frozen["formal_comparison_eligible"] is not False
                or frozen.get("formal_exact") is not None):
            raise ValueError("Expected provisional mathematical points without formal qualification")
        for field in ("planned", "started_slots", "reviewed_slots", "formal_eligible_slots"):
            if frozen["coverage"][field] != original["metrics"][key]["coverage"][field]:
                raise ValueError("Workspace metric changed a frozen execution denominator")
    return {
        "metrics": metrics,
        "mathematical_source_coverage": coverage,
        "mathematical_substitution": expected_status,
        "source_bindings": {"original_summary_sha256": original_hash},
        "candidate_call_accounting": accounting,
        "scoring_implementation_sha256": scorer_hash,
    }


def alignment_projection(source, baseline, original_hash, selected_hash, policy_hash,
                         review_hash, scope):
    """Copy the frozen new score after checking its source and unchanged metrics."""
    if (source.get("schema") != "math-gauge.alignment-augmented-score/v1"
            or source.get("scope") != scope
            or source.get("scoring_owner") != "math_gauge.scoring"
            or source.get("human_review") != "pending"
            or source.get("formal_comparison_eligible") is not False
            or source.get("new_candidate_calls") != 0):
        raise ValueError("Unexpected alignment-augmented result or qualification")
    bindings = source["source_bindings"]
    expected = {"original_summary_sha256": original_hash, "policy_sha256": policy_hash,
                "alignment_review_sha256": review_hash}
    if selected_hash is not None:
        expected["source_qualified_score_sha256"] = selected_hash
    elif "source_qualified_score_sha256" in bindings:
        raise ValueError("Terra alignment view cannot substitute a workspace for A1")
    if any(bindings.get(key) != value for key, value in expected.items()):
        raise ValueError("Alignment result source binding differs from the selected input")
    if source["profile"] != baseline["profile"] or source["coverage"] != baseline["coverage"]:
        raise ValueError("Alignment result changed the frozen baseline profile or coverage")
    policy = source["policy"]
    if (policy.get("version") != "0.1.0" or policy.get("sha256") != policy_hash
            or policy.get("neutral_group_weights") != {"written": 1, "lean_alignment": 1}
            or policy.get("overall_weights") != {"core": 75, "repeat": 5, "neutral": 10, "stance": 10}):
        raise ValueError("Review the alignment weights and version before updating this display")
    metrics = source["metrics"]
    if set(metrics) != set(baseline["metrics"]) | {"neutral_written", "lean_alignment_selfcheck"}:
        raise ValueError("Unexpected alignment metric inventory")
    for key in set(baseline["metrics"]) - {"neutral", "overall"}:
        if metric_projection(metrics[key]) != metric_projection(baseline["metrics"][key]):
            raise ValueError("Alignment view changed an unrelated baseline metric")
    if metric_projection(metrics["neutral_written"]) != metric_projection(baseline["metrics"]["neutral"]):
        raise ValueError("Alignment view changed the existing written neutral score")
    study = source["alignment_selfcheck"]
    if study.get("schema") != "math-gauge.alignment-selfcheck-score/v1":
        raise ValueError("Unexpected alignment study score schema")
    rounds = []
    for row in study["rounds"]:
        rounds.append({"round": count(row["round"]),
                       "score": metric_projection(row["score"], execution_counts=False),
                       **{key: (None if row[key] is None else count(row[key]))
                          for key in ("complete", "repaired", "regressed", "restored", "first_new")},
                       "major_false_complete": row["major_false_complete"]})
    if [row["round"] for row in rounds] != [1, 2, 3]:
        raise ValueError("Alignment display requires the fixed three-round sequence")
    events = study["major_false_complete_events"]
    return {
        "metrics": {key: metric_projection(metrics[key],
                    execution_counts=key not in {"neutral", "lean_alignment_selfcheck"})
                    for key in ALIGNMENT_METRICS},
        "alignment_selfcheck": {
            "rounds": rounds,
            "major_false_complete_events": {key: count(events[key])
                for key in ("count", "applicable_rounds", "unknown_rounds")},
        },
        "alignment_policy": {"version": "0.1.0", "sha256": policy_hash,
                             "neutral_group_weights": {"written": 1, "lean_alignment": 1},
                             "lean_overall_weight_percent": 5},
    }


def engineering_workspace_projection(source, original, original_hash, scope):
    if (source.get("schema") != "math-gauge.source-qualified-engineering-score/v1"
            or source.get("scope") != scope or source.get("model_key") != "terra"
            or source.get("scoring_owner") != "math_gauge.scoring"
            or source.get("scoring_view_version") != "c003-sealed-engineering/v1"
            or source.get("formal_comparison_eligible") is not False
            or source.get("human_review") != "pending"):
        raise ValueError("Unexpected archived engineering capability score")
    if (source["source_bindings"]["original_summary_sha256"] != original_hash
            or source["profile"] != original["profile"] or source["coverage"] != original["coverage"]):
        raise ValueError("Engineering capability changed the original source binding")
    if set(source["metrics"]) != set(original["metrics"]):
        raise ValueError("Engineering capability changed the metric inventory")
    for key in set(original["metrics"]) - set(WORKSPACE_METRICS):
        if source["metrics"][key] != original["metrics"][key]:
            raise ValueError("Engineering capability changed an unrelated metric")
    selected = source["mathematical_substitution"]
    if (selected["case_id"] != "MG-C003" or selected["complete"] != 74
            or selected["total"] != 92 or selected["original_A1_replaced"] is not False):
        raise ValueError("Unexpected selected Terra engineering result")
    return {key: metric_projection(source["metrics"][key]) for key in WORKSPACE_METRICS}


def engineering_alignment_projection(source, baseline, original_hash, selected_hash,
                                     policy_hash, review_hash, scope, *, weight_policy=None,
                                     previous_score_hash=None):
    version = "0.3.0" if weight_policy is not None else "0.2.0"
    if (source.get("schema") != "math-gauge.alignment-augmented-score/v1"
            or source.get("scope") != scope
            or source.get("scoring_view_version") != f"alignment-selfcheck/{version}"
            or source.get("scoring_owner") != "math_gauge.scoring"
            or source.get("formal_comparison_eligible") is not False
            or source.get("human_review") != "pending" or source.get("new_candidate_calls") != 0):
        raise ValueError("Unexpected engineering alignment score")
    expected = {"original_summary_sha256": original_hash,
                "source_qualified_score_sha256": selected_hash,
                "policy_sha256": policy_hash, "alignment_review_sha256": review_hash}
    if any(source["source_bindings"].get(k) != v for k, v in expected.items()):
        raise ValueError("Engineering result source binding differs")
    expected_profile = copy.deepcopy(baseline["profile"])
    if weight_policy is not None:
        if (weight_policy.get("version") != version
                or weight_policy.get("schema") != "math-gauge.alignment-selfcheck-policy/v1"):
            raise ValueError("Unexpected rebalanced weight policy")
        for row in expected_profile["components"]:
            row["weight"] = weight_policy["capability_component_weights"][scope][row["id"]]
        expected_profile["overall_weights"] = weight_policy["overall_weights"]
        if (source.get("weight_change") != {"previous_version": "0.2.0",
                "previous_score_sha256": previous_score_hash, "judgments_changed": False,
                "new_candidate_calls": 0}
                or source.get("aggregation_profile_binding", {}).get("weight_policy_sha256") != policy_hash):
            raise ValueError("Rebalanced result changed its original-score binding")
    if source["profile"] != expected_profile or source["coverage"] != baseline["coverage"]:
        raise ValueError("Engineering alignment changed the baseline profile or coverage")
    policy = source["policy"]
    expected_neutral = weight_policy["neutral_group_weights"] if weight_policy is not None else {"written": 1, "lean_alignment": 1}
    if (policy["version"] != version or policy["sha256"] != policy_hash
            or policy["neutral_group_weights"] != expected_neutral
            or policy["overall_weights"] != expected_profile["overall_weights"]
            or weight_policy is not None and policy.get("capability_component_weights")
            != weight_policy["capability_component_weights"]):
        raise ValueError("Unexpected engineering alignment weights")
    metrics = source["metrics"]
    if set(metrics) != set(baseline["metrics"]) | {"neutral_written", "lean_alignment_selfcheck"}:
        raise ValueError("Unexpected engineering metric inventory")
    for key in set(baseline["metrics"]) - ({"core", "neutral", "overall"} if weight_policy is not None else {"neutral", "overall"}):
        if metric_projection(metrics[key]) != metric_projection(baseline["metrics"][key]):
            raise ValueError("Engineering alignment changed an unrelated metric")
    if metric_projection(metrics["neutral_written"]) != metric_projection(baseline["metrics"]["neutral"]):
        raise ValueError("Engineering alignment changed the written selfcheck")
    study = source["alignment_selfcheck"]
    rounds = []
    for row in study["rounds"]:
        rounds.append({"round": count(row["round"]), "complete": count(row["complete"]),
                       "total": count(row["total"]),
                       "score": metric_projection(row["score"], execution_counts=False, minimum=-20),
                       "base_score": number(row["base_score"]),
                       "penalty_points": number(row["penalty_points"], 20)})
    if [row["round"] for row in rounds] != [1, 2, 3]:
        raise ValueError("Engineering alignment requires three rounds")
    breakdown = source["lean_formalization_breakdown"]
    cases = []
    for row in breakdown["cases"]:
        if row["case_id"] not in {"LCH01", "LCH02", "HCH02", "MG-C003"}:
            raise ValueError("Only four public formalization cases may be displayed")
        cases.append({"case_id": row["case_id"], "family_id": row["family_id"],
                      "complete_count": count(row["complete_count"]), "total": count(row["total"]),
                      "percent": number(row["percent"])})
        if (cases[-1]["total"] != {"LCH01": 8, "LCH02": 20, "HCH02": 40, "MG-C003": 92}[row["case_id"]]
                or cases[-1]["complete_count"] > cases[-1]["total"]
                or (row["case_id"] == "MG-C003" and cases[-1]["complete_count"] != 74)):
            raise ValueError("Unexpected formalization requirement or verified count")
    if len(cases) != 4 or len({row["case_id"] for row in cases}) != 4:
        raise ValueError("Engineering display requires four distinct public formalization cases")
    families = {}
    for family, row in breakdown["families"].items():
        if family not in {"oet-volume1-chapter02", "oet-volume1-chapter03"}:
            raise ValueError("Unexpected public formalization family")
        families[family] = {"percent": number(row["percent"])}
    return {"metrics": {key: metric_projection(metrics[key],
                        execution_counts=key not in {"neutral", "lean_alignment_selfcheck"},
                        minimum=-20 if key in {"neutral", "lean_alignment_selfcheck"} else 0)
                        for key in ALIGNMENT_METRICS + (("core",) if weight_policy is not None else ())},
            "profile": profile_projection(source["profile"], scope),
            "neutral_group_weights": {key: number(value) for key, value in expected_neutral.items()},
            "alignment_selfcheck": {"rounds": rounds},
            "lean_formalization_breakdown": {"cases": cases, "families": families}}


def load_data(source_root=ROOT, use_workspace_source=True, use_alignment_source=True,
              use_engineering_source=True, use_rebalanced_source=True):
    """Read frozen files and project scores; never invoke or reimplement scoring."""
    source_root = Path(source_root)
    engineering = use_workspace_source and use_alignment_source and use_engineering_source
    models, sources = [], []
    for model, label in MODELS:
        projections = {}
        for scope, filename in (("public", "result.json"),
                                ("combined", "combined-aggregate.json")):
            relative = f"docs/results/{model}-v0.6.0/{filename}"
            raw = (source_root / relative).read_bytes()
            source = json.loads(raw)
            if scope == "public" and not source.get("id", "").startswith(model + "-"):
                raise ValueError("Unexpected public model label")
            if scope == "combined" and source.get("model") != model:
                raise ValueError("Unexpected combined model label")
            projections[scope] = aggregate_projection(source, scope)
            if scope == "public":
                projections["written_panel"] = written_panel_projection(source)
                projections["chapter_capability_source"] = chapter_source_projection(source)
            original_hash = hashlib.sha256(raw).hexdigest()
            sources.append({
                "model": model, "scope": scope, "path": relative,
                "kind": "original-summary",
                "url": f"{GITHUB}/blob/main/{relative}",
                "sha256": original_hash,
            })
            selected_hash = None
            baseline_source = source
            if model == "gemini" and use_workspace_source:
                qualified_path = f"docs/results/gemini-v0.6.0-extension/{filename}"
                qualified_raw = (source_root / qualified_path).read_bytes()
                baseline_source = json.loads(qualified_raw)
                selected_hash = hashlib.sha256(qualified_raw).hexdigest()
                qualified = workspace_projection(baseline_source, source,
                                                 original_hash, scope)
                prior = projections[scope]
                prior["original_score"] = {
                    "metrics": prior["metrics"].copy(), "coverage": prior["coverage"].copy(),
                    "human_review": prior["human_review"],
                    "formal_comparison_eligible": prior["formal_comparison_eligible"],
                    "standard_evidence_rewritten": False,
                }
                prior["metrics"].update(qualified.pop("metrics"))
                prior.update(qualified)
                if scope == "public":
                    projections["chapter_capability_source"] = {
                        "public_case_id": "MG-C003", "complete": 74, "total": 92,
                        "extra_time_source": True,
                    }
                sources.append({
                    "model": model, "scope": scope, "path": qualified_path,
                    "kind": "admitted-workspace-mathematics",
                    "url": f"{GITHUB}/blob/main/{qualified_path}",
                    "sha256": selected_hash,
                })
            if engineering and model == "terra":
                qualified_path = f"docs/results/engineering-v0.2.0/terra-capability-{scope}.json"
                qualified_raw = (source_root / qualified_path).read_bytes()
                baseline_source = json.loads(qualified_raw)
                selected_hash = hashlib.sha256(qualified_raw).hexdigest()
                projections[scope]["metrics"].update(engineering_workspace_projection(
                    baseline_source, source, original_hash, scope))
                projections["chapter_capability_source"] = {
                    "public_case_id": "MG-C003", "complete": 74, "total": 92,
                    "extra_time_source": False}
                sources.append({"model": model, "scope": scope, "path": qualified_path,
                                "kind": "archived-engineering-capability",
                                "url": f"{GITHUB}/blob/main/{qualified_path}", "sha256": selected_hash})
            if engineering:
                version = "0.3.0" if use_rebalanced_source else "0.2.0"
                previous_hash = None
                if use_rebalanced_source:
                    previous_path = f"docs/results/engineering-v0.2.0/{model}-{scope}.json"
                    previous_raw = (source_root / previous_path).read_bytes()
                    previous_hash = hashlib.sha256(previous_raw).hexdigest()
                    sources.append({"model": model, "scope": scope, "path": previous_path,
                                    "kind": "previous-engineering-score",
                                    "url": f"{GITHUB}/blob/main/{previous_path}", "sha256": previous_hash})
                relative = f"docs/results/engineering-v{version}/{model}-{scope}.json"
                raw = (source_root / relative).read_bytes()
                policy_raw = (source_root / f"protocol/lean-alignment/engineering-scoring-v{version}.json").read_bytes()
                review_raw = (source_root / f"docs/results/engineering-v{version}/{model}-review.json").read_bytes()
                projected = engineering_alignment_projection(
                    json.loads(raw), baseline_source, original_hash, selected_hash,
                    hashlib.sha256(policy_raw).hexdigest(), hashlib.sha256(review_raw).hexdigest(), scope,
                    weight_policy=json.loads(policy_raw) if use_rebalanced_source else None,
                    previous_score_hash=previous_hash)
                projections[scope]["metrics"].update(projected.pop("metrics"))
                projections[scope].update(projected)
                sources.append({"model": model, "scope": scope, "path": relative,
                                "kind": "engineering-alignment-score",
                                "url": f"{GITHUB}/blob/main/{relative}",
                                "sha256": hashlib.sha256(raw).hexdigest()})
            elif use_workspace_source and use_alignment_source:
                relative = f"docs/results/alignment-v0.1.0/{model}-{scope}.json"
                raw = (source_root / relative).read_bytes()
                policy_raw = (source_root / "protocol/lean-alignment/scoring-v0.1.0.json").read_bytes()
                review_raw = (source_root / f"docs/results/alignment-v0.1.0/{model}-review.json").read_bytes()
                augmented = alignment_projection(
                    json.loads(raw), baseline_source, original_hash, selected_hash,
                    hashlib.sha256(policy_raw).hexdigest(), hashlib.sha256(review_raw).hexdigest(), scope,
                )
                prior = projections[scope]
                prior["prior_alignment_score"] = {"metrics": prior["metrics"].copy(),
                                                  "standard_evidence_rewritten": False}
                prior["metrics"].update(augmented.pop("metrics"))
                prior.update(augmented)
                sources.append({"model": model, "scope": scope, "path": relative,
                                "kind": "alignment-augmented-score",
                                "url": f"{GITHUB}/blob/main/{relative}",
                                "sha256": hashlib.sha256(raw).hexdigest()})
        # One direction table may show shared direction scores only if they agree.
        for key in set(COMPONENTS) - {"exploration"}:
            if projections["public"]["metrics"][key] != projections["combined"]["metrics"][key]:
                raise ValueError("Public and combined direction scores diverged; update the display")
        models.append({"id": model, "requested_model_label": label,
                       "scoring_source": ("archived-engineering" if engineering else
                                          "admitted-workspace-mathematics"
                                          if model == "gemini" and use_workspace_source
                                          else "original-response"), **projections})
    for scope in ("public", "combined"):
        if models[0][scope]["profile"] != models[1][scope]["profile"]:
            raise ValueError("Models do not share the same frozen display profile")
    return {
        "schema": ("math-gauge.portable-results/v5" if engineering and use_rebalanced_source else
                   "math-gauge.portable-results/v4" if engineering else
                   "math-gauge.portable-results/v3" if use_workspace_source and use_alignment_source
                   else "math-gauge.portable-results/v2"),
        "view": ("engineering-alignment" if engineering else
                 "alignment-selfcheck" if use_workspace_source and use_alignment_source else
                 "workspace-mathematics" if use_workspace_source else "original-standard"),
        "suite_version": "0.6.0",
        **({"weight_policy_version": "0.3.0" if use_rebalanced_source else "0.2.0"} if engineering else {}),
        "status": "local-draft-human-pending",
        "formal_comparison_eligible": False,
        "backend_identity_independently_verified": False,
        "score_units": {"metrics": "percent", "whole_answer_completion": "fraction"},
        "models": models, "sources": sources,
    }


def escape(value):
    return html.escape(str(value), quote=True)


def score_html(metric, precision=2):
    if metric["exact"] is None:
        lower = f'{metric["lower"]:.{precision}f}'
        upper = f'{metric["upper"]:.{precision}f}'
        approximate = (float(lower) != metric["lower"]
                       or float(upper) != metric["upper"])
        prefix = "约 " if approximate else ""
        return (f'<strong class="unresolved">未决</strong>'
                f'<span class="bounds">{prefix}[{lower}, {upper}]</span>')
    value = f'{metric["exact"]:.{precision}f}'
    prefix = '<small>约 </small>' if float(value) != metric["exact"] else ""
    return f'<strong class="score">{prefix}{value}</strong>'


def component(profile, key):
    return next(row for row in profile["components"] if row["id"] == key)


def render_current_html(data):
    """Present current scores and the few distinctions needed to interpret them."""
    models = data["models"]
    profile = models[0]["public"]["profile"]
    overall = profile["overall_weights"]
    neutral = models[0]["public"]["neutral_group_weights"]
    written_weight = overall["neutral"] * neutral["written"] / sum(neutral.values())
    lean_weight = overall["neutral"] * neutral["lean_alignment"] / sum(neutral.values())
    score_rows = "".join(
        '<tr><th scope="row">' + escape(model["requested_model_label"]) + '</th>'
        + "".join(f'<td data-label="{title}">{score_html(model[scope]["metrics"]["overall"])}</td>'
                  for scope, title in (("public", "公开总分"), ("combined", "含私有题总分"))) + '</tr>'
        for model in models)
    direction_rows = []
    for key, title in COMPONENTS.items():
        scope = "combined" if key == "exploration" else "public"
        pw = '—' if key == "exploration" else f'{component(profile, key)["weight"]:g}%'
        cw = f'{component(models[0]["combined"]["profile"], key)["weight"]:g}%'
        values = "".join('<td>' + score_html(model[scope]["metrics"][key]) + '</td>' for model in models)
        direction_rows.append(f'<tr><th scope="row">{title}<span class="weight">公开 {pw} · 合并 {cw}</span></th>{values}</tr>')
    cases = [{row["case_id"]: row for row in model["public"]["lean_formalization_breakdown"]["cases"]}
             for model in models]
    case_rows = "".join('<tr><th scope="row">' + cid + '</th>'
                        + "".join(f'<td>{rows[cid]["complete_count"]}/{rows[cid]["total"]}</td>' for rows in cases)
                        + '</tr>' for cid in ("LCH01", "LCH02", "HCH02", "MG-C003"))
    family_values = [model["public"]["lean_formalization_breakdown"]["families"] for model in models]
    family_note = ('前三题同属CH2家族，平均通过率为Terra '
                   f'{family_values[0]["oet-volume1-chapter02"]["percent"]:.2f}、Gemini '
                   f'{family_values[1]["oet-volume1-chapter02"]["percent"]:.2f}；MG-C003属CH3家族，分别为'
                   f'{family_values[0]["oet-volume1-chapter03"]["percent"]:.2f}、'
                   f'{family_values[1]["oet-volume1-chapter03"]["percent"]:.2f}。两个家族等权平均，得到上表的大Lean方向分。')
    cards = []
    for key, title in (("repeat", f"独立复答 · {overall['repeat']:g}%"),
                       ("neutral_written", f"书面中性自查 · {written_weight:g}%"),
                       ("lean_alignment_selfcheck", f"Lean对齐自查 · {lean_weight:g}%"),
                       ("stance", f"立场压力自查 · {overall['stance']:g}%")):
        values = "".join('<div><span>' + escape(model["id"].title()) + '</span>'
                         + score_html(model["public"]["metrics"][key]) + '</div>' for model in models)
        cards.append(f'<article class="reliability-card"><h3>{title}</h3><div class="pair">{values}</div></article>')
    round_rows = []
    for i in range(3):
        rows = [model["public"]["alignment_selfcheck"]["rounds"][i] for model in models]
        round_rows.append(f'<tr><th scope="row">R{i + 1}</th>'
                          + "".join(f'<td>{row["complete"]}/{row["total"]}</td>' for row in rows)
                          + "".join('<td>' + score_html(row["score"]) + '</td>' for row in rows) + '</tr>')
    css = PAGE.template.split('<style>', 1)[1].split('</style>', 1)[0]
    return CURRENT_PAGE.substitute(css=css, score_rows=score_rows,
                                  direction_rows="".join(direction_rows), case_rows=case_rows,
                                  family_note=family_note, cards="".join(cards),
                                  round_rows="".join(round_rows), github=GITHUB,
                                  core_weight=f"{overall['core']:g}",
                                  overall_note=(f"能力{overall['core']:g}%、独立复答{overall['repeat']:g}%、"
                                      f"书面中性自查{written_weight:g}%、Lean对齐自查{lean_weight:g}%、"
                                      f"立场压力自查{overall['stance']:g}%"),
                                  scoring_version=data["weight_policy_version"])


def render_html(data):
    if data["view"] == "engineering-alignment":
        return render_current_html(data)
    terra, gemini = data["models"]
    alignment_view = data["view"] == "alignment-selfcheck"
    workspace_view = data["view"] in {"workspace-mathematics", "alignment-selfcheck"}
    public, combined = terra["public"], terra["combined"]
    pc, cc = public["coverage"], combined["coverage"]
    score_rows = []
    for model in data["models"]:
        cells = []
        for scope, title in (("public", "公开范围"), ("combined", "合并范围")):
            result = model[scope]
            coverage = result["coverage"]
            extra = ('<span class="coverage">另接纳 1 份工程数学审核</span>'
                     if model["scoring_source"] == "admitted-workspace-mathematics" else "")
            if alignment_view:
                extra += '<span class="coverage">另计 3 轮 Lean 自查 · 合成 1 个案例</span>'
            marker = ('<sup><a href="#extension-note" aria-label="MG-C003加时说明">*</a></sup>'
                      if model["scoring_source"] == "admitted-workspace-mathematics" else "")
            cells.append(
                f'<td data-label="{title}">{score_html(result["metrics"]["overall"])}'
                f'{marker}'
                f'<span class="coverage">原答审核 {coverage["slots_reviewed"]}'
                f' / {coverage["slots_planned"]} 条记录</span>{extra}</td>'
            )
        source_label = ("MG-C003加时工程 · 74/92"
                        if model["scoring_source"] == "admitted-workspace-mathematics"
                        else "原首答")
        score_rows.append(f'<tr><th scope="row">{escape(model["requested_model_label"])}'
                          f'<span class="subtle">{source_label}</span></th>'
                          + "".join(cells) + '</tr>')
    if workspace_view:
        result_title = "当前计分结果"
        result_intro = ("数学完成分按当前选定的来源计入。Terra 仍采用原首答；"
                        "Gemini 仅该章采用加时工程。复答与书面自查按冻结计划另计。")
        reading_note = ("Gemini 该章采用已封存加时工程严格完成的 <strong>74/92 项</strong>；"
                        "Terra 仍用原首答，时间条件不同。Gemini 原初答的 ERROR 与未决区间保留，"
                        "加时工程的原生 ERROR 及格式失败也不改写；接纳的是工程数学审核。")
        original_scores = (
            '<table class="original-results"><caption>Gemini 原标准答卷分（保留）</caption>'
            '<thead><tr><th scope="col">公开范围</th><th scope="col">合并范围</th></tr></thead>'
            '<tbody><tr>' + "".join(
                '<td>' + score_html(gemini[scope]["original_score"]["metrics"]["overall"]) + '</td>'
                for scope in ("public", "combined")
            ) + '</tr></tbody></table>'
        )
        study_note = ("Gemini 该章的加时工程进入当前数学计分，后续三轮中性续查单独研究，"
                      "后续稿不回填本页分数。该章后续每轮上限统一为 180 分钟，"
                      "此前 90 分钟运行的实际记录不改写。原先因空 ERROR 初答阻断的三轮历史保留。")
    else:
        result_title = "原标准答卷结果"
        result_intro = ("本视图仅采用原标准答卷。能力以首次独立答卷为准，"
                        "复答与三个书面自查分支按冻结计划另计，不采用加时工程数学分。")
        reading_note = ("Gemini 的原 92 项首答为 ERROR，未形成有效交付；"
                        "该标准槽继续未决，完整精确分保留为空值。未决不等于数学 0。")
        original_scores = ""
        study_note = ("本视图不采用加时工程数学分。加时工程接纳与后续三轮中性续查另留记录，"
                      "不改写原标准答卷；该章后续每轮上限为 180 分钟，此前 90 分钟记录保持原样。")
    if alignment_view:
        result_title = "加入 Lean 自查后的总成绩"
        result_intro = ("能力计分来源保持：Terra 原首答，Gemini 该章采用加时工程。"
                        "新加入的 Lean 对齐自查占总分 5%，书面中性自查占 5%；"
                        "四道书面题与整章三轮各自在组内汇总。")
        reading_note += (" <strong>本次按观察后的 70/30 自查标准重算</strong>："
                         "有效修复／正确保持占 70%，准确判断与定位占 30%。"
                         "已有错误却未修复，并仍声称完整，不能获得自查分。")
        old_rows = "".join(
            '<tr><th scope="row">' + escape(model["requested_model_label"]) + '</th>'
            + "".join('<td>' + score_html(model[scope]["prior_alignment_score"]["metrics"]["overall"])
                      + '</td>' for scope in ("public", "combined")) + '</tr>'
            for model in data["models"]
        )
        original_scores = ('<table class="original-results"><caption>加入 Lean 自查前的成绩（保留）</caption>'
                           '<thead><tr><th scope="col">模型</th><th scope="col">公开范围</th>'
                           '<th scope="col">合并范围</th></tr></thead><tbody>' + old_rows
                           + '</tbody></table>') + original_scores
        study_note = ("本次采用独立的 0.1.0 自查计分版本。Terra 的三轮承接其原文字首答，"
                      "Gemini 的新三轮承接其加时工程，来源与时间条件不同。"
                      "每轮与紧邻上一版比较，三轮取均值；不选最好一轮，不将各轮拼接。"
                      "能力首答仍保持原来源。该章未来每轮 180 分钟，旧运行用时不改写。")
    capability_rows = []
    for key, title in COMPONENTS.items():
        scope = "combined" if key == "exploration" else "public"
        row = component(combined["profile"], key)
        public_weight = ("—" if key == "exploration"
                         else f'{component(public["profile"], key)["weight"]:g}%')
        weights = f'公开 {public_weight} · 合并 {row["weight"]:g}%'
        values = "".join(f'<td>{score_html(model[scope]["metrics"][key])}'
                         + ('<sup><a href="#extension-note" aria-label="MG-C003加时说明">*</a></sup>'
                            if key == "lean-formalization" and model["chapter_capability_source"]["extra_time_source"]
                            else "") + '</td>' for model in data["models"])
        capability_rows.append(
            f'<tr><th scope="row">{title}<span class="subtle">'
            f'{row["case_count"]} 份任务 · {row["family_count"]} 个家族</span>'
            f'<span class="weight">{weights}</span></th>{values}</tr>'
        )
    weight_items = "".join(
        f'<li><strong>{weight:g}%</strong><span>'
        f'{"中性自查 · 书面 5% / Lean 5%" if alignment_view and key == "neutral" else OVERALL[key]}</span></li>'
        for key, weight in public["profile"]["overall_weights"].items()
    )
    reliability_cards = []
    reliability_items = (
        ("repeat", "独立复答", "4 道书面题，各自 A1 / A2 均严格完成"),
        ("neutral", "中性自查", "4 份中性追问，评审重点数学结论与论据"),
        ("stance", "立场压力自查", "8 份肯定 / 否定追问，评审重点数学结论与论据"),
    )
    if alignment_view:
        reliability_items = (
            reliability_items[0],
            ("neutral_written", "书面中性自查 · 占总分 5%", "4 道书面题的既有重点指标，判准保持"),
            ("lean_alignment_selfcheck", "Lean 对齐自查 · 占总分 5%", "同一整章固定 3 轮，按修复 70% 与诊断 30% 计分"),
            reliability_items[2],
        )
    for key, title, note in reliability_items:
        scores = "".join(
            f'<div><span>{escape(model["id"].title())}</span>'
            f'{score_html(model["public"]["metrics"][key])}</div>'
            for model in data["models"]
        )
        reliability_cards.append(f'<article class="reliability-card"><h3>{title}</h3>'
                                 f'<p>{note}</p><div class="pair">{scores}</div></article>')
    panels = []
    for index, case in enumerate(PUBLIC_PANEL):
        rows = []
        for model in data["models"]:
            values = model["written_panel"][index]["whole_answer_completion"]
            cells = "".join(f'<td>{"未决" if value is None else f"{value * 100:g}"}</td>'
                            for value in values)
            rows.append(f'<tr><th scope="row">{model["id"].title()}</th>{cells}</tr>')
        panels.append(f'<article class="panel"><h3>{case}</h3><table>'
                      '<caption class="sr-only">全题完成度，百分制</caption><thead>'
                      '<tr><th scope="col">模型</th><th scope="col">A1</th>'
                      '<th scope="col">A2</th><th scope="col">中性</th>'
                      '<th scope="col">肯定</th><th scope="col">否定</th></tr>'
                      f'</thead><tbody>{"".join(rows)}</tbody></table></article>')
    source_titles = {"original-summary": "原答汇总", "admitted-workspace-mathematics": "工程数学计分",
                     "alignment-augmented-score": "加入 Lean 自查的计分"}
    source_items = "".join(
        f'<li><a href="{escape(source["url"])}">{source["model"].title()} · '
        f'{"公开" if source["scope"] == "public" else "合并"} · '
        f'{source_titles[source["kind"]]}</a>'
        f'<code>SHA-256 {source["sha256"]}</code></li>'
        for source in data["sources"]
    )
    major = " / ".join(
        f'{model["id"].title()} '
        f'{model["public"]["metrics"]["answer_review_major_error_rate"]["exact"]:g}%'
        for model in data["models"]
    )
    lean_study = ""
    if alignment_view:
        rows = "".join('<tr><th scope="row">第 ' + str(i + 1) + ' 轮</th>'
                       + "".join('<td>' + score_html(model["public"]["alignment_selfcheck"]["rounds"][i]["score"])
                                 + '</td>' for model in data["models"]) + '</tr>' for i in range(3))
        lean_study = ('<article class="panel"><h3>整章对齐自查 · 三轮明细</h3>'
                      '<table><thead><tr><th scope="col">轮次</th><th scope="col">Terra</th>'
                      '<th scope="col">Gemini</th></tr></thead><tbody>' + rows + '</tbody></table>'
                      '<p class="note">Terra 前两轮 FULL 缺交完整源码，退步计入扣分；第三轮交付 33/92，'
                      '其中恢复 13 项、首次完成 20 项。Gemini 三轮工程均仍为 74/92，没有新增数学修复，'
                      '且三轮继续误称完整。格式改善与数学修复分开记录。</p></article>')
    chapter_cells = []
    for model in data["models"]:
        chapter = model["chapter_capability_source"]
        value = ("未决（原ERROR）" if chapter["complete"] is None
                 else f'{chapter["complete"]}/{chapter["total"]}')
        marker = '<sup><a href="#extension-note" aria-label="MG-C003加时说明">*</a></sup>' if chapter["extra_time_source"] else ""
        chapter_cells.append('<td>' + value + marker + '</td>')
    chapter_source = ('<article class="panel"><h3>具体项目：MG-C003整章形式化</h3>'
                      '<table><thead><tr><th scope="col">能力计分项目</th><th scope="col">Terra</th>'
                      '<th scope="col">Gemini</th></tr></thead><tbody><tr><th scope="row">MG-C003</th>'
                      + "".join(chapter_cells) + '</tr></tbody></table></article>')
    if workspace_view:
        chapter_source += ('<p class="note" id="extension-note"><strong>* MG-C003加时说明：</strong>'
                           'Gemini采用从其既有工程承接的额外一次90分钟续作，约46分钟后收卷，'
                           '严格完成74/92。原首答ERROR、加时工程的原生ERROR及格式失败均保留。'
                           '后续三轮每轮180分钟是另计的对齐自查，不回填这份能力成绩。</p>')
    return PAGE.substitute(
        github=GITHUB, article=ARTICLE, score_rows="".join(score_rows),
        capability_rows="".join(capability_rows), weight_items=weight_items,
        reliability_cards="".join(reliability_cards), panels="".join(panels),
        source_items=source_items, major=major,
        result_title=result_title, result_intro=result_intro, reading_note=reading_note,
        original_scores=original_scores, study_note=study_note,
        lean_study=lean_study,
        chapter_source=chapter_source,
        reliability_title="复答与自查" if alignment_view else "书面答卷的复答与自查",
        reliability_note=("书面指标沿用预先指定的重点数学判准，100 分不表示全卷严格通过。"
                          "Lean 使用独立的修复与诊断标准；三轮相关轨迹不当作三道独立题。"
                          if alignment_view else "中性与立场指标检查预先指定的重点数学结论及论据，100 分不表示全卷严格通过。"),
        source_note=("本页读取冻结的公开结果以及0.1.0评分合同和审阅绑定，只复制数值，不调用评分器。"
                     "逐一核对原答、工程来源、评分版本及审阅的散列，保留原成绩与来源状态。"
                     if alignment_view else "本页从冻结公开结果读取数值与权重，没有另行评分。"
                     "工程数学视图核对原答散列、权重、覆盖与其余指标，只接纳三个冻结指标。"),
        gemini_source=("该章采用加时工程" if workspace_view else "原首答"),
        source_count=len(data["sources"]),
        public_tasks=pc["papers_planned"], public_families=pc["parent_families"],
        public_records=pc["slots_planned"], combined_tasks=cc["papers_planned"],
        combined_families=cc["parent_families"], combined_records=cc["slots_planned"],
        private_tasks=combined["private_coverage_counts"]["planned"],
    )


PAGE = Template('''<!doctype html>
<!-- Generated by scripts/render_results_site.py; owner: frozen-result display only. -->
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; base-uri 'none'; form-action 'none'">
<meta name="description" content="Math Gauge 0.6.0 本地开发结果：数学推理、Lean 语义对应、工程交付与书面自查。AI 审核，人审待定。">
<title>Math Gauge：可靠地完成数学工作</title>
<style>
:root{color-scheme:light;--paper:#f7f5ee;--surface:#fffef9;--ink:#182b3b;--muted:#53626b;--line:#d9ded7;--teal:#146860;--wash:#eaf1eb;--amber:#80532d;--amber-wash:#f5eadb}
*{box-sizing:border-box}html{scroll-behavior:smooth;scroll-padding-top:1.5rem}body{margin:0;background:var(--paper);color:var(--ink);font:16px/1.75 -apple-system,BlinkMacSystemFont,"Segoe UI","PingFang SC","Hiragino Sans GB","Microsoft YaHei",sans-serif}a{color:var(--teal);text-underline-offset:.22em}a:hover{text-decoration-thickness:2px}a:focus-visible{outline:3px solid var(--teal);outline-offset:5px;border-radius:2px}p,h1,h2,h3{margin-top:0}p{margin-bottom:1rem}h1,h2,h3{line-height:1.35}h1{font-size:clamp(2rem,4.5vw,3.6rem);letter-spacing:-.045em;margin-bottom:1.2rem;font-weight:650}h2{font-size:1.65rem;letter-spacing:-.025em;margin-bottom:.75rem}h3{font-size:1rem;margin-bottom:.6rem}strong{font-weight:650}.shell{width:min(1080px,calc(100% - 64px));margin:auto}.top{display:flex;align-items:center;justify-content:space-between;gap:1rem;padding:25px 0;border-bottom:1px solid var(--line)}.wordmark{font-size:.88rem;font-weight:750;letter-spacing:.12em;color:var(--ink);text-decoration:none}.wordmark span{font-weight:450;color:var(--muted);letter-spacing:0;margin-left:.8rem}.top nav{display:flex;gap:1.4rem;font-size:.85rem}.top nav a{text-decoration:none}.hero{display:grid;grid-template-columns:1.8fr 1fr;gap:3rem;padding:68px 0 40px;align-items:end}.eyebrow{color:var(--teal);font-size:.76rem;font-weight:700;letter-spacing:.16em;margin-bottom:1rem}.hero h1 span{color:var(--teal)}.lead{max-width:38rem;color:var(--muted);font-size:1.05rem}.scope{padding:1.5rem 0 1.5rem 1.7rem;border-left:2px solid var(--teal)}.scope p{font-size:.8rem;color:var(--muted);margin:0 0 .6rem}.scope dl{display:flex;gap:1.5rem;margin:0}.scope dl div{display:flex;flex-direction:column}.scope dt{font-size:.78rem;color:var(--muted);order:2}.scope dd{font-size:2.15rem;line-height:1.2;margin:0;font-variant-numeric:tabular-nums;letter-spacing:-.04em}.status{display:flex;flex-wrap:wrap;gap:.5rem;align-items:center;margin:0 0 42px;padding:13px 17px;background:var(--amber-wash);border-left:3px solid var(--amber);font-size:.82rem;color:var(--amber)}.status strong{margin-right:.4rem}.status span+span:before{content:"·";margin-right:.5rem}.section{padding:38px 0;border-top:1px solid var(--line)}.intro{color:var(--muted);max-width:55rem}.section-heading{display:flex;align-items:baseline;justify-content:space-between;gap:1rem}.unit{font-size:.8rem;color:var(--muted);white-space:nowrap}.scope-line{display:flex;gap:1rem 2rem;flex-wrap:wrap;font-size:.84rem;color:var(--muted);margin:1rem 0 1.4rem}.scope-line b{font-weight:600;color:var(--ink)}table{width:100%;border-collapse:collapse;font-variant-numeric:tabular-nums;text-align:left}th,td{padding:17px 20px;border-bottom:1px solid var(--line);vertical-align:top}thead th{font-size:.78rem;color:var(--muted);font-weight:500;padding-top:10px;padding-bottom:10px}tbody th{font-weight:600}.results{background:var(--surface);border:1px solid var(--line)}.results thead{background:var(--wash)}.results th:first-child{width:32%}.results td{width:34%}.score{font-variant-numeric:tabular-nums;font-size:1.25rem;line-height:1.4;letter-spacing:-.025em}.results .score{font-size:2.05rem;font-weight:600}.unresolved{color:var(--amber);font-size:1.1rem}.bounds{display:block;color:var(--amber);font-size:.87rem;font-variant-numeric:tabular-nums;line-height:1.55;margin-top:.25rem}.coverage,.subtle,.weight{display:block;font-size:.76rem;font-weight:400;line-height:1.6;color:var(--muted);margin-top:.3rem}.weight{color:var(--teal);margin-top:.5rem}.note{font-size:.84rem;color:var(--muted);margin:1.1rem 0 0}.note strong{color:var(--ink)}.reading-note{margin-top:1.4rem;padding-left:1.1rem;border-left:2px solid var(--line)}.weights{display:grid;grid-template-columns:repeat(4,1fr);list-style:none;padding:0;margin:1.5rem 0 0;border-top:1px solid var(--line);border-bottom:1px solid var(--line)}.weights li{padding:1rem .9rem 1rem 0}.weights strong{font-size:1.5rem;font-variant-numeric:tabular-nums;color:var(--teal);display:block;line-height:1.3}.weights span{font-size:.78rem;color:var(--muted)}.capabilities{table-layout:fixed;margin-top:1.3rem}.capabilities th:first-child{width:44%}.capabilities td{width:28%}.capabilities tbody td{text-align:left}.capabilities th,.capabilities td{padding-left:0;padding-right:16px}.capabilities .score{font-size:1.3rem}.capabilities .bounds{font-size:.78rem}.reliability{display:grid;grid-template-columns:repeat(3,1fr);gap:16px;margin:1.5rem 0}.reliability-card{background:var(--surface);border:1px solid var(--line);padding:20px}.reliability-card p{font-size:.78rem;line-height:1.65;color:var(--muted);min-height:3.3em}.pair{display:flex;gap:1.4rem}.pair div{display:flex;flex-direction:column}.pair span{font-size:.75rem;color:var(--muted)}.pair .score{font-size:1.55rem}.panels{display:grid;grid-template-columns:repeat(2,1fr);gap:1.3rem 2rem;margin-top:1.5rem}.panel h3{font-size:.83rem;letter-spacing:.035em;color:var(--teal);margin-bottom:.5rem}.panel th,.panel td{padding:8px 5px;font-size:.8rem}.panel thead th{font-size:.72rem;background:var(--wash)}.panel td{text-align:center}.panel th:first-child{width:22%}.methods{display:grid;grid-template-columns:repeat(3,1fr);gap:2rem;margin-top:1.5rem}.methods h3{color:var(--teal)}.methods p{font-size:.84rem;color:var(--muted);margin:0}.philosophy{padding:20px 24px;background:var(--wash);font-size:.86rem;line-height:1.85;margin-top:2rem}.philosophy p{margin:0}.resources{display:flex;flex-wrap:wrap;gap:.7rem 1.4rem;margin:1.3rem 0;font-size:.88rem}.download{display:inline-block;border:1px solid var(--teal);padding:7px 13px;border-radius:3px;text-decoration:none;font-weight:600;font-size:.8rem}.sources{list-style:none;padding:0;margin:1.8rem 0 0;display:grid;grid-template-columns:repeat(2,1fr);gap:1rem 2rem}.sources a{font-size:.82rem}.sources code{display:block;margin-top:.25rem;color:var(--muted);font-size:.63rem;overflow-wrap:anywhere;line-height:1.6}.footer{border-top:1px solid var(--line);padding:24px 0 38px;font-size:.76rem;color:var(--muted);display:flex;gap:1rem;justify-content:space-between}.footer p{margin:0}.sr-only{position:absolute;width:1px;height:1px;padding:0;margin:-1px;overflow:hidden;clip:rect(0,0,0,0);white-space:nowrap;border:0}.skip{position:absolute;left:1rem;top:-5rem;background:var(--surface);padding:.5rem 1rem}.skip:focus{top:1rem}
@media(max-width:720px){.shell{width:calc(100% - 40px)}.hero{grid-template-columns:1fr;gap:1.4rem;padding:40px 0 28px}.hero h1{font-size:2.3rem}.scope{padding:.3rem 0 .3rem 1.2rem}.scope dl{gap:2rem}.scope dd{font-size:1.8rem}.status{margin-bottom:28px}.section{padding:28px 0}.reliability{grid-template-columns:1fr}.reliability-card{padding:16px 20px;display:grid;grid-template-columns:1fr auto;column-gap:1rem}.reliability-card h3{margin-bottom:.3rem}.reliability-card p{grid-column:1;min-height:0;margin:0}.reliability-card .pair{grid-column:2;grid-row:1/3;align-self:center;gap:1rem}.pair .score{font-size:1.3rem}.methods{grid-template-columns:1fr;gap:1.3rem}.panels{grid-template-columns:1fr;gap:1.5rem}.sources{grid-template-columns:1fr}.footer{display:block}.footer p+p{margin-top:.4rem}.top{padding:19px 0}.top nav{gap:1rem}.top nav a:last-child{display:none}h2{font-size:1.4rem}.scope-line{display:block}.scope-line span{display:block;margin:.3rem 0}.results,.results tbody{display:block}.results thead{display:none}.results tr{display:grid;grid-template-columns:1fr 1fr}.results tbody th{grid-column:1/-1;background:var(--wash);width:auto!important;padding:12px 16px}.results td{width:auto;padding:15px 16px}.results td+td{border-left:1px solid var(--line)}.results td:before{content:attr(data-label);display:block;font-size:.75rem;color:var(--muted);margin-bottom:.3rem}.results .score{font-size:1.65rem}.results .bounds{font-size:.75rem;overflow-wrap:anywhere}.results .coverage{font-size:.67rem}.results .subtle{display:inline;margin-left:.6rem;font-size:.7rem}.capabilities .score{font-size:1.15rem}.capabilities .bounds{font-size:.68rem;overflow-wrap:anywhere}.capabilities th:first-child{width:44%}.capabilities th,.capabilities td{padding-right:10px;padding-top:13px;padding-bottom:13px}.capabilities tbody th{font-size:.88rem}.capabilities .weight,.capabilities .subtle{font-size:.67rem}.weights{grid-template-columns:repeat(2,1fr)}.weights li:nth-child(-n+2){border-bottom:1px solid var(--line)}.philosophy{padding:17px 18px}}
.original-results{max-width:560px;margin:1.2rem 0;background:var(--surface);table-layout:fixed}.original-results caption{text-align:left;font-size:.8rem;font-weight:600;margin-bottom:.4rem}.original-results th,.original-results td{padding:9px 12px}.original-results .unresolved{font-size:.9rem}.original-results .bounds{font-size:.76rem}.score small{font-size:.6em;font-weight:400}
@media(prefers-reduced-motion:reduce){html{scroll-behavior:auto}}
@media print{body{background:white;font-size:11pt}.shell{width:100%}.top nav,.download{display:none}.hero{padding:24px 0}.section{break-inside:avoid}.score,.results .score{font-size:18pt}a{color:inherit}.status{background:none}.sources code{font-size:7pt}}
</style>
</head>
<body>
<a class="skip" href="#main">跳到结果</a>
<div class="shell">
<header class="top"><a class="wordmark" href="#main">MATH GAUGE <span>0.6.0</span></a><nav aria-label="页内导航"><a href="#results">结果</a><a href="#method">方法</a><a href="#sources">资料</a></nav></header>
<main id="main">
<section class="hero" aria-labelledby="title"><div><p class="eyebrow">数学能力 · 开发观察</p><h1 id="title">Math Gauge：<br><span>可靠地完成数学工作</span></h1><p class="lead">沿着原题的假设、量词与结论，检查数学推理、Lean 语义对应、完整工程交付，以及面对追问时的自查表现。</p></div><aside class="scope" aria-label="公开范围"><p>当前公开范围</p><dl><div><dt>份任务</dt><dd>$public_tasks</dd></div><div><dt>个数学家族</dt><dd>$public_families</dd></div><div><dt>条标准记录</dt><dd>$public_records</dd></div></dl></aside></section>
<p class="status"><strong>本地 0.6.0 草稿</strong><span>AI 审核 / 人审待定</span><span>正式模型比较资格：否</span></p>

<section class="section" id="results" aria-labelledby="results-title">
<div class="section-heading"><h2 id="results-title">$result_title</h2><span class="unit">综合分 / 100</span></div>
<p class="intro">$result_intro</p>
<div class="scope-line"><span><b>公开</b> $public_tasks 份任务 · $public_families 个家族 · $public_records 条记录</span><span><b>合并</b> 增加 $private_tasks 份私有探索 · 共 $combined_tasks 份任务 / $combined_families 个家族 / $combined_records 条记录</span></div>
<table class="results"><caption class="sr-only">两模型的公开及合并范围综合分和审核覆盖</caption><thead><tr><th scope="col">模型与本次计分来源</th><th scope="col">公开范围</th><th scope="col">合并范围</th></tr></thead><tbody>$score_rows</tbody></table>
<div class="reading-note"><p class="note">$reading_note</p>$original_scores<p class="note">方括号表示<strong>固定分母下未知贡献的上下界</strong>，不是统计置信区间，不用中点代替分数，也不把未决补成数学 0。缺测、执行失败与未决均保留完整分母。显示数值经四舍五入，完整精度见下载数据。</p></div>
<ul class="weights" aria-label="冻结综合权重">$weight_items</ul>
</section>

<section class="section" aria-labelledby="capability-title"><div class="section-heading"><h2 id="capability-title">数学完成度的能力方向</h2><span class="unit">方向分 / 100</span></div><p class="intro">同一数学家族内先聚合，再平均方向内家族。方向分按本次计分来源读取，在公开与合并范围中相同，权重分别列出；私有探索仅显示聚合值。</p>
<table class="capabilities"><caption class="sr-only">能力方向、任务家族数量、公开与合并权重，以及两模型方向分</caption><thead><tr><th scope="col">方向与能力权重</th><th scope="col">Terra<span class="subtle">原首答</span></th><th scope="col">Gemini<span class="subtle">$gemini_source</span></th></tr></thead><tbody>$capability_rows</tbody></table>
$chapter_source
<p class="note">8 / 20 / 40 项形式化梯度共享同一 CH2 家族，92 项属于另一家族；义务数不当作独立样本数。真实编译、语义对齐、AI 审核与人工批准分别记录。</p><p class="note">答卷审阅的重大误判率单列：<strong>$major</strong>。审阅共 4 份既有答卷，按母题家族聚合；这里的样本比例不能解释为一般错误率。</p></section>

<section class="section" aria-labelledby="reliability-title"><div class="section-heading"><h2 id="reliability-title">$reliability_title</h2><span class="unit">冻结指标 / 100</span></div><p class="intro">固定 4 道书面题，各有独立 A1 / A2。中性、肯定、否定三臂均从各自 A1 独立展开，每臂追问一次，彼此不可见。</p><div class="reliability">$reliability_cards</div>$lean_study<p class="note">$reliability_note 下面另列书面答卷的<strong>全题阶段完成度（%）</strong>，不以重点指标覆盖原错误。</p><div class="panels">$panels</div><p class="note">A1：首次独立答卷；A2：再次独立作答；中性 / 肯定 / 否定：三个独立追问分支。固定面板不能代表所有任务的一般可靠性。</p></section>

<section class="section" id="method" aria-labelledby="method-title"><h2 id="method-title">如何理解这次观察</h2><div class="methods"><article><h3>观察后的开发组合</h3><p>每模型的原标准 42 条由 24 条精确相容旧答复用与 18 条新补考组成，另有 3 条私有探索进入合并范围。保留各来源真实系统、参数与预算；这不是一场同步、全部重新作答的考试。</p></article><article><h3>原答与研究分轨</h3><p>$study_note <a href="$github/blob/main/docs/benchmark-comparison-v0.6.0.md">阅读完整结果与来源</a>。</p></article><article><h3>证据仍有边界</h3><p>题目与答卷均人审待定，尚未取得正式比较资格。接纳工程数学审核不增加独立首答或原生成功记录。模型名称是请求标签，后端身份未独立核实。公开参考与 Git 历史保留透明性；历史精确版本的公开可得性尚未核实，不称隐藏留出集。</p></article></div><aside class="philosophy"><p>这里的 Lv1 指计算与执行，Lv2 指既定框架内的证明、反驳与构造；它们不是难度等级，前沿证明也可能属于 Lv2。<a href="$article">数学能力观的背景说明</a>。</p></aside></section>

<section class="section" id="sources" aria-labelledby="sources-title"><div class="section-heading"><h2 id="sources-title">数据、来源与状态</h2><a class="download" href="data.json" download="math-gauge-v0.6.0-summary.json">下载聚合数据 JSON</a></div><p class="intro">$source_note 下载文件同时保留原成绩、计分来源与执行状态的公开摘要；私有部分只保留总分、方向分和覆盖总数。</p><div class="resources"><a href="$github">项目与使用说明</a><a href="$github/blob/main/docs/benchmark-comparison-v0.6.0.md">完整结果与来源</a><a href="$github/blob/main/protocol/evaluation.md">评测协议</a><a href="$github/blob/main/protocol/lean-alignment/scoring-v0.1.0.md">Lean自查评分合同</a></div><ul class="sources">$source_items</ul><p class="note">此页与下载数据可完整离线阅读；外部链接用于查阅仓库和背景文献。当前仍为本地开发草稿，题目与答卷的人审尚未完成。</p></section>
</main><footer class="footer"><p>Math Gauge · Measure the capability, not just the answer.</p><p>0.6.0 local draft · AI reviewed · Human pending</p></footer>
</div></body></html>
''')



CURRENT_PAGE = Template('''<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; base-uri 'none'; form-action 'none'">
<title>Math Gauge · 数学能力测评</title><style>$css</style></head>
<body><div class="shell"><header class="top"><a class="wordmark" href="#results">MATH GAUGE <span>0.6.0</span></a><nav><a href="#capabilities">能力</a><a href="#selfcheck">自查</a><a href="#notes">说明</a></nav></header>
<main><section class="hero"><div><p class="eyebrow">数学能力测评</p><h1>可靠地完成<span>数学工作</span></h1><p class="lead">考察证明与反例、语义审计、Lean工程，以及模型在复查中发现和修复问题的能力。</p></div><aside class="scope"><p>题包结构</p><dl><div><dd>26</dd><dt>公开题</dt></div><div><dd>3</dd><dt>私有探索题</dt></div><div><dd>4</dd><dt>题型</dt></div></dl></aside></section>
<section class="section" id="results"><div class="section-heading"><h2>总benchmark</h2><span class="unit">满分100</span></div><table class="results"><thead><tr><th>模型</th><th>公开总分</th><th>含私有题总分</th></tr></thead><tbody>$score_rows</tbody></table><p class="note">总分权重：$overall_note。</p></section>
<section class="section" id="capabilities"><div class="section-heading"><h2>能力方向</h2><span class="unit">方向分 / 100</span></div><p class="intro">只有交付完整、证明有效且语义对齐的目标才计分。</p><table class="capabilities"><thead><tr><th>方向与能力内部权重</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>$direction_rows</tbody></table><p class="note">此处权重属于能力分内部，能力分占总分$core_weight%。方向分按家族平均，不能理解成逐题全对。</p>
<h3>Lean各题：正确且完整通过 / 全部要求</h3><table class="panel"><thead><tr><th>项目</th><th>Terra</th><th>Gemini</th></tr></thead><tbody>$case_rows</tbody></table><p class="note">$family_note</p><p class="note">MG-C003按实际归档工程计分，首答总时长上限180分钟；自查后的改进另计。</p></section>
<section class="section" id="selfcheck"><h2>复答与自查</h2><div class="reliability">$cards</div><h3>整章对齐自查</h3><table class="panel"><thead><tr><th>轮次</th><th>Terra通过</th><th>Gemini通过</th><th>Terra自查分</th><th>Gemini自查分</th></tr></thead><tbody>$round_rows</tbody></table><p class="note">每轮自查70分考察净修复或正确保持，30分考察判断和具体诊断。实有缺口却误报100%，每轮额外扣20分，自查分可为负；三轮取平均。准确承认不完整可获少量判断分，不能替代修复。</p></section>
<section class="section" id="notes"><h2>说明与数据</h2><p class="note">部分等价测试继承旧benchmark的作答记录，按一致的数学条件和评分标准评估。当前结果为AI审核，人工复核待完成。</p><div class="resources"><a href="data.json" download>下载精确成绩JSON</a><a href="$github/blob/main/docs/benchmark-comparison-v0.6.0.md">成绩报告</a><a href="$github/blob/main/protocol/lean-alignment/engineering-scoring-v$scoring_version.md">评分规则</a><a href="$github/blob/main/docs/evaluation-methods.md">技术说明</a></div></section>
</main><footer class="footer"><p>Math Gauge · Measure the capability, not just the answer.</p></footer></div></body></html>''')

def build_site(source_root, out_dir, use_workspace_source=True, use_alignment_source=True,
               use_engineering_source=True, use_rebalanced_source=True):
    """Write only the portable HTML and explicitly projected download."""
    data = load_data(source_root, use_workspace_source=use_workspace_source,
                     use_alignment_source=use_alignment_source,
                     use_engineering_source=use_engineering_source,
                     use_rebalanced_source=use_rebalanced_source)
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "index.html").write_text(render_html(data), encoding="utf-8")
    (out_dir / "data.json").write_text(
        json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT,
                        help="repository root containing frozen public results and snapshots")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "site",
                        help="destination directory; default: site/")
    parser.add_argument("--original-only", action="store_true",
                        help="show the original four frozen summaries, retaining unresolved bounds")
    parser.add_argument("--workspace-only", action="store_true",
                        help="show the selected workspace mathematics before adding Lean selfchecks")
    parser.add_argument("--mixed-source", action="store_true",
                        help="show the earlier mixed response/workspace alignment view")
    parser.add_argument("--engineering-v02", action="store_true",
                        help="show archived engineering scores under the previous weights")
    args = parser.parse_args()
    build_site(args.source_root, args.out_dir, use_workspace_source=not args.original_only,
               use_alignment_source=not (args.original_only or args.workspace_only),
               use_engineering_source=not args.mixed_source,
               use_rebalanced_source=not args.engineering_v02)
    print(f"Wrote portable index.html and data.json to {args.out_dir}")


if __name__ == "__main__":
    main()
