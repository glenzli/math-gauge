"""Validate complete mathematical goals, separate from fine content assertions.

Each goal is an independently acceptable source result. Its proof, scope and
representation requirements are acceptance conditions, not fractional goals.
This module owns evidence/contract validation; scoring.py owns all arithmetic.
"""
import hashlib
import json

from .content_rates import (
    CURRENT_VERSION, _CURRENT_BINDINGS, _META, _descriptor, _hash, _inventory,
    _keys, _metadata, _number, _policy_counts, _require, _source_task_identity,
    _text, validate_review,
)

SCHEMA = "math-gauge.goal-attainment-review/v1"
_IDENTITY = ("id", "case_id", "subcategory", "family_id", "kind", "measured")
_DEFINITION = (
    "id", "label", "statement", "scope", "weight", "weight_origin",
    "acceptance_conditions", "dependency_scope", "required_goals",
    "source_unit_ids", "definition_evidence",
)


def goal_contract(tasks):
    """Cross-model contract; excludes observations and candidate-specific evidence."""
    return [dict({key: task[key] for key in _IDENTITY if key != "measured"},
                 goals=[{key: goal[key] for key in _DEFINITION} for goal in task["goals"]])
            for task in sorted(tasks, key=lambda row: row["id"])]


def definition_digest(tasks):
    data = json.dumps(goal_contract(tasks), ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def validate_goal_review(review, content_review, assessment_policy, source_report=None):
    """Bind one complete-goal judgment to every selected task and fixed round.

    Passing requires a delivered result satisfying every acceptance condition.
    A necessary failed goal cannot be hidden by passing a dependent one. Human
    semantic review is still needed; a schema cannot establish proof correctness.
    """
    validate_review(content_review, assessment_policy, source_report)
    _metadata(review, SCHEMA, version=CURRENT_VERSION, bindings=_CURRENT_BINDINGS)
    _keys(review, _META | {"post_observation", "goal_definition_sha256", "tasks", "sources"},
          "goal review")
    _require(review["post_observation"] is True, "goal mapping is post-observation")
    _require(review["model_id"] == content_review["model_id"], "goal/content models differ")
    _hash(review["goal_definition_sha256"], "goal_definition_sha256")
    for key in ("record_sha256", "assessment_result_sha256", "assessment_policy_sha256"):
        _require(review["source_bindings"][key] == content_review["source_bindings"][key],
                 "goal/content source selection differs")
    _require(review["source_bindings"]["content_method_policy_sha256"]
             == content_review["source_bindings"]["method_policy_sha256"],
             "goal review binds another content method")
    tasks = review["tasks"]
    _require(isinstance(tasks, list), "goal tasks must be a list")
    originals = {task["id"]: task for task in content_review["tasks"]}
    _require(len(tasks) == len(originals) and {t.get("id") for t in tasks} == set(originals),
             "goal review must retain every selected task and prescribed round")
    for task in tasks:
        _keys(task, set(_IDENTITY) | {"goals"}, "goal task")
        original = originals[task["id"]]
        _require(all(task[key] == original[key] for key in _IDENTITY),
                 "goal task selection/measurement differs from source")
        goals = task["goals"]
        _require(isinstance(goals, list) and bool(goals), "task needs complete goals")
        _require(all(isinstance(g, dict) for g in goals), "goal must be an object")
        ids = [goal.get("id") for goal in goals]
        _require(len(set(ids)) == len(ids), "task repeats a goal")
        original_units = {unit["id"] for unit in original["units"]}
        by_id = {goal["id"]: goal for goal in goals}
        for goal in goals:
            _keys(goal, set(_DEFINITION) | {"passed", "reason", "evidence"}, "goal")
            for key in ("id", "label", "statement", "scope", "weight_origin"):
                _text(goal[key], "goal " + key)
            _number(goal["weight"], "goal weight")
            _require(goal["weight"] > 0, "complete goals need positive weights")
            for key in ("acceptance_conditions", "dependency_scope", "source_unit_ids", "required_goals"):
                _require(isinstance(goal[key], list), "goal " + key + " must be a list")
                for value in goal[key]:
                    _text(value, "goal " + key)
            _require(bool(goal["acceptance_conditions"]), "goal needs full acceptance conditions")
            _require(set(goal["source_unit_ids"]) <= original_units, "goal refers to unknown original units")
            _require(set(goal["required_goals"]) <= set(ids) - {goal["id"]},
                     "goal dependency is absent or self-referential")
            _require(goal["passed"] is None or type(goal["passed"]) is bool,
                     "goal passed must be boolean or unknown")
            _text(goal["reason"], "goal reason", empty=not task["measured"])
            if not task["measured"]:
                _require(goal["passed"] is None, "unrun goals must remain unknown")
            _require(isinstance(goal["evidence"], list), "goal evidence must be a list")
            _require(isinstance(goal["definition_evidence"], list)
                     and bool(goal["definition_evidence"]), "goal needs source definition evidence")
            for source in goal["evidence"] + goal["definition_evidence"]:
                _descriptor(source, evidence=True)
            if task["measured"]:
                _require(bool(goal["evidence"]), "reviewed goal needs candidate evidence")
            if goal["passed"] is True:
                _require(all(by_id[ident]["passed"] is True for ident in goal["required_goals"]),
                         "attained goal has an unmet necessary dependency")
        def visit(ident, trail):
            _require(ident not in trail, "goal dependency cycle")
            for dep in by_id[ident]["required_goals"]:
                visit(dep, trail | {ident})
        for ident in ids:
            visit(ident, set())
    _require(definition_digest(tasks) == review["goal_definition_sha256"],
             "goal definition digest differs")
    _policy_counts(tasks, assessment_policy)
    if source_report is not None:
        _source_task_identity(tasks, source_report)
    _inventory(review)
    return review
