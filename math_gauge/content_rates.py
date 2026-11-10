"""Validate content-rate evidence and project aggregate reports without scoring.

Usage::
    validate_review(review, assessment_policy=policy, source_report=assessment)
    verify_sources(review, {"public": public_root, "private": private_root})
    public_report = project_rates(private_report)
    validate_public_rates(public_report)

The caller owns score arithmetic and source-report selection. Public projection
never copies task rows, source paths, labels, reasons, or arbitrary nested keys.
One selfcheck task may contain the fixed three-round review, or the three rounds
may be separate tasks; unit/round grouping is frozen by the caller's method.
"""

import copy
import hashlib
import math
import os
from pathlib import Path, PurePosixPath
import re
import stat

REVIEW_SCHEMA = "math-gauge.content-rate-review/v1"
SCORE_SCHEMA = "math-gauge.content-rates/v1"
VERSION = "0.1.0"
CURRENT_VERSION = "0.2.0"
CURRENT_SCORE_SCHEMA = "math-gauge.content-rates/v2"
BENCHMARK_VERSION = "0.6.0"
CONDITION = "nonlogical_retry_3"
SUBCATEGORIES = (
    "written-argument", "argument-review", "lean-audit", "lean-formalization",
    "lean-selfcheck", "background-check", "manuscript-completion",
    "theorem-extension",
)
_BINDINGS = frozenset({"record_sha256", "assessment_result_sha256",
                       "assessment_policy_sha256", "method_policy_sha256"})
_CURRENT_BINDINGS = _BINDINGS | {"content_review_sha256", "content_method_policy_sha256"}
_META = frozenset({"schema", "version", "benchmark_version", "model_id",
                   "condition", "reviewer_kind", "human_review",
                   "formal_comparison_eligible", "new_candidate_calls",
                   "assessment_policy_sha256", "source_bindings"})
_PUBLIC = _META | {"metrics", "categories", "coverage", "private_review_sha256"}
_CURRENT_PUBLIC = _PUBLIC | {"private_goal_review_sha256", "goal_definition_sha256"}
_DELIVERY = frozenset({"exact", "confirmed", "lower", "upper",
                       "unknown_weight", "complete"})
_RELIABILITY = frozenset({"exact", "observed", "lower", "upper", "correct_weight",
                          "asserted_weight", "unknown_weight", "complete"})
_GLOBAL_COVERAGE = frozenset({
    "planned_initial_tasks", "reviewed_initial_tasks", "planned_selfcheck_rounds",
    "reviewed_selfcheck_rounds", "planned_unit_reviews", "reviewed_unit_reviews",
})
_CURRENT_COVERAGE = _GLOBAL_COVERAGE | {"planned_goals", "reviewed_goals"}
_CATEGORY_COVERAGE = frozenset({"planned_families", "reviewed_families",
                                "planned_tasks", "reviewed_tasks"})
_HEX = re.compile(r"[0-9a-fA-F]{64}\Z")
_MODEL = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]*\Z")


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _object(value, label):
    _require(isinstance(value, dict), f"{label} must be an object")
    return value


def _keys(value, required, label, optional=frozenset()):
    _object(value, label)
    _require(set(value) >= set(required), f"{label} is missing required fields")
    _require(set(value) <= set(required) | set(optional),
             f"{label} contains unsupported fields")


def _text(value, label, *, empty=False):
    _require(isinstance(value, str) and "\x00" not in value
             and (empty or bool(value.strip())), f"{label} must be text")


def _number(value, label, *, maximum=None):
    finite = type(value) is int or type(value) is float and math.isfinite(value)
    _require(finite and value >= 0,
             f"{label} must be a finite nonnegative number")
    if maximum is not None:
        _require(value <= maximum, f"{label} is above its maximum")


def _count(value, label):
    _require(type(value) is int and value >= 0, f"{label} must be a nonnegative integer")


def _hash(value, label):
    _require(isinstance(value, str) and _HEX.fullmatch(value),
             f"{label} must be a SHA256 hex digest")


def _metadata(data, schema, *, version=VERSION, bindings=_BINDINGS):
    _object(data, "report")
    _require(_META <= set(data), "report is missing metadata")
    for key, expected in (("schema", schema), ("version", version),
                          ("benchmark_version", BENCHMARK_VERSION),
                          ("condition", CONDITION), ("reviewer_kind", "ai"),
                          ("human_review", "pending")):
        _require(data[key] == expected, f"unsupported {key}")
    _require(data["formal_comparison_eligible"] is False,
             "content rates cannot upgrade comparison eligibility")
    _require(type(data["new_candidate_calls"]) is int and data["new_candidate_calls"] == 0,
             "content-rate review must not introduce candidate calls")
    _require(isinstance(data["model_id"], str) and _MODEL.fullmatch(data["model_id"]),
             "model_id must be a safe model identifier")
    _hash(data["assessment_policy_sha256"], "assessment_policy_sha256")
    _keys(data["source_bindings"], bindings, "source_bindings")
    for key, digest in data["source_bindings"].items():
        _hash(digest, f"source_bindings.{key}")
    _require(data["assessment_policy_sha256"].lower()
             == data["source_bindings"]["assessment_policy_sha256"].lower(),
             "assessment policy binding differs from metadata")


def _relative_path(value):
    _text(value, "source path")
    _require("\\" not in value and not any(ord(c) < 32 or ord(c) == 127 for c in value),
             "source path contains unsafe characters")
    path = PurePosixPath(value)
    _require(not path.is_absolute() and value == "/".join(path.parts)
             and all(part not in ("", ".", "..") for part in value.split("/"))
             and ":" not in value.split("/", 1)[0],
             "source path must be a canonical safe relative path")
    return path.parts


def _descriptor(source, *, evidence=False):
    required = {"repository", "path", "sha256"} | ({"pointer"} if evidence else set())
    _keys(source, required, "source descriptor")
    _require(source["repository"] in ("public", "private"), "unknown source repository")
    _relative_path(source["path"])
    _hash(source["sha256"], "source sha256")
    if evidence:
        _text(source["pointer"], "evidence pointer", empty=True)


def _inventory(review):
    _object(review, "review")
    _require(isinstance(review.get("sources"), list) and bool(review["sources"]),
             "review needs a nonempty source inventory")
    inventory = {}
    descriptors = [(s, False) for s in review["sources"]]
    _require(isinstance(review.get("tasks", []), list), "tasks must be a list")
    for task in review.get("tasks", []):
        _object(task, "task")
        units = task.get("goals", task.get("units", []))
        _require(isinstance(units, list), "units/goals must be a list")
        for unit in units:
            _object(unit, "unit")
            _require(isinstance(unit.get("evidence", []), list), "evidence must be a list")
            descriptors.extend((s, True) for s in unit.get("evidence", []))
            descriptors.extend((s, True) for s in unit.get("definition_evidence", []))
    for source, is_evidence in descriptors:
        _descriptor(source, evidence=is_evidence)
        key = (source["repository"], source["path"])
        digest = source["sha256"].lower()
        _require(key not in inventory or inventory[key] == digest,
                 "conflicting SHA256 bindings for the same source")
        inventory[key] = digest
    return inventory


def _policy_counts(tasks, policy):
    _object(policy, "assessment_policy")
    _require(policy.get("benchmark_version") == BENCHMARK_VERSION,
             "assessment policy benchmark version differs")
    scope = _object(policy.get("scope"), "assessment policy scope")
    initial = [t for t in tasks if t["kind"] == "initial"]
    rounds = [t for t in tasks if t["kind"] == "selfcheck"]
    _require(len(initial) == scope.get("initial_slots", scope.get("tasks")),
             "initial task count differs from assessment policy")
    _require(len(rounds) in {1, scope.get("alignment_rounds", 3)},
             "selfcheck representation differs from assessment policy")
    children = policy.get("subcategories")
    _require(isinstance(children, list), "assessment policy needs subcategories")
    _require(len(children) == len(SUBCATEGORIES)
             and {c.get("id") for c in children} == set(SUBCATEGORIES),
             "assessment policy subcategories differ")
    for child in children:
        category = child["id"]
        rows = [t for t in tasks if t["subcategory"] == category]
        if child.get("aggregation") == "trajectory":
            _require(all(t["kind"] == "selfcheck" for t in rows),
                     "trajectory category contains initial tasks")
            _require(len(rows) in {1, child.get("rounds", scope.get("alignment_rounds", 3))},
                     "trajectory round count differs")
            if child.get("reuses_case_id") is not None:
                _require(all(t["case_id"] == child["reuses_case_id"] for t in rows),
                         "selfcheck does not reuse the policy case")
        else:
            _require(all(t["kind"] == "initial" for t in rows),
                     "ordinary category contains a selfcheck task")
            expected = child.get("public_tasks", 0) + child.get("private_tasks", 0)
            _require(len(rows) == expected, "subcategory task count differs from policy")
        _require(len({t["family_id"] for t in rows}) == child.get("families"),
                 "subcategory family count differs from policy")
    if scope.get("parent_families") is not None:
        _require(len({t["family_id"] for t in tasks}) == scope["parent_families"],
                 "global family count differs from policy")


def _source_task_identity(tasks, source_report):
    _object(source_report, "source_report")
    if source_report.get("benchmark_version") is not None:
        _require(source_report["benchmark_version"] == BENCHMARK_VERSION,
                 "source report benchmark version differs")
    if source_report.get("attempt_condition") is not None:
        _require(source_report["attempt_condition"] == CONDITION,
                 "source report uses another attempt condition")
    source_tasks = source_report.get("tasks")
    _require(isinstance(source_tasks, list), "source report needs task identities")
    original = {}
    for task in source_tasks:
        if task.get("kind") == "selfcheck" or task.get("subcategory") == "lean-selfcheck":
            continue
        sid = task.get("slot_id", task.get("id"))
        _text(sid, "source task id")
        _require(sid not in original, "source report repeats a task id")
        original[sid] = task
    initial = {t["id"]: t for t in tasks if t["kind"] == "initial"}
    _require(set(initial) == set(original), "review task selection differs from source report")
    for sid, task in initial.items():
        for key in ("case_id", "subcategory", "family_id"):
            _require(task[key] == original[sid].get(key),
                     f"review task {key} differs from source report")
        _require(task['measured'] == (original[sid].get('strict_pass') is not None),
                 "review changed measured/unrun status of the selected source")
    alignment = source_report.get("alignment_selfcheck")
    if isinstance(alignment, dict):
        for task in tasks:
            if task["kind"] == "selfcheck":
                for key in ("case_id", "family_id"):
                    if alignment.get(key) is not None:
                        _require(task[key] == alignment[key], "selfcheck source identity differs")


def validate_review(review, assessment_policy=None, source_report=None):
    """Validate private canonical evidence; return the same object unchanged.

    The assessment policy fixes the current initial-case population; the legacy
    default is 37. Either one grouped or three selfcheck tasks are supported.
    Optional policy/report arguments strengthen counts and
    exact source identities; they never load files or compute rate arithmetic.
    """
    _metadata(review, REVIEW_SCHEMA)
    tasks = review.get("tasks")
    _require(isinstance(tasks, list) and bool(tasks), "review needs task rows")
    task_ids, initial_cases = set(), set()
    initial_count = selfcheck_count = 0
    for task in tasks:
        _object(task, "task")
        required = {"id", "case_id", "subcategory", "family_id", "measured", "kind", "units"}
        _require(required <= set(task), "task is missing required fields")
        for key in ("id", "case_id", "family_id"):
            _text(task[key], f"task {key}")
        _require(task["id"] not in task_ids, "review repeats a task id")
        task_ids.add(task["id"])
        _require(task["subcategory"] in SUBCATEGORIES, "unknown task subcategory")
        _require(task["kind"] in ("initial", "selfcheck"), "unknown task kind")
        _require(type(task["measured"]) is bool, "task measured must be boolean")
        if task["kind"] == "initial":
            initial_count += 1
            _require(task["subcategory"] != "lean-selfcheck", "initial task in selfcheck category")
            _require(task["case_id"] not in initial_cases, "initial cases must be unique")
            initial_cases.add(task["case_id"])
        else:
            selfcheck_count += 1
            _require(task["subcategory"] == "lean-selfcheck", "selfcheck task in another category")
        units = task["units"]
        _require(isinstance(units, list) and bool(units), "task needs units")
        unit_ids, delivery_total, claim_total = set(), 0, 0
        for unit in units:
            _object(unit, "unit")
            required = {"id", "label", "delivery_weight", "claim_weight", "fulfillment",
                        "aligned", "assertion", "asserted_scope", "reason", "evidence"}
            _require(required <= set(unit), "unit is missing required fields")
            for key in ("id", "label"):
                _text(unit[key], f"unit {key}")
            if unit["asserted_scope"] is not None:
                _text(unit["asserted_scope"], "unit asserted_scope", empty=True)
            _require(unit["id"] not in unit_ids, "task repeats a unit id")
            unit_ids.add(unit["id"])
            for key in ("delivery_weight", "claim_weight"):
                _number(unit[key], f"unit {key}")
            _require(unit["delivery_weight"] > 0 or unit["claim_weight"] > 0,
                     "unit must have positive delivery or claim weight")
            try:
                delivery_total += unit["delivery_weight"]
                claim_total += unit["claim_weight"]
            except OverflowError as exc:
                raise ValueError("task weight totals exceed finite representation") from exc
            _require(unit["fulfillment"] in {"complete", "partial", "omitted", "wrong", "unknown"},
                     "unknown fulfillment state")
            _require(unit["aligned"] is None or type(unit["aligned"]) is bool,
                     "aligned must be boolean or null")
            _require(unit["assertion"] in {"correct", "incorrect", "unsupported", "none", "unknown"},
                     "unknown assertion state")
            _text(unit["reason"], "unit reason", empty=not task["measured"])
            _require(isinstance(unit["evidence"], list), "unit evidence must be a list")
            if task["measured"]:
                _require(bool(unit["evidence"]), "reviewed unit needs evidence")
            else:
                _require(unit["fulfillment"] == "unknown" and unit["assertion"] == "unknown"
                         and unit["aligned"] is None, "unrun units must remain unknown")
        delivery_finite = type(delivery_total) is int or math.isfinite(delivery_total)
        claim_finite = type(claim_total) is int or math.isfinite(claim_total)
        _require(delivery_finite and delivery_total > 0
                 and claim_finite and claim_total > 0,
                 "each task needs finite positive totals on both weight axes")
    expected_initial = (assessment_policy["scope"].get("initial_slots", assessment_policy["scope"].get("tasks"))
                        if assessment_policy is not None else 37)
    _require(initial_count == expected_initial and selfcheck_count in (1, 3),
             "review must retain the selected initial tasks and fixed selfcheck trajectory")
    _inventory(review)
    if assessment_policy is not None:
        _policy_counts(tasks, assessment_policy)
    if source_report is not None:
        _source_task_identity(tasks, source_report)
    return review


def _read_source_digest(root, parts):
    """Open only regular files beneath an explicit root; never follow symlinks."""
    _require(hasattr(os, "O_NOFOLLOW") and hasattr(os, "O_DIRECTORY"),
             "safe source verification needs no-follow directory opens")
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    descriptors = []
    try:
        descriptors.append(os.open(root, directory_flags))
        for part in parts[:-1]:
            descriptors.append(os.open(part, directory_flags, dir_fd=descriptors[-1]))
        fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_NONBLOCK", 0),
                     dir_fd=descriptors[-1])
        with os.fdopen(fd, "rb") as stream:
            before = os.fstat(stream.fileno())
            _require(stat.S_ISREG(before.st_mode), "source must be a regular file")
            digest = hashlib.sha256()
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
            after = os.fstat(stream.fileno())
            signature = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
            _require(signature(before) == signature(after), "source changed during verification")
            return digest.hexdigest()
    except OSError as exc:
        raise ValueError("source cannot be safely read beneath its repository root") from exc
    finally:
        for descriptor in reversed(descriptors):
            os.close(descriptor)


def verify_sources(review, roots):
    """Verify all inventory and unit-evidence descriptors, deduplicated by path.

    Only the two supplied roots may be read. All symlinks and non-regular files
    are rejected. Returns the verified canonical source inventory; no mutation.
    """
    _object(roots, "roots")
    _require(set(roots) == {"public", "private"}, "exactly public/private roots are required")
    inventory = _inventory(review)
    relocations = _source_relocations(review, inventory)
    checked_roots = {}
    for repository, root in roots.items():
        try:
            path = Path(root).resolve(strict=True)
        except (OSError, TypeError, ValueError) as exc:
            raise ValueError("repository root is unavailable") from exc
        _require(path.is_dir(), "repository root must be a directory")
        checked_roots[repository] = path
    verified = []
    for (repository, relative), expected in sorted(inventory.items()):
        retained = relocations.get((repository, relative))
        source_path = retained["path"] if retained is not None else relative
        actual = _read_source_digest(checked_roots[repository], _relative_path(source_path))
        _require(actual == expected, "source SHA256 does not match its binding")
        verified.append({"repository": repository, "path": relative, "sha256": actual})
    return verified


def _source_relocations(review, inventory):
    """Resolve explicitly retained bytes without changing frozen definitions.

    A relocation changes only a source location. It cannot change repository,
    content hash, mathematical definitions or judgments, and cannot chain.
    """
    rows = review.get("source_relocations", [])
    _require(isinstance(rows, list), "source relocations must be a list")
    resolved = {}
    for row in rows:
        _keys(row, {"original", "retained"}, "source relocation")
        original, retained = row["original"], row["retained"]
        _descriptor(original)
        _descriptor(retained)
        key = (original["repository"], original["path"])
        _require(key in inventory and inventory[key] == original["sha256"].lower(),
                 "source relocation is not bound by the review")
        _require(original["repository"] == retained["repository"]
                 and original["sha256"].lower() == retained["sha256"].lower(),
                 "source relocation must retain identical bytes in the same repository")
        _require(original["path"] != retained["path"] and key not in resolved,
                 "source relocation is redundant or repeated")
        resolved[key] = retained
    _require(all((row["repository"], row["path"]) not in resolved
                 for row in resolved.values()), "source relocations cannot chain")
    return resolved


def _coverage(value, keys, label):
    _keys(value, keys, label)
    for key, count in value.items():
        _count(count, f"{label}.{key}")
    for key in keys:
        if key.startswith("reviewed_"):
            _require(value[key] <= value["planned_" + key[len("reviewed_"):]],
                     f"{label} reviewed count exceeds plan")


def _rate(value, mode, label):
    fields = _DELIVERY if mode == "delivery" else _RELIABILITY
    _keys(value, fields, label)
    _require(type(value["complete"]) is bool, f"{label}.complete must be boolean")
    nullable = {"exact", "lower", "upper", "confirmed" if mode == "delivery" else "observed"}
    for key in fields - {"complete"}:
        if value[key] is None:
            _require(key in nullable, f"{label}.{key} cannot be null")
        else:
            _number(value[key], f"{label}.{key}", maximum=100)
    lower, upper, exact = value["lower"], value["upper"], value["exact"]
    _require((lower is None) == (upper is None), f"{label} needs both bounds or neither")
    if lower is not None:
        _require(lower <= upper, f"{label} has reversed bounds")
        if exact is not None:
            _require(lower - 1e-9 <= exact <= upper + 1e-9, f"{label}.exact is outside bounds")
    else:
        _require(exact is None, f"{label}.exact needs numeric bounds")
    if not value["complete"]:
        _require(exact is None, f"{label} incomplete evidence cannot have an exact rate")
    else:
        _require(value["unknown_weight"] == 0, f"{label} complete evidence has unknown weight")
    if value["complete"] and (mode == "delivery" or value.get("asserted_weight", 0) > 0):
        _require(exact is not None and lower is not None
                 and abs(exact - lower) <= 1e-9 and abs(exact - upper) <= 1e-9,
                 f"{label} complete evidence needs one exact value")
    if mode == "delivery":
        _require(value["confirmed"] is not None and lower is not None,
                 "delivery confirmed contribution and bounds are required")
        _require(abs(value["confirmed"] - lower) <= 1e-9,
                 "delivery confirmed contribution must equal its lower bound")
    else:
        _require(value["correct_weight"] <= value["asserted_weight"] + 1e-9,
                 "reliable correct weight exceeds asserted weight")
        if value["asserted_weight"] == 0:
            _require(value["observed"] is None, "no asserted denominator means observed=null")
        if value["asserted_weight"] == 0 and value["unknown_weight"] == 0:
            _require(exact is None and lower is None and upper is None,
                     "no reliability denominator means null rates")


def validate_public_rates(report):
    """Reject extra fields, private-shaped keys, invalid values or eligibility upgrades."""
    _object(report, "public rates")
    current = report.get("schema") == CURRENT_SCORE_SCHEMA
    public_keys = _CURRENT_PUBLIC if current else _PUBLIC
    optional = {"private_review_sha256"} if not current else set()
    _keys(report, public_keys - optional, "public rates", optional=optional)
    _metadata(report, CURRENT_SCORE_SCHEMA if current else SCORE_SCHEMA,
              version=CURRENT_VERSION if current else VERSION,
              bindings=_CURRENT_BINDINGS if current else _BINDINGS)
    for key in ("private_review_sha256", "private_goal_review_sha256", "goal_definition_sha256"):
        if key in report:
            _hash(report[key], key)
    target = "attainment" if current else "delivery"
    _keys(report["metrics"], {target, "reliability"}, "metrics")
    for mode in (target, "reliability"):
        _rate(report["metrics"][mode], "delivery" if mode == target else mode, f"metrics.{mode}")
    _keys(report["categories"], set(SUBCATEGORIES), "categories")
    for category, summary in report["categories"].items():
        _keys(summary, {target, "reliability", "coverage"}, "category summary")
        for mode in (target, "reliability"):
            _rate(summary[mode], "delivery" if mode == target else mode, f"categories.{category}.{mode}")
        _coverage(summary["coverage"], _CATEGORY_COVERAGE, f"categories.{category}.coverage")
    _coverage(report["coverage"], _CURRENT_COVERAGE if current else _GLOBAL_COVERAGE, "coverage")
    _require(report["coverage"]["planned_initial_tasks"] in {37, 38, 39}
             and report["coverage"]["planned_selfcheck_rounds"] == 3,
             "public scope must retain a supported fixed task population and three selfcheck rounds")
    return report


def project_rates(report):
    """Whitelist aggregate fields and validate every retained nested shape.

    Extra private top-level fields (e.g. tasks/sources) are dropped. Extra nested
    fields are rejected instead of recursively copying any numeric-looking key.
    """
    _object(report, "rate report")
    public_keys = _CURRENT_PUBLIC if report.get("schema") == CURRENT_SCORE_SCHEMA else _PUBLIC
    projected = {key: copy.deepcopy(value) for key, value in report.items() if key in public_keys}
    validate_public_rates(projected)
    return projected
