#!/usr/bin/env python3
"""Bounded author checks; default is read-only, --write creates the local report.

These finite checks do not prove the arbitrary-set/group reference argument and
do not call any model, network service, Lean process, or shared runner.
"""

import argparse
import hashlib
import itertools
import json
from datetime import datetime, timezone
from pathlib import Path


BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
BOUND_FILES = (
    "task.md", "reference.md", "rubric.json", "draft.json", "design.md",
    "self-review.md", "sources.json", "author_checks.py",
)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def functions(domain_size, codomain_size):
    return tuple(itertools.product(range(codomain_size), repeat=domain_size))


def orientations(n):
    if n == 0:
        return []
    full = (1 << n) - 1
    representatives = [a for a in range(1, full) if a < (full ^ a)]
    result = []
    for bits in itertools.product((0, 1), repeat=len(representatives)):
        c = [0] * (full + 1)
        c[full] = 1
        for a, value in zip(representatives, bits):
            c[a] = value
            c[full ^ a] = 1 - value
        result.append(tuple(c))
    return result


def fibre(f, label):
    return sum(1 << i for i, value in enumerate(f) if value == label)


def binary_value(c, f):
    return c[fibre(f, 1)]


def check_binary_naturality(n, c):
    records = {(1, f): 0 for f in functions(n, 1)}
    records.update({(2, f): binary_value(c, f) for f in functions(n, 2)})
    equations = 0
    for a in range(3):
        for b in range(3):
            for f in functions(n, a):
                for alpha in functions(a, b):
                    composite = tuple(alpha[value] for value in f)
                    require(alpha[records[a, f]] == records[b, composite],
                            "binary naturality failed")
                    equations += 1
    return equations


def ternary_survivors(n, all_orientations):
    survivors = []
    examined = 0
    ternary_tests = functions(n, 3)
    for c in all_orientations:
        valid = True
        # Inspect every ordered three-block partition, including empty blocks.
        for f in ternary_tests:
            examined += 1
            if sum(c[fibre(f, j)] for j in range(3)) != 1:
                valid = False
        if valid:
            survivors.append(c)
    principal = [tuple((a >> x) & 1 for a in range(1 << n)) for x in range(n)]
    require(set(survivors) == set(principal),
            "three-test survivors differ from exactly the point records")
    return survivors, examined


def check_ternary_record(n, c):
    records = {}
    for a in range(4):
        for f in functions(n, a):
            selected = [j for j in range(a) if c[fibre(f, j)]]
            require(len(selected) == 1, "not exactly one selected finite fibre")
            records[a, f] = selected[0]
    equations = 0
    for a in range(4):
        for b in range(4):
            for f in functions(n, a):
                for alpha in functions(a, b):
                    composite = tuple(alpha[value] for value in f)
                    require(alpha[records[a, f]] == records[b, composite],
                            "ternary record all-map naturality failed")
                    equations += 1
    return equations


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def generated_subgroup(n, generators):
    identity = tuple(range(n))
    seen = {identity}
    pending = [identity]
    while pending:
        p = pending.pop()
        for g in generators:
            value = compose(p, g)
            if value not in seen:
                seen.add(value)
                pending.append(value)
    return frozenset(seen)


def all_subgroups(n):
    perms = tuple(itertools.permutations(range(n)))
    identity = frozenset({tuple(range(n))})
    seen = {identity}
    pending = [identity]
    while pending:
        subgroup = pending.pop()
        for p in perms:
            if p in subgroup:
                continue
            extension = generated_subgroup(n, tuple(subgroup) + (p,))
            if extension not in seen:
                seen.add(extension)
                pending.append(extension)
    return tuple(sorted(seen, key=lambda g: (len(g), tuple(sorted(g)))))


def image_mask(p, a):
    return sum(1 << p[i] for i in range(len(p)) if a & (1 << i))


def fixed_mask(n, group):
    return sum(1 << i for i in range(n) if all(p[i] == i for p in group))


def orbit_count(n, group):
    full = (1 << n) - 1
    unseen = {a for a in range(1, full) if a < (full ^ a)}
    count = 0
    while unseen:
        a = min(unseen)
        orbit = {min(image_mask(p, a), full ^ image_mask(p, a)) for p in group}
        unseen.difference_update(orbit)
        count += 1
    return count


def fixed_orientation(c, group):
    return all(c[a] == c[image_mask(p, a)]
               for p in group for a in range(len(c)))


def finite_action_checks(n, all_orientations, survivors):
    groups = all_subgroups(n)
    expected_subgroup_counts = {0: 1, 1: 1, 2: 2, 3: 6, 4: 30}
    require(len(groups) == expected_subgroup_counts[n], "subgroup enumeration count")
    actions = []
    for group in groups:
        full = (1 << n) - 1
        fixed = [c for c in all_orientations if fixed_orientation(c, group)]
        higher = [c for c in survivors if fixed_orientation(c, group)]
        no_swap = not any(image_mask(p, a) == (full ^ a)
                          for p in group for a in range(full + 1))
        count = (1 << orbit_count(n, group)) if n and no_swap else 0
        require(len(fixed) == count, "fixed orientation orbit-count formula")
        points = fixed_mask(n, group).bit_count()
        require(len(higher) == points, "higher fixed records differ from fixed points")
        # The fixed restriction image consists precisely of fixed principal choices.
        require(set(higher).issubset(fixed), "fixed restriction lost fixedness")
        require(len(set(fixed).intersection(survivors)) == points,
                "binary-to-full extension count")
        # Finite analogue of the intrinsic ideal, using every subgroup of G.
        for a in range(full + 1):
            in_ideal = any((a & fixed_mask(n, subgroup)) == 0
                           for subgroup in groups if subgroup.issubset(group))
            require(in_ideal == ((a & fixed_mask(n, group)) == 0),
                    "finite intrinsic-ideal classification")
        actions.append({"group_order": len(group), "binary_fixed": len(fixed),
                        "higher_fixed": len(higher), "complement_orbits": orbit_count(n, group),
                        "complement_swap_absent": no_swap})
    return {"n": n, "permutation_subgroups": len(groups), "actions": actions}


def color_moved_cycles(p):
    colors = [-1] * len(p)
    seen = set()
    for start in range(len(p)):
        if start in seen:
            continue
        cycle = []
        current = start
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = p[current]
        if len(cycle) == 1:
            continue
        for j, x in enumerate(cycle):
            colors[x] = 2 if len(cycle) % 2 and j == len(cycle) - 1 else j % 2
    return colors


def finite_coloring_checks():
    rows = []
    for n in range(8):
        count = 0
        for p in itertools.permutations(range(n)):
            colors = color_moved_cycles(p)
            for i in range(n):
                if p[i] == i:
                    require(colors[i] == -1, "colored a fixed point")
                else:
                    require(colors[i] in (0, 1, 2), "invalid cycle color")
                    require(colors[i] != colors[p[i]], "adjacent moved points share color")
            count += 1
        rows.append({"n": n, "permutations_checked": count})
    return rows


def structure_and_binding_checks():
    draft = json.loads((BASE / "draft.json").read_text())
    rubric = json.loads((BASE / "rubric.json").read_text())
    sources = json.loads((BASE / "sources.json").read_text())
    require(draft["version"] == rubric["version"] == "0.1.0", "draft version mismatch")
    require(draft["candidate_projection"] == ["task.md"], "candidate projection drift")
    require(draft["solver_files"] == [], "unexpected candidate attachment")
    require(draft["review"]["human"] == "pending", "invented human approval")
    require(draft["review"]["independent_mathematical"] == "pending",
            "author check cannot create independent mathematical review")
    require(draft["old_model_results_inherited"] is False, "inherited model evidence")
    categories = rubric["categories"]
    require([c["points"] for c in categories] == [30, 30, 15, 15, 10], "rubric weights")
    for category in categories:
        require(sum(check["points"] for check in category["checks"]) == category["points"],
                "rubric category sum")
        for check in category["checks"]:
            require(all(k in check for k in ("full", "half", "zero")), "grading levels missing")
    require(sum(c["points"] for c in categories) == 100, "rubric total")
    task = (BASE / "task.md").read_text()
    for forbidden in ("超滤子", "ultrafilter", "三着色", "有限生成群", "补对轨道", "评分", "Terra", "Gemini"):
        require(forbidden not in task, "answer/evaluator hint in candidate task: " + forbidden)
    require(all(f"{i}. **" in task for i in (1, 2, 3)), "three final targets missing")
    parent_count = 0
    for item in sources["current_parent_files"]:
        path = ROOT / item["path"]
        require(path.is_file(), "missing parent source: " + str(path))
        require(hashlib.sha256(path.read_bytes()).hexdigest() == item["sha256"],
                "parent source changed: " + item["path"])
        parent_count += 1
    hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest() for name in BOUND_FILES}
    return {"candidate_projection": ["task.md"], "rubric_total": 100,
            "category_points": [30, 30, 15, 15, 10], "parent_files_checked": parent_count,
            "bound_input_sha256": hashes}


def run_checks():
    structure = structure_and_binding_checks()
    finite = []
    binary_equations = 0
    ternary_equations = 0
    for n in range(5):
        choices = orientations(n)
        if n:
            for c in choices:
                binary_equations += check_binary_naturality(n, c)
        high, tested = ternary_survivors(n, choices)
        for c in high:
            ternary_equations += check_ternary_record(n, c)
        action = finite_action_checks(n, choices, high)
        finite.append({"n": n, "binary_records": len(choices),
                       "ternary_survivors": len(high), "ordered_three_partitions_examined": tested,
                       "fixed_actions": action})
    cycle = generated_subgroup(3, ((1, 2, 0),))
    c3_binary = sum(fixed_orientation(c, cycle) for c in orientations(3))
    c3_full = fixed_mask(3, cycle).bit_count()
    require((c3_binary, c3_full) == (2, 0), "three-point cyclic nonextension witness")
    coloring = finite_coloring_checks()
    return {"structure": structure, "finite_records_and_actions": finite,
            "binary_naturality_equations": binary_equations,
            "ternary_naturality_equations": ternary_equations,
            "finite_cycle_colorings": coloring,
            "c3_nonextension": {"binary_fixed": c3_binary, "full_fixed": c3_full},
            "all_passed": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true",
                        help="Write author-checks.json; never use after the coordinator freezes the draft.")
    args = parser.parse_args()
    checks = run_checks()
    report_path = BASE / "author-checks.json"
    if args.write:
        report = {"schema": "math-gauge.local-author-checks/v1", "draft_version": "0.1.0",
                  "generated_utc": datetime.now(timezone.utc).isoformat(),
                  "evidence_kind": "bounded-finite-exhaustion-and-byte-binding",
                  "scope_limit": "Does not machine-prove infinite sets/groups, ultrafilter extension, arbitrary products, human approval, or candidate performance.",
                  "candidate_model_calls": 0, "lean_compilations": 0,
                  "independent_mathematical_review": "pending", "human_review": "pending",
                  "checks": checks}
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    else:
        report = json.loads(report_path.read_text())
        require(report["checks"] == checks, "report/input mismatch; do not mutate a frozen draft")
    print(json.dumps({"mode": "write" if args.write else "read-only-verify",
                      "all_passed": checks["all_passed"],
                      "binary_naturality_equations": checks["binary_naturality_equations"],
                      "ternary_naturality_equations": checks["ternary_naturality_equations"],
                      "finite_permutation_actions": sum(r["fixed_actions"]["permutation_subgroups"]
                                                        for r in checks["finite_records_and_actions"]),
                      "permutation_colorings": sum(r["permutations_checked"]
                                                   for r in checks["finite_cycle_colorings"]),
                      "c3_nonextension": checks["c3_nonextension"]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
