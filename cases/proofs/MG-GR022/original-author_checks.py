#!/usr/bin/env python3
"""Finite author checks for this local draft; never calls candidate models.

This script writes only author-checks.json in its own directory. Do not run it
after the root task freezes or accepts the nine-file author contribution.
Finite-rank computations are not proofs of the infinite-module classification.
"""

from __future__ import annotations

import ast
from datetime import datetime, timezone
import hashlib
import itertools
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
INPUTS = (
    "task.md",
    "reference.md",
    "rubric.json",
    "draft.json",
    "design.md",
    "self-review.md",
    "sources.json",
    "author_checks.py",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name: str) -> dict:
    return json.loads((HERE / name).read_text())


def rank_f2(columns: list[int]) -> int:
    """Rank of an actual binary matrix represented by its bit columns."""
    pivots: dict[int, int] = {}
    for column in columns:
        value = column
        while value:
            position = value.bit_length() - 1
            if position in pivots:
                value ^= pivots[position]
            else:
                pivots[position] = value
                break
    return len(pivots)


def apply_f2(columns: list[int], vector: int) -> int:
    result = 0
    while vector:
        bit = vector & -vector
        result ^= columns[bit.bit_length() - 1]
        vector ^= bit
    return result


def level_matrices(nu: tuple[int, ...], m: int) -> tuple[list[int], list[int]]:
    """D and q for F2[t]^N modulo the actual powers t^m.

    The first two terms have N*m coefficients; the quotient term has
    sum(min(m,nu_i)) coefficients. These are matrices of the original maps.
    """
    diagonal: list[int] = []
    quotient: list[int] = []
    offset = 0
    for coordinate, exponent in enumerate(nu):
        width = min(m, exponent)
        for degree in range(m):
            diagonal.append(
                1 << (coordinate * m + degree + exponent)
                if degree + exponent < m
                else 0
            )
            quotient.append(1 << (offset + degree) if degree < width else 0)
        offset += width
    return diagonal, quotient


def check_finite_levels() -> dict:
    count = 0
    noninjective_diagonals = 0
    for size in range(1, 5):
        for nu in itertools.product(range(4), repeat=size):
            for m in range(1, 6):
                diagonal, quotient = level_matrices(nu, m)
                domain_dimension = size * m
                quotient_dimension = sum(min(m, exponent) for exponent in nu)
                rank_d = rank_f2(diagonal)
                rank_q = rank_f2(quotient)
                assert all(apply_f2(quotient, column) == 0 for column in diagonal)
                assert rank_q == quotient_dimension
                assert rank_d + rank_q == domain_dimension
                assert domain_dimension - rank_d == quotient_dimension
                noninjective_diagonals += rank_d < domain_dimension
                count += 1
    return {
        "id": "finite-level-diagonal-exactness",
        "passed": True,
        "field": "F2",
        "exhaustive_parameters": {
            "rank": [1, 2, 3, 4],
            "coordinate_exponents": [0, 1, 2, 3],
            "levels": [1, 2, 3, 4, 5],
        },
        "matrix_instances": count,
        "maximum_middle_dimension": 20,
        "noninjective_finite_level_diagonals": noninjective_diagonals,
        "identities": ["qD=0", "rank(q)=sum(min(m,nu_i))", "im(D)=ker(q)"],
        "limitation": "Every instance has finite rank. This does not prove middle exactness after taking the countable inverse limit, nor does finite-level noninjectivity refute completed injectivity.",
    }


def support_mod_t_power(vector: dict[int, int], m: int) -> list[int]:
    mask = (1 << m) - 1
    return sorted(n for n, polynomial in vector.items() if polynomial & mask)


def valuation(polynomial: int) -> int:
    assert polynomial > 0
    return (polynomial & -polynomial).bit_length() - 1


def check_oscillating_prefixes() -> dict:
    instances = 0
    for count in range(1, 41):
        raw = {2 * j: 1 for j in range(1, count + 1)}
        image = {2 * j: 1 << j for j in range(1, count + 1)}
        torsion = {2 * j: 1 << (j - 1) for j in range(1, count + 1)}
        assert support_mod_t_power(raw, 1) == list(range(2, 2 * count + 1, 2))
        for j in range(1, count + 1):
            modulus_mask = (1 << j) - 1
            assert image[2 * j] & modulus_mask == 0
            assert torsion[2 * j] & modulus_mask != 0
            assert (torsion[2 * j] << 1) & modulus_mask == 0
        for m in range(1, 11):
            assert support_mod_t_power(image, m) == [
                2 * j for j in range(1, min(count, m - 1) + 1)
            ]
            assert support_mod_t_power(torsion, m) == [
                2 * j for j in range(1, min(count, m) + 1)
            ]
            if count >= m:
                extended = dict(image)
                extended[2 * (count + 1)] = 1 << (count + 1)
                assert support_mod_t_power(image, m) == support_mod_t_power(extended, m)
            instances += 1
        for cutoff in range(count):
            raw_tail = [raw[2 * j] for j in range(cutoff + 1, count + 1)]
            image_tail = [image[2 * j] for j in range(cutoff + 1, count + 1)]
            assert min(map(valuation, raw_tail)) == 0
            assert min(map(valuation, image_tail)) == cutoff + 1
            instances += 1
    return {
        "id": "oscillating-exponent-prefix-identities",
        "passed": True,
        "sequence": "nu_(2j)=j, nu_(2j-1)=0",
        "prefixes": 40,
        "level_and_tail_instances": instances,
        "identities": [
            "D of the even-coordinate unit prefix has valuation j on coordinate 2j",
            "its modulo-t^m support is exactly 2j with j<m",
            "raw preimage modulo-t support grows with every prefix",
            "the tail image has minimum valuation cutoff+1 while its raw preimage tail has minimum valuation 0",
            "the residue t^(j-1) mod t^j is nonzero and killed by t",
            "the torsion-prefix modulo-t^m support is exactly 2j with j<=m",
        ],
        "sample_with_40_nonzero_even_coordinates": {
            "image_support_mod_t4": [2, 4, 6],
            "torsion_support_mod_t4": [2, 4, 6, 8],
            "raw_preimage_support_mod_t": 40,
        },
        "limitation": "Exact polynomial prefix identities illustrate the arbitrary-unbounded-sequence and support traps. Infinitude, closure, non-splitting and completeness still require the universal reference proof.",
    }


def check_ambient_submodule_trap() -> dict:
    diagonal, quotient = level_matrices((1, 1), 3)
    assert rank_f2(diagonal) == 4
    assert rank_f2(quotient) == 2
    assert rank_f2(diagonal) < 6
    assert rank_f2(diagonal) == 6 - rank_f2(quotient)
    return {
        "id": "image-ambient-space-distinction",
        "passed": True,
        "exponents": [1, 1],
        "level": 3,
        "middle_dimension": 6,
        "image_dimension": 4,
        "kernel_of_quotient_dimension": 4,
        "meaning": "An image can be proper in the middle module while equal to the quotient-map kernel. The reference specifies H as the ambient submodule in the unboundedness criterion.",
    }


def check_artifact_contract() -> dict:
    draft = load("draft.json")
    rubric = load("rubric.json")
    sources = load("sources.json")
    task = (HERE / "task.md").read_text()
    ast.parse((HERE / "author_checks.py").read_text())
    assert draft["version"] == rubric["version"] == sources["version"] == "0.1.0"
    assert draft["family_id"] == sources["family_id"] == "MG-R015"
    assert draft["official_case"] is False and draft["suite_integration"] is False
    assert draft["candidate_projection"] == {
        "files": ["task.md"], "candidate_instruction": "", "solver_files": []
    }
    assert draft["execution"]["candidate_models_called"] == 0
    assert draft["execution"]["inherited_model_results"] is False
    assert draft["execution"]["inherited_formal_coverage"] is False
    for document in (draft, sources):
        assert document["review"]["human"] == "pending"
    assert rubric["review_status"]["human"] == "pending"
    expected_points = [25, 25, 25, 15, 10]
    assert [part["points"] for part in rubric["dimensions"]] == expected_points
    for part in rubric["dimensions"]:
        assert sum(check["points"] for check in part["checks"]) == part["points"]
        assert all(check[key] for check in part["checks"] for key in ("full", "half", "zero"))
    assert sum(expected_points) == rubric["total_points"] == 100
    assert re.findall(r"^([123])\. ", task, re.MULTILINE) == ["1", "2", "3"]
    forbidden = (
        "Z_", "Z/X", "c_0", "有界", "无界", "平凡拓扑", "不可分拓扑",
        "参考答案", "评分", "100", "提示", "建议先", "MG-GR015", "MG-R015",
        "Terra", "Gemini", "GPT", "rubric", "reference.md", "design.md",
    )
    assert not any(token in task for token in forbidden)
    assert sources["source_visibility"] == "public"
    for source in sources["materials"]:
        path = REPO / source["path"]
        assert path.is_file(), source["path"]
        assert digest(path) == source["sha256"], source["path"]
        assert path.stat().st_size == source["bytes"], source["path"]
    return {
        "id": "candidate-projection-and-author-metadata",
        "passed": True,
        "candidate_files": ["task.md"],
        "global_targets": 3,
        "rubric_points": expected_points,
        "rubric_checks": sum(len(part["checks"]) for part in rubric["dimensions"]),
        "source_files_unchanged": len(sources["materials"]),
        "syntax_check": "author_checks.py parsed successfully; no bytecode artifact written",
        "limitation": "Token checks support the manual hint audit; they are not a proof of semantic prompt isolation or mathematical correctness.",
    }


def main() -> None:
    results = [
        check_finite_levels(),
        check_oscillating_prefixes(),
        check_ambient_submodule_trap(),
        check_artifact_contract(),
    ]
    report = {
        "schema": "math-gauge.local-author-checks/v1",
        "draft_id": "MG-GR015-COMPLETION-UPGRADE-LOCAL",
        "version": "0.1.0",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "status": "passed",
        "input_sha256": {name: digest(HERE / name) for name in INPUTS},
        "checks": results,
        "evidence_scope": "Exact finite algebra and local artifact contracts only. Universal mathematical proof is reference.md; this is not Lean, candidate-model evidence, independent mathematical review, or human approval.",
        "candidate_calls": 0,
        "lean_compilations": 0,
        "human_review": "pending",
    }
    destination = HERE / "author-checks.json"
    destination.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({
        "status": report["status"],
        "finite_level_instances": results[0]["matrix_instances"],
        "prefix_level_and_tail_instances": results[1]["level_and_tail_instances"],
        "checks": len(results),
        "output": str(destination),
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
