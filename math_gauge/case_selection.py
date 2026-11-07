"""Versioned assessment selection over immutable public source inventories."""

from collections import Counter
import re


RETIRED_PUBLIC_CASE_IDS = frozenset({
    "MG-GP003", "MG-GR002", "MG-GR008", "MG-GR010", "MG-GR014", "MG-GR104",
})
CANONICAL_PARENT_FAMILIES = {
    "MG-GR104": "MG-R104", "MG-GR014": "MG-R014",
    "MG-GR010": "MG-R010", "MG-GP003": "MG-P003",
}


def validate_case_selection(selection):
    """Validate the component revision without changing source plans or reviews."""
    if (not isinstance(selection, dict)
            or selection.get("schema") != "math-gauge.case-selection/v1"
            or selection.get("version") != "0.1.0"
            or not isinstance(selection.get("source_revision"), str)
            or not re.fullmatch(r"[0-9a-f]{40}", selection["source_revision"])):
        raise ValueError("Unsupported assessment case selection")
    inventories = {}
    for key, count in (("public_case_ids", 20), ("retired_public_case_ids", 6),
                       ("source_public_case_ids", 26)):
        ids = selection.get(key)
        if (not isinstance(ids, list) or len(ids) != count
                or not all(isinstance(cid, str) and re.fullmatch(r"[A-Za-z0-9_-]+", cid)
                           for cid in ids) or len(set(ids)) != len(ids)):
            raise ValueError("Assessment case selection requires unique fixed inventories")
        inventories[key] = set(ids)
    kept, retired, source = (inventories[key] for key in (
        "public_case_ids", "retired_public_case_ids", "source_public_case_ids"))
    if (retired != RETIRED_PUBLIC_CASE_IDS or kept & retired or kept | retired != source
            or selection.get("canonical_parent_families") != CANONICAL_PARENT_FAMILIES):
        raise ValueError("Assessment case selection contradicts its frozen partition or parent families")
    return selection


def assessment_family(case, cases, selection=None):
    """Keep ordinary families and normalize only answer-review parent identities."""
    if (case.get("contract_kind") != "answer_review"
            and case.get("task_kind") != "answer_review"):
        return case["family_id"]
    family = case["parent_family_id"]
    if selection is not None:
        family = selection["canonical_parent_families"].get(family, family)
    return cases[family]["family_id"] if family in cases else family


def selected_assessment_cases(cases, selection, *, current_plan=False):
    """Select public members and every private exploration; missing rows stay planned."""
    if selection is None:
        return cases
    selection = validate_case_selection(selection)
    kept = set(selection["public_case_ids"])
    source = set(selection["source_public_case_ids"])
    public = {cid for cid, case in cases.items() if case["component"] != "exploration"}
    private = {cid for cid, case in cases.items() if case["component"] == "exploration"}
    if (not kept <= public or not public <= source or private & source
            or len(private) > 3 or (current_plan and public != kept)):
        raise ValueError("Assessment case selection differs from the source task inventory")
    if any(cases[cid]["component"] != "proofs" for cid in public - kept):
        raise ValueError("Assessment case selection may retire only public written arguments")
    selected = {cid: case for cid, case in cases.items() if cid in kept or cid in private}
    if Counter(case["component"] for cid, case in selected.items() if cid in public) != {
            "proofs": 8, "lean-audit": 4, "lean-formalization": 4, "answer-review": 4}:
        raise ValueError("Assessment case selection changed the fixed category populations")
    if (len({selected[cid]["family_id"] for cid in kept
             if selected[cid]["component"] == "proofs"}) != 8
            or len({selected[cid]["family_id"] for cid in private}) != len(private)):
        raise ValueError("Assessment case selection changed the argument family denominator")
    parents = selection["canonical_parent_families"]
    if any(cid in cases and cases[cid]["family_id"] != family for cid, family in parents.items()):
        raise ValueError("Assessment case selection contradicts the original parent family")
    review_families = {assessment_family(case, cases, selection) for case in selected.values()
                       if case["component"] == "answer-review"}
    if review_families != set(parents.values()):
        raise ValueError("Assessment case selection changed the answer-review parent families")
    return selected


def selected_current_cases(cases, selection, *, current_plan=False):
    """Preserve research additions outside the immutable legacy selection."""
    extra = {cid: c for cid, c in cases.items()
             if c['component'] in {'theorem-extension', 'background-check'}}
    base = {cid: c for cid, c in cases.items() if cid not in extra}
    normalized = {cid: dict(c, component='exploration')
                  if c['component']=='proofs' and c.get('source_visibility', c.get('visibility'))=='private'
                  else c for cid,c in base.items()}
    selected = selected_assessment_cases(normalized, selection, current_plan=current_plan)
    return {cid:c for cid,c in cases.items() if cid in selected or cid in extra}
