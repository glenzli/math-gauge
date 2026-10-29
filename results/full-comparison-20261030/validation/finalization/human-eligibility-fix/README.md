# Proposed human comparison eligibility fix

Status: proposal only. Neither the repository runner nor its tests were modified.

## Finding

`compare_models` first sets `resolved` from the semantic review decision. For generate/repair, `compile_error` and `axiom_rejected` then make the strict outcome resolved even when the human decision is `unresolved`. The final human-eligibility predicate currently trusts that overloaded `resolved` field. For an approved case, valid execution and unresolved human review, it consequently reports eligibility as true. This conflicts with `report`'s explicit exclusion of unresolved human decisions and the separation of Lean checking from human judgment in the protocol.

## Minimal change

Add `and decision != "unresolved"` to `human_comparison_eligible`. Preserve automatic strict failure, `resolved`, outcome, paired counts, and all request/evidence bindings. The patch includes this one-line production change and one focused regression method.

## Regression scope

The regression uses the existing bound synthetic run fixtures, with approved cases, valid receipts and exact candidate Lean report hashes. It crosses generate/repair with compile_error/axiom_rejected and human unresolved/fail/partial: 12 subtests, two synthetic models each. It requires unresolved human reviews to remain ineligible at both case and aggregate levels. Fail/partial decisions are positive controls that must remain eligible. In every combination, strict failure stays resolved, complete remains true, and paired neither-pass counts stay unchanged.

The unmodified source copy fails the four unresolved subtests; the proposed source copy passes all 12. Only this new method ran. No models, Lean processes, real reviews or result files were used or changed. `verification.json` records exact source and artifact hashes.

## Adoption and rerun

Root should apply the proposal only after the R005 supplement archive/offline closure. The usual repository validation required by AGENTS.md belongs to that adoption, not this isolated proposal. A focused rerun after applying the patch is:

```sh
python3 -B -m unittest discover -s tests -p test_comparison_report.py
```

Artifacts `before/` and `after/` are disposable copies of the six package Python modules and the augmented comparison test; the logs are synthetic test evidence, never model results.
