# Additive result admission across the sealed edition boundary

Component `result-edition-admission0.1.0`, schema
`math-gauge.result-edition-admission/v1`, admits a newly selected result that
actually executed against benchmark0.6.0 to the unchanged benchmark1.0.0 task
and scoring contracts. `math_gauge/result_admissions.py` owns only identity,
source binding and contract verification; `editions.py` composes that check
with the original sealed compatibility validation. This is a result selection,
not a new mathematical judgment or a claim that execution used1.0.0.

The released `releases/v1.0.0/compatibility.json`, its source bindings and its
original selected-record set remain immutable. Newly executed1.0.0 results
continue using `selected_result_source_versions` and `results/v1.0.0/`.
Previously selected0.6.0 results keep the original compatibility route.

A newly selected0.6.0 result uses its actual archive identity and a separate
source-bound admission. `benchmark.json` declares the normal model/record
selection plus this entry; every source descriptor has exactly `path`, `bytes`
and lowercase SHA-256. Paths are safe repository-relative regular files.

```json
{
  "selected_result_admissions": {
    "<distinct-model-id>": {
      "source_benchmark_version": "0.6.0",
      "archive_root": "results/v0.6.0",
      "admission": {
        "path": "results/edition-admissions/v0.1.0/<distinct-model-id>/<record-id>/admission.json",
        "bytes": 0,
        "sha256": "<actual-admission-sha256>"
      }
    }
  }
}
```

This illustration is not installable. An admission cannot collide with a
sealed legacy model or a model selected through `selected_result_source_versions`.
It needs an explicit record ID. The validator currently supports only the
0.6.0→1.0.0 boundary, not a general cross-version compatibility claim.

The admission document has these exact top-level fields:

- `schema`, `version`, `visibility` (`public`), `model_id`, `record_id`;
- `target_benchmark_version` (`1.0.0`), `source_benchmark_version` (`0.6.0`),
  `archive_root` (`results/v0.6.0`);
- `record`, `score_views`, `current_policies`, `public_case_contracts`;
- `selection_disclosure`, `sealed_compatibility_sha256`, `counts`, `migration`.

`record` binds the unchanged source record. `score_views` binds its six exact
original reports: capability/partial/strict × single_attempt/nonlogical_retry_3.
Their identities keep benchmark0.6.0, and their descriptors must equal those
in the source record. No arithmetic is recomputed in this component.

`current_policies` binds assessment, strict, capability, claim_penalty and
submission to their current public policy files. The source record's
corresponding policy bytes must be identical. `counts` is fixed at25 publicA1,
14 privateA1,39 combinedA1,35 families and3 C003 rounds.

`public_case_contracts` is sorted by the same25 current IDs selected by the
shared assessment policy. Each row has exactly `case_id`, `current_task`,
`current_contract`, `source_request`, `source_contract`. The current files must
be the catalog's task/group-contract files and the entire public Suite hash
must match the edition. The source request must equal `Suite.request(case)`,
including instructions, version, task text and attachments; its source group
contract must equal the current contract. Source request/contract files stay
under the original selected record. Do not manufacture a historical request
by editing it into the current identity. This public boundary does not replace
private case-contract validation in the paired private record pipeline.

`migration` fixes post_observation=true, new_candidate_calls=0,
source_raw_bytes_rewritten=false, mathematical_judgments_changed=false,
human_review=pending and formal_comparison_eligible=false. Source records keep
the same pending/unqualified status.

`selection_disclosure` has exactly `kind`=
`source_bound_selection_disclosure_only`, `retry3_policy_changed`=false,
`actual_ordinals_rewritten`=false, `formal_comparison_eligible`=false and a
nonempty `evidence` descriptor list bound to the same source archive. It may
explain specific user-selected fourth/fifth effective attempts while retaining
all actual physical/effective counts and raw evidence. It grants no generic
retry-budget, native-delivery or mathematical qualification waiver. Keep private
case identifiers, paths, answers and reviews out of public disclosure files;
use permitted anonymous aggregates/opaque hashes and paired private evidence.

All ordinary `records.validate_record`, attempt-condition, native evidence,
private paired-record and shared scoring checks remain mandatory. In particular,
this component does not reinterpret `records.apply_retry_selection` or the
AGY manuscript v3 maximum-three/current-freeze requirements. If a genuine
source history cannot pass an existing validator, retain the failure and resolve
that separate source contract explicitly; never falsify the execution edition,
renumber an effective attempt, hide a normal final or use best-of selection.

Before canonical adoption, run the full runner/format checks required by
AGENTS.md in an isolated prepared tree. A loader-only identity fixture is not a
validated benchmark answer, review, submission, cost/rate report or publication.

## First assessment of a retained older source

A newly retained source0.6.0 answer need not have previously published0.8.0
scores. Never create six fictitious historical views or relabel its actual
execution1.0.0 to satisfy the fresh-source contract. The separate
`source_assessment_admission` record field uses
`math-gauge.source-assessment-admission/v1` (component0.1.0), validated by
`source_assessments.py`. It binds the actual pre-call0.6.0 freeze, the exact
profile hash named by that freeze, its first original native dispatch/admission,
and the actual post-observation user selection. The original0.8.0 profile
assessment must equal current0.9.0 after only the existing assessment,
capability and submission method metadata transition. Mathematical weights and
contracts cannot change. This record has neither `score_history` nor the
distinct1.0.0 `first_assessment_source`. Public evidence keeps the private proof
hash; native/raw profile materials remain private.

## Exact original stage credit

`stage_credit_reviews.py` owns the exceptional
`math-gauge.source-stage-credit-review/v1` (component0.1.0) replay. It is restricted
to an unchanged written progressive A1 with an original source-bound continuous
stage judgment, or full required-stage credit with a separately documented false
extra assertion that prevents whole-task Strict completion. It preserves every
original unit, maximum, earned point, false-claim finding and Strict decision.
It verifies the actual normal native final, original import/material/contract
binding, and original review execution/terminal/seal hashes. Existing ordinary
reliability review validators remain unchanged. Its temporary criterion list is
only a view for existing review arithmetic; it never replaces a frozen case,
task, group contract, model input or native plan. Ordinary binary stage reviews
cannot enter this exceptional path. `scoring.py` still owns all weighted totals.
