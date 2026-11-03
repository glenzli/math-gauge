# Math Gauge

- First read README.md, protocol/evaluation.md and the relevant case's complete material.
- Preserve the supplied mathematical structures, quantifiers, domains and conclusion strengths.
- Every new case needs public/private provenance, a full reference argument or counterexample,
  specific review criteria, and explicit mathematical/human review status.
- AI review, a successful Lean compilation, and human approval are different evidence.
  Do not mark a case human-approved or invent a real model result.
- A supplied Lean file can be intentionally semantically mismatched while compiling successfully.
  Do not "fix" such an input without updating the benchmark design and version.
- Candidate-facing files are an explicit projection. References, rubrics and review records stay out of it.
- The local v0.5.0 default suite has 30 related tasks: 14 written proofs, 5 Lean audits,
  5 Lean constructions, 2 chapters and 4 answer reviews, spanning 21 mathematical families.
  The explicit reserve suite has 20 tasks: 18 written papers, 1 Lean audit and 1 Lean repair.
  Eleven physical reserve directories remain unchanged; 9 manifest references retain the
  original paths of 7 proofs plus the GF109/GF110 Lean pair. The bank retains the original
  43 mathematical papers plus 3 same-family strengthened variants, for 46 mathematical
  papers and 4 reviews (50 tasks).
  Original author Lean evidence covers only 43 papers, 372 obligations and 470 compiled modules;
  the 3 new written papers' 15 criteria have no author Lean evidence and remain human pending.
  Default historical mathematical stages/chapter obligations total 252; keep these separate
  from the 15 new written-proof criteria. Reviews are correlated with their parent papers.
  Default full coverage is 54 records; adding 3 private exploration tasks yields 33 initial
  answers, 24 families and 57 records. Version0.3 repeat/self-check selects 6 public papers,
  uses A1/A2 (two independent answers), and one follow-up per neutral/affirm/deny arm.
  Old version0.2 A3/R2 records remain archived but are excluded from the new default;
  recompute from existing A1/A2/R1 without making new model calls. In both versions,
  the 4 review parents remain selected. Read current machine profiles for counts and weights.
  Selection/recomputation is post-observation: compatible old answers are reused and the 3
  strengthened tasks have new native initial answers. Do not call this a synchronous new exam.
  Historical 80/83/84/87/177-record evidence keeps its original version and denominator;
  equal record counts do not identify the same experiment. Published v0.4.0 assets stay immutable.
- Answer review uses dedicated review dimensions (core judgment 60, evidence and impact 30,
  supplementary completeness 10), never mathematical stages or candidate Lean obligations.
  Aggregate within parent_family_id before averaging review families. Report major-error rate
  separately; strict pass is auxiliary. AR inclusion and regrading of the 8 existing answers are
  post-observation method changes, not a new exam. Preserve original answers and old reviews.
- Public and combined overall weights are 75/5/10/10. AR has 10% of capability; the public
  original four directions each have 22.5%, and the combined original five have
  22.5/18/18/18/13.5%. Read current machine profiles rather than reimplementing scoring in displays.
- Public references and Git history remain available for transparency; do not describe them as
  a hidden holdout or include them in solver packets. Published release assets stay immutable;
  Publish each release from its exact clean source commit and keep existing release assets immutable.
- External harness bundles separate solver content, controller scheduling and evaluator data. Keep the
  full plan/profile, expected truth, rubrics, approval and author evidence outside the exported bundle.
  Preserve complete candidate messages and attachments, fresh independent contexts and isolated branches.
- All public and private suites use the same runner. Do not copy runner implementations into private data.
- Execution and original-response evidence live in math_gauge/execution.py, case contracts in catalog.py,
  and single-answer judgments/reporting in review.py. benchmarks.py owns evaluator-only profiles and
  selected benchmark plans; scoring.py owns versioned cross-attempt aggregation; reliability.py owns
  branch history and KEEP/FULL composition with separately bound follow-up reviews.
- eligibility.py owns immutable execution-evidence imports, attributed execution-audit snapshots
  and per-slot qualification. Source integrity, human provenance review and mathematical review
  remain separate; request labels or fixture evidence cannot establish formal comparison eligibility.
- harness.py owns standalone solver/controller exports and read-only bundle checks; harness_answers.py
  owns raw response collection and single return archives; harness_import.py owns external-submission
  and archive ingestion into the same reliability evidence and review contracts.
  CLI only composes these interfaces. Export, check and import do not invoke candidate models.
- Candidate release datasets stay immutable and runtime-free. harness.py freezes each chosen model,
  budget and selected target into a new run workspace; harness_import.py binds v2 submissions to that
  unchanged dataset and a trusted evaluator anchor. scripts/release.py owns named ZIP/checksum assets
  and reproducible evaluator-plan recovery. New task releases use the suite version as the release
  version; the published v0.1.0 release retains its historical convention. GitHub
  automatic source archives contain public evaluator materials and are not solver deliveries.
- Neutral release inputs use the versioned projection in release_projection.py; source cases,
  original responses and legacy releases remain unchanged. Export/import must reconstruct the same
  projected bytes from trusted sources; complete repository provenance stays evaluator-side.
- Operator guides, runtime declarations, release metadata and schedules stay outside candidate
  messages. Runtime hashes, UUIDs, dates and source declarations do not authenticate a backend or
  third-party execution chronology. Generic external imports retain their current provisional status.
- Benchmark scores use frozen profile weights and fixed denominators. Missing, execution-failed and
  unresolved slots stay explicit; never renormalize a partial run into a full-benchmark score.
- Run python3 -m unittest discover -s tests and python3 -m math_gauge validate for affected runner contracts.
  Compile only changed Lean fixtures or their dependent group; keep evidence tied to file hashes.
- Do not commit or push unless the user authorizes that step. Keep .dev-mesh and runs local.
