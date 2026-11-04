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
- The local v0.6.0 draft default suite has 26 related tasks: the unchanged 14 written
  proofs and 4 answer reviews, 4 historical semantic audits AHR01..04, and 4 large Lean
  formalizations LCH01(8), LCH02(20), HCH02(40), MG-C003(92). The first three share
  oet-volume1-chapter02; aggregate variants within family before averaging families.
  There are 18 default mathematical families, 31 explicit reserves and 57 retained tasks.
  Default stages/formalization obligations total 226, separate from 15 written-proof
  criteria, 16 semantic-audit dimensions and 12 AR dimensions. Original author evidence
  remains 43 papers/372 obligations/470 modules. New cases do not inherit author coverage.
  Profile v5 and reliability0.4 are post-observation local draft methods, human pending.
  New four-written panel: GR002, GR014, GP001, GP002; A1/A2 and one
  followup per neutral/affirm/deny arm. Public42 records; plus3 private exploration gives
  29 initial answers/21 families/45 records. Read current machine profiles for all counts.
  Eight Lean capabilities use fresh A1 only; GP001/GP002 use complete fresh five-slot panels.
  Both models have18 new standard slots, plus3 separate92-obligation alignment followups.
  Reuse compatible original written/AR records (including GR002/GR014 five-slot packages) with identity,
  source systems/parameters/budgets and explicit unknowns. Native operational resume
  pilots do not automatically populate formal A1 slots. Missing slots keep fixed denominators.
  Default formerly selected5 audits/5 constructions/C002 move by manifest only; all original
  paths, old0.5 configurations/results, original responses and published assets stay immutable.
  New historical exact-edition public availability is unverified; do not call it a hidden holdout.
- Answer review uses dedicated review dimensions (core judgment 60, evidence and impact 30,
  supplementary completeness 10), never mathematical stages or candidate Lean obligations.
  Aggregate within parent_family_id before averaging review families. Report major-error rate
  separately; strict pass is auxiliary. AR inclusion and regrading of the 8 existing answers are
  post-observation method changes, not a new exam. Preserve original answers and old reviews.
- Public and combined overall weights are 75/5/10/10. AR has 10% of capability; the public
  proof/audit/large-formalization weights are22.5/22.5/45 and combined weights are
  22.5/18/36/13.5 for proof/audit/formalization/exploration. Read current machine profiles rather than reimplementing scoring in displays.
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
