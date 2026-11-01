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
- The current 43-paper suite is a public development suite. Public references and Git history remain
  available for transparency; do not describe them as a hidden holdout or include them in solver packets.
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
- harness.py owns standalone solver/controller exports and read-only bundle checks; harness_import.py
  owns external-submission ingestion into the same reliability evidence and review contracts.
  CLI only composes these interfaces. Export, check and import do not invoke candidate models.
- Candidate release datasets stay immutable and runtime-free. harness.py freezes each chosen model,
  budget and selected target into a new run workspace; harness_import.py binds v2 submissions to that
  unchanged dataset and a trusted evaluator anchor. scripts/release.py owns named ZIP/checksum assets
  and reproducible evaluator-plan recovery. Keep release version and suite version separate; GitHub
  automatic source archives contain public evaluator materials and are not solver deliveries.
- Operator guides, runtime declarations, release metadata and schedules stay outside candidate
  messages. Runtime hashes, UUIDs, dates and source declarations do not authenticate a backend or
  third-party execution chronology. Generic external imports retain their current provisional status.
- Benchmark scores use frozen profile weights and fixed denominators. Missing, execution-failed and
  unresolved slots stay explicit; never renormalize a partial run into a full-benchmark score.
- Run python3 -m unittest discover -s tests and python3 -m math_gauge validate for affected runner contracts.
  Compile only changed Lean fixtures or their dependent group; keep evidence tied to file hashes.
- Do not commit or push unless the user authorizes that step. Keep .dev-mesh and runs local.
