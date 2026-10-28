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
- All public and private suites use the same runner. Do not copy runner implementations into private data.
- Execution lives in math_gauge/execution.py, case contracts in catalog.py, and judgments/reporting in review.py.
- Run python3 -m unittest discover -s tests and python3 -m math_gauge validate for affected runner contracts.
  Compile only changed Lean fixtures or their dependent group; keep evidence tied to file hashes.
- Do not commit or push unless the user authorizes that step. Keep .dev-mesh and runs local.
