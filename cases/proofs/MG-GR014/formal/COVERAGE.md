# MG-GR014 author formal coverage

All six stages are implemented. This is author formal evidence, not human approval or candidate performance. The exact statements and source hashes appear in `alignment.json`.

| Stage | Formal obligations |
|---|---|
| S1 | Full coefficient functions on finite I converted to Finsupp with exact pairing; row span and coordinate span; actual solution/fiber parameter maps and both affine dimensions; exact extension criterion |
| S2 | Three cardinality formulas; actual image and common fiber product decomposition; both image-exponent forms; empty cases included |
| S3 | Nonempty global solutions, compact closed solution set, totally disconnected subspace, closed coordinate images and exact finite joint row/coordinate realizability |
| S4 | Explicit unrestricted-field algebraic global existence, all solutions, every image and all nonempty fibers |
| S5 | All finite coordinate equations x_i=1 have finite-support solutions; the entire system has none |
| S6 | Exact eliminated finite-coordinate equations and their closedness over any discrete field, including infinite fields |

`LinearSystems.lean` and `CoordinateFibers.lean` are byte-identical copies of public MG-R014 author modules, with frozen identity in alignment provenance. New obligations are in `ProgressiveLinearSystems.lean` and `AffineDimensions.lean`. Actual assignment domains remain full products; finite support is imposed only on coefficient rows except in the explicit S5 counterexample. `AffineDimensions.direction` is an actual subspace of the original full assignment space. `directionEquiv` is a genuine linear equivalence from the quotient dual, and `solution_is_translate` / `fiber_is_translate` prove exactly that the original solution and fiber sets are translates of these direction spaces. Their actual finranks are computed in `actual_solution_and_fiber_dimensions`; no dimension is inferred from a plain set bijection.

For S3, compactness uses actual closed subspaces of compact products. Nonemptiness and the finite joint extension criterion use the already proved algebraic extension applied to an explicit augmented row system. This valid alternative proof avoids an unnecessary repeated finite-intersection compactness argument, as permitted by the alternative-proofs contract; no independently chosen finite solutions are treated as a compatible family. S6 does not assume compactness of an infinite field.

All local modules receive fresh isolated compilation and dynamic whole-module axiom audit by the shared verifier. No old build output is reused. Human review remains pending; no candidate model has run.
