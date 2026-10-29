# MG-GR011 author formal coverage

All six stages are implemented. `alignment.json` binds stage statements, actual declarations and exact task source bytes. This is author formal evidence, not human approval.

| Stage | Formal coverage |
|---|---|
| S1 | Affine translate projection formula, actual nearest point and uniqueness, linearity iff the affine set contains zero |
| S2 | Rebase to a common origin with proof, nested-subspace reduction, both projection absorption identities, exact Pythagoras |
| S3 | Every finite family, including no factors; exact product range equals the intersection; actual orthogonal projection identification; all reorderings; two-factor iff commute |
| S4 | Arbitrary-index finite-subset net; actual global construction, unique minimum, norm convergence, supremum optimal value and nonexpansiveness |
| S5 | Actual singleton nonnegative-ray family with B=0; S4 global projection equals max x 0; explicit midpoint failure |
| S6 | VI/fixed-point equivalence, quantitative contraction, Banach construction, uniqueness, geometric error and convergence |

`ConvexProjection.lean` and `FiniteConstraints.lean` are byte-identical copies of public MG-R011 author modules; source identities are retained. New stages are in `AffineProjections.lean` and `VariationalIteration.lean`. Closed-subspace completeness is derived, and mathlib's existing orthogonal projection is used. Nonempty closed affine spaces are represented as translations of closed linear spaces; explicit rebase and inclusion equivalences justify the common-origin representation in S2. Finite lists and `Fin n` both occur in S3 so the empty product and arbitrary order are covered. The two-factor necessity uses adjoint symmetry, not just idempotence.

The VI estimate does not assume H nontrivial or infer m≤L without two distinct points. It uses s≤sqrt(s)^2, valid even for negative s in the zero-space case, so the stated q always works. It constructs the fixed point from the genuine contraction theorem and then proves the variational inequality; no certificate assumes the requested solution.

All modules receive fresh isolated compilation and whole-module dynamic axiom audit. Source-side or sibling build outputs are excluded. No candidate model execution; human review remains pending.
