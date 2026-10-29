# MG-GR012 author Lean coverage

All six stages are formalized. The exact stage declaration map, hypothesis/quantifier/domain audit and frozen source hashes are in `alignment.json`. Human review is pending; no candidate model was run.

| Stage | Mathematical coverage |
|---|---|
| S1 | Native matrix and Euclidean-space coordinate bridge; actual support square identity, cyclic monotonicity, complete subgradient singleton and uniqueness of every normalized extended-valued supporting potential. Differentiability is derived from the supplied support record through an explicit quadratic remainder bound. |
| S2 | Actual EReal supremum on the whole primal space, completion of squares, inverse derived from positive definiteness, the unique optimizer, Fenchel gap/equality, actual dual derivative and both gradient inverse identities. |
| S3 | Semidefinite finite domain b+im Q, value independent of chosen preimage, all optimizers v+ker Q and uniqueness iff the kernel is zero. An actual orthogonal kernel direction makes the objective exceed every real bound outside the image. The zero scalar operator is a fully instantiated counterexample. |
| S4 | Exact copied parent path-supremum construction on the original topological vector space, with no added norm, Hilbert, Hausdorff, completeness or local-convexity assumptions. Properness, lower semicontinuity, convexity, all supports, minimum and uniqueness are all proved. |
| S5 | The actual singleton input has canonical zero potential and a strict extra subgradient at (1,0). |
| S6 | Original-topology monotonicity and supremum over every finite subrecord. Every finite subrecord containing the base is represented by the actual Finset Γ index. Finite slope bounds and cyclicity prove finite potentials are real-valued; in finite dimension convexity gives continuity. Actual real monotone convergence and the directed-net Dini theorem yield TendstoUniformlyOn on any compact set. |

## Proof routes and closure

S1 uses a proved differentiability estimate and equality of derivatives instead of the reference Riemann-sum route. S6 bounds finite path slopes and uses finite-dimensional convex continuity instead of deleting cycles. These are complete alternative proofs explicitly permitted by the contract; no desired conclusion is assumed.

`CyclicPotential.lean` is copied byte-for-byte from `cases/public/MG-R012/formal/CyclicPotential.lean`, with exact hash and base commit in the alignment record. The other four modules are new. The shared v2 verifier compiles the entire closure in isolation with Lean 4.29.1 and pinned mathlib, then audits all local declarations, including private declarations. This compiler evidence is separate from independent semantic review and human approval.
