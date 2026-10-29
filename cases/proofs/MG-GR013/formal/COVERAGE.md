# MG-GR013 author formal coverage

All six mandatory stages are formally implemented. This is author proof coverage; independent semantic review and human review are separate evidence, and no candidate model has been run.

| Stage | Actual content |
|---|---|
| S1 | Finite-dimensional strong-to-norm convergence and full-sequence spectral recovery by actual nearest characteristic-polynomial roots |
| S2 | Eventual spectral avoidance on the whole compact set, uniform convergence of actual two-sided resolvents, norm convergence for every fixed polynomial |
| S3 | Strong convergence of fixed powers and all polynomials; operator norm liminf inequality with boundedness verified |
| S4 | Complete actual c0 counterexample, all polynomial norms and finite ranks, nilpotent spectra and unrecoverable limiting spectral point |
| S5 | Actual finite geometric inverse, both inverse equations, uniqueness, exact norm max(1,n), unboundedness |
| S6 | Exact norms of positive powers, all inner limits separately, the two outer limits, failure of a threshold uniform in degree |

S1 uses a shorter valid route than the reference: the factorization of each monic characteristic polynomial gives an actual root within epsilon when its value at the limiting root is smaller than epsilon to the common degree. Determinant continuity gives this eventually. Nearest-root selection is available at every index because the common dimension is positive, so the result concerns an entire sequence and not just a subsequence. The characteristic-polynomial/spectrum bridge and the finite basis/operator topology bridge are both explicit.

S2 is proved in the stronger setting of an arbitrary complex Banach space under operator norm convergence. Inversion is jointly continuous near each actual unit; the compact tube-neighborhood lemma yields one eventual threshold and the required uniform convergence. This is an alternative to the quantitative Neumann-series proof, with exactly the stated conclusions. S3 works also for the zero space and does not strengthen strong convergence to norm convergence.

Polynomial notation is the finite coefficient-list representation sum(k=0..d) a_k T^k, covering every polynomial and retaining a_0 I on the full common space. S6 uses the real power of the actual norm and proves the numerical 0/1 formula from the actual shift, then both orders of limits.

The four parent modules are copied byte for byte, with exact provenance hashes in alignment.json. The whole explicit case closure is freshly compiled and dynamically audited by the shared verifier. No assumed goal, placeholder proof, new axiom or inherited candidate score is used.
