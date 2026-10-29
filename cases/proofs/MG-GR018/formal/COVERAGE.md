# MG-GR018 author formal coverage

All six stages are formally implemented. The claim is author coverage under the explicit representation below, not human approval or candidate performance. `alignment.json` binds each stage to declarations and frozen source hashes.

| Stage | Actual content | Modules |
|---|---|---|
| S1 | Finite records are unique points; empty records impossible; arbitrary-universe finite skeleton transport | Both |
| S2 | Natural operations on all finite sets are uniquely coordinate projections; no nullary operation | ProgressiveObservations |
| S3 | Three-point majority is natural for every allowed map between targets of size at most two and differs from every point | ProgressiveObservations |
| S4 | Explicit ultrafilter equivalence, all finite fibers, functor and monad operations/laws, exact finite/infinite point boundary | FiniteObservations |
| S5 | Stone topology; every clopen is one basic set; observations continuous; every continuous finite observation has a unique originating map | ProgressiveObservations |
| S6 | Explicit unequal preimages at every nonpoint record; multiplication injective exactly for finite X | ProgressiveObservations |

The record definition ranges over finite Type 0 tests while the bottom set is arbitrary Type u. The copied module proves extension and uniqueness for finite targets in every universe using `Fin (card A)`; no hidden assumption that X is a small test is used. The natural-operation stage uses Type 0 finite tests exactly as in the task. Stone topology is the induced topology of the already proved equivalence to `Ultrafilter X`, and `recordHomeomorph` proves the correspondence. Standard compact Hausdorff extension and density results come from pinned Mathlib; the novel observation classification and clopen consequence are proved in the authored module.

`FiniteObservations.lean` is copied byte for byte from the public MG-R018 author source, with exact identity in alignment provenance. Compilation is fresh through the shared verifier; no old olean, declaration list or verification report is copied. No sorry, new axiom, assumed classification certificate or candidate run is used. Human review remains pending.
