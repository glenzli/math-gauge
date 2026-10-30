# MG-GP003 S5: completed target and scope of the proof

S5 has no remaining author-formalization gap. The endpoint is the literal
canonical Zariski sheafification unit on the original-X neighborhood colimit,
proved in `MathGauge/GP003/S5Complete.lean`. This record replaces the earlier
G0–G4 frontier; the earlier version remains in Git. It does not reclassify
conditional helpers as unconditional theorems.

## What closed the previous frontier

| Previous obligation | Actual proof now used |
| --- | --- |
| G0: genuine finite correspondences and HI PST | Fixed Motivic/Aglib/Mathlib sources, Lean 4.34.1, actual Cor composition/graph/A1 structures, audited transitive source and axiom closure. |
| G1: one neighborhood preserving all selected points | `S5SimultaneousUniversal` constructs simultaneous moving geometry over infinite fields. `S5SimultaneousFinite` and `S5FiniteScalarMovingDescent` retain full scalar preimages and descend via two coprime degrees. `S5AllFieldMoving` proves the all-field producer. |
| G2: actual Zariski separated quotient | `S5ZariskiKernel` identifies the actual Nis unit kernel with Zariski locally zero sections, proves stability under transfers, and identifies the objectwise quotient with the genuine unit image. HI and ordinary Zariski sheafification comparison are proved. |
| G3: geometry sufficient for S5 | The completed proof uses one common transfer restriction factor, kernel vanishing and section lifting. It does not require the stronger two-open exactness theorem or instantiate `SingletonBlockGluing`. |
| G4: finite assembly, original ambient and canonical site unit | Actual Cor finite coproducts handle clopen integral components; actual affine refinement and open-image maps return to original-X opens. `S5SiteBridge` identifies ordinary big/small Zariski sheafification and its unit. |

## Endpoints and exact hypotheses

`MathGauge.GP003.Transfers.semilocal_zariski_unit_isIso` takes:

- an arbitrary field k;
- an actual `Motivic.PresheafWithTransfers k` P and its A1 invariance;
- a genuine smooth separated finite-type object X;
- an arbitrary nonempty finite set of points s in X;
- the affine open W containing s already selected when the task defines S.

Its conclusion is `IsIso (SmoothZariski.siteNeighborhoodUnit X F s)` for the
actual underlying presheaf F. The index consists of all original-X opens
containing s, with restriction toward smaller opens, exactly as in the task.
`semilocal_small_zariski_unit_isIso` proves the ordinary small-site unit
statement using the proved canonical-unit identity, not an unrelated abstract
isomorphism.

No separation of P, infinite/perfect-field condition, geometrically integral
condition, ambient closed-point condition, transfer factor, or lifting property
is assumed at either endpoint. Internal integral/closed-point reductions are
proved and removed. The zero-dimensional case is handled by an actual open
isomorphism; positive dimension is not an endpoint restriction.

## Boundaries retained explicitly

The common affine open is part of the task's chosen presentation. As for S1/S2,
we prove the result for every such presentation; a separate theorem deriving
that presentation from a formal `IsQuasiProjective` predicate is not claimed.
The values in S5 are already defined by these original-X colimits.

The old `S5FiniteInduction` proves valid conditional statements about ordinary
presheaves. Its `SingletonBlockGluing` is still an explicit input there. The
completed S5 route does not use it and does not claim to have formalized every
part of MVW Lemma 22.10, including its stronger two-open surjectivity result.
The reference's source-based reconstruction and the new direct formal proof
are two sufficient routes to the same S5 target.

The fixed native dependency and its transitive imported sources are part of
the verification evidence. Successful compilation and a standard-three-axiom
audit establish formal derivability; source-bound independent review checks
mathematical alignment. Neither constitutes human approval or candidate model
performance. Human review remains pending; no candidate model was run.
