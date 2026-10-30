# MG-GP003: exact remaining formal obligations

This is a frontier record, not a list of new theorem assumptions. No declaration in
this author project assumes the MVW conclusion or introduces the statements below
as axioms. The underlying mathematics was checked against the primary source;
`SOURCE-RECHECK.md` separates that evidence from the Lean boundary.

## Existing actual objects

* `FinitePrimeLocalization.lean` defines `outside_primes sigma` and
  `finite_prime_localization sigma = Localization (outside_primes sigma)` and
  proves the image and closed-point statements, including nonclosed ambient points.
* `AffineScheme.lean` defines `finite_point_scheme sigma : Scheme` as the actual
  `Spec` of that localization, and proves the closed-point cover criterion.
* `NeighborhoodValues.lean` defines `neighborhood_value E s : AddCommGrpCat`
  using the actual colimit of the restriction functor on `SetNeighborhoods s`.
  `finite_neighborhood_sheafification_comparison E sigma` is the actual
  colimit map induced by the ordinary small-site Zariski sheafification unit.
* `MathGauge/GP003/FiniteGermDescent.lean` uses actual stalks and actual colimits
  of `E(U ∩ V)` over pairs of point neighborhoods. Its overlap maps come from
  restriction and final product projections; the refinement lemma extracts
  an actual equality of restrictions, not a supplied descent certificate.
* `MathGauge/GP003/TwoPointComparison.lean` proves the two-point comparison for
  actual abelian presheaves and sheaves on the small site. Its shrinking
  hypothesis is exactly the one explicitly supplied in S2.

The type of the remaining small-site endpoint, with no unbound symbolic maps, is:

```lean
{X : TopCat.{u}} (E : X.Presheaf AddCommGrpCat.{u}) (sigma : Finset X) ⊢
  IsIso (MathGauge.PublicProof.Semilocal.finite_neighborhood_sheafification_comparison
    E sigma)
```

It is **false for arbitrary E**. The missing transfer geometry must prove it for
the actual restriction of the specified homotopy invariant presheaf with transfers.
A theorem assuming this `IsIso`, or an arbitrary package of its consequences,
would not complete S5.

## G0: integrate the transfer objects before stating geometric lemmas

The frozen Lean 4.29.1/Mathlib snapshot has no located actual `Cor_k`/PST interface.
The inspected public library at commit
`a6805c4a87cdfd7717dd7a94039246a167f15380` supplies the actual types

```lean
Motivic.Cor k
Motivic.PresheafWithTransfers.{v} k = (Motivic.Cor k)ᵒᵖ ⥤+ AddCommGrpCat.{v}
```

and the actual proposition `P.IsA1Invariant`. Its smooth objects, finite integral
correspondences, intersection/pushforward composition, graph functor, and ordinary
presheaf restriction must be imported with their audited dependency closure or
proved under the frozen pin. That library uses Lean 4.34.1 and different Mathlib
and Aglib pins; its declarations are **not** imported or compiler-verified here.
Its checked Nisnevich sheafification endpoint is different from S5.

Readable fixed source locations are recorded in
`verification/author/gp003-frontier/external-sources.json` (repository relative),
with the new focused checks in `transfers/upstream-recheck.json`.
In particular: `Motivic/AlgebraicGeometry/Correspondences/Basic.lean`,
`Motivic/Transfers/Presheaf/Basic.lean`, and
`Motivic/Cohomology/A1/Sheafification/DenseDetection.lean`.

## G1: simultaneous finite-point generic detection

For the actual restricted HI PST E, prove injectivity of the canonical map from
`neighborhood_value E sigma` to the product of its generic stalks, one per
irreducible component meeting sigma. In the integral case this is a single
actual stalk. The map must be assembled from `E.germ U eta h_eta_U`; every
`U` in `SetNeighborhoods sigma` contains the relevant generic point.
The required result concerns the original E before separatedness is known.

Minimal geometric input: a section vanishing on a dense open becomes zero on
one open neighborhood containing **all** selected points at once, over every
field. A collection of unrelated single-point neighborhoods is insufficient for
a presheaf, because gluing or separation cannot be assumed at this step.
The external all-field local-zero and separated dense-detection results do not
by themselves prove this simultaneous statement.

## G2: the actual Zariski separated quotient retains transfers and HI

Use the actual presheaf kernel of the ordinary Zariski unit. For every actual
finite correspondence alpha, prove its transfer sends locally zero sections to
locally zero sections. Descend the action to the actual objectwise quotient;
verify identity, composition, additivity and the actual A1 projection isomorphism.
Identify its ordinary Zariski sheafification with that of E and identify the
canonical units. G1 must then give the canonical bijection on each finite-point
neighborhood colimit. A Nisnevich unit image cannot be substituted without a
proved comparison with this Zariski quotient.

The current actual small-site kernel/unit exists through Mathlib sheafification,
but no type for a Zariski **transfer** quotient is claimed under the frozen pin.
The missing first dependency is G0, not an omitted proof on a preexisting type.

## G3: successful finite-point shrinking with actual section maps

After constructing the genuine small-site extension E on the semilocal scheme,
the minimum exactness endpoint needed for the two-block induction is the
following existing, elaborated type shape:

```lean
∀ U0 V : Opens S,
  Separates A B U0 V → U0 ⊔ V = ⊤ →
  ∃ U : Opens S, U ≤ U0 ∧ U ⊔ V = ⊤ ∧
    Function.Exact (MathGauge.GP003.twoOpenRestriction E U V)
      (MathGauge.GP003.twoOpenDifference E U V)
```

Here A and B must be the actual nonempty disjoint blocks of the finite closed
point set, and `Separates` is the existing definition in
`NeighborhoodRefinement.lean`. Injection of the first map is separately required
and follows only after the preceding separatedness/generic-detection steps.
The cited corrected geometric argument supplies even right surjectivity, which
is not needed by `comparison_two_closed_points`.

The proof must supply the shrink, not assume the original row is exact. Finite
fields and points not closed in the original X remain in scope. This geometry
is not proved by the elementary neighborhood-refinement lemmas in this project.

## G4: original ambient, finite assembly and remaining site bridge

Completed in this revision:

* `AffineRestriction` proves the actual image/preimage adjunction for an open
  immersion into any ambient X, the canonical neighborhood colimit comparison,
  and naturality for both original presheaf maps and actual scheme restrictions.
* `GeneralAmbient.general_semilocal_descent_exact` is S1 for the original G on X,
  with actual local schemes, actual fiber products and both actual arrows.
  `generalFinitePointValueIso` identifies the values with the original-X finite
  point convention, including nonclosed ambient points, naturally in the unit.
* `GeneralAmbientNonOpen.NonOpenExample.closedPoint_local_not_open_immersion`
  supplies the explicit S1 counterexample inside a two-point semilocalization
  of the actual smooth affine plane over Q. It concerns the map to S itself,
  not merely a non-open map to the original ambient affine plane.
* `GeneralAmbientComparison.general_two_closed_comparison` transports S2's
  original map, injections, local surjections and successful shrinking row
  through these canonical comparisons. No target, extension-sheaf instance,
  unchanged-cover exactness or overlap surjectivity is assumed.
* `S5FiniteInduction` performs genuine finite insertion induction and recovers
  the literal original sheafification unit by `toSheafify_naturality`. Its
  `SingletonBlockGluing`, quotient finite-value isomorphism and quotient
  sheafification isomorphism are explicit **conditional** inputs. The module
  does not prove them for the task's original HI presheaf with transfers.

An affine chart presents the given semilocalization; the S1/S2 theorems hold for
all such presentations in arbitrary X and all commutative rings. A separate
common-affine-existence theorem from a formal `IsQuasiProjective` predicate is
not claimed. This no longer hides a missing restriction/value/map comparison.

Remaining for S5, in addition to G0–G3:

1. Prove the comparison between the actual big smooth-site Zariski
   sheafification and restriction to the small site, with its canonical unit.
2. Instantiate the finite assembly with the genuine transfer-separated quotient:
   derive its pointwise injections, actual `SingletonBlockGluing`, its finite
   point comparison with F and its sheafification comparison from G1–G3.
   Supplying these as inputs to the conditional helper is not completion.

The current source recheck is `transfers/upstream-recheck.json`. It records
actual signatures checked at the fixed upstream commit and focused searches;
it makes no claim that no other proof exists. Per-point zero neighborhoods,
Nisnevich unit images and sheaf hypotheses do not supply the missing original
presheaf simultaneous finite-point theorem.

S1 and S2 now have complete author coverage. S5 remains partial because of these
actual transfer-geometry and site obligations. No target is introduced as an
axiom, and no candidate model was run.
