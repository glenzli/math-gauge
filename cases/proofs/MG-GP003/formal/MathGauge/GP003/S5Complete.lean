/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5AffineComparison
import MathGauge.GP003.S5AllFieldMoving
import MathGauge.GP003.S5AmbientComparison

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme
universe u
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

local instance : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u+1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u+1, u+1, u, u} _

/-- GP003 S5: the literal canonical Zariski unit on the original-X all-open
neighborhood colimit is an isomorphism. W is the affine neighborhood already
selected in the problem's definition of S. The theorem imposes no separation
on P, no condition on the field, no ambient closedness of the finite points,
and no geometric factorization or lifting hypothesis. -/
theorem semilocal_zariski_unit_isIso
    (P : PresheafWithTransfers.{u+1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) (s : Finset X.left) (hs : s.Nonempty)
    (W : X.left.Opens) (hW : IsAffineOpen W) (hsW : (↑s : Set X.left) ⊆ W) :
    IsIso (SmoothZariski.siteNeighborhoodUnit X ((toPresheaf k).obj P)
      (↑s : Set X.left)) := by
  apply siteNeighborhoodUnit_isIso_of_affine_zero_lift ((toPresheaf k).obj P)
    (fun Y _ t ht a ha => affine_kernel_zero (integralAffineMoving_of_field k)
      P hP Y t ht a ha)
    (fun Y _ t ht b => affine_section_lift (integralAffineMoving_of_field k)
      P hP Y t ht b) X s hs W hW hsW

/-- The same statement for ordinary sheafification on the small Zariski site
of the original X. Its unit is canonically identified, not merely replaced
by an abstract isomorphic arrow. -/
theorem semilocal_small_zariski_unit_isIso
    (P : PresheafWithTransfers.{u+1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) (s : Finset X.left) (hs : s.Nonempty)
    (W : X.left.Opens) (hW : IsAffineOpen W) (hsW : (↑s : Set X.left) ⊆ W) :
    IsIso (SmoothZariski.neighborhoodMap X
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.left)
        ((SmoothZariski.opensFunctor X).op ⋙ ((toPresheaf k).obj P)))
      (↑s : Set X.left)) := by
  have h := semilocal_zariski_unit_isIso P hP X s hs W hW hsW
  have he := SmoothZariski.neighborhoodRestrictionIso_unit X ((toPresheaf k).obj P)
    (↑s : Set X.left)
  have : IsIso (SmoothZariski.neighborhoodMap X
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.left)
        ((SmoothZariski.opensFunctor X).op ⋙ ((toPresheaf k).obj P)))
      (↑s : Set X.left) ≫
    (SmoothZariski.neighborhoodRestrictionIso X ((toPresheaf k).obj P)
      (↑s : Set X.left)).hom) := by rw [he]; exact h
  exact IsIso.of_isIso_comp_right _
    (SmoothZariski.neighborhoodRestrictionIso X ((toPresheaf k).obj P)
      (↑s : Set X.left)).hom

end MathGauge.GP003.Transfers
