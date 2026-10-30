/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5GenericRepresentative
import MathGauge.GP003.S5InfiniteAffineMoving

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme
universe u
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

/-- A common restriction factor is a geometric intermediate statement about
actual correspondences and their action on every HI additive presheaf. The
final S5 theorem will instantiate this predicate with the proved producers. -/
def IntegralAffineMoving (k : Type u) [Field k] : Prop :=
  ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (s : Finset X.left), s.Nonempty →
    ∀ (A : SmoothSite (Spec (.of k))) [IsAffine A.left] [Nonempty A.left]
      (a : A ⟶ X) [IsOpenImmersion a.left],
      ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
        IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑s : Set X.left) ⊆ Set.range r.left ∧
          ∃ β : Cor.mk S ⟶ Cor.mk A, ∀ (P : PresheafWithTransfers.{u+1} k),
            P.IsA1Invariant → P.transfer ((Cor.graphFunctor k).map r) =
              P.transfer ((Cor.graphFunctor k).map a) ≫ P.transfer β

/-- The infinite-field producer proves the predicate, including dimension
zero and arbitrary points, without any presheaf-specific hypothesis. -/
theorem integralAffineMoving_infinite [Infinite k] : IntegralAffineMoving k := by
  intro X _ _ s hs A _ _ a _
  obtain ⟨S, r, hS, hr, hsr, β, α, h0, h1⟩ :=
    exists_infinite_integral_affine_moving X s hs a
  exact ⟨S, r, hS, hr, hsr, β, fun P hP =>
    restriction_factor_of_moving_endpoints P hP r a β α h0 h1⟩

/-- Actual simultaneous vanishing on an integral affine model. This consumes
the geometric factor once; it does not combine unrelated pointwise zeros. -/
theorem integral_affine_kernel_zero
    (hgeometry : IntegralAffineMoving k)
    (P : PresheafWithTransfers.{u+1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (s : Finset X.left) (hs : s.Nonempty) (a : P.sections (Cor.mk X))
    (ha : (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).app (op X) a = 0) :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑s : Set X.left) ⊆ Set.range r.left ∧
        P.transfer ((Cor.graphFunctor k).map r) a = 0 := by
  let η := CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
    ((toPresheaf k).obj P)
  have heq : η.app (op X) a = η.app (op X) 0 := by simpa using ha
  have hcover := Presheaf.equalizerSieve_mem (SmoothZariski.topology (Spec (.of k))) η a 0 heq
  obtain ⟨x, hx⟩ := hs
  obtain ⟨Y, f, y, hfzero, hf, _⟩ := hcover x
  have := hf
  obtain ⟨i, t, _⟩ := Y.left.affineCover.exists_eq y
  let A : SmoothSite (Spec (.of k)) := SmoothSite.mk (Y.left.affineCover.f i ≫ Y.hom)
  let c : A ⟶ Y := SmoothSite.homMk (Y.left.affineCover.f i) rfl
  have : IsAffine A.left := inferInstanceAs (IsAffine (Y.left.affineCover.X i))
  have : Nonempty A.left := ⟨t⟩
  have : IsOpenImmersion (c ≫ f).left :=
    inferInstanceAs (IsOpenImmersion (Y.left.affineCover.f i ≫ f.left))
  have hv : P.transfer ((Cor.graphFunctor k).map (c ≫ f)) a = 0 := by
    change P.transfer ((Cor.graphFunctor k).map f) a =
      P.transfer ((Cor.graphFunctor k).map f) 0 at hfzero
    rw [map_zero] at hfzero
    rw [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply, hfzero, map_zero]
  obtain ⟨S, r, hS, hr, hsr, β, hfactor⟩ := hgeometry X s ⟨x, hx⟩ A (c ≫ f)
  refine ⟨S, r, hS, hr, hsr, ?_⟩
  rw [hfactor P hP, ConcreteCategory.comp_apply, hv, map_zero]

/-- Actual simultaneous section lifting on an integral affine model, using
one original affine representative and one common genuine moving factor. -/
theorem integral_affine_section_lift
    (hgeometry : IntegralAffineMoving k)
    (P : PresheafWithTransfers.{u+1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (s : Finset X.left) (hs : s.Nonempty)
    (b : (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).obj (op X)) :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑s : Set X.left) ⊆ Set.range r.left ∧
        ∃ a : P.sections (Cor.mk S),
          (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
            ((toPresheaf k).obj P)).app (op S) a =
          (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
            ((toPresheaf k).obj P)).map r.op b := by
  obtain ⟨A, hA, hne, a, ha, v, hv⟩ := exists_affine_zariski_representative P X b
  have := hA
  have := hne
  have := ha
  obtain ⟨S, r, hS, hr, hsr, β, hfactor⟩ := hgeometry X s hs A a
  exact ⟨S, r, hS, hr, hsr,
    zariski_section_lift_of_transfer_factor P hP r a β hfactor b v hv⟩

end MathGauge.GP003.Transfers
