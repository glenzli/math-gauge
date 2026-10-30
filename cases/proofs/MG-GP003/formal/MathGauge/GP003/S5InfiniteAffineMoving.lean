/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5SimultaneousUniversal
import MathGauge.GP003.S5FiniteClosedPointReduction
import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Complement.AffineOpenComplementIdeal
import Motivic.Cohomology.A1.Moving.ZeroDimensional
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open Motivic.OneSidedMovingEndpoints
universe u
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

/-- Zero-dimensional smooth domains are fields, so a nonempty open immersion
into their spectrum is already an isomorphism. This holds over every field. -/
theorem affine_open_isIso_of_trdeg_zero
    (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (hd : Algebra.trdeg k B = 0)
    {A : SmoothSite (Spec (.of k))} [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left] : IsIso a := by
  have : Algebra.IsAlgebraic k B := (trdeg_eq_zero_iff).mp hd
  let : Field B := (isField_of_isIntegral_of_isField' (R := k) (S := B)
    (Field.toIsField k)).toField
  have ha : Function.Surjective a.left := by
    obtain ⟨x⟩ := ‹Nonempty A.left›
    intro y
    have : Subsingleton (PrimeSpectrum B) := inferInstance
    exact ⟨x, @Subsingleton.elim (PrimeSpectrum B) this (a.left x) y⟩
  have : Surjective a.left := ⟨ha⟩
  have : IsIso a.left := (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, inferInstance⟩
  have : IsIso ((SmoothSite.forgetScheme _).map a) := ‹IsIso a.left›
  exact isIso_of_reflects_iso a (SmoothSite.forgetScheme _)

/-- The identity has a literal constant A1-homotopy through any isomorphic
open. This supplies the zero-dimensional geometry without a positive-dimension
presentation or any hypothesis on a presheaf. -/
theorem moving_identity_of_isIso
    {X V : SmoothSite (Spec (.of k))} (v : V ⟶ X) [IsIso v] :
    HasMovingEndpoints (𝟙 X) v := by
  refine ⟨(Cor.graphFunctor k).map (inv v),
    (Cor.graphFunctor k).map (SmoothSite.a1Projection (.of k) X), ?_, ?_⟩
  · rw [← Functor.map_comp, SmoothSite.a1Section_projection]
  · rw [← Functor.map_comp, SmoothSite.a1Section_projection,
      ← Functor.map_comp, IsIso.inv_hom_id]

/-- The finite-point original moving theorem over an infinite field, with no
closedness or positive-dimension restriction on the original finite points.
Closed specializations, generators, complementary ideal and dimension split
are all constructed from the stated data. -/
theorem exists_infinite_affine_moving
    [Infinite k] (B : Type u) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (s : Finset (Spec (.of B))) (hs : s.Nonempty)
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left] :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ originalAffineObject k B),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧
      (↑s : Set (Spec (.of B))) ⊆ Set.range r.left ∧ HasMovingEndpoints r a := by
  classical
  by_cases hd : Algebra.trdeg k B = 0
  · have : IsIso a := affine_open_isIso_of_trdeg_zero B hd a
    refine ⟨originalAffineObject k B, 𝟙 _,
      (inferInstanceAs (IsAffine (Spec (.of B)))), inferInstance, ?_,
      moving_identity_of_isIso a⟩
    intro x _
    exact ⟨x, rfl⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : JacobsonSpace (Spec (.of B)) :=
    LocallyOfFiniteType.jacobsonSpace (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  obtain ⟨t, ht, hts, hne⟩ := exists_finite_closed_specializations s
  let τ := {x : Spec (.of B) // x ∈ t}
  let points : τ → PrimeSpectrum B := fun x => x.val
  have hp : ∀ j : τ, (points j).asIdeal.IsMaximal := fun j =>
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal j.val).mp (ht j.val j.property)
  let : ∀ j : τ, (points j).asIdeal.IsMaximal := hp
  obtain ⟨x₀, hx₀⟩ := hne hs
  let i₀ : τ := ⟨x₀, hx₀⟩
  let J := Scheme.openComplementIdeal B a.left.opensRange
  have hJ : J ≠ ⊥ := Scheme.openComplementIdeal_ne_bot B a.left.opensRange
    (Set.range_nonempty a.left)
  have hr : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      (Set.range a.left)ᶜ := by
    simpa only [Scheme.Hom.coe_opensRange] using
      Scheme.range_openComplementIdeal B a.left.opensRange
  have ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [hr]
    exact disjoint_compl_right
  have hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
    intro y
    rw [hr]
    exact Classical.em _
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k) (A := B)
  have hg : Algebra.adjoin k (Set.range (fun t : G => (t : B))) = ⊤ := by
    convert hG using 1
    congr 1
    ext b
    simp
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := B))
  cases n with
  | zero => exact (hd (by simpa using hn)).elim
  | succ d =>
    obtain ⟨S, r, hS, hr, hpoints, hm⟩ :=
      S5Simultaneous.exists_finitelyMany_original_moving k B points i₀ J hJ
        (fun t : G => (t : B)) hg d hn a ha hcover
    have := hr
    refine ⟨S, r, hS, hr, ?_, hm⟩
    exact hts r.left.opensRange (fun x hx => hpoints ⟨x, hx⟩)


/-- Affine-coordinate transport retains the original smooth-site object and
its original finite (possibly nonclosed) point set. -/
theorem exists_infinite_integral_affine_moving
    [Infinite k] (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (s : Finset X.left) (hs : s.Nonempty)
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ X) [IsOpenImmersion a.left] :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧
      (↑s : Set X.left) ⊆ Set.range r.left ∧ HasMovingEndpoints r a := by
  classical
  let : Algebra k Γ(X.left, ⊤) := AffineCoordinates.sectionsAlgebra X
  let e : affineSite k Γ(X.left, ⊤) ≅ X := AffineCoordinates.affineIso X
  let s' : Finset (Spec (.of Γ(X.left, ⊤))) := s.image e.inv.left
  have hs' : s'.Nonempty := hs.image e.inv.left
  have : IsOpenImmersion (a ≫ e.inv).left :=
    inferInstanceAs (IsOpenImmersion (a.left ≫ X.left.isoSpec.hom))
  obtain ⟨S, r, hS, hr, hsr, hm⟩ :=
    exists_infinite_affine_moving Γ(X.left, ⊤) s' hs' (a ≫ e.inv)
  have := hr
  have hcomp : IsOpenImmersion (r ≫ e.hom).left :=
    inferInstanceAs (IsOpenImmersion (r.left ≫ X.left.isoSpec.inv))
  refine ⟨S, r ≫ e.hom, hS, hcomp, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht⟩ := hsr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    refine ⟨t, ?_⟩
    change e.hom.left (r.left t) = x
    rw [ht]
    exact congrArg (fun f => f.left x) e.inv_hom_id
  · exact hm.postcompose e.hom (𝟙 A) a (by simp)

end MathGauge.GP003.Transfers
