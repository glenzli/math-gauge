/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5IntegralComparison
import MathGauge.GP003.S5FiniteFieldMoving

noncomputable section
set_option maxHeartbeats 0
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

/-- Finite-field moving for arbitrary finite original points. Closed auxiliary
specializations, complementary ideal, generators, dimension split, both scalar
extensions, and the final affine common shrink are all constructed here. -/
theorem exists_finite_affine_uniform_factor
    [Finite k] (B : Type u) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (s : Finset (Spec (.of B))) (hs : s.Nonempty)
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left] :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ affineSite k B),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧
      (↑s : Set (Spec (.of B))) ⊆ Set.range r.left ∧
        ∃ β : Cor.mk S ⟶ Cor.mk A, ∀ (P : PresheafWithTransfers.{u+1} k),
          P.IsA1Invariant → P.transfer ((Cor.graphFunctor k).map r) =
            P.transfer ((Cor.graphFunctor k).map a) ≫ P.transfer β := by
  classical
  by_cases hd : Algebra.trdeg k B = 0
  · have : IsIso a := affine_open_isIso_of_trdeg_zero B hd a
    refine ⟨affineSite k B, 𝟙 _,
      (inferInstanceAs (IsAffine (Spec (.of B)))), inferInstance, ?_,
      (Cor.graphFunctor k).map (inv a), ?_⟩
    · intro x _
      exact ⟨x, rfl⟩
    · intro P _
      rw [← transfer_comp, ← (Cor.graphFunctor k).map_comp, IsIso.inv_hom_id]
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
    obtain ⟨U, hU, β, hβ⟩ := exists_finiteField_finitelyMany_uniform_factor
      k B points i₀ J hJ (fun t : G => (t : B)) hg d hn a ha hcover
    let sB : Finset (PrimeSpectrum B) := s
    have hsU : (↑sB : Set (PrimeSpectrum B)) ⊆ U.1 :=
      hts U (fun x hx => hU (Set.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩))
    obtain ⟨f, hsf, hfU⟩ := PrimeSpectrum.exists_basicOpen_of_finite_subset
      U (↑sB : Set (PrimeSpectrum B)) sB.finite_toSet hsU
    let W : (affineSite k B).left.Opens := PrimeSpectrum.basicOpen f
    let S := (SmoothZariski.opensFunctor (affineSite k B)).obj W
    let r := SmoothZariski.openInclusion (affineSite k B) W
    let q : S ⟶ (SmoothZariski.opensFunctor (affineSite k B)).obj U :=
      (SmoothZariski.opensFunctor (affineSite k B)).map (homOfLE hfU)
    have hq : q ≫ SmoothZariski.openInclusion (affineSite k B) U = r := by
      apply MorphismProperty.Over.Hom.ext
      exact (affineSite k B).left.homOfLE_ι hfU
    have : IsAffine S.left := IsAffineOpen.Spec_basicOpen f
    have : IsOpenImmersion r.left := inferInstance
    refine ⟨S, r, inferInstance, inferInstance, ?_, (Cor.graphFunctor k).map q ≫ β, ?_⟩
    · intro x hx
      exact ⟨⟨x, hsf hx⟩, rfl⟩
    · intro P hP
      rw [transfer_comp, ← Category.assoc, hβ P hP,
        ← transfer_comp, ← (Cor.graphFunctor k).map_comp, hq]

/-- Native affine-coordinate transport preserves the original arbitrary point
set and the same correspondence action on every HI presheaf. -/
theorem exists_finite_integral_affine_uniform_factor
    [Finite k] (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (s : Finset X.left) (hs : s.Nonempty)
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ X) [IsOpenImmersion a.left] :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑s : Set X.left) ⊆ Set.range r.left ∧
        ∃ β : Cor.mk S ⟶ Cor.mk A, ∀ (P : PresheafWithTransfers.{u+1} k),
          P.IsA1Invariant → P.transfer ((Cor.graphFunctor k).map r) =
            P.transfer ((Cor.graphFunctor k).map a) ≫ P.transfer β := by
  classical
  let : Algebra k Γ(X.left, ⊤) := AffineCoordinates.sectionsAlgebra X
  let e : affineSite k Γ(X.left, ⊤) ≅ X := AffineCoordinates.affineIso X
  let s' : Finset (Spec (.of Γ(X.left, ⊤))) := s.image e.inv.left
  have hs' : s'.Nonempty := hs.image e.inv.left
  have : IsOpenImmersion (a ≫ e.inv).left :=
    inferInstanceAs (IsOpenImmersion (a.left ≫ X.left.isoSpec.hom))
  obtain ⟨S, r, hS, hr, hsr, β, hβ⟩ :=
    exists_finite_affine_uniform_factor Γ(X.left, ⊤) s' hs' (a ≫ e.inv)
  have := hr
  have hcomp : IsOpenImmersion (r ≫ e.hom).left :=
    inferInstanceAs (IsOpenImmersion (r.left ≫ X.left.isoSpec.inv))
  refine ⟨S, r ≫ e.hom, hS, hcomp, ?_, β, ?_⟩
  · intro x hx
    obtain ⟨t, ht⟩ := hsr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    refine ⟨t, ?_⟩
    change e.hom.left (r.left t) = x
    rw [ht]
    exact congrArg (fun f => f.left x) e.inv_hom_id
  · intro P hP
    rw [(Cor.graphFunctor k).map_comp, transfer_comp, hβ P hP, ← Category.assoc,
      ← transfer_comp, ← (Cor.graphFunctor k).map_comp]
    have he : (a ≫ e.inv) ≫ e.hom = a := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun f : A ⟶ X => P.transfer ((Cor.graphFunctor k).map f) ≫ P.transfer β) he

theorem integralAffineMoving_finite [Finite k] : IntegralAffineMoving k := by
  intro X _ _ s hs A _ _ a _
  exact exists_finite_integral_affine_uniform_factor X s hs a

/-- Actual finite-correspondence moving on all fields, all integral smooth
affine models, and every finite nonempty set of their original points. This
is the proved geometric producer; no geometry predicate is an assumption. -/
theorem integralAffineMoving_of_field (k : Type u) [Field k] : IntegralAffineMoving k := by
  cases finite_or_infinite k
  · exact integralAffineMoving_finite
  · exact integralAffineMoving_infinite

end MathGauge.GP003.Transfers
