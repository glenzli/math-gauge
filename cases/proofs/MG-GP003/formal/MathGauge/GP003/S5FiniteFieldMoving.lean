/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5FiniteScalarMovingDescent
import MathGauge.GP003.S5SimultaneousFinite

noncomputable section
set_option maxHeartbeats 0
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe v u
namespace MathGauge.GP003.Transfers

/-- Over every finite field, the actual simultaneous moving geometry and the
original finite scalar traces produce one signed correspondence that factors
restriction for every HI PST, retaining every specified closed point. All
scalar opens, full preimages and extension degrees are constructed internally. -/
theorem exists_finiteField_finitelyMany_uniform_factor
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    {τ : Type u} [Fintype τ] (points : τ → PrimeSpectrum B)
    [∀ j, (points j).asIdeal.IsMaximal] (i₀ : τ)
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    ∃ (U : (affineSite k B).left.Opens), Set.range points ⊆ (U : Set (affineSite k B).left) ∧
      ∃ β : Cor.mk ((SmoothZariski.opensFunctor (affineSite k B)).obj U) ⟶ Cor.mk A,
        ∀ (P : PresheafWithTransfers.{v} k), P.IsA1Invariant →
          P.transfer ((Cor.graphFunctor k).map a) ≫ P.transfer β =
            P.transfer ((Cor.graphFunctor k).map
              (SmoothZariski.openInclusion (affineSite k B) U)) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let p := ringChar k
  let : Fact p.Prime := ⟨CharP.prime_ringChar k⟩
  obtain ⟨n, m, hn, hm, hnm, h⟩ :=
    S5Simultaneous.exists_two_prime_finitelyMany_native_moving
      k B p points i₀ J hJ g hg d hd a ha hcover 0
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let E := ULift.{u} (FiniteField.Extension k p n)
  let L := ULift.{u} (FiniteField.Extension k p m)
  obtain ⟨hdegreeE, T, rE, hT, hrE, hE, hmE⟩ := h n (Or.inl rfl)
  obtain ⟨hdegreeL, T', rL, hT', hrL, hL, hmL⟩ := h m (Or.inr rfl)
  have : IsOpenImmersion rE.left := hrE
  have : IsOpenImmersion rL.left := hrL
  have hdegree : (Module.finrank k E).Coprime (Module.finrank k L) := by
    rw [hdegreeE, hdegreeL]
    exact hnm
  exact exists_uniform_factor_of_coprime_scalar_moving
    (E := E) (L := L) (affineSite k B) a (Set.range points)
    rE rL hE hL hmE hmL hdegree

end MathGauge.GP003.Transfers
