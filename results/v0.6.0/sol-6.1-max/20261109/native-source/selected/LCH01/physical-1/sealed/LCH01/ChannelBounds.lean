import LCH01.MatrixInterfaces

/-!
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I,
§2.2 and Exercise 2.2, https://glenzli.com/books/oet/,
author ORCID https://orcid.org/0009-0006-6536-3453,
DOI 10.5281/zenodo.21457931. License: CC BY 4.0,
https://creativecommons.org/licenses/by/4.0/.
This file supplies new Lean proofs of the selected statements.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-- Algebraic row reduction, valid also for infinite ENNReal coefficients. -/
theorem singleInputRow_sum {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) {L : ChannelMatrix I} {i j : I}
    (hrow : SingleInputRow L i j) (x y : X) :
    (∑ k : I, entry L k j * d k x y) = entry L i j * d i x y := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- CH02-P19: a row supported on one input gives the scalar Lip bound. -/
theorem single_input_lip_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {L : ChannelMatrix I} {i j : I}
    (hL : L ∈ restrictedLipMatrices d φ U) (hrow : SingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L i j * d i x y := by
  intro x hx y hy
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, entry L k j * d k x y :=
      hL.2 x hx y hy j
    _ = entry L i j * d i x y := singleInputRow_sum d hrow x y

/-- CH02-P19, diagonal special case, simultaneously for every output. -/
theorem diagonal_lip_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {L : ChannelMatrix I}
    (hL : L ∈ restrictedLipMatrices d φ U) (hdiag : IsDiagonal L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro j
  exact single_input_lip_bound d hd hL (diagonal_singleInputRow hdiag j)

/-- Each input-channel term is below the full co-Lip sum and the output. -/
theorem coLip_channel_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    {φ : Operator X bot} {U : Set X} {K : ChannelMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    (i j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    entry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  classical
  calc
    entry K i j * d i x y ≤ ∑ k : I, entry K k j * d k x y :=
      Finset.single_le_sum (fun k _ => zero_le (entry K k j * d k x y))
        (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

/-- CH02-P20: a positive co-Lip channel preserves positive distance. -/
theorem positive_coLip_channel {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {K : ChannelMatrix I} {i j : I}
    (hK : K ∈ restrictedCoLipMatrices d φ U) (hpos : 0 < entry K i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d i x y → 0 < d j (φ.func x) (φ.func y) := by
  intro x hx y hy hxy
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpos, hxy⟩)
    (coLip_channel_le d hK i j hx hy)

/-- CH02-P21: positive diagonal entries reflect the family zero relation. -/
theorem positive_diagonal_reflects_gauge_zero {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {K : ChannelMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    (hdiag : ∀ j : I, 0 < entry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  apply le_antisymm _ (zero_le _)
  by_contra hn
  have hin : 0 < d j x y := lt_of_not_ge hn
  have hout := positive_coLip_channel d hd hK (hdiag j) x hx y hy hin
  rw [hzero j] at hout
  exact (lt_irrefl (0 : ENNReal)) hout

/-- CH02-P25 (Exercise 2.2): only the chosen output row must be sparse. -/
theorem scalar_two_sided_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {L K : ChannelMatrix I} {j : I}
    (hL : L ∈ restrictedLipMatrices d φ U)
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    (hrow : SingleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro x hx y hy
  exact ⟨coLip_channel_le d hK j j hx hy,
    single_input_lip_bound d hd hL hrow x hx y hy⟩

end LCH01
