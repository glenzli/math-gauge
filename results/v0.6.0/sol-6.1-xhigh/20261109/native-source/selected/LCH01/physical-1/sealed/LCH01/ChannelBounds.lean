import LCH01.MatrixChannels

/-!
Formalization of the selected channel results in Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, Volume I, §2.2 and Exercise 2.2.
See MatrixChannels.lean for source attribution and the CC BY 4.0 license.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} [Fintype I] {bot : X}

/-- The sum in a row with a single possible input reduces to that term. -/
theorem single_input_row_sum (M : ChannelMatrix I) (v : I → ENNReal)
    (i j : I) (hrow : SingleInputRow M i j) :
    (∑ k : I, entry M k j * v k) = entry M i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [hrow k hk, zero_mul]
  · simp

/-- Each nonnegative summand is bounded by the co-Lip output distance. -/
theorem colip_entry_le {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : ChannelMatrix I} (hK : IsRestrictedCoLip d φ U K)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    entry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  calc
    entry K i j * d i x y ≤ ∑ k : I, entry K k j * d k x y :=
      Finset.single_le_sum (f := fun k : I => entry K k j * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

section GaugeSpace

variable (d : I → X → X → ENNReal)

/-- CH02-P19: a sparse output row gives a scalar upper bound. -/
theorem lip_single_input [Nonempty I]
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : IsRestrictedLip d φ U L)
    {i j : I} (hrow : SingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L i j * d i x y := by
  intro x hx y hy
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, entry L k j * d k x y :=
      hL.2 x hx y hy j
    _ = entry L i j * d i x y :=
      single_input_row_sum L (fun k => d k x y) i j hrow

/-- CH02-P19, diagonal special case, simultaneously for every output. -/
theorem lip_diagonal [Nonempty I]
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : IsRestrictedLip d φ U L)
    (hdiag : Diagonal L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro j
  exact lip_single_input d hd hL (diagonal_singleInputRow hdiag j)

/-- CH02-P20: a positive co-Lip channel preserves positive distance. -/
theorem positive_colip_channel [Nonempty I]
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : IsRestrictedCoLip d φ U K)
    {i j : I} (hpos : 0 < entry K i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d i x y → 0 < d j (φ.func x) (φ.func y) := by
  intro x hx y hy hxy
  exact lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hxy.ne')
    (colip_entry_le hK hx hy i j)

/-- CH02-P21: positive diagonal entries reflect the family zero relation. -/
theorem colip_reflects_gauge_zero [Nonempty I]
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : IsRestrictedCoLip d φ U K)
    (hdiag : ∀ j : I, 0 < entry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout := positive_colip_channel d hd hK (hdiag j) x hx y hy hpos
  rw [hzero j] at hout
  exact (lt_irrefl (0 : ENNReal)) hout

/-- CH02-P25 (Exercise 2.2): the diagonal scalar two-sided bound. -/
theorem scalar_two_sided [Nonempty I]
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L K : ChannelMatrix I}
    (hL : IsRestrictedLip d φ U L) (hK : IsRestrictedCoLip d φ U K)
    (j : I) (hrow : SingleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro x hx y hy
  exact ⟨colip_entry_le hK hx hy j j,
    lip_single_input d hd hL hrow x hx y hy⟩

end GaugeSpace

end LCH01
