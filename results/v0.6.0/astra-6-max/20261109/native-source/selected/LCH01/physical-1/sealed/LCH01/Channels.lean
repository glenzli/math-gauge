import LCH01.Definitions

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X} [Fintype I]

/-- CH02-P19: a row supported at one input has exactly one possible summand. -/
theorem singleInputRow_sum (M : ChannelMatrix I) (i j : I)
    (hrow : SingleInputRow M i j) (v : I → ENNReal) :
    rowSum M j v = entry M i j * v i := by
  classical
  unfold rowSum
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Each nonnegative input term is bounded by the full row sum. -/
theorem entry_mul_le_rowSum (M : ChannelMatrix I) (i j : I)
    (v : I → ENNReal) :
    entry M i j * v i ≤ rowSum M j v := by
  classical
  exact Finset.single_le_sum (fun k _ => zero_le (entry M k j * v k))
    (Finset.mem_univ i)

section Gauge

variable {d : I → X → X → ENNReal}

-- The explicit premises retain the source's nonempty gauge-space context.

/-- CH02-P19: the Lip bound when output row `j` only uses input `i`. -/
theorem single_input_lip_bound [Nonempty I]
    (_hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : L ∈ restrictedLipMatrices d φ U)
    {i j : I} (hrow : SingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ entry L i j * d i x y := by
  have h := hL.2 x hx y hy j
  rw [singleInputRow_sum L i j hrow] at h
  exact h

/-- CH02-P19: the same reduction for every diagonal channel. -/
theorem diagonal_lip_bound [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : L ∈ restrictedLipMatrices d φ U)
    (hdiag : IsDiagonal L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  exact single_input_lip_bound hGauge hL
    ((isDiagonal_iff_singleInputRows L).mp hdiag j) hx hy

/-- Any individual co-Lip channel gives a lower bound. -/
theorem colip_channel_lower_bound [Nonempty I]
    (_hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : K ∈ restrictedCoLipMatrices d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    entry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  exact (entry_mul_le_rowSum K i j (fun k => d k x y)).trans
    (hK.2.2 x hx y hy j)

/-- CH02-P20, Proposition 2.8(i): positive channels preserve positive distance. -/
theorem positive_colip_channel [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : K ∈ restrictedCoLipMatrices d φ U)
    {i j : I} (hpos : 0 < entry K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hxy : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  exact lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hxy.ne')
    (colip_channel_lower_bound hGauge hK hx hy i j)

/-- CH02-P21, Proposition 2.8(ii): reflection of family zero distance only. -/
theorem positive_diagonal_reflects_zero [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : K ∈ restrictedCoLipMatrices d φ U)
    (hdiag : ∀ j : I, 0 < entry K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout := positive_colip_channel hGauge hK (hdiag j) hx hy hpos
  rw [hzero j] at hout
  exact (lt_irrefl 0) hout

/-- CH02-P25, Exercise 2.2: the scalar two-sided bound on output `j`. -/
theorem scalar_two_sided_bound [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L K : ChannelMatrix I}
    (hL : L ∈ restrictedLipMatrices d φ U)
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    {j : I} (hrow : SingleInputRow L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  exact ⟨colip_channel_lower_bound hGauge hK hx hy j j,
    single_input_lip_bound hGauge hL hrow hx hy⟩

end Gauge

end LCH01
