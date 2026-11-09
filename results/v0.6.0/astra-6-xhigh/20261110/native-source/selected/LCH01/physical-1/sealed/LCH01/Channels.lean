import LCH01.MatrixBounds

/-!
Selected channel results from Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, Volume I, Chapter 2.
Source: https://glenzli.com/books/oet/ ; CC BY 4.0.
The proofs below are a new Lean formalization of the supplied source.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-- The complete row sum equals its sole potentially nonzero input term. -/
theorem row_sum_eq {I : Type} [Fintype I]
    {M : ChannelMatrix I} {i j : I}
    (hrow : RowSupported M i j) (v : I → ENNReal) :
    (∑ k, entry M k j * v k) = entry M i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

section Channels

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable {G : Gauge X I bot} {φ : Operator X bot} {U : Set X}

/-- CH02-P19: row sparsity yields a scalar channel Lip bound. -/
theorem lip_single_input {L : ChannelMatrix I} {i j : I}
    (hL : LipOn G φ U L) (hrow : RowSupported L i j) :
    ChannelLipOn G φ U i j (entry L i j) := by
  refine ⟨hL.1, ?_⟩
  intro x hx y hy
  calc
    G.d j (φ.func x) (φ.func y) ≤
        ∑ k, entry L k j * G.d k x y := hL.2 x hx y hy j
    _ = entry L i j * G.d i x y := row_sum_eq hrow (fun k => G.d k x y)

/-- CH02-P19: the specialization for every diagonal channel. -/
theorem lip_diagonal {L : ChannelMatrix I}
    (hL : LipOn G φ U L) (hdiag : IsDiagonal L) :
    ∀ j, ChannelLipOn G φ U j j (entry L j j) := by
  intro j
  exact lip_single_input hL (hdiag j)

/-- Each nonnegative input term is bounded by the co-Lip row sum. -/
theorem coLip_term_le {K : ChannelMatrix I}
    (hK : CoLipOn G φ U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (i j : I) :
    entry K i j * G.d i x y ≤ G.d j (φ.func x) (φ.func y) := by
  calc
    entry K i j * G.d i x y ≤ ∑ k, entry K k j * G.d k x y :=
      Finset.single_le_sum (f := fun k => entry K k j * G.d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ G.d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

/-- CH02-P20: a positive co-Lip channel preserves positive distance. -/
theorem positive_coLip_channel {K : ChannelMatrix I} {i j : I}
    (hK : CoLipOn G φ U K) (hchannel : 0 < entry K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hxy : 0 < G.d i x y) :
    0 < G.d j (φ.func x) (φ.func y) := by
  have hprod : 0 < entry K i j * G.d i x y :=
    ENNReal.mul_pos (ne_of_gt hchannel) (ne_of_gt hxy)
  exact lt_of_lt_of_le hprod (coLip_term_le hK hx hy i j)

/-- CH02-P21: reflect family zero distance, without any separation assumption. -/
theorem coLip_reflects_gaugeZero {K : ChannelMatrix I}
    (hK : CoLipOn G φ U K) (hdiag : ∀ j, 0 < entry K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated G.d (φ.func x) (φ.func y)) :
    GaugeZeroRelated G.d x y := by
  intro j
  apply le_antisymm _ (zero_le _)
  by_contra h
  have hpos := positive_coLip_channel hK (hdiag j) hx hy (lt_of_not_ge h)
  rw [hzero j] at hpos
  exact (lt_irrefl 0) hpos

/-- CH02-P25 (Exercise 2.2): both scalar bounds, for any selected output row. -/
theorem scalar_two_sided {L K : ChannelMatrix I} {j : I}
    (hL : LipOn G φ U L) (hK : CoLipOn G φ U K)
    (hrow : RowSupported L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.d j x y ≤ G.d j (φ.func x) (φ.func y) ∧
      G.d j (φ.func x) (φ.func y) ≤ entry L j j * G.d j x y := by
  exact ⟨coLip_term_le hK hx hy j j,
    (lip_single_input hL hrow).2 x hx y hy⟩

end Channels

end LCH01
