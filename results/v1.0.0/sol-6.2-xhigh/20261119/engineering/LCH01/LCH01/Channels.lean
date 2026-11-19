import LCH01.Bounds
import Mathlib.Data.ENNReal.Operations
import Mathlib.LinearAlgebra.Matrix.IsDiag

open scoped BigOperators

namespace LCH01

open formal_oet.vol_01.ch_01_foundations (GaugeZeroRelated Operator)

/-- An ordered pair of input and output components. -/
abbrev Channel (I : Type) := I × I

/-- In the output row of `c`, every coefficient outside its input column is zero. -/
def SingleInputRow {I : Type} (M : CoeffMatrix I) (c : Channel I) : Prop :=
  ∀ k : I, k ≠ c.1 → entry M k c.2 = 0

theorem isDiag_iff_singleInputRows {I : Type} (M : CoeffMatrix I) :
    M.IsDiag ↔ ∀ j : I, SingleInputRow M (j, j) := by
  constructor
  · intro h j k hkj
    exact h hkj.symm
  · intro h j k hjk
    exact h j k hjk.symm

theorem rowSum_singleInput {I : Type} [Fintype I] (M : CoeffMatrix I) (v : I → ENNReal)
    (c : Channel I) (h : SingleInputRow M c) :
    rowSum M v c.2 = entry M c.1 c.2 * v c.1 := by
  unfold rowSum
  refine Finset.sum_eq_single c.1 (fun k _ hk => ?_) (fun hmem => ?_)
  · rw [h k hk, zero_mul]
  · exact (hmem (Finset.mem_univ c.1)).elim

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable {G : GaugeFamily X I bot} {φ : Operator X bot} {U : Set X}
variable {L K : CoeffMatrix I} {x y : X}

theorem lip_singleInput (hL : L ∈ restrictedLipMatrices G φ U)
    (c : Channel I) (hrow : SingleInputRow L c) (hx : x ∈ U) (hy : y ∈ U) :
    G.dist c.2 (φ.func x) (φ.func y) ≤ entry L c.1 c.2 * G.dist c.1 x y := by
  have h : IsRestrictedLip G φ U L := hL
  simpa only [rowSum_singleInput L (fun i => G.dist i x y) c hrow] using
    h.2 x hx y hy c.2

theorem lip_diagonal (hL : L ∈ restrictedLipMatrices G φ U)
    (hdiag : L.IsDiag) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  lip_singleInput hL (j, j) ((isDiag_iff_singleInputRows L).mp hdiag j) hx hy

theorem coLip_entry_le (hK : K ∈ restrictedCoLipMatrices G φ U)
    (c : Channel I) (hx : x ∈ U) (hy : y ∈ U) :
    entry K c.1 c.2 * G.dist c.1 x y ≤ G.dist c.2 (φ.func x) (φ.func y) := by
  have h : IsRestrictedCoLip G φ U K := hK
  calc
    entry K c.1 c.2 * G.dist c.1 x y ≤ rowSum K (fun i => G.dist i x y) c.2 :=
      Finset.single_le_sum (f := fun i => entry K i c.2 * G.dist i x y)
        (fun _ _ => zero_le _) (Finset.mem_univ c.1)
    _ ≤ G.dist c.2 (φ.func x) (φ.func y) := h.2.2 x hx y hy c.2

theorem coLip_channel_pos (hK : K ∈ restrictedCoLipMatrices G φ U)
    (c : Channel I) (hpos : 0 < entry K c.1 c.2) (hx : x ∈ U) (hy : y ∈ U) :
    0 < G.dist c.1 x y → 0 < G.dist c.2 (φ.func x) (φ.func y) := by
  intro hdist
  exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hdist))
    (coLip_entry_le hK c hx hy)

theorem coLip_reflects_zero (hK : K ∈ restrictedCoLipMatrices G φ U)
    (hdiag : ∀ j : I, 0 < entry K j j) (hx : x ∈ U) (hy : y ∈ U) :
    GaugeZeroRelated G.dist (φ.func x) (φ.func y) → GaugeZeroRelated G.dist x y := by
  intro hzero j
  by_contra hne
  have hpos : 0 < G.dist j x y := pos_iff_ne_zero.mpr hne
  exact (ne_of_gt (coLip_channel_pos hK (j, j) (hdiag j) hx hy hpos)) (hzero j)

theorem scalar_two_sided (hL : L ∈ restrictedLipMatrices G φ U)
    (hK : K ∈ restrictedCoLipMatrices G φ U) (j : I)
    (hrow : SingleInputRow L (j, j)) (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  ⟨coLip_entry_le hK (j, j) hx hy, lip_singleInput hL (j, j) hrow hx hy⟩

end LCH01
