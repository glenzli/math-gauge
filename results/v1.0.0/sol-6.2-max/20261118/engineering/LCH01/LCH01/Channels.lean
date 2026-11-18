import LCH01.MatrixBounds
import Mathlib.Data.ENNReal.Operations
import Mathlib.LinearAlgebra.Matrix.IsDiag

open scoped BigOperators ENNReal
open formal_oet.vol_01.ch_01_foundations

namespace LCH01

/-- An ordered pair of input and output components, in that order. -/
abbrev Channel (I : Type) := I × I

/-- In the output row of `c`, every coefficient away from its input is zero. -/
def HasOnlyInput {I : Type} (M : BoundMatrix I) (c : Channel I) : Prop :=
  ∀ k : I, k ≠ c.1 → M.coeff k c.2 = 0

theorem zero_channel_term {I : Type} (M : BoundMatrix I) (c : Channel I)
    (v : I → ℝ≥0∞) (h : M.coeff c.1 c.2 = 0) :
    M.coeff c.1 c.2 * v c.1 = 0 := by
  rw [h, zero_mul]

theorem isDiag_iff_onlyInput {I : Type} (M : BoundMatrix I) :
    Matrix.IsDiag M ↔ ∀ j : I, HasOnlyInput M (j, j) := by
  constructor
  · intro h j k hkj
    exact h (Ne.symm hkj)
  · intro h j k hjk
    exact h j k (Ne.symm hjk)

theorem rowSum_eq_of_onlyInput {I : Type} [Fintype I] (M : BoundMatrix I)
    (c : Channel I) (v : I → ℝ≥0∞) (hrow : HasOnlyInput M c) :
    M.rowSum c.2 v = M.coeff c.1 c.2 * v c.1 := by
  unfold BoundMatrix.rowSum
  apply Finset.sum_eq_single c.1
  · intro k _ hk
    exact zero_channel_term M (k, c.2) v (hrow k hk)
  · simp

theorem rowSum_eq_of_diagonal {I : Type} [Fintype I] (M : BoundMatrix I)
    (hdiag : Matrix.IsDiag M) (j : I) (v : I → ℝ≥0∞) :
    M.rowSum j v = M.coeff j j * v j :=
  rowSum_eq_of_onlyInput M (j, j) v ((isDiag_iff_onlyInput M).mp hdiag j)

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable {G : Gauge X I bot} {φ : Operator X bot} {U : Set X}
variable {L K : BoundMatrix I}

theorem lip_of_onlyInput (hL : L ∈ restrictedLipMatrices G φ U)
    (i j : I) (hrow : HasOnlyInput L (i, j)) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ L.coeff i j * G.dist i x y := by
  calc
    _ ≤ L.rowSum j (fun k => G.dist k x y) := hL.2 x hx y hy j
    _ = _ := rowSum_eq_of_onlyInput L (i, j) (fun k => G.dist k x y) hrow

theorem lip_of_diagonal (hL : L ∈ restrictedLipMatrices G φ U) (hdiag : Matrix.IsDiag L)
    (j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ L.coeff j j * G.dist j x y := by
  calc
    _ ≤ L.rowSum j (fun k => G.dist k x y) := hL.2 x hx y hy j
    _ = _ := rowSum_eq_of_diagonal L hdiag j (fun k => G.dist k x y)

theorem positive_coLip_channel (hK : K ∈ restrictedCoLipMatrices G φ U)
    (i j : I) (hpos : 0 < K.coeff i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    0 < G.dist i x y → 0 < G.dist j (φ.func x) (φ.func y) := by
  intro hdist
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpos, hdist⟩) (coLip_term_le hK i j hx hy)

theorem reflect_gauge_zero_of_positive_diagonal (hK : K ∈ restrictedCoLipMatrices G φ U)
    (hdiag : ∀ j : I, 0 < K.coeff j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    GaugeZeroRelated G.dist (φ.func x) (φ.func y) → GaugeZeroRelated G.dist x y := by
  intro hzero j
  by_contra hne
  have hpos := positive_coLip_channel hK j j (hdiag j) hx hy (pos_iff_ne_zero.mpr hne)
  exact (ne_of_gt hpos) (hzero j)

theorem diagonal_scalar_bounds (hL : L ∈ restrictedLipMatrices G φ U)
    (hK : K ∈ restrictedCoLipMatrices G φ U) (j : I) (hrow : HasOnlyInput L (j, j))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K.coeff j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
      G.dist j (φ.func x) (φ.func y) ≤ L.coeff j j * G.dist j x y :=
  ⟨coLip_term_le hK j j hx hy, lip_of_onlyInput hL j j hrow hx hy⟩

end LCH01
