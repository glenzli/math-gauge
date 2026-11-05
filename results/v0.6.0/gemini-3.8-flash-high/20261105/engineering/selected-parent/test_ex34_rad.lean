
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ThresholdClassification
import OperatorLocalDegeneracy.NullificationRadius

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

noncomputable def floor_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some ↑⌊r⌋
  preserves_bot := rfl

def ex34_Da : Set (Option ℝ) := { x | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 ∧ x = some r }
def ex34_Db : Set (Option ℝ) := { x | ∃ r : ℝ, 9 / 10 ≤ r ∧ r ≤ 11 / 10 ∧ x = some r }
def ex34_Dc : Set (Option ℝ) := { some 0, some 2 }
def ex34_Dd : Set (Option ℝ) := { x | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 2 ∧ x = some r }

lemma floor_op_Da (x : Option ℝ) (hx : x ∈ ex34_Da) : floor_op.func x = some 0 := by
  rcases hx with ⟨r, hr0, hr1, rfl⟩
  dsimp [floor_op]
  congr 1
  have : ⌊r⌋ = 0 := by
    rw [Int.floor_eq_iff]
    constructor
    · linarith
    · norm_num; linarith
  norm_cast

lemma r_null_unif_Da : r_null_uniform d_real_bot d_real_bot floor_op ex34_Da = ⊤ := by
  dsimp [r_null_uniform]
  apply le_antisymm le_top
  apply le_biInf; intro y hy
  dsimp [r_null]
  refine le_trans le_top (le_sSup ?_)
  intro x hx _
  rw [floor_op_Da x hx, floor_op_Da y hy]
  dsimp [d_real_bot]; norm_num

lemma r_null_unif_Db : r_null_uniform d_real_bot d_real_bot floor_op ex34_Db = 0 := by
  dsimp [r_null_uniform]
  have h1_in : some 1 ∈ ex34_Db := ⟨1, by norm_num, by norm_num, rfl⟩
  refine le_trans (biInf_le (f := fun y => r_null d_real_bot d_real_bot floor_op y ex34_Db) (some 1) h1_in) ?_
  dsimp [r_null]
  apply sSup_le; intro r hr
  by_contra! hr_pos
  -- hr says for all x in Db with d(x, 1) < r, floor_op x = floor_op 1
  have h_ne : ∃ x ∈ ex34_Db, d_real_bot x (some 1) < r ∧ d_real_bot (floor_op.func x) (floor_op.func (some 1)) ≠ 0 := by
    -- pick delta = min (1/20) (r / 2)
    set delta : ENNReal := min (ENNReal.ofReal (1 / 20)) (r / 2)
    have hd_pos : 0 < delta := lt_min (by rw [ENNReal.ofReal_pos]; norm_num) (ENNReal.half_pos hr_pos.ne')
    have hd_top : delta < ⊤ := lt_of_le_of_lt (min_le_left _ _) (by rw [ENNReal.ofReal_lt_top])
    lift delta to NNReal using hd_top.ne
    have hd_pos_real : 0 < (delta : ℝ) := by rwa [ENNReal.coe_pos] at hd_pos
    set x_real : ℝ := 1 - (delta : ℝ)
    have hx_in : some x_real ∈ ex34_Db := by
      refine ⟨x_real, ?_, ?_, rfl⟩
      · have : (delta : ℝ) ≤ 1 / 20 := by
          have h_le := min_le_left (ENNReal.ofReal (1 / 20)) (r / 2)
          exact (ENNReal.ofReal_le_iff_le_toReal (by norm_num)).mp (by exact h_le)
        linarith
      · linarith
    refine ⟨some x_real, hx_in, ?_, ?_⟩
    · dsimp [d_real_bot]
      have : abs (x_real - 1) = (delta : ℝ) := by
        dsimp [x_real]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos hd_pos_real]
      rw [this]
      have : (delta : ENNReal) < r := by
        refine lt_of_le_of_lt (min_le_right _ _) ?_
        exact ENNReal.half_lt_self hr_pos.ne' (by intro h; rw [h] at hr_pos; contradiction)
      exact this
    · dsimp [floor_op, d_real_bot]
      have hfl1 : ⌊(1 : ℝ)⌋ = 1 := by norm_num
      have hflx : ⌊x_real⌋ = 0 := by
        rw [Int.floor_eq_iff]
        constructor
        · have : (delta : ℝ) ≤ 1 / 20 := by
            have h_le := min_le_left (ENNReal.ofReal (1 / 20)) (r / 2)
            exact (ENNReal.ofReal_le_iff_le_toReal (by norm_num)).mp (by exact h_le)
          linarith
        · norm_num; linarith
      rw [hfl1, hflx]
      have : abs ((0 : ℝ) - (1 : ℝ)) = 1 := by norm_num
      rw [this]
      exact ENNReal.ofReal_ne_zero.mpr (by norm_num)
  rcases h_ne with ⟨x, hx, hdist, hne⟩
  exact hne (hr x hx hdist)

end OperatorLocalDegeneracy
