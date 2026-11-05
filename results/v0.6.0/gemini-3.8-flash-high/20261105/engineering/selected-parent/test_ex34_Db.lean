
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ThresholdClassification
import OperatorLocalDegeneracy.NullificationRadius

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

noncomputable def floor_func (r : ℝ) : ℝ :=
  if r < 1 then 0 else if r < 2 then 1 else 2

noncomputable def floor_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (floor_func r)
  preserves_bot := rfl

def ex34_Db : Set (Option ℝ) := { x | ∃ r : ℝ, 9 / 10 ≤ r ∧ r ≤ 11 / 10 ∧ x = some r }
def ex34_Dd : Set (Option ℝ) := { x | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 2 ∧ x = some r }

lemma r_null_unif_Db : r_null_uniform d_real_bot d_real_bot floor_op ex34_Db = 0 := by
  dsimp [r_null_uniform]
  have h1_in : some 1 ∈ ex34_Db := ⟨1, by norm_num, by norm_num, rfl⟩
  refine le_antisymm ?_ (zero_le _)
  refine le_trans (biInf_le (fun y => r_null d_real_bot d_real_bot floor_op y ex34_Db) h1_in) ?_
  dsimp [r_null]
  apply sSup_le; intro r hr
  rcases hr with ⟨hr0, hrt, hball⟩
  by_contra!
  by_cases h_large : ENNReal.ofReal (1 / 10) < r
  · have hx : some (9 / 10 : ℝ) ∈ ex34_Db := ⟨9 / 10, by norm_num, by norm_num, rfl⟩
    have hdist : d_real_bot (some (9 / 10 : ℝ)) (some 1) < r := by
      dsimp [d_real_bot]
      have : ENNReal.ofReal (abs (9 / 10 - 1 : ℝ)) = ENNReal.ofReal (1 / 10) := by norm_num
      rw [this]; exact h_large
    have hzero := hball (some (9 / 10 : ℝ)) hx hdist
    dsimp [floor_op, floor_func, d_real_bot] at hzero
    norm_num at hzero
  · have h_le : r ≤ ENNReal.ofReal (1 / 10) := le_of_not_gt h_large
    have hr_pos_real : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hrt.ne
    set delta := r.toReal / 2
    have hdelta_pos : 0 < delta := half_pos hr_pos_real
    have hdelta_lt : delta < r.toReal := half_lt_self hr_pos_real
    have h_r_real_le : r.toReal ≤ 1 / 10 := by
      rw [← ENNReal.ofReal_toReal hrt.ne] at h_le
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h_le
    have hdelta_le : delta ≤ 1 / 20 := by dsimp [delta]; linarith [h_r_real_le]
    set x_real := 1 - delta
    have hx_in : some x_real ∈ ex34_Db := by
      refine ⟨x_real, ?_, ?_, rfl⟩
      · dsimp [x_real]; linarith [hdelta_le]
      · dsimp [x_real]; linarith [hdelta_pos]
    have hdist : d_real_bot (some x_real) (some 1) < r := by
      dsimp [d_real_bot]
      have : abs (x_real - 1) = delta := by
        dsimp [x_real]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos hdelta_pos]
      rw [this]
      have : ENNReal.ofReal delta < r := by
        rw [← ENNReal.ofReal_toReal hrt.ne]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hdelta_pos)).mpr hdelta_lt
      exact this
    have hzero := hball (some x_real) hx_in hdist
    dsimp [floor_op, floor_func, d_real_bot] at hzero
    have h_x_lt1 : x_real < 1 := by dsimp [x_real]; linarith [hdelta_pos]
    have h1_ge1 : ¬ ((1 : ℝ) < 1) := by norm_num
    have h1_lt2 : (1 : ℝ) < 2 := by norm_num
    rw [if_pos h_x_lt1, if_neg h1_ge1, if_pos h1_lt2] at hzero
    norm_num at hzero

lemma ex34_Db_sub_Dd : ex34_Db ⊆ ex34_Dd := by
  rintro x ⟨r, hr0, hr1, rfl⟩
  exact ⟨r, by linarith, by linarith, rfl⟩

lemma r_null_unif_Dd : r_null_uniform d_real_bot d_real_bot floor_op ex34_Dd = 0 := by
  have hmono := prop_3_14_ii_b d_real_bot d_real_bot floor_op ex34_Db_sub_Dd
  rw [r_null_unif_Db] at hmono
  exact nonpos_iff_eq_zero.mp hmono

end OperatorLocalDegeneracy
