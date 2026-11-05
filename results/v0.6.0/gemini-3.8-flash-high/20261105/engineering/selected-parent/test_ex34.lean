
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

-- Diameters:
-- For Da: diam = 1/2
lemma diam_Da : diam d_real_bot ex34_Da = ENNReal.ofReal (1 / 2) := by
  dsimp [diam]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro ⟨rx, hrx0, hrx1, hx⟩
    apply iSup_le; intro y
    apply iSup_le; intro ⟨ry, hry0, hry1, hy⟩
    subst hx hy
    dsimp [d_real_bot]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    have : abs (rx - ry) ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    exact this
  · refine le_iSup_of_le (some 0) ?_
    refine le_iSup_of_le ⟨0, by norm_num, by norm_num, rfl⟩ ?_
    refine le_iSup_of_le (some (1 / 2)) ?_
    refine le_iSup_of_le ⟨1 / 2, by norm_num, by norm_num, rfl⟩ ?_
    dsimp [d_real_bot]
    norm_num

-- For Db: diam = 1/5
lemma diam_Db : diam d_real_bot ex34_Db = ENNReal.ofReal (1 / 5) := by
  dsimp [diam]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro ⟨rx, hrx0, hrx1, hx⟩
    apply iSup_le; intro y
    apply iSup_le; intro ⟨ry, hry0, hry1, hy⟩
    subst hx hy
    dsimp [d_real_bot]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    have : abs (rx - ry) ≤ 1 / 5 := by
      rw [abs_le]
      constructor <;> linarith
    exact this
  · refine le_iSup_of_le (some (9 / 10)) ?_
    refine le_iSup_of_le ⟨9 / 10, by norm_num, by norm_num, rfl⟩ ?_
    refine le_iSup_of_le (some (11 / 10)) ?_
    refine le_iSup_of_le ⟨11 / 10, by norm_num, by norm_num, rfl⟩ ?_
    dsimp [d_real_bot]
    have : abs (9 / 10 - 11 / 10 : ℝ) = 1 / 5 := by norm_num
    rw [this]

-- For Dc: diam = 2
lemma diam_Dc : diam d_real_bot ex34_Dc = ENNReal.ofReal 2 := by
  dsimp [diam, ex34_Dc]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> {
      dsimp [d_real_bot]; norm_num
    }
  · refine le_iSup_of_le (some 0) ?_
    refine le_iSup_of_le (Or.inl rfl) ?_
    refine le_iSup_of_le (some 2) ?_
    refine le_iSup_of_le (Or.inr rfl) ?_
    dsimp [d_real_bot]; norm_num

-- For Dd: diam = 2
lemma diam_Dd : diam d_real_bot ex34_Dd = ENNReal.ofReal 2 := by
  dsimp [diam]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro ⟨rx, hrx0, hrx1, hx⟩
    apply iSup_le; intro y
    apply iSup_le; intro ⟨ry, hry0, hry1, hy⟩
    subst hx hy
    dsimp [d_real_bot]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    have : abs (rx - ry) ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    exact this
  · refine le_iSup_of_le (some 0) ?_
    refine le_iSup_of_le ⟨0, by norm_num, by norm_num, rfl⟩ ?_
    refine le_iSup_of_le (some 2) ?_
    refine le_iSup_of_le ⟨2, by norm_num, by norm_num, rfl⟩ ?_
    dsimp [d_real_bot]; norm_num

end OperatorLocalDegeneracy
