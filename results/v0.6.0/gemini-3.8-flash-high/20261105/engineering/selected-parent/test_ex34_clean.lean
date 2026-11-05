
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

def ex34_Da : Set (Option ℝ) := { x | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 ∧ x = some r }
def ex34_Db : Set (Option ℝ) := { x | ∃ r : ℝ, 9 / 10 ≤ r ∧ r ≤ 11 / 10 ∧ x = some r }
def ex34_Dc : Set (Option ℝ) := { some 0, some 2 }
def ex34_Dd : Set (Option ℝ) := { x | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 2 ∧ x = some r }

lemma floor_op_Da (x : Option ℝ) (hx : x ∈ ex34_Da) : floor_op.func x = some 0 := by
  rcases hx with ⟨r, hr0, hr1, rfl⟩
  dsimp [floor_op, floor_func]
  have : r < 1 := by linarith
  rw [if_pos this]

lemma r_null_unif_Da : r_null_uniform d_real_bot d_real_bot floor_op ex34_Da = ⊤ := by
  dsimp [r_null_uniform]
  apply le_antisymm le_top
  apply le_iInf; intro y
  apply le_iInf; intro hy
  dsimp [r_null]
  rw [top_le_iff, sSup_eq_top]
  intro b hb
  -- find n : ℕ such that b < n
  rcases ENNReal.exists_nat_gt (ne_top_of_lt hb) with ⟨n, hn⟩
  refine ⟨n + 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · norm_num
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top n, ENNReal.one_lt_top⟩
  · intro x hx _
    rw [floor_op_Da x hx, floor_op_Da y hy]
    dsimp [d_real_bot]; norm_num
  · exact lt_of_lt_of_le hn (by simp)

lemma r_null_unif_Dc : r_null_uniform d_real_bot d_real_bot floor_op ex34_Dc = 2 := by
  dsimp [r_null_uniform]
  apply le_antisymm
  · have h0_in : some 0 ∈ ex34_Dc := Or.inl rfl
    refine le_trans (biInf_le (fun y => r_null d_real_bot d_real_bot floor_op y ex34_Dc) h0_in) ?_
    dsimp [r_null]
    apply sSup_le; intro r hr
    rcases hr with ⟨hr0, hrt, hball⟩
    by_contra! hgt
    have hdist : d_real_bot (some 2) (some 0) < r := by
      dsimp [d_real_bot]
      have : ENNReal.ofReal (abs (2 - 0 : ℝ)) = 2 := by norm_num
      rw [this]; exact hgt
    have hzero := hball (some 2) (Or.inr rfl) hdist
    dsimp [floor_op, floor_func, d_real_bot] at hzero
    norm_num at hzero
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    dsimp [r_null]
    refine le_trans ?_ (le_sSup (a := 2) ?_)
    · exact le_rfl
    · refine ⟨by norm_num, by norm_num, ?_⟩
      intro x hx hdist
      simp only [ex34_Dc, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · cases floor_op.func (some 0) <;> simp [d_real_bot]
      · dsimp [d_real_bot] at hdist
        have : ENNReal.ofReal (abs (0 - 2 : ℝ)) = 2 := by norm_num
        rw [this] at hdist
        exact False.elim (lt_irrefl 2 hdist)
      · dsimp [d_real_bot] at hdist
        have : ENNReal.ofReal (abs (2 - 0 : ℝ)) = 2 := by norm_num
        rw [this] at hdist
        exact False.elim (lt_irrefl 2 hdist)
      · cases floor_op.func (some 2) <;> simp [d_real_bot]

end OperatorLocalDegeneracy
