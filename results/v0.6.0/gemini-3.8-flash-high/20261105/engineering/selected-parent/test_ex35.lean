
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.CoveringEntropy

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

def ex35_U : Set (Option ℝ) := { some 0, some 1, some 2, some 3 }

lemma mem_ex35_U (x : Option ℝ) : x ∈ ex35_U ↔ x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 := by
  dsimp [ex35_U]; simp

noncomputable def ex35_f : Operator (Option ℝ) none where
  func := fun x => match x with
    | some r => if r = 0 then some 0 else if r = 1 then some 1 else if r = 2 then some 2 else if r = 3 then some 3 else none
    | none => none
  preserves_bot := rfl

noncomputable def ex35_g : Operator (Option ℝ) none where
  func := fun x => match x with
    | some r => if r = 0 then some 0 else if r = 1 then some 3 else if r = 2 then some 1 else if r = 3 then some 2 else none
    | none => none
  preserves_bot := rfl

lemma ex35_f_0 : ex35_f.func (some 0) = some 0 := by dsimp [ex35_f]; norm_num
lemma ex35_f_1 : ex35_f.func (some 1) = some 1 := by dsimp [ex35_f]; norm_num
lemma ex35_f_2 : ex35_f.func (some 2) = some 2 := by dsimp [ex35_f]; norm_num
lemma ex35_f_3 : ex35_f.func (some 3) = some 3 := by dsimp [ex35_f]; norm_num

lemma ex35_g_0 : ex35_g.func (some 0) = some 0 := by dsimp [ex35_g]; norm_num
lemma ex35_g_1 : ex35_g.func (some 1) = some 3 := by dsimp [ex35_g]; norm_num
lemma ex35_g_2 : ex35_g.func (some 2) = some 1 := by dsimp [ex35_g]; norm_num
lemma ex35_g_3 : ex35_g.func (some 3) = some 2 := by dsimp [ex35_g]; norm_num

theorem ex35_f_image : ex35_f.func '' ex35_U = ex35_U := by
  ext x
  simp only [Set.mem_image, mem_ex35_U]
  constructor
  · rintro ⟨y, rfl | rfl | rfl | rfl, rfl⟩
    · rw [ex35_f_0]; exact Or.inl rfl
    · rw [ex35_f_1]; exact Or.inr (Or.inl rfl)
    · rw [ex35_f_2]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [ex35_f_3]; exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨some 0, Or.inl rfl, ex35_f_0⟩
    · exact ⟨some 1, Or.inr (Or.inl rfl), ex35_f_1⟩
    · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), ex35_f_2⟩
    · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), ex35_f_3⟩

theorem ex35_g_image : ex35_g.func '' ex35_U = ex35_U := by
  ext x
  simp only [Set.mem_image, mem_ex35_U]
  constructor
  · rintro ⟨y, rfl | rfl | rfl | rfl, rfl⟩
    · rw [ex35_g_0]; exact Or.inl rfl
    · rw [ex35_g_1]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [ex35_g_2]; exact Or.inr (Or.inl rfl)
    · rw [ex35_g_3]; exact Or.inr (Or.inr (Or.inl rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨some 0, Or.inl rfl, ex35_g_0⟩
    · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), ex35_g_2⟩
    · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), ex35_g_3⟩
    · exact ⟨some 1, Or.inr (Or.inl rfl), ex35_g_1⟩

theorem ex35_f_lip (x y : Option ℝ) (hx : x ∈ ex35_U) (hy : y ∈ ex35_U) :
    d_real_bot (ex35_f.func x) (ex35_f.func y) ≤ 1 * d_real_bot x y := by
  rw [one_mul]
  rw [mem_ex35_U] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> {
    try rw [ex35_f_0]
    try rw [ex35_f_1]
    try rw [ex35_f_2]
    try rw [ex35_f_3]
    exact le_rfl
  }

theorem ex35_g_lip (x y : Option ℝ) (hx : x ∈ ex35_U) (hy : y ∈ ex35_U) :
    d_real_bot (ex35_g.func x) (ex35_g.func y) ≤ 3 * d_real_bot x y := by
  rw [mem_ex35_U] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> {
    try rw [ex35_g_0]
    try rw [ex35_g_1]
    try rw [ex35_g_2]
    try rw [ex35_g_3]
    dsimp [d_real_bot]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    norm_num
  }

theorem ex35_g_lip_lower (L : ENNReal)
    (hL : ∀ x ∈ ex35_U, ∀ y ∈ ex35_U, d_real_bot (ex35_g.func x) (ex35_g.func y) ≤ L * d_real_bot x y) :
    3 ≤ L := by
  have h := hL (some 0) (by simp [mem_ex35_U]) (some 1) (by simp [mem_ex35_U])
  rw [ex35_g_0, ex35_g_1] at h
  dsimp [d_real_bot] at h
  have hdg : ENNReal.ofReal (abs (0 - 3 : ℝ)) = 3 := by norm_num
  have hdin : ENNReal.ofReal (abs (0 - 1 : ℝ)) = 1 := by norm_num
  rw [hdg, hdin, mul_one] at h
  exact h

theorem ex35_center_3_2_not_in_U : some (3 / 2 : ℝ) ∉ ex35_U := by
  intro h
  rw [mem_ex35_U] at h
  rcases h with h | h | h | h <;> {
    injection h with h_eq
    norm_num at h_eq
  }

end OperatorLocalDegeneracy
