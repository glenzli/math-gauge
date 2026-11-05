
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

noncomputable def d_abs (x y : Option ℝ) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => ENNReal.ofReal (abs (abs a - abs b))
  | _, _ => ⊤

theorem d_abs_extended : ExtendedPseudoMetric (Option ℝ) none d_abs := by
  refine {
    nonabsorbing := ⟨some 0, by simp⟩
    dist_self := by
      intro x; cases x <;> simp [d_abs]
    symm := by
      intro x y; cases x <;> cases y <;> simp [d_abs]
      rw [abs_sub_comm]
    triangle := by
      intro x y z
      cases x <;> cases y <;> cases z <;> simp [d_abs]
      rename_i a b c
      have h : abs (abs a - abs c) ≤ abs (abs a - abs b) + abs (abs b - abs c) := by
        have := abs_sub_le (abs a) (abs b) (abs c)
        linarith
      refine le_trans (ENNReal.ofReal_le_ofReal h) ?_
      exact ENNReal.ofReal_add_le
    isolate_bot := by
      intro x hx; cases x
      · exact False.elim (hx rfl)
      · rfl
  }

noncomputable def affine_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (2 * r - 1)
  preserves_bot := rfl

def ex31_U : Set (Option ℝ) := { some 0, some 1 }

lemma mem_ex31_U (x : Option ℝ) : x ∈ ex31_U ↔ x = some 0 ∨ x = some 1 := by
  dsimp [ex31_U]; simp

noncomputable def d_abs_gauge : Unit → Option ℝ → Option ℝ → ENNReal := fun () => d_abs

lemma affine_op_eval_zero : affine_op.func (some 0) = some (-1) := by
  dsimp [affine_op]; congr 1; norm_num

lemma affine_op_eval_one : affine_op.func (some 1) = some 1 := by
  dsimp [affine_op]; congr 1; norm_num

lemma affine_sq_eval_zero : (affine_op * affine_op).func (some 0) = some (-3) := by
  change affine_op.func (affine_op.func (some 0)) = some (-3)
  rw [affine_op_eval_zero]
  dsimp [affine_op]; congr 1; norm_num

lemma affine_sq_eval_one : (affine_op * affine_op).func (some 1) = some 1 := by
  change affine_op.func (affine_op.func (some 1)) = some 1
  rw [affine_op_eval_one, affine_op_eval_one]

theorem ex_3_1_i_a_fiber :
    Fib_single d_abs_gauge affine_op () (affine_op.func (some 0)) ex31_U = ex31_U := by
  ext x
  simp only [Fib_single, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_⟩
    rw [mem_ex31_U] at hx
    dsimp [d_abs_gauge]
    rw [affine_op_eval_zero]
    rcases hx with rfl | rfl
    · rw [affine_op_eval_zero]
      dsimp [d_abs]
      have : abs (abs (-1 : ℝ) - abs (-1 : ℝ)) = 0 := by norm_num
      rw [this]; exact ENNReal.ofReal_zero
    · rw [affine_op_eval_one]
      dsimp [d_abs]
      have : abs (abs (1 : ℝ) - abs (-1 : ℝ)) = 0 := by norm_num
      rw [this]; exact ENNReal.ofReal_zero

theorem ex_3_1_i_a_const :
    () ∈ I_const d_abs_gauge affine_op ex31_U := by
  intro x hx y hy
  rw [mem_ex31_U] at hx hy
  dsimp [d_abs_gauge]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rw [affine_op_eval_zero, affine_op_eval_zero]; dsimp [d_abs]; norm_num
  · rw [affine_op_eval_zero, affine_op_eval_one]; dsimp [d_abs]; norm_num
  · rw [affine_op_eval_one, affine_op_eval_zero]; dsimp [d_abs]; norm_num
  · rw [affine_op_eval_one, affine_op_eval_one]; dsimp [d_abs]; norm_num

theorem ex_3_1_i_b_fiber :
    Fib_single d_abs_gauge (affine_op * affine_op) () ((affine_op * affine_op).func (some 0)) ex31_U = {some 0} := by
  ext x
  simp only [Fib_single, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hdist⟩
    rw [mem_ex31_U] at hx
    rcases hx with rfl | rfl
    · rfl
    · dsimp [d_abs_gauge] at hdist
      rw [affine_sq_eval_one, affine_sq_eval_zero] at hdist
      dsimp [d_abs] at hdist
      have : abs (abs (1 : ℝ) - abs (-3 : ℝ)) = 2 := by norm_num
      rw [this] at hdist
      have : ENNReal.ofReal 2 ≠ 0 := by norm_num
      contradiction
  · rintro rfl
    refine ⟨by simp [mem_ex31_U], ?_⟩
    dsimp [d_abs_gauge]
    rw [affine_sq_eval_zero]
    dsimp [d_abs]
    have : abs (abs (-3 : ℝ) - abs (-3 : ℝ)) = 0 := by norm_num
    rw [this]; exact ENNReal.ofReal_zero

theorem ex_3_1_i_b_act :
    () ∈ I_act d_abs_gauge (affine_op * affine_op) ex31_U := by
  dsimp [I_act, I_const, I_id]
  simp only [Set.mem_setOf_eq, not_and]
  constructor
  · intro hconst
    have h := hconst (some 0) (by simp [mem_ex31_U]) (some 1) (by simp [mem_ex31_U])
    dsimp [d_abs_gauge] at h
    rw [affine_sq_eval_zero, affine_sq_eval_one] at h
    dsimp [d_abs] at h
    have : abs (abs (-3 : ℝ) - abs (1 : ℝ)) = 2 := by norm_num
    rw [this] at h
    have : ENNReal.ofReal 2 ≠ 0 := by norm_num
    contradiction
  · intro _ hid
    have h := hid (some 0) (by simp [mem_ex31_U])
    dsimp [d_abs_gauge] at h
    rw [affine_sq_eval_zero] at h
    dsimp [d_abs] at h
    have : abs (abs (-3 : ℝ) - abs (0 : ℝ)) = 3 := by norm_num
    rw [this] at h
    have : ENNReal.ofReal 3 ≠ 0 := by norm_num
    contradiction

theorem ex_3_1_ii (c : Option ℝ) :
    let const_op : Operator (Option ℝ) none := {
      func := fun x => match x with | none => none | some _ => c,
      preserves_bot := rfl
    }
    ∀ x ∈ ex31_U, ∀ y ∈ ex31_U,
      d_abs ((const_op * const_op).func x) ((const_op * const_op).func y) = 0 := by
  intro const_op x hx y hy
  rw [mem_ex31_U] at hx hy
  change d_abs (const_op.func (const_op.func x)) (const_op.func (const_op.func y)) = 0
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> {
    dsimp [const_op]
    cases c <;> simp [d_abs]
  }

end OperatorLocalDegeneracy
