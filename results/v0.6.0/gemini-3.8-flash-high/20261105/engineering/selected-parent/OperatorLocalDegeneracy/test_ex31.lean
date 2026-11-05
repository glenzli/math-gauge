import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers
import OperatorLocalDegeneracy.NullificationRadius

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

noncomputable def d_abs (x y : Option ℝ) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => ENNReal.ofReal (abs (abs a - abs b))
  | _, _ => ⊤

noncomputable def affine_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (2 * r - 1)
  preserves_bot := rfl

def ex31_U : Set (Option ℝ) := { some 0, some 1 }

lemma mem_ex31_U (x : Option ℝ) : x ∈ ex31_U ↔ x = some 0 ∨ x = some 1 := by
  dsimp [ex31_U]; simp

theorem ex_3_1_i_a :
    d_abs (affine_op.func (some 0)) (affine_op.func (some 1)) = 0 := by
  dsimp [affine_op, d_abs]
  have : abs (abs (2 * 0 - 1 : ℝ) - abs (2 * 1 - 1 : ℝ)) = 0 := by norm_num
  rw [this]
  exact ENNReal.ofReal_zero

theorem ex_3_1_i_b :
    d_abs ((affine_op * affine_op).func (some 0)) ((affine_op * affine_op).func (some 1)) = ENNReal.ofReal 2 := by
  change d_abs (affine_op.func (affine_op.func (some 0))) (affine_op.func (affine_op.func (some 1))) = ENNReal.ofReal 2
  dsimp [affine_op, d_abs]
  have : abs (abs (2 * (2 * 0 - 1) - 1 : ℝ) - abs (2 * (2 * 1 - 1) - 1 : ℝ)) = 2 := by norm_num
  rw [this]

theorem ex_3_1_ii (c : ℝ) :
    let const_op : Operator (Option ℝ) none := {
      func := fun x => match x with | none => none | some _ => some c,
      preserves_bot := rfl
    }
    ∀ x ∈ ex31_U, ∀ y ∈ ex31_U,
      d_abs ((const_op * const_op).func x) ((const_op * const_op).func y) = 0 := by
  intro const_op x hx y hy
  change d_abs (const_op.func (const_op.func x)) (const_op.func (const_op.func y)) = 0
  rw [mem_ex31_U] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · dsimp [const_op, d_abs]; simp
  · dsimp [const_op, d_abs]; simp
  · dsimp [const_op, d_abs]; simp
  · dsimp [const_op, d_abs]; simp
