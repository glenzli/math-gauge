
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ComponentPartition

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

noncomputable def d_abs_gauge : Unit → Option ℝ → Option ℝ → ENNReal := fun () => d_abs

theorem ex_3_1_i_a_const :
    () ∈ I_const d_abs_gauge affine_op ex31_U := by
  intro x hx y hy
  rw [mem_ex31_U] at hx hy
  dsimp [d_abs_gauge]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> {
    change d_abs (some (2 * _ - 1)) (some (2 * _ - 1)) = 0
    dsimp [d_abs]
    norm_num
  }
