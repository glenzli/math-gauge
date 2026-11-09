import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib
open formal_oet.vol_01.ch_01_foundations
def absLineDist : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | some x, some y => ENNReal.ofReal (abs (abs x - abs y))
  | none, some _ => ⊤
  | some _, none => ⊤
def phi31 : Operator (Option ℝ) none where
  func
    | none => none
    | some x => some (2 * x - 1)
  preserves_bot := rfl
def phi31sq : Operator (Option ℝ) none := phi31 * phi31
@[simp] theorem mul_func {X} {bot:X} (φ ψ : Operator X bot) (x:X) : (φ*ψ).func x = φ.func (ψ.func x) := rfl
example : phi31sq.func (some 0) = some (-3) := by
  simp [phi31sq, phi31]
example : phi31sq.func (some 1) = some 1 := by
  simp [phi31sq, phi31]
example : absLineDist (phi31sq.func (some 0)) (phi31sq.func (some 1)) = 2 := by
  norm_num [phi31sq, phi31, absLineDist]
