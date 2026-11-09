import formal_oet.vol_01.ch_01_foundations.operator_space
open formal_oet.vol_01.ch_01_foundations
def swapAB : Operator (Fin 3) 0 where
  func x := if x = 1 then 2 else if x = 2 then 1 else 0
  preserves_bot := by simp
example : swapAB * swapAB = (1 : Operator (Fin 3) 0) := by
  apply Operator.ext
  funext x
  change swapAB.func (swapAB.func x) = x
  fin_cases x <;> simp [swapAB]
