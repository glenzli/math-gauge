import CH03.Core6
open formal_oet.vol_01.ch_01_foundations
namespace test

def d7 (k : Fin 2) (x y : Fin 7) : ENNReal :=
  if x = 0 then (if y = 0 then 0 else ⊤)
  else if y = 0 then ⊤
  else if x = y then 0
  else if k = 0 ∧ ((x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3)) then 0
  else 1

set_option maxHeartbeats 3000000 in
example (k : Fin 2) : ExtendedPseudoMetric (Fin 7) 0 (d7 k) where
  nonabsorbing := ⟨1, by decide⟩
  dist_self := by intro x; fin_cases x <;> simp [d7]
  symm := by
    intro x y
    fin_cases x <;> fin_cases y <;> fin_cases k <;> simp [d7]
  triangle := by
    intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases k <;> simp [d7]
  isolate_bot := by
    intro x hx
    fin_cases x <;> simp [d7] at hx ⊢
end test
