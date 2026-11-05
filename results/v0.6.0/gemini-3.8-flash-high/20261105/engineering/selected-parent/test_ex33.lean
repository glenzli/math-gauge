
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers
import OperatorLocalDegeneracy.NullificationRadius
import OperatorLocalDegeneracy.CoveringEntropy

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

def id_op (X : Type) (bot : X) : Operator X bot := ⟨id, rfl⟩

noncomputable def trans_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (r + 1)
  preserves_bot := rfl

def ex33_U : Set (Option ℝ) := { some (-3), some (-2), some 0, some 2 }

def d_real_gauge : Unit → Option ℝ → Option ℝ → ENNReal := fun () => d_real_bot

lemma mem_ex33_U (x : Option ℝ) : x ∈ ex33_U ↔ x = some (-3) ∨ x = some (-2) ∨ x = some 0 ∨ x = some 2 := by
  dsimp [ex33_U]; simp

-- (i) Fibers of id and trans_op are singletons
theorem ex_3_3_i_id_fiber (x : Option ℝ) (hx : x ∈ ex33_U) :
    Fib_single d_real_gauge (id_op (Option ℝ) none) () ((id_op (Option ℝ) none).func x) ex33_U = {x} := by
  ext y
  simp only [Fib_single, id_op, id_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hdist⟩
    rw [mem_ex33_U] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> try rfl
    all_goals {
      dsimp [d_real_gauge, d_real_bot] at hdist
      norm_num at hdist
    }
  · rintro rfl
    refine ⟨hx, ?_⟩
    dsimp [d_real_gauge, d_real_bot]
    rw [mem_ex33_U] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem ex_3_3_i_trans_fiber (x : Option ℝ) (hx : x ∈ ex33_U) :
    Fib_single d_real_gauge trans_op () (trans_op.func x) ex33_U = {x} := by
  ext y
  simp only [Fib_single, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hdist⟩
    rw [mem_ex33_U] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> try rfl
    all_goals {
      dsimp [trans_op, d_real_gauge, d_real_bot] at hdist
      norm_num at hdist
    }
  · rintro rfl
    refine ⟨hx, ?_⟩
    dsimp [trans_op, d_real_gauge, d_real_bot]
    rw [mem_ex33_U] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp

end OperatorLocalDegeneracy
