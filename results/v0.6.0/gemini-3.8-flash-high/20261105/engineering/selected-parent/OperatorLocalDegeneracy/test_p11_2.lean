import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fin.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers

namespace OperatorLocalDegeneracy

set_option linter.unusedVariables false

open formal_oet.vol_01.ch_01_foundations

def inf_two_pt_d (i : Fin 2) (x y : Option (Fin 2)) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => if a = b then 0 else ⊤
  | _, _ => ⊤

lemma inf_two_pt_d_self (i : Fin 2) (x : Option (Fin 2)) : inf_two_pt_d i x x = 0 := by
  cases x <;> simp [inf_two_pt_d]

lemma inf_two_pt_d_symm (i : Fin 2) (x y : Option (Fin 2)) : inf_two_pt_d i x y = inf_two_pt_d i y x := by
  cases x <;> cases y <;> simp [inf_two_pt_d, eq_comm]

lemma inf_two_pt_d_tri (i : Fin 2) (x y z : Option (Fin 2)) : inf_two_pt_d i x z ≤ inf_two_pt_d i x y + inf_two_pt_d i y z := by
  cases x <;> cases y <;> cases z <;> simp [inf_two_pt_d]
  rename_i a b c
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab]

lemma inf_two_pt_d_iso (i : Fin 2) (x : Option (Fin 2)) (hx : x ≠ none) : inf_two_pt_d i x none = ⊤ := by
  cases x <;> [contradiction; rfl]

instance instInfTwoPtMetric (i : Fin 2) : ExtendedPseudoMetric (Option (Fin 2)) none (inf_two_pt_d i) where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := inf_two_pt_d_self i
  symm := inf_two_pt_d_symm i
  triangle := inf_two_pt_d_tri i
  isolate_bot := inf_two_pt_d_iso i

def inf_two_pt_op : Operator (Option (Fin 2)) none where
  func := id
  preserves_bot := rfl

def inf_two_pt_U : Set (Option (Fin 2)) := { some 0, some 1 }

noncomputable def r_null (d_in d_out : Option (Fin 2) → Option (Fin 2) → ENNReal)
    (ϕ : Operator (Option (Fin 2)) none) (y : Option (Fin 2)) (U : Set (Option (Fin 2))) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_uniform (d_in d_out : Option (Fin 2) → Option (Fin 2) → ENNReal)
    (ϕ : Operator (Option (Fin 2)) none) (U : Set (Option (Fin 2))) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

lemma mem_inf_two_pt_U (x : Option (Fin 2)) : x ∈ inf_two_pt_U ↔ x = some 0 ∨ x = some 1 := by
  dsimp [inf_two_pt_U]
  simp

theorem prop_3_8_ii_counterexample :
    (∀ i j : Fin 2, r_null_uniform (inf_two_pt_d i) (inf_two_pt_d j) inf_two_pt_op inf_two_pt_U = ⊤) ∧
    (∀ j : Fin 2, j ∉ I_const inf_two_pt_d inf_two_pt_op inf_two_pt_U) ∧
    (none : Option (Fin 2)) ∉ inf_two_pt_U ∧
    inf_two_pt_U.Nonempty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    dsimp [r_null_uniform, r_null]
    rw [iInf_eq_top]
    intro y
    rw [iInf_eq_top]
    intro hy
    apply sSup_eq_top.mpr
    intro b hb
    rcases exists_between hb with ⟨r, hbr, hrt⟩
    refine ⟨r, ⟨?_, hrt, ?_⟩, hbr⟩
    · exact lt_of_le_of_lt bot_le hbr
    · intro x hx hdist
      rw [mem_inf_two_pt_U] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · simp [inf_two_pt_d, inf_two_pt_op]
      · exfalso
        dsimp [inf_two_pt_d] at hdist
        exact (not_top_lt (lt_trans hdist hrt)).elim
      · exfalso
        dsimp [inf_two_pt_d] at hdist
        exact (not_top_lt (lt_trans hdist hrt)).elim
      · simp [inf_two_pt_d, inf_two_pt_op]
  · intro j hj
    dsimp [I_const] at hj
    have h0 : (some 0 : Option (Fin 2)) ∈ inf_two_pt_U := by rw [mem_inf_two_pt_U]; left; rfl
    have h1 : (some 1 : Option (Fin 2)) ∈ inf_two_pt_U := by rw [mem_inf_two_pt_U]; right; rfl
    have h01 := hj (some 0) h0 (some 1) h1
    dsimp [inf_two_pt_d, inf_two_pt_op] at h01
    contradiction
  · intro h
    rw [mem_inf_two_pt_U] at h
    rcases h with h | h <;> contradiction
  · exact ⟨some 0, by rw [mem_inf_two_pt_U]; left; rfl⟩
