import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.FinCases
import OperatorLocalDegeneracy.ComponentPartition

namespace OperatorLocalDegeneracy

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

inductive TwoPt : Type
  | a : TwoPt
  | b : TwoPt
  | bot : TwoPt
deriving DecidableEq, Fintype

def two_pt_dist (x y : TwoPt) : ENNReal :=
  if x = TwoPt.bot ∧ y = TwoPt.bot then 0
  else if x = TwoPt.bot ∨ y = TwoPt.bot then ⊤
  else if x = y then 0 else 1

def two_pt_gauge : Unit → TwoPt → TwoPt → ENNReal :=
  fun () => two_pt_dist

theorem two_pt_gauge_extended : ∀ i : Unit, ExtendedPseudoMetric TwoPt TwoPt.bot (two_pt_gauge i) := by
  intro ()
  refine {
    nonabsorbing := ⟨TwoPt.a, by decide⟩
    dist_self := by intro x; cases x <;> simp [two_pt_gauge, two_pt_dist]
    symm := by intro x y; cases x <;> cases y <;> simp [two_pt_gauge, two_pt_dist]
    triangle := by intro x y z; cases x <;> cases y <;> cases z <;> simp [two_pt_gauge, two_pt_dist]
    isolate_bot := by intro x hx; cases x <;> simp [two_pt_gauge, two_pt_dist] <;> try contradiction
  }

def swap_func : TwoPt → TwoPt
  | TwoPt.a => TwoPt.b
  | TwoPt.b => TwoPt.a
  | TwoPt.bot => TwoPt.bot

def swap_op : Operator TwoPt TwoPt.bot :=
  ⟨swap_func, rfl⟩

def two_pt_U : Set TwoPt := {TwoPt.a, TwoPt.b}

theorem swap_im : swap_op.func '' two_pt_U = two_pt_U := by
  ext x
  simp only [two_pt_U, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩
    · right; rfl
    · left; rfl
  · rintro (rfl | rfl)
    · exact ⟨TwoPt.b, Or.inr rfl, rfl⟩
    · exact ⟨TwoPt.a, Or.inl rfl, rfl⟩

theorem swap_I_act : () ∈ I_act two_pt_gauge swap_op two_pt_U := by
  dsimp [I_act, I_const, I_id]
  refine ⟨?_, ?_⟩
  · intro hc
    have h := hc TwoPt.a (Or.inl rfl) TwoPt.b (Or.inr rfl)
    change two_pt_dist TwoPt.b TwoPt.a = 0 at h
    simp [two_pt_dist] at h
  · rintro ⟨-, hid⟩
    have h := hid TwoPt.a (Or.inl rfl)
    change two_pt_dist TwoPt.b TwoPt.a = 0 at h
    simp [two_pt_dist] at h

theorem swap_comp_I_id : () ∈ I_id two_pt_gauge (swap_op * swap_op) two_pt_U := by
  dsimp [I_id, I_const]
  refine ⟨?_, ?_⟩
  · intro hc
    have h := hc TwoPt.a (Or.inl rfl) TwoPt.b (Or.inr rfl)
    change two_pt_dist TwoPt.a TwoPt.b = 0 at h
    simp [two_pt_dist] at h
  · intro x hx
    rcases hx with rfl | rfl
    · change two_pt_dist TwoPt.a TwoPt.a = 0
      simp [two_pt_dist]
    · change two_pt_dist TwoPt.b TwoPt.b = 0
      simp [two_pt_dist]

theorem swap_comp_I_act_empty : I_act two_pt_gauge (swap_op * swap_op) two_pt_U = ∅ := by
  ext x; cases x
  simp [I_act]
  intro _
  exact swap_comp_I_id

/-- CH03-P03-01: 注（复合分量保持的逆向蕴含一般不成立） -/
theorem remark_3_2_counterexample :
    (¬ (I_act two_pt_gauge swap_op two_pt_U ∪ I_act two_pt_gauge swap_op (swap_op.func '' two_pt_U) ⊆
        I_act two_pt_gauge (swap_op * swap_op) two_pt_U)) ∧
    (¬ (I_id two_pt_gauge (swap_op * swap_op) two_pt_U ⊆
        I_id two_pt_gauge swap_op two_pt_U ∩ I_id two_pt_gauge swap_op (swap_op.func '' two_pt_U))) := by
  constructor
  · intro hsub
    have h_mem : () ∈ I_act two_pt_gauge swap_op two_pt_U ∪ I_act two_pt_gauge swap_op (swap_op.func '' two_pt_U) :=
      Or.inl swap_I_act
    have h_in := hsub h_mem
    rw [swap_comp_I_act_empty] at h_in
    exact h_in
  · intro hsub
    have h_in := hsub swap_comp_I_id
    rcases h_in with ⟨h1, -⟩
    have h_act := swap_I_act
    dsimp [I_act] at h_act
    exact h_act.2 h1

inductive SevenPt : Type
  | bot : SevenPt
  | a : SevenPt
  | b : SevenPt
  | p : SevenPt
  | q : SevenPt
  | r : SevenPt
  | s : SevenPt
deriving DecidableEq, Fintype

def seven_pt_d0 (x y : SevenPt) : ENNReal :=
  if x = SevenPt.bot ∧ y = SevenPt.bot then 0
  else if x = SevenPt.bot ∨ y = SevenPt.bot then ⊤
  else if x = y then 0
  else if (x = SevenPt.p ∧ y = SevenPt.q) ∨ (x = SevenPt.q ∧ y = SevenPt.p) then 0
  else 1

def seven_pt_d1 (x y : SevenPt) : ENNReal :=
  if x = SevenPt.bot ∧ y = SevenPt.bot then 0
  else if x = SevenPt.bot ∨ y = SevenPt.bot then ⊤
  else if x = y then 0
  else 1

def seven_pt_gauge : Fin 2 → SevenPt → SevenPt → ENNReal
  | 0 => seven_pt_d0
  | 1 => seven_pt_d1

theorem seven_pt_gauge_extended : ∀ i : Fin 2, ExtendedPseudoMetric SevenPt SevenPt.bot (seven_pt_gauge i) := by
  intro i
  fin_cases i
  · refine {
      nonabsorbing := ⟨SevenPt.a, by decide⟩
      dist_self := by intro x; cases x <;> simp [seven_pt_gauge, seven_pt_d0]
      symm := by intro x y; cases x <;> cases y <;> simp [seven_pt_gauge, seven_pt_d0]
      triangle := by intro x y z; cases x <;> cases y <;> cases z <;> simp [seven_pt_gauge, seven_pt_d0]
      isolate_bot := by intro x hx; cases x <;> simp [seven_pt_gauge, seven_pt_d0] <;> try contradiction
    }
  · refine {
      nonabsorbing := ⟨SevenPt.a, by decide⟩
      dist_self := by intro x; cases x <;> simp [seven_pt_gauge, seven_pt_d1]
      symm := by intro x y; cases x <;> cases y <;> simp [seven_pt_gauge, seven_pt_d1]
      triangle := by intro x y z; cases x <;> cases y <;> cases z <;> simp [seven_pt_gauge, seven_pt_d1]
      isolate_bot := by intro x hx; cases x <;> simp [seven_pt_gauge, seven_pt_d1] <;> try contradiction
    }

def seven_phi_func : SevenPt → SevenPt
  | SevenPt.a => SevenPt.p
  | SevenPt.b => SevenPt.q
  | _ => SevenPt.bot

def seven_psi_func : SevenPt → SevenPt
  | SevenPt.p => SevenPt.r
  | SevenPt.q => SevenPt.s
  | _ => SevenPt.bot

def seven_phi : Operator SevenPt SevenPt.bot := ⟨seven_phi_func, rfl⟩
def seven_psi : Operator SevenPt SevenPt.bot := ⟨seven_psi_func, rfl⟩

def seven_U : Set SevenPt := {SevenPt.a, SevenPt.b}

/-- CH03-P04-02: 命题 3.3 (ii) 内侧同分量零距未必复合零距的合法七点、双分量反例 -/
theorem prop_3_3_ii_counterexample :
    (0 : Fin 2) ∈ I_const seven_pt_gauge seven_phi seven_U ∧
    (0 : Fin 2) ∉ I_const seven_pt_gauge (seven_psi * seven_phi) seven_U := by
  constructor
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [seven_phi, seven_phi_func, seven_pt_gauge, seven_pt_d0]
  · intro hc
    have h := hc SevenPt.a (Or.inl rfl) SevenPt.b (Or.inr rfl)
    change seven_pt_d0 SevenPt.r SevenPt.s = 0 at h
    simp [seven_pt_d0] at h

end OperatorLocalDegeneracy
