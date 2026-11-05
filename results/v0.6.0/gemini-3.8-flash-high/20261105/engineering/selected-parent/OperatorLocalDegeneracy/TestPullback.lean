import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.FinCases
import OperatorLocalDegeneracy.ComponentPartition

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

def option_discrete_dist {α : Type} [DecidableEq α] : Option α → Option α → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => if x = y then 0 else 1

theorem option_discrete_extended {α : Type} [DecidableEq α] (hα : Nonempty α) :
    ExtendedPseudoMetric (Option α) none option_discrete_dist := by
  rcases hα with ⟨a⟩
  refine {
    nonabsorbing := ⟨some a, by simp⟩
    dist_self := by
      intro x
      cases x <;> simp [option_discrete_dist]
    symm := by
      intro x y
      cases x <;> cases y <;> simp [option_discrete_dist]
      split_ifs <;> tauto
    triangle := by
      intro x y z
      cases x <;> cases y <;> cases z <;> simp [option_discrete_dist]
      split_ifs <;> try simp <;> try (subst_vars; contradiction)
    isolate_bot := by
      intro x hx
      cases x
      · exact False.elim (hx rfl)
      · rfl
  }

theorem pullback_extended_pseudo_metric {X Y : Type} {botX : X} {botY : Y}
    (dY : Y → Y → ENNReal) (hY : ExtendedPseudoMetric Y botY dY)
    (f : X → Y) (h_bot : f botX = botY) (h_bot_iff : ∀ x, f x = botY ↔ x = botX)
    (h_nonabsorbing : ∃ x, x ≠ botX) :
    ExtendedPseudoMetric X botX (fun x y => dY (f x) (f y)) := by
  refine {
    nonabsorbing := h_nonabsorbing
    dist_self := fun x => hY.dist_self (f x)
    symm := fun x y => hY.symm (f x) (f y)
    triangle := fun x y z => hY.triangle (f x) (f y) (f z)
    isolate_bot := by
      intro x hx
      have hfx : f x ≠ botY := by
        intro h
        exact hx ((h_bot_iff x).mp h)
      have h := hY.isolate_bot (f x) hfx
      rw [h_bot]
      exact h
  }

inductive SevenPt : Type
  | bot : SevenPt
  | a : SevenPt
  | b : SevenPt
  | p : SevenPt
  | q : SevenPt
  | r : SevenPt
  | s : SevenPt
deriving DecidableEq, Fintype

def to_opt_fin5 : SevenPt → Option (Fin 5)
  | SevenPt.bot => none
  | SevenPt.a => some 0
  | SevenPt.b => some 1
  | SevenPt.p => some 2
  | SevenPt.q => some 2
  | SevenPt.r => some 3
  | SevenPt.s => some 4

def to_opt_fin6 : SevenPt → Option (Fin 6)
  | SevenPt.bot => none
  | SevenPt.a => some 0
  | SevenPt.b => some 1
  | SevenPt.p => some 2
  | SevenPt.q => some 3
  | SevenPt.r => some 4
  | SevenPt.s => some 5

def seven_pt_d0 (x y : SevenPt) : ENNReal :=
  option_discrete_dist (to_opt_fin5 x) (to_opt_fin5 y)

def seven_pt_d1 (x y : SevenPt) : ENNReal :=
  option_discrete_dist (to_opt_fin6 x) (to_opt_fin6 y)

def seven_pt_gauge : Fin 2 → SevenPt → SevenPt → ENNReal
  | 0 => seven_pt_d0
  | 1 => seven_pt_d1

theorem seven_pt_d0_extended : ExtendedPseudoMetric SevenPt SevenPt.bot seven_pt_d0 := by
  apply pullback_extended_pseudo_metric option_discrete_dist
    (option_discrete_extended ⟨0⟩) to_opt_fin5 rfl
  · intro x; cases x <;> simp [to_opt_fin5]
  · exact ⟨SevenPt.a, by decide⟩

theorem seven_pt_d1_extended : ExtendedPseudoMetric SevenPt SevenPt.bot seven_pt_d1 := by
  apply pullback_extended_pseudo_metric option_discrete_dist
    (option_discrete_extended ⟨0⟩) to_opt_fin6 rfl
  · intro x; cases x <;> simp [to_opt_fin6]
  · exact ⟨SevenPt.a, by decide⟩

theorem seven_pt_gauge_extended : ∀ i : Fin 2, ExtendedPseudoMetric SevenPt SevenPt.bot (seven_pt_gauge i) := by
  intro i
  fin_cases i
  · exact seven_pt_d0_extended
  · exact seven_pt_d1_extended

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
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
  · intro hc
    have h := hc SevenPt.a (Or.inl rfl) SevenPt.b (Or.inr rfl)
    change (1 : ENNReal) = 0 at h
    exact one_ne_zero h

end OperatorLocalDegeneracy
#print axioms OperatorLocalDegeneracy.prop_3_3_ii_counterexample
