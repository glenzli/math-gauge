import formal_oet.vol_01.ch_01_foundations.gauge_space
import Mathlib.Data.ENNReal.Basic

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

end OperatorLocalDegeneracy
