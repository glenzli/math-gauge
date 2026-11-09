import Channels

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped Classical

/-- `none` is absorbing; the two ordinary points have infinite input distance
and unit output distance. The two components are indexed by `Bool`. -/
def exampleDist (i : Bool) (x y : Option Bool) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else if i then 1 else ⊤

theorem none_ne_some_bool (b : Bool) : (none : Option Bool) ≠ some b := by
  intro h
  cases h

@[reducible] def exampleMetric (i : Bool) : ExtendedPseudoMetric (Option Bool) none (exampleDist i) where
  nonabsorbing := ⟨some false, by simp⟩
  dist_self := by intro x; simp [exampleDist]
  symm := by
    intro x y
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      norm_num [exampleDist, Option.some_ne_none, none_ne_some_bool]
  triangle := by
    intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
      norm_num [exampleDist, Option.some_ne_none, none_ne_some_bool]
  isolate_bot := by intro x hx; simp [exampleDist, hx]

def exampleOp : Operator (Option Bool) none := ident
def exampleU : Set (Option Bool) := {x | x ≠ none}

theorem example_domain : exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp :=
  ⟨⟨some false, by simp [exampleU]⟩, fun _ hx => hx⟩

theorem example_positive_feasible {a : ENNReal} (ha : 0 < a) :
    a ∈ Scalars exampleDist exampleOp exampleU false true := by
  intro x hx y hy
  change x ≠ none at hx
  change y ≠ none at hy
  by_cases hxy : x = y
  · subst y
    simp [exampleOp, ident, exampleDist]
  · simp [exampleOp, ident, exampleDist, hxy, hx, hy, ENNReal.mul_top (ne_of_gt ha)]

theorem example_zero_infeasible :
    0 ∉ Scalars exampleDist exampleOp exampleU false true := by
  intro h
  have hh := h (some false) (by simp [exampleU]) (some true) (by simp [exampleU])
  norm_num [exampleDist, exampleOp, ident, Option.some_ne_none] at hh

theorem example_inf_zero : singleInf exampleDist exampleOp exampleU false true = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  obtain ⟨a, ha, hlt⟩ := exists_between (lt_of_not_ge hn)
  exact (not_lt_of_ge (sInf_le (example_positive_feasible ha))) hlt

theorem zero_not_attained :
    exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp ∧
    singleInf exampleDist exampleOp exampleU false true = 0 ∧
    0 ∉ Scalars exampleDist exampleOp exampleU false true :=
  ⟨example_domain.1, example_domain.2, example_inf_zero, example_zero_infeasible⟩

end
end HCH02
