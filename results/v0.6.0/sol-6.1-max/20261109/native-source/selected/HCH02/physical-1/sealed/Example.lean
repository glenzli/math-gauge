import Scalar

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

/-- Two nonabsorbing points; input distance infinity, output distance one. -/
def exampleDist (i : Bool) (x y : Option Bool) : ℝ≥0∞ :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else if i then 1 else ⊤

theorem example_gauge (i : Bool) :
    ExtendedPseudoMetric (Option Bool) none (exampleDist i) := by
  refine
    { nonabsorbing := ⟨some false, by simp⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    simp [exampleDist]
  · intro x y
    simp [exampleDist, eq_comm, or_comm]
  · intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [exampleDist]
  · intro x hx
    simp [exampleDist, hx]

def exampleU : Set (Option Bool) := Set.range some
def exampleOp : Operator (Option Bool) none := ident

theorem example_domain : exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp := by
  refine ⟨⟨some false, ⟨false, rfl⟩⟩, ?_⟩
  rintro _ ⟨b, rfl⟩
  simp [dom, exampleOp, ident]

theorem example_positive_feasible {c : ℝ≥0∞} (hc : 0 < c) :
    c ∈ ScalarSet exampleDist exampleOp exampleU false true := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  by_cases hab : a = b
  · subst b
    simp [exampleDist, exampleOp, ident]
  · simp [exampleDist, exampleOp, ident, hab, ENNReal.mul_top (ne_of_gt hc)]

theorem example_zero_not_feasible :
    (0 : ℝ≥0∞) ∉ ScalarSet exampleDist exampleOp exampleU false true := by
  intro h
  have hz := h (some false) ⟨false, rfl⟩ (some true) ⟨true, rfl⟩
  simp [exampleDist, exampleOp, ident] at hz

theorem example_inf_zero : scalarInf exampleDist exampleOp exampleU false true = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  have ha : 0 < scalarInf exampleDist exampleOp exampleU false true := lt_of_not_ge hn
  obtain ⟨c, hc, hca⟩ := exists_between ha
  have hle : scalarInf exampleDist exampleOp exampleU false true ≤ c :=
    sInf_le (example_positive_feasible hc)
  exact (not_le_of_gt hca) hle

/-- Full counterexample, including all gauge and domain obligations. -/
theorem zero_inf_not_attained :
    (∀ i, ExtendedPseudoMetric (Option Bool) none (exampleDist i)) ∧
    exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp ∧
    scalarInf exampleDist exampleOp exampleU false true = 0 ∧
    (0 : ℝ≥0∞) ∉ ScalarSet exampleDist exampleOp exampleU false true :=
  ⟨example_gauge, example_domain.1, example_domain.2, example_inf_zero,
    example_zero_not_feasible⟩

end HCH02
