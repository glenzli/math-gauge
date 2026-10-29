import CoefficientClassification

namespace MathGauge.F112

open ENNReal

def sourceValue (_ : Unit) : ℝ≥0∞ := ∞
def targetValue (_ : Unit) : ℝ≥0∞ := 1

theorem boundary_ratio : ratioSup sourceValue targetValue = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro x
  exact False.elim (x.property.2 rfl)

theorem boundary_feasible : ∃ c, c ≠ ∞ ∧ Bound sourceValue targetValue c := by
  refine ⟨1, by simp, ?_⟩
  intro x
  simp [sourceValue, targetValue]

theorem boundary_not_attained : ¬ ∃ c, LeastFinite sourceValue targetValue c := by
  intro h
  have ht := ((least_finite_exists_iff sourceValue targetValue).mp h).2.2 boundary_ratio
  have := ht () rfl
  simpa [targetValue] using this

#print axioms boundary_feasible
#print axioms boundary_not_attained

end MathGauge.F112
