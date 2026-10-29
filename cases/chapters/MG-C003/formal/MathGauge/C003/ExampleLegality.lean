import MathGauge.C003.Completeness

namespace MathGauge.C003

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

theorem seven_point_gauge_legal (i : TwoGauge) :
    ExtendedPseudoMetric SevenPoint SevenPoint.bottom (composition_counter_distance i) := by
  have h := composition_counter_distance_is_extended
  exact ⟨⟨SevenPoint.a, by decide⟩,h.1 i,h.2.1 i,h.2.2.1 i,h.2.2.2 i⟩

theorem swap_gauge_legal :
    ExtendedPseudoMetric ThreePoint ThreePoint.bottom (swap_counter_distance ()) := by
  have h := swap_counter_distance_is_extended
  exact ⟨⟨ThreePoint.a, by decide⟩,h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem infinite_gauge_legal :
    ExtendedPseudoMetric ThreePoint ThreePoint.bottom (infinite_counter_distance ()) := by
  have h := infinite_counter_distance_is_extended
  exact ⟨⟨ThreePoint.a, by decide⟩,h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem separated_gauges_legal (i : TwoGauge) :
    ExtendedPseudoMetric ThreePoint ThreePoint.bottom (separation_counter_distance i) := by
  have h := separation_counter_distance_is_extended
  exact ⟨⟨ThreePoint.a, by decide⟩,h.1 i,h.2.1 i,h.2.2.1 i,h.2.2.2.1 i⟩

theorem swap_strict_reverse_failures :
    ¬ (ActComponent swap_counter_distance swap_counter_operator three_point_domain ∪
      ActComponent swap_counter_distance swap_counter_operator
        (swap_counter_operator.func '' three_point_domain)) ⊆
      ActComponent swap_counter_distance
        (OperatorChain [swap_counter_operator, swap_counter_operator]) three_point_domain ∧
    ¬ IdComponent swap_counter_distance
        (OperatorChain [swap_counter_operator, swap_counter_operator]) three_point_domain ⊆
      (IdComponent swap_counter_distance swap_counter_operator three_point_domain ∩
      IdComponent swap_counter_distance swap_counter_operator
        (swap_counter_operator.func '' three_point_domain)) := by
  have h := swap_counterexample_is_active_but_square_is_identity
  constructor
  · intro hincl
    exact h.2.2.2.2 (hincl (Or.inl h.2.1))
  · intro hincl
    exact h.2.1.1 (hincl h.2.2.2.1).1

open formal_oet.vol_01.exercise_solutions.four_point_covering
open threshold_examples (RealPoint)

/-- Exact domains also verify that the two finite lookup operators are absorbing outside U. -/
theorem four_point_operator_domains :
    dom ordered_operator = sample_domain ∧ dom reordered_operator = sample_domain := by
  constructor
  · ext x
    by_cases hx : x ∈ sample_domain
    · have hnone : x ≠ none := by
        intro h; subst x; simp [sample_domain] at hx
      simp [dom,ordered_operator,hx,hnone]
    · simp [dom,ordered_operator,hx]
  · ext x
    by_cases h0 : x = some 0
    · subst x; norm_num [dom,reordered_operator,sample_domain] <;> decide
    by_cases h1 : x = some 1
    · subst x; norm_num [dom,reordered_operator,sample_domain] <;> decide
    by_cases h2 : x = some 2
    · subst x; norm_num [dom,reordered_operator,sample_domain] <;> decide
    by_cases h3 : x = some 3
    · subst x; norm_num [dom,reordered_operator,sample_domain] <;> decide
    simp [dom,reordered_operator,sample_domain,h0,h1,h2,h3]

theorem four_point_table :
    ordered_operator.func (some 0) = some 0 ∧ ordered_operator.func (some 1) = some 1 ∧
    ordered_operator.func (some 2) = some 2 ∧ ordered_operator.func (some 3) = some 3 ∧
    reordered_operator.func (some 0) = some 0 ∧ reordered_operator.func (some 1) = some 3 ∧
    reordered_operator.func (some 2) = some 1 ∧ reordered_operator.func (some 3) = some 2 := by
  norm_num [ordered_operator,reordered_operator,sample_domain]

end
end MathGauge.C003
