import ExtendedData

namespace MathGauge.F112

open ENNReal
variable {X : Type*}

theorem ratio_le_iff (d e : X → ℝ≥0∞) (c : ℝ≥0∞) :
    ratioSup d e ≤ c ↔ ∀ x, d x ≠ 0 → d x ≠ ∞ → e x ≤ c * d x := by
  constructor
  · intro h x h0 ht
    have hr : e x / d x ≤ c := (le_iSup (fun y : {x : X // d x ≠ 0 ∧ d x ≠ ∞} => e y / d y) ⟨x, h0, ht⟩).trans h
    exact (ENNReal.div_le_iff h0 ht).mp hr
  · intro h
    apply iSup_le
    intro x
    exact (ENNReal.div_le_iff x.property.1 x.property.2).mpr (h x x.property.1 x.property.2)

theorem bound_iff (d e : X → ℝ≥0∞) (c : ℝ≥0∞) :
    Bound d e c ↔ ZeroCompatible d e ∧ ratioSup d e ≤ c ∧ (c = 0 → TopCompatible d e) := by
  constructor
  · intro h
    refine ⟨?_, (ratio_le_iff d e c).mpr (fun x _ _ => h x), ?_⟩
    · intro x hx
      have hx' := h x
      rw [hx, mul_zero] at hx'
      exact le_antisymm hx' bot_le
    · intro hc x hx
      have hx' := h x
      rw [hc, zero_mul] at hx'
      exact le_antisymm hx' bot_le
  · rintro ⟨hz, hr, ht⟩ x
    by_cases h0 : d x = 0
    · rw [h0, hz x h0, mul_zero]
    by_cases htop : d x = ∞
    · by_cases hc : c = 0
      · rw [htop, hc, ht hc x htop, zero_mul]
      · rw [htop, ENNReal.mul_top hc]; exact le_top
    · exact (ratio_le_iff d e c).mp hr x h0 htop

end MathGauge.F112
