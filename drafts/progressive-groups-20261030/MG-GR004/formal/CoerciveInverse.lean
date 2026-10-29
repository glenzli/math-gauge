import ClosedRange

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace MathGauge.HilbertCriteria
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- A genuine coercive bounded operator has closed range and a bounded inverse, without a prepackaged solver. -/
theorem coercive_bijective (L : F →L[ℂ] F) (c : ℝ) (hc : 0<c)
    (h : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) :
    Function.Bijective L ∧ (∀ x, ‖x‖ ≤ c⁻¹*‖L x‖) := by
  have hbound : ∀ x, ‖x‖ ≤ c⁻¹*‖L x‖ := by
    intro x
    have he := (h x).trans (re_inner_le_norm (𝕜 := ℂ) (L x) x)
    by_cases hx : ‖x‖=0
    · rw [hx]; positivity
    · have hn : 0<‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
      have hh : c*‖x‖ ≤ ‖L x‖ := by nlinarith
      have hh2 : ‖x‖ * c ≤ ‖L x‖ := by simpa [mul_comm] using hh
      simpa [div_eq_mul_inv,mul_comm] using (le_div_iff₀ hc).mpr hh2
  have ha : AntilipschitzWith ⟨c⁻¹,inv_nonneg.mpr hc.le⟩ L := L.antilipschitz_of_bound hbound
  have hclosed : IsClosed (L.range : Set F) := ha.isClosed_range L.uniformContinuous
  letI : CompleteSpace L.range := hclosed.completeSpace_coe
  have ht : L.range=⊤ := by
    rw [← L.range.orthogonal_orthogonal,Submodule.eq_top_iff']
    intro x y hy
    have hh : inner ℂ (L y) y=0 := (L.range.mem_orthogonal y).mp hy (L y) ⟨y,rfl⟩
    have hy0 : y=0 := by
      have he := h y
      rw [hh,Complex.zero_re] at he
      have hz : ‖y‖^2 ≤ 0 := by
        by_contra! hz
        exact (not_le_of_gt (mul_pos hc hz)) he
      have : ‖y‖=0 := by nlinarith [sq_nonneg ‖y‖,norm_nonneg y]
      exact norm_eq_zero.mp this
    rw [hy0,inner_zero_left]
  exact ⟨⟨ha.injective,LinearMap.range_eq_top.mp ht⟩,hbound⟩

def coerciveEquiv (L : F →L[ℂ] F) (c : ℝ) (hc : 0<c)
    (h : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) : F ≃L[ℂ] F :=
  ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr (coercive_bijective L c hc h).1.1)
    (LinearMap.range_eq_top.mpr (coercive_bijective L c hc h).1.2)

theorem coercive_inverse_bound (L : F →L[ℂ] F) (c : ℝ) (hc : 0<c)
    (h : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) :
    ‖(coerciveEquiv L c hc h).symm.toContinuousLinearMap‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
  intro x
  have hh := (coercive_bijective L c hc h).2 ((coerciveEquiv L c hc h).symm x)
  have hid : L ((coerciveEquiv L c hc h).symm x)=x := (coerciveEquiv L c hc h).apply_symm_apply x
  rw [hid] at hh
  exact hh

end MathGauge.HilbertCriteria
