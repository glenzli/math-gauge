import ShiftSpectrum

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace MathGauge.SpectralApproximation

theorem clm_smul_mul (c : ℂ) (A B : E→L[ℂ]E) : (c • A)*B=c • (A*B) := by
  ext x j
  rfl

theorem clm_mul_smul (c : ℂ) (A B : E→L[ℂ]E) : A*(c • B)=c • (A*B) := by
  ext x j
  change (A (c • B x)) j = (c • A (B x)) j
  rw [map_smul]

theorem clm_neg_mul (A B : E→L[ℂ]E) : (-A)*B= -(A*B) := by
  ext x j
  rfl

theorem clm_smul_smul (c d : ℂ) (A : E→L[ℂ]E) : c • (d • A)=(c*d) • A := by
  ext x j
  change c*(d*(A x j))=(c*d)*(A x j)
  ring

theorem clm_one_smul (A : E→L[ℂ]E) : (1:ℂ) • A=A := by
  ext x j
  change (1:ℂ)*(A x j)=A x j
  exact one_mul _

theorem truncated_power_zero (n : ℕ) : truncated n^(n+1)=0 := by
  ext x k
  rw [truncated_pow_succ,if_neg (by omega)]
  rfl

/-- Actual finite polynomial inverse displayed in the reference. -/
def finite_resolvent (n : ℕ) (μ : ℂ) : E→L[ℂ]E :=
  μ⁻¹ • ∑ k∈Finset.range (n+1), (μ⁻¹ • truncated n)^k

theorem finite_resolvent_two_sided (n : ℕ) (μ : ℂ) (hμ : μ≠0) :
    (algebraMap ℂ (E→L[ℂ]E) μ-truncated n)*finite_resolvent n μ=1 ∧
    finite_resolvent n μ*(algebraMap ℂ (E→L[ℂ]E) μ-truncated n)=1 := by
  let r := μ⁻¹ • truncated n
  let Q := ∑ k∈Finset.range (n+1), r^k
  have hr : r^(n+1)=0 := by
    change (μ⁻¹ • truncated n)^(n+1)=0
    rw [clm_smul_pow,truncated_power_zero]
    ext x j
    change (μ⁻¹^(n+1))*(0:ℂ)=0
    exact mul_zero _
  have hleft : (1-r)*Q=1 := by
    have he : (r-1)*Q = r^(n+1)-1 := mul_geom_sum r (n+1)
    rw [show (1:E→L[ℂ]E)-r= -(r-1) by abel,clm_neg_mul (r-1) Q,he,hr]
    ext x j
    change -((0:ℂ)-x j)=x j
    ring
  have hright : Q*(1-r)=1 := by
    change (∑ k∈Finset.range (n+1),r^k)*(1-r)=1
    rw [geom_sum_mul_neg r (n+1),hr]
    simp
  have hfac : algebraMap ℂ (E→L[ℂ]E) μ-truncated n = μ • (1-r) := by
    ext x j
    simp [r,smul_sub,smul_smul,hμ]
  change (algebraMap ℂ (E→L[ℂ]E) μ-truncated n)*(μ⁻¹ • Q)=1 ∧
    (μ⁻¹ • Q)*(algebraMap ℂ (E→L[ℂ]E) μ-truncated n)=1
  rw [hfac]
  constructor
  · rw [clm_smul_mul,clm_mul_smul,clm_smul_smul,mul_inv_cancel₀ hμ,clm_one_smul,hleft]
  · rw [clm_smul_mul,clm_mul_smul,clm_smul_smul,inv_mul_cancel₀ hμ,clm_one_smul,hright]

end MathGauge.SpectralApproximation
