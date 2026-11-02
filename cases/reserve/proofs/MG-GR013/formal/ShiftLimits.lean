import PolynomialNorms
import FiniteResolvent
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter Topology
namespace MathGauge.ShiftLimits
open MathGauge.SpectralApproximation

theorem truncated_pow_zero_of_ge (n m : ℕ) (hm : 0<m) (hn : n≤m) : truncated n^m=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  ext x j
  rw [truncated_pow_succ,if_neg (by omega)]
  rfl

theorem basis_norm (k : ℕ) : ‖basis_vector k‖=1 := by
  apply le_antisymm
  · apply norm_le_of_coords (by norm_num)
    intro j
    simp only [basis_apply]
    split_ifs <;> norm_num
  · simpa using coord_le (basis_vector k) k

theorem truncated_power_norm (n m : ℕ) (hm : 0<m) :
    ‖truncated n^m‖=if m<n then 1 else 0 := by
  by_cases hmn : m<n
  · rw [if_pos hmn]
    apply le_antisymm
    · have hp := pow_le_pow_left₀ (norm_nonneg (truncated n)) (truncated_norm_le n) m
      exact (norm_pow_le (truncated n) m).trans (by simpa using hp)
    · have hvec : (truncated n^m) (basis_vector 0) m=1 := by
        obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
        rw [truncated_pow_succ,if_pos ⟨le_rfl,hmn⟩]
        simp
      have hc := coord_le ((truncated n^m) (basis_vector 0)) m
      rw [hvec,norm_one] at hc
      exact hc.trans (by simpa [basis_norm] using (truncated n^m).le_opNorm (basis_vector 0))
  · rw [if_neg hmn,truncated_pow_zero_of_ge n m hm (by omega)]
    change ‖(0 : E →L[ℂ] E)‖=0
    exact @norm_zero (E →L[ℂ] E) _

def powerRootNorm (n m : ℕ) : ℝ := ‖truncated n^m‖ ^ ((m : ℝ)⁻¹)

theorem powerRootNorm_eq (n m : ℕ) (hm : 0<m) :
    powerRootNorm n m=if m<n then 1 else 0 := by
  rw [powerRootNorm,truncated_power_norm n m hm]
  split_ifs
  · exact Real.one_rpow _
  · exact Real.zero_rpow (by positivity)

theorem inner_power_limit (n : ℕ) : Tendsto (powerRootNorm n) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (max 1 n)] with m hm
  rw [powerRootNorm_eq n m (by omega),if_neg (by omega)]

theorem inner_model_limit (m : ℕ) (hm : 0<m) :
    Tendsto (fun n => powerRootNorm n m) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (m+1)] with n hn
  rw [powerRootNorm_eq n m hm,if_pos (by omega)]

/-- Each inner limit is proved separately. The outer functions are the
resulting actual constant limit values, not an exchanged double limit. -/
theorem iterated_limits :
    (∀ n,Tendsto (powerRootNorm n) atTop (𝓝 0)) ∧
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) ∧
    (∀ m,0<m → Tendsto (fun n => powerRootNorm n m) atTop (𝓝 1)) ∧
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
  ⟨inner_power_limit,tendsto_const_nhds,inner_model_limit,tendsto_const_nhds⟩

theorem no_uniform_threshold : ¬∃ N : ℕ,∀ n≥N,∀ m>0,‖truncated n^m‖=1 := by
  rintro ⟨N,h⟩
  have hN := h N le_rfl (N+1) (by omega)
  rw [truncated_power_norm N (N+1) (by omega),if_neg (by omega)] at hN
  norm_num at hN

def inverseAtOne (n : ℕ) : E →L[ℂ] E := ∑ k∈Finset.range (max 1 n),truncated n^k

theorem inverseAtOne_two_sided (n : ℕ) :
    (1-truncated n)*inverseAtOne n=1 ∧ inverseAtOne n*(1-truncated n)=1 := by
  have hz := truncated_pow_zero_of_ge n (max 1 n) (by omega) (by omega)
  constructor
  · unfold inverseAtOne
    have h := mul_geom_sum (truncated n) (max 1 n)
    have he : (1-truncated n)= -(truncated n-1) := by abel
    rw [he,clm_neg_mul,h,hz]
    ext x j
    change -((0 : ℂ)-x j)=x j
    ring
  · unfold inverseAtOne
    have hg := geom_sum_mul_neg (truncated n) (max 1 n)
    rw [hz] at hg
    exact hg.trans (sub_zero (1 : E →L[ℂ] E))

theorem inverseAtOne_as_poly (n : ℕ) :
    inverseAtOne n=poly (fun _ => 1) (max 1 n-1) (truncated n) := by
  have he : max 1 n-1+1=max 1 n := by omega
  simp only [inverseAtOne,poly,he,clm_one_smul]

theorem inverseAtOne_norm (n : ℕ) : ‖inverseAtOne n‖=(max 1 n : ℕ) := by
  cases n with
  | zero =>
    simp [inverseAtOne]
  | succ n =>
    rw [inverseAtOne_as_poly,truncated_poly_norm (fun _ => 1) _ (n+1) (by omega)]
    simp [coeff_norm,show max 1 (n+1)-1=n by omega]

theorem inverseAtOne_unique (n : ℕ) (B : E →L[ℂ] E)
    (hB : (1-truncated n)*B=1 ∧ B*(1-truncated n)=1) : B=inverseAtOne n := by
  calc B=B*((1-truncated n)*inverseAtOne n) := by rw [(inverseAtOne_two_sided n).1,mul_one]
    _=(B*(1-truncated n))*inverseAtOne n := (mul_assoc _ _ _).symm
    _=inverseAtOne n := by rw [hB.2,one_mul]

theorem inverse_norm_unbounded : ¬BddAbove (Set.range (fun n => ‖inverseAtOne n‖)) := by
  rintro ⟨C,hC⟩
  obtain ⟨n,hn⟩ := exists_nat_gt C
  have hb := hC (Set.mem_range_self n)
  rw [inverseAtOne_norm] at hb
  have : (n : ℝ) ≤ (max 1 n : ℕ) := by exact_mod_cast le_max_right 1 n
  linarith

end MathGauge.ShiftLimits
