import ShiftSpectrum

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped ZeroAtInfty
namespace MathGauge.SpectralApproximation

/-- Polynomials are parameterized by a finite coefficient list, including their constant term. -/
def poly (a : ℕ→ℂ) (d : ℕ) (T : E→L[ℂ]E) : E→L[ℂ]E :=
  ∑ k∈Finset.range (d+1), a k • T^k

def coeff_norm (a : ℕ→ℂ) (d : ℕ) : ℝ := ∑ k∈Finset.range (d+1), ‖a k‖

theorem poly_norm_upper (a : ℕ→ℂ) (d : ℕ) (T : E→L[ℂ]E) (hT : ‖T‖≤1) :
    ‖poly a d T‖≤coeff_norm a d := by
  unfold poly coeff_norm
  refine (norm_sum_le (Finset.range (d+1)) (fun k : ℕ => (a k • T^k : E→L[ℂ]E))).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  have hs := ContinuousLinearMap.opNorm_smul_le (a k) (T^k)
  have hp : ‖T^k‖≤1 := (norm_pow_le T k).trans (by simpa using pow_le_pow_left₀ (norm_nonneg T) hT k)
  exact hs.trans (by simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg (a k)))

/-- The phase is defined at zero as well, since division by zero in ℂ is zero. -/
def phase (z : ℂ) : ℂ := (‖z‖ : ℂ)/z

theorem phase_norm (z : ℂ) : ‖phase z‖≤1 := by
  by_cases hz : z=0
  · simp [phase,hz]
  · have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
    simp [phase,norm_div,Complex.norm_real,Real.norm_of_nonneg,norm_nonneg,hn]

theorem mul_phase (z : ℂ) : z*phase z=(‖z‖:ℂ) := by
  by_cases hz : z=0
  · simp [phase,hz]
  · simp [phase,mul_div_cancel₀, hz]

def phase_vector (a : ℕ→ℂ) (d : ℕ) : E where
  toFun j := if j≤d then phase (a (d-j)) else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (d+1)] with j hj
    simp [show ¬j≤d by omega]

theorem phase_vector_bound (a : ℕ→ℂ) (d : ℕ) : ‖phase_vector a d‖≤1 := by
  apply norm_le_of_coords (by norm_num)
  intro j
  change ‖if j≤d then phase (a (d-j)) else 0‖≤1
  split_ifs
  · exact phase_norm _
  · norm_num

def coordinate (k : ℕ) : E →ₗ[ℂ] ℂ where
  toFun x := x k
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem poly_apply_coordinate (a : ℕ→ℂ) (d : ℕ) (T : E→L[ℂ]E) (x : E) (j : ℕ) :
    poly a d T x j = ∑ k∈Finset.range (d+1), a k*((T^k) x j) := by
  change coordinate j (poly a d T x) = _
  simp [poly,ContinuousLinearMap.sum_apply,map_sum,coordinate]

theorem poly_phase_coordinate (a : ℕ→ℂ) (d : ℕ) (T : E→L[ℂ]E)
    (h : ∀ k≤d, (T^k) (phase_vector a d) d=phase_vector a d (d-k)) :
    poly a d T (phase_vector a d) d=(coeff_norm a d : ℂ) := by
  rw [poly_apply_coordinate]
  simp only [coeff_norm,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k≤d := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [h k hkd]
  change a k*(if d-k≤d then phase (a (d-(d-k))) else 0)=(‖a k‖:ℂ)
  rw [if_pos (Nat.sub_le d k),Nat.sub_sub_self hkd]
  exact mul_phase (a k)

theorem coeff_norm_le_poly (a : ℕ→ℂ) (d : ℕ) (T : E→L[ℂ]E)
    (h : ∀ k≤d, (T^k) (phase_vector a d) d=phase_vector a d (d-k)) :
    coeff_norm a d≤‖poly a d T‖ := by
  have hc := coord_le (poly a d T (phase_vector a d)) d
  have hnonneg : 0≤coeff_norm a d := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rw [poly_phase_coordinate a d T h,Complex.norm_real,Real.norm_of_nonneg hnonneg] at hc
  exact hc.trans ((poly a d T).le_opNorm _ |>.trans (by
    simpa using mul_le_mul_of_nonneg_left (phase_vector_bound a d) (norm_nonneg (poly a d T))))

theorem shift_poly_norm (a : ℕ→ℂ) (d : ℕ) : ‖poly a d shift‖=coeff_norm a d := by
  apply le_antisymm (poly_norm_upper a d shift shift_norm_le)
  apply coeff_norm_le_poly
  intro k hk
  rw [shift_pow_apply,if_pos hk]

theorem truncated_poly_norm (a : ℕ→ℂ) (d n : ℕ) (hdn : d<n) :
    ‖poly a d (truncated n)‖=coeff_norm a d := by
  apply le_antisymm (poly_norm_upper a d (truncated n) (truncated_norm_le n))
  apply coeff_norm_le_poly
  intro k hk
  cases k with
  | zero => simp
  | succ k => rw [truncated_pow_succ,if_pos ⟨hk,hdn⟩]

theorem polynomial_norm_eventually_equal (a : ℕ→ℂ) (d : ℕ) :
    ∀ᶠ n in atTop, ‖poly a d (truncated n)‖=‖poly a d shift‖ := by
  filter_upwards [eventually_ge_atTop (d+1)] with n hn
  rw [truncated_poly_norm a d n (by omega),shift_poly_norm]

theorem polynomial_norm_tendsto (a : ℕ→ℂ) (d : ℕ) :
    Tendsto (fun n => ‖poly a d (truncated n)‖) atTop (𝓝 ‖poly a d shift‖) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [polynomial_norm_eventually_equal a d] with n hn
    exact hn.symm)

/-- Full legal counterexample, with each hypothesis proved for concrete continuous linear maps. -/
theorem counterexample :
    CompleteSpace E ∧ (∃x : E, x≠0) ∧ ‖shift‖≤1 ∧ (∀n, ‖truncated n‖≤1) ∧
    (∀n, FiniteDimensional ℂ (LinearMap.range (truncated n).toLinearMap)) ∧
    (∀n, IsNilpotent (truncated n)) ∧
    (∀x, Tendsto (fun n => truncated n x) atTop (𝓝 (shift x))) ∧
    (∀a d, ∀ᶠ n in atTop, ‖poly a d (truncated n)‖=‖poly a d shift‖) ∧
    (∀n, spectrum ℂ (truncated n)={0}) ∧ (1:ℂ)∈spectrum ℂ shift ∧
    ¬∃ μ : ℕ→ℂ, (∀n, μ n∈spectrum ℂ (truncated n)) ∧ Tendsto μ atTop (𝓝 1) :=
  ⟨inferInstance,⟨basis_vector 0,basis_ne_zero 0⟩,shift_norm_le,truncated_norm_le,truncated_finite_rank,truncated_nilpotent,
    truncated_strong,polynomial_norm_eventually_equal,truncated_spectrum,shift_one_spectral,
    no_spectral_approximation⟩

end MathGauge.SpectralApproximation
