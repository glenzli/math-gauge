import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace MathGauge.HilbertComplex

/-- The actual complex Hilbert sequence space in the length-one counterexample. -/
abbrev H := lp (fun _ : ℕ => ℂ) 2

def weight (n : ℕ) : ℂ := ((n : ℂ) + 1)⁻¹

theorem weight_ne_zero (n : ℕ) : weight n ≠ 0 := by
  apply inv_ne_zero
  exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)

theorem weight_norm (n : ℕ) : ‖weight n‖ = ((n : ℝ) + 1)⁻¹ := by
  rw [weight, norm_inv]
  have he : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem weight_norm_le_one (n : ℕ) : ‖weight n‖ ≤ 1 := by
  rw [weight_norm]
  exact inv_le_one_of_one_le₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

def diagonal_linear : H →ₗ[ℂ] H where
  toFun x := ⟨fun n => weight n * x n, by
    apply memℓp_gen
    have hx := (lp.memℓp x).summable (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _ hx
    intro n
    apply Real.rpow_le_rpow (norm_nonneg _) _ (by norm_num)
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (weight_norm_le_one n) (norm_nonneg (x n))⟩
  map_add' x y := by
    ext n
    change weight n * (x n + y n) = weight n * x n + weight n * y n
    ring
  map_smul' c x := by ext n; simp [Pi.smul_apply, mul_left_comm]

theorem diagonal_norm_le (x : H) : ‖diagonal_linear x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num)]
  apply Summable.tsum_le_tsum
  · intro n
    apply Real.rpow_le_rpow (norm_nonneg _) _ (by norm_num)
    change ‖weight n * x n‖ ≤ ‖x n‖
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (weight_norm_le_one n) (norm_nonneg (x n))
  · exact (lp.memℓp (diagonal_linear x)).summable (by norm_num)
  · exact (lp.memℓp x).summable (by norm_num)

/-- The differential is the reference diagonal, indexed from zero as 1/(n+1). -/
def d : H →L[ℂ] H := diagonal_linear.mkContinuous 1 (by
  intro x
  simpa using diagonal_norm_le x)

@[simp] theorem d_apply (x : H) (n : ℕ) : d x n = weight n * x n := rfl

theorem d_norm_le_one : ‖d‖ ≤ 1 := by
  apply d.opNorm_le_bound (by norm_num)
  intro x
  simpa using diagonal_norm_le x

theorem d_injective : Function.Injective d := by
  intro x y h
  ext n
  have hn := congrArg (fun z : H => z n) h
  exact mul_left_cancel₀ (weight_ne_zero n) hn

theorem d_ker : LinearMap.ker d.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr d_injective

@[simp] theorem d_single (n : ℕ) (a : ℂ) :
    d (lp.single 2 n a) = lp.single 2 n (weight n * a) := by
  ext k
  by_cases h : k = n
  · subst k; simp
  · simp [h]

theorem single_mem_range (n : ℕ) (a : ℂ) : lp.single 2 n a ∈ LinearMap.range d.toLinearMap := by
  refine ⟨lp.single 2 n ((weight n)⁻¹ * a), ?_⟩
  change d (lp.single 2 n ((weight n)⁻¹ * a)) = _
  rw [d_single, mul_inv_cancel_left₀ (weight_ne_zero n)]

/-- Every vector is a norm limit of finite sums in the differential's range. -/
theorem d_dense_range : DenseRange d := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) x)
  filter_upwards [] with s
  exact Submodule.sum_mem _ fun n _ => single_mem_range n (x n)

theorem d_range_closure : (LinearMap.range d.toLinearMap).topologicalClosure = ⊤ := by
  apply top_unique
  intro x _
  exact d_dense_range x

/-- Reduced exactness at both endpoints, with the endpoint zero differentials. -/
theorem reduced_exactness :
    LinearMap.ker d.toLinearMap = (⊥ : Submodule ℂ H) ∧
    (LinearMap.range d.toLinearMap).topologicalClosure = ⊤ :=
  ⟨d_ker, d_range_closure⟩

/-- A bounded left inverse would have to multiply each unit vector by n+1. -/
theorem no_bounded_left_inverse : ¬ ∃ s : H →L[ℂ] H, s.comp d = ContinuousLinearMap.id ℂ H := by
  rintro ⟨s, hs⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖s‖
  have he := congrArg (fun t : H →L[ℂ] H => t (lp.single 2 n ((weight n)⁻¹))) hs
  have hv : s (lp.single 2 n (1 : ℂ)) = lp.single 2 n ((weight n)⁻¹) := by
    simpa [ContinuousLinearMap.comp_apply, d_single, weight_ne_zero] using he
  have hb := s.le_opNorm (lp.single 2 n (1 : ℂ))
  rw [hv, lp.norm_single (by norm_num), lp.norm_single (by norm_num)] at hb
  simp only [norm_one, mul_one, norm_inv, weight_norm, inv_inv] at hb
  linarith

/-- Consequently no chain contraction exists for this genuine length-one Hilbert complex. -/
theorem no_chain_contraction : ¬ ∃ s : H →L[ℂ] H,
    s.comp d = ContinuousLinearMap.id ℂ H ∧
    d.comp s = ContinuousLinearMap.id ℂ H := by
  rintro ⟨s, hs, _⟩
  exact no_bounded_left_inverse ⟨s, hs⟩

theorem no_bounded_right_inverse : ¬ ∃ s : H →L[ℂ] H,
    d.comp s = ContinuousLinearMap.id ℂ H := by
  rintro ⟨s, hs⟩
  apply no_bounded_left_inverse
  refine ⟨s, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply d_injective
  exact congrArg (fun t : H →L[ℂ] H => t (d x)) hs

theorem d_self_adjoint : d.adjoint = d := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff d d).2
  intro x y
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [d_apply, RCLike.inner_apply, weight, mul_assoc, mul_left_comm]

/-- The actual degree-zero and degree-one Laplacians, including the zero endpoint terms. -/
def L₀ : H →L[ℂ] H := d.adjoint.comp d
def L₁ : H →L[ℂ] H := d.comp d.adjoint

theorem laplacians_eq : L₀ = d.comp d ∧ L₁ = d.comp d := by
  simp [L₀, L₁, d_self_adjoint]

theorem no_laplacian_right_inverse :
    (¬ ∃ G : H →L[ℂ] H, L₀.comp G = ContinuousLinearMap.id ℂ H) ∧
    (¬ ∃ G : H →L[ℂ] H, L₁.comp G = ContinuousLinearMap.id ℂ H) := by
  have hn : ¬ ∃ G : H →L[ℂ] H,
      (d.comp d).comp G = ContinuousLinearMap.id ℂ H := by
    rintro ⟨G, hG⟩
    apply no_bounded_right_inverse
    exact ⟨d.comp G, by simpa only [ContinuousLinearMap.comp_assoc] using hG⟩
  simpa only [laplacians_eq.1, laplacians_eq.2] using And.intro hn hn

theorem laplacians_injective : Function.Injective L₀ ∧ Function.Injective L₁ := by
  simpa only [laplacians_eq.1, laplacians_eq.2, ContinuousLinearMap.coe_comp'] using
    And.intro (d_injective.comp d_injective) (d_injective.comp d_injective)

theorem d_norm_eq_one : ‖d‖ = 1 := by
  apply le_antisymm d_norm_le_one
  have h := d.le_opNorm (lp.single 2 0 (1 : ℂ))
  simpa [d_single, weight, lp.norm_single (show (0 : ℝ≥0∞) < 2 by norm_num)] using h

theorem not_surjective : ¬ Function.Surjective d := by
  intro h
  let e := ContinuousLinearEquiv.ofBijective d d_ker (LinearMap.range_eq_top.mpr h)
  apply no_bounded_left_inverse
  refine ⟨e.symm.toContinuousLinearMap, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact e.symm_apply_apply x

theorem range_not_closed : ¬ IsClosed (Set.range d) := by
  intro h
  apply not_surjective
  intro x
  exact h.closure_subset (d_dense_range x)

/-- Complete counterexample to the universal task, with exact reference differential. -/
theorem counterexample :
    ‖d‖ = 1 ∧
    LinearMap.ker d.toLinearMap = ⊥ ∧
    (LinearMap.range d.toLinearMap).topologicalClosure = ⊤ ∧
    (¬ ∃ s : H →L[ℂ] H, s.comp d = ContinuousLinearMap.id ℂ H ∧
      d.comp s = ContinuousLinearMap.id ℂ H) ∧
    (¬ ∃ G : H →L[ℂ] H, L₀.comp G = ContinuousLinearMap.id ℂ H) ∧
    (¬ ∃ G : H →L[ℂ] H, L₁.comp G = ContinuousLinearMap.id ℂ H) :=
  ⟨d_norm_eq_one, d_ker, d_range_closure, no_chain_contraction,
    no_laplacian_right_inverse.1, no_laplacian_right_inverse.2⟩

end MathGauge.HilbertComplex
