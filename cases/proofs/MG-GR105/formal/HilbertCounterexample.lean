import ObservationRecovery
import FiniteProjections
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries

noncomputable section
open Topology Filter Finset
namespace MathGauge.GR105
open MathGauge.R105
abbrev L2 := lp (fun _ : ℕ => ℝ) 2

private theorem two_real : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num

theorem l2_summable_squares (x : L2) : Summable (fun n => ‖x n‖ ^ (2:ℕ)) := by
  simpa only [two_real, Real.rpow_two] using (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)

def weight (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)
theorem weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity
theorem weight_le_one (n : ℕ) : weight n ≤ 1 := by
  unfold weight
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
  linarith

theorem weighted_mem (x : L2) : Memℓp (fun n => weight n * x n) 2 := by
  apply memℓp_gen
  simp only [two_real, Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (l2_summable_squares x)
  intro n
  have hn : ‖weight n * x n‖ ≤ ‖x n‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (weight_pos n)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one n)
  nlinarith [norm_nonneg (weight n * x n), norm_nonneg (x n)]

def diagonalLinear : L2 →ₗ[ℝ] L2 where
  toFun x := ⟨fun n => weight n * x n, weighted_mem x⟩
  map_add' x y := by ext n; exact mul_add _ _ _
  map_smul' a x := by ext n; change weight n * (a * x n) = a * (weight n * x n); ring

theorem diagonal_norm_bound (x : L2) : ‖diagonalLinear x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2:ENNReal).toReal) (norm_nonneg _)
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal)]
  simp only [two_real, Real.rpow_two]
  apply Summable.tsum_le_tsum _ (l2_summable_squares (diagonalLinear x)) (l2_summable_squares x)
  intro n
  change ‖weight n * x n‖ ^ 2 ≤ ‖x n‖ ^ 2
  have hn : ‖weight n * x n‖ ≤ ‖x n‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (weight_pos n)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one n)
  nlinarith [norm_nonneg (weight n * x n), norm_nonneg (x n)]

def diagonalOperator : L2 →L[ℝ] L2 :=
  diagonalLinear.mkContinuous 1 (by intro x; simpa using diagonal_norm_bound x)

theorem diagonal_injective : Function.Injective diagonalOperator := by
  intro x y he
  ext n
  have h := congrArg (fun z : L2 => z n) he
  change weight n * x n = weight n * y n at h
  exact mul_left_cancel₀ (ne_of_gt (weight_pos n)) h

theorem single_in_diagonal_range (n : ℕ) (a : ℝ) :
    lp.single (E := fun _ : ℕ => ℝ) 2 n a ∈ diagonalOperator.range := by
  refine ⟨lp.single (E := fun _ : ℕ => ℝ) 2 n (((n:ℝ)+1)*a), ?_⟩
  ext i
  by_cases hi : i = n
  · subst i
    change weight n * (lp.single (E := fun _ : ℕ => ℝ) 2 n (((n:ℝ)+1)*a)) n = (lp.single (E := fun _ : ℕ => ℝ) 2 n a) n
    simp only [lp.single_apply, Pi.single_eq_same]
    unfold weight
    field_simp
  · change weight i * (lp.single (E := fun _ : ℕ => ℝ) 2 n (((n:ℝ)+1)*a)) i = (lp.single (E := fun _ : ℕ => ℝ) 2 n a) i
    simp [lp.single_apply, hi, Ne.symm hi]

theorem diagonal_closure_range : diagonalOperator.range.topologicalClosure = ⊤ := by
  apply top_unique
  intro x _
  apply diagonalOperator.range.isClosed_topologicalClosure.mem_of_tendsto (lp.hasSum_single (by norm_num) x)
  apply Filter.Eventually.of_forall
  intro s
  exact diagonalOperator.range.topologicalClosure.sum_mem
    (fun n _ => diagonalOperator.range.le_topologicalClosure (single_in_diagonal_range n (x n)))

theorem diagonal_dense : DenseRange diagonalOperator := by
  rw [DenseRange, dense_iff_closure_eq]
  change (diagonalOperator.range.topologicalClosure : Set L2) = Set.univ
  rw [diagonal_closure_range]
  rfl

theorem weight_mem : Memℓp weight 2 := by
  apply memℓp_gen
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
  simpa [two_real, Real.rpow_two, weight, Real.norm_eq_abs, sq_abs, div_pow] using h

def targetData : L2 := ⟨weight, weight_mem⟩

theorem target_not_in_range : targetData ∉ diagonalOperator.range := by
  rintro ⟨x, hx⟩
  have hx1 (n : ℕ) : x n = 1 := by
    have he := congrArg (fun z : L2 => z n) hx
    change weight n * x n = weight n at he
    exact mul_left_cancel₀ (ne_of_gt (weight_pos n)) (by simpa using he)
  have hs : Summable (fun _ : ℕ => (1:ℝ)) := by
    simpa [hx1] using l2_summable_squares x
  exact Set.infinite_univ (Set.Finite.of_summable_const (by norm_num) hs)

theorem target_unattained :
    ¬ ∃ x : L2, OriginalMinimizer diagonalOperator.toLinearMap targetData x := by
  rw [original_attainment_iff]
  have he : observation_closure diagonalOperator.toLinearMap = ⊤ := diagonal_closure_range
  simpa [predicted, he, Submodule.starProjection_top] using target_not_in_range

theorem target_infimum_zero : (⨅ x : L2, ‖targetData - diagonalOperator x‖) = 0 := by
  change (⨅ x : L2, ‖targetData - diagonalOperator.toLinearMap x‖) = 0
  rw [original_iInf]
  have he : observation_closure diagonalOperator.toLinearMap = ⊤ := diagonal_closure_range
  simp [predicted, he, Submodule.starProjection_top]

def coordinateSpaces (n : ℕ) : Submodule ℝ L2 :=
  Submodule.span ℝ (Set.range (fun i : Fin n => lp.single (E := fun _ : ℕ => ℝ) 2 i.val (1:ℝ)))

instance coordinateSpaces_finite (n : ℕ) : FiniteDimensional ℝ (coordinateSpaces n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem coordinateSpaces_monotone : Monotone coordinateSpaces := by
  intro n m hnm
  apply Submodule.span_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hnm⟩, rfl⟩

theorem single_mem_coordinateSpaces (n : ℕ) (a : ℝ) :
    lp.single (E := fun _ : ℕ => ℝ) 2 n a ∈ coordinateSpaces (n+1) := by
  have h : lp.single (E := fun _ : ℕ => ℝ) 2 n (1:ℝ) ∈ coordinateSpaces (n+1) :=
    Submodule.subset_span ⟨⟨n, by omega⟩, rfl⟩
  simpa only [← lp.single_smul, smul_eq_mul, mul_one] using (coordinateSpaces (n+1)).smul_mem a h

theorem coordinateSpaces_dense : (⨆ n, coordinateSpaces n).topologicalClosure = ⊤ := by
  apply top_unique
  intro x _
  apply (⨆ n, coordinateSpaces n).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num) x)
  apply Filter.Eventually.of_forall
  intro s
  exact (⨆ n, coordinateSpaces n).topologicalClosure.sum_mem
    (fun n _ => (⨆ n, coordinateSpaces n).le_topologicalClosure
      ((le_iSup coordinateSpaces (n+1)) (single_mem_coordinateSpaces n (x n))))

theorem l2_not_finite_dimensional : ¬ FiniteDimensional ℝ L2 := by
  intro h
  letI := h
  let b : HilbertBasis ℕ ℝ L2 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ L2)
  exact Module.Finite.not_linearIndependent_of_infinite b b.orthonormal.linearIndependent

theorem coordinate_projection_gap (n : ℕ) :
    ‖(coordinateSpaces n).starProjection - ContinuousLinearMap.id ℝ L2‖ = 1 := by
  have hi : ¬ FiniteDimensional ℝ (⊤ : Submodule ℝ L2) := by
    intro h
    letI := h
    haveI := Module.Finite.of_surjective (⊤ : Submodule ℝ L2).subtype
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    exact l2_not_finite_dimensional inferInstance
  simpa [Submodule.starProjection_top] using infinite_exhaustion_gap coordinateSpaces
    (⊤ : Submodule ℝ L2) (fun _ => le_top) hi n

theorem coordinate_projection_strong (x : L2) :
    Tendsto (fun n => (coordinateSpaces n).starProjection x) atTop (𝓝 x) := by
  simpa [Submodule.starProjection_top] using finite_projection_strong_limit coordinateSpaces
    (⊤ : Submodule ℝ L2) coordinateSpaces_monotone coordinateSpaces_dense x

end MathGauge.GR105
