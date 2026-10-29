import ErgodicConsequences
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology Finset
namespace MathGauge.DiagonalSlow
open ErgodicOperators ErgodicRecovery
abbrev E := lp (fun _ : ℕ => ℝ) 2

/-- Zero-based index n denotes the task's positive integer j=n+1. -/
def weight (n : ℕ) : ℝ := ((n:ℝ)+1)/((n:ℝ)+2)

theorem weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity

theorem weight_lt_one (n : ℕ) : weight n < 1 := by
  unfold weight
  apply (div_lt_iff₀ (by positivity : 0 < (n:ℝ)+2)).mpr
  linarith

theorem weight_tendsto : Tendsto weight atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+2)) atTop (𝓝 0) :=
    by
      have ht : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        ht.comp (tendsto_add_atTop_nat 1)
  have he : weight = fun n : ℕ => 1-1/((n:ℝ)+2) := by
    funext n
    unfold weight
    field_simp
    ring
  rw [he]
  simpa using hi.const_sub 1

theorem squares_summable (x : E) : Summable (fun n => ‖x n‖^(2:ℕ)) := by
  simpa only [show (2:ENNReal).toReal = (2:ℝ) by norm_num,Real.rpow_two] using
    (lp.memℓp x).summable (by norm_num : 0 < (2:ENNReal).toReal)

theorem weighted_mem (x : E) : Memℓp (fun n => weight n*x n) 2 := by
  apply memℓp_gen
  simp only [show (2:ENNReal).toReal = (2:ℝ) by norm_num,Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (squares_summable x)
  intro n
  have hn : ‖weight n*x n‖ ≤ ‖x n‖ := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (weight_pos n)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_lt_one n).le
  nlinarith [norm_nonneg (weight n*x n),norm_nonneg (x n)]

def diagonalLinear : E →ₗ[ℝ] E where
  toFun x := ⟨fun n => weight n*x n,weighted_mem x⟩
  map_add' x y := by ext n; exact mul_add _ _ _
  map_smul' a x := by ext n; change weight n*(a*x n)=a*(weight n*x n); ring

theorem diagonal_norm (x : E) : ‖diagonalLinear x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2:ENNReal).toReal) (norm_nonneg _)
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal)]
  simp only [show (2:ENNReal).toReal = (2:ℝ) by norm_num,Real.rpow_two]
  apply Summable.tsum_le_tsum _ (squares_summable (diagonalLinear x)) (squares_summable x)
  intro n
  change ‖weight n*x n‖^2 ≤ ‖x n‖^2
  have hn : ‖weight n*x n‖ ≤ ‖x n‖ := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (weight_pos n)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_lt_one n).le
  nlinarith [norm_nonneg (weight n*x n),norm_nonneg (x n)]

def T : E →L[ℝ] E := diagonalLinear.mkContinuous 1 (by intro x; simpa using diagonal_norm x)

@[simp] theorem T_apply (x : E) (n : ℕ) : T x n = weight n*x n := rfl

theorem T_norm_le : ‖T‖ ≤ 1 := by
  apply T.opNorm_le_bound (by norm_num)
  intro x
  simpa using diagonal_norm x

theorem T_power_bound (n : ℕ) : ‖T^n‖ ≤ 1 := by
  induction n with
  | zero => simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (T^n),T_norm_le,norm_nonneg T])

theorem identity_power_bound (n : ℕ) : ‖(1:E →L[ℝ] E)^n‖ ≤ 1 := by
  simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))

theorem fixed_eq_zero : fixed T 1 = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have ht := ((mem_fixed_iff T 1 x).mp hx).1
  change x = 0
  ext n
  have he : weight n*x n=x n := congrArg (fun z : E => z n) ht
  have hh := weight_lt_one n
  change x n = 0
  nlinarith

theorem single_in_difference_range (n : ℕ) (a : ℝ) :
    lp.single (E := fun _ : ℕ => ℝ) 2 n a ∈ (1-T).range := by
  refine ⟨lp.single (E := fun _ : ℕ => ℝ) 2 n (((n:ℝ)+2)*a),?_⟩
  ext k
  change (lp.single (E := fun _ : ℕ => ℝ) 2 n (((n:ℝ)+2)*a)) k -
    weight k*(lp.single (E := fun _ : ℕ => ℝ) 2 n (((n:ℝ)+2)*a)) k =
      (lp.single (E := fun _ : ℕ => ℝ) 2 n a) k
  by_cases hk : k=n
  · subst k
    simp only [lp.single_apply,Pi.single_eq_same]
    unfold weight
    field_simp
    ring
  · simp [lp.single_apply,hk,Ne.symm hk]

theorem differences_eq_top : differences T 1 = ⊤ := by
  apply top_unique
  intro x _
  apply (differences_closed T 1).mem_of_tendsto (lp.hasSum_single (by norm_num) x)
  apply Eventually.of_forall
  intro s
  apply (differences T 1).sum_mem
  intro n _
  apply Submodule.le_topologicalClosure
  exact Submodule.mem_sup_left (single_in_difference_range n (x n))

theorem pointwise_rectangle (x : E) :
    Tendsto (fun nm => rectangle T 1 nm x) atTop (𝓝 0) := by
  apply (comparison T 1 (Commute.one_right T) T_power_bound identity_power_bound x 0).1.mpr
  exact ⟨Submodule.zero_mem _,by rw [differences_eq_top]; trivial⟩

theorem pointwise_iteration (x : E) :
    Tendsto (fun n => (iteration T 1^n) x) atTop (𝓝 0) := by
  apply (comparison T 1 (Commute.one_right T) T_power_bound identity_power_bound x 0).2.mpr
  exact ⟨Submodule.zero_mem _,by rw [differences_eq_top]; trivial⟩

theorem power_coordinate (n j : ℕ) (x : E) : (T^n) x j = (weight j)^n*x j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',ContinuousLinearMap.mul_apply,T_apply,ih,pow_succ]; ring

def averageWeight (n j : ℕ) : ℝ := ((n:ℝ)+1)⁻¹ * ∑ i ∈ range (n+1), weight j^i

theorem average_coordinate (n j : ℕ) (x : E) : avg T n x j = averageWeight n j*x j := by
  simp only [avg,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,lp.coeFn_sum,Finset.sum_apply,power_coordinate,averageWeight,
    Finset.sum_mul,mul_assoc]

theorem rectangle_coordinate (nm : ℕ×ℕ) (j : ℕ) (x : E) :
    rectangle T 1 nm x j = averageWeight nm.1 j*x j := by
  rw [rectangle,ContinuousLinearMap.mul_apply,avg_fixed 1 (by simp),average_coordinate]

theorem iteration_coordinate (n j : ℕ) (x : E) :
    (iteration T 1 ^ n) x j = ((1+weight j)/2)^n*x j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply]
    change ((1/4:ℝ) • ((1+T)*(1+(1:E →L[ℝ] E)))) ((iteration T 1^n) x) j = _
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.mul_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,T_apply,ih,pow_succ]
    ring

theorem averageWeight_tendsto (n : ℕ) : Tendsto (averageWeight n) atTop (𝓝 1) := by
  have ht : Tendsto (fun j => ∑ i ∈ range (n+1), weight j^i) atTop (𝓝 ((n:ℝ)+1)) := by
    convert tendsto_finset_sum (range (n+1)) (fun i _ => weight_tendsto.pow i) using 1 <;> simp
  have hn : ((n:ℝ)+1) ≠ 0 := by positivity
  simpa only [averageWeight,inv_mul_cancel₀ hn] using ht.const_mul ((n:ℝ)+1)⁻¹

theorem iterationWeight_tendsto (n : ℕ) :
    Tendsto (fun j => ((1+weight j)/2)^n) atTop (𝓝 1) := by
  simpa using ((weight_tendsto.const_add 1).div_const 2).pow n

theorem norm_lower_from_coordinates (U : E →L[ℝ] E) (a : ℕ → ℝ)
    (ha : ∀ j x, U x j = a j*x j) (ht : Tendsto a atTop (𝓝 1)) : 1 ≤ ‖U‖ := by
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  let e : E := lp.single 2 j 1
  have hn : ‖e‖ = 1 := by simp [e,lp.norm_single (show (0:ENNReal)<2 by norm_num)]
  have he : U e j = a j := by rw [ha]; simp [e,lp.single_apply]
  have hv : ‖U e j‖ ≤ ‖U e‖ := lp.norm_apply_le_norm (by norm_num) (U e) j
  have hb : ‖U e‖ ≤ ‖U‖ := by simpa only [hn,mul_one] using U.le_opNorm e
  exact (le_abs_self _).trans (he ▸ hv.trans hb)

theorem rectangle_norm_one (nm : ℕ×ℕ) : ‖rectangle T 1 nm‖ = 1 := by
  apply le_antisymm
  · simpa using rectangle_bound T 1 T_power_bound identity_power_bound nm
  · exact norm_lower_from_coordinates _ _ (rectangle_coordinate nm) (averageWeight_tendsto nm.1)

theorem iteration_norm_one (n : ℕ) : ‖iteration T 1 ^ n‖ = 1 := by
  apply le_antisymm
  · simpa using iteration_bound T 1 (Commute.one_right T) T_power_bound identity_power_bound n
  · exact norm_lower_from_coordinates _ _ (iteration_coordinate n) (iterationWeight_tendsto n)

theorem operator_limit_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    (U : ι → E →L[ℝ] E) (V : E →L[ℝ] E) (hU : Tendsto U l (𝓝 V))
    (hx : ∀ x, Tendsto (fun i => U i x) l (𝓝 0)) : V = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact tendsto_nhds_unique
    (((ContinuousLinearMap.apply ℝ E x).continuous.tendsto V).comp hU) (hx x)

theorem rectangle_no_operator_limit :
    ¬ ∃ V : E →L[ℝ] E, Tendsto (rectangle T 1) atTop (𝓝 V) := by
  rintro ⟨V,hV⟩
  have hzero := operator_limit_zero _ _ hV pointwise_rectangle
  have hn : Tendsto (fun _ : ℕ×ℕ => (1:ℝ)) atTop (𝓝 0) := by
    simpa only [rectangle_norm_one,hzero,norm_zero] using hV.norm
  have h10 : (1:ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hn
  norm_num at h10

theorem iteration_no_operator_limit :
    ¬ ∃ V : E →L[ℝ] E, Tendsto (fun n => iteration T 1^n) atTop (𝓝 V) := by
  rintro ⟨V,hV⟩
  have hzero := operator_limit_zero _ _ hV pointwise_iteration
  have hn : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 0) := by
    simpa only [iteration_norm_one,hzero,norm_zero] using hV.norm
  have h10 : (1:ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hn
  norm_num at h10

end MathGauge.DiagonalSlow
