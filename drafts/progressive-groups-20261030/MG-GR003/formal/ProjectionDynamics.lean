import OrthogonalComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology Finset
namespace MathGauge.OrthogonalComponents
open ErgodicOperators ErgodicRecovery BinomialSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def eigen (b : Bool) : ℝ := if b then 1 else 0

theorem side_eigen {T : E →L[ℝ] E} (hT : IsStarProjection T) (b : Bool) :
    T * side T b = eigen b • side T b := by
  cases b
  · simpa [side,eigen] using hT.mul_one_sub_self
  · simpa [side,eigen] using hT.isIdempotentElem.eq

theorem component_eigen_T {T S : E →L[ℝ] E} (hT : IsStarProjection T) (i : Part) :
    T * component T S i = eigen i.1 • component T S i := by
  rw [component,← mul_assoc,side_eigen hT,smul_mul_assoc]

theorem component_eigen_S {T S : E →L[ℝ] E} (hS : IsStarProjection S)
    (h : Commute T S) (i : Part) :
    S * component T S i = eigen i.2 • component T S i := by
  have hc : Commute S (side T i.1) := by
    simpa only [side,if_true] using side_commute h.symm true i.1
  rw [component,← mul_assoc,hc.eq,mul_assoc,side_eigen hS,mul_smul_comm]

theorem power_on_component (U Q : E →L[ℝ] E) (c : ℝ) (h : U*Q = c•Q) (n : ℕ) :
    U^n*Q = c^n • Q := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',mul_assoc,ih,mul_smul_comm,h,smul_smul,pow_succ]

theorem avg_projection {T : E →L[ℝ] E} (hT : IsStarProjection T) (n : ℕ) :
    avg T n = T + ((n:ℝ)+1)⁻¹ • (1-T) := by
  have hs : (∑ i ∈ range (n+1), T^i) = 1 + (n:ℝ) • T := by
    rw [Finset.sum_range_succ']
    simp only [hT.pow_succ_eq,Finset.sum_const,Finset.card_range,pow_zero]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    module
  rw [avg,hs]
  have hn : ((n:ℝ)+1)⁻¹ * ((n:ℝ)+1) = 1 := inv_mul_cancel₀ (by positivity)
  linear_combination (norm := module) hn • T

def averageCoeff (n : ℕ) (b : Bool) : ℝ := if b then 1 else ((n:ℝ)+1)⁻¹

def lazyCoeff (b : Bool) : ℝ := if b then 1 else 1/2

theorem avg_on_component {T Q : E →L[ℝ] E} (hT : IsStarProjection T)
    (b : Bool) (hQ : T*Q = eigen b • Q) (n : ℕ) :
    avg T n * Q = averageCoeff n b • Q := by
  rw [avg_projection hT,add_mul,smul_mul_assoc,sub_mul,one_mul,hQ]
  cases b <;> simp [eigen,averageCoeff]

theorem lazy_on_component {T Q : E →L[ℝ] E} (b : Bool)
    (hQ : T*Q = eigen b • Q) : lazy T * Q = lazyCoeff b • Q := by
  rw [lazy,smul_mul_assoc,add_mul,one_mul,hQ]
  cases b <;> simp [eigen,lazyCoeff]
  module

theorem rectangle_component {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (nm : ℕ×ℕ) (i : Part) :
    rectangle T S nm * component T S i =
      (averageCoeff nm.1 i.1 * averageCoeff nm.2 i.2) • component T S i := by
  rw [rectangle,mul_assoc,avg_on_component hS i.2 (component_eigen_S hS h i),
    mul_smul_comm,avg_on_component hT i.1 (component_eigen_T hT i),smul_smul]
  congr 1
  ring

theorem iteration_component {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (n : ℕ) (i : Part) :
    iteration T S ^ n * component T S i =
      (lazyCoeff i.1 * lazyCoeff i.2)^n • component T S i := by
  apply power_on_component
  rw [iteration_eq_lazy,mul_assoc,lazy_on_component i.2 (component_eigen_S hS h i),
    mul_smul_comm,lazy_on_component i.1 (component_eigen_T hT i),smul_smul]
  congr 1
  ring

theorem operator_expansion (T S U : E →L[ℝ] E) (a : Part → ℝ)
    (ha : ∀ i, U*component T S i = a i • component T S i) (x : E) :
    U x = ∑ i, a i • component T S i x := by
  conv_lhs => rw [← component_decomposition T S x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun V : E →L[ℝ] E => V x) (ha i)

theorem projection_component {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (i : Part) :
    (T*S)*component T S i = (eigen i.1 * eigen i.2) • component T S i := by
  rw [mul_assoc,component_eigen_S hS h,mul_smul_comm,component_eigen_T hT,smul_smul]
  congr 1
  ring

theorem difference_expansion {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (U : E →L[ℝ] E)
    (a : Part → ℝ) (ha : ∀ i, U*component T S i = a i • component T S i) (x : E) :
    (U-T*S) x = ∑ i, (a i-eigen i.1*eigen i.2) • component T S i x := by
  apply operator_expansion
  intro i
  rw [sub_mul,ha i,projection_component hT hS h,sub_smul]

theorem inverse_length_nonneg (n : ℕ) : 0 ≤ ((n:ℝ)+1)⁻¹ := by positivity

theorem inverse_length_le_one (n : ℕ) : ((n:ℝ)+1)⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem rectangle_operator_bound {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (nm : ℕ×ℕ) :
    ‖rectangle T S nm - T*S‖ ≤ max ((nm.1:ℝ)+1)⁻¹ ((nm.2:ℝ)+1)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (inverse_length_nonneg _))
  intro x
  rw [difference_expansion hT hS h _ _ (rectangle_component hT hS h nm)]
  apply weighted_bound hT hS h _ (le_max_of_le_left (inverse_length_nonneg _))
  intro ⟨b,c⟩
  cases b <;> cases c <;> simp only [averageCoeff,eigen,Bool.false_eq_true,if_false,if_true,
    zero_mul,mul_zero,one_mul,mul_one,sub_zero,sub_self,abs_zero]
  · rw [abs_of_nonneg (mul_nonneg (inverse_length_nonneg _) (inverse_length_nonneg _))]
    exact (mul_le_of_le_one_right (inverse_length_nonneg _) (inverse_length_le_one _)).trans (le_max_left _ _)
  · rw [abs_of_nonneg (inverse_length_nonneg _)]; exact le_max_left _ _
  · rw [abs_of_nonneg (inverse_length_nonneg _)]; exact le_max_right _ _
  · exact le_max_of_le_left (inverse_length_nonneg _)

theorem iteration_operator_bound {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (n : ℕ) :
    ‖iteration T S ^ n - T*S‖ ≤ (1/2:ℝ)^n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [difference_expansion hT hS h _ _ (iteration_component hT hS h n)]
  apply weighted_bound hT hS h _ (by positivity)
  intro ⟨b,c⟩
  cases b <;> cases c <;> simp only [lazyCoeff,eigen,Bool.false_eq_true,if_false,if_true,
    zero_mul,mul_zero,one_mul,mul_one,sub_zero,one_pow,sub_self,abs_zero]
  · rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  · rw [abs_of_nonneg (by positivity)]
  · rw [abs_of_nonneg (by positivity)]
  · positivity

theorem projection_power_bound {T : E →L[ℝ] E} (hT : IsStarProjection T) (n : ℕ) :
    ‖T^n‖ ≤ 1 := by
  cases n with
  | zero => simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
  | succ n => rw [hT.pow_succ_eq]; exact hT.norm_le

theorem iteration_operator_converges {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) :
    Tendsto (fun n => iteration T S ^ n) atTop (𝓝 (T*S)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (iteration_operator_bound hT hS h)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem rectangle_operator_converges {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) :
    Tendsto (rectangle T S) atTop (𝓝 (T*S)) := by
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0))
  have hf : Tendsto (Prod.fst : ℕ×ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hs : Tendsto (Prod.snd : ℕ×ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_snd
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (rectangle_operator_bound hT hS h)
  simpa using (hi.comp hf).max (hi.comp hs)

theorem iteration_pointwise_converges {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (x : E) :
    Tendsto (fun n => (iteration T S ^ n) x) atTop (𝓝 ((T*S) x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun n => iteration T S ^ n - T*S) atTop (𝓝 0) := by
    simpa using (iteration_operator_converges hT hS h).sub_const (T*S)
  have hh := apply_tendsto_zero atTop ht x
  simpa only [ContinuousLinearMap.sub_apply,norm_zero] using hh.norm

theorem differences_eq_kernel {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) :
    differences T S = (T*S).ker := by
  ext x
  have hc := (comparison T S h (projection_power_bound hT)
    (projection_power_bound hS) x 0).2
  constructor
  · intro hx
    have hz : Tendsto (fun n => (iteration T S ^ n) x) atTop (𝓝 0) :=
      hc.mpr ⟨Submodule.zero_mem _,by simpa using hx⟩
    exact tendsto_nhds_unique (iteration_pointwise_converges hT hS h x) hz
  · intro hx
    have ht := iteration_pointwise_converges hT hS h x
    have hx0 : (T*S) x = 0 := hx
    rw [hx0] at ht
    simpa using (hc.mp ht).2

theorem fixed_eq_range {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) :
    fixed T S = (T*S).range := by
  ext x
  constructor
  · intro hx
    refine ⟨x,?_⟩
    obtain ⟨hTx,hSx⟩ := (mem_fixed_iff T S x).mp hx
    simp [ContinuousLinearMap.mul_apply,hSx,hTx]
  · rintro ⟨y,rfl⟩
    apply (mem_fixed_iff T S _).mpr
    constructor
    · change (T*(T*S)) y = (T*S) y
      rw [← mul_assoc,hT.isIdempotentElem.eq]
    · change (S*(T*S)) y = (T*S) y
      rw [← mul_assoc,h.symm.eq,mul_assoc,hS.isIdempotentElem.eq]

end MathGauge.OrthogonalComponents
