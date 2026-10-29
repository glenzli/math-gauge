import UniformPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology
namespace MathGauge.ErgodicUniform
open ErgodicOperators ErgodicRecovery
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact algebraic decomposition for the actual R in the question. -/
theorem iteration_difference_identity (T S : E →L[ℝ] E) :
    1-iteration T S = (1/2:ℝ) • (1-T) + (1/4:ℝ) • ((1+T)*(1-S)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [iteration,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.mul_apply,
    map_add,map_sub]
  module

def defectBound (KT KS : ℝ) (nm : ℕ×ℕ) : ℝ :=
  ((1+KT)*KS)/2*((nm.1:ℝ)+1)⁻¹ + ((1+KT)*KT*(1+KS))/4*((nm.2:ℝ)+1)⁻¹

variable (T S : E →L[ℝ] E) (h : Commute T S) {KT KS : ℝ}
  (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS)

local instance avg_restricted_normed : NormedAddCommGroup (differences T S) := inferInstance
local instance avg_restricted_space : NormedSpace ℝ (differences T S) := inferInstance
local instance avg_restricted_end_normed : NormedAddCommGroup
    (differences T S →L[ℝ] differences T S) := inferInstance

include h hT hS in
theorem rectangle_iteration_defect (nm : ℕ×ℕ) :
    ‖rectangle T S nm*(1-iteration T S)‖ ≤ defectBound KT KS nm := by
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  have hs0 : 0 ≤ KS := (norm_nonneg (S^0)).trans (hS 0)
  have ht1 : ‖T‖ ≤ KT := by simpa only [pow_one] using hT 1
  have h1 : ‖(1:E →L[ℝ] E)+T‖ ≤ 1+KT :=
    (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ht1)
  have hc : Commute (rectangle T S nm) (1+T) :=
    (Commute.one_right _).add_right (rectangle_commute_T T S h nm)
  rw [iteration_difference_identity,mul_add,mul_smul_comm,mul_smul_comm,
    ← mul_assoc _ (1+T),hc.eq,mul_assoc]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),abs_of_pos (by norm_num : (0:ℝ)<1/4)]
  have ha := rectangle_defect_sharp_T T S h hT hS nm
  have hb := rectangle_defect_sharp_S T S hT hS nm
  have hh : ‖((1:E →L[ℝ] E)+T)*(rectangle T S nm*(1-S))‖ ≤
      (1+KT)*(KT*(1+KS)*((nm.2:ℝ)+1)⁻¹) := by
    exact (norm_mul_le _ _).trans (mul_le_mul h1 hb (norm_nonneg _) (by positivity))
  unfold defectBound
  nlinarith

variable [CompleteSpace E]

def neumannOperator : differences T S →L[ℝ] differences T S :=
  ∑' n : ℕ, restrictedIteration T S^n

theorem restricted_geometric_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hR : ‖restrictedIteration T S‖ ≤ r) :
    Summable (fun n : ℕ => restrictedIteration T S^n) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hr1)
  exact operator_power_bound _ hr0 hR

theorem neumannOperator_norm {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hR : ‖restrictedIteration T S‖ ≤ r) :
    ‖neumannOperator T S‖ ≤ (1-r)⁻¹ :=
  tsum_of_norm_bounded (hasSum_geometric_of_lt_one hr0 hr1) (operator_power_bound _ hr0 hR)

theorem neumannOperator_right {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hR : ‖restrictedIteration T S‖ ≤ r) :
    (1-restrictedIteration T S)*neumannOperator T S = 1 :=
  (restricted_geometric_summable T S hr0 hr1 hR).one_sub_mul_tsum_pow

variable (hfull : domain T S = ⊤)

theorem lifted_difference {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hR : ‖restrictedIteration T S‖ ≤ r) (x : E) :
    (1-iteration T S) ((neumannOperator T S (differencePart T S h hT hS hfull x)).val) =
      x-fullProjection T S h hT hS hfull x := by
  have he := congrArg (fun U : differences T S →L[ℝ] differences T S =>
    (U (differencePart T S h hT hS hfull x)).val) (neumannOperator_right T S hr0 hr1 hR)
  exact he

theorem rectangle_geometric_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hR : ‖restrictedIteration T S‖ ≤ r) (nm : ℕ×ℕ) :
    ‖rectangle T S nm-fullProjection T S h hT hS hfull‖ ≤
      (1+KT*KS)*defectBound KT KS nm/(1-r) := by
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  have hs0 : 0 ≤ KS := (norm_nonneg (S^0)).trans (hS 0)
  have hb0 : 0 ≤ defectBound KT KS nm := by unfold defectBound; positivity
  have hden : 0 < 1-r := by linarith
  have hi0 : 0 ≤ (1-r)⁻¹ := inv_nonneg.mpr hden.le
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  let y := differencePart T S h hT hS hfull x
  let u := neumannOperator T S y
  have he : (rectangle T S nm-fullProjection T S h hT hS hfull) x =
      (rectangle T S nm*(1-iteration T S)) u.val := by
    rw [ContinuousLinearMap.mul_apply,lifted_difference T S h hT hS hfull hr0 hr1 hR x]
    rw [map_sub,rectangle_fixed T S _ (fullProjection_fixed T S h hT hS hfull x)]
    rfl
  have hu : ‖u‖ ≤ (1-r)⁻¹*((1+KT*KS)*‖x‖) := by
    have h1 := (neumannOperator T S).le_opNorm y
    have h2 := (differencePart T S h hT hS hfull).le_opNorm x
    have h3 := differencePart_norm T S h hT hS hfull
    have h4 := neumannOperator_norm T S hr0 hr1 hR
    have hy : ‖y‖ ≤ (1+KT*KS)*‖x‖ := h2.trans
      (mul_le_mul_of_nonneg_right h3 (norm_nonneg x))
    exact h1.trans (mul_le_mul h4 hy (norm_nonneg _) hi0)
  rw [he]
  calc
    _ ≤ ‖rectangle T S nm*(1-iteration T S)‖*‖u.val‖ :=
      (rectangle T S nm*(1-iteration T S)).le_opNorm u.val
    _ ≤ defectBound KT KS nm*((1-r)⁻¹*((1+KT*KS)*‖x‖)) :=
      mul_le_mul (rectangle_iteration_defect T S h hT hS nm) hu (norm_nonneg _) hb0
    _ = ((1+KT*KS)*defectBound KT KS nm/(1-r))*‖x‖ := by ring

end MathGauge.ErgodicUniform
