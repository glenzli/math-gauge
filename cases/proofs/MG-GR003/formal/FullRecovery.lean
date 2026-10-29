import ErgodicConsequences

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology
namespace MathGauge.ErgodicUniform
open ErgodicOperators ErgodicRecovery
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T S : E →L[ℝ] E) (h : Commute T S) {KT KS : ℝ}
  (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS)
  (hfull : domain T S = ⊤)

def liftDomain : E →L[ℝ] domain T S :=
  (ContinuousLinearMap.id ℝ E).codRestrict (domain T S) (by intro x; rw [hfull]; trivial)

def fullProjection : E →L[ℝ] E :=
  (fixed T S).subtypeL.comp ((recovery T S h hT hS).comp (liftDomain T S hfull))

theorem fullProjection_fixed (x : E) : fullProjection T S h hT hS hfull x ∈ fixed T S :=
  (recovery T S h hT hS (liftDomain T S hfull x)).property

theorem fullProjection_difference (x : E) : x-fullProjection T S h hT hS hfull x ∈ differences T S :=
  recovered_difference T S (liftDomain T S hfull x)

theorem fullProjection_norm : ‖fullProjection T S h hT hS hfull‖ ≤ KT*KS := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg ((norm_nonneg (T^0)).trans (hT 0)) ((norm_nonneg (S^0)).trans (hS 0)))
  intro x
  exact recovered_norm T S h hT hS (liftDomain T S hfull x)

theorem fullProjection_on_fixed (x : E) (hx : x ∈ fixed T S) :
    fullProjection T S h hT hS hfull x = x := by
  have he := recovery_on_fixed T S h hT hS (⟨x,hx⟩ : fixed T S)
  exact congrArg Subtype.val he

theorem fullProjection_on_difference (x : E) (hx : x ∈ differences T S) :
    fullProjection T S h hT hS hfull x = 0 := by
  have he := (recovery_eq_zero_iff T S h hT hS (liftDomain T S hfull x)).mpr hx
  exact congrArg Subtype.val he

def differencePart : E →L[ℝ] differences T S :=
  (1-fullProjection T S h hT hS hfull).codRestrict (differences T S)
    (fullProjection_difference T S h hT hS hfull)

theorem differencePart_norm : ‖differencePart T S h hT hS hfull‖ ≤ 1+KT*KS := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have hk := mul_nonneg ((norm_nonneg (T^0)).trans (hT 0)) ((norm_nonneg (S^0)).trans (hS 0))
    positivity)
  intro x
  change ‖x-fullProjection T S h hT hS hfull x‖ ≤ _
  have hp := (fullProjection T S h hT hS hfull).le_opNorm x
  have hn := fullProjection_norm T S h hT hS hfull
  have hs := norm_sub_le x (fullProjection T S h hT hS hfull x)
  nlinarith [norm_nonneg x]

omit h hT hS hfull in
theorem iteration_invariant (x : E) (hx : x ∈ differences T S) :
    iteration T S x ∈ differences T S := by
  have hd := iteration_record T S x 1
  simp only [pow_one] at hd
  have hh := (differences T S).sub_mem hx hd
  simpa only [sub_sub_cancel] using hh

omit h hT hS hfull in
def restrictedIteration : differences T S →L[ℝ] differences T S :=
  ((iteration T S).comp (differences T S).subtypeL).codRestrict (differences T S)
    (fun y => iteration_invariant T S y y.property)

omit h hT hS hfull in
theorem restricted_power_apply (n : ℕ) (y : differences T S) :
    ((restrictedIteration T S ^ n) y).val = (iteration T S ^ n) y.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply,pow_succ',ContinuousLinearMap.mul_apply]
    change iteration T S (((restrictedIteration T S ^ n) y).val) =
      iteration T S ((iteration T S^n) y.val)
    rw [ih]

include h hT hS in
theorem restricted_power_bound (n : ℕ) : ‖restrictedIteration T S ^ n‖ ≤ KT*KS := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg ((norm_nonneg (T^0)).trans (hT 0)) ((norm_nonneg (S^0)).trans (hS 0)))
  intro y
  change ‖((restrictedIteration T S^n) y).val‖ ≤ _
  rw [restricted_power_apply]
  exact ((iteration T S^n).le_opNorm y.val).trans
    (mul_le_mul_of_nonneg_right (iteration_bound T S h hT hS n) (norm_nonneg y.val))

theorem iteration_error_identity (n : ℕ) (x : E) :
    (iteration T S^n-fullProjection T S h hT hS hfull) x =
      ((restrictedIteration T S^n) (differencePart T S h hT hS hfull x)).val := by
  rw [restricted_power_apply]
  change (iteration T S^n) x - fullProjection T S h hT hS hfull x =
    (iteration T S^n) (x-fullProjection T S h hT hS hfull x)
  rw [map_sub,iteration_fixed T S _ (fullProjection_fixed T S h hT hS hfull x)]

theorem iteration_error_bound (n : ℕ) :
    ‖iteration T S^n-fullProjection T S h hT hS hfull‖ ≤
      (1+KT*KS)*‖restrictedIteration T S^n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · have hk := mul_nonneg ((norm_nonneg (T^0)).trans (hT 0)) ((norm_nonneg (S^0)).trans (hS 0))
    exact mul_nonneg (by linarith) (norm_nonneg (restrictedIteration T S^n))
  intro x
  rw [iteration_error_identity T S h hT hS hfull]
  change ‖(restrictedIteration T S^n) (differencePart T S h hT hS hfull x)‖ ≤ _
  have h1 := (restrictedIteration T S^n).le_opNorm (differencePart T S h hT hS hfull x)
  have h2 := (differencePart T S h hT hS hfull).le_opNorm x
  have h3 := differencePart_norm T S h hT hS hfull
  have hn := norm_nonneg (restrictedIteration T S^n)
  have h4 : ‖differencePart T S h hT hS hfull x‖ ≤ (1+KT*KS)*‖x‖ :=
    h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg x))
  exact h1.trans ((mul_le_mul_of_nonneg_left h4 hn).trans_eq (by ring))

theorem restricted_error_bound (n : ℕ) :
    ‖restrictedIteration T S^n‖ ≤ ‖iteration T S^n-fullProjection T S h hT hS hfull‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  change ‖((restrictedIteration T S^n) y).val‖ ≤ _
  rw [restricted_power_apply]
  have he : (iteration T S^n-fullProjection T S h hT hS hfull) y.val =
      (iteration T S^n) y.val := by
    rw [ContinuousLinearMap.sub_apply,fullProjection_on_difference T S h hT hS hfull y.val y.property,sub_zero]
  rw [← he]
  exact (iteration T S^n-fullProjection T S h hT hS hfull).le_opNorm y.val

end MathGauge.ErgodicUniform
