import ErgodicRecoveryMap
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Filter Topology

namespace MathGauge.ErgodicRecovery
open ErgodicOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T S : E →L[ℝ] E)

instance differences_closed_instance : IsClosed (differences T S : Set E) := differences_closed T S

theorem fixed_closed : IsClosed (fixed T S : Set E) :=
  (1-T).isClosed_ker.inter (1-S).isClosed_ker

def quotient_map : E →L[ℝ] (E ⧸ differences T S) :=
  (differences T S).mkQ.mkContinuous 1 (by
    intro x
    simpa using Submodule.Quotient.norm_mk_le (differences T S) x)

def quotient_fixed : fixed T S →ₗ[ℝ] (E ⧸ differences T S) :=
  (differences T S).mkQ.comp (fixed T S).subtype

def quotient_fixed_clm : fixed T S →L[ℝ] (E ⧸ differences T S) :=
  (quotient_fixed T S).mkContinuous 1 (by
    intro z
    simpa using Submodule.Quotient.norm_mk_le (differences T S) z.val)

variable (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS)
include h hT hS

theorem fixed_norm_le_representative (z : fixed T S) (v : E)
    (hv : (differences T S).mkQ v = quotient_fixed T S z) :
    ‖z‖ ≤ KT*KS*‖v‖ := by
  have hy : v-z.val ∈ differences T S := by
    apply (Submodule.Quotient.mk_eq_zero (differences T S)).mp
    change (differences T S).mkQ (v-z.val) = 0
    rw [map_sub, hv]
    simp [quotient_fixed]
  have hl := (comparison T S h hT hS v z.val).2.mpr ⟨z.property,hy⟩
  exact limit_bound atTop (fun n => iteration T S^n) (iteration_bound T S h hT hS) hl

/-- The sharp two-sided quotient stability in the reference, including the zero space case. -/
theorem fixed_quotient_bound (z : fixed T S) :
    ‖quotient_fixed T S z‖ ≤ ‖z‖ ∧ ‖z‖ ≤ KT*KS*‖quotient_fixed T S z‖ := by
  refine ⟨Submodule.Quotient.norm_mk_le _ z.val, ?_⟩
  have ht0 : 0 ≤ KT := (norm_nonneg (T^0)).trans (hT 0)
  have hs0 : 0 ≤ KS := (norm_nonneg (S^0)).trans (hS 0)
  have hK : 0 ≤ KT*KS := mul_nonneg ht0 hs0
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(KT*KS+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨v,hv,hvn⟩ := Submodule.Quotient.norm_mk_lt (quotient_fixed T S z) hδ
  have hδK : KT*KS*δ ≤ ε := by
    have he : (KT*KS+1)*δ = ε := by dsimp [δ]; field_simp
    nlinarith
  calc
    ‖z‖ ≤ KT*KS*‖v‖ := fixed_norm_le_representative T S h hT hS z v hv
    _ ≤ KT*KS*(‖quotient_fixed T S z‖+δ) := mul_le_mul_of_nonneg_left hvn.le hK
    _ ≤ KT*KS*‖quotient_fixed T S z‖+ε := by nlinarith

theorem quotient_fixed_injective : Function.Injective (quotient_fixed T S) := by
  intro z w hzw
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hb := (fixed_quotient_bound T S h hT hS (z-w)).2
  rw [map_sub, hzw, sub_self, norm_zero, mul_zero] at hb
  exact le_antisymm hb (norm_nonneg _)

def quotient_equiv : fixed T S ≃ₗ[ℝ] LinearMap.range (quotient_fixed T S) :=
  LinearEquiv.ofInjective (quotient_fixed T S) (quotient_fixed_injective T S h hT hS)

theorem quotient_inverse_property (a : LinearMap.range (quotient_fixed T S)) :
    quotient_fixed T S ((quotient_equiv T S h hT hS).symm a) = a.val :=
  congrArg Subtype.val ((quotient_equiv T S h hT hS).apply_symm_apply a)

theorem record_recovery_bound (a : LinearMap.range (quotient_fixed T S)) :
    ‖(quotient_equiv T S h hT hS).symm a‖ ≤ KT*KS*‖a‖ := by
  have hb := (fixed_quotient_bound T S h hT hS ((quotient_equiv T S h hT hS).symm a)).2
  rwa [quotient_inverse_property] at hb

/-- The actual quotient-record recovery map, defined exactly on q(Z). -/
def record_recovery : LinearMap.range (quotient_fixed T S) →L[ℝ] fixed T S :=
  (quotient_equiv T S h hT hS).symm.toLinearMap.mkContinuous (KT*KS)
    (record_recovery_bound T S h hT hS)

theorem record_recovery_two_sided (a b : LinearMap.range (quotient_fixed T S)) :
    ‖a-b‖ ≤ ‖record_recovery T S h hT hS a - record_recovery T S h hT hS b‖ ∧
    ‖record_recovery T S h hT hS a - record_recovery T S h hT hS b‖ ≤ KT*KS*‖a-b‖ := by
  rw [← map_sub]
  constructor
  · have hb := (fixed_quotient_bound T S h hT hS ((quotient_equiv T S h hT hS).symm (a-b))).1
    rwa [quotient_inverse_property] at hb
  · exact record_recovery_bound T S h hT hS (a-b)

theorem record_recovery_surjective : Function.Surjective (record_recovery T S h hT hS) :=
  (quotient_equiv T S h hT hS).symm.surjective

omit h hT hS in
theorem domain_iff_record_recoverable (x : E) :
    x ∈ domain T S ↔ (differences T S).mkQ x ∈ LinearMap.range (quotient_fixed T S) := by
  constructor
  · intro hx
    let xx : domain T S := ⟨x,hx⟩
    refine ⟨recovered T S xx, ?_⟩
    have hm := (Submodule.Quotient.mk_eq_zero (differences T S)).2 (recovered_difference T S xx)
    change (differences T S).mkQ (x-(recovered T S xx).val) = 0 at hm
    rw [map_sub, sub_eq_zero] at hm
    exact hm.symm
  · rintro ⟨z,hz⟩
    have hy : x-z.val ∈ differences T S := by
      apply (Submodule.Quotient.mk_eq_zero (differences T S)).mp
      change (differences T S).mkQ (x-z.val) = 0
      rw [map_sub, ← hz]
      simp [quotient_fixed]
    exact Submodule.mem_sup.mpr ⟨z.val,z.property,x-z.val,hy,by abel⟩

theorem record_range_closed [CompleteSpace E] :
    IsClosed (LinearMap.range (quotient_fixed T S) : Set (E ⧸ differences T S)) := by
  letI : CompleteSpace (fixed T S) := (fixed_closed T S).completeSpace_coe
  have hK : 0 ≤ KT*KS := mul_nonneg ((norm_nonneg (T^0)).trans (hT 0))
    ((norm_nonneg (S^0)).trans (hS 0))
  have ha : AntilipschitzWith ⟨KT*KS,hK⟩ (quotient_fixed_clm T S) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro z w
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (fixed_quotient_bound T S h hT hS (z-w)).2
  exact ha.isClosed_range (quotient_fixed_clm T S).uniformContinuous

theorem recovery_domain_closed [CompleteSpace E] : IsClosed (domain T S : Set E) := by
  have he : (domain T S : Set E) = (quotient_map T S) ⁻¹'
      (LinearMap.range (quotient_fixed T S) : Set (E ⧸ differences T S)) := by
    ext x
    exact domain_iff_record_recoverable T S x
  rw [he]
  exact (record_range_closed T S h hT hS).preimage (quotient_map T S).continuous

end MathGauge.ErgodicRecovery
