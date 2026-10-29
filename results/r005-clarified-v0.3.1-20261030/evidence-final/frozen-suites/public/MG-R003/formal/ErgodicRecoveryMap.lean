import ErgodicComparison
import Mathlib.Algebra.Module.Submodule.Equiv

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Filter Topology

namespace MathGauge.ErgodicRecovery
open ErgodicOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T S : E →L[ℝ] E)

def domain : Submodule ℝ E := fixed T S ⊔ differences T S

theorem domain_decomposition (x : domain T S) :
    ∃ z : E, z ∈ fixed T S ∧ x.val-z ∈ differences T S := by
  obtain ⟨z,hz,y,hy,hxy⟩ := Submodule.mem_sup.mp x.property
  refine ⟨z,hz,?_⟩
  rw [← hxy]
  simpa using hy

def recovered (x : domain T S) : fixed T S :=
  ⟨Classical.choose (domain_decomposition T S x),
    (Classical.choose_spec (domain_decomposition T S x)).1⟩

theorem recovered_difference (x : domain T S) :
    x.val-(recovered T S x).val ∈ differences T S :=
  (Classical.choose_spec (domain_decomposition T S x)).2

variable (h : Commute T S) {KT KS : ℝ}
    (hT : ∀ n : ℕ, ‖T^n‖ ≤ KT) (hS : ∀ n : ℕ, ‖S^n‖ ≤ KS)
include h hT hS

theorem recovered_limit (x : domain T S) :
    Tendsto (fun n => (iteration T S ^ n) x.val) atTop (𝓝 (recovered T S x).val) :=
  (comparison T S h hT hS _ _).2.mpr ⟨(recovered T S x).property, recovered_difference T S x⟩

theorem recovered_norm (x : domain T S) : ‖recovered T S x‖ ≤ KT*KS*‖x‖ :=
  limit_bound atTop (fun n => iteration T S ^ n) (iteration_bound T S h hT hS)
    (recovered_limit T S h hT hS x)

def recovery_linear : domain T S →ₗ[ℝ] fixed T S where
  toFun := recovered T S
  map_add' x y := by
    apply Subtype.ext
    apply tendsto_nhds_unique (recovered_limit T S h hT hS (x+y))
    simpa using (recovered_limit T S h hT hS x).add (recovered_limit T S h hT hS y)
  map_smul' c x := by
    apply Subtype.ext
    apply tendsto_nhds_unique (recovered_limit T S h hT hS (c • x))
    simpa using (recovered_limit T S h hT hS x).const_smul c

/-- The requested bounded linear recovery map on every recoverable input. -/
def recovery : domain T S →L[ℝ] fixed T S :=
  (recovery_linear T S h hT hS).mkContinuous (KT*KS) (recovered_norm T S h hT hS)

theorem recovery_stable (x y : domain T S) :
    ‖recovery T S h hT hS x - recovery T S h hT hS y‖ ≤ KT*KS*‖x-y‖ := by
  rw [← map_sub]
  exact recovered_norm T S h hT hS (x-y)

omit h hT hS in
theorem fixed_mem_domain (z : fixed T S) : z.val ∈ domain T S := Submodule.mem_sup_left z.property

theorem recovery_on_fixed (z : fixed T S) :
    recovery T S h hT hS ⟨z.val, fixed_mem_domain T S z⟩ = z := by
  apply Subtype.ext
  apply tendsto_nhds_unique (recovered_limit T S h hT hS ⟨z.val, fixed_mem_domain T S z⟩)
  simpa only [iteration_fixed T S z.val z.property] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => z.val) atTop (𝓝 z.val))

theorem recovery_surjective : Function.Surjective (recovery T S h hT hS) := by
  intro z
  exact ⟨⟨z.val, fixed_mem_domain T S z⟩, recovery_on_fixed T S h hT hS z⟩

theorem recovery_eq_zero_iff (x : domain T S) :
    recovery T S h hT hS x = 0 ↔ x.val ∈ differences T S := by
  constructor
  · intro hx
    have he := recovered_difference T S x
    have hz : (recovered T S x).val = 0 := congrArg Subtype.val hx
    simpa only [hz, sub_zero] using he
  · intro hx
    apply Subtype.ext
    apply tendsto_nhds_unique (recovered_limit T S h hT hS x)
    apply (comparison T S h hT hS _ _).2.mpr
    exact ⟨Submodule.zero_mem _, by simpa using hx⟩

theorem recovery_depends_only_on_record (x y : domain T S)
    (hxy : (differences T S).mkQ x.val = (differences T S).mkQ y.val) :
    recovery T S h hT hS x = recovery T S h hT hS y := by
  apply sub_eq_zero.mp
  rw [← map_sub, recovery_eq_zero_iff T S h hT hS]
  apply (Submodule.Quotient.mk_eq_zero (differences T S)).mp
  change (differences T S).mkQ (x.val-y.val) = 0
  rw [map_sub, hxy, sub_self]

theorem full_convergence_domain (x : E) :
    (∃ z, Tendsto (fun nm => rectangle T S nm x) atTop (𝓝 z)) ↔ x ∈ domain T S := by
  constructor
  · rintro ⟨z,hz⟩
    have hh := (comparison T S h hT hS x z).1.mp hz
    exact Submodule.mem_sup.mpr ⟨z,hh.1,x-z,hh.2,by abel⟩
  · intro hx
    refine ⟨(recovered T S ⟨x,hx⟩).val, ?_⟩
    exact (equal_convergence_and_limits T S h hT hS _ _).mpr
      (recovered_limit T S h hT hS ⟨x,hx⟩)

theorem direct_sum : Disjoint (fixed T S) (differences T S) := by
  apply Submodule.disjoint_def.mpr
  intro z hz hy
  have hlim : Tendsto (fun n => (iteration T S^n) z) atTop (𝓝 (0:E)) :=
    (comparison T S h hT hS z 0).2.mpr ⟨Submodule.zero_mem _, by simpa using hy⟩
  have hconst : Tendsto (fun n => (iteration T S^n) z) atTop (𝓝 z) := by
    simpa only [iteration_fixed T S z hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
  exact tendsto_nhds_unique hconst hlim

end MathGauge.ErgodicRecovery
