import FiniteConstraints
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open Set Filter Topology InnerProductSpace Function
namespace MathGauge.VariationalIteration
open MathGauge.FiniteConstraints
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K) (hco : Convex ℝ K)

theorem projection_variational_iff (x p : H) :
    project K hne hcl hco x = p ↔ p ∈ K ∧ ∀ z ∈ K, ⟪x-p,z-p⟫_ℝ ≤ 0 := by
  constructor
  · rintro rfl
    exact ⟨(project_spec K hne hcl hco x).1,
      fun z hz => project_variation K hne hcl hco x z hz⟩
  · rintro ⟨hp,hv⟩
    have he := (norm_eq_iInf_iff_real_inner_le_zero hco hp).2 hv
    symm
    apply project_unique K hne hcl hco x p hp
    intro z hz
    rw [he]
    exact ciInf_le (f := fun w : K => ‖x-w‖)
      ⟨0,Set.forall_mem_range.2 (fun _ => norm_nonneg _)⟩ ⟨z,hz⟩

def step (A : H → H) (γ : ℝ) (x : H) : H := project K hne hcl hco (x - γ • A x)

def vi (A : H → H) (p : H) : Prop := p ∈ K ∧ ∀ z ∈ K, 0 ≤ ⟪A p,z-p⟫_ℝ

theorem fixed_iff_vi (A : H → H) {γ : ℝ} (hγ : 0 < γ) (p : H) :
    IsFixedPt (step K hne hcl hco A γ) p ↔ vi K A p := by
  change project K hne hcl hco (p-γ • A p) = p ↔ _
  rw [projection_variational_iff]
  constructor
  · rintro ⟨hp,hv⟩
    refine ⟨hp,fun z hz => ?_⟩
    have h := hv z hz
    have he : p-γ • A p-p = -γ • A p := by module
    rw [he, real_inner_smul_left] at h
    nlinarith
  · rintro ⟨hp,hv⟩
    refine ⟨hp,fun z hz => ?_⟩
    have he : p-γ • A p-p = -γ • A p := by module
    rw [he,real_inner_smul_left]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hv z hz)

def rate (m L γ : ℝ) : ℝ := Real.sqrt (1 - 2*γ*m + γ^2*L^2)

theorem rate_range {m L γ : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hγ : 0 < γ) (hγu : γ < 2*m/L^2) : 0 ≤ rate m L γ ∧ rate m L γ < 1 := by
  have hL2 : 0 < L^2 := sq_pos_of_pos hL
  have hs : γ*L^2 < 2*m := (lt_div_iff₀ hL2).1 hγu
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  change Real.sqrt _ < 1
  apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).2
  nlinarith [mul_pos hγ (sub_pos.2 hs)]

/-- This estimate uses max(s,0)=sqrt(s)^2, so it includes the zero Hilbert
space without silently inferring m≤L from two nonexistent distinct points. -/
theorem forward_step_bound (A : H → H) {m L γ : ℝ}
    (hL : 0 < L) (hγ : 0 < γ)
    (hstrong : ∀ x y, m * ‖x-y‖^2 ≤ ⟪A x-A y,x-y⟫_ℝ)
    (hlip : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖) (x y : H) :
    ‖(x-γ • A x)-(y-γ • A y)‖ ≤ rate m L γ * ‖x-y‖ := by
  have he : (x-γ • A x)-(y-γ • A y) = (x-y)-γ • (A x-A y) := by module
  rw [he]
  have hl := hlip x y
  have hm := hstrong x y
  have hsq : ‖A x-A y‖^2 ≤ L^2*‖x-y‖^2 := by
    nlinarith [norm_nonneg (A x-A y), norm_nonneg (x-y)]
  have hinner : ⟪x-y,A x-A y⟫_ℝ = ⟪A x-A y,x-y⟫_ℝ := real_inner_comm _ _
  have hn := norm_sub_sq_real (x-y) (γ • (A x-A y))
  rw [norm_smul, Real.norm_of_nonneg hγ.le, real_inner_smul_right, hinner] at hn
  have h1 : ‖(x-y)-γ • (A x-A y)‖^2 ≤
      (1-2*γ*m+γ^2*L^2)*‖x-y‖^2 := by
    nlinarith [mul_nonneg (sq_nonneg γ) (sub_nonneg.2 hsq),
      mul_nonneg hγ.le (sub_nonneg.2 hm)]
  have hrate : 1-2*γ*m+γ^2*L^2 ≤ (rate m L γ)^2 := by
    by_cases hs : 0 ≤ 1-2*γ*m+γ^2*L^2
    · exact (Real.sq_sqrt hs).ge
    · exact (le_of_not_ge hs).trans (sq_nonneg _)
  have h2 := mul_le_mul_of_nonneg_right hrate (sq_nonneg ‖x-y‖)
  have hnonneg : 0 ≤ rate m L γ * ‖x-y‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg ((x-y)-γ • (A x-A y))]

theorem step_bound (A : H → H) {m L γ : ℝ}
    (hL : 0 < L) (hγ : 0 < γ)
    (hstrong : ∀ x y, m * ‖x-y‖^2 ≤ ⟪A x-A y,x-y⟫_ℝ)
    (hlip : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖) (x y : H) :
    ‖step K hne hcl hco A γ x-step K hne hcl hco A γ y‖ ≤
      rate m L γ * ‖x-y‖ :=
  (project_nonexpansive K hne hcl hco _ _).trans (forward_step_bound A hL hγ hstrong hlip x y)

theorem step_contracting (A : H → H) {m L γ : ℝ}
    (hm : 0 < m) (hL : 0 < L) (hγ : 0 < γ) (hγu : γ < 2*m/L^2)
    (hstrong : ∀ x y, m * ‖x-y‖^2 ≤ ⟪A x-A y,x-y⟫_ℝ)
    (hlip : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖) :
    ContractingWith ⟨rate m L γ, (rate_range hm hL hγ hγu).1⟩
      (step K hne hcl hco A γ) := by
  refine ⟨(rate_range hm hL hγ hγu).2, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa only [dist_eq_norm] using step_bound K hne hcl hco A hL hγ hstrong hlip x y

/-- Full construction by Banach's theorem, exact VI uniqueness and geometric
error bound for every initial point, with the task's explicit q. -/
theorem complete_vi_iteration (A : H → H) {m L γ : ℝ}
    (hm : 0 < m) (hL : 0 < L) (hγ : 0 < γ) (hγu : γ < 2*m/L^2)
    (hstrong : ∀ x y, m * ‖x-y‖^2 ≤ ⟪A x-A y,x-y⟫_ℝ)
    (hlip : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖) :
    ∃ p : H, vi K A p ∧ (∀ z, vi K A z → z=p) ∧
      0 ≤ rate m L γ ∧ rate m L γ < 1 ∧
      ∀ x n, ‖(step K hne hcl hco A γ)^[n] x-p‖ ≤
        (rate m L γ)^n * ‖x-p‖ := by
  let T := step K hne hcl hco A γ
  have hc := step_contracting K hne hcl hco A hm hL hγ hγu hstrong hlip
  let p := hc.fixedPoint T
  have hp : IsFixedPt T p := hc.fixedPoint_isFixedPt
  refine ⟨p,(fixed_iff_vi K hne hcl hco A hγ p).1 hp, ?_,
    (rate_range hm hL hγ hγu).1,(rate_range hm hL hγ hγu).2, ?_⟩
  · intro z hz
    exact hc.fixedPoint_unique ((fixed_iff_vi K hne hcl hco A hγ z).2 hz)
  · intro x n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hb := step_bound K hne hcl hco A hL hγ hstrong hlip (T^[n] x) p
      change T p = p at hp
      change ‖T (T^[n] x)-p‖ ≤ _
      change ‖T (T^[n] x)-T p‖ ≤ _ at hb
      rw [hp] at hb
      have hz := mul_le_mul_of_nonneg_left ih (rate_range hm hL hγ hγu).1
      calc
        ‖T (T^[n] x)-p‖ ≤ rate m L γ * ‖T^[n] x-p‖ := hb
        _ ≤ rate m L γ * ((rate m L γ)^n * ‖x-p‖) := hz
        _ = (rate m L γ)^(n+1) * ‖x-p‖ := by ring

theorem vi_iteration_converges (A : H → H) {m L γ : ℝ}
    (hm : 0 < m) (hL : 0 < L) (hγ : 0 < γ) (hγu : γ < 2*m/L^2)
    (hstrong : ∀ x y, m * ‖x-y‖^2 ≤ ⟪A x-A y,x-y⟫_ℝ)
    (hlip : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖) (x : H) :
    ∃ p : H, vi K A p ∧ Tendsto (fun n => (step K hne hcl hco A γ)^[n] x) atTop (𝓝 p) := by
  have hc := step_contracting K hne hcl hco A hm hL hγ hγu hstrong hlip
  exact ⟨hc.fixedPoint _, (fixed_iff_vi K hne hcl hco A hγ _).1 hc.fixedPoint_isFixedPt,
    hc.tendsto_iterate_fixedPoint x⟩

/-- The actual projection onto the half-line, identifying the convex counterexample. -/
theorem positive_ray_project (x : ℝ) :
    project (Set.Ici 0) ⟨0,by simp⟩ isClosed_Ici (convex_Ici 0) x = max x 0 := by
  apply (projection_variational_iff _ _ _ _ _ _).2
  refine ⟨show 0 ≤ max x 0 from le_max_right _ _, ?_⟩
  intro z hz
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp only [max_eq_right hx', sub_zero]
    change z*x ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos hz hx'

theorem positive_ray_not_midpoint_affine :
    max (((-1:ℝ)+1)/2) 0 ≠ (max (-1:ℝ) 0 + max (1:ℝ) 0)/2 := by norm_num

theorem positive_ray_finitely_feasible (F : Finset Unit) :
    ∃ z ∈ finite_meet (fun _ : Unit => Set.Ici (0:ℝ)) F, ‖z‖ ≤ (0:ℝ) := by
  exact ⟨0, by simp [finite_meet], by simp⟩

theorem positive_ray_global (x : ℝ) :
    global_project (fun _ : Unit => Set.Ici (0:ℝ)) (fun _ => isClosed_Ici)
      (fun _ => convex_Ici 0) 0 positive_ray_finitely_feasible x = max x 0 := by
  simpa only [global_project, iInter_const] using positive_ray_project x

end MathGauge.VariationalIteration
