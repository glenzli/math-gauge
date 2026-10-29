import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

noncomputable section
open Filter Topology InnerProductSpace
namespace MathGauge.FiniteConstraints
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The metric projection is selected from the actual Hilbert projection theorem. -/
def project (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K) (hco : Convex ℝ K)
    (x : H) : H :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hco x)

theorem project_spec (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hco : Convex ℝ K) (x : H) :
    project K hne hcl hco x ∈ K ∧
    ‖x - project K hne hcl hco x‖ = ⨅ z : K, ‖x - z‖ :=
  Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hco x)

theorem project_min (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hco : Convex ℝ K) (x z : H) (hz : z ∈ K) :
    ‖x - project K hne hcl hco x‖ ≤ ‖x - z‖ := by
  rw [(project_spec K hne hcl hco x).2]
  exact ciInf_le (f := fun w : K => ‖x - w‖)
    ⟨0, Set.forall_mem_range.2 (fun _ => norm_nonneg _)⟩ ⟨z,hz⟩

theorem project_variation (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hco : Convex ℝ K) (x z : H) (hz : z ∈ K) :
    ⟪x - project K hne hcl hco x, z - project K hne hcl hco x⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hco (project_spec K hne hcl hco x).1).1
    (project_spec K hne hcl hco x).2 z hz

theorem project_energy (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hco : Convex ℝ K) (x z : H) (hz : z ∈ K) :
    ‖project K hne hcl hco x - z‖ ^ 2 ≤
      ‖x-z‖ ^ 2 - ‖x-project K hne hcl hco x‖ ^ 2 := by
  have h := project_variation K hne hcl hco x z hz
  have he := norm_sub_sq_real (x-project K hne hcl hco x)
    (z-project K hne hcl hco x)
  rw [sub_sub_sub_cancel_right, norm_sub_rev z] at he
  nlinarith

theorem project_unique (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hco : Convex ℝ K) (x z : H) (hz : z ∈ K)
    (hm : ∀ w ∈ K, ‖x-z‖ ≤ ‖x-w‖) : z = project K hne hcl hco x := by
  have h1 := project_energy K hne hcl hco x z hz
  have h2 := hm _ (project_spec K hne hcl hco x).1
  have hn : ‖project K hne hcl hco x-z‖ = 0 := by
    nlinarith [norm_nonneg (project K hne hcl hco x-z), norm_nonneg (x-z),
      norm_nonneg (x-project K hne hcl hco x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem project_firm (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hco : Convex ℝ K) (x y : H) :
    ‖project K hne hcl hco x-project K hne hcl hco y‖ ^ 2 ≤
      ⟪x-y,project K hne hcl hco x-project K hne hcl hco y⟫_ℝ := by
  let u := project K hne hcl hco x
  let v := project K hne hcl hco y
  have hx := project_variation K hne hcl hco x v (project_spec K hne hcl hco y).1
  have hy := project_variation K hne hcl hco y u (project_spec K hne hcl hco x).1
  change ⟪x-u,v-u⟫_ℝ ≤ 0 at hx
  change ⟪y-v,u-v⟫_ℝ ≤ 0 at hy
  have he : ⟪x-u,v-u⟫_ℝ + ⟪y-v,u-v⟫_ℝ =
      ‖u-v‖^2 - ⟪x-y,u-v⟫_ℝ := by
    rw [@norm_sq_eq_re_inner ℝ]
    simp only [RCLike.re_to_real, inner_sub_left, inner_sub_right]
    ring
  change ‖u-v‖^2 ≤ ⟪x-y,u-v⟫_ℝ
  linarith

theorem project_nonexpansive (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hco : Convex ℝ K) (x y : H) :
    ‖project K hne hcl hco x-project K hne hcl hco y‖ ≤ ‖x-y‖ := by
  have h1 := project_firm K hne hcl hco x y
  have h2 := real_inner_le_norm (x-y)
    (project K hne hcl hco x-project K hne hcl hco y)
  nlinarith [norm_nonneg (x-y),
    norm_nonneg (project K hne hcl hco x-project K hne hcl hco y)]

end MathGauge.FiniteConstraints
