import TikhonovExistence

noncomputable section
open Topology Filter Set
open scoped InnerProductSpace
namespace MathGauge.GR105
open MathGauge.R105
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem regularized_observations_tendsto (A : E →L[ℝ] H) (y : H) :
    Tendsto (fun lam : ℝ => A (regularized A y lam)) (𝓝[>] 0)
      (𝓝 (predicted A.toLinearMap y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hm : predicted A.toLinearMap y ∈ closure (Set.range A) := predicted_mem A.toLinearMap y
  obtain ⟨w, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.mp hm (ε/2) (by positivity)
  have hb : 0 < ε^2 / (4*(‖x‖^2+1)) := by positivity
  have he : ∀ᶠ lam : ℝ in 𝓝[>] 0, lam < ε^2 / (4*(‖x‖^2+1)) :=
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he] with lam hlam hl
  change 0 < lam at hlam
  have hc := observation_error_comparison A y hlam x
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 4*(‖x‖^2+1))).mp hl
  rw [dist_eq_norm] at hx
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (predicted A.toLinearMap y - A x),
    norm_nonneg (predicted A.toLinearMap y - A (regularized A y lam)), sq_nonneg ‖x‖]

/-- A Hilbert-space argument using the genuine closure of the adjoint range:
    bounded norm plus observation convergence recovers the minimum-norm vector. -/
theorem strong_limit_from_norm_bound {ι : Type*} {l : Filter ι}
    (A : E →L[ℝ] H) (f : ι → E) (z : E) (hz : z ∈ A.kerᗮ)
    (hbound : ∀ᶠ i in l, ‖f i‖ ≤ ‖z‖)
    (hobs : Tendsto (fun i => A (f i)) l (𝓝 (A z))) : Tendsto f l (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε^2 / (8*(‖z‖+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hdense : z ∈ closure (Set.range A.adjoint) := by
    simpa only [A.orthogonal_ker] using hz
  obtain ⟨w, ⟨v, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hdense η hη
  let δ := ε^2 / (4*(‖v‖+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hηeq : η * (8*(‖z‖+1)) = ε^2 := div_mul_cancel₀ _ (by positivity)
  have hδeq : δ * (4*(‖v‖+1)) = ε^2 := div_mul_cancel₀ _ (by positivity)
  have he := Metric.tendsto_nhds.mp hobs δ hδ
  filter_upwards [hbound, he] with i hi hobs_i
  rw [dist_eq_norm] at hv hobs_i ⊢
  have hi2 : ‖f i‖^2 ≤ ‖z‖^2 := by nlinarith [norm_nonneg (f i), norm_nonneg z]
  have hdiff : ‖z-f i‖ ≤ 2*‖z‖ := by
    have hn := norm_sub_le z (f i)
    linarith
  have heq := norm_sub_sq_real (f i) z
  have hinner : ⟪z-f i,z⟫_ℝ = ‖z‖^2 - ⟪f i,z⟫_ℝ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have hsq : ‖f i-z‖^2 ≤ 2*⟪z-f i,z⟫_ℝ := by linarith
  have hsplit : ⟪z-f i,z⟫_ℝ = ⟪z-f i,z-A.adjoint v⟫_ℝ + ⟪A z-A (f i),v⟫_ℝ := by
    rw [inner_sub_right, ← map_sub, ← A.adjoint_inner_right]
    ring
  have hb1 := real_inner_le_norm (z-f i) (z-A.adjoint v)
  have hb2 := real_inner_le_norm (A z-A (f i)) v
  have hb3 : ‖z-f i‖ * ‖z-A.adjoint v‖ ≤ 2*‖z‖*η := by
    calc
      _ ≤ (2*‖z‖) * ‖z-A.adjoint v‖ := mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      _ ≤ (2*‖z‖) * η := mul_le_mul_of_nonneg_left hv.le (by positivity)
  have hb4 : ‖A z-A (f i)‖ * ‖v‖ ≤ δ * ‖v‖ := by
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hobs_i.le (norm_nonneg _)
  nlinarith [norm_nonneg (f i-z)]

def minimumNormRepresentative (A : E →L[ℝ] H) (x : E) : E := A.kerᗮ.starProjection x

theorem minimumNormRepresentative_observation (A : E →L[ℝ] H) (x : E) :
    A (minimumNormRepresentative A x) = A x := by
  rw [minimumNormRepresentative, Submodule.starProjection_orthogonal_val, map_sub]
  have hk : A (A.ker.starProjection x) = 0 := Submodule.starProjection_apply_mem A.ker x
  rw [hk, sub_zero]

theorem minimumNormRepresentative_orthogonal (A : E →L[ℝ] H) (x : E) :
    minimumNormRepresentative A x ∈ A.kerᗮ := Submodule.starProjection_apply_mem _ _

theorem minimumNormRepresentative_minimal (A : E →L[ℝ] H) (x w : E) (hw : A w = A x) :
    ‖minimumNormRepresentative A x‖ ≤ ‖w‖ := by
  have hker : w-x ∈ A.ker := by change A (w-x) = 0; simp [map_sub, hw]
  have hproj : A.kerᗮ.starProjection (w-x) = 0 := by
    apply A.kerᗮ.starProjection_apply_eq_zero_iff.mpr
    exact A.ker.le_orthogonal_orthogonal hker
  have he : minimumNormRepresentative A w = minimumNormRepresentative A x := by
    simpa only [map_sub, sub_eq_zero, minimumNormRepresentative] using hproj
  rw [← he]
  exact A.kerᗮ.norm_starProjection_apply_le w

theorem regularized_tendsto_minimumNorm (A : E →L[ℝ] H) (y : H) (x : E)
    (hx : OriginalMinimizer A.toLinearMap y x) :
    Tendsto (regularized A y) (𝓝[>] 0) (𝓝 (minimumNormRepresentative A x)) := by
  have hx' := (original_minimizer_iff A.toLinearMap y x).mp hx
  have hz : A (minimumNormRepresentative A x) = predicted A.toLinearMap y :=
    (minimumNormRepresentative_observation A x).trans hx'
  apply strong_limit_from_norm_bound A (regularized A y) (minimumNormRepresentative A x)
    (minimumNormRepresentative_orthogonal A x)
  · filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact regularized_norm_le_solution A y hlam _ hz
  · rw [hz]
    exact regularized_observations_tendsto A y

theorem regularized_converges_iff_attained (A : E →L[ℝ] H) (y : H) :
    (∃ x : E, Tendsto (regularized A y) (𝓝[>] 0) (𝓝 x)) ↔
      ∃ x : E, OriginalMinimizer A.toLinearMap y x := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x, (original_minimizer_iff A.toLinearMap y x).mpr ?_⟩
    exact tendsto_nhds_unique (A.continuous.tendsto x |>.comp hx) (regularized_observations_tendsto A y)
  · rintro ⟨x,hx⟩
    exact ⟨minimumNormRepresentative A x, regularized_tendsto_minimumNorm A y x hx⟩

theorem limit_is_minimumNorm_original (A : E →L[ℝ] H) (y : H) (x : E)
    (hx : OriginalMinimizer A.toLinearMap y x) :
    OriginalMinimizer A.toLinearMap y (minimumNormRepresentative A x) ∧
    ∀ w, OriginalMinimizer A.toLinearMap y w → ‖minimumNormRepresentative A x‖ ≤ ‖w‖ := by
  have hx' := (original_minimizer_iff A.toLinearMap y x).mp hx
  constructor
  · exact (original_minimizer_iff A.toLinearMap y _).mpr
      ((minimumNormRepresentative_observation A x).trans hx')
  · intro w hw
    apply minimumNormRepresentative_minimal A x w
    exact ((original_minimizer_iff A.toLinearMap y w).mp hw).trans hx'.symm
end MathGauge.GR105
