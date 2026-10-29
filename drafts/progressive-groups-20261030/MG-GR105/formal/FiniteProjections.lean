import ObservationRecovery
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
open Topology Filter
namespace MathGauge.GR105
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- This works for any nested closed subspaces, not just finite-dimensional ones. -/
theorem nested_projection_difference_bound (U Z : Submodule ℝ H)
    [U.HasOrthogonalProjection] [Z.HasOrthogonalProjection] (hUZ : U ≤ Z) :
    ‖Z.starProjection - U.starProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (Z.starProjection - U.starProjection) (by norm_num)
  intro x
  have hc : U.starProjection (Z.starProjection x) = U.starProjection x :=
    DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le hUZ) x
  have he : (Z.starProjection - U.starProjection) x = Uᗮ.starProjection (Z.starProjection x) := by
    simp only [ContinuousLinearMap.sub_apply, Submodule.starProjection_orthogonal_val, hc]
  rw [he, one_mul]
  exact (Uᗮ.norm_starProjection_apply_le _).trans (Z.norm_starProjection_apply_le x)

theorem nested_projection_difference_norm (U Z : Submodule ℝ H)
    [U.HasOrthogonalProjection] [Z.HasOrthogonalProjection] (hUZ : U ≤ Z) (hne : U ≠ Z) :
    ‖Z.starProjection - U.starProjection‖ = 1 := by
  apply le_antisymm (nested_projection_difference_bound U Z hUZ)
  obtain ⟨x, hxZ, hxU⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hUZ hne)
  let z := x - U.starProjection x
  have hz0 : z ≠ 0 := by
    intro hz
    have : U.starProjection x = x := (sub_eq_zero.mp hz).symm
    exact hxU (U.starProjection_eq_self_iff.mp this)
  have hzZ : z ∈ Z := Z.sub_mem hxZ (hUZ (Submodule.starProjection_apply_mem _ _))
  have hzU : z ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have he : (Z.starProjection - U.starProjection) z = z := by
    rw [ContinuousLinearMap.sub_apply, Z.starProjection_eq_self_iff.mpr hzZ,
      U.starProjection_apply_eq_zero_iff.mpr hzU, sub_zero]
  have hb := (Z.starProjection - U.starProjection).le_opNorm z
  rw [he] at hb
  nlinarith [norm_pos_iff.mpr hz0]

/-- The given dense union is expressed as equality of its closed linear span. -/
theorem finite_projection_strong_limit (U : ℕ → Submodule ℝ H)
    [∀ n, FiniteDimensional ℝ (U n)] (Z : Submodule ℝ H)
    [Z.HasOrthogonalProjection] (hU : Monotone U)
    (hdense : (⨆ n, U n).topologicalClosure = Z) (y : H) :
    Tendsto (fun n => (U n).starProjection y) atTop (𝓝 (Z.starProjection y)) := by
  have he := Submodule.starProjection_tendsto_closure_iSup U hU y
  simpa only [hdense] using he

/-- In a monotone finite-dimensional exhaustion operator norm convergence occurs
    exactly when one stage already equals the entire closed observation space. -/
theorem finite_projection_norm_iff (U : ℕ → Submodule ℝ H)
    [∀ n, FiniteDimensional ℝ (U n)] (Z : Submodule ℝ H)
    [Z.HasOrthogonalProjection] (hU : Monotone U) (hUZ : ∀ n, U n ≤ Z) :
    Tendsto (fun n => ‖(U n).starProjection - Z.starProjection‖) atTop (𝓝 0) ↔
      ∃ N, U N = Z := by
  constructor
  · intro h
    have he : ∀ᶠ n in atTop, ‖(U n).starProjection - Z.starProjection‖ < (1:ℝ) :=
      h.eventually (gt_mem_nhds (by norm_num))
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    refine ⟨N, ?_⟩
    by_contra hn
    have hg := nested_projection_difference_norm (U N) Z (hUZ N) hn
    have hh := hN N le_rfl
    rw [norm_sub_rev, hg] at hh
    exact lt_irrefl _ hh
  · rintro ⟨N, hN⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hEq : U n = Z := le_antisymm (hUZ n) (by rw [← hN]; exact hU hn)
    simp [hEq]

/-- A uniformly nonzero gap gives the negative half without confusing pointwise
    convergence with a uniform convergence stage. -/
theorem infinite_exhaustion_gap (U : ℕ → Submodule ℝ H)
    [∀ n, FiniteDimensional ℝ (U n)] (Z : Submodule ℝ H)
    [Z.HasOrthogonalProjection] (hUZ : ∀ n, U n ≤ Z) (hinfinite : ¬ FiniteDimensional ℝ Z) :
    ∀ n, ‖(U n).starProjection - Z.starProjection‖ = 1 := by
  intro n
  rw [norm_sub_rev]
  apply nested_projection_difference_norm (U n) Z (hUZ n)
  intro h
  apply hinfinite
  rw [← h]
  infer_instance
end MathGauge.GR105
