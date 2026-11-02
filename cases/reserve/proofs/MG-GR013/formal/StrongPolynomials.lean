import PolynomialNorms
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Topology
namespace MathGauge.StrongPolynomials
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

def poly (a : ℕ → ℂ) (d : ℕ) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  ∑ k∈Finset.range (d+1),a k • T^k

theorem norm_upper (a : ℕ → ℂ) (d : ℕ) (T : E →L[ℂ] E) (hT : ‖T‖≤1) :
    ‖poly a d T‖≤∑ k∈Finset.range (d+1),‖a k‖ := by
  nontriviality E using (show 0≤∑ k∈Finset.range (d+1),‖a k‖ from Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  unfold poly
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  have hp : ‖T^k‖≤1 := (norm_pow_le T k).trans (by simpa using pow_le_pow_left₀ (norm_nonneg T) hT k)
  exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg (a k)))

theorem moving_apply (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hT : ∀ n,‖T n‖≤1) (hs : ∀ x,Tendsto (fun n => T n x) atTop (𝓝 (A x)))
    (x : ℕ → E) (y : E) (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => T n (x n)) atTop (𝓝 (A y)) := by
  have hsmall : Tendsto (fun n => T n (x n-y)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa using (hx.sub_const y).norm)
    exact (T n).le_opNorm _ |>.trans (by
      simpa using mul_le_mul_of_nonneg_right (hT n) (norm_nonneg (x n-y)))
  have he : (fun n => T n (x n))=(fun n => T n (x n-y)+T n y) := by
    funext n
    rw [← map_add,sub_add_cancel]
  rw [he]
  simpa using hsmall.add (hs y)

theorem powers_strong (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hT : ∀ n,‖T n‖≤1) (hs : ∀ x,Tendsto (fun n => T n x) atTop (𝓝 (A x)))
    (m : ℕ) (x : E) : Tendsto (fun n => ((T n)^m) x) atTop (𝓝 ((A^m) x)) := by
  induction m with
  | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  | succ m ih =>
    simpa only [pow_succ',ContinuousLinearMap.mul_apply] using
      moving_apply T A hT hs (fun n => ((T n)^m) x) ((A^m) x) ih

theorem polynomial_strong (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hT : ∀ n,‖T n‖≤1) (hs : ∀ x,Tendsto (fun n => T n x) atTop (𝓝 (A x)))
    (a : ℕ → ℂ) (d : ℕ) (x : E) :
    Tendsto (fun n => poly a d (T n) x) atTop (𝓝 (poly a d A x)) := by
  simp only [poly,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
  exact tendsto_finset_sum _ (fun k hk => (powers_strong T A hT hs k x).const_smul (a k))

/-- Operator norm is lower semicontinuous for strong convergence on a
uniformly norm-bounded sequence. The bound is derived below for polynomials. -/
theorem norm_le_liminf (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hs : ∀ x,Tendsto (fun n => T n x) atTop (𝓝 (A x)))
    (C : ℝ) (hC : ∀ n,‖T n‖≤C) : ‖A‖≤liminf (fun n => ‖T n‖) atTop := by
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖T n‖) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hC)
  have hl : atTop.IsBoundedUnder (· ≥ ·) (fun n => ‖T n‖) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => norm_nonneg (T n)))
  have hnonneg : 0≤liminf (fun n => ‖T n‖) atTop :=
    le_liminf_of_le hb.isCoboundedUnder_ge (Eventually.of_forall (fun n => norm_nonneg _))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hnonneg
  intro x hx
  rw [le_liminf_iff hb.isCoboundedUnder_ge hl]
  intro y hy
  have he := ((hs x).norm).eventually (eventually_gt_nhds hy)
  filter_upwards [he] with n hn
  exact hn.trans_le (by simpa [hx] using (T n).le_opNorm x)

theorem polynomial_norm_liminf (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hT : ∀ n,‖T n‖≤1) (hs : ∀ x,Tendsto (fun n => T n x) atTop (𝓝 (A x)))
    (a : ℕ → ℂ) (d : ℕ) :
    ‖poly a d A‖≤liminf (fun n => ‖poly a d (T n)‖) atTop :=
  norm_le_liminf _ _ (polynomial_strong T A hT hs a d) _ (fun n => norm_upper a d (T n) (hT n))

/-- This finite-dimensional equivalence is exactly the operator norm topology,
not the pointwise topology on an infinite-dimensional domain. -/
theorem finite_dimensional_norm_convergence [FiniteDimensional ℂ E]
    (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hs : ∀ x,Tendsto (fun n => T n x) atTop (𝓝 (A x))) : Tendsto T atTop (𝓝 A) := by
  let d := Module.finrank ℂ E
  let e₁ : E ≃L[ℂ] Fin d → ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  let e₂ : (E →L[ℂ] E) ≃L[ℂ] Fin d → E :=
    (e₁.arrowCongr (1 : E ≃L[ℂ] E)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have he : Tendsto (fun n => e₂ (T n)) atTop (𝓝 (e₂ A)) :=
    tendsto_pi_nhds.mpr (fun i => hs _)
  have hh := e₂.symm.continuous.tendsto (e₂ A) |>.comp he
  simpa only [Function.comp_def,e₂.symm_apply_apply] using hh

theorem polynomial_norm_convergence (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (h : Tendsto T atTop (𝓝 A)) (a : ℕ → ℂ) (d : ℕ) :
    Tendsto (fun n => ‖poly a d (T n)-poly a d A‖) atTop (𝓝 0) := by
  have hp : Tendsto (fun n => poly a d (T n)) atTop (𝓝 (poly a d A)) := by
    unfold poly
    exact tendsto_finset_sum _ (fun k hk => (h.pow k).const_smul (a k))
  simpa using (hp.sub_const (poly a d A)).norm

end MathGauge.StrongPolynomials
