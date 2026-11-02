import ErgodicOperators
import Mathlib.Analysis.Normed.Group.Quotient

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators

namespace MathGauge.ErgodicRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} (l : Filter ι) (F : ι → E →L[ℝ] E)

def vanishing : Submodule ℝ E where
  carrier := {x | Tendsto (fun i => F i x) l (𝓝 0)}
  zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (0:E)) l (𝓝 0))
  add_mem' := by
    intro x y hx hy
    simpa using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa using hx.const_smul c

theorem vanishing_closed {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ i, ‖F i‖ ≤ K) :
    IsClosed (vanishing l F : Set E) := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hδ : 0 < ε / (2*(K+1)) := by positivity
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hδ
  have hy' := (Metric.tendsto_nhds.1 hy) (ε/2) (by positivity)
  filter_upwards [hy'] with i hi
  rw [dist_zero_right] at hi ⊢
  have hdist : K*‖x-y‖ < ε/2 := by
    rw [dist_eq_norm] at hxy
    have hn : 0 ≤ ‖x-y‖ := norm_nonneg _
    have hh := (mul_lt_mul_of_pos_left hxy (show 0 < K+1 by positivity))
    have he : (K+1)*(ε/(2*(K+1))) = ε/2 := by field_simp
    rw [he] at hh
    nlinarith
  have hb : ‖F i (x-y)‖ ≤ K*‖x-y‖ :=
    ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
  have he : F i x = F i (x-y) + F i y := by rw [map_sub]; abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem apply_tendsto_zero {A : ι → E →L[ℝ] E}
    (h : Tendsto A l (𝓝 0)) (x : E) : Tendsto (fun i => A i x) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) (fun i => (A i).le_opNorm x)
  simpa using h.norm.mul_const ‖x‖

def fixed (T S : E →L[ℝ] E) : Submodule ℝ E :=
  LinearMap.ker (1-T).toLinearMap ⊓ LinearMap.ker (1-S).toLinearMap

def differences (T S : E →L[ℝ] E) : Submodule ℝ E :=
  (LinearMap.range (1-T).toLinearMap ⊔ LinearMap.range (1-S).toLinearMap).topologicalClosure

theorem differences_closed (T S : E →L[ℝ] E) : IsClosed (differences T S : Set E) :=
  Submodule.isClosed_topologicalClosure _

theorem differences_vanish (T S : E →L[ℝ] E) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ i, ‖F i‖ ≤ K)
    (hT : Tendsto (fun i => F i * (1-T)) l (𝓝 0))
    (hS : Tendsto (fun i => F i * (1-S)) l (𝓝 0)) :
    differences T S ≤ vanishing l F := by
  apply Submodule.topologicalClosure_minimal
  · apply sup_le
    · rintro y ⟨x, rfl⟩
      exact apply_tendsto_zero l hT x
    · rintro y ⟨x, rfl⟩
      exact apply_tendsto_zero l hS x
  · exact vanishing_closed l F hK0 hK

theorem limit_is_fixed [NeBot l] (T S : E →L[ℝ] E)
    (hcommT : ∀ i, Commute (F i) T) (hcommS : ∀ i, Commute (F i) S)
    (hT : Tendsto (fun i => F i * (1-T)) l (𝓝 0))
    (hS : Tendsto (fun i => F i * (1-S)) l (𝓝 0))
    {x z : E} (hz : Tendsto (fun i => F i x) l (𝓝 z)) : z ∈ fixed T S := by
  have hone (U : E →L[ℝ] E) (hc : ∀ i, Commute (F i) U)
      (hu : Tendsto (fun i => F i * (1-U)) l (𝓝 0)) : (1-U) z = 0 := by
    have hleft := (1-U).continuous.tendsto z |>.comp hz
    have hright := apply_tendsto_zero l hu x
    have he : (fun i => (1-U) (F i x)) = (fun i => (F i * (1-U)) x) := by
      funext i
      exact congrArg (fun A : E →L[ℝ] E => A x) (((Commute.one_right (F i)).sub_right (hc i)).eq.symm)
    change Tendsto (fun i => (1-U) (F i x)) l (𝓝 ((1-U) z)) at hleft
    rw [he] at hleft
    exact tendsto_nhds_unique hleft hright
  exact ⟨hone T hcommT hT, hone S hcommS hS⟩

theorem convergence_criterion [NeBot l] (T S : E →L[ℝ] E) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ i, ‖F i‖ ≤ K)
    (hcommT : ∀ i, Commute (F i) T) (hcommS : ∀ i, Commute (F i) S)
    (hT : Tendsto (fun i => F i * (1-T)) l (𝓝 0))
    (hS : Tendsto (fun i => F i * (1-S)) l (𝓝 0))
    (hfix : ∀ z ∈ fixed T S, ∀ i, F i z = z)
    (hrecord : ∀ x i, x-F i x ∈ differences T S) (x z : E) :
    Tendsto (fun i => F i x) l (𝓝 z) ↔ z ∈ fixed T S ∧ x-z ∈ differences T S := by
  constructor
  · intro hz
    refine ⟨limit_is_fixed l F T S hcommT hcommS hT hS hz, ?_⟩
    exact (differences_closed T S).mem_of_tendsto (tendsto_const_nhds.sub hz)
      (Eventually.of_forall (hrecord x))
  · rintro ⟨hz, hy⟩
    have hv := differences_vanish l F T S hK0 hK hT hS hy
    have he : (fun i => F i x) = (fun i => z + F i (x-z)) := by
      funext i
      rw [map_sub, hfix z hz i]
      abel
    rw [he]
    simpa using tendsto_const_nhds.add hv

theorem limit_bound [NeBot l] {K : ℝ} (hK : ∀ i, ‖F i‖ ≤ K)
    {x z : E} (hz : Tendsto (fun i => F i x) l (𝓝 z)) : ‖z‖ ≤ K*‖x‖ := by
  apply le_of_tendsto hz.norm
  exact Eventually.of_forall fun i => ((F i).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))

end MathGauge.ErgodicRecovery
