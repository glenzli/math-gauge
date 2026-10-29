import SubspaceRecovery
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
namespace MathGauge.RecordBidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finitePairing (F : FinitePart E) : F.val →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun φ := φ.val.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- On finite-dimensional F all algebraic functionals are continuous, so this
is the exact q_F:E->F* in the task, with no norm constraint encoded in q_F. -/
def finiteObservation (F : FinitePart E) : E →ₗ[ℝ] F.val →ₗ[ℝ] ℝ :=
  (finitePairing F).flip

theorem finiteObservation_apply (F : FinitePart E) (x : E) (φ : F.val) :
    finiteObservation F x φ = φ.val x := rfl

theorem finiteObservation_surjective (F : FinitePart E) :
    Function.Surjective (finiteObservation F) := by
  apply LinearMap.flip_surjective_iff₁.mpr
  intro φ ψ h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun h x

theorem finite_kernel_annihilator (F : FinitePart E) (φ : Dual E)
    (hφ : annihilates (finiteObservation F).ker φ) : φ ∈ F.val := by
  have hm : φ.toLinearMap ∈ ((finiteObservation F).ker).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).mpr hφ
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hm
  obtain ⟨ψ,hψ⟩ := hm
  have he : ψ.val = φ := by
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun hψ x
  exact he ▸ ψ.property

/-- A proof of the quotient-norm estimate; no minimum-norm representative
is assumed and the C bound is the bound supplied for this particular record. -/
theorem finiteMatching_quotient_bound (F : FinitePart E) (r : Record E)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (G : FinitePart E) (φ : G.val), ‖r.value G φ‖ ≤ C*‖φ‖)
    (x : E) (hx : finiteObservation F x = r.value F) :
    ‖quotientMap (finiteObservation F).ker x‖ ≤ C := by
  rw [quotient_norm_distance]
  obtain ⟨φ,hφ,hφn,hval⟩ := exists_norming_annihilator (finiteObservation F).ker x
  let ψ : F.val := ⟨φ,finite_kernel_annihilator F φ hφ⟩
  have hxφ : φ x = r.value F ψ := LinearMap.congr_fun hx ψ
  have hnorm : ‖φ x‖ ≤ C := by
    rw [hxφ]
    exact (hb F ψ).trans (by simpa using mul_le_mul_of_nonneg_left hφn hC)
  rw [← hval]
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)

theorem finite_exact_matching (r : Record E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (F : FinitePart E) (φ : F.val), ‖r.value F φ‖ ≤ C*‖φ‖)
    (F : FinitePart E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, finiteObservation F x = r.value F ∧ ‖x‖ ≤ C+ε := by
  obtain ⟨x₀,hx₀⟩ := finiteObservation_surjective F (r.value F)
  let K := (finiteObservation F).ker
  obtain ⟨x,hx,hn⟩ := Submodule.Quotient.norm_mk_lt
    (Submodule.Quotient.mk x₀ : E ⧸ K) hε
  refine ⟨x,?_,?_⟩
  · have hk : x-x₀ ∈ K := (Submodule.Quotient.eq K).mp hx
    have he : finiteObservation F x = finiteObservation F x₀ := by
      simpa only [K,LinearMap.mem_ker,map_sub,sub_eq_zero] using hk
    exact he.trans hx₀
  · have hbq : ‖(Submodule.Quotient.mk x₀ : E ⧸ K)‖ ≤ C :=
      finiteMatching_quotient_bound F r hC hb x₀ hx₀
    linarith

end MathGauge.RecordBidual
