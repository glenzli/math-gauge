import ShiftOperators
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped ZeroAtInfty
namespace MathGauge.SpectralApproximation

theorem shift_pow_apply (m : ℕ) (x : E) (k : ℕ) :
    (shift^m) x k = if m≤k then x (k-m) else 0 := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change shift ((shift^m) x) k = _
    cases k with
    | zero => simp
    | succ j =>
      rw [shift_apply_succ, ih]
      simp only [Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub]

theorem truncated_pow_succ (n m : ℕ) (x : E) (k : ℕ) :
    (truncated n^(m+1)) x k = if m+1≤k ∧ k<n then x (k-(m+1)) else 0 := by
  induction m generalizing k with
  | zero =>
    rw [show 0+1=1 by omega,pow_one]
    cases k with
    | zero => simp
    | succ j => simp
  | succ m ih =>
    rw [pow_succ']
    change truncated n ((truncated n^(m+1)) x) k = _
    cases k with
    | zero => simp
    | succ j =>
      rw [truncated_apply_succ,ih]
      by_cases hj : j+1<n
      · simp only [hj,if_true]
        by_cases hm : m+1≤j
        · simp [hm,show j<n by omega,show m+1+1≤j+1 by omega]
        · simp [hm,show ¬m+1+1≤j+1 by omega]
      · simp [hj]

theorem truncated_outside (n : ℕ) (x : E) (k : ℕ) (hk : n≤k) : truncated n x k=0 := by
  cases k with
  | zero => rfl
  | succ j => simp [show ¬j+1<n by omega]

theorem truncated_nilpotent (n : ℕ) : IsNilpotent (truncated n) := by
  refine ⟨n+1,?_⟩
  ext x k
  rw [truncated_pow_succ]
  rw [if_neg (by omega)]
  rfl

/-- The range is finite-dimensional via its actual finite coordinate map. -/
theorem truncated_finite_rank (n : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (truncated n).toLinearMap) := by
  let R := LinearMap.range (truncated n).toLinearMap
  let f : R →ₗ[ℂ] (Fin n → ℂ) := {
    toFun := fun y i => y.val i.val
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective (V₂ := Fin n → ℂ) f
  intro y z hyz
  apply Subtype.ext
  ext k
  by_cases hk : k<n
  · exact congrFun hyz ⟨k,hk⟩
  · obtain ⟨u,hu⟩ := y.property
    obtain ⟨v,hv⟩ := z.property
    have hy : y.val k=0 := by
      rw [← hu]
      exact truncated_outside n u k (Nat.le_of_not_gt hk)
    have hz : z.val k=0 := by
      rw [← hv]
      exact truncated_outside n v k (Nat.le_of_not_gt hk)
    exact hy.trans hz.symm

def basis_vector (k : ℕ) : E where
  toFun j := if j=k then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (k+1)] with j hj
    simp [show j≠k by omega]

@[simp] theorem basis_apply (j k : ℕ) : basis_vector k j=if j=k then 1 else 0 := rfl

theorem basis_ne_zero (k : ℕ) : basis_vector k≠0 := by
  intro h
  have he := congrArg (fun x : E => x k) h
  simpa using he

instance : Nontrivial E := ⟨⟨basis_vector 0,0,basis_ne_zero 0⟩⟩

theorem truncated_basis_kernel (n : ℕ) : truncated n (basis_vector n)=0 := by
  ext k
  cases k with
  | zero => simp
  | succ j =>
    simp only [truncated_apply_succ,basis_apply]
    by_cases hj : j=n
    · subst j; simp
    · simp [hj]

theorem truncated_zero_spectral (n : ℕ) : (0 : ℂ)∈spectrum ℂ (truncated n) := by
  rw [spectrum.mem_iff]
  intro h
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.1 h).1
  have he : (algebraMap ℂ (E→L[ℂ]E) 0-truncated n) (basis_vector n)=
      (algebraMap ℂ (E→L[ℂ]E) 0-truncated n) 0 := by
    simp [truncated_basis_kernel]
  exact basis_ne_zero n (hi he)

theorem clm_smul_pow (c : ℂ) (T : E→L[ℂ]E) (k : ℕ) :
    (c • T)^k = c^k • T^k := by
  induction k with
  | zero =>
    ext x j
    change x j = (1:ℂ)*x j
    simp
  | succ k ih =>
    rw [pow_succ',ih,pow_succ']
    ext x
    simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply,map_smul,smul_smul,
      pow_succ']
    rw [mul_comm]

theorem truncated_nonzero_resolvent (n : ℕ) {μ : ℂ} (hμ : μ≠0) :
    μ∉spectrum ℂ (truncated n) := by
  rw [spectrum.notMem_iff]
  have hnil : IsNilpotent (μ⁻¹ • truncated n) := by
    obtain ⟨k,hk⟩ := truncated_nilpotent n
    refine ⟨k,?_⟩
    rw [clm_smul_pow,hk]
    ext x j
    change (μ⁻¹^k)*(0:ℂ)=0
    simp
  have hu : IsUnit (1-μ⁻¹ • truncated n) :=
    IsNilpotent.isUnit_one_sub (R := E→L[ℂ]E) hnil
  have hs := (isUnit_iff_ne_zero.mpr hμ).map (algebraMap ℂ (E→L[ℂ]E))
  convert hs.mul hu using 1
  ext x
  simp [ContinuousLinearMap.algebraMap_apply,smul_sub,smul_smul,hμ]

theorem truncated_spectrum (n : ℕ) : spectrum ℂ (truncated n)={0} := by
  ext μ
  constructor
  · intro h
    by_contra hn
    exact truncated_nonzero_resolvent n (by simpa using hn) h
  · intro h
    have hμ : μ=0 := h
    subst μ
    exact truncated_zero_spectral n

/-- Invertibility would solve (I-S)x=e₀, forcing a nonvanishing constant sequence. -/
theorem shift_one_spectral : (1 : ℂ)∈spectrum ℂ shift := by
  rw [spectrum.mem_iff]
  intro h
  obtain ⟨x,hx⟩ := (ContinuousLinearMap.isUnit_iff_bijective.1 h).2 (basis_vector 0)
  have h0 : x 0=1 := by
    have he := congrArg (fun y : E => y 0) hx
    simpa using he
  have hstep : ∀ k, x (k+1)=x k := by
    intro k
    have he := congrArg (fun y : E => y (k+1)) hx
    have hh : x (k+1)-x k=0 := by simpa using he
    exact sub_eq_zero.mp hh
  have hall : ∀k, x k=1 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact (hstep k).trans ih
  have hone : Tendsto (fun k => x k) atTop (𝓝 (1 : ℂ)) := by
    simpa only [hall] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1))
  have he : (0 : ℂ)=1 := tendsto_nhds_unique (zero_limit x) hone
  norm_num at he

/-- In particular no finite-model spectral points can approach the spectral point 1. -/
theorem no_spectral_approximation : ¬∃ μ : ℕ→ℂ,
    (∀ n, μ n∈spectrum ℂ (truncated n)) ∧ Tendsto μ atTop (𝓝 1) := by
  rintro ⟨μ,hμ,ht⟩
  have hz : ∀n, μ n=0 := fun n => by simpa [truncated_spectrum] using hμ n
  have ht0 : Tendsto μ atTop (𝓝 (0:ℂ)) := by
    have he : μ = fun _ => 0 := funext hz
    rw [he]
    exact tendsto_const_nhds
  have he : (0:ℂ)=1 := tendsto_nhds_unique ht0 ht
  norm_num at he

end MathGauge.SpectralApproximation
