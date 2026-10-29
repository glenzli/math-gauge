import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
open Filter Topology
open scoped ENNReal ZeroAtInfty

namespace MathGauge.CompatibleRecords

abbrev B := lp (fun _ : ℕ => ℝ) ∞

/-- The subspace of convergent bounded sequences; the limit is not postulated. -/
def convergent : Submodule ℝ B where
  carrier := {x | ∃ a : ℝ, Tendsto (fun n => x n) atTop (𝓝 a)}
  zero_mem' := ⟨0, tendsto_const_nhds⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a+b, ha.add hb⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c*a, ha.const_mul c⟩

def seq_limit (x : convergent) : ℝ := Classical.choose x.property

theorem tendsto_seq_limit (x : convergent) :
    Tendsto (fun n => x.val n) atTop (𝓝 (seq_limit x)) := Classical.choose_spec x.property

def limit_linear : convergent →ₗ[ℝ] ℝ where
  toFun := seq_limit
  map_add' x y := tendsto_nhds_unique (tendsto_seq_limit (x+y))
    ((tendsto_seq_limit x).add (tendsto_seq_limit y))
  map_smul' c x := tendsto_nhds_unique (tendsto_seq_limit (c • x))
    ((tendsto_seq_limit x).const_mul c)

theorem seq_limit_bound (x : convergent) : ‖seq_limit x‖ ≤ ‖x‖ := by
  apply le_of_tendsto (tendsto_seq_limit x).norm
  exact Eventually.of_forall fun n => lp.norm_apply_le_norm (by simp) x.val n

def limit_clm : convergent →L[ℝ] ℝ := limit_linear.mkContinuous 1 (by
  intro x
  simpa using seq_limit_bound x)

theorem limit_clm_norm_le : ‖limit_clm‖ ≤ 1 := by
  apply limit_clm.opNorm_le_bound (by norm_num)
  intro x
  simpa using seq_limit_bound x

/-- Hahn--Banach constructs, rather than assumes, an extension of the scalar limit. -/
theorem exists_extended_limit : ∃ L : B →L[ℝ] ℝ,
    ‖L‖ ≤ 1 ∧ ∀ (x : B) (a : ℝ), Tendsto (fun n => x n) atTop (𝓝 a) → L x = a := by
  obtain ⟨L, hL, hn⟩ := Real.exists_extension_norm_eq convergent limit_clm
  refine ⟨L, hn ▸ limit_clm_norm_le, ?_⟩
  intro x a ha
  let xc : convergent := ⟨x, a, ha⟩
  have he : L x = seq_limit xc := hL xc
  exact he.trans (tendsto_nhds_unique (tendsto_seq_limit xc) ha)

def extended_limit : B →L[ℝ] ℝ := Classical.choose exists_extended_limit
theorem extended_limit_norm_le : ‖extended_limit‖ ≤ 1 :=
  (Classical.choose_spec exists_extended_limit).1
theorem extended_limit_eq (x : B) (a : ℝ)
    (h : Tendsto (fun n => x n) atTop (𝓝 a)) : extended_limit x = a :=
  (Classical.choose_spec exists_extended_limit).2 x a h

/-- C₀ on the discrete natural numbers is the real Banach space c₀. -/
abbrev E := C₀(ℕ, ℝ)
abbrev Dual := E →L[ℝ] ℝ

local instance dual_group : AddCommGroup Dual := inferInstance

def partial_ones (N : ℕ) : E where
  toFun n := if n < N then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [not_lt.mpr hn]

theorem partial_ones_norm (N : ℕ) : ‖partial_ones N‖ ≤ 1 := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by norm_num)).2
  intro n
  change ‖if n < N then (1 : ℝ) else 0‖ ≤ 1
  split_ifs <;> norm_num

def coordinate (n : ℕ) : Dual :=
  (show E →ₗ[ℝ] ℝ from
    { toFun := fun x => x n
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).mkContinuous 1 (by
        intro x
        simpa using BoundedContinuousFunction.norm_coe_le_norm x.toBCF n)

@[simp] theorem coordinate_apply (n : ℕ) (x : E) : coordinate n x = x n := rfl

/-- All partial-one tests have norm at most one, so dual evaluations give bounded sequences. -/
def test_sequence_linear : Dual →ₗ[ℝ] B where
  toFun φ := ⟨fun N => φ (partial_ones N), memℓp_infty ⟨‖φ‖, by
    rintro a ⟨N, rfl⟩
    exact (φ.le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_left (partial_ones_norm N) (norm_nonneg φ))⟩⟩
  map_add' φ ψ := by ext N; rfl
  map_smul' c φ := by ext N; rfl

theorem test_sequence_bound (φ : Dual) : ‖test_sequence_linear φ‖ ≤ ‖φ‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg φ)
  intro N
  exact (φ.le_opNorm _).trans (by
    simpa using mul_le_mul_of_nonneg_left (partial_ones_norm N) (norm_nonneg φ))

/-- A linear functional on the actual c₀ dual. The next theorem proves its bound. -/
def z : Dual →ₗ[ℝ] ℝ := extended_limit.toLinearMap.comp test_sequence_linear

theorem z_bound (φ : Dual) : ‖z φ‖ ≤ ‖φ‖ := by
  apply (extended_limit.le_opNorm _).trans
  calc
    ‖extended_limit‖ * ‖test_sequence_linear φ‖ ≤ 1 * ‖test_sequence_linear φ‖ :=
      mul_le_mul_of_nonneg_right extended_limit_norm_le (norm_nonneg _)
    _ ≤ ‖φ‖ := by simpa only [one_mul] using test_sequence_bound φ

theorem z_coordinate (n : ℕ) : z (coordinate n) = 1 := by
  apply extended_limit_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (n+1)] with N hN
  change (1 : ℝ) = if n < N then 1 else 0
  simp [show n < N by omega]

def record (F : Submodule ℝ Dual) : F →ₗ[ℝ] ℝ := z.comp F.subtype

theorem record_compatible (F G : Submodule ℝ Dual) (h : F ≤ G) (φ : F) :
    record G (Submodule.inclusion h φ) = record F φ := rfl

theorem record_bound (F : Submodule ℝ Dual) (φ : F) :
    |record F φ| ≤ 1 * ‖φ.val‖ := by
  simpa [record, Real.norm_eq_abs] using z_bound φ.val

/-- The fixed legal record family has no representative in the original c₀ Banach space. -/
theorem no_original_realization : ¬ ∃ x : E,
    ∀ (F : Submodule ℝ Dual), FiniteDimensional ℝ F → ∀ (φ : F), φ.val x = record F φ := by
  rintro ⟨x, hx⟩
  have hc : ∀ n : ℕ, x n = 1 := by
    intro n
    let F : Submodule ℝ Dual := Submodule.span ℝ {coordinate n}
    let φ : F := ⟨coordinate n, Submodule.subset_span (by simp)⟩
    have he := hx F inferInstance φ
    exact he.trans (z_coordinate n)
  have ht : Tendsto (fun n => x n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [cocompact_eq_atTop] using x.zero_at_infty'
  have ht1 : Tendsto (fun n => x n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hc] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique ht ht1
  norm_num at h01

theorem original_space_complete : CompleteSpace E := inferInstance

/-- All task hypotheses and the failure of original-space realization in one statement.
The restrictions are defined for every subspace, so in particular for every finite-dimensional one. -/
theorem counterexample :
    CompleteSpace E ∧
    (∀ (F G : Submodule ℝ Dual) (h : F ≤ G) (φ : F),
      record G (Submodule.inclusion h φ) = record F φ) ∧
    (∀ (F : Submodule ℝ Dual) (φ : F), |record F φ| ≤ 1 * ‖φ.val‖) ∧
    ¬ (∃ x : E, ∀ (F : Submodule ℝ Dual), FiniteDimensional ℝ F →
      ∀ (φ : F), φ.val x = record F φ) :=
  ⟨original_space_complete, record_compatible, record_bound, no_original_realization⟩

end MathGauge.CompatibleRecords
