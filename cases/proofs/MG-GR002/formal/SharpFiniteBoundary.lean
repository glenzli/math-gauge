import FiniteMatching
import RecordInstantiation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000
open Filter Topology
open MathGauge.RecordBidual MathGauge.CompatibleRecords MathGauge.RecordInstantiation
namespace MathGauge.SharpFiniteBoundary

abbrev E := CompatibleRecords.E
local instance dual_normed : NormedAddCommGroup CompatibleRecords.Dual := inferInstance
local instance dual_space : NormedSpace ℝ CompatibleRecords.Dual := inferInstance
local instance dual_norm_smul : NormSMulClass ℝ CompatibleRecords.Dual := NormedSpace.toNormSMulClass

def weight (n : ℕ) : ℝ := (1/2:ℝ)^n * (1/2)

theorem weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity

theorem weight_summable : Summable weight :=
  (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_right _

theorem weight_sum : ∑' n, weight n = 1 := by
  unfold weight
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)]
  norm_num

theorem coordinate_norm_le (n : ℕ) : ‖coordinate n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using BoundedContinuousFunction.norm_coe_le_norm x.toBCF n

theorem weighted_coordinate_bound (n : ℕ) : ‖weight n • coordinate n‖ ≤ weight n := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (weight_pos n)]
  simpa using mul_le_mul_of_nonneg_left (coordinate_norm_le n) (weight_pos n).le

theorem weighted_coordinate_summable : Summable (fun n => weight n • coordinate n) := by
  apply Summable.of_norm_bounded (g := weight) weight_summable
  exact weighted_coordinate_bound

def witness : RecordBidual.Dual E := ∑' n, weight n • coordinate n

theorem witness_norm : ‖witness‖ ≤ 1 := by
  exact tsum_of_norm_bounded (weight_sum ▸ weight_summable.hasSum) weighted_coordinate_bound

theorem witness_apply (x : E) : witness x = ∑' n, weight n * x n := by
  exact (J x).map_tsum weighted_coordinate_summable

theorem witness_values_summable (x : E) : Summable (fun n => weight n * x n) :=
  (J x).summable weighted_coordinate_summable

theorem c0Record_coordinate (n : ℕ) : c0Record.toBidual (coordinate n) = 1 :=
  z_coordinate n

theorem record_witness : c0Record.toBidual witness = 1 := by
  rw [witness,c0Record.toBidual.map_tsum weighted_coordinate_summable]
  simpa only [map_smul,smul_eq_mul,c0Record_coordinate,mul_one] using weight_sum

theorem exists_coordinate_lt_one (x : E) (hx : ‖x‖ ≤ 1) : ∃ n, x n < 1 := by
  by_contra! h
  have he : ∀ n, x n = 1 := by
    intro n
    have hb : ‖x n‖ ≤ 1 := (BoundedContinuousFunction.norm_coe_le_norm x.toBCF n).trans hx
    exact le_antisymm ((le_abs_self _).trans hb) (h n)
  have ht : Tendsto (fun n => x n) atTop (𝓝 (0:ℝ)) := by
    simpa only [cocompact_eq_atTop] using x.zero_at_infty'
  have ht1 : Tendsto (fun n => x n) atTop (𝓝 (1:ℝ)) := by
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  have : (0:ℝ) = 1 := tendsto_nhds_unique ht ht1
  norm_num at this

theorem witness_not_attained (x : E) (hx : ‖x‖ ≤ 1) : witness x < 1 := by
  obtain ⟨n,hn⟩ := exists_coordinate_lt_one x hx
  have hle : ∀ k, weight k * x k ≤ weight k := by
    intro k
    have hk : x k ≤ 1 := (le_abs_self _).trans
      ((BoundedContinuousFunction.norm_coe_le_norm x.toBCF k).trans hx)
    simpa using mul_le_mul_of_nonneg_left hk (weight_pos k).le
  have hlt : weight n * x n < weight n := by
    simpa using mul_lt_mul_of_pos_left hn (weight_pos n)
  rw [witness_apply,← weight_sum]
  exact Summable.tsum_lt_tsum hle hlt (witness_values_summable x) weight_summable

/-- A fixed legal C=1 record on the complete real Banach space c₀ has a
one-dimensional finite observation which admits no exact lift of norm ≤ C. -/
theorem zero_epsilon_fails :
    CompleteSpace E ∧
    (∀ (F : FinitePart E) (φ : F.val), ‖c0Record.value F φ‖ ≤ 1*‖φ‖) ∧
    ¬ ∃ x : E, finiteObservation (line witness) x = c0Record.value (line witness) ∧
      ‖x‖ ≤ 1 := by
  refine ⟨inferInstance,?_,?_⟩
  · intro F φ
    simpa only [Real.norm_eq_abs] using record_bound F.val φ
  · rintro ⟨x,hx,hn⟩
    have he : witness x = c0Record.toBidual witness :=
      LinearMap.congr_fun hx (linePoint witness)
    have hf := witness_not_attained x hn
    rw [he,record_witness] at hf
    exact lt_irrefl _ hf

/-- The same record matches every finite test, with arbitrary positive norm slack,
but there is no single original vector matching the whole directed family. -/
theorem finite_does_not_global :
    (∀ (F : FinitePart E) (ε : ℝ), 0 < ε →
      ∃ x : E, finiteObservation F x = c0Record.value F ∧ ‖x‖ ≤ 1+ε) ∧
    ¬ ∃ x : E, Represents c0Record x := by
  refine ⟨?_,c0Record_no_realization⟩
  intro F ε hε
  apply finite_exact_matching c0Record (by norm_num) ?_ F hε
  intro G φ
  simpa only [Real.norm_eq_abs] using record_bound G.val φ

end MathGauge.SharpFiniteBoundary
