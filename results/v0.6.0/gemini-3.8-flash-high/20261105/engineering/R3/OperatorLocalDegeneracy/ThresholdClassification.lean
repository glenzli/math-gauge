import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Fin.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers
import OperatorLocalDegeneracy.NullificationRadius

namespace OperatorLocalDegeneracy

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- CH03-D06: 直径尺度函数 -/
noncomputable def diam (d_metric : X → X → ENNReal) (U : Set X) : ENNReal :=
  ⨆ x ∈ U, ⨆ y ∈ U, d_metric x y

/-- CH03-D06: 尺度函数的单调性 -/
def IsMonotoneScale (σ : Set X → ENNReal) : Prop :=
  ∀ ⦃B U : Set X⦄, B ⊆ U → σ B ≤ σ U

lemma diam_is_monotone (d_metric : X → X → ENNReal) :
    IsMonotoneScale (diam d_metric) := by
  intro B U hBU
  dsimp [diam]
  apply iSup_le; intro x
  apply iSup_le; intro hx
  apply iSup_le; intro y
  apply iSup_le; intro hy
  refine le_iSup_of_le x ?_
  refine le_iSup_of_le (hBU hx) ?_
  refine le_iSup_of_le y ?_
  refine le_iSup_of_le (hBU hy) le_rfl

/-- CH03-D06: 阈值分类枚举 -/
inductive ThresholdType
  | T11 : ThresholdType -- 尺度满足且零化满足
  | T10 : ThresholdType -- 尺度满足且零化不满足
  | T01 : ThresholdType -- 尺度不满足且零化满足
  | T00 : ThresholdType -- 尺度不满足且零化不满足
  deriving DecidableEq, Repr

noncomputable def classify_channel (σ_val : ENNReal) (N_val : ENNReal) (τ_σ τ_N : ENNReal) : ThresholdType :=
  if σ_val ≤ τ_σ then
    if τ_N ≤ N_val then ThresholdType.T11 else ThresholdType.T10
  else
    if τ_N ≤ N_val then ThresholdType.T01 else ThresholdType.T00

noncomputable def classify_pair (σ_val : ENNReal) (N_val : ENNReal) (τ_σ τ_N : ENNReal) : Bool × Bool :=
  (decide (σ_val ≤ τ_σ), decide (τ_N ≤ N_val))

/-- CH03-P16-01: 引理 3.13 四种阈值组合互斥且穷尽 -/
theorem lemma_3_13_exhaustive (σ_val N_val τ_σ τ_N : ENNReal) :
    classify_channel σ_val N_val τ_σ τ_N = ThresholdType.T11 ∨
    classify_channel σ_val N_val τ_σ τ_N = ThresholdType.T10 ∨
    classify_channel σ_val N_val τ_σ τ_N = ThresholdType.T01 ∨
    classify_channel σ_val N_val τ_σ τ_N = ThresholdType.T00 := by
  dsimp [classify_channel]
  split_ifs <;> simp

theorem lemma_3_13_exclusive :
    (ThresholdType.T11 ≠ ThresholdType.T10) ∧
    (ThresholdType.T11 ≠ ThresholdType.T01) ∧
    (ThresholdType.T11 ≠ ThresholdType.T00) ∧
    (ThresholdType.T10 ≠ ThresholdType.T01) ∧
    (ThresholdType.T10 ≠ ThresholdType.T00) ∧
    (ThresholdType.T01 ≠ ThresholdType.T00) := by
  decide

/-- CH03-P16-02: 引理 3.13 (i) 输入尺度阈值增大，第一项为1的通道集合不减 -/
theorem lemma_3_13_i (σ : I → Set X → ENNReal) (U : Set X)
    (τ_σ1 τ_σ2 : ENNReal) (hτ : τ_σ1 ≤ τ_σ2) :
    { i : I | σ i U ≤ τ_σ1 } ⊆ { i : I | σ i U ≤ τ_σ2 } := by
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  exact le_trans hi hτ

/-- CH03-P16-03: 引理 3.13 (ii) 零化阈值增大，第二项为1的通道集合不增 -/
theorem lemma_3_13_ii (N : I → I → ENNReal)
    (τ_N1 τ_N2 : ENNReal) (hτ : τ_N1 ≤ τ_N2) :
    { p : I × I | τ_N2 ≤ N p.1 p.2 } ⊆ { p : I × I | τ_N1 ≤ N p.1 p.2 } := by
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  exact le_trans hτ hp

/-- CH03-P17-01: 命题 3.14 (i) 任意单调尺度函数的域缩小单调性及阈值推论 -/
theorem prop_3_14_i (σ : Set X → ENNReal) (hmono : IsMonotoneScale σ)
    {B U : Set X} (hBU : B ⊆ U) (τ_σ : ENNReal) :
    σ B ≤ σ U ∧ (σ U ≤ τ_σ → σ B ≤ τ_σ) := by
  have hle := hmono hBU
  refine ⟨hle, fun h => le_trans hle h⟩

/-- CH03-P17-02: 命题 3.14 (ii-a) 固定基点属于B时，缩小评估域使点态半径不减 -/
theorem prop_3_14_ii_a (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot)
    {B U : Set X} (hBU : B ⊆ U) {y : X} (hy : y ∈ B) :
    r_null d_in d_out ϕ y U ≤ r_null d_in d_out ϕ y B := by
  dsimp [r_null]
  apply sSup_le_sSup
  intro r hr
  rcases hr with ⟨hr0, hrt, hball⟩
  refine ⟨hr0, hrt, ?_⟩
  intro x hx hdist
  exact hball x (hBU hx) hdist

/-- CH03-P17-03: 命题 3.14 (ii-b) 同时缩小评估域与取inf基点集合，证明统一半径不减 -/
theorem prop_3_14_ii_b (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot)
    {B U : Set X} (hBU : B ⊆ U) :
    r_null_uniform d_in d_out ϕ U ≤ r_null_uniform d_in d_out ϕ B := by
  dsimp [r_null_uniform]
  apply le_iInf; intro y
  apply le_iInf; intro hy
  have hyU : y ∈ U := hBU hy
  refine le_trans (biInf_le (fun y => r_null d_in d_out ϕ y U) hyU) ?_
  exact prop_3_14_ii_a d_in d_out ϕ hBU hy

/-- CH03-P17-04: 命题 3.14 (iii) 直径尺度的二点/单点反例，否定反向尺度判断 -/
def counter_two_pt_d (x y : Option (Fin 2)) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => if a = b then 0 else ENNReal.ofReal 1
  | _, _ => ⊤

theorem prop_3_17_counterexample :
    let U : Set (Option (Fin 2)) := { some 0, some 1 }
    let B : Set (Option (Fin 2)) := { some 0 }
    let τ_σ : ENNReal := ENNReal.ofReal (1 / 2)
    B ⊆ U ∧
    diam counter_two_pt_d B ≤ τ_σ ∧
    ¬(diam counter_two_pt_d U ≤ τ_σ) := by
  intro U B τ_σ
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; simp [B, U] at hx ⊢; left; exact hx
  · dsimp [diam, B, counter_two_pt_d, τ_σ]
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    simp at hx hy
    subst hx; subst hy
    exact bot_le
  · dsimp [diam, U, counter_two_pt_d, τ_σ]
    intro hle
    have h1 : counter_two_pt_d (some 0) (some 1) ≤ ⨆ x ∈ U, ⨆ y ∈ U, counter_two_pt_d x y := by
      refine le_iSup_of_le (some 0) ?_
      refine le_iSup_of_le (by simp [U]) ?_
      refine le_iSup_of_le (some 1) ?_
      refine le_iSup_of_le (by simp [U]) le_rfl
    dsimp [counter_two_pt_d] at h1
    have h_contra : ENNReal.ofReal 1 ≤ ENNReal.ofReal (1 / 2) := le_trans h1 hle
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h_contra
    norm_num at h_contra

end OperatorLocalDegeneracy
