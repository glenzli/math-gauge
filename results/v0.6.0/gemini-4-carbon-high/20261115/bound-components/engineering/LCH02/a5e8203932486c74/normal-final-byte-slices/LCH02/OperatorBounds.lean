import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import LCH02.MatrixProducts

namespace LCH02

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

/-!
# 第 2 章 算子界 · 有限复合与路径节群（LCH02）

覆盖 `obligations.json` 中与算子 Lipschitz / co-Lipschitz 矩阵界、受限域单调性、
两步与任意有限步链复合及零步边界相关的全部定义与定理义务。
-/

/--
OET anchor: oet-af85899693cc8750
**定义（全域合法 Lipschitz 矩阵谓词，`CH02-D01`）**：
对所有 `x, y ∈ dom ϕ` 与所有 `j ∈ I`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i → j} · d_i(x, y)`。
-/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/--
OET anchor: oet-af85899693cc8750
**定义（全域 Lipschitz 矩阵证书族 `mathscr_L(ϕ)`，`CH02-D01`）**。
-/
def lipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限合法 Lipschitz 矩阵谓词，`CH02-D01`）**：
对子集 `U ⊆ dom ϕ`，在 `U` 上对所有 `x, y ∈ U` 与所有 `j ∈ I` 满足距离放缩上界。
-/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 Lipschitz 矩阵证书族 `mathscr_L(ϕ)|_U`，`CH02-D01`）**。
-/
def restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

@[simp]
theorem restrictedLipMatrices_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedLipMatrices d ϕ (dom ϕ) = lipMatrices d ϕ := by
  ext L
  simp [restrictedLipMatrices, IsRestrictedLipMatrix, lipMatrices, IsLipMatrix]

/--
OET anchor: oet-af85899693cc8750
**定义（含非空条件的子集受限 co-Lipschitz 矩阵谓词，`CH02-D02`）**：
按正文约定，凡出现 `mathscr_K(ϕ)|_U` 均包含非空性条件 `U ≠ ∅` 及定义域包含 `U ⊆ dom ϕ`，
且对所有 `x, y ∈ U` 与所有 `j ∈ I` 满足 `d_j(ϕ(x), ϕ(y)) ≥ ∑_{i ∈ I} K_{i → j} · d_i(x, y)`。
-/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/--
OET anchor: oet-af85899693cc8750
**定义（含非空条件的子集受限 co-Lipschitz 矩阵证书族 `mathscr_K(ϕ)|_U`，`CH02-D02`）**。
-/
def restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

theorem IsRestrictedCoLipMatrix.nonempty {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) :
    U.Nonempty :=
  hK.1

theorem IsRestrictedCoLipMatrix.subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) :
    U ⊆ dom ϕ :=
  hK.2.1

/--
OET anchor: oet-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界，指标集等于单点集形式，`CH02-P01`）**：
当 `I = {i}` 时，全域 Lip 矩阵条件等价于标量不等式
`d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} · d_i(x, y)`（`∀ x, y ∈ dom ϕ`）。
-/
theorem lipMatrices_mem_iff_scalar_of_univ_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (i : I) (hi : (Finset.univ : Finset I) = {i}) :
    L ∈ lipMatrices d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    rwa [hi, Finset.sum_singleton] at h
  · intro hscalar x hx y hy j
    have hj : j = i := by
      have hj_mem : j ∈ (Finset.univ : Finset I) := Finset.mem_univ j
      rw [hi, Finset.mem_singleton] at hj_mem
      exact hj_mem
    subst hj
    rw [hi, Finset.sum_singleton]
    exact hscalar x hx y hy

/--
OET anchor: oet-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界，基数 `|I| = 1` 形式，`CH02-P01`）**：
当 `Fintype.card I = 1` 且 `i ∈ I` 时，全域 Lip 矩阵条件退化为单个标量不等式。
-/
theorem lipMatrices_mem_iff_scalar_of_card_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hcard : Fintype.card I = 1) (i : I) :
    L ∈ lipMatrices d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  have hi : (Finset.univ : Finset I) = {i} := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Fintype.card_le_one_iff.mp hcard.le k i
  exact lipMatrices_mem_iff_scalar_of_univ_singleton d ϕ L i hi

/--
OET anchor: oet-c4369c63c86cbacf
单分量受限 Lip 矩阵标量界等价形式（`CH02-P01`）。
-/
theorem restrictedLipMatrices_mem_iff_scalar_of_univ_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ)
    (L : GaugeMatrix I) (i : I) (hi : (Finset.univ : Finset I) = {i}) :
    L ∈ restrictedLipMatrices d ϕ U ↔
      ∀ x ∈ U, ∀ y ∈ U,
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  constructor
  · intro hL x hx y hy
    have h := hL.2 x hx y hy i
    rwa [hi, Finset.sum_singleton] at h
  · intro hscalar
    refine ⟨hU, fun x hx y hy j => ?_⟩
    have hj : j = i := by
      have hj_mem : j ∈ (Finset.univ : Finset I) := Finset.mem_univ j
      rw [hi, Finset.mem_singleton] at hj_mem
      exact hj_mem
    subst hj
    rw [hi, Finset.sum_singleton]
    exact hscalar x hx y hy

/--
OET anchor: oet-4ff5c58d71e1651f
**引理 2.1（受限 Lip 矩阵族的单调性 / 反单调性，`CH02-P02`）**：
若 `U ⊆ V ⊆ dom ϕ`，则 `mathscr_L(ϕ)|_V ⊆ mathscr_L(ϕ)|_U`。
-/
theorem restrictedLipMatrices_anti {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    restrictedLipMatrices d ϕ V ⊆ restrictedLipMatrices d ϕ U := by
  intro L hL
  refine ⟨hUV.trans hV, fun x hx y hy j => ?_⟩
  exact hL.2 x (hUV hx) y (hUV hy) j

/--
OET anchor: oet-4ff5c58d71e1651f
**引理 2.1 特例（全域 Lip 证书可限制到任意定义域子集，`CH02-P03`）**：
对任意 `U ⊆ dom ϕ`，有 `mathscr_L(ϕ) ⊆ mathscr_L(ϕ)|_U`。
-/
theorem lipMatrices_subset_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hU : U ⊆ dom ϕ) :
    lipMatrices d ϕ ⊆ restrictedLipMatrices d ϕ U := by
  rw [← restrictedLipMatrices_dom d ϕ]
  exact restrictedLipMatrices_anti d ϕ hU Set.Subset.rfl

/-- 复合定义域包含关系引理（左因子输入域）：`U₁ ⊆ dom(ϕ₂ ∘ ϕ₁) → U₁ ⊆ dom ϕ₁`。 -/
theorem subset_dom_left_of_subset_dom_comp {X : Type} {bot : X}
    {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    U₁ ⊆ dom ϕ₁ := by
  intro x hx hbot
  have hcomp : ϕ₂.func (ϕ₁.func x) ≠ bot := hU₁ hx
  rw [hbot, ϕ₂.preserves_bot] at hcomp
  exact hcomp rfl

/--
OET anchor: oet-193cebcc1a7f9259
复合定义域包含关系引理（精确中间像域，`CH02-P04`）：
若 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，记 `U₂ = ϕ₁(U₁)`，则 `U₂ ⊆ dom ϕ₂`。
-/
theorem image_subset_dom_of_subset_dom_comp {X : Type} {bot : X}
    {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro y ⟨x, hx, rfl⟩
  exact hU₁ hx

/-- 两步复合定义域的精确充要刻画：`U₁ ⊆ dom(ϕ₂ ∘ ϕ₁) ↔ U₁ ⊆ dom ϕ₁ ∧ ϕ₁(U₁) ⊆ dom ϕ₂`。 -/
theorem subset_dom_comp_iff {X : Type} {bot : X}
    (ϕ₂ ϕ₁ : Operator X bot) (U₁ : Set X) :
    U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁) ↔
      U₁ ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  constructor
  · intro hU₁
    exact ⟨subset_dom_left_of_subset_dom_comp hU₁, image_subset_dom_of_subset_dom_comp hU₁⟩
  · rintro ⟨_, hU₂⟩ x hx
    exact hU₂ ⟨x, hx, rfl⟩

/--
OET anchor: oet-193cebcc1a7f9259
**命题 2.2（Lip 矩阵复合律，`CH02-P04`）**：
设 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，精确中间像集 `U₂ = ϕ₁(U₁)`。
若 `L₁ ∈ mathscr_L(ϕ₁)|_{U₁}` 且 `L₂ ∈ mathscr_L(ϕ₂)|_{U₂}`，
则 `L₂ · L₁ ∈ mathscr_L(ϕ₂ ∘ ϕ₁)|_{U₁}`。
-/
theorem restrictedLipMatrices_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₂ ϕ₁ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁))
    {L₂ L₁ : GaugeMatrix I}
    (hL₁ : L₁ ∈ restrictedLipMatrices d ϕ₁ U₁)
    (hL₂ : L₂ ∈ restrictedLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul L₂ L₁ ∈ restrictedLipMatrices d (operator_compose ϕ₂ ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((operator_compose ϕ₂ ϕ₁).func x) ((operator_compose ϕ₂ ϕ₁).func y)
        = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, channelEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) :=
        hL₂.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ ≤ ∑ k : I, channelEntry L₂ k j * (∑ i : I, channelEntry L₁ i k * d i x y) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (hL₁.2 x hx y hy k) (zero_le _)
    _ = ∑ k : I, ∑ i : I, channelEntry L₂ k j * (channelEntry L₁ i k * d i x y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.mul_sum _ _ _
    _ = ∑ i : I, ∑ k : I, (channelEntry L₂ k j * channelEntry L₁ i k) * d i x y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc]
    _ = ∑ i : I, (∑ k : I, channelEntry L₂ k j * channelEntry L₁ i k) * d i x y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i : I, channelEntry (gaugeMatrixMul L₂ L₁) i j * d i x y := by
        simp [Matrix.mul_apply]

/--
OET anchor: oet-893b1d33535f7245
**引理 2.3（受限 co-Lip 矩阵族的单调性 / 反单调性，`CH02-P05`）**：
若 `∅ ≠ U ⊆ V ⊆ dom ϕ`，则 `mathscr_K(ϕ)|_V ⊆ mathscr_K(ϕ)|_U`。
-/
theorem restrictedCoLipMatrices_anti {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hU_ne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    restrictedCoLipMatrices d ϕ V ⊆ restrictedCoLipMatrices d ϕ U := by
  intro K hK
  refine ⟨hU_ne, hUV.trans hV, fun x hx y hy j => ?_⟩
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/--
OET anchor: oet-893b1d33535f7245
**引理 2.3 特例（全域 co-Lip 证书可限制到任意非空定义域子集，`CH02-P06`）**：
对任意非空子集 `U ⊆ dom ϕ`，有 `mathscr_K(ϕ)|_{dom ϕ} ⊆ mathscr_K(ϕ)|_U`。
-/
theorem globalCoLipMatrices_subset_restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    restrictedCoLipMatrices d ϕ (dom ϕ) ⊆ restrictedCoLipMatrices d ϕ U :=
  restrictedCoLipMatrices_anti d ϕ hU_ne hU Set.Subset.rfl

/--
OET anchor: oet-88784dcbfff0ea66
受限域版本：若 `U` 中存在点对使 `d_j(ϕ(x), ϕ(y)) = 0` 且 `d_i(x, y) > 0`，
则任一受限 co-Lip 矩阵 `K ∈ mathscr_K(ϕ)|_U` 满足 `K_{i → j} = 0`（`CH02-P07`）。
-/
theorem channelEntry_eq_zero_of_restrictedCoLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {i j : I} {K : GaugeMatrix I}
    (h_witness : ∃ x ∈ U, ∃ y ∈ U, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) :
    channelEntry K i j = 0 := by
  rcases h_witness with ⟨x, hx, y, hy, h_out_zero, h_in_pos⟩
  have h_le : ∑ k : I, channelEntry K k j * d k x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    hK.2.2 x hx y hy j
  rw [h_out_zero] at h_le
  have h_term_le : channelEntry K i j * d i x y ≤ ∑ k : I, channelEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k => channelEntry K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h_mul_zero : channelEntry K i j * d i x y = 0 :=
    le_antisymm (h_term_le.trans h_le) (zero_le _)
  rcases mul_eq_zero.mp h_mul_zero with hK0 | hd0
  · exact hK0
  · exact absurd hd0 (ne_of_gt h_in_pos)

/--
OET anchor: oet-88784dcbfff0ea66
**注（co-Lip 条目为零的充分条件，`CH02-P07`）**：
若存在 `x, y ∈ dom ϕ` 使 `d_j(ϕ(x), ϕ(y)) = 0` 且 `d_i(x, y) > 0`，
则任一全域 co-Lip 矩阵 `K ∈ mathscr_K(ϕ)|_{dom ϕ}` 必满足 `K_{i → j} = 0`。
-/
theorem channelEntry_eq_zero_of_globalCoLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {i j : I} {K : GaugeMatrix I}
    (h_witness : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y)
    (hK : K ∈ restrictedCoLipMatrices d ϕ (dom ϕ)) :
    channelEntry K i j = 0 :=
  channelEntry_eq_zero_of_restrictedCoLip d ϕ h_witness hK

/--
OET anchor: oet-0f256e6f1d38a612
两步 co-Lip 复合中的精确中间像域非空性与定义域包含引理（`CH02-P08`）：
由 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)` 与 `K₁ ∈ mathscr_K(ϕ₁)|_{U₁}`，推出中间像域 `U₂ = ϕ₁(U₁)` 非空且 `U₂ ⊆ dom ϕ₂`。
-/
theorem image_nonempty_and_subset_dom_of_restrictedCoLip {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁))
    {K₁ : GaugeMatrix I} (hK₁ : K₁ ∈ restrictedCoLipMatrices d ϕ₁ U₁) :
    (operator_image ϕ₁ U₁).Nonempty ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ :=
  ⟨hK₁.1.image ϕ₁.func, image_subset_dom_of_subset_dom_comp hU₁⟩

/--
OET anchor: oet-0f256e6f1d38a612
**命题 2.4（co-Lip 矩阵复合律，`CH02-P08`）**：
设 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，精确中间像集 `U₂ = ϕ₁(U₁)`。
若 `K₁ ∈ mathscr_K(ϕ₁)|_{U₁}` 且 `K₂ ∈ mathscr_K(ϕ₂)|_{U₂}`，
则 `K₂ · K₁ ∈ mathscr_K(ϕ₂ ∘ ϕ₁)|_{U₁}`。
-/
theorem restrictedCoLipMatrices_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₂ ϕ₁ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁))
    {K₂ K₁ : GaugeMatrix I}
    (hK₁ : K₁ ∈ restrictedCoLipMatrices d ϕ₁ U₁)
    (hK₂ : K₂ ∈ restrictedCoLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul K₂ K₁ ∈ restrictedCoLipMatrices d (operator_compose ϕ₂ ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, channelEntry (gaugeMatrixMul K₂ K₁) i j * d i x y
        = ∑ i : I, (∑ k : I, channelEntry K₂ k j * channelEntry K₁ i k) * d i x y := by
            simp [Matrix.mul_apply]
    _ = ∑ i : I, ∑ k : I, (channelEntry K₂ k j * channelEntry K₁ i k) * d i x y := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, channelEntry K₂ k j * (channelEntry K₁ i k * d i x y) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
            rw [mul_assoc]
    _ = ∑ k : I, channelEntry K₂ k j * (∑ i : I, channelEntry K₁ i k * d i x y) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
    _ ≤ ∑ k : I, channelEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
            refine Finset.sum_le_sum fun k _ => ?_
            exact mul_le_mul_of_nonneg_left (hK₁.2.2 x hx y hy k) (zero_le _)
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
            hK₂.2.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ = d j ((operator_compose ϕ₂ ϕ₁).func x) ((operator_compose ϕ₂ ϕ₁).func y) := rfl

/--
OET anchor: oet-c80171fa685dc795
**定义（按作用次序索引的有限复合算子 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`，`CH02-D05`）**：
`k = 0` 时取恒等算子 `operator_identity`；`k + 1` 时在第 `k` 步前缀复合之后作用 `ϕ_k`。
-/
def finiteComp {X : Type} {bot : X} :
    (k : ℕ) → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => operator_identity
  | k + 1, ϕ => operator_compose (ϕ (Fin.last k)) (finiteComp k (ϕ ∘ Fin.castSucc))

@[simp]
theorem finiteComp_zero {X : Type} {bot : X} (ϕ : Fin 0 → Operator X bot) :
    finiteComp 0 ϕ = operator_identity := rfl

@[simp]
theorem finiteComp_one {X : Type} {bot : X} (ϕ : Fin 1 → Operator X bot) :
    finiteComp 1 ϕ = ϕ 0 := rfl

@[simp]
theorem finiteComp_succ {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) :
    finiteComp (k + 1) ϕ =
      operator_compose (ϕ (Fin.last k)) (finiteComp k (ϕ ∘ Fin.castSucc)) := rfl

/--
OET anchor: oet-c80171fa685dc795
链表示对应定理（`CH02-D05`）：
按正向作用步序 `1, ..., k` 给出的 `finiteComp k ϕ` 与冻结前置模块中按复合外层到内层排列的
`OperatorChain ((List.ofFn ϕ).reverse)` 完全相等。
-/
theorem finiteComp_eq_operatorChain {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) :
    finiteComp k ϕ = OperatorChain ((List.ofFn ϕ).reverse) := by
  induction k with
  | zero =>
      rfl
  | succ m ih =>
      rw [finiteComp_succ, ih, List.ofFn_succ']
      simp [List.concat_eq_append, OperatorChain, operator_compose]
      rfl

theorem finiteComp_eq_reverse_prod {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) :
    finiteComp k ϕ = ((List.ofFn ϕ).reverse).prod := by
  rw [finiteComp_eq_operatorChain, operator_chain_eq_prod]

/-- 反向链表示对应（`CH02-D05`）：任意正向算子列表 `ϕs = [ϕ₁, ..., ϕₖ]` 的逆序 `OperatorChain` 等于 `finiteComp`。 -/
theorem operatorChain_reverse_eq_finiteComp {X : Type} {bot : X}
    (ϕs : List (Operator X bot)) :
    OperatorChain ϕs.reverse = finiteComp ϕs.length ϕs.get := by
  rw [finiteComp_eq_operatorChain, List.ofFn_get]

/--
OET anchor: oet-c80171fa685dc795
**定义（复合链的实际中间像域序列 `U_1, ..., U_{k+1}`，`CH02-D05`）**：
由起始域 `U₁` 出发，递归定义 `U_0 = U₁`、`U_{m+1} = ϕ_m(U_m)`（`m : Fin k`）。
-/
def chainImageDomain {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) : Fin (k + 1) → Set X :=
  Fin.induction U₁ (fun m Um => operator_image (ϕ m) Um)

@[simp]
theorem chainImageDomain_zero {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    chainImageDomain k ϕ U₁ 0 = U₁ := by
  simp [chainImageDomain]

@[simp]
theorem chainImageDomain_succ {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    chainImageDomain k ϕ U₁ m.succ =
      operator_image (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc) := by
  simp [chainImageDomain]

/-- 前缀不变性：扩展第 `k + 1` 步算子不改变前 `k + 1` 个中间像域（`CH02-D05`）。 -/
theorem chainImageDomain_castSucc {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) (U₁ : Set X) (r : Fin (k + 1)) :
    chainImageDomain (k + 1) ϕ U₁ r.castSucc =
      chainImageDomain k (ϕ ∘ Fin.castSucc) U₁ r := by
  refine Fin.inductionOn r ?_ ?_
  · simp
  · intro m ih
    have h_cs : (m.succ : Fin (k + 1)).castSucc = (m.castSucc : Fin (k + 1)).succ := by
      ext
      rfl
    rw [h_cs, chainImageDomain_succ, chainImageDomain_succ, ih]
    rfl

/-- 终点像集刻画：第 `k + 1` 个域 `U_{k+1}` 恰好等于全复合 `c_k` 对 `U₁` 的像集（`CH02-D05`）。 -/
theorem chainImageDomain_last_eq_image_finiteComp {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    chainImageDomain k ϕ U₁ (Fin.last k) = operator_image (finiteComp k ϕ) U₁ := by
  induction k with
  | zero =>
      change U₁ = id '' U₁
      simp
  | succ m ih =>
      have h_last : (Fin.last (m + 1)) = (Fin.last m).succ := by
        ext
        rfl
      rw [h_last, chainImageDomain_succ, chainImageDomain_castSucc, ih]
      simp [operator_image, finiteComp_succ, operator_compose, Set.image_image]

/-- 中间像域非空性传播：若起始域 `U₁` 非空，则链上所有实际中间像域均非空（`CH02-D05`）。 -/
theorem chainImageDomain_nonempty {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) {U₁ : Set X} (hU₁ : U₁.Nonempty) :
    ∀ r : Fin (k + 1), (chainImageDomain k ϕ U₁ r).Nonempty := by
  intro r
  refine Fin.inductionOn r ?_ ?_
  · simpa using hU₁
  · intro m ih
    rw [chainImageDomain_succ]
    exact ih.image (ϕ m).func

/--
OET anchor: oet-c80171fa685dc795
链定义域递推保证引理（`CH02-D05`）：
若 `U₁ ⊆ dom(c_k)`，则对每一步 `m ∈ {1, ..., k}`，实际中间输入域满足 `U_m ⊆ dom(ϕ_m)`。
-/
theorem chainImageDomain_subset_dom {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ)) :
    ∀ m : Fin k, chainImageDomain k ϕ U₁ m.castSucc ⊆ dom (ϕ m) := by
  induction k with
  | zero =>
      intro m
      exact Fin.elim0 m
  | succ n ih =>
      rw [finiteComp_succ, subset_dom_comp_iff] at hU₁
      rcases hU₁ with ⟨h_init, h_last⟩
      intro m
      refine Fin.lastCases ?_ ?_ m
      · rw [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp]
        exact h_last
      · intro s
        have h_cs : s.castSucc.castSucc = (s.castSucc : Fin (n + 1)).castSucc := rfl
        rw [h_cs, chainImageDomain_castSucc]
        exact ih (ϕ ∘ Fin.castSucc) h_init s

/-- 正长度链（`k ≥ 1`）定义域递推充要刻画（`CH02-D05`）：
`U₁ ⊆ dom(c_k)` 当且仅当每一步实际中间输入域满足 `U_m ⊆ dom(ϕ_m)`。 -/
theorem chainImageDomain_subset_dom_iff {X : Type} {bot : X}
    (k : ℕ) (hk : 1 ≤ k) (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    U₁ ⊆ dom (finiteComp k ϕ) ↔
      ∀ m : Fin k, chainImageDomain k ϕ U₁ m.castSucc ⊆ dom (ϕ m) := by
  constructor
  · exact chainImageDomain_subset_dom k ϕ
  · induction k with
    | zero => exact absurd hk (Nat.not_succ_le_zero 0)
    | succ n ih =>
        cases n with
        | zero =>
            intro h
            simpa using h 0
        | succ r =>
            intro h
            rw [finiteComp_succ, subset_dom_comp_iff]
            constructor
            · apply ih (Nat.succ_pos r)
              intro s
              have hs := h s.castSucc
              rwa [chainImageDomain_castSucc] at hs
            · have hlast := h (Fin.last (r + 1))
              rwa [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp] at hlast

/-- 由链起始域条件 `U₁ ⊆ dom(c_k)` 与第 `m` 步逐点不等式构造局部 Lip 证书 `L_m ∈ mathscr_L(ϕ_m)|_{U_m}`（`CH02-P09`）。 -/
theorem step_mem_restrictedLipMatrices_of_chain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : ℕ} {ϕ : Fin k → Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ)) (m : Fin k) (Lm : GaugeMatrix I)
    (h_bound : ∀ x ∈ chainImageDomain k ϕ U₁ m.castSucc,
      ∀ y ∈ chainImageDomain k ϕ U₁ m.castSucc, ∀ j : I,
        d j ((ϕ m).func x) ((ϕ m).func y) ≤ ∑ i : I, channelEntry Lm i j * d i x y) :
    Lm ∈ restrictedLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc) :=
  ⟨chainImageDomain_subset_dom k ϕ hU₁ m, h_bound⟩

/-- 由链起始域非空且 `U₁ ⊆ dom(c_k)` 与第 `m` 步逐点下界不等式构造局部 co-Lip 证书 `K_m ∈ mathscr_K(ϕ_m)|_{U_m}`（`CH02-P10`）。 -/
theorem step_mem_restrictedCoLipMatrices_of_chain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : ℕ} {ϕ : Fin k → Operator X bot} {U₁ : Set X}
    (hU₁_ne : U₁.Nonempty) (hU₁ : U₁ ⊆ dom (finiteComp k ϕ))
    (m : Fin k) (Km : GaugeMatrix I)
    (h_bound : ∀ x ∈ chainImageDomain k ϕ U₁ m.castSucc,
      ∀ y ∈ chainImageDomain k ϕ U₁ m.castSucc, ∀ j : I,
        ∑ i : I, channelEntry Km i j * d i x y ≤ d j ((ϕ m).func x) ((ϕ m).func y)) :
    Km ∈ restrictedCoLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc) :=
  ⟨chainImageDomain_nonempty k ϕ hU₁_ne m.castSucc,
    chainImageDomain_subset_dom k ϕ hU₁ m, h_bound⟩

/--
OET anchor: oet-c80171fa685dc795
**推论 2.5(i)（有限复合的局部 Lip 矩阵界，`CH02-P09`）**：
设 `k ≥ 1`，`c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`，起始子集 `U₁ ⊆ dom(c_k)`，实际中间像域 `U_{m+1} = ϕ_m(U_m)`。
若各单步满足 `L^{(m)} ∈ mathscr_L(ϕ_m)|_{U_m}`，则有序连乘满足
`L^{(k)} · ⋯ · L^{(1)} ∈ mathscr_L(c_k)|_{U₁}`。
-/
theorem finiteComp_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ))
    (L : Fin k → GaugeMatrix I)
    (hL : ∀ m : Fin k,
      L m ∈ restrictedLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc)) :
    nonemptyMatrixProd k hk L ∈ restrictedLipMatrices d (finiteComp k ϕ) U₁ := by
  induction k with
  | zero => exact absurd hk (Nat.not_succ_le_zero 0)
  | succ n ih =>
      cases n with
      | zero =>
          simpa [nonemptyMatrixProd, finiteComp] using hL 0
      | succ r =>
          have hr : 1 ≤ r + 1 := Nat.succ_pos r
          have hr' : 1 ≤ r + 2 := Nat.succ_pos (r + 1)
          rw [nonemptyMatrixProd_succ hr hr', finiteComp_succ]
          have hU_init : U₁ ⊆ dom (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) :=
            subset_dom_left_of_subset_dom_comp hU₁
          have hL_init : ∀ m : Fin (r + 1),
              (L ∘ Fin.castSucc) m ∈
                restrictedLipMatrices d ((ϕ ∘ Fin.castSucc) m)
                  (chainImageDomain (r + 1) (ϕ ∘ Fin.castSucc) U₁ m.castSucc) := by
            intro m
            have hm := hL m.castSucc
            rwa [chainImageDomain_castSucc] at hm
          have h_ih := ih hr (ϕ ∘ Fin.castSucc) hU_init (L ∘ Fin.castSucc) hL_init
          have hL_last := hL (Fin.last (r + 1))
          rw [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp] at hL_last
          exact restrictedLipMatrices_comp d (ϕ (Fin.last (r + 1)))
            (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) hU₁ h_ih hL_last

/-- `OperatorChain` 列表接口下的有限复合局部 Lip 矩阵连乘界（`CH02-P09`）。 -/
theorem operatorChain_reverse_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕs : List (Operator X bot)) (hϕs : 1 ≤ ϕs.length)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (OperatorChain ϕs.reverse))
    (L : Fin ϕs.length → GaugeMatrix I)
    (hL : ∀ m : Fin ϕs.length,
      L m ∈ restrictedLipMatrices d (ϕs.get m)
        (chainImageDomain ϕs.length ϕs.get U₁ m.castSucc)) :
    nonemptyMatrixProd ϕs.length hϕs L ∈
      restrictedLipMatrices d (OperatorChain ϕs.reverse) U₁ := by
  rw [operatorChain_reverse_eq_finiteComp] at hU₁ ⊢
  exact finiteComp_restrictedLipMatrices d ϕs.length hϕs ϕs.get hU₁ L hL

/--
OET anchor: oet-c80171fa685dc795
**推论 2.5(ii)（有限复合的局部 co-Lip 矩阵界，`CH02-P10`）**：
设 `k ≥ 1`，`c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`，起始子集 `U₁ ⊆ dom(c_k)`，实际中间像域 `U_{m+1} = ϕ_m(U_m)`。
若各单步满足 `K^{(m)} ∈ mathscr_K(ϕ_m)|_{U_m}`，则有序连乘满足
`K^{(k)} · ⋯ · K^{(1)} ∈ mathscr_K(c_k)|_{U₁}`。
-/
theorem finiteComp_restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ))
    (K : Fin k → GaugeMatrix I)
    (hK : ∀ m : Fin k,
      K m ∈ restrictedCoLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc)) :
    nonemptyMatrixProd k hk K ∈ restrictedCoLipMatrices d (finiteComp k ϕ) U₁ := by
  induction k with
  | zero => exact absurd hk (Nat.not_succ_le_zero 0)
  | succ n ih =>
      cases n with
      | zero =>
          simpa [nonemptyMatrixProd, finiteComp] using hK 0
      | succ r =>
          have hr : 1 ≤ r + 1 := Nat.succ_pos r
          have hr' : 1 ≤ r + 2 := Nat.succ_pos (r + 1)
          rw [nonemptyMatrixProd_succ hr hr', finiteComp_succ]
          have hU_init : U₁ ⊆ dom (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) :=
            subset_dom_left_of_subset_dom_comp hU₁
          have hK_init : ∀ m : Fin (r + 1),
              (K ∘ Fin.castSucc) m ∈
                restrictedCoLipMatrices d ((ϕ ∘ Fin.castSucc) m)
                  (chainImageDomain (r + 1) (ϕ ∘ Fin.castSucc) U₁ m.castSucc) := by
            intro m
            have hm := hK m.castSucc
            rwa [chainImageDomain_castSucc] at hm
          have h_ih := ih hr (ϕ ∘ Fin.castSucc) hU_init (K ∘ Fin.castSucc) hK_init
          have hK_last := hK (Fin.last (r + 1))
          rw [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp] at hK_last
          exact restrictedCoLipMatrices_comp d (ϕ (Fin.last (r + 1)))
            (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) hU₁ h_ih hK_last

/-- `OperatorChain` 列表接口下的有限复合局部 co-Lip 矩阵连乘界（`CH02-P10`）。 -/
theorem operatorChain_reverse_restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕs : List (Operator X bot)) (hϕs : 1 ≤ ϕs.length)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (OperatorChain ϕs.reverse))
    (K : Fin ϕs.length → GaugeMatrix I)
    (hK : ∀ m : Fin ϕs.length,
      K m ∈ restrictedCoLipMatrices d (ϕs.get m)
        (chainImageDomain ϕs.length ϕs.get U₁ m.castSucc)) :
    nonemptyMatrixProd ϕs.length hϕs K ∈
      restrictedCoLipMatrices d (OperatorChain ϕs.reverse) U₁ := by
  rw [operatorChain_reverse_eq_finiteComp] at hU₁ ⊢
  exact finiteComp_restrictedCoLipMatrices d ϕs.length hϕs ϕs.get hU₁ K hK

/-- 单位矩阵在分量距离求和下的恒等展开：`∑_{i ∈ I} I_{i → j} · d_i(x, y) = d_j(x, y)`。 -/
theorem sum_identityMatrix_mul_dist {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    ∑ i : I, channelEntry (identityMatrix (I := I)) i j * d i x y = d j x y := by
  simp [identityMatrix, Matrix.one_apply]

/--
OET anchor: oet-11006ddd8c43bfec
**注（恒等算子的全域单位 Lip 矩阵证书，`CH02-P11`）**：
`I ∈ mathscr_L(id_X)`。
-/
theorem identityMatrix_mem_lipMatrices {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    identityMatrix (I := I) ∈ lipMatrices d (operator_identity (X := X) (bot := bot)) := by
  intro x _ y _ j
  rw [sum_identityMatrix_mul_dist]
  rfl

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步恒等算子的受限单位 Lip 矩阵证书，`CH02-P11`）**：
对任意 `U ⊆ dom(id_X)`，`I ∈ mathscr_L(id_X)|_U`。
-/
theorem identityMatrix_mem_restrictedLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    identityMatrix (I := I) ∈
      restrictedLipMatrices d (operator_identity (X := X) (bot := bot)) U :=
  lipMatrices_subset_restrictedLipMatrices d operator_identity hU
    (identityMatrix_mem_lipMatrices d)

/--
OET anchor: oet-11006ddd8c43bfec
零步复合形式（`k = 0`，`CH02-P11`）：
矩阵空复合乘积 `matrixChainProd 0 L = I` 属于零步复合 `finiteComp 0 ϕ = id_X` 在 `U` 上的受限 Lip 证书族。
-/
theorem zeroStep_matrixChainProd_mem_restrictedLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Fin 0 → Operator X bot)
    (L : Fin 0 → GaugeMatrix I) {U : Set X}
    (hU : U ⊆ dom (finiteComp 0 ϕ)) :
    matrixChainProd 0 L ∈ restrictedLipMatrices d (finiteComp 0 ϕ) U :=
  identityMatrix_mem_restrictedLipMatrices d hU

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步恒等算子的受限单位 co-Lip 矩阵证书，`CH02-P12`）**：
对任意非空 `U ⊆ dom(id_X)`，`I ∈ mathscr_K(id_X)|_U`。
-/
theorem identityMatrix_mem_restrictedCoLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    identityMatrix (I := I) ∈
      restrictedCoLipMatrices d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU_ne, hU, fun x _ y _ j => ?_⟩
  rw [sum_identityMatrix_mul_dist]
  rfl

/--
OET anchor: oet-11006ddd8c43bfec
零步复合形式（`k = 0`，`CH02-P12`）：
对任意非空 `U ⊆ dom(c_0)`，矩阵空复合乘积 `matrixChainProd 0 K = I` 属于 `mathscr_K(c_0)|_U`。
-/
theorem zeroStep_matrixChainProd_mem_restrictedCoLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Fin 0 → Operator X bot)
    (K : Fin 0 → GaugeMatrix I) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (finiteComp 0 ϕ)) :
    matrixChainProd 0 K ∈ restrictedCoLipMatrices d (finiteComp 0 ϕ) U :=
  identityMatrix_mem_restrictedCoLipMatrices d hU_ne hU

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步复合的单位矩阵双侧证书封装，`CH02-P11` / `CH02-P12`）**：
对任意非空 `U ⊆ dom(id_X)`，`I ∈ mathscr_L(id_X)|_U ∩ mathscr_K(id_X)|_U`。
-/
theorem identityMatrix_mem_lip_inter_coLip {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    identityMatrix (I := I) ∈
      restrictedLipMatrices d (operator_identity (X := X) (bot := bot)) U ∩
        restrictedCoLipMatrices d (operator_identity (X := X) (bot := bot)) U :=
  ⟨identityMatrix_mem_restrictedLipMatrices d hU,
    identityMatrix_mem_restrictedCoLipMatrices d hU_ne hU⟩

/-- 扩展规范空间语境下，恒等算子的全定义域 `dom(id_X) = X \ {bot}` 非空，故单位矩阵属于全域 co-Lip 族。 -/
theorem identityMatrix_mem_globalCoLipMatrices_of_gaugeSpace {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    identityMatrix (I := I) ∈
      restrictedCoLipMatrices d (operator_identity (X := X) (bot := bot))
        (dom (operator_identity (X := X) (bot := bot))) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  rcases (hd i₀).nonabsorbing with ⟨x₀, hx₀⟩
  exact identityMatrix_mem_restrictedCoLipMatrices d ⟨x₀, hx₀⟩ Set.Subset.rfl

end LCH02
