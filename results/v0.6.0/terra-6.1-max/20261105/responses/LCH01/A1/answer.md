已完成清单中的 8 项义务。源码在指定环境中编译通过；公理检查仅显示 `propext`、`Classical.choice` 和 `Quot.sound`。构建时，`LEAN_PATH` 须包含冻结的 `formal_oet` 模块及指定版本的预置 mathlib。

理论来源：Zhe Li（Glen Li / glenzli），ORCID https://orcid.org/0009-0006-6536-3453，*The Operator Evolution Theory*，https://glenzli.com/books/oet/，许可协议 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下是对所选内容的 Lean 改写。

```lean filename=ChannelBounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Lean reformulation of selected material from Zhe Li (also known as Glen Li /
glenzli), ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution
Theory*, Volume I, Chapter 2, https://glenzli.com/books/oet/ . Licensed under
CC BY 4.0, https://creativecommons.org/licenses/by/4.0/ .
-/

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

namespace LCH01

variable {X I : Type} {bot : X} [Fintype I]

/-- Matrices use output components as rows and input components as columns. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- A component channel is an ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

/-- The coefficient of a channel `(i,j)` is the matrix entry at row `j`, column `i`. -/
def channelCoefficient (M : ChannelMatrix I) (c : ComponentChannel I) : ENNReal :=
  M c.2 c.1

omit [Fintype I] in
@[simp] theorem channelCoefficient_pair (M : ChannelMatrix I) (i j : I) :
    channelCoefficient M (i, j) = M j i := rfl

/-- The composition product has the later matrix on the left. -/
noncomputable def channelProduct (M₂ M₁ : ChannelMatrix I) : ChannelMatrix I := M₂ * M₁

theorem channelProduct_entry (M₂ M₁ : ChannelMatrix I) (i j : I) :
    channelCoefficient (channelProduct M₂ M₁) (i, j) =
      ∑ k : I, channelCoefficient M₂ (k, j) * channelCoefficient M₁ (i, k) := by
  exact Matrix.mul_apply

/-- An unrestricted Lip matrix has the defining inequality on the whole domain. -/
def IsLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L j i * d i x y

/-- Restricted Lip certificates require the restriction to lie in the domain. -/
def IsRestrictedLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L j i * d i x y

def lipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (ChannelMatrix I) :=
  { L | IsLipMatrix d φ L }

def restrictedLipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  { L | IsRestrictedLipMatrix d φ U L }

theorem lipMatrix_iff_restricted_domain (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : ChannelMatrix I) :
    IsLipMatrix d φ L ↔ IsRestrictedLipMatrix d φ (dom φ) L := by
  constructor
  · intro h
    exact ⟨Set.Subset.rfl, h⟩
  · intro h
    exact h.2

/-- Restricted co-Lip certificates additionally require a nonempty restriction. -/
def IsRestrictedCoLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, K j i * d i x y ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  { K | IsRestrictedCoLipMatrix d φ U K }

/-- Only the coefficient on channel `(i,j)` may be nonzero in output row `j`. -/
def IsSingleInputRow (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L j k = 0

/-- Each output row of a diagonal matrix is supported on its diagonal input. -/
def IsDiagonal (L : ChannelMatrix I) : Prop :=
  ∀ j : I, IsSingleInputRow L j j

omit [Fintype I] in
theorem zero_channel_term (L : ChannelMatrix I) (i j : I)
    (d : I → X → X → ENNReal) (x y : X)
    (hzero : channelCoefficient L (i, j) = 0) :
    L j i * d i x y = 0 := by
  simpa using congrArg (fun a : ENNReal => a * d i x y) hzero

open scoped Classical in
/-- A zero channel can be omitted from the corresponding Lip row bound. -/
theorem zero_channel_lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsRestrictedLipMatrix d φ U L)
    (hzero : channelCoefficient L (i, j) = 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤
      ∑ k ∈ Finset.univ.erase i, L j k * d k x y := by
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, L j k * d k x y :=
      hL.2 x hx y hy j
    _ = ∑ k ∈ Finset.univ.erase i, L j k * d k x y := by
      symm
      exact Finset.sum_erase Finset.univ (zero_channel_term L i j d x y hzero)

/-- Exact simplification of a single-input row, including infinite values. -/
theorem singleInputRow_sum (d : I → X → X → ENNReal)
    (L : ChannelMatrix I) (i j : I) (hrow : IsSingleInputRow L i j) (x y : X) :
    (∑ k : I, L j k * d k x y) = L j i * d i x y := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- A single-input row gives the stated scalar Lip bound on that channel. -/
theorem singleInputRow_lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsRestrictedLipMatrix d φ U L) (hrow : IsSingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j i * d i x y := by
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, L j k * d k x y :=
      hL.2 x hx y hy j
    _ = L j i * d i x y := singleInputRow_sum d L i j hrow x y

/-- The diagonal case holds simultaneously for every component. -/
theorem diagonal_lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I)
    (hL : IsRestrictedLipMatrix d φ U L) (hdiag : IsDiagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  singleInputRow_lip d φ U L j j hL (hdiag j) hx hy

/-- A single nonnegative channel term is bounded by the full output-row sum. -/
theorem channel_term_le_sum (d : I → X → X → ENNReal)
    (K : ChannelMatrix I) (i j : I) (x y : X) :
    K j i * d i x y ≤ ∑ k : I, K j k * d k x y := by
  classical
  exact Finset.single_le_sum (f := fun k : I => K j k * d k x y)
    (fun k _ => zero_le (K j k * d k x y)) (Finset.mem_univ i)

/-- Positive co-Lip channels preserve positive input-component distance. -/
theorem positive_coLip_channel (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I) (i j : I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hpos : 0 < K j i)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hd : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hprod : 0 < K j i * d i x y :=
    ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hd)
  exact lt_of_lt_of_le hprod
    (le_trans (channel_term_le_sum d K i j x y) (hK.2.2 x hx y hy j))

/-- Strictly positive diagonal co-Lip entries reflect family-zero distance. -/
theorem positive_diagonal_coLip_reflects_zero
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hdiag : ∀ j : I, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have houtpos := positive_coLip_channel d φ U K j j hK (hdiag j) hx hy hpos
  exact (ne_of_gt houtpos) (hout j)

/-- Exercise 2.2: the diagonal channel gives a scalar two-sided estimate. -/
theorem scalar_two_sided_bounds (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (L K : ChannelMatrix I) (j : I)
    (hL : IsRestrictedLipMatrix d φ U L)
    (hK : IsRestrictedCoLipMatrix d φ U K)
    (hrow : IsSingleInputRow L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · exact le_trans (channel_term_le_sum d K j j x y) (hK.2.2 x hx y hy j)
  · exact singleInputRow_lip d φ U L j j hL hrow hx hy

/-!
The preceding algebraic results do not need the pseudometric axioms or a
nonempty index set. The following specializations explicitly retain the
ambient extended-gauge-space assumptions of the source.
-/
namespace Textbook

/-- The single-row Lip display in the finite nonempty gauge setting. -/
theorem singleInputRow [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsRestrictedLipMatrix d φ U L) (hrow : IsSingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ (∑ k : I, L j k * d k x y) ∧
      (∑ k : I, L j k * d k x y) = L j i * d i x y :=
  ⟨hL.2 x hx y hy j, singleInputRow_sum d L i j hrow x y⟩

/-- For a diagonal Lip matrix the single-row bound holds in each component. -/
theorem diagonal [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (L : ChannelMatrix I)
    (hL : IsRestrictedLipMatrix d φ U L) (hdiag : IsDiagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  diagonal_lip d φ U L hL hdiag hx hy j

theorem positiveChannel [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I) (i j : I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hpos : 0 < K j i)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hdist : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  positive_coLip_channel d φ U K i j hK hpos hx hy hdist

theorem reflectsFamilyZero [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hdiag : ∀ j : I, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y :=
  positive_diagonal_coLip_reflects_zero d φ U K hK hdiag hx hy hout

theorem scalarTwoSided [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (L K : ChannelMatrix I) (j : I)
    (hL : IsRestrictedLipMatrix d φ U L)
    (hK : IsRestrictedCoLipMatrix d φ U K)
    (hrow : IsSingleInputRow L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  scalar_two_sided_bounds d φ U L K j hL hK hrow hx hy

end Textbook

end LCH01
```

```lean filename=Main.lean
import ChannelBounds
```

```lean filename=AxiomAudit.lean
import ChannelBounds
#print axioms LCH01.channelCoefficient_pair
#print axioms LCH01.channelProduct_entry
#print axioms LCH01.lipMatrix_iff_restricted_domain
#print axioms LCH01.zero_channel_term
#print axioms LCH01.zero_channel_lip
#print axioms LCH01.singleInputRow_sum
#print axioms LCH01.singleInputRow_lip
#print axioms LCH01.diagonal_lip
#print axioms LCH01.channel_term_le_sum
#print axioms LCH01.positive_coLip_channel
#print axioms LCH01.positive_diagonal_coLip_reflects_zero
#print axioms LCH01.scalar_two_sided_bounds
#print axioms LCH01.Textbook.singleInputRow
#print axioms LCH01.Textbook.diagonal
#print axioms LCH01.Textbook.positiveChannel
#print axioms LCH01.Textbook.reflectsFamilyZero
#print axioms LCH01.Textbook.scalarTwoSided
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```sh filename=build.sh
#!/bin/sh
# LEAN_PATH must contain the frozen formal_oet modules and the preinstalled
# mathlib build and its dependencies.
set -eu
export LEAN_PATH=".:${LEAN_PATH:-}"
lean -o ChannelBounds.olean ChannelBounds.lean
lean -o Main.olean Main.lean
lean AxiomAudit.lean
```

```json filename=alignment.json
{
  "case_id": "LCH01",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.IsLipMatrix"},
        {"file": "ChannelBounds.lean", "name": "LCH01.IsRestrictedLipMatrix"},
        {"file": "ChannelBounds.lean", "name": "LCH01.lipMatrices"},
        {"file": "ChannelBounds.lean", "name": "LCH01.restrictedLipMatrices"},
        {"file": "ChannelBounds.lean", "name": "LCH01.lipMatrix_iff_restricted_domain"}
      ],
      "representation": {
        "objects": "X、bot、Operator 和 dom 使用冻结基础模块；d i 是第 i 个 ENNReal 值分量，矩阵 L 使用 ChannelMatrix。",
        "parameters": "I 带 Fintype；U 为 X 的集合。定义对任意 d 均成立，因而适用于正文的有限非空指标集及扩展伪度量族。",
        "quantifiers": "全域谓词量化所有 x,y ∈ dom φ 和 j ∈ I；受限谓词包含 U ⊆ dom φ，并量化所有 x,y ∈ U 和 j ∈ I。",
        "conclusion": "两种谓词分别给出 d j (φ x) (φ y) ≤ ∑ i, L j i * d i x y；两个集合恰为满足对应谓词的矩阵族。全域谓词等价于取 U = dom φ 的受限谓词。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.IsRestrictedCoLipMatrix"},
        {"file": "ChannelBounds.lean", "name": "LCH01.restrictedCoLipMatrices"}
      ],
      "representation": {
        "objects": "K 是 ENNReal 值通道矩阵，φ 是保持 bot 的冻结 Operator，d 是分量距离族。",
        "parameters": "U 为 X 的子集，谓词显式要求 U.Nonempty 和 U ⊆ dom φ；I 带 Fintype。",
        "quantifiers": "对所有 x,y ∈ U 和所有输出分量 j 取有限输入指标和。",
        "conclusion": "合法性恰为 ∑ i, K j i * d i x y ≤ d j (φ x) (φ y)，restrictedCoLipMatrices 恰为这些 K 的集合；允许零与无穷条目。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.ChannelMatrix"},
        {"file": "ChannelBounds.lean", "name": "LCH01.ComponentChannel"},
        {"file": "ChannelBounds.lean", "name": "LCH01.channelCoefficient"},
        {"file": "ChannelBounds.lean", "name": "LCH01.channelCoefficient_pair"},
        {"file": "ChannelBounds.lean", "name": "LCH01.channelProduct"},
        {"file": "ChannelBounds.lean", "name": "LCH01.channelProduct_entry"}
      ],
      "representation": {
        "objects": "ChannelMatrix I 是 Matrix I I ENNReal，行是输出、列是输入；ComponentChannel I 是输入在前、输出在后的有序对。",
        "parameters": "channelCoefficient M (i,j) 定义为 M j i；channelProduct M₂ M₁ 使用标准矩阵乘积，较晚作用的矩阵在左。",
        "quantifiers": "对任意有限指标类型 I、矩阵 M₂、M₁ 和 i,j，求和遍历所有中间指标 k。",
        "conclusion": "乘积的 i→j 条目恰为 ∑ k, M₂ j k * M₁ k i；系数和运算均在 ENNReal 中，包含 0 * ∞ = 0。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.ComponentChannel"},
        {"file": "ChannelBounds.lean", "name": "LCH01.channelCoefficient"},
        {"file": "ChannelBounds.lean", "name": "LCH01.IsSingleInputRow"},
        {"file": "ChannelBounds.lean", "name": "LCH01.IsDiagonal"},
        {"file": "ChannelBounds.lean", "name": "LCH01.zero_channel_term"},
        {"file": "ChannelBounds.lean", "name": "LCH01.zero_channel_lip"}
      ],
      "representation": {
        "objects": "通道 (i,j) 表示输入分量 i 到输出分量 j；其系数是 L j i。IsSingleInputRow L i j 描述只可能保留输入 i 的输出行 j；IsDiagonal 要求每个输出行 j 只可能保留输入 j。",
        "parameters": "零通道结论针对任意受限 Lip 证书 L、合法限制域 U、通道 i→j 和 x,y ∈ U。",
        "quantifiers": "单行稀疏对每个 k ≠ i 要求 L j k = 0；对角条件对每个 j 给出相应单行条件。",
        "conclusion": "零系数对应的乘积项为零，且 zero_channel_lip 证明可从该行上界的有限和中删除此项；单行和对角的具体界由 CH02-P19 给出。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.singleInputRow_sum"},
        {"file": "ChannelBounds.lean", "name": "LCH01.singleInputRow_lip"},
        {"file": "ChannelBounds.lean", "name": "LCH01.diagonal_lip"},
        {"file": "ChannelBounds.lean", "name": "LCH01.Textbook.singleInputRow"},
        {"file": "ChannelBounds.lean", "name": "LCH01.Textbook.diagonal"}
      ],
      "representation": {
        "objects": "φ、U、L、i、j 与正文相同，hL 为受限 Lip 合法性，hrow 是除 i 外第 j 行系数为零。",
        "parameters": "Textbook 版本显式要求 I 有限非空且每个 d i 是冻结模块的 ExtendedPseudoMetric；较一般的代数引理对任意 ENNReal 值 d 成立。",
        "quantifiers": "对任意 x,y ∈ U 和任意选定通道 i→j；对角版本对每个 j 同时适用。",
        "conclusion": "先给出完整有限和恰等于 L j i * d i x y，再给出 d j (φ x) (φ y) ≤ 该项；对角版本取 i=j。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.channel_term_le_sum"},
        {"file": "ChannelBounds.lean", "name": "LCH01.positive_coLip_channel"},
        {"file": "ChannelBounds.lean", "name": "LCH01.Textbook.positiveChannel"}
      ],
      "representation": {
        "objects": "K 为 U 上合法受限 co-Lip 矩阵，i→j 通道系数 K j i 是严格正的 ENNReal。",
        "parameters": "U 的非空及 U ⊆ dom φ 包含在合法性中；Textbook 版本另保留有限非空指标族和扩展伪度量族背景。",
        "quantifiers": "对任意这样的 K、i、j 以及任意 x,y ∈ U。",
        "conclusion": "d i x y > 0 蕴含 d j (φ x) (φ y) > 0；证明使用该通道项不超过完整非负行和，允许系数或距离为 ∞。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.positive_diagonal_coLip_reflects_zero"},
        {"file": "ChannelBounds.lean", "name": "LCH01.Textbook.reflectsFamilyZero"}
      ],
      "representation": {
        "objects": "GaugeZeroRelated 使用冻结模块定义的所有分量距离为零关系；K 为 U 上受限 co-Lip 矩阵。",
        "parameters": "要求所有 j 的对角条目 K j j > 0，U 的非空性和定义域包含在 co-Lip 合法性中；Textbook 版本保留完整规范空间背景。",
        "quantifiers": "对所有 x,y ∈ U，从 φ x 与 φ y 在每个 j 上零距推出 x 与 y 在每个 j 上零距。",
        "conclusion": "只断言 GaugeZeroRelated d (φ x) (φ y) → GaugeZeroRelated d x y；未假设族分离，也未加强为 x = y。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.scalar_two_sided_bounds"},
        {"file": "ChannelBounds.lean", "name": "LCH01.Textbook.scalarTwoSided"}
      ],
      "representation": {
        "objects": "L 与 K 分别是 φ 在同一 U 上的合法受限 Lip 与 co-Lip 矩阵；j 是输出分量。",
        "parameters": "IsSingleInputRow L j j 表示 L k→j = 0 对所有 k ≠ j；非空及定义域要求由两种合法性谓词保留，Textbook 版本保留规范空间背景。",
        "quantifiers": "对任意满足前提的 φ、U、L、K、j 和所有 x,y ∈ U。",
        "conclusion": "同时证明 K j j * d j x y ≤ d j (φ x) (φ y) 以及 d j (φ x) (φ y) ≤ L j j * d j x y；K 的其他行条目不要求为零。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19", "CH02-P20"]
    }
  ]
}
```