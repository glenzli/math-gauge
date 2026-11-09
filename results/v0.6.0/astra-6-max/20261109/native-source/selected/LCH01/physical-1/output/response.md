全部 8 项已完成。源码已通过指定 Lean 4.29.1、mathlib 版本的编译检查，零警告；23 个声明的公理审计均符合要求。冻结的 `formal_oet/` 文件按附件原路径保留。

```toml filename=lakefile.toml
name = "lch01"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "LCH01"
globs = ["LCH01.+"]

[[lean_lib]]
name = "formal_oet"
globs = ["formal_oet.+"]

[[lean_lib]]
name = "Main"
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```lean filename=LCH01/Definitions.lean
import Mathlib.Data.Matrix.Mul
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
Formalization of the eight LCH01 obligations from Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, Volume I, v1.0.0, Chapter 2.
Author ORCID: https://orcid.org/0009-0006-6536-3453
Source DOI: https://doi.org/10.5281/zenodo.21457931
Official work: https://glenzli.com/books/oet/
Current source repository: https://gitlab.com/glenzli/oet-public
Source snapshot: https://github.com/glenzli/oet-public
at commit 539b40cec73184d98e06d54fbd10e4b4698bd6e7.
License: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/
The Lean declarations in LCH01 are a new formalization of the cited text.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- CH02-D03: rows are output indices; columns are input indices. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- The source's `M_{i → j}` is the usual matrix entry `M j i`. -/
def entry (M : ChannelMatrix I) (i j : I) : ENNReal := M j i

/-- Standard matrix multiplication in the source's input/output notation. -/
theorem entry_mul [Fintype I] (M₂ M₁ : ChannelMatrix I) (i j : I) :
    entry (M₂ * M₁) i j = ∑ k : I, entry M₂ k j * entry M₁ i k := by
  rfl

/-- The finite weighted sum for one output row. -/
noncomputable def rowSum [Fintype I] (M : ChannelMatrix I) (j : I) (v : I → ENNReal) :
    ENNReal := ∑ i : I, entry M i j * v i

/-- CH02-D01: a restricted Lip matrix includes its domain condition. -/
def IsRestrictedLipMatrix [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ rowSum L j (fun i => d i x y)

/-- A global Lip matrix is a restricted one on the full operator domain. -/
def IsLipMatrix [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : ChannelMatrix I) : Prop :=
  IsRestrictedLipMatrix d φ (dom φ) L

/-- The global definition has precisely the source's pointwise quantifiers. -/
theorem isLipMatrix_iff [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : ChannelMatrix I) :
    IsLipMatrix d φ L ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
        d j (φ.func x) (φ.func y) ≤ rowSum L j (fun i => d i x y) := by
  simp [IsLipMatrix, IsRestrictedLipMatrix]

/-- The source's `𝓛(φ)`. -/
def lipMatrices [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) : Set (ChannelMatrix I) :=
  {L | IsLipMatrix d φ L}

/-- The source's `𝓛(φ)|_U`. -/
def restrictedLipMatrices [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {L | IsRestrictedLipMatrix d φ U L}

/-- CH02-D02: nonemptiness is part of the co-Lip predicate. -/
def IsRestrictedCoLipMatrix [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      rowSum K j (fun i => d i x y) ≤ d j (φ.func x) (φ.func y)

/-- The source's `𝓚(φ)|_U`, with nonemptiness required of every member. -/
def restrictedCoLipMatrices [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {K | IsRestrictedCoLipMatrix d φ U K}

/-- CH02-D07: a component channel is an ordered (input, output) pair. -/
abbrev ComponentChannel (I : Type) := I × I

/-- Only input `i` may contribute to output row `j`; its entry may also be zero. -/
def SingleInputRow (M : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → entry M k j = 0

/-- A diagonal matrix has no off-diagonal input contributions. -/
def IsDiagonal (M : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → entry M i j = 0

theorem isDiagonal_iff_singleInputRows (M : ChannelMatrix I) :
    IsDiagonal M ↔ ∀ j : I, SingleInputRow M j j := by
  constructor
  · intro h j k hkj
    exact h k j hkj
  · intro h i j hij
    exact h j i hij

end LCH01
```

```lean filename=LCH01/Channels.lean
import LCH01.Definitions

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X} [Fintype I]

/-- CH02-P19: a row supported at one input has exactly one possible summand. -/
theorem singleInputRow_sum (M : ChannelMatrix I) (i j : I)
    (hrow : SingleInputRow M i j) (v : I → ENNReal) :
    rowSum M j v = entry M i j * v i := by
  classical
  unfold rowSum
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Each nonnegative input term is bounded by the full row sum. -/
theorem entry_mul_le_rowSum (M : ChannelMatrix I) (i j : I)
    (v : I → ENNReal) :
    entry M i j * v i ≤ rowSum M j v := by
  classical
  exact Finset.single_le_sum (fun k _ => zero_le (entry M k j * v k))
    (Finset.mem_univ i)

section Gauge

variable {d : I → X → X → ENNReal}

-- The explicit premises retain the source's nonempty gauge-space context.

/-- CH02-P19: the Lip bound when output row `j` only uses input `i`. -/
theorem single_input_lip_bound [Nonempty I]
    (_hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : L ∈ restrictedLipMatrices d φ U)
    {i j : I} (hrow : SingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ entry L i j * d i x y := by
  have h := hL.2 x hx y hy j
  rw [singleInputRow_sum L i j hrow] at h
  exact h

/-- CH02-P19: the same reduction for every diagonal channel. -/
theorem diagonal_lip_bound [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : L ∈ restrictedLipMatrices d φ U)
    (hdiag : IsDiagonal L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  exact single_input_lip_bound hGauge hL
    ((isDiagonal_iff_singleInputRows L).mp hdiag j) hx hy

/-- Any individual co-Lip channel gives a lower bound. -/
theorem colip_channel_lower_bound [Nonempty I]
    (_hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : K ∈ restrictedCoLipMatrices d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    entry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  exact (entry_mul_le_rowSum K i j (fun k => d k x y)).trans
    (hK.2.2 x hx y hy j)

/-- CH02-P20, Proposition 2.8(i): positive channels preserve positive distance. -/
theorem positive_colip_channel [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : K ∈ restrictedCoLipMatrices d φ U)
    {i j : I} (hpos : 0 < entry K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hxy : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  exact lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hxy.ne')
    (colip_channel_lower_bound hGauge hK hx hy i j)

/-- CH02-P21, Proposition 2.8(ii): reflection of family zero distance only. -/
theorem positive_diagonal_reflects_zero [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : K ∈ restrictedCoLipMatrices d φ U)
    (hdiag : ∀ j : I, 0 < entry K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout := positive_colip_channel hGauge hK (hdiag j) hx hy hpos
  rw [hzero j] at hout
  exact (lt_irrefl 0) hout

/-- CH02-P25, Exercise 2.2: the scalar two-sided bound on output `j`. -/
theorem scalar_two_sided_bound [Nonempty I]
    (hGauge : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L K : ChannelMatrix I}
    (hL : L ∈ restrictedLipMatrices d φ U)
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    {j : I} (hrow : SingleInputRow L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  exact ⟨colip_channel_lower_bound hGauge hK hx hy j j,
    single_input_lip_bound hGauge hL hrow hx hy⟩

end Gauge

end LCH01
```

```lean filename=Main.lean
import LCH01.Definitions
import LCH01.Channels

#print axioms LCH01.ChannelMatrix
#print axioms LCH01.entry
#print axioms LCH01.entry_mul
#print axioms LCH01.rowSum
#print axioms LCH01.IsRestrictedLipMatrix
#print axioms LCH01.IsLipMatrix
#print axioms LCH01.isLipMatrix_iff
#print axioms LCH01.lipMatrices
#print axioms LCH01.restrictedLipMatrices
#print axioms LCH01.IsRestrictedCoLipMatrix
#print axioms LCH01.restrictedCoLipMatrices
#print axioms LCH01.ComponentChannel
#print axioms LCH01.SingleInputRow
#print axioms LCH01.IsDiagonal
#print axioms LCH01.isDiagonal_iff_singleInputRows
#print axioms LCH01.singleInputRow_sum
#print axioms LCH01.entry_mul_le_rowSum
#print axioms LCH01.single_input_lip_bound
#print axioms LCH01.diagonal_lip_bound
#print axioms LCH01.colip_channel_lower_bound
#print axioms LCH01.positive_colip_channel
#print axioms LCH01.positive_diagonal_reflects_zero
#print axioms LCH01.scalar_two_sided_bound
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
        {"file": "LCH01/Definitions.lean", "name": "LCH01.IsRestrictedLipMatrix"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.IsLipMatrix"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.isLipMatrix_iff"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.lipMatrices"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.restrictedLipMatrices"}
      ],
      "representation": {
        "objects": "X、bot、Operator X bot、dom 沿用冻结前置模块；d i 是分量距离，矩阵条目取 ENNReal。",
        "parameters": "I 带 Fintype；受限定义包含 U ⊆ dom φ。谓词可对任意距离族定义；目标定理另显式保留 Nonempty I 及每个 d i 的 ExtendedPseudoMetric 背景。",
        "quantifiers": "对所有 x ∈ U、y ∈ U、j ∈ I，输出距离 ≤ rowSum L j (fun i => d i x y)。",
        "conclusion": "rowSum 是有限和 Σ_i L_{i→j} d_i(x,y)。全域谓词取 U = dom φ，isLipMatrix_iff 展示原文量词；两个 Set 定义分别是全部合法全域和受限证书族。Lip 不要求 U 非空，也不要求条目有限。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Definitions.lean", "name": "LCH01.IsRestrictedCoLipMatrix"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.restrictedCoLipMatrices"}
      ],
      "representation": {
        "objects": "与 Lip 使用相同的算子、距离族及 ENNReal 矩阵。",
        "parameters": "U.Nonempty 和 U ⊆ dom φ 都直接包含于合法受限 co-Lip 谓词。",
        "quantifiers": "对所有 x ∈ U、y ∈ U、j ∈ I，Σ_i K_{i→j} d_i(x,y) ≤ d_j(φ(x),φ(y))。",
        "conclusion": "restrictedCoLipMatrices 恰为满足以上定义的矩阵集合；取 U = dom φ 即原文全域 co-Lip 证书族，仍保留非空要求。条目允许 +∞，乘法沿用 ENNReal 的 0·∞=0。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Definitions.lean", "name": "LCH01.ChannelMatrix"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.entry"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.entry_mul"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.rowSum"}
      ],
      "representation": {
        "objects": "ChannelMatrix I = Matrix I I ENNReal；标准矩阵行表示输出，列表示输入。",
        "parameters": "entry M i j 定义为 M j i，精确对应 M_{i→j}。乘法与有限和使用 Fintype I。",
        "quantifiers": "entry_mul 对任意 M₂、M₁、i、j 成立。",
        "conclusion": "采用标准矩阵乘法，并证明 (M₂*M₁)_{i→j} = Σ_k (M₂)_{k→j}(M₁)_{i→k}；rowSum 明确定义对应输出行的加权有限和。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Definitions.lean", "name": "LCH01.ComponentChannel"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.SingleInputRow"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.IsDiagonal"},
        {"file": "LCH01/Definitions.lean", "name": "LCH01.isDiagonal_iff_singleInputRows"}
      ],
      "representation": {
        "objects": "ComponentChannel I = I × I，有序对第一项是输入，第二项是输出。",
        "parameters": "SingleInputRow M i j 表示输出行 j 仅可能使用输入 i；允许这个剩余条目也为零。",
        "quantifiers": "单行条件为 ∀ k ≠ i, M_{k→j}=0；IsDiagonal 为 ∀ i ≠ j, M_{i→j}=0。",
        "conclusion": "isDiagonal_iff_singleInputRows 证明对角矩阵恰好在每行 j 满足 SingleInputRow M j j；实际有限和及距离界化简由 CH02-P19 给出。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.singleInputRow_sum"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.single_input_lip_bound"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.diagonal_lip_bound"}
      ],
      "representation": {
        "objects": "合法受限 Lip 矩阵 L，以及输出行 j 的单输入条件 SingleInputRow L i j。",
        "parameters": "距离界定理保留有限非空 I、扩展规范空间前提、U 上的合法证书及 x,y ∈ U。",
        "quantifiers": "任意 i,j 及 x,y ∈ U；对角特例对所有 j 成立。",
        "conclusion": "singleInputRow_sum 证明整行有限和等于 L_{i→j}d_i(x,y)；single_input_lip_bound 给出相应输出距离上界；diagonal_lip_bound 以 IsDiagonal L 为前提给出所有同分量上界。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.entry_mul_le_rowSum"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.colip_channel_lower_bound"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.positive_colip_channel"}
      ],
      "representation": {
        "objects": "U 上的合法受限 co-Lip 矩阵 K 及通道 (i,j)。",
        "parameters": "保留有限非空规范族及全部规范公理；证书包含 U 非空和定义域条件；另要求 0 < K_{i→j}。",
        "quantifiers": "对任意 x,y ∈ U，若 0 < d_i(x,y)，则结论成立。",
        "conclusion": "先证明单项 ≤ 行和 ≤ 输出距离，再用 ENNReal 正乘积推出 0 < d_j(φ(x),φ(y))；不增加系数或距离的有限性条件。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.positive_diagonal_reflects_zero"}
      ],
      "representation": {
        "objects": "使用冻结模块的 GaugeZeroRelated d，定义为所有分量距离均为零。",
        "parameters": "K 是 U 上合法 co-Lip 矩阵，并且 ∀ j, 0 < K_{j→j}；不要求 K 的非对角条目为零，不假设规范族分离。",
        "quantifiers": "对任意 x,y ∈ U，GaugeZeroRelated d (φ(x)) (φ(y)) 蕴含 GaugeZeroRelated d x y。",
        "conclusion": "逐分量应用正通道结论的逆否推理，反射族零距关系；结论没有加强为 x=y 或算子单射。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.scalar_two_sided_bound"}
      ],
      "representation": {
        "objects": "同一算子 φ、同一受限域 U 上的 Lip 矩阵 L 与 co-Lip 矩阵 K，以及指定输出分量 j。",
        "parameters": "保留有限非空规范族及全部规范公理；仅要求 L 的第 j 行满足 ∀ k≠j, L_{k→j}=0；对 K 无额外对角性或严格正性要求。",
        "quantifiers": "对任意 x,y ∈ U 成立；U 的非空性和定义域包含条件由合法证书保留。",
        "conclusion": "以合取精确表达 K_{j→j}d_j(x,y) ≤ d_j(φ(x),φ(y)) ≤ L_{j→j}d_j(x,y)，分别由 co-Lip 单项下界和 Lip 单行化简得到。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19", "CH02-P20"]
    }
  ]
}
```