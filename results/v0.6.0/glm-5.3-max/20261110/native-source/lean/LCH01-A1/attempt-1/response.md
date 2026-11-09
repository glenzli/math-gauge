全部 8 项义务已完成形式化并验证通过。以下交付完整源码。

## 交付总览

| 义务 | 内容 | 载体文件 |
|:--|:--|:--|
| CH02-D01 | 全域/受限 Lip 矩阵谓词与证书族 𝓛(φ)、𝓛(φ)\|_U | `lip_matrix.lean` |
| CH02-D02 | 含非空条件的受限 co-Lip 矩阵及证书族 𝓚(φ)\|_U | `colip_matrix.lean` |
| CH02-D03 | 输入/输出指标约定（(𝐋)_{ji}=L_{i→j}）与代数矩阵乘法 | `channel_matrix.lean` |
| CH02-D07 | 分量通道、单行稀疏、对角特例、零条目不参与上界 | `component_channel.lean` |
| CH02-P19 | 单一输入项行化简（和式与证书形式，含对角特例） | `component_channel.lean` |
| CH02-P20 | 命题 2.8(i)：正 co-Lip 通道保持正距离 | `colip_reflection.lean` |
| CH02-P21 | 命题 2.8(ii)：全对角正 co-Lip 反射 ∼_G；反例证明不可加强为 x=y | `colip_reflection.lean` |
| CH02-P25 | 习题 2.2：标量双侧界 | `exercise_02_02.lean` |

**验证**（Lean 4.29.1 + mathlib 5e932f97，冻结模块原样导入，未修改任何附件）：`lake build formal_oet` 全部模块从零重建成功、零警告零错误；`lake env lean Main.lean` 通过；对全部 28 个核心声明 `#print axioms` 仅依赖 `propext, Classical.choice, Quot.sound`，无 sorry/新公理；alignment.json 中 72 个声明名逐一 `#check` 通过。

**表示要点**：正文记号 𝓛(φ)\|_U 以 `U ⊆ dom(φ)` 为定义前提、𝓚(φ)\|_U 按原文约定额外含 `U ≠ ∅`，两者均作为侧条件并入谓词 `IsLipMatrixOn` / `IsCoLipMatrixOn`；底座规范公理与 `I` 的非空性在各项证明中均不使用，故一般定理未假设（陈述强于原文语境），另按冻结模块 `operator_gauge_space_textbook` 的先例提供 `_textbook` 正文语境封装。

```lean
filename=Main.lean
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.colip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.component_channel
import formal_oet.vol_01.ch_02_operator_bounds.colip_reflection
import formal_oet.vol_01.ch_02_operator_bounds.exercise_02_02

/-!
# LCH01 · 通道接口节群 —— 第 2 章义务清单总入口

导入 `formal_oet/vol_01/ch_02_operator_bounds/` 下全部目标模块，
覆盖 obligations.json 的 8 项义务：

| 义务        | 模块与声明                                                                    |
|:------------|:------------------------------------------------------------------------------|
| `CH02-D01`  | `lip_matrix.lean`：全域/受限 Lip 矩阵谓词与证书族                              |
| `CH02-D02`  | `colip_matrix.lean`：含非空条件的受限 co-Lip 矩阵及证书族                     |
| `CH02-D03`  | `channel_matrix.lean`：输入/输出矩阵指标约定与乘法                            |
| `CH02-D07`  | `component_channel.lean`：分量通道、单行稀疏与对角特例                        |
| `CH02-P19`  | `component_channel.lean`：单一输入项行化简（含对角特例）                      |
| `CH02-P20`  | `colip_reflection.lean`：正 co-Lip 通道保持正距离                             |
| `CH02-P21`  | `colip_reflection.lean`：全对角正 co-Lip 反射族零距（不可加强为点相等）        |
| `CH02-P25`  | `exercise_02_02.lean`：习题 2.2 标量双侧界                                    |

冻结前置模块为 `formal_oet.vol_01.ch_01_foundations`
（`gauge_space.lean`、`operator_space.lean`），保持原样导入。
-/
```

```lean
filename=formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

/-!
# 第 2 章 算子界：通道矩阵的指标约定与乘法（义务 CH02-D03）

本文件形式化正文 § 2.1 中矩阵 `𝐋` 的书写约定与乘法：
条目以 `i → j`（输入分量 `i`、输出分量 `j`）标记，取值于 `ℝ̄₊`；
书写矩阵时以输出分量为行指标、输入分量为列指标，
即 `(𝐋)_{ji} = L_{i→j}`；并给出命题 2.2 证明中使用的代数矩阵乘法。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

/--
OET anchor: oet-af85899693cc8750
**约定（通道矩阵）**
以 `L i j` 表示条目 `L_{i→j}`：输入分量为 `i`，输出分量为 `j`。
条目取值于 `ℝ̄₊`（`ENNReal`），非负性由值类型保证。
-/
abbrev ChannelMatrix (I : Type) : Type := I → I → ENNReal

section Conventions

variable {I : Type}

/--
OET anchor: oet-af85899693cc8750
**约定（行/列指标）**
书写矩阵 `𝐋` 时，以输出分量为行指标、输入分量为列指标：
`L_{i→j}` 位于第 `j` 行、第 `i` 列，即 `(𝐋)_{ji} = L_{i→j}`。
`toRowMatrix L` 即 `L` 在该行列约定下的矩阵形式。 -/
def toRowMatrix (L : ChannelMatrix I) : Matrix I I ENNReal := fun j i => L i j

@[simp] theorem toRowMatrix_apply (L : ChannelMatrix I) (j i : I) :
    toRowMatrix L j i = L i j := rfl

/--
OET anchor: oet-af85899693cc8750
**第 `j` 行**：汇集指向输出分量 `d_j` 的系数（以输入分量为参变量）。 -/
def outputRow (L : ChannelMatrix I) (j : I) : I → ENNReal := fun i => L i j

/--
OET anchor: oet-af85899693cc8750
**第 `i` 列**：汇集自输入分量 `d_i` 出发的系数（以输出分量为参变量）。 -/
def inputCol (L : ChannelMatrix I) (i : I) : I → ENNReal := fun j => L i j

@[simp] theorem outputRow_apply (L : ChannelMatrix I) (j i : I) :
    outputRow L j i = L i j := rfl

@[simp] theorem inputCol_apply (L : ChannelMatrix I) (i j : I) :
    inputCol L i j = L i j := rfl

/-- 行列约定下的第 `j` 行即 `outputRow L j`。 -/
theorem toRowMatrix_eq_outputRow (L : ChannelMatrix I) (j : I) :
    toRowMatrix L j = outputRow L j := rfl

end Conventions

section Multiplication

variable {I : Type} [Fintype I]

/--
OET anchor: oet-af85899693cc8750
**定义（矩阵乘法的通道形式）**
对应命题 2.2 证明中的代数矩阵乘法元素：
`(𝐋² · 𝐋¹)_{i→j} = ∑_{k ∈ I} L²_{k→j} · L¹_{i→k}`
（左因子 `L2` 后作用；`I` 有限保证求和合法）。 -/
noncomputable def matMul (L2 L1 : ChannelMatrix I) : ChannelMatrix I :=
  fun i j => ∑ k : I, L2 k j * L1 i k

@[simp] theorem matMul_apply (L2 L1 : ChannelMatrix I) (i j : I) :
    matMul L2 L1 i j = ∑ k : I, L2 k j * L1 i k := rfl

/--
OET anchor: oet-af85899693cc8750
通道形式的乘法与正文行列约定下的代数矩阵乘法一致：
`toRowMatrix (matMul L2 L1) = toRowMatrix L2 * toRowMatrix L1`。 -/
theorem toRowMatrix_matMul (L2 L1 : ChannelMatrix I) :
    toRowMatrix (matMul L2 L1) = toRowMatrix L2 * toRowMatrix L1 := by
  ext j i
  simp [Matrix.mul_apply]

/--
OET anchor: oet-af85899693cc8750
通道矩阵乘法满足结合律
（`ℝ̄₊` 的有限和可按分配律展开并交换求和次序）。 -/
theorem matMul_assoc (L3 L2 L1 : ChannelMatrix I) :
    matMul (matMul L3 L2) L1 = matMul L3 (matMul L2 L1) := by
  funext i j
  have h1 : matMul (matMul L3 L2) L1 i j
      = ∑ k : I, ∑ m : I, (L3 m j * L2 k m) * L1 i k := by
    simp only [matMul_apply, Finset.sum_mul]
  have h2 : ∑ k : I, ∑ m : I, (L3 m j * L2 k m) * L1 i k
      = ∑ m : I, ∑ k : I, (L3 m j * L2 k m) * L1 i k := Finset.sum_comm
  have h3 : ∑ m : I, ∑ k : I, (L3 m j * L2 k m) * L1 i k
      = ∑ m : I, ∑ k : I, L3 m j * (L2 k m * L1 i k) :=
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  have h4 : ∑ m : I, ∑ k : I, L3 m j * (L2 k m * L1 i k)
      = matMul L3 (matMul L2 L1) i j := by
    simp only [matMul_apply, Finset.mul_sum]
  rw [h1, h2, h3, h4]

end Multiplication

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean
filename=formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix

/-!
# 第 2 章 算子界：全域/受限 Lip 矩阵谓词与证书族（义务 CH02-D01）

形式化正文 § 2.1 的 Lipschitz 上界矩阵：
全域合法 Lipschitz 矩阵（`L ∈ 𝓛(φ)`）、子集受限 Lip 矩阵
（`L ∈ 𝓛(φ)|_U`，`U ⊆ dom(φ)`）及对应证书族。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section LipCertificates

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-af85899693cc8750
Lip 距离放缩不等式在子集 `U` 上的纯不等式形式：
对所有 `x, y ∈ U` 与所有 `j ∈ I`，
`d_j(φ(x), φ(y)) ≤ ∑_{i∈I} L_{i→j} · d_i(x, y)`。 -/
def LipBoundOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y

/--
OET anchor: oet-af85899693cc8750
**定义（Lipschitz 矩阵）**
对 `φ ∈ X_op`，称非负矩阵 `L`（条目 `L_{i→j} ∈ ℝ̄₊`）为 `φ` 的
合法 Lipschitz 矩阵（`L ∈ 𝓛(φ)`），若对所有 `x, y ∈ dom(φ)` 和所有
`j ∈ I`：
`d_j(φ(x), φ(y)) ≤ ∑_{i∈I} L_{i→j} · d_i(x, y)`。 -/
def IsLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  LipBoundOn d φ L (dom φ)

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 Lip 矩阵）**
对子集 `U ⊆ dom(φ)`，若对任意 `x, y ∈ U` 均满足上述距离放缩不等式，
则称 `L` 为 `φ` 在 `U` 上的受限 Lip 矩阵（`L ∈ 𝓛(φ)|_U`）。
正文记号 `𝓛(φ)|_U` 以 `U ⊆ dom(φ)` 为前提，故谓词合并该侧条件。 -/
def IsLipMatrixOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) (U : Set X) : Prop :=
  U ⊆ dom φ ∧ LipBoundOn d φ L U

/--
OET anchor: oet-af85899693cc8750
`φ` 的全体合法 Lip 矩阵之集 `𝓛(φ)`（上界证书族）。
本章把它作为证书族使用，不预设其中存在同时实现所有条目下确界的矩阵。 -/
def lipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (ChannelMatrix I) := { L | IsLipMatrix d φ L }

/--
OET anchor: oet-af85899693cc8750
`φ` 在 `U` 上的全体合法受限 Lip 矩阵之集 `𝓛(φ)|_U`
（受限上界证书族）。 -/
def lipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) := { L | IsLipMatrixOn d φ L U }

theorem mem_lipFamily {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} :
    L ∈ lipFamily d φ ↔ IsLipMatrix d φ L := Iff.rfl

theorem mem_lipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} {U : Set X} :
    L ∈ lipFamilyOn d φ U ↔ IsLipMatrixOn d φ L U := Iff.rfl

theorem IsLipMatrix.lip_bound {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} (h : IsLipMatrix d φ L)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (j : I) :
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y :=
  h x hx y hy j

theorem IsLipMatrixOn.subset_dom {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} {U : Set X} (h : IsLipMatrixOn d φ L U) :
    U ⊆ dom φ := h.1

theorem IsLipMatrixOn.lip_bound {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} {U : Set X} (h : IsLipMatrixOn d φ L U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y :=
  h.2 x hx y hy j

/--
全域证书族即限制在 `dom(φ)` 上的受限证书族：`𝓛(φ) = 𝓛(φ)|_{dom(φ)}`。 -/
theorem lipFamily_eq_lipFamilyOn_dom (d : I → X → X → ENNReal)
    (φ : Operator X bot) :
    lipFamily d φ = lipFamilyOn d φ (dom φ) := by
  ext L
  exact ⟨fun h => ⟨fun _ hx => hx, h⟩, fun h => h.2⟩

end LipCertificates

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean
filename=formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix

/-!
# 第 2 章 算子界：含非空条件的受限 co-Lip 矩阵及证书族（义务 CH02-D02）

形式化正文 § 2.1 的子集受限 co-Lipschitz 下界矩阵：
对 `φ ∈ X_op` 与非空子集 `U ⊆ dom(φ)`，谓词 `K ∈ 𝓚(φ)|_U` 及
下界证书族 `𝓚(φ)|_U`。按正文约定，凡出现 `𝓚(φ)|_U` 均包含
非空性条件 `U ≠ ∅`。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section CoLipCertificates

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-af85899693cc8750
co-Lip 下界不等式在子集 `U` 上的纯不等式形式：
对所有 `x, y ∈ U` 与所有 `j ∈ I`，
`∑_{i∈I} K_{i→j} · d_i(x, y) ≤ d_j(φ(x), φ(y))`。 -/
def CoLipBoundOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (K : ChannelMatrix I) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, K i j * d i x y ≤ d j (φ.func x) (φ.func y)

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 co-Lipschitz 矩阵）**
对 `φ ∈ X_op` 与给定的非空子集 `U ⊆ dom(φ)`，称非负矩阵 `K`
（条目 `K_{i→j} ∈ ℝ̄₊`）为 `φ` 在 `U` 上的合法受限 co-Lipschitz
矩阵（`K ∈ 𝓚(φ)|_U`），若对所有 `x, y ∈ U` 和所有 `j ∈ I`：
`d_j(φ(x), φ(y)) ≥ ∑_{i∈I} K_{i→j} · d_i(x, y)`。
按正文约定，凡出现 `𝓚(φ)|_U` 均包含非空性条件 `U ≠ ∅`，
故谓词合并 `U.Nonempty`、`U ⊆ dom(φ)` 与不等式三部分。 -/
def IsCoLipMatrixOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (K : ChannelMatrix I) (U : Set X) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ CoLipBoundOn d φ K U

/--
OET anchor: oet-af85899693cc8750
`φ` 在 `U` 上的全体合法受限 co-Lip 矩阵之集 `𝓚(φ)|_U`
（下界证书族）。本章把它视为下界证书族使用，不预设其中存在
同时实现所有条目上确界的指定矩阵。 -/
def coLipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) := { K | IsCoLipMatrixOn d φ K U }

theorem mem_coLipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} :
    K ∈ coLipFamilyOn d φ U ↔ IsCoLipMatrixOn d φ K U := Iff.rfl

theorem IsCoLipMatrixOn.nonempty {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} (h : IsCoLipMatrixOn d φ K U) :
    U.Nonempty := h.1

theorem IsCoLipMatrixOn.subset_dom {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} (h : IsCoLipMatrixOn d φ K U) :
    U ⊆ dom φ := h.2.1

theorem IsCoLipMatrixOn.colip_bound {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} (h : IsCoLipMatrixOn d φ K U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i : I, K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  h.2.2 x hx y hy j

end CoLipCertificates

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean
filename=formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix

/-!
# 第 2 章 算子界：分量通道、单行稀疏与单一输入项行化简

形式化正文 § 2.2 的分量通道记号（义务 CH02-D07）与单一输入项
行化简命题（义务 CH02-P19）：条目 `L_{i→j}` 作为输入分量 `d_i`
在输出分量 `d_j` 上界中的系数；零条目不参与该上界；若第 `j` 行
除 `L_{i→j}` 外均为零，Lip 不等式化为单通道项，对角矩阵时
化简对每个同分量通道 `(j, j)` 均成立。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/--
OET anchor: oet-7fa97eb6e24d5527
**定义（分量通道）**
对 `i, j ∈ I`，有序对 `(i, j)` 为从输入分量 `d_i` 到输出分量 `d_j`
的一个分量通道。 -/
abbrev ComponentChannel (I : Type) : Type := I × I

section Channels

variable {I : Type}

/-- 分量通道的输入分量。 -/
def channelInput (c : ComponentChannel I) : I := c.1

/-- 分量通道的输出分量。 -/
def channelOutput (c : ComponentChannel I) : I := c.2

@[simp] theorem channelInput_apply (i j : I) :
    channelInput (i, j) = i := rfl

@[simp] theorem channelOutput_apply (i j : I) :
    channelOutput (i, j) = j := rfl

/-- 同分量通道 `(i, i)`：输入与输出为同一分量的通道。 -/
def IsSameComponentChannel (c : ComponentChannel I) : Prop := c.1 = c.2

@[simp] theorem isSameComponentChannel_iff {i j : I} :
    IsSameComponentChannel (i, j) ↔ i = j := Iff.rfl

/--
OET anchor: oet-7fa97eb6e24d5527
**单输入通道 / 单行稀疏**：第 `j` 行除 `L_{i→j}` 外均为零，
即通道 `(i, j)` 是第 `j` 行唯一可能非零的条目来源。 -/
def IsSingleInputRow (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/--
OET anchor: oet-7fa97eb6e24d5527
**对角特例（结构部分）**：`L` 为对角矩阵，
即所有异分量通道条目均为零。 -/
def IsDiagonalMatrix (L : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- 对角矩阵的第 `j` 行是只含同分量通道 `(j, j)` 的单输入行。 -/
theorem IsDiagonalMatrix.singleInputRow {L : ChannelMatrix I}
    (h : IsDiagonalMatrix L) (j : I) : IsSingleInputRow L j j :=
  fun k hk => h k j hk

/--
OET anchor: oet-7fa97eb6e24d5527
**零条目不参与上界**：条目 `L_{k→j}` 是输入分量 `d_k` 在输出分量
`d_j` 上界中的系数；若其为零，相应项便不参与该上界——
第 `j` 行的右端和式只须对非零条目求和。 -/
theorem lipRowSum_nonzero_entries {X : Type} {I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : ChannelMatrix I) (j : I) (x y : X) :
    (∑ k : I, L k j * d k x y)
      = ∑ k ∈ Finset.univ.filter (fun k => L k j ≠ 0), L k j * d k x y := by
  refine (Finset.sum_filter_of_ne
    (f := fun k => L k j * d k x y)
    (p := fun k => L k j ≠ 0) ?_).symm
  intro k _ hne h0
  refine hne ?_
  show L k j * d k x y = 0
  rw [h0, zero_mul]

end Channels

section SingleInputRowReduction

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-7fa97eb6e24d5527
**单一输入项行化简（和式形式）**
若第 `j` 行除 `L_{i→j}` 外均为零，则该行右端和式化为单通道项：
`∑_{k∈I} L_{k→j} · f k = L_{i→j} · f i`。 -/
theorem singleInputRow_sum {L : ChannelMatrix I} {i j : I}
    (h : IsSingleInputRow L i j) (f : I → ENNReal) :
    (∑ k : I, L k j * f k) = L i j * f i :=
  Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun k _ hk => by rw [h k hk, zero_mul])

/--
OET anchor: oet-7fa97eb6e24d5527
**单一输入项行化简（证书形式）**
设 `φ ∈ X_op`，`U ⊆ dom(φ)`，受限 Lip 证书 `L ∈ 𝓛(φ)|_U`。
若第 `j` 行除 `L_{i→j}` 外均为零，则对任意 `x, y ∈ U`，Lip 不等式化为
`d_j(φ(x), φ(y)) ≤ ∑_{k∈I} L_{k→j} · d_k(x,y) = L_{i→j} · d_i(x, y)`。 -/
theorem lip_singleInputRow_bound (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsLipMatrixOn d φ L U) (hrow : IsSingleInputRow L i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  calc d j (φ.func x) (φ.func y) ≤ ∑ k : I, L k j * d k x y :=
        hL.lip_bound hx hy j
    _ = L i j * d i x y := singleInputRow_sum hrow _

/--
OET anchor: oet-7fa97eb6e24d5527
**对角特例（化简形式）**
若 `L` 为对角矩阵，上述化简对每个同分量通道 `(j, j)` 均成立：
对任意 `x, y ∈ U` 与 `j ∈ I`，
`d_j(φ(x), φ(y)) ≤ L_{j→j} · d_j(x, y)`。 -/
theorem lip_diagonal_bound (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (hL : IsLipMatrixOn d φ L U)
    (hdiag : IsDiagonalMatrix L) (j : I)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  lip_singleInputRow_bound d φ U L j j hL (hdiag.singleInputRow j) x y hx hy

set_option linter.unusedVariables false in
/--
OET anchor: oet-7fa97eb6e24d5527
**（正文语境封装）** 在扩展规范空间正文语境（`I` 有限非空，`d` 为
扩展伪度量族）下，§ 2.2 单一输入项行化简的原文形式。
底座公理在证明中不使用，一般形式见 `lip_singleInputRow_bound`。 -/
theorem lip_singleInputRow_bound_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I) (hU : U ⊆ dom φ)
    (hL : L ∈ lipFamilyOn d φ U) (hrow : IsSingleInputRow L i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y :=
  lip_singleInputRow_bound d φ U L i j hL hrow x y hx hy

set_option linter.unusedVariables false in
/--
OET anchor: oet-7fa97eb6e24d5527
**（正文语境封装）** 在扩展规范空间正文语境下，
§ 2.2 对角特例的原文形式。 -/
theorem lip_diagonal_bound_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (hU : U ⊆ dom φ)
    (hL : L ∈ lipFamilyOn d φ U) (hdiag : IsDiagonalMatrix L) (j : I)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  lip_diagonal_bound d φ U L hL hdiag j x y hx hy

end SingleInputRowReduction

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean
filename=formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.colip_matrix

/-!
# 第 2 章 算子界：正 co-Lip 通道与族零距反射（义务 CH02-P20、CH02-P21）

形式化正文 § 2.2 命题 2.8：
(i) 正 co-Lip 通道保持正距离；
(ii) 全对角正 co-Lip 矩阵使算子反射族零距关系 `∼_G`。
按 § 1.1 约定，正文不预设族分离性，故 (ii) 的结论只能是
族零距关系而不能加强为点相等；文件末尾给出验证此事的反例模型。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section PositiveChannel

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-f82672ec0dd48f28
co-Lip 不等式中的单通道项下界（命题 2.8 证明中的链式放缩）：
`K_{i→j} · d_i(x,y) ≤ ∑_{k∈I} K_{k→j} · d_k(x,y) ≤ d_j(φ(x), φ(y))`。 -/
theorem IsCoLipMatrixOn.channel_term_le
    {d : I → X → X → ENNReal} {φ : Operator X bot} {K : ChannelMatrix I}
    {U : Set X} (hK : IsCoLipMatrixOn d φ K U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  calc K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
        Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
          (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.colip_bound hx hy j

/--
OET anchor: oet-f82672ec0dd48f28
**命题 2.8 (i)（正 co-Lip 通道保持正距离）**
设 `K ∈ 𝓚(φ)|_U`。若 `K_{i→j} > 0`，则对任意 `x, y ∈ U`：
`d_i(x, y) > 0 ⟹ d_j(φ(x), φ(y)) > 0`。 -/
theorem coLip_pos_channel_preserves_pos (d : I → X → X → ENNReal)
    (φ : Operator X bot) (K : ChannelMatrix I) (U : Set X)
    (hK : IsCoLipMatrixOn d φ K U) (i j : I) (hpos : 0 < K i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hdi : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hprod : K i j * d i x y ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact hpos.ne' h1
    · exact hdi.ne' h2
  calc (0 : ENNReal) < K i j * d i x y :=
        lt_of_le_of_ne (zero_le _) (Ne.symm hprod)
    _ ≤ d j (φ.func x) (φ.func y) := hK.channel_term_le hx hy i j

/--
OET anchor: oet-f82672ec0dd48f28
**命题 2.8 (ii)（全对角正 co-Lip 反射族零距关系）**
设 `K ∈ 𝓚(φ)|_U`。若 `K_{j→j} > 0` 对所有 `j ∈ I` 成立，则 `φ` 反射
族零距关系：对任意 `x, y ∈ U`，`φ(x) ∼_G φ(y) ⟹ x ∼_G y`。 -/
theorem coLip_diag_pos_reflects_zero_related (d : I → X → X → ENNReal)
    (φ : Operator X bot) (K : ChannelMatrix I) (U : Set X)
    (hK : IsCoLipMatrixOn d φ K U) (hdiag : ∀ j : I, 0 < K j j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hxy : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  rcases eq_or_ne (d j x y) 0 with h0 | h0
  · exact h0
  · exact absurd (hxy j) (ne_of_gt
      (coLip_pos_channel_preserves_pos d φ K U hK j j (hdiag j) x y hx hy
        (lt_of_le_of_ne (zero_le _) (Ne.symm h0))))

set_option linter.unusedVariables false in
/--
OET anchor: oet-f82672ec0dd48f28
**（正文语境封装）** 在扩展规范空间正文语境（`I` 有限非空，`d` 为
扩展伪度量族）下，命题 2.8 (i) 的原文形式。
底座公理在证明中不使用，一般形式见 `coLip_pos_channel_preserves_pos`。 -/
theorem coLip_pos_channel_preserves_pos_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) (hK : K ∈ coLipFamilyOn d φ U)
    (i j : I) (hpos : 0 < K i j) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hdi : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  coLip_pos_channel_preserves_pos d φ K U hK i j hpos x y hx hy hdi

set_option linter.unusedVariables false in
/--
OET anchor: oet-f82672ec0dd48f28
**（正文语境封装）** 在扩展规范空间正文语境下，命题 2.8 (ii) 的
原文形式。底座公理在证明中不使用。 -/
theorem coLip_diag_pos_reflects_zero_related_textbook {X : Type} {bot : X}
    {I : Type} [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ j : I, 0 < K j j) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hxy : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y :=
  coLip_diag_pos_reflects_zero_related d φ K U hK hdiag x y hx hy hxy

end PositiveChannel

/-! ### 命题 2.8 (ii) 的结论不能加强为点相等：反例模型 -/

namespace ReflectionNotStrengthenable

/-- 反例底座 `X = {⊥, a, b}`：以 `Option (Fin 2)` 实现，`none` 为吸收元。 -/
abbrev Xc : Type := Option (Fin 2)

/-- 吸收元 `⊥`。 -/
def botc : Xc := none

/-- 单分量指标集。 -/
abbrev Ic : Type := Fin 1

/--
唯一分量上的扩展伪度量：两个非吸收点之间距离为 `0`，与吸收元的
距离为 `⊤`。该规范族不分离：`some 0 ∼_G some 1` 但两点不同。 -/
def dc : Ic → Xc → Xc → ENNReal := fun _ x y =>
  if x.isNone = y.isNone then 0 else ⊤

/-- 恒等算子 `id_X ∈ X_op`。 -/
def phic : Operator Xc botc := operator_identity

/-- 受限域 `U = {a, b}`（不含吸收元）。 -/
def Uc : Set Xc := {some 0, some 1}

/-- 单分量下的全 `1` 矩阵：`φ = id` 的 co-Lip 证书。 -/
def Kc : ChannelMatrix Ic := fun _ _ => 1

/-- 反射结论中不可加强为相等的两个点。 -/
def xc : Xc := some 0

def yc : Xc := some 1

theorem Uc_nonempty : Uc.Nonempty := ⟨some 0, by simp [Uc]⟩

theorem Uc_subset_dom : Uc ⊆ dom phic := by
  intro x hx
  simp [Uc] at hx
  rcases hx with rfl | rfl
  · exact Option.some_ne_none 0
  · exact Option.some_ne_none 1

theorem dc_is_gauge : ∀ i : Ic, ExtendedPseudoMetric Xc botc (dc i) := by
  intro i
  refine
    { nonabsorbing := ⟨some 0, by simp [botc]⟩
      dist_self := fun x => by simp [dc]
      symm := fun x y => by
        rcases hx : x.isNone with _ | _ <;> rcases hy : y.isNone with _ | _ <;>
          simp [dc, hx, hy]
      triangle := fun x y z => by
        rcases hx : x.isNone with _ | _ <;> rcases hy : y.isNone with _ | _ <;>
          rcases hz : z.isNone with _ | _ <;>
          simp [dc, hx, hy, hz, add_top]
      isolate_bot := fun x hx => by
        cases x with
        | none => exact (hx rfl).elim
        | some v => simp [dc, botc] }

theorem Kc_is_coLip : IsCoLipMatrixOn dc phic Kc Uc := by
  refine ⟨Uc_nonempty, Uc_subset_dom, ?_⟩
  intro x _hx y _hy j
  fin_cases j
  simp only [Fin.sum_univ_one, Kc, one_mul]
  exact le_rfl

theorem Kc_diag_pos : ∀ j : Ic, 0 < Kc j j := fun _ => by simp [Kc]

theorem xc_mem : xc ∈ Uc := by simp [xc, Uc]

theorem yc_mem : yc ∈ Uc := by simp [yc, Uc]

theorem phic_zero_related : GaugeZeroRelated dc (phic.func xc) (phic.func yc) := by
  intro i
  show dc i (some 0) (some 1) = 0
  simp [dc]

theorem xc_ne_yc : xc ≠ yc := by simp [xc, yc]

/--
OET anchor: oet-f82672ec0dd48f28
**命题 2.8 (ii) 的结论不能加强为点相等**
本模型满足正文全部语境与命题 2.8 (ii) 的全部前提：
`(Xc, dc, botc)` 是真正的（非分离）扩展规范空间，`Kc ∈ 𝓚(phic)|_{Uc}`，
全对角条目为正，`xc, yc ∈ Uc`，且 `phic(xc) ∼_G phic(yc)`。
由命题 2.8 (ii) 得 `xc ∼_G yc`，但 `xc ≠ yc`。
因此反射结论只能是族零距关系 `x ∼_G y`，不能加强为点相等 `x = y`。 -/
theorem coLip_reflection_not_strengthenable :
    (∀ i : Ic, ExtendedPseudoMetric Xc botc (dc i))
      ∧ IsCoLipMatrixOn dc phic Kc Uc
      ∧ (∀ j : Ic, 0 < Kc j j)
      ∧ xc ∈ Uc
      ∧ yc ∈ Uc
      ∧ GaugeZeroRelated dc (phic.func xc) (phic.func yc)
      ∧ GaugeZeroRelated dc xc yc
      ∧ xc ≠ yc :=
  ⟨dc_is_gauge, Kc_is_coLip, Kc_diag_pos, xc_mem, yc_mem, phic_zero_related,
    coLip_diag_pos_reflects_zero_related dc phic Kc Uc Kc_is_coLip Kc_diag_pos
      xc yc xc_mem yc_mem phic_zero_related,
    xc_ne_yc⟩

end ReflectionNotStrengthenable

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean
filename=formal_oet/vol_01/ch_02_operator_bounds/exercise_02_02.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.colip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.component_channel
import formal_oet.vol_01.ch_02_operator_bounds.colip_reflection

/-!
# 第 2 章习题 2.2：对角输入项的标量双侧界（义务 CH02-P25）

设 `φ ∈ X_op`，`U ⊆ dom(φ)`，`j ∈ I`，给定 `L ∈ 𝓛(φ)|_U` 与
`K ∈ 𝓚(φ)|_U`。若 `L` 的第 `j` 行只保留对角输入项
（`L_{k→j} = 0`，`∀ k ≠ j`），则对任意 `x, y ∈ U` 有标量双侧不等式
`K_{j→j} · d_j(x,y) ≤ d_j(φ(x),φ(y)) ≤ L_{j→j} · d_j(x,y)`。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section Exercise0202

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-6a98a58b5bc95360
**习题 2.2（对角输入项的标量双侧界）**
设 `φ ∈ X_op`，`U ⊆ dom(φ)`，`j ∈ I`。给定 `L ∈ 𝓛(φ)|_U` 与
`K ∈ 𝓚(φ)|_U`。若 `φ` 在 `U` 上关于输出分量 `d_j` 满足只保留对角
输入项的 Lip 上界 `L_{k→j} = 0`（`∀ k ≠ j`），则对任意 `x, y ∈ U`
有标量双侧不等式：
`K_{j→j} · d_j(x, y) ≤ d_j(φ(x), φ(y)) ≤ L_{j→j} · d_j(x, y)`。 -/
theorem scalar_two_sided_bound (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L K : ChannelMatrix I) (j : I)
    (hL : IsLipMatrixOn d φ L U) (hK : IsCoLipMatrixOn d φ K U)
    (hsparse : IsSingleInputRow L j j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y)
      ∧ d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · exact hK.channel_term_le hx hy j j
  · calc d j (φ.func x) (φ.func y) ≤ ∑ k : I, L k j * d k x y :=
        hL.lip_bound hx hy j
    _ = L j j * d j x y := singleInputRow_sum hsparse _

set_option linter.unusedVariables false in
/--
OET anchor: oet-6a98a58b5bc95360
**（正文语境封装）** 在扩展规范空间正文语境（`I` 有限非空，`d` 为
扩展伪度量族）下，习题 2.2 的原文形式。 -/
theorem scalar_two_sided_bound_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (L K : ChannelMatrix I) (j : I) (hU : U ⊆ dom φ)
    (hL : L ∈ lipFamilyOn d φ U) (hK : K ∈ coLipFamilyOn d φ U)
    (hsparse : ∀ k : I, k ≠ j → L k j = 0)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y)
      ∧ d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  scalar_two_sided_bound d φ U L K j hL hK hsparse x y hx hy

end Exercise0202

end formal_oet.vol_01.ch_02_operator_bounds
```

```json
filename=alignment.json
{
  "case_id": "LCH01",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.LipBoundOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrix"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrixOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamily"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_lipFamily"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_lipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrix.lip_bound"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrixOn.subset_dom"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrixOn.lip_bound"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamily_eq_lipFamilyOn_dom"}
      ],
      "representation": "对象：非负矩阵 L 表示为 ChannelMatrix I（义务 D03），条目 L i j = L_{i→j}，取值于 ℝ̄₊ = ENNReal（非负由类型保证）；算子 φ 为冻结模块的 Operator X bot（φ.func 即 φ(·)）；d : I → X → X → ENNReal 为分量伪度量族参数（正文规范结构 G 的分量；四条伪度量公理在这一定义中不被使用，故 d 取任意族，陈述不弱于原文语境）。参数与量词：全域谓词 IsLipMatrix d φ L := LipBoundOn d φ L (dom φ)，即 ∀ x ∈ dom(φ), ∀ y ∈ dom(φ), ∀ j ∈ I, d_j(φ(x),φ(y)) ≤ ∑_{i∈I} L_{i→j}·d_i(x,y)，对应 L ∈ 𝓛(φ)。受限谓词 IsLipMatrixOn d φ L U := (U ⊆ dom(φ)) ∧ 同一不等式对 ∀ x,y ∈ U, ∀ j ∈ I 成立，对应 L ∈ 𝓛(φ)|_U；正文记号 𝓛(φ)|_U 以 U ⊆ dom(φ) 为定义前提，故作为侧条件并入谓词（LipBoundOn 为纯不等式层）。证书族：lipFamily d φ = {L | IsLipMatrix d φ L} 即 𝓛(φ)，lipFamilyOn d φ U = {L | IsLipMatrixOn d φ L U} 即 𝓛(φ)|_U；mem_lipFamily/mem_lipFamilyOn 为成员资格等价，lipFamily_eq_lipFamilyOn_dom 给出 𝓛(φ) = 𝓛(φ)|_{dom(φ)}。结论强度：定义与原文逐条对应，不预设证书族中最优矩阵的存在。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipBoundOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCoLipMatrixOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_coLipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCoLipMatrixOn.nonempty"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCoLipMatrixOn.subset_dom"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCoLipMatrixOn.colip_bound"}
      ],
      "representation": "对象同 D01（ChannelMatrix I 的 K、Operator X bot 的 φ、任意分量族 d）。参数与量词：纯不等式层 CoLipBoundOn d φ K U：∀ x ∈ U, ∀ y ∈ U, ∀ j ∈ I, ∑_{i∈I} K_{i→j}·d_i(x,y) ≤ d_j(φ(x),φ(y))。受限谓词 IsCoLipMatrixOn d φ K U := U.Nonempty ∧ (U ⊆ dom(φ)) ∧ CoLipBoundOn d φ K U，即 K ∈ 𝓚(φ)|_U；按正文约定（凡出现 𝓚(φ)|_U 均包含非空性条件 U ≠ ∅），非空条件与子集条件均并入谓词。证书族：coLipFamilyOn d φ U = {K | IsCoLipMatrixOn d φ K U} 即 𝓚(φ)|_U；mem_coLipFamilyOn 为成员资格等价；nonempty/subset_dom/colip_bound 提取三组成部分。原文只定义带非空前提的受限 co-Lip 矩阵（全域情形 𝓚(φ)|_{dom(φ)} 是其在 U = dom(φ) 的特例），本形式化与之严格对应，且不预设上确界矩阵的存在。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ChannelMatrix"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.toRowMatrix"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.toRowMatrix_apply"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.outputRow"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.inputCol"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.outputRow_apply"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.inputCol_apply"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.toRowMatrix_eq_outputRow"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul_apply"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.toRowMatrix_matMul"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul_assoc"}
      ],
      "representation": "对象：扩展非负矩阵表示为 ChannelMatrix I := I → I → ENNReal，条目 L i j 即正文的 L_{i→j}（输入分量 i、输出分量 j），ℝ̄₊ 对应 ENNReal。行列指标约定：toRowMatrix L 为行列约定下的矩阵，toRowMatrix_apply 即正文 (𝐋)_{ji} = L_{i→j}（第 j 行汇集指向输出分量 d_j 的系数，第 i 列汇集自输入分量 d_i 出发的系数；outputRow L j 与 inputCol L i 分别显式给出第 j 行与第 i 列，toRowMatrix_eq_outputRow 连接二者）。乘法：matMul L2 L1 i j = ∑_{k∈I} L2 k j * L1 i k，即命题 2.2 证明中的代数矩阵乘法元素 (𝐋⁽²⁾·𝐋⁽¹⁾)_{i→j}（左因子后作用）；toRowMatrix_matMul 证明它与行列约定下的标准矩阵乘法 Matrix.mul 逐元素一致，matMul_assoc 给出结合律（ℝ̄₊ 有限和的分配律与次序交换）。指标集的有限性由 [Fintype I] 承担（正文 I 为有限非空指标集；非空性在这些定义与命题中不使用，故未假设，陈述不弱于原文）。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelInput"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelOutput"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelInput_apply"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelOutput_apply"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsSameComponentChannel"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.isSameComponentChannel_iff"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsSingleInputRow"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagonalMatrix"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagonalMatrix.singleInputRow"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipRowSum_nonzero_entries"}
      ],
      "representation": "分量通道：ComponentChannel I := I × I，有序对 (i, j) 从输入分量 d_i（channelInput）指向输出分量 d_j（channelOutput）；IsSameComponentChannel 刻画同分量通道 (i,i)。单输入通道/单行稀疏：IsSingleInputRow L i j := ∀ k : I, k ≠ i → L k j = 0，即正文第 j 行除 L_{i→j} 外均为零。对角特例：IsDiagonalMatrix L := ∀ i j, i ≠ j → L i j = 0；IsDiagonalMatrix.singleInputRow 证明对角矩阵的第 j 行是只含同分量通道 (j,j) 的单输入行。条目角色与零条目缺席：正文条目 L_{k→j} 是输入分量 d_k 在输出分量 d_j 上界中的系数、若其为零相应项不参与该上界，形式化为 lipRowSum_nonzero_entries：第 j 行右端和式 ∑_{k∈I} L_{k→j}·d_k(x,y) 等于仅对非零条目（univ.filter (fun k => L k j ≠ 0)）求和。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.singleInputRow_sum"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_singleInputRow_bound"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_diagonal_bound"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_singleInputRow_bound_textbook"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channel.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_diagonal_bound_textbook"}
      ],
      "representation": "前提：φ ∈ X_op、U ⊆ dom(φ)、受限 Lip 证书 L ∈ 𝓛(φ)|_U（合并为 hL : IsLipMatrixOn d φ L U，义务 D01/D07 记号）、单行稀疏 IsSingleInputRow L i j。结论分两层：singleInputRow_sum 给出行化和简 ∑_{k∈I} L_{k→j}·f k = L_{i→j}·f i（对任意 f : I → ENNReal，取 f k = d_k(x,y) 即正文的 ∑ L_{k→j}d_k(x,y) = L_{i→j}d_i(x,y)）；lip_singleInputRow_bound 给出证书形式的完整化简：对任意 x, y ∈ U（∀ 量词以参数加成员假设 hx : x ∈ U、hy : y ∈ U 表示），d_j(φ(x),φ(y)) ≤ L_{i→j}·d_i(x,y)，由 Lip 不等式与和式化简传递得到，对应正文化简链的两步。对角特例：lip_diagonal_bound——若 IsDiagonalMatrix L，则对每个同分量通道 (j,j) 与任意 x,y ∈ U 有 d_j(φ(x),φ(y)) ≤ L_{j→j}·d_j(x,y)。两个 _textbook 声明给出正文语境（I 有限非空、d 为扩展伪度量族、U ⊆ dom(φ) 显式列出）下的原文形式；底座公理在证明中不使用，故一般形式陈述更强。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCoLipMatrixOn.channel_term_le"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_pos_channel_preserves_pos"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_pos_channel_preserves_pos_textbook"}
      ],
      "representation": "命题 2.8 (i)。前提：K ∈ 𝓚(φ)|_U（hK : IsCoLipMatrixOn d φ K U，含非空性与 U ⊆ dom(φ) 侧条件）、K_{i→j} > 0（hpos : 0 < K i j）、x, y ∈ U、d_i(x,y) > 0（hdi）。结论：0 < d_j(φ(x),φ(y))。证明与原文链式放缩一致：IsCoLipMatrixOn.channel_term_le 先给出 d_j(φ(x),φ(y)) ≥ ∑_{k∈I} K_{k→j}·d_k(x,y) ≥ K_{i→j}·d_i(x,y)（co-Lip 不等式加非负单项不超过全和），再由 ENNReal 无零因子（mul_eq_zero）得两个正量之积严格正，从而结论严格正。coLip_pos_channel_preserves_pos_textbook 为正文语境（I 有限非空、d 为扩展伪度量族）下的原文形式；其证明不使用底座公理，故一般形式陈述更强。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_diag_pos_reflects_zero_related"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_diag_pos_reflects_zero_related_textbook"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Xc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.botc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Ic"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.dc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.phic"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Uc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Kc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.xc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.yc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Uc_nonempty"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Uc_subset_dom"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.dc_is_gauge"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Kc_is_coLip"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.Kc_diag_pos"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.xc_mem"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.yc_mem"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.phic_zero_related"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.xc_ne_yc"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_reflection.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ReflectionNotStrengthenable.coLip_reflection_not_strengthenable"}
      ],
      "representation": "命题 2.8 (ii)。前提：K ∈ 𝓚(φ)|_U（含非空与子集侧条件）、∀ j ∈ I, K_{j→j} > 0（hdiag : ∀ j : I, 0 < K j j）、x, y ∈ U、φ(x) ∼_G φ(y)（hxy : GaugeZeroRelated d (φ.func x) (φ.func y)，复用冻结模块 ch_01 的族零距关系定义，即 ∀ i, d_i(φ(x),φ(y)) = 0）。结论：GaugeZeroRelated d x y，即 x ∼_G y（∀ i ∈ I 内置于该定义）。证明与原文一致：对每个 j，若 d_j(x,y) ≠ 0 则由 (i) 取同分量通道 (j,j) 得 d_j(φ(x),φ(y)) > 0，与 φ(x) ∼_G φ(y) 矛盾，故 d_j(x,y) = 0。不加强为点相等：ReflectionNotStrengthenable 命名空间给出满足全部前提的具体模型——Xc = Option (Fin 2)（三点集，botc = none 为吸收元）、Ic = Fin 1、dc 为非吸收点间距离 0、与吸收元距离 ⊤ 的分量（dc_is_gauge 验证四个伪度量公理与吸收元隔离，即 (Xc, dc, botc) 是真正的扩展规范空间且不分离）、phic = 恒等算子、Uc = {some 0, some 1}、Kc ≡ 1（Kc_is_coLip 验证其为 phic 在 Uc 上的 co-Lip 证书）、xc = some 0、yc = some 1；coLip_reflection_not_strengthenable 汇总：规范空间公理 + 全部命题前提 + φ(xc) ∼_G φ(yc) + 由本定理推出的 xc ∼_G yc + xc ≠ yc 同时成立，因此反射结论只能是族零距关系而不能加强为点相等（正文 §1.1 不预设族分离性约定的具体体现）。_textbook 声明为正文语境下的原文形式。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/exercise_02_02.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/exercise_02_02.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound_textbook"}
      ],
      "representation": "习题 2.2。前提：φ ∈ X_op、U ⊆ dom(φ)、j ∈ I、L ∈ 𝓛(φ)|_U（hL : IsLipMatrixOn d φ L U）、K ∈ 𝓚(φ)|_U（hK : IsCoLipMatrixOn d φ K U，含非空性条件）、只保留对角输入项的行稀疏 L_{k→j} = 0 (∀ k ≠ j)（hsparse : IsSingleInputRow L j j，义务 D07 的谓词）。结论：对任意 x, y ∈ U（∀ 以参数加成员假设表示），标量双侧不等式 K_{j→j}·d_j(x,y) ≤ d_j(φ(x),φ(y)) ∧ d_j(φ(x),φ(y)) ≤ L_{j→j}·d_j(x,y)（以合取表示双侧）。证明：下界由 co-Lip 不等式的单对角通道项（IsCoLipMatrixOn.channel_term_le，义务 P20 的引理）给出；上界由 Lip 不等式（hL.lip_bound）加行和化简（singleInputRow_sum，义务 P19 的引理）给出。scalar_two_sided_bound_textbook 为正文语境（I 有限非空、d 为扩展伪度量族、hsparse 按原文写为 ∀ k ≠ j, L k j = 0）下的原文形式。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19", "CH02-P20"]
    }
  ]
}
```

**出处说明**：形式化对象取自 Zhe Li (Glen Li / glenzli)，The Operator Evolution Theory, Vol. I, v1.0.0（DOI 10.5281/zenodo.21457931，CC BY 4.0），按题面选段义务清单对第 2 章 §2.1–§2.2 及习题 2.2 的指定条目做 Lean 形式化；冻结前置模块 `formal_oet.vol_01.ch_01_foundations` 保持原样导入，未做任何修改。