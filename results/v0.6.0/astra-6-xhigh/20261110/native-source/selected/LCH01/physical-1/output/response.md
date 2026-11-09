8 项全部完成。各模块及 Main.lean 已用指定 Lean/mathlib 编译通过；公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。冻结前置模块未修改，按要求不重复交付。

数学来源：Zhe Li（Glen Li / glenzli，[ORCID](https://orcid.org/0009-0006-6536-3453)），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[公开仓库](https://gitlab.com/glenzli/oet-public)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下为基于所给原文新编写的 Lean 形式化。

```toml filename=lakefile.toml
name = "lch01"
version = "0.1.0"
defaultTargets = ["LCH01", "Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "formal_oet"
globs = ["formal_oet.+"]

[[lean_lib]]
name = "LCH01"
globs = ["LCH01.+"]

[[lean_lib]]
name = "Main"
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```lean filename=LCH01/MatrixBounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Formalization of the selected definitions in Chapter 2 of
Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I.
Source: https://glenzli.com/books/oet/ ; CC BY 4.0.
This file is a new Lean formalization, not an author-supplied implementation.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-- The background gauge axioms, using the frozen prerequisite definition. -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X bot (d i)

/-- Rows are output components; columns are input components. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- The textbook entry `M_{i → j}` is the ordinary matrix entry `M j i`. -/
def entry {I : Type} (M : ChannelMatrix I) (i j : I) : ENNReal := M j i

/-- The second step acts after the first step. -/
noncomputable def matrixComp {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) : ChannelMatrix I := M₂ * M₁

theorem entry_matrixComp {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) (i j : I) :
    entry (matrixComp M₂ M₁) i j =
      ∑ k, entry M₂ k j * entry M₁ i k := by
  exact Matrix.mul_apply

/-- A component channel is an ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

def channelCoefficient {I : Type}
    (M : ChannelMatrix I) (c : ComponentChannel I) : ENNReal :=
  entry M c.1 c.2

/-- Output row `j` may use only input `i`; that entry may itself be zero. -/
def RowSupported {I : Type} (M : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k, k ≠ i → entry M k j = 0

/-- Each output row uses only the input with the same index. -/
def IsDiagonal {I : Type} (M : ChannelMatrix I) : Prop :=
  ∀ j, RowSupported M j j

section Bounds

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

/-- Restricted Lip legality includes the specified domain containment. -/
def LipOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      G.d j (φ.func x) (φ.func y) ≤ ∑ i, entry L i j * G.d i x y

def Lip (G : Gauge X I bot) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  LipOn G φ (dom φ) L

def lipMatricesOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  {L | LipOn G φ U L}

def lipMatrices (G : Gauge X I bot) (φ : Operator X bot) :
    Set (ChannelMatrix I) :=
  {L | Lip G φ L}

/-- Nonemptiness is part of co-Lip legality, including for the full domain. -/
def CoLipOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      (∑ i, entry K i j * G.d i x y) ≤ G.d j (φ.func x) (φ.func y)

def coLipMatricesOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  {K | CoLipOn G φ U K}

/-- The scalar inequality associated with one input/output channel. -/
def ChannelLipOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (i j : I) (l : ENNReal) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U,
      G.d j (φ.func x) (φ.func y) ≤ l * G.d i x y

end Bounds

end LCH01
```

```lean filename=LCH01/Channels.lean
import LCH01.MatrixBounds

/-!
Selected channel results from Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, Volume I, Chapter 2.
Source: https://glenzli.com/books/oet/ ; CC BY 4.0.
The proofs below are a new Lean formalization of the supplied source.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-- The complete row sum equals its sole potentially nonzero input term. -/
theorem row_sum_eq {I : Type} [Fintype I]
    {M : ChannelMatrix I} {i j : I}
    (hrow : RowSupported M i j) (v : I → ENNReal) :
    (∑ k, entry M k j * v k) = entry M i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

section Channels

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable {G : Gauge X I bot} {φ : Operator X bot} {U : Set X}

/-- CH02-P19: row sparsity yields a scalar channel Lip bound. -/
theorem lip_single_input {L : ChannelMatrix I} {i j : I}
    (hL : LipOn G φ U L) (hrow : RowSupported L i j) :
    ChannelLipOn G φ U i j (entry L i j) := by
  refine ⟨hL.1, ?_⟩
  intro x hx y hy
  calc
    G.d j (φ.func x) (φ.func y) ≤
        ∑ k, entry L k j * G.d k x y := hL.2 x hx y hy j
    _ = entry L i j * G.d i x y := row_sum_eq hrow (fun k => G.d k x y)

/-- CH02-P19: the specialization for every diagonal channel. -/
theorem lip_diagonal {L : ChannelMatrix I}
    (hL : LipOn G φ U L) (hdiag : IsDiagonal L) :
    ∀ j, ChannelLipOn G φ U j j (entry L j j) := by
  intro j
  exact lip_single_input hL (hdiag j)

/-- Each nonnegative input term is bounded by the co-Lip row sum. -/
theorem coLip_term_le {K : ChannelMatrix I}
    (hK : CoLipOn G φ U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (i j : I) :
    entry K i j * G.d i x y ≤ G.d j (φ.func x) (φ.func y) := by
  calc
    entry K i j * G.d i x y ≤ ∑ k, entry K k j * G.d k x y :=
      Finset.single_le_sum (f := fun k => entry K k j * G.d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ G.d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

/-- CH02-P20: a positive co-Lip channel preserves positive distance. -/
theorem positive_coLip_channel {K : ChannelMatrix I} {i j : I}
    (hK : CoLipOn G φ U K) (hchannel : 0 < entry K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hxy : 0 < G.d i x y) :
    0 < G.d j (φ.func x) (φ.func y) := by
  have hprod : 0 < entry K i j * G.d i x y :=
    ENNReal.mul_pos (ne_of_gt hchannel) (ne_of_gt hxy)
  exact lt_of_lt_of_le hprod (coLip_term_le hK hx hy i j)

/-- CH02-P21: reflect family zero distance, without any separation assumption. -/
theorem coLip_reflects_gaugeZero {K : ChannelMatrix I}
    (hK : CoLipOn G φ U K) (hdiag : ∀ j, 0 < entry K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated G.d (φ.func x) (φ.func y)) :
    GaugeZeroRelated G.d x y := by
  intro j
  apply le_antisymm _ (zero_le _)
  by_contra h
  have hpos := positive_coLip_channel hK (hdiag j) hx hy (lt_of_not_ge h)
  rw [hzero j] at hpos
  exact (lt_irrefl 0) hpos

/-- CH02-P25 (Exercise 2.2): both scalar bounds, for any selected output row. -/
theorem scalar_two_sided {L K : ChannelMatrix I} {j : I}
    (hL : LipOn G φ U L) (hK : CoLipOn G φ U K)
    (hrow : RowSupported L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.d j x y ≤ G.d j (φ.func x) (φ.func y) ∧
      G.d j (φ.func x) (φ.func y) ≤ entry L j j * G.d j x y := by
  exact ⟨coLip_term_le hK hx hy j j,
    (lip_single_input hL hrow).2 x hx y hy⟩

end Channels

end LCH01
```

```lean filename=Main.lean
import LCH01.MatrixBounds
import LCH01.Channels
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
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.Gauge"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.LipOn"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.Lip"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.lipMatricesOn"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.lipMatrices"}
      ],
      "representation": {
        "objects": "Gauge.d 是原文规范族；Gauge.metric 使用冻结的 ExtendedPseudoMetric，包含非吸收点存在及四条公理。算子及 dom 均直接使用冻结模块。",
        "parameters": "X、bot、有限非空 I、G、φ、U 及 ENNReal 矩阵 L；Gauge 的类型参数显式要求 Fintype I 与 Nonempty I。",
        "quantifiers": "LipOn 包含 U ⊆ dom φ，并对所有 x∈U、y∈U、j∈I 要求原文上界；Lip 取 U=dom φ。",
        "conclusion": "lipMatricesOn 和 lipMatrices 分别是上述谓词的集合推导式；不要求存在最优矩阵。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.CoLipOn"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.coLipMatricesOn"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.coLip_term_le"}
      ],
      "representation": {
        "objects": "CoLipOn 是合法受限 co-Lip 矩阵谓词；coLipMatricesOn 是其证书族。",
        "parameters": "同一规范空间、算子 φ、子集 U 和 ENNReal 矩阵 K；条目允许无穷大。",
        "quantifiers": "谓词同时包含 U.Nonempty、U ⊆ dom φ，以及所有 x∈U、y∈U、j∈I 的下界不等式。",
        "conclusion": "原文的 ≥ 表示为有限和 ≤ 输出距离；全域情形直接取 U=dom φ，仍要求非空。辅助引理从该有限和下界推出任意单项下界。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.ChannelMatrix"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.entry"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.matrixComp"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.entry_matrixComp"}
      ],
      "representation": {
        "objects": "ChannelMatrix I = Matrix I I ENNReal。",
        "parameters": "entry M i j = M j i，i 是输入列，j 是输出行。",
        "quantifiers": "对任意有限 I、矩阵 M₂、M₁ 及 i、j，给出乘积条目公式。",
        "conclusion": "matrixComp M₂ M₁ 是标准矩阵乘积 M₂*M₁；其 i→j 条目等于 ∑k (M₂)_{k→j}(M₁)_{i→k}，第二步在左。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.ComponentChannel"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.channelCoefficient"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.RowSupported"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.IsDiagonal"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.ChannelLipOn"}
      ],
      "representation": {
        "objects": "ComponentChannel I = I×I，依次表示输入与输出；channelCoefficient 取对应矩阵条目。",
        "parameters": "RowSupported M i j 表示第 j 行只能保留输入 i；所保留条目也允许为零。",
        "quantifiers": "RowSupported 对所有 k≠i 要求 M_{k→j}=0；IsDiagonal 要求所有 j 的 RowSupported M j j。",
        "conclusion": "ChannelLipOn 包含 U ⊆ dom φ，并对所有 x,y∈U 表达 d_j(φx,φy)≤l*d_i(x,y)。稀疏行和对角矩阵产生此界的证明见 CH02-P19。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.row_sum_eq"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.lip_single_input"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.lip_diagonal"}
      ],
      "representation": {
        "objects": "一般稀疏行的有限和恒等式及其 Lip 界应用。",
        "parameters": "任意合法受限 Lip 矩阵 L、输入 i、输出 j，假设第 j 行所有 k≠i 的条目为零。",
        "quantifiers": "row_sum_eq 对任意 ENNReal 向量成立；lip_single_input 对所有 x,y∈U 成立；lip_diagonal 对所有 j 成立。",
        "conclusion": "有限和严格等于 L_{i→j}d_i(x,y)，故输出距离被该单项控制；对角特例取 i=j。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.positive_coLip_channel"}
      ],
      "representation": {
        "objects": "命题 2.8(i) 的正 co-Lip 通道。",
        "parameters": "K 满足 CoLipOn G φ U K，且 K_{i→j}>0。",
        "quantifiers": "任意 x,y∈U，假设 d_i(x,y)>0；i、j 均任意。",
        "conclusion": "得到 d_j(φx,φy)>0。使用 ENNReal 正乘积性质，未附加条目或距离有限的条件。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.coLip_reflects_gaugeZero"}
      ],
      "representation": {
        "objects": "命题 2.8(ii)；族零距关系直接使用冻结定义 GaugeZeroRelated。",
        "parameters": "K 是合法受限 co-Lip 矩阵，所有对角条目 K_{j→j}>0。",
        "quantifiers": "对任意 x,y∈U，若所有输出分量距离为零，则逐一证明所有输入分量距离为零。",
        "conclusion": "结论为 GaugeZeroRelated G.d x y；没有分离性前提，也没有点相等结论。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.scalar_two_sided"}
      ],
      "representation": {
        "objects": "习题 2.2 的标量双侧界。",
        "parameters": "同一 φ、U 上合法的 Lip 矩阵 L 和 co-Lip 矩阵 K，任意输出 j；仅要求 L 的第 j 行其他输入条目为零。",
        "quantifiers": "对所有 x,y∈U 成立；U 的非空性由 CoLipOn 保留。不要求 K 稀疏或 K_{j→j}>0。",
        "conclusion": "以合取表达 K_{j→j}d_j(x,y)≤d_j(φx,φy)≤L_{j→j}d_j(x,y)，完整保留两侧不等式。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```