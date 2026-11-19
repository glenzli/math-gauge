**8 项义务均已完成。** 项目已使用 Lean 4.29.1 和指定提交的 mathlib 离线通过 `lake build`。`leanchecker` 已复核 `LCH01` 和 `Main`。`alignment.json` 中的 21 个声明均已逐一核对，公理依赖仅涉及 `propext`、`Classical.choice` 和 `Quot.sound`。

```lean filename=LCH01.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Operations
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
本文件形式化 Zhe Li（Glen Li / glenzli）《The Operator Evolution Theory》
第一卷 v1.0.0 的 §2.1、§2.2 与习题 2.2 选段。
[原作](https://glenzli.com/books/oet/) · [DOI](https://doi.org/10.5281/zenodo.21457931) ·
[原作仓库](https://gitlab.com/glenzli/oet-public) ·
[ORCID](https://orcid.org/0009-0006-6536-3453) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

noncomputable section

/-- 第一章的有限非空规范族，每个分量采用冻结模块的扩展伪度量。 -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  component : ∀ i, ExtendedPseudoMetric X bot (dist i)

variable {X I : Type} {bot : X}

/-! ### §2.1 矩阵约定与证书族 -/

/-- 输入 i 对应列，输出 j 对应行。 -/
abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

def entry (M : BoundMatrix I) (i j : I) : ENNReal := M j i

theorem entry_mul [Fintype I] (B A : BoundMatrix I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

section Certificates

variable [Fintype I] [Nonempty I] (G : Gauge X I bot) (φ : Operator X bot)

def rowSum (M : BoundMatrix I) (j : I) (x y : X) : ENNReal :=
  ∑ i, entry M i j * G.dist i x y

def IsLipOn (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    G.dist j (φ.func x) (φ.func y) ≤ rowSum G L j x y

def IsLip (L : BoundMatrix I) : Prop := IsLipOn G φ (dom φ) L

def lipMatricesOn (U : Set X) : Set (BoundMatrix I) := {L | IsLipOn G φ U L}

def lipMatrices : Set (BoundMatrix I) := {L | IsLip G φ L}

def IsCoLipOn (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    rowSum G K j x y ≤ G.dist j (φ.func x) (φ.func y)

def coLipMatricesOn (U : Set X) : Set (BoundMatrix I) := {K | IsCoLipOn G φ U K}

end Certificates

/-! ### §2.2 分量通道 -/

/-- (i, j) 表示从输入分量 i 到输出分量 j 的通道。 -/
abbrev Channel (I : Type) := I × I

def OnlyInput (M : BoundMatrix I) (c : Channel I) : Prop :=
  ∀ k, k ≠ c.1 → entry M k c.2 = 0

theorem channel_term_zero {M : BoundMatrix I} (c : Channel I)
    (h : entry M c.1 c.2 = 0) (r : ENNReal) : entry M c.1 c.2 * r = 0 := by
  rw [h, zero_mul]

theorem isDiag_iff_onlyInput (M : BoundMatrix I) :
    M.IsDiag ↔ ∀ j, OnlyInput M (j, j) := by
  constructor
  · intro h j k hk
    exact h (Ne.symm hk)
  · intro h j k hjk
    exact h j k (Ne.symm hjk)

variable [Fintype I] [Nonempty I] {G : Gauge X I bot} {φ : Operator X bot}
variable {U : Set X} {L K : BoundMatrix I} {x y : X} {i j : I}

theorem rowSum_single (M : BoundMatrix I) (hrow : OnlyInput M (i, j)) (x y : X) :
    rowSum G M j x y = entry M i j * G.dist i x y := by
  unfold rowSum
  apply Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
  intro k _ hk
  exact channel_term_zero (k, j) (hrow k hk) (G.dist k x y)

theorem lip_single_input (hL : L ∈ lipMatricesOn G φ U) (hrow : OnlyInput L (i, j))
    (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L i j * G.dist i x y := by
  calc
    _ ≤ rowSum G L j x y := hL.2 x hx y hy j
    _ = _ := rowSum_single L hrow x y

theorem lip_diagonal (hL : L ∈ lipMatricesOn G φ U) (hd : L.IsDiag) (j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  lip_single_input hL ((isDiag_iff_onlyInput L).mp hd j) hx hy

/-- co-Lip 行和控制该行中的每个非负项。 -/
theorem coLip_term_le (hK : K ∈ coLipMatricesOn G φ U) (i j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    entry K i j * G.dist i x y ≤ G.dist j (φ.func x) (φ.func y) := by
  calc
    _ ≤ rowSum G K j x y :=
      Finset.single_le_sum (fun k _ => zero_le (entry K k j * G.dist k x y))
        (Finset.mem_univ i)
    _ ≤ _ := hK.2.2 x hx y hy j

/-- 命题 2.8(i)。 -/
theorem positive_channel (hK : K ∈ coLipMatricesOn G φ U) (hc : 0 < entry K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < G.dist i x y) :
    0 < G.dist j (φ.func x) (φ.func y) :=
  lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hc, hin⟩) (coLip_term_le hK i j hx hy)

/-- 命题 2.8(ii)。 -/
theorem reflects_gauge_zero (hK : K ∈ coLipMatricesOn G φ U)
    (hd : ∀ j, 0 < entry K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated G.dist (φ.func x) (φ.func y)) :
    GaugeZeroRelated G.dist x y := by
  intro j
  by_contra hn
  exact (positive_channel hK (hd j) hx hy (pos_iff_ne_zero.mpr hn)).ne' (hout j)

/-- 习题 2.2，对角输入项的标量双侧界。 -/
theorem scalar_two_sided (hL : L ∈ lipMatricesOn G φ U) (hK : K ∈ coLipMatricesOn G φ U)
    (hrow : OnlyInput L (j, j)) (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  ⟨coLip_term_le hK j j hx hy, lip_single_input hL hrow hx hy⟩

end

end LCH01
```

```lean filename=Main.lean
import LCH01
```

```toml filename=lakefile.toml
name = "lch01"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "Main"
roots = [
  "Main",
  "LCH01",
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.operator_space"
]
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
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
        {"file": "LCH01.lean", "name": "LCH01.IsLip"},
        {"file": "LCH01.lean", "name": "LCH01.IsLipOn"},
        {"file": "LCH01.lean", "name": "LCH01.lipMatrices"},
        {"file": "LCH01.lean", "name": "LCH01.lipMatricesOn"}
      ],
      "representation": {
        "objects": "Gauge 的 G.dist i 是第 i 个扩展伪度量。φ、dom φ 分别采用冻结模块的 Operator、dom。",
        "parameters": "I 有限非空，L 的条目属于 ENNReal。IsLipOn G φ U L 包含 U ⊆ dom φ，允许 U 为空。",
        "quantifiers": "对每个 x ∈ U、y ∈ U 和输出 j，比较像点距离与第 j 行的加权和。",
        "conclusion": "受限谓词要求像距 ≤ rowSum G L j x y。全域谓词取 U = dom φ，两种证书族分别收集满足对应谓词的全部矩阵。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH01.lean", "name": "LCH01.IsCoLipOn"},
        {"file": "LCH01.lean", "name": "LCH01.coLipMatricesOn"},
        {"file": "LCH01.lean", "name": "LCH01.coLip_term_le"}
      ],
      "representation": {
        "objects": "IsCoLipOn 是受限下界谓词，coLipMatricesOn 是满足它的矩阵集合。",
        "parameters": "给定规范族 G、算子 φ、集合 U 和 ENNReal 矩阵 K，成员资格同时要求 U.Nonempty 和 U ⊆ dom φ。",
        "quantifiers": "对每个 x ∈ U、y ∈ U 和输出 j，沿全部输入 i 取有限和。",
        "conclusion": "第 j 行的加权和 ≤ 第 j 分量的像距。辅助定理 coLip_term_le 证明每个单项也给出该像距的下界。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH01.lean", "name": "LCH01.BoundMatrix"},
        {"file": "LCH01.lean", "name": "LCH01.entry"},
        {"file": "LCH01.lean", "name": "LCH01.entry_mul"},
        {"file": "LCH01.lean", "name": "LCH01.rowSum"}
      ],
      "representation": {
        "objects": "BoundMatrix I 是 Matrix I I ENNReal，乘法取 mathlib 的矩阵乘法。",
        "parameters": "entry M i j = M j i，输入 i 为列，输出 j 为行。A 为第一步，B 为第二步。",
        "quantifiers": "任取 i、j，对所有中间指标 k 求和。rowSum 对给定行 j 和点对 x、y 沿全部输入求和。",
        "conclusion": "entry (B * A) i j = ∑ k, entry B k j * entry A i k。rowSum 的第 i 项是 entry M i j * G.dist i x y。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "LCH01.lean", "name": "LCH01.Channel"},
        {"file": "LCH01.lean", "name": "LCH01.OnlyInput"},
        {"file": "LCH01.lean", "name": "LCH01.channel_term_zero"},
        {"file": "LCH01.lean", "name": "LCH01.isDiag_iff_onlyInput"}
      ],
      "representation": {
        "objects": "Channel I 是有序对 I × I，(i,j) 表示从 d_i 到 d_j 的通道。",
        "parameters": "OnlyInput M (i,j) 指定输出行 j，允许保留输入列 i。",
        "quantifiers": "该行对每个 k ≠ i 满足 entry M k j = 0。零条目乘以任意 r : ENNReal 都为零。",
        "conclusion": "矩阵的标准对角谓词 M.IsDiag 等价于对每个 j 都有 OnlyInput M (j,j)。保留项本身可以为零。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "LCH01.lean", "name": "LCH01.rowSum_single"},
        {"file": "LCH01.lean", "name": "LCH01.lip_single_input"},
        {"file": "LCH01.lean", "name": "LCH01.lip_diagonal"}
      ],
      "representation": {
        "objects": "rowSum_single 化简行和，lip_single_input 将等式用于受限 Lip 证书。",
        "parameters": "对选定的 i、j 假设 OnlyInput L (i,j)。对角特例取 L.IsDiag。",
        "quantifiers": "行和等式对任意点对成立。像距上界对所有 x、y ∈ U 成立，对角结论遍历每个 j。",
        "conclusion": "第 j 行和等于 L_{i→j} d_i(x,y)，故第 j 分量像距至多为该项。对角时得到 L_{j→j} d_j(x,y) 上界。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "LCH01.lean", "name": "LCH01.positive_channel"}
      ],
      "representation": {
        "objects": "命题 2.8(i) 使用 U 上的 co-Lip 证书 K 和通道条目 entry K i j。",
        "parameters": "假设 0 < entry K i j 与 0 < G.dist i x y，系数和距离均取 ENNReal。",
        "quantifiers": "任取输入 i、输出 j 及 x、y ∈ U。",
        "conclusion": "正条目与正输入距离之积严格为正，且受第 j 分量像距控制，故该像距严格为正。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "LCH01.lean", "name": "LCH01.reflects_gauge_zero"}
      ],
      "representation": {
        "objects": "命题 2.8(ii) 在像点和输入点上均使用冻结定义 GaugeZeroRelated G.dist。",
        "parameters": "K 是 U 上的 co-Lip 证书，每个对角条目 entry K j j 严格为正。",
        "quantifiers": "任取 x、y ∈ U。若像点在每个分量上距离为零，则逐个分量 j 应用正通道结论。",
        "conclusion": "得到 GaugeZeroRelated G.dist x y，即对每个 j 有 G.dist j x y = 0。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "LCH01.lean", "name": "LCH01.scalar_two_sided"}
      ],
      "representation": {
        "objects": "习题 2.2 在同一算子 φ、同一受限域 U 上选取上界证书 L 和下界证书 K。",
        "parameters": "固定输出 j，稀疏条件 OnlyInput L (j,j) 只施于 L 的第 j 行。",
        "quantifiers": "对任意 x ∈ U、y ∈ U，两侧使用同一个分量 j 和同一对点。",
        "conclusion": "以合取同时给出 K_{j→j} d_j(x,y) ≤ d_j(φx,φy) 和 d_j(φx,φy) ≤ L_{j→j} d_j(x,y)。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```