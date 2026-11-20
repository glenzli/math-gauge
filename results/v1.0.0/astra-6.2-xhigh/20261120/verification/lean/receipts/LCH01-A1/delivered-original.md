8 项义务全部完成。项目使用 Lean 4.29.1 和指定提交的本地 mathlib 离线构建通过。`leanchecker` 已重检 `ChannelBounds` 和 `Main`，`#print axioms` 确认全部 21 个对照声明及辅助结构 `Gauge` 的公理依赖均在许可范围内。

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
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
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.operator_space",
  "ChannelBounds",
  "Main"
]
```

```lean filename=ChannelBounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul

/-!
# 分量通道与矩阵界

本文件将 Zhe Li（Glen Li / glenzli）《The Operator Evolution Theory》
卷一 §2.1、§2.2 和习题 2.2 的指定选段改写为 Lean 证明。
原著 https://glenzli.com/books/oet/ ，DOI 10.5281/zenodo.21457931 ，
ORCID 0009-0006-6536-3453 ，许可 https://creativecommons.org/licenses/by/4.0/ 。
-/

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

namespace LCH01

noncomputable section

variable {X I : Type} {bot : X}

abbrev CoeffMatrix (I : Type) := Matrix I I ENNReal

/-- 通道按输入、输出命名，矩阵按行、列存取。 -/
def entry (M : CoeffMatrix I) (i j : I) : ENNReal := M j i

theorem entry_mul [Fintype I] (B A : CoeffMatrix I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

def rowValue [Fintype I] (M : CoeffMatrix I) (v : I → ENNReal) (j : I) : ENNReal :=
  ∑ k, entry M k j * v k

/-- 正文的有限非空规范族，每个分量使用冻结模块的扩展伪度量。 -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X bot (dist i)

variable [Fintype I] [Nonempty I]

def IsLipOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (L : CoeffMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    G.dist j (φ.func x) (φ.func y) ≤ rowValue L (fun i => G.dist i x y) j

def IsLip (G : Gauge X I bot) (φ : Operator X bot) (L : CoeffMatrix I) : Prop :=
  IsLipOn G φ (dom φ) L

def lipFamilyOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) := {L | IsLipOn G φ U L}

def lipFamily (G : Gauge X I bot) (φ : Operator X bot) : Set (CoeffMatrix I) :=
  {L | IsLip G φ L}

def IsCoLipOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (K : CoeffMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    rowValue K (fun i => G.dist i x y) j ≤ G.dist j (φ.func x) (φ.func y)

def coLipFamilyOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) := {K | IsCoLipOn G φ U K}

variable {G : Gauge X I bot} {φ : Operator X bot} {U : Set X}
variable {L K : CoeffMatrix I} {x y : X} {i j : I}

theorem coLip_term_le (hK : K ∈ coLipFamilyOn G φ U) (i j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    entry K i j * G.dist i x y ≤ G.dist j (φ.func x) (φ.func y) := by
  have hsum : entry K i j * G.dist i x y ≤ rowValue K (fun k => G.dist k x y) j :=
    Finset.single_le_sum (fun k _ => zero_le (entry K k j * G.dist k x y))
      (Finset.mem_univ i)
  exact hsum.trans (hK.2.2 x hx y hy j)

abbrev Channel (I : Type) := I × I

def OnlyInput (M : CoeffMatrix I) (c : Channel I) : Prop :=
  ∀ k, k ≠ c.1 → entry M k c.2 = 0

def IsDiagonal (M : CoeffMatrix I) : Prop := ∀ j, OnlyInput M (j, j)

omit [Fintype I] [Nonempty I] in
theorem zero_channel_term (M : CoeffMatrix I) (c : Channel I) (v : I → ENNReal)
    (h : entry M c.1 c.2 = 0) : entry M c.1 c.2 * v c.1 = 0 := by
  rw [h, zero_mul]

omit [Nonempty I] in
theorem rowValue_onlyInput {M : CoeffMatrix I} {i j : I} (h : OnlyInput M (i, j))
    (v : I → ENNReal) : rowValue M v j = entry M i j * v i := by
  classical
  unfold rowValue
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [h k hki, zero_mul]
  · simp

theorem lip_onlyInput (hL : L ∈ lipFamilyOn G φ U) (h : OnlyInput L (i, j))
    (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L i j * G.dist i x y :=
  (hL.2 x hx y hy j).trans_eq (rowValue_onlyInput h _)

theorem lip_diagonal (hL : L ∈ lipFamilyOn G φ U) (h : IsDiagonal L)
    (j : I) (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  lip_onlyInput hL (h j) hx hy

theorem positive_channel (hK : K ∈ coLipFamilyOn G φ U) (hc : 0 < entry K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hd : 0 < G.dist i x y) :
    0 < G.dist j (φ.func x) (φ.func y) :=
  (ENNReal.mul_pos_iff.mpr ⟨hc, hd⟩).trans_le (coLip_term_le hK i j hx hy)

theorem reflects_gauge_zero (hK : K ∈ coLipFamilyOn G φ U)
    (hdiag : ∀ j, 0 < entry K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated G.dist (φ.func x) (φ.func y)) :
    GaugeZeroRelated G.dist x y := by
  intro j
  by_contra hn
  have hout := positive_channel hK (hdiag j) hx hy (pos_iff_ne_zero.mpr hn)
  exact (ne_of_gt hout) (hzero j)

theorem diagonal_two_sided (hL : L ∈ lipFamilyOn G φ U) (hK : K ∈ coLipFamilyOn G φ U)
    (h : OnlyInput L (j, j)) (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  ⟨coLip_term_le hK j j hx hy, lip_onlyInput hL h hx hy⟩

end

end LCH01
```

```lean filename=Main.lean
import ChannelBounds
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
        {"file": "ChannelBounds.lean", "name": "LCH01.IsLip"},
        {"file": "ChannelBounds.lean", "name": "LCH01.IsLipOn"},
        {"file": "ChannelBounds.lean", "name": "LCH01.lipFamily"},
        {"file": "ChannelBounds.lean", "name": "LCH01.lipFamilyOn"}
      ],
      "representation": "Gauge 的 dist 是有限非空指标族上的扩展伪度量，φ 使用冻结的 Operator。IsLipOn 要求 U ⊆ dom φ，且对所有 x,y ∈ U 和输出 j，像距至多为第 j 行作用于输入距离向量的和。U 可以为空。IsLip 取 U = dom φ，两种 family 分别收集满足相应谓词的全部矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.IsCoLipOn"},
        {"file": "ChannelBounds.lean", "name": "LCH01.coLipFamilyOn"},
        {"file": "ChannelBounds.lean", "name": "LCH01.coLip_term_le"}
      ],
      "representation": "K 属于 coLipFamilyOn G φ U 当且仅当 U 非空、U ⊆ dom φ，且对任意 x,y ∈ U 和 j，第 j 行的加权输入距离和至多为第 j 分量像距。coLip_term_le 从该定义推出每个输入项也受该像距控制。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.CoeffMatrix"},
        {"file": "ChannelBounds.lean", "name": "LCH01.entry"},
        {"file": "ChannelBounds.lean", "name": "LCH01.entry_mul"},
        {"file": "ChannelBounds.lean", "name": "LCH01.rowValue"}
      ],
      "representation": "CoeffMatrix I 是 ENNReal 方阵。entry M i j = M j i，i 表示输入列，j 表示输出行。对任意 B,A,i,j，先 A 后 B 的乘积条目为 ∑ k, entry B k j * entry A i k。rowValue M v j 是该行与 v 的有限加权和。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.Channel"},
        {"file": "ChannelBounds.lean", "name": "LCH01.OnlyInput"},
        {"file": "ChannelBounds.lean", "name": "LCH01.IsDiagonal"},
        {"file": "ChannelBounds.lean", "name": "LCH01.zero_channel_term"}
      ],
      "representation": "Channel I 是输入、输出的有序对 (i,j)。OnlyInput M (i,j) 要求所有 k ≠ i 的第 j 行条目为零，允许保留的条目也为零。IsDiagonal 要求每一行 j 均满足 OnlyInput M (j,j)。零系数对任意扩展非负输入值的贡献均为零。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.rowValue_onlyInput"},
        {"file": "ChannelBounds.lean", "name": "LCH01.lip_onlyInput"},
        {"file": "ChannelBounds.lean", "name": "LCH01.lip_diagonal"}
      ],
      "representation": "第 j 行只保留输入 i 时，对任意向量 v，行和等于 entry L i j * v i。取 v k = G.dist k x y，对受限 Lip 族中任意 L 和任意 x,y ∈ U 得到单项上界。若 L 对角，则对每个 j 得到输入与输出同为 j 的上界。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.positive_channel"}
      ],
      "representation": "对任意合法受限 co-Lip 矩阵 K、通道指标 i,j 和 x,y ∈ U，若 entry K i j 与输入分量距离 G.dist i x y 均严格为正，则第 j 分量的像距严格为正。乘法在 ENNReal 中进行，包含无穷值。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.reflects_gauge_zero"}
      ],
      "representation": "若合法 K 的每个对角条目严格为正，则对任意 x,y ∈ U，像点之间的 GaugeZeroRelated 蕴含原点对的 GaugeZeroRelated。两处均使用冻结定义，即所有分量距离为零。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "ChannelBounds.lean", "name": "LCH01.diagonal_two_sided"}
      ],
      "representation": "任取同一 φ、U 上的合法 L 和 K，以及满足 OnlyInput L (j,j) 的指定行 j。对每对 x,y ∈ U，以合取表达标量双侧界：第 j 分量像距介于 entry K j j * G.dist j x y 与 entry L j j * G.dist j x y 之间。下界来自 coLip_term_le，上界来自 lip_onlyInput。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```