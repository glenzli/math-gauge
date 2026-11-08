已完成 8 项义务。`Channels.lean` 与 `Main.lean` 均通过 Lean 4.29.1 检查；公理依赖检查只发现 `propext`、`Classical.choice` 和 `Quot.sound`。下列源码不改写冻结前置模块。

数学内容依据 Zhe Li（Glen Li），[*The Operator Evolution Theory*](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)；本交付为其指定选段的形式化。

```lean filename=Channels.lean
import formal_oet.vol_01.ch_01_foundations.operator_space

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

namespace Channels

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

/-- Entries are indexed by input first and output second. -/
abbrev Coeff (I : Type) := I → I → ENNReal

noncomputable def matrixMul (B A : Coeff I) : Coeff I :=
  fun i j => ∑ k : I, B k j * A i k

def lipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Coeff I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y

def lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : Coeff I) : Prop := lipOn d φ (dom φ) L

def lipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Coeff I) :=
  {L | lip d φ L}

def lipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Coeff I) := {L | lipOn d φ U L}

def coLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i : I, K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

def coLipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Coeff I) := {K | coLipOn d φ U K}

/-- A component channel is an input/output pair. -/
abbrev Channel (I : Type) := I × I

def singleInputRow (L : Coeff I) (i j : I) : Prop :=
  ∀ k, k ≠ i → L k j = 0

def diagonal (L : Coeff I) : Prop := ∀ i j, i ≠ j → L i j = 0

theorem diagonal_singleInputRow (L : Coeff I) (h : diagonal L) (j : I) :
    singleInputRow L j j := by
  intro k hk
  exact h k j hk

theorem row_sum (L : Coeff I) (d : I → X → X → ENNReal)
    (i j : I) (h : singleInputRow L i j) (x y : X) :
    (∑ k : I, L k j * d k x y) = L i j * d i x y := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [h k hk, zero_mul]
  · simp

theorem lip_single_channel (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Coeff I) (i j : I)
    (hL : lipOn d φ U L) (hrow : singleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  simpa only [row_sum L d i j hrow x y] using hL.2 x hx y hy j

theorem lip_diagonal_channel (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Coeff I) (hL : lipOn d φ U L) (hdiag : diagonal L) :
    ∀ j x, x ∈ U → ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  exact lip_single_channel d φ U L j j hL (diagonal_singleInputRow L hdiag j) x hx y hy

theorem coLip_term_le (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) (hK : coLipOn d φ U K)
    (i j : I) (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  classical
  calc
    K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

theorem positive_channel (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) (hK : coLipOn d φ U K)
    (i j : I) (hpos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (φ.func x) (φ.func y) := by
  intro x hx y hy hd
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpos, hd⟩)
    (coLip_term_le d φ U K hK i j x y hx hy)

theorem reflects_gauge_zero (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) (hK : coLipOn d φ U K)
    (hdiag : ∀ j, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hn
  have hp : 0 < d j x y := bot_lt_iff_ne_bot.mpr hn
  have hout := positive_channel d φ U K hK j j (hdiag j) x hx y hy hp
  rw [hzero j] at hout
  exact (lt_irrefl 0) hout

theorem scalar_two_sided (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L K : Coeff I) (j : I)
    (hL : lipOn d φ U L) (hK : coLipOn d φ U K)
    (hrow : singleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  exact ⟨coLip_term_le d φ U K hK j j x y hx hy,
    lip_single_channel d φ U L j j hL hrow x hx y hy⟩

end Channels
```

```lean filename=Main.lean
import Channels
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
        {"file": "Channels.lean", "name": "Channels.lip"},
        {"file": "Channels.lean", "name": "Channels.lipOn"},
        {"file": "Channels.lean", "name": "Channels.lipFamily"},
        {"file": "Channels.lean", "name": "Channels.lipFamilyOn"}
      ],
      "representation": "d i 为第 i 个分量距离，φ 为冻结模块中的保持吸收元算子。lipOn 要求 U ⊆ dom φ，并对所有 x,y ∈ U 和输出 j 给出原文有限和上界；lip 是 U = dom φ 的特例。两个 family 分别是满足对应谓词的矩阵集合。ENNReal 表示扩展非负数。"
      ,
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "Channels.lean", "name": "Channels.coLipOn"},
        {"file": "Channels.lean", "name": "Channels.coLipFamilyOn"}
      ],
      "representation": "coLipOn 同时要求 U 非空、U ⊆ dom φ，并对所有 x,y ∈ U 和输出 j 给出原文有限和下界；coLipFamilyOn 是全部满足该谓词的矩阵集合。"
      ,
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "Channels.lean", "name": "Channels.Coeff"},
        {"file": "Channels.lean", "name": "Channels.matrixMul"}
      ],
      "representation": "Coeff I 是 I → I → ENNReal；M i j 对应输入 i、输出 j 的条目 M_{i→j}，即通常书写矩阵的第 j 行、第 i 列。matrixMul B A i j = ∑ k, B k j * A i k，对应 B · A。I 由 Fintype 表示有限指标集。"
      ,
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "Channels.lean", "name": "Channels.Channel"},
        {"file": "Channels.lean", "name": "Channels.singleInputRow"},
        {"file": "Channels.lean", "name": "Channels.diagonal"},
        {"file": "Channels.lean", "name": "Channels.diagonal_singleInputRow"}
      ],
      "representation": "Channel I = I × I，首坐标为输入、次坐标为输出。singleInputRow L i j 表示输出行 j 除输入 i 外的条目均为零；diagonal 表示所有非对角条目为零，diagonal_singleInputRow 给出各对角行的特例。"
      ,
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "Channels.lean", "name": "Channels.row_sum"},
        {"file": "Channels.lean", "name": "Channels.lip_single_channel"},
        {"file": "Channels.lean", "name": "Channels.lip_diagonal_channel"}
      ],
      "representation": "row_sum 证明稀疏输出行的完整有限和等于唯一保留项；lip_single_channel 对任意 x,y ∈ U 推出相应 Lip 上界；lip_diagonal_channel 对每个 j 给出对角矩阵特例。U ⊆ dom φ 包含在 lipOn 中。"
      ,
      "dependencies": ["CH02-D01", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "Channels.lean", "name": "Channels.coLip_term_le"},
        {"file": "Channels.lean", "name": "Channels.positive_channel"}
      ],
      "representation": "对任意输入 i、输出 j 和 x,y ∈ U，coLip_term_le 从非负有限和取出 K i j * d i x y。positive_channel 在 K i j > 0 时证明 d i x y > 0 蕴含像点的第 j 分量距离严格为正；允许距离或系数为无穷。"
      ,
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "Channels.lean", "name": "Channels.reflects_gauge_zero"}
      ],
      "representation": "在每个对角条目 K j j 严格为正时，对任意 x,y ∈ U，冻结模块的 GaugeZeroRelated d (φ.func x) (φ.func y) 蕴含 GaugeZeroRelated d x y。结论是逐分量零距离关系，不要求规范族分离，也不声称 x = y。"
      ,
      "dependencies": ["CH02-D02", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "Channels.lean", "name": "Channels.scalar_two_sided"}
      ],
      "representation": "对给定 j、受限 Lip 矩阵 L 和受限 co-Lip 矩阵 K，singleInputRow L j j 表示第 j 输出行仅保留对角输入项。对所有 x,y ∈ U，结论同时给出 K j j * d j x y ≤ d j (φ x) (φ y) ≤ L j j * d j x y；域包含与非空条件由两个受限谓词保留。"
      ,
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D07", "CH02-P19", "CH02-P20"]
    }
  ]
}
```