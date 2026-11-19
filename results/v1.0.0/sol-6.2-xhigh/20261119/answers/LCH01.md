清单中的 8 项义务全部完成。源码已用 Lean 4.29.1 和 mathlib 提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6` 编译。两个目标模块均通过 `leanchecker` 内核重放，声明的公理依赖均在允许范围内。对齐表记录了对象对应和直接使用的义务。

```lean filename=Main.lean
import LCH01.Bounds
import LCH01.Channels

/-!
Lean formalization of selected statements from Zhe Li (Glen Li / glenzli),
*The Operator Evolution Theory*, Volume I, Chapter 2, v1.0.0.
The original work is licensed under CC BY 4.0.

https://orcid.org/0009-0006-6536-3453
https://glenzli.com/books/oet/
https://gitlab.com/glenzli/oet-public
https://creativecommons.org/licenses/by/4.0/
-/
```

```lean filename=LCH01/Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

open scoped BigOperators

namespace LCH01

open formal_oet.vol_01.ch_01_foundations (ExtendedPseudoMetric Operator dom)

/-- A finite, nonempty family of extended pseudometrics with the same absorbing point. -/
structure GaugeFamily (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  isExtended : ∀ i, ExtendedPseudoMetric X bot (dist i)

abbrev CoeffMatrix (I : Type) := Matrix I I ENNReal

/-- The coefficient from an input component to an output component. -/
def entry {I : Type} (M : CoeffMatrix I) (input output : I) : ENNReal :=
  M output input

theorem entry_mul {I : Type} [Fintype I] (A B : CoeffMatrix I) (i j : I) :
    entry (A * B) i j = ∑ k : I, entry A k j * entry B i k :=
  Matrix.mul_apply

/-- The weighted sum for output component `j` and input vector `v`. -/
noncomputable def rowSum {I : Type} [Fintype I] (M : CoeffMatrix I) (v : I → ENNReal) (j : I) :
    ENNReal :=
  ∑ i : I, entry M i j * v i

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def IsRestrictedLip (G : GaugeFamily X I bot) (φ : Operator X bot)
    (U : Set X) (L : CoeffMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.dist j (φ.func x) (φ.func y) ≤ rowSum L (fun i => G.dist i x y) j

def IsLip (G : GaugeFamily X I bot) (φ : Operator X bot) (L : CoeffMatrix I) : Prop :=
  IsRestrictedLip G φ (dom φ) L

def restrictedLipMatrices (G : GaugeFamily X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) :=
  {L | IsRestrictedLip G φ U L}

def lipMatrices (G : GaugeFamily X I bot) (φ : Operator X bot) : Set (CoeffMatrix I) :=
  {L | IsLip G φ L}

def IsRestrictedCoLip (G : GaugeFamily X I bot) (φ : Operator X bot)
    (U : Set X) (K : CoeffMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      rowSum K (fun i => G.dist i x y) j ≤ G.dist j (φ.func x) (φ.func y)

def restrictedCoLipMatrices (G : GaugeFamily X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) :=
  {K | IsRestrictedCoLip G φ U K}

end LCH01
```

```lean filename=LCH01/Channels.lean
import LCH01.Bounds
import Mathlib.Data.ENNReal.Operations
import Mathlib.LinearAlgebra.Matrix.IsDiag

open scoped BigOperators

namespace LCH01

open formal_oet.vol_01.ch_01_foundations (GaugeZeroRelated Operator)

/-- An ordered pair of input and output components. -/
abbrev Channel (I : Type) := I × I

/-- In the output row of `c`, every coefficient outside its input column is zero. -/
def SingleInputRow {I : Type} (M : CoeffMatrix I) (c : Channel I) : Prop :=
  ∀ k : I, k ≠ c.1 → entry M k c.2 = 0

theorem isDiag_iff_singleInputRows {I : Type} (M : CoeffMatrix I) :
    M.IsDiag ↔ ∀ j : I, SingleInputRow M (j, j) := by
  constructor
  · intro h j k hkj
    exact h hkj.symm
  · intro h j k hjk
    exact h j k hjk.symm

theorem rowSum_singleInput {I : Type} [Fintype I] (M : CoeffMatrix I) (v : I → ENNReal)
    (c : Channel I) (h : SingleInputRow M c) :
    rowSum M v c.2 = entry M c.1 c.2 * v c.1 := by
  unfold rowSum
  refine Finset.sum_eq_single c.1 (fun k _ hk => ?_) (fun hmem => ?_)
  · rw [h k hk, zero_mul]
  · exact (hmem (Finset.mem_univ c.1)).elim

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable {G : GaugeFamily X I bot} {φ : Operator X bot} {U : Set X}
variable {L K : CoeffMatrix I} {x y : X}

theorem lip_singleInput (hL : L ∈ restrictedLipMatrices G φ U)
    (c : Channel I) (hrow : SingleInputRow L c) (hx : x ∈ U) (hy : y ∈ U) :
    G.dist c.2 (φ.func x) (φ.func y) ≤ entry L c.1 c.2 * G.dist c.1 x y := by
  have h : IsRestrictedLip G φ U L := hL
  simpa only [rowSum_singleInput L (fun i => G.dist i x y) c hrow] using
    h.2 x hx y hy c.2

theorem lip_diagonal (hL : L ∈ restrictedLipMatrices G φ U)
    (hdiag : L.IsDiag) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  lip_singleInput hL (j, j) ((isDiag_iff_singleInputRows L).mp hdiag j) hx hy

theorem coLip_entry_le (hK : K ∈ restrictedCoLipMatrices G φ U)
    (c : Channel I) (hx : x ∈ U) (hy : y ∈ U) :
    entry K c.1 c.2 * G.dist c.1 x y ≤ G.dist c.2 (φ.func x) (φ.func y) := by
  have h : IsRestrictedCoLip G φ U K := hK
  calc
    entry K c.1 c.2 * G.dist c.1 x y ≤ rowSum K (fun i => G.dist i x y) c.2 :=
      Finset.single_le_sum (f := fun i => entry K i c.2 * G.dist i x y)
        (fun _ _ => zero_le _) (Finset.mem_univ c.1)
    _ ≤ G.dist c.2 (φ.func x) (φ.func y) := h.2.2 x hx y hy c.2

theorem coLip_channel_pos (hK : K ∈ restrictedCoLipMatrices G φ U)
    (c : Channel I) (hpos : 0 < entry K c.1 c.2) (hx : x ∈ U) (hy : y ∈ U) :
    0 < G.dist c.1 x y → 0 < G.dist c.2 (φ.func x) (φ.func y) := by
  intro hdist
  exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hdist))
    (coLip_entry_le hK c hx hy)

theorem coLip_reflects_zero (hK : K ∈ restrictedCoLipMatrices G φ U)
    (hdiag : ∀ j : I, 0 < entry K j j) (hx : x ∈ U) (hy : y ∈ U) :
    GaugeZeroRelated G.dist (φ.func x) (φ.func y) → GaugeZeroRelated G.dist x y := by
  intro hzero j
  by_contra hne
  have hpos : 0 < G.dist j x y := pos_iff_ne_zero.mpr hne
  exact (ne_of_gt (coLip_channel_pos hK (j, j) (hdiag j) hx hy hpos)) (hzero j)

theorem scalar_two_sided (hL : L ∈ restrictedLipMatrices G φ U)
    (hK : K ∈ restrictedCoLipMatrices G φ U) (j : I)
    (hrow : SingleInputRow L (j, j)) (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  ⟨coLip_entry_le hK (j, j) hx hy, lip_singleInput hL (j, j) hrow hx hy⟩

end LCH01
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
        {"file": "LCH01/Bounds.lean", "name": "LCH01.IsRestrictedLip"},
        {"file": "LCH01/Bounds.lean", "name": "LCH01.IsLip"},
        {"file": "LCH01/Bounds.lean", "name": "LCH01.restrictedLipMatrices"},
        {"file": "LCH01/Bounds.lean", "name": "LCH01.lipMatrices"}
      ],
      "representation": "GaugeFamily 的 G.dist i 对应 d_i，I 有限非空，每个分量满足冻结模块的 ExtendedPseudoMetric。φ 与 dom φ 使用冻结模块的算子和定义域。受限谓词要求 U ⊆ dom φ，并对每个 x,y ∈ U 和 j ∈ I 给出输出距离的行和上界，允许 U 为空。全域谓词取 U = dom φ，此时子集条件自反。两个证书族分别取满足对应谓词的所有 ENNReal 矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Bounds.lean", "name": "LCH01.IsRestrictedCoLip"},
        {"file": "LCH01/Bounds.lean", "name": "LCH01.restrictedCoLipMatrices"}
      ],
      "representation": "同一规范族 G 和算子 φ 下，谓词要求 U.Nonempty 与 U ⊆ dom φ，并对每个 x,y ∈ U 和 j ∈ I 要求 K 的加权行和不超过像点距离。证书族由满足该谓词的全部矩阵组成，矩阵条目允许为 +∞。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Bounds.lean", "name": "LCH01.CoeffMatrix"},
        {"file": "LCH01/Bounds.lean", "name": "LCH01.entry"},
        {"file": "LCH01/Bounds.lean", "name": "LCH01.entry_mul"},
        {"file": "LCH01/Bounds.lean", "name": "LCH01.rowSum"}
      ],
      "representation": "CoeffMatrix I 是 Matrix I I ENNReal。entry M i j 指 M j i，即第 j 个输出行、第 i 个输入列。对任意 i,j，entry_mul 给出标准矩阵乘积 (A * B) 的通道条目，等于对所有中间分量 k 求和的 A[k→j] * B[i→k]。rowSum 对所有输入分量求和。乘积与行和采用 ENNReal 算术，其中 0 * ⊤ = ⊤ * 0 = 0。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.Channel"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.SingleInputRow"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.isDiag_iff_singleInputRows"}
      ],
      "representation": "Channel I 的 c=(i,j) 从输入 i 指向输出 j。SingleInputRow M c 要求第 j 行每个 k ≠ i 的条目为零，保留条目可为零。矩阵对角性用 mathlib 的 Matrix.IsDiag 表示，与每个同分量通道 (j,j) 满足该行条件等价。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.rowSum_singleInput"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.lip_singleInput"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.lip_diagonal"}
      ],
      "representation": "rowSum_singleInput 对任意输入向量给出单输入行的精确求和等式。取向量 i ↦ d_i(x,y)，对任意 x,y ∈ U，将等式代入合法受限 Lip 上界，得到通道 (i,j) 的标量上界。若 L 为对角矩阵，任取 j 得到对应的 (j,j) 标量上界。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.coLip_entry_le"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.coLip_channel_pos"}
      ],
      "representation": "对任意合法受限 co-Lip 矩阵 K、通道 (i,j) 和 x,y ∈ U，coLip_entry_le 从行和取出 K[i→j] * d_i(x,y) 作为输出距离的下界。若 K[i→j] > 0 且 d_i(x,y) > 0，coLip_channel_pos 推出 d_j(φ(x),φ(y)) > 0。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.coLip_reflects_zero"}
      ],
      "representation": "假设 K 是合法受限 co-Lip 矩阵且每个对角条目为正。对任意 x,y ∈ U，用冻结模块的 GaugeZeroRelated G.dist 表示族零距。结论由 φ(x) 与 φ(y) 的全分量零距推出 x 与 y 的全分量零距。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.scalar_two_sided"}
      ],
      "representation": "在同一 U 上取合法的受限 Lip 矩阵 L 和受限 co-Lip 矩阵 K。对给定 j，仅假设 L 的第 j 行满足 SingleInputRow L (j,j)。对任意 x,y ∈ U，用两个不等式的合取表示 K[j→j] * d_j(x,y) ≤ d_j(φ(x),φ(y)) ≤ L[j→j] * d_j(x,y)。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19", "CH02-P20"]
    }
  ]
}
```