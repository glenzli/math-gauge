8 项义务均已完成。源码使用 Lean 4.29.1 和 mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6` 编译通过，并通过 `leanchecker` 内核复核。对应表中的声明只依赖允许的逻辑公理 `propext`、`Classical.choice` 和 `Quot.sound`。

本交付是 Zhe Li（Glen Li / glenzli）《The Operator Evolution Theory》第一卷 v1.0.0 指定选段的 Lean 形式化改写。[ORCID](https://orcid.org/0009-0006-6536-3453) · [作品主页](https://glenzli.com/books/oet/) · [原文仓库](https://gitlab.com/glenzli/oet-public) · [DOI](https://doi.org/10.5281/zenodo.21457931) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

```lean filename=Main.lean
import LCH01.MatrixBounds
import LCH01.Channels
```

```lean filename=LCH01/MatrixBounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

open scoped BigOperators ENNReal
open formal_oet.vol_01.ch_01_foundations

namespace LCH01

/-- A finite, nonempty family of extended pseudometrics with a shared absorbing point. -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ℝ≥0∞
  component : ∀ i : I, ExtendedPseudoMetric X bot (dist i)

/-- Rows are outputs and columns are inputs. -/
abbrev BoundMatrix (I : Type) := Matrix I I ℝ≥0∞

namespace BoundMatrix

/-- The coefficient of the channel from input `i` to output `j`. -/
def coeff {I : Type} (M : BoundMatrix I) (i j : I) : ℝ≥0∞ := M j i

/-- The extended nonnegative weighted sum at output `j`. -/
noncomputable def rowSum {I : Type} [Fintype I]
    (M : BoundMatrix I) (j : I) (v : I → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, M.coeff i j * v i

theorem mul_coeff {I : Type} [Fintype I] (B A : BoundMatrix I) (i j : I) :
    coeff (B * A) i j = ∑ k, B.coeff k j * A.coeff i k :=
  Matrix.mul_apply

end BoundMatrix

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def IsRestrictedLipMatrix (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.dist j (φ.func x) (φ.func y) ≤ L.rowSum j (fun i => G.dist i x y)

def IsLipMatrix (G : Gauge X I bot) (φ : Operator X bot) (L : BoundMatrix I) : Prop :=
  IsRestrictedLipMatrix G φ (dom φ) L

theorem isLipMatrix_iff (G : Gauge X I bot) (φ : Operator X bot) (L : BoundMatrix I) :
    IsLipMatrix G φ L ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
        G.dist j (φ.func x) (φ.func y) ≤ L.rowSum j (fun i => G.dist i x y) :=
  ⟨fun h => h.2, fun h => ⟨Set.Subset.rfl, h⟩⟩

def lipMatrices (G : Gauge X I bot) (φ : Operator X bot) : Set (BoundMatrix I) :=
  { L | IsLipMatrix G φ L }

def restrictedLipMatrices (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) :=
  { L | IsRestrictedLipMatrix G φ U L }

def IsRestrictedCoLipMatrix (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ U.Nonempty ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      K.rowSum j (fun i => G.dist i x y) ≤ G.dist j (φ.func x) (φ.func y)

def restrictedCoLipMatrices (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) :=
  { K | IsRestrictedCoLipMatrix G φ U K }

theorem coLip_term_le {G : Gauge X I bot} {φ : Operator X bot}
    {U : Set X} {K : BoundMatrix I} (hK : K ∈ restrictedCoLipMatrices G φ U)
    (i j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K.coeff i j * G.dist i x y ≤ G.dist j (φ.func x) (φ.func y) := by
  calc
    _ ≤ K.rowSum j (fun k => G.dist k x y) :=
      Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)
    _ ≤ _ := hK.2.2 x hx y hy j

end LCH01
```

```lean filename=LCH01/Channels.lean
import LCH01.MatrixBounds
import Mathlib.Data.ENNReal.Operations
import Mathlib.LinearAlgebra.Matrix.IsDiag

open scoped BigOperators ENNReal
open formal_oet.vol_01.ch_01_foundations

namespace LCH01

/-- An ordered pair of input and output components, in that order. -/
abbrev Channel (I : Type) := I × I

/-- In the output row of `c`, every coefficient away from its input is zero. -/
def HasOnlyInput {I : Type} (M : BoundMatrix I) (c : Channel I) : Prop :=
  ∀ k : I, k ≠ c.1 → M.coeff k c.2 = 0

theorem zero_channel_term {I : Type} (M : BoundMatrix I) (c : Channel I)
    (v : I → ℝ≥0∞) (h : M.coeff c.1 c.2 = 0) :
    M.coeff c.1 c.2 * v c.1 = 0 := by
  rw [h, zero_mul]

theorem isDiag_iff_onlyInput {I : Type} (M : BoundMatrix I) :
    Matrix.IsDiag M ↔ ∀ j : I, HasOnlyInput M (j, j) := by
  constructor
  · intro h j k hkj
    exact h (Ne.symm hkj)
  · intro h j k hjk
    exact h j k (Ne.symm hjk)

theorem rowSum_eq_of_onlyInput {I : Type} [Fintype I] (M : BoundMatrix I)
    (c : Channel I) (v : I → ℝ≥0∞) (hrow : HasOnlyInput M c) :
    M.rowSum c.2 v = M.coeff c.1 c.2 * v c.1 := by
  unfold BoundMatrix.rowSum
  apply Finset.sum_eq_single c.1
  · intro k _ hk
    exact zero_channel_term M (k, c.2) v (hrow k hk)
  · simp

theorem rowSum_eq_of_diagonal {I : Type} [Fintype I] (M : BoundMatrix I)
    (hdiag : Matrix.IsDiag M) (j : I) (v : I → ℝ≥0∞) :
    M.rowSum j v = M.coeff j j * v j :=
  rowSum_eq_of_onlyInput M (j, j) v ((isDiag_iff_onlyInput M).mp hdiag j)

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable {G : Gauge X I bot} {φ : Operator X bot} {U : Set X}
variable {L K : BoundMatrix I}

theorem lip_of_onlyInput (hL : L ∈ restrictedLipMatrices G φ U)
    (i j : I) (hrow : HasOnlyInput L (i, j)) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ L.coeff i j * G.dist i x y := by
  calc
    _ ≤ L.rowSum j (fun k => G.dist k x y) := hL.2 x hx y hy j
    _ = _ := rowSum_eq_of_onlyInput L (i, j) (fun k => G.dist k x y) hrow

theorem lip_of_diagonal (hL : L ∈ restrictedLipMatrices G φ U) (hdiag : Matrix.IsDiag L)
    (j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ L.coeff j j * G.dist j x y := by
  calc
    _ ≤ L.rowSum j (fun k => G.dist k x y) := hL.2 x hx y hy j
    _ = _ := rowSum_eq_of_diagonal L hdiag j (fun k => G.dist k x y)

theorem positive_coLip_channel (hK : K ∈ restrictedCoLipMatrices G φ U)
    (i j : I) (hpos : 0 < K.coeff i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    0 < G.dist i x y → 0 < G.dist j (φ.func x) (φ.func y) := by
  intro hdist
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpos, hdist⟩) (coLip_term_le hK i j hx hy)

theorem reflect_gauge_zero_of_positive_diagonal (hK : K ∈ restrictedCoLipMatrices G φ U)
    (hdiag : ∀ j : I, 0 < K.coeff j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    GaugeZeroRelated G.dist (φ.func x) (φ.func y) → GaugeZeroRelated G.dist x y := by
  intro hzero j
  by_contra hne
  have hpos := positive_coLip_channel hK j j (hdiag j) hx hy (pos_iff_ne_zero.mpr hne)
  exact (ne_of_gt hpos) (hzero j)

theorem diagonal_scalar_bounds (hL : L ∈ restrictedLipMatrices G φ U)
    (hK : K ∈ restrictedCoLipMatrices G φ U) (j : I) (hrow : HasOnlyInput L (j, j))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K.coeff j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
      G.dist j (φ.func x) (φ.func y) ≤ L.coeff j j * G.dist j x y :=
  ⟨coLip_term_le hK j j hx hy, lip_of_onlyInput hL j j hrow hx hy⟩

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
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.IsRestrictedLipMatrix"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.IsLipMatrix"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.isLipMatrix_iff"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.lipMatrices"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.restrictedLipMatrices"}
      ],
      "representation": "G.dist i 对应 d_i。Gauge 打包分量及冻结的扩展伪度量公理，Fintype I 与 Nonempty I 表示有限非空指标集。φ.func 与 dom φ 是冻结的算子作用和定义域。受限谓词包含 U ⊆ dom φ 并对一切 x,y ∈ U 及 j ∈ I 要求输出距离不超过第 j 行加权和。全域谓词取 U = dom φ，isLipMatrix_iff 展开其量词。两个 Set 分别收集满足全域或受限谓词的全部矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.IsRestrictedCoLipMatrix"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.restrictedCoLipMatrices"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.coLip_term_le"}
      ],
      "representation": "U ⊆ dom φ 与 U.Nonempty 表示给定的非空受限域。对每个 x,y ∈ U 和输出 j，第 j 行加权和不超过 d_j(φ(x),φ(y))。restrictedCoLipMatrices 收集全部合法 K。辅助引理 coLip_term_le 用非负性从和中抽出任意一项作为下界。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.BoundMatrix"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.BoundMatrix.coeff"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.BoundMatrix.rowSum"},
        {"file": "LCH01/MatrixBounds.lean", "name": "LCH01.BoundMatrix.mul_coeff"}
      ],
      "representation": "BoundMatrix I 使用 Matrix I I ℝ≥0∞。M.coeff i j 是 M j i，即输出行 j 和输入列 i。rowSum 对有限输入集求加权和。mul_coeff 给出后步矩阵 B 左乘前步矩阵 A 时的 (B * A)_{i→j} = ∑ k, B_{k→j} A_{i→k}。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.Channel"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.HasOnlyInput"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.zero_channel_term"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.isDiag_iff_onlyInput"}
      ],
      "representation": "Channel I 是有序对 (i,j)，依次表示输入和输出。HasOnlyInput L (i,j) 要求每个 k ≠ i 对应的 L_{k→j} 为零。zero_channel_term 证明零系数的乘积项为零。Matrix.IsDiag L 等价于每一行 j 都满足 HasOnlyInput L (j,j)。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.rowSum_eq_of_onlyInput"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.rowSum_eq_of_diagonal"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.lip_of_onlyInput"},
        {"file": "LCH01/Channels.lean", "name": "LCH01.lip_of_diagonal"}
      ],
      "representation": "对稀疏行 j，取 v k = d_k(x,y) 后，rowSum_eq_of_onlyInput 给出第 j 行和等于 L_{i→j}d_i(x,y)。lip_of_onlyInput 对合法受限 L 与每对 x,y ∈ U 得到该单项上界。两个对角声明在 Matrix.IsDiag L 下对任意 j 给出同分量的行和等式及 Lip 上界。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.positive_coLip_channel"}
      ],
      "representation": "给定 K 属于受限 co-Lip 证书族及通道 (i,j) 的正系数，对任意 x,y ∈ U，从 0 < d_i(x,y) 推出 0 < d_j(φ(x),φ(y))。乘积正性与单项下界均在 ℝ≥0∞ 中成立。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.reflect_gauge_zero_of_positive_diagonal"}
      ],
      "representation": "给定合法受限 K，并假设每个 K_{j→j} 严格正。对任意 x,y ∈ U，由 φ(x) 与 φ(y) 的 GaugeZeroRelated 得到 x 与 y 的 GaugeZeroRelated，亦即对每个 j 都有 d_j(x,y) = 0。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/Channels.lean", "name": "LCH01.diagonal_scalar_bounds"}
      ],
      "representation": "L 和 K 分别属于 φ 在同一 U 上的受限 Lip 与 co-Lip 证书族。对给定输出 j，仅要求 HasOnlyInput L (j,j)。对任意 x,y ∈ U，以合取给出 K_{j→j}d_j(x,y) ≤ d_j(φ(x),φ(y)) 及 d_j(φ(x),φ(y)) ≤ L_{j→j}d_j(x,y)。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```