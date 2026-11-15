{}
已完成 [obligations.json](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/obligations.json) 中全部 8 项义务的形式化与内核验证（Lean 4.29.1 + 指定 mathlib，直接复用冻结前置模块 [gauge_space.lean](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean) 与 [operator_space.lean](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean)，未使用 `sorry`/`admit`/新增公理，全部声明仅依赖标准逻辑公理 `[propext, Classical.choice, Quot.sound]`）：

- [MatrixBounds.lean](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/LCH01/MatrixBounds.lean)：形式化 `CH02-D03`、`CH02-D01`、`CH02-D02`。
- [ChannelInterface.lean](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/LCH01/ChannelInterface.lean)：形式化 `CH02-D07`、`CH02-P19`、`CH02-P20`、`CH02-P21`、`CH02-P25`。
- [Main.lean](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/Main.lean) 与 [alignment.json](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/alignment.json)：入口汇总与完整对齐账本。

> **理论来源署名（CC BY 4.0）**：Zhe Li (also known as Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution Theory* ([01-foundations.md](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/source/01-foundations.md), [02-operator-bounds.md](file:///private/tmp/math-gauge-carbon-high-lane2-20261115-v1/attempts/LCH01/physical-1/session/work/source/02-operator-bounds.md)), https://glenzli.com/books/oet/, licensed under CC BY 4.0.

```lean filename=LCH01/MatrixBounds.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

set_option linter.style.longLine false

/-!
# 第 2 章 算子界 · 矩阵指标约定与 Lip / co-Lip 证书族

形式化覆盖义务：
- `CH02-D03`：输入/输出矩阵指标约定（输出分量为行指标 `j`、输入分量为列指标 `i`，即 $(\mathbf{M})_{ji} = M_{i \to j}$）与扩展非负矩阵乘法。
- `CH02-D01`：全域与子集受限 Lipschitz 矩阵谓词及证书族 $\mathscr{L}(\phi)$、$\mathscr{L}(\phi)\big|_U$。
- `CH02-D02`：含非空条件 $U \neq \emptyset$ 与定义域包含 $U \subseteq \mathrm{dom}(\phi)$ 的受限 co-Lipschitz 矩阵谓词及证书族 $\mathscr{K}(\phi)\big|_U$。
-/

/--
OET §2.1（`CH02-D03`）：以指标集 `I` 索引的扩展非负矩阵（条目取值于 $\bar{\mathbb{R}}_+ = \text{ENNReal}$）。
按正文行列约定，第一个参数为输出行指标 `j`，第二个参数为输入列指标 `i`。
-/
abbrev GaugeMatrix (I : Type) : Type := Matrix I I ENNReal

/--
OET §2.1（`CH02-D03`）：分量通道条目读取约定 $M_{i \to j} = (\mathbf{M})_{j i}$。
其中 `i` 为输入分量（列指标），`j` 为输出分量（行指标）。
-/
def channelEntry {I : Type} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

/--
OET §2.1（`CH02-D03`）：由输入到输出条目函数 `i ↦ j ↦ f i j` 构造矩阵，使得第 `j` 行、第 `i` 列等于 `f i j`。
-/
def ofChannelEntries {I : Type} (f : I → I → ENNReal) : GaugeMatrix I :=
  Matrix.of fun j i => f i j

/--
OET §2.1（`CH02-D03`）：扩展非负矩阵乘法 $\mathbf{M}_2 \cdot \mathbf{M}_1$，遵循 $\bar{\mathbb{R}}_+$ 标准算术（含 $0 \cdot +\infty = 0$）。
-/
noncomputable def gaugeMatrixMul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) : GaugeMatrix I :=
  M₂ * M₁

/-- 行列指标与箭头记号的对应：$(\mathbf{M})_{j i} = M_{i \to j}$。 -/
@[simp]
theorem channelEntry_eq_row_col {I : Type} (M : GaugeMatrix I) (i j : I) :
    channelEntry M i j = M j i :=
  rfl

/-- 由输入/输出条目函数构造的矩阵在通道 `(i, j)` 处还原 `f i j`。 -/
@[simp]
theorem channelEntry_ofChannelEntries {I : Type} (f : I → I → ENNReal) (i j : I) :
    channelEntry (ofChannelEntries f) i j = f i j :=
  rfl

/--
OET §2.1（`CH02-D03`）：矩阵乘积在输入/输出通道指标下的展开式
$(\mathbf{M}_2 \cdot \mathbf{M}_1)_{i \to j} = \sum_{k \in I} M^{(2)}_{k \to j} \cdot M^{(1)}_{i \to k}$。
-/
theorem channelEntry_mul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    channelEntry (gaugeMatrixMul M₂ M₁) i j =
      ∑ k : I, channelEntry M₂ k j * channelEntry M₁ i k := by
  simp [channelEntry, gaugeMatrixMul, Matrix.mul_apply]

/-- 标准 `*` 记号下的通道条目展开式。 -/
theorem channelEntry_hmul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    channelEntry (M₂ * M₁) i j =
      ∑ k : I, channelEntry M₂ k j * channelEntry M₁ i k :=
  channelEntry_mul M₂ M₁ i j

/--
OET §2.1（`CH02-D01`）：全域合法 Lipschitz 矩阵谓词。
对所有 $x, y \in \mathrm{dom}(\phi)$ 和所有 $j \in I$，满足
$d_j(\phi(x), \phi(y)) \le \sum_{i \in I} L_{i \to j} \cdot d_i(x, y)$。
-/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/--
OET §2.1（`CH02-D01`）：算子 $\phi$ 的全体合法全域 Lipschitz 矩阵证书族 $\mathscr{L}(\phi)$。
-/
def lipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/--
OET §2.1（`CH02-D01`）：子集受限合法 Lipschitz 矩阵谓词。
要求 $U \subseteq \mathrm{dom}(\phi)$，且对所有 $x, y \in U$ 和所有 $j \in I$ 满足距离上界放缩不等式。
-/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/--
OET §2.1（`CH02-D01`）：算子 $\phi$ 在子集 $U$ 上的受限 Lipschitz 矩阵证书族 $\mathscr{L}(\phi)\big|_U$。
-/
def restrictedLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

/-- 在完整定义域 $\mathrm{dom}(\phi)$ 上的受限 Lip 谓词与全域 Lip 谓词等价。 -/
@[simp]
theorem isRestrictedLipMatrix_dom_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsRestrictedLipMatrix d ϕ (dom ϕ) L ↔ IsLipMatrix d ϕ L := by
  simp [IsRestrictedLipMatrix, IsLipMatrix]

/-- 在完整定义域 $\mathrm{dom}(\phi)$ 上的受限 Lip 证书族等于全域证书族 $\mathscr{L}(\phi)$。 -/
@[simp]
theorem restrictedLipFamily_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedLipFamily d ϕ (dom ϕ) = lipFamily d ϕ := by
  ext L
  exact isRestrictedLipMatrix_dom_iff d ϕ L

/--
OET §2.1（`CH02-D02`）：子集受限合法 co-Lipschitz 矩阵谓词。
显式包含定义域子集条件 $U \subseteq \mathrm{dom}(\phi)$ 与非空条件 $U \neq \emptyset$，
并要求对所有 $x, y \in U$ 和所有 $j \in I$ 满足
$\sum_{i \in I} K_{i \to j} \cdot d_i(x, y) \le d_j(\phi(x), \phi(y))$。
-/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧ U.Nonempty ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/--
OET §2.1（`CH02-D02`）：算子 $\phi$ 在非空定义域子集 $U$ 上的受限 co-Lipschitz 矩阵证书族 $\mathscr{K}(\phi)\big|_U$。
-/
def restrictedCoLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

/-- 空集不满足受限 co-Lip 的非空条件，故空集上的受限 co-Lip 证书族为空集。 -/
@[simp]
theorem restrictedCoLipFamily_empty {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedCoLipFamily d ϕ ∅ = ∅ := by
  ext K
  simp [restrictedCoLipFamily, IsRestrictedCoLipMatrix]
```

```lean filename=LCH01/ChannelInterface.lean
import LCH01.MatrixBounds

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

set_option linter.style.longLine false

/-!
# 第 2 章 算子界 · 分量通道接口与习题 2.2

形式化覆盖义务：
- `CH02-D07`：分量通道 $(i, j)$、单输入通道/单行稀疏条件与对角矩阵特例。
- `CH02-P19`：单一输入项行化简及对角矩阵同分量通道特例。
- `CH02-P20`：命题 2.8 (i) 正 co-Lip 通道保持正距离。
- `CH02-P21`：命题 2.8 (ii) 全对角正 co-Lip 反射族零距关系（保持 $\sim_{\mathcal{G}}$，不加强为点相等）。
- `CH02-P25`：习题 2.2 对角输入项的标量双侧界。
-/

/--
OET §2.2（`CH02-D07`）：从输入分量 $d_i$ 到输出分量 $d_j$ 的分量通道有序对 $(i, j)$。
-/
abbrev ComponentChannel (I : Type) : Type := I × I

/--
OET §2.2（`CH02-D07`）：同分量（对角）通道 $(i, i)$。
-/
def diagChannel {I : Type} (i : I) : ComponentChannel I := (i, i)

/--
OET §2.2（`CH02-D07`）：矩阵 `M` 在分量通道 `c = (i, j)` 上的系数 $M_{i \to j}$。
-/
def channelCoeff {I : Type} (M : GaugeMatrix I) (c : ComponentChannel I) : ENNReal :=
  channelEntry M c.1 c.2

/--
OET §2.2（`CH02-D07`）：单行稀疏（单输入通道）条件——第 `j` 行除输入通道 `(i, j)` 的条目 $M_{i \to j}$ 外均为零，
即 $\forall k \neq i,\; M_{k \to j} = 0$。
-/
def IsSingleInputRow {I : Type} (M : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → channelEntry M k j = 0

/--
OET §2.2 & 习题 2.2（`CH02-D07`）：第 `j` 行只保留对角输入项 `(j, j)` 的稀疏条件，
即 $\forall k \neq j,\; M_{k \to j} = 0$。
-/
abbrev IsDiagonalRow {I : Type} (M : GaugeMatrix I) (j : I) : Prop :=
  IsSingleInputRow M j j

/--
OET §2.2（`CH02-D07`）：对角矩阵特例——所有跨分量通道条目均为零，
即 $\forall i, j \in I,\; i \neq j \Rightarrow M_{i \to j} = 0$。
-/
def IsDiagonalGaugeMatrix {I : Type} (M : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → channelEntry M i j = 0

/-- 对角规范矩阵谓词等价于行列表示下所有非对角元为零（$\forall j \neq i,\; (\mathbf{M})_{ji} = 0$）。 -/
theorem isDiagonalGaugeMatrix_iff_offDiag_zero {I : Type} (M : GaugeMatrix I) :
    IsDiagonalGaugeMatrix M ↔ ∀ j i : I, j ≠ i → M j i = 0 := by
  constructor
  · intro h j i hji
    exact h i j hji.symm
  · intro h i j hij
    exact h j i hij.symm

/-- 矩阵为对角矩阵当且仅当每一输出行都只保留同分量对角输入项。 -/
theorem isDiagonalGaugeMatrix_iff_forall_diagonalRow {I : Type} (M : GaugeMatrix I) :
    IsDiagonalGaugeMatrix M ↔ ∀ j : I, IsDiagonalRow M j := by
  constructor
  · intro h j k hkj
    exact h k j hkj
  · intro h i j hij
    exact h j i hij

/--
OET §2.2（`CH02-P19`）：当第 `j` 行除 $L_{i \to j}$ 外均为零时，行加权距离和化简为单一输入项
$\sum_{k \in I} L_{k \to j} d_k(x, y) = L_{i \to j} d_i(x, y)$。
-/
theorem single_input_row_sum_eq {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) (i j : I)
    (hrow : IsSingleInputRow L i j) (x y : X) :
    (∑ k : I, channelEntry L k j * d k x y) = channelEntry L i j * d i x y := by
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/--
OET §2.2（`CH02-P19`）：单一输入项行化简。
设 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$（含 $U \subseteq \mathrm{dom}(\phi)$），且第 `j` 行除 $L_{i \to j}$ 外均为零，
则对任意 $x, y \in U$，有
$\sum_{k \in I} L_{k \to j} d_k(x, y) = L_{i \to j} d_i(x, y)$ 且
$d_j(\phi(x), \phi(y)) \le L_{i \to j} d_i(x, y)$。
-/
theorem restricted_lip_single_input_row {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipFamily d ϕ U) (i j : I)
    (hrow : IsSingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      (∑ k : I, channelEntry L k j * d k x y) = channelEntry L i j * d i x y ∧
        d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L i j * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, channelEntry L k j * d k x y) = channelEntry L i j * d i x y :=
    single_input_row_sum_eq d L i j hrow x y
  refine ⟨hsum, ?_⟩
  calc
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k j * d k x y := hL.2 x hx y hy j
    _ = channelEntry L i j * d i x y := hsum

/--
OET §2.2（`CH02-P19` 对角特例）：若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 为对角矩阵，
则对每个同分量通道 $(i, i)$ 及任意 $x, y \in U$，均有单输入项行化简与标量上界
$d_i(\phi(x), \phi(y)) \le L_{i \to i} d_i(x, y)$。
-/
theorem restricted_lip_diagonal {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipFamily d ϕ U)
    (hdiag : IsDiagonalGaugeMatrix L) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      (∑ k : I, channelEntry L k i * d k x y) = channelEntry L i i * d i x y ∧
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  intro i x hx y hy
  have hrow : IsSingleInputRow L i i :=
    (isDiagonalGaugeMatrix_iff_forall_diagonalRow L).mp hdiag i
  exact restricted_lip_single_input_row d ϕ U L hL i i hrow x hx y hy

/--
辅助引理：受限 co-Lip 证书给出任一单通道下界
$K_{i \to j} d_i(x, y) \le d_j(\phi(x), \phi(y))$（$x, y \in U$）。
-/
theorem restricted_colip_channel_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipFamily d ϕ U) (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  calc
    channelEntry K i j * d i x y
        ≤ ∑ k : I, channelEntry K k j * d k x y := by
          exact Finset.single_le_sum
            (f := fun k => channelEntry K k j * d k x y)
            (fun k _ => zero_le (channelEntry K k j * d k x y))
            (Finset.mem_univ i)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
OET 命题 2.8 (i)（`CH02-P20`）：正 co-Lip 通道保持正距离（可分辨性）。
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且 $K_{i \to j} > 0$，则对任意 $x, y \in U$，
$d_i(x, y) > 0 \Rightarrow d_j(\phi(x), \phi(y)) > 0$。
-/
theorem restricted_colip_pos_channel {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipFamily d ϕ U) {i j : I}
    (hpos : 0 < channelEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdi
  have hmul_pos : 0 < channelEntry K i j * d i x y :=
    ENNReal.mul_pos (pos_iff_ne_zero.mp hpos) (pos_iff_ne_zero.mp hdi)
  exact lt_of_lt_of_le hmul_pos (restricted_colip_channel_le d ϕ U K hK i j x hx y hy)

/--
OET 命题 2.8 (ii)（`CH02-P21`）：全对角正 co-Lip 反射族零距关系。
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且对所有 $j \in I$ 有 $K_{j \to j} > 0$，
则对任意 $x, y \in U$，$\phi(x) \sim_{\mathcal{G}} \phi(y) \Rightarrow x \sim_{\mathcal{G}} y$
（结论严格保持 `GaugeZeroRelated`，不预设族分离性、不加强为 $x = y$）。
-/
theorem restricted_colip_reflects_gauge_zero {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipFamily d ϕ U)
    (hdiag_pos : ∀ j : I, 0 < channelEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hdj_ne
  have hdj_pos : 0 < d j x y := pos_iff_ne_zero.mpr hdj_ne
  have hphi_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    restricted_colip_pos_channel d ϕ U K hK (hdiag_pos j) x hx y hy hdj_pos
  exact (ne_of_gt hphi_pos) (hzero j)

/--
OET 习题 2.2（`CH02-P25`）：对角输入项的标量双侧界。
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$U \subseteq \mathrm{dom}(\phi)$，$j \in I$，
给定 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 与 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。
若第 $j$ 行满足 $\forall k \neq j,\; L_{k \to j} = 0$（即 `IsDiagonalRow L j`），
则对任意 $x, y \in U$ 有
$K_{j \to j} \cdot d_j(x, y) \le d_j(\phi(x), \phi(y)) \le L_{j \to j} \cdot d_j(x, y)$。
-/
theorem scalar_two_sided_bound_of_diagonal_row {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I)
    (L K : GaugeMatrix I)
    (hL : L ∈ restrictedLipFamily d ϕ U)
    (hK : K ∈ restrictedCoLipFamily d ϕ U)
    (hL_row : IsDiagonalRow L j) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L j j * d j x y := by
  intro x hx y hy
  refine ⟨restricted_colip_channel_le d ϕ U K hK j j x hx y hy, ?_⟩
  exact (restricted_lip_single_input_row d ϕ U L hL j j hL_row x hx y hy).2
```

```lean filename=Main.lean
import LCH01.MatrixBounds
import LCH01.ChannelInterface

def main : IO Unit := pure ()
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
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "IsLipMatrix"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "lipFamily"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "IsRestrictedLipMatrix"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "restrictedLipFamily"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "isRestrictedLipMatrix_dom_iff"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "restrictedLipFamily_dom"
        }
      ],
      "representation": "对象与参数：以底层类型 X、吸收元 bot : X、有限指标集 I ([Fintype I])、分量距离族 d : I → X → X → ENNReal、算子 ϕ : Operator X bot、子集 U : Set X 及扩展非负矩阵 L : GaugeMatrix I 表示原文对象。量词与定义域：IsLipMatrix 量化 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I，要求 d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y；lipFamily 为满足该谓词的全体矩阵集合 mathscr{L}(ϕ)。IsRestrictedLipMatrix 显式包含定义域限制 U ⊆ dom ϕ 并量化 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I 满足同一上界放缩不等式；restrictedLipFamily 为对应的受限证书族 mathscr{L}(ϕ)|_U，并由 restrictedLipFamily_dom 确认 U = dom ϕ 时与全域证书族一致。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "IsRestrictedCoLipMatrix"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "restrictedCoLipFamily"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "restrictedCoLipFamily_empty"
        }
      ],
      "representation": "对象与参数：同以 d : I → X → X → ENNReal ([Fintype I])、ϕ : Operator X bot、U : Set X 与 K : GaugeMatrix I 表示。量词、定义域与结论：IsRestrictedCoLipMatrix 显式合取 U ⊆ dom ϕ 与非空条件 U.Nonempty（对应原文 U ≠ ∅），并量化 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I 要求 ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)。restrictedCoLipFamily 定义受限证书族 mathscr{K}(ϕ)|_U := { K | IsRestrictedCoLipMatrix d ϕ U K }，使任何 K ∈ restrictedCoLipFamily d ϕ U 均自带 U ⊆ dom ϕ 与 U ≠ ∅（restrictedCoLipFamily_empty 验证空集上证书族为空）。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "GaugeMatrix"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "channelEntry"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "ofChannelEntries"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "gaugeMatrixMul"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "channelEntry_eq_row_col"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "channelEntry_ofChannelEntries"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "channelEntry_mul"
        },
        {
          "file": "LCH01/MatrixBounds.lean",
          "name": "channelEntry_hmul"
        }
      ],
      "representation": "对象与参数：GaugeMatrix I := Matrix I I ENNReal 表示条目取值于扩展非负实数 ENNReal（自动满足 0 * ⊤ = 0 与 ⊤ * 0 = 0 约定）的方阵，第一个指标为行（输出分量 j）、第二个指标为列（输入分量 i）。指标约定与乘法：channelEntry M i j := M j i 对应 M_{i → j} = (M)_{j i}，ofChannelEntries 由 i → j 条目函数构造矩阵；gaugeMatrixMul M₂ M₁ := M₂ * M₁ 定义有限指标集 ([Fintype I]) 上的矩阵乘法，channelEntry_mul 与 channelEntry_hmul 证明通道指标下的乘积展开式 (M₂ · M₁)_{i → j} = ∑ k : I, M₂_{k → j} * M₁_{i → k}。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "ComponentChannel"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "diagChannel"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "channelCoeff"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "IsSingleInputRow"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "IsDiagonalRow"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "IsDiagonalGaugeMatrix"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "isDiagonalGaugeMatrix_iff_offDiag_zero"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "isDiagonalGaugeMatrix_iff_forall_diagonalRow"
        }
      ],
      "representation": "对象与参数：ComponentChannel I := I × I 表示从输入分量 i 到输出分量 j 的有序对通道 (i, j)，diagChannel i := (i, i) 表示同分量通道，channelCoeff 提取通道系数 M_{i → j}。稀疏与对角谓词：IsSingleInputRow M i j 定义单行单输入稀疏条件 ∀ k : I, k ≠ i → channelEntry M k j = 0（第 j 行除 M_{i → j} 外均为零）；IsDiagonalRow M j := IsSingleInputRow M j j 为第 j 行仅保留对角输入项；IsDiagonalGaugeMatrix M 定义对角矩阵条件 ∀ i j : I, i ≠ j → channelEntry M i j = 0，并证明其与非对角行列元归零及全行对角稀疏的等价刻画。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "single_input_row_sum_eq"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "restricted_lip_single_input_row"
        },
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "restricted_lip_diagonal"
        }
      ],
      "representation": "前提与量词：设有限指标集 [Fintype I]、算子 ϕ : Operator X bot、受限证书 hL : L ∈ restrictedLipFamily d ϕ U（含定义域条件 U ⊆ dom ϕ）。结论对应：(1) single_input_row_sum_eq 与 restricted_lip_single_input_row 在单行稀疏前提 IsSingleInputRow L i j 下，对 ∀ x ∈ U, ∀ y ∈ U 证明行和恒等式 (∑ k : I, channelEntry L k j * d k x y) = channelEntry L i j * d i x y 及化简后的 Lip 上界 d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L i j * d i x y；(2) restricted_lip_diagonal 在对角前提 IsDiagonalGaugeMatrix L 下，对每个同分量通道 ∀ i : I 及 ∀ x ∈ U, ∀ y ∈ U 给出相同的行化简等式与对角标量上界 d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D07"
      ]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "restricted_colip_pos_channel"
        }
      ],
      "representation": "对应命题 2.8 (i)。前提与量词：设有限指标集 [Fintype I]、受限 co-Lip 证书 hK : K ∈ restrictedCoLipFamily d ϕ U（含 U ⊆ dom ϕ 与 U.Nonempty）及正通道条件 hpos : 0 < channelEntry K i j，对任意点对 ∀ x ∈ U, ∀ y ∈ U 量化。结论：0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y)，完整覆盖有限正值与 +∞ (⊤) 情形。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "restricted_colip_reflects_gauge_zero"
        }
      ],
      "representation": "对应命题 2.8 (ii)。前提与量词：设有限指标集 [Fintype I]、受限 co-Lip 证书 hK : K ∈ restrictedCoLipFamily d ϕ U 及全对角严格正条件 hdiag_pos : ∀ j : I, 0 < channelEntry K j j，对 ∀ x ∈ U, ∀ y ∈ U 量化。结论强度：直接复用前置模块 gauge_space.lean 中的 GaugeZeroRelated，证明 GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y（即 ϕ(x) ~_G ϕ(y) ⇒ x ~_G y），不附加族分离性假设，亦不将结论加强为 x = y。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-P20"
      ]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH01/ChannelInterface.lean",
          "name": "scalar_two_sided_bound_of_diagonal_row"
        }
      ],
      "representation": "对应习题 2.2。前提与量词：给定有限指标集 [Fintype I]、ϕ : Operator X bot、U : Set X、输出分量 j : I、受限 Lip 证书 hL : L ∈ restrictedLipFamily d ϕ U（含 U ⊆ dom ϕ）、受限 co-Lip 证书 hK : K ∈ restrictedCoLipFamily d ϕ U（含 U ⊆ dom ϕ 与 U.Nonempty），以及第 j 行只保留对角输入项的条件 hL_row : IsDiagonalRow L j（即 ∀ k ≠ j, L_{k → j} = 0）。结论：对 ∀ x ∈ U, ∀ y ∈ U，证明标量双侧不等式 channelEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧ d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L j j * d j x y。",
      "dependencies": [
        "CH02-D01",
        "CH02-D02",
        "CH02-D03",
        "CH02-D07",
        "CH02-P19"
      ]
    }
  ]
}
```
