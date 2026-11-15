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
