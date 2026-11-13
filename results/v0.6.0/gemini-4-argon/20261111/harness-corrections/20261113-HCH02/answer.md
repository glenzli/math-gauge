已完成第2章《算子界》（[02-operator-bounds.md](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/source/02-operator-bounds.md)）全部数学内容与 [obligations.json](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/obligations.json) 中全部 40 项义务（`HC02-D01` 至 `HC02-D08`，`HC02-P01` 至 `HC02-P32`）的 Lean 4.29.1 形式化验证。

所有目标定义与定理均实现在 [Main.lean](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/Main.lean) 的命名空间 `formal_oet.vol_01.ch_02_operator_bounds` 中，直接复用冻结前置模块 [gauge_space.lean](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean)（[`ExtendedPseudoMetric`](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L9-L15)、[`GaugeZeroRelated`](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L24-L25)）与 [operator_space.lean](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean)（[`Operator`](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean#L8-L10)、[`dom`](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean#L17-L18)、[`operator_image`](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean#L21-L22)、[`OperatorChain`](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean#L36-L38)），对齐清单保存在 [alignment.json](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/alignment.json)。

### 完整源码 `Main.lean`

```lean filename=Main.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

/-!
# 第2章 算子界 (Operator Bounds)

本文件完整形式化第2章《算子界》（`source/02-operator-bounds.md`）的全部数学内容，
严格覆盖 `obligations.json` 中的全部40项定义、表示及证明义务（`HC02-D01` 至 `HC02-D08`，
`HC02-P01` 至 `HC02-P32`）。
-/

/-!
## 1. 矩阵表示、复合与有限链基础 (`HC02-D01` – `HC02-D06`)
-/

/--
**义务 `HC02-D03`（输入优先存储的规范界矩阵）**：
`GaugeMatrix I` 以输入优先方式存储：`M i j` 表示从输入分量 `i` 到输出分量 `j` 的系数 $M_{i \to j} \in \bar{\mathbb{R}}_+$。
-/
abbrev GaugeMatrix (I : Type) : Type := I → I → ENNReal

/--
**义务 `HC02-D03`（显示矩阵表示）**：
写成通常的行列矩阵时，输出指标 `j` 标记行，输入指标 `i` 标记列，
即第 `j` 行第 `i` 列的条目为 `M i j`（$M_{i \to j}$）。
-/
def toDisplayMatrix {I : Type} (M : GaugeMatrix I) : Matrix I I ENNReal :=
  fun j i => M i j

/--
**义务 `HC02-D03`（从显示矩阵还原输入优先矩阵）**：
将第 `j` 行第 `i` 列的显示矩阵还原为输入优先表示。
-/
def ofDisplayMatrix {I : Type} (A : Matrix I I ENNReal) : GaugeMatrix I :=
  fun i j => A j i

/--
**义务 `HC02-D03`（矩阵的第 `j` 行与第 `i` 列）**：
固定输出指标 `j` 为第 `j` 行；固定输入指标 `i` 为第 `i` 列。
-/
def gaugeMatrixRow {I : Type} (M : GaugeMatrix I) (j : I) : I → ENNReal :=
  fun i => M i j

def gaugeMatrixCol {I : Type} (M : GaugeMatrix I) (i : I) : I → ENNReal :=
  fun j => M i j

@[simp]
theorem toDisplayMatrix_apply {I : Type} (M : GaugeMatrix I) (j i : I) :
    toDisplayMatrix M j i = M i j := rfl

@[simp]
theorem ofDisplayMatrix_toDisplayMatrix {I : Type} (M : GaugeMatrix I) :
    ofDisplayMatrix (toDisplayMatrix M) = M := rfl

@[simp]
theorem toDisplayMatrix_ofDisplayMatrix {I : Type} (A : Matrix I I ENNReal) :
    toDisplayMatrix (ofDisplayMatrix A) = A := rfl

/--
**义务 `HC02-D03`（规范界矩阵乘法）**：
复合律 $(\mathbf{M}_2 \cdot \mathbf{M}_1)_{i \to j} = \sum_{k \in I} (\mathbf{M}_2)_{k \to j} (\mathbf{M}_1)_{i \to k}$。
-/
noncomputable def gaugeMatrixMul {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) : GaugeMatrix I :=
  fun i j => ∑ k : I, M₂ k j * M₁ i k

@[simp]
theorem gaugeMatrixMul_apply {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) (i j : I) :
    gaugeMatrixMul M₂ M₁ i j = ∑ k : I, M₂ k j * M₁ i k := rfl

/--
**义务 `HC02-D03`（显示矩阵乘法与输入优先复合乘法的一致性）**：
在输出指标 `j` 标记行、输入指标 `i` 标记列的约定下，
`gaugeMatrixMul M₂ M₁` 的显示矩阵恰好等于标准矩阵乘法 `toDisplayMatrix M₂ * toDisplayMatrix M₁`。
-/
theorem toDisplayMatrix_gaugeMatrixMul {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) :
    toDisplayMatrix (gaugeMatrixMul M₂ M₁) = toDisplayMatrix M₂ * toDisplayMatrix M₁ := by
  ext j i
  simp [toDisplayMatrix, gaugeMatrixMul, Matrix.mul_apply]

/-- 规范界矩阵乘法的结合律。 -/
theorem gaugeMatrixMul_assoc {I : Type} [Fintype I] (M₃ M₂ M₁ : GaugeMatrix I) :
    gaugeMatrixMul (gaugeMatrixMul M₃ M₂) M₁ = gaugeMatrixMul M₃ (gaugeMatrixMul M₂ M₁) := by
  ext i j
  simp only [gaugeMatrixMul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/--
**义务 `HC02-D04`（单位矩阵）**：
单位矩阵 $\mathbf{I}_{i \to j} = \delta_{ij}$。
-/
noncomputable def gaugeMatrixId (I : Type) : GaugeMatrix I :=
  fun i j => if i = j then 1 else 0

@[simp]
theorem gaugeMatrixId_apply {I : Type} (i j : I) :
    gaugeMatrixId I i j = if i = j then 1 else 0 := rfl

@[simp]
theorem gaugeMatrixId_self {I : Type} (i : I) :
    gaugeMatrixId I i i = 1 := by
  simp [gaugeMatrixId]

theorem gaugeMatrixId_ne {I : Type} {i j : I} (h : i ≠ j) :
    gaugeMatrixId I i j = 0 := by
  simp [gaugeMatrixId, h]

@[simp]
theorem gaugeMatrixMul_id_left {I : Type} [Fintype I] (M : GaugeMatrix I) :
    gaugeMatrixMul (gaugeMatrixId I) M = M := by
  ext i j
  simp [gaugeMatrixMul, gaugeMatrixId]

@[simp]
theorem gaugeMatrixMul_id_right {I : Type} [Fintype I] (M : GaugeMatrix I) :
    gaugeMatrixMul M (gaugeMatrixId I) = M := by
  ext i j
  simp [gaugeMatrixMul, gaugeMatrixId]

/--
**义务 `HC02-D04`（按施行顺序排列的矩阵有限乘积）**：
给定按算子施行顺序排列的矩阵列表 `[L₁, L₂, …, Lₖ]`（对应先施行 $\phi_1$、最后施行 $\phi_k$），
定义其有序乘积 $\mathbf{L}^{(k)} \cdot \cdots \cdot \mathbf{L}^{(1)}$：
- 空乘积（$k=0$）为单位矩阵 `gaugeMatrixId I`；
- 单元素列表（$k=1$）等于该唯一矩阵 `M`；
- 多步列表 `[M₁, M₂, …, Mₖ]` 为 `(Mₖ ⋯ M₂) · M₁`。
-/
noncomputable def gaugeMatrixChainProd {I : Type} [Fintype I] : List (GaugeMatrix I) → GaugeMatrix I
  | [] => gaugeMatrixId I
  | [M] => M
  | M :: rest => gaugeMatrixMul (gaugeMatrixChainProd rest) M

@[simp]
theorem gaugeMatrixChainProd_nil {I : Type} [Fintype I] :
    gaugeMatrixChainProd ([] : List (GaugeMatrix I)) = gaugeMatrixId I := rfl

@[simp]
theorem gaugeMatrixChainProd_singleton {I : Type} [Fintype I] (M : GaugeMatrix I) :
    gaugeMatrixChainProd [M] = M := rfl

@[simp]
theorem gaugeMatrixChainProd_cons {I : Type} [Fintype I]
    (M : GaugeMatrix I) (rest : List (GaugeMatrix I)) :
    gaugeMatrixChainProd (M :: rest) = gaugeMatrixMul (gaugeMatrixChainProd rest) M := by
  cases rest with
  | nil => simp [gaugeMatrixChainProd]
  | cons M₂ tail => rfl

@[simp]
theorem gaugeMatrixChainProd_pair {I : Type} [Fintype I] (M₁ M₂ : GaugeMatrix I) :
    gaugeMatrixChainProd [M₁, M₂] = gaugeMatrixMul M₂ M₁ := rfl

/--
**义务 `HC02-D01`（全域及受限 Lipschitz 矩阵与证书族）**：
在有限非空指标集 `I`、扩展伪度量族 `d` 与保持 `bot` 的算子 `ϕ : Operator X bot` 下，
定义全域合法 Lip 矩阵集合 $\mathscr{L}(\phi)$ 与子集受限合法 Lip 矩阵集合 $\mathscr{L}(\phi)\big|_U$。
-/
def LipMatrices {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y }

def RestrictedLipMatrices {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y }

/-- 全域 Lip 证书族等于在 `dom ϕ` 上的受限 Lip 证书族。 -/
theorem lipMatrices_eq_restrictedLipMatrices_dom
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) :
    LipMatrices d ϕ = RestrictedLipMatrices d ϕ (dom ϕ) := by
  ext L
  simp [LipMatrices, RestrictedLipMatrices]

/--
**义务 `HC02-D02`（含非空性的子集受限 co-Lipschitz 矩阵与证书族）**：
定义 $\mathscr{K}(\phi)\big|_U$，显式包含 $U \neq \emptyset$（`U.Nonempty`）、$U \subseteq \mathrm{dom}(\phi)$，
以及对所有 $x, y \in U$ 和 $j \in I$ 满足 $\sum_{i \in I} K_{i \to j} d_i(x, y) \le d_j(\phi(x), \phi(y))$。
系数取值于 `ENNReal`（`0` 与 `⊤` 均为合法系数）。
-/
def RestrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y) }

/-- 在任意非空定义域子集上，全零矩阵（系数为 `0`）是合法的受限 co-Lip 矩阵。 -/
theorem zeroMatrix_mem_restrictedCoLipMatrices
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ) :
    (fun _ _ => (0 : ENNReal)) ∈ RestrictedCoLipMatrices d ϕ U := by
  refine ⟨hU_ne, hU_dom, ?_⟩
  intro x _ y _ j
  simp

/-- 恒等算子 $\mathrm{id}_{\mathcal{X}}$。 -/
def idOperator (X : Type) (bot : X) : Operator X bot :=
  ⟨id, rfl⟩

/-- 两个算子的复合 $\phi_2 \circ \phi_1$。 -/
def compOperator {X : Type} {bot : X} (ϕ₂ ϕ₁ : Operator X bot) : Operator X bot :=
  ⟨ϕ₂.func ∘ ϕ₁.func, by simp [ϕ₁.preserves_bot, ϕ₂.preserves_bot]⟩

@[simp]
theorem idOperator_func {X : Type} {bot : X} (x : X) :
    (idOperator X bot).func x = x := rfl

@[simp]
theorem compOperator_func {X : Type} {bot : X} (ϕ₂ ϕ₁ : Operator X bot) (x : X) :
    (compOperator ϕ₂ ϕ₁).func x = ϕ₂.func (ϕ₁.func x) := rfl

/--
**义务 `HC02-D04` & `HC02-D05`（按施行顺序排列的有限算子复合链）**：
给定按施行顺序排列的算子列表 `[ϕ₁, ϕ₂, …, ϕₖ]`，其复合为 $c_k = \phi_k \circ \cdots \circ \phi_1$；
当 $k=0$（空列表）时为恒等算子 `idOperator X bot`。
-/
def composeOperatorChain {X : Type} {bot : X} : List (Operator X bot) → Operator X bot
  | [] => idOperator X bot
  | [ϕ] => ϕ
  | ϕ :: rest => compOperator (composeOperatorChain rest) ϕ

@[simp]
theorem composeOperatorChain_nil {X : Type} {bot : X} :
    composeOperatorChain ([] : List (Operator X bot)) = idOperator X bot := rfl

@[simp]
theorem composeOperatorChain_singleton {X : Type} {bot : X} (ϕ : Operator X bot) :
    composeOperatorChain [ϕ] = ϕ := rfl

@[simp]
theorem composeOperatorChain_cons {X : Type} {bot : X}
    (ϕ : Operator X bot) (rest : List (Operator X bot)) :
    composeOperatorChain (ϕ :: rest) = compOperator (composeOperatorChain rest) ϕ := by
  cases rest with
  | nil =>
      ext x
      rfl
  | cons ϕ₂ tail => rfl

@[simp]
theorem composeOperatorChain_pair {X : Type} {bot : X} (ϕ₁ ϕ₂ : Operator X bot) :
    composeOperatorChain [ϕ₁, ϕ₂] = compOperator ϕ₂ ϕ₁ := rfl

/-- `composeOperatorChain` 与第1章辅助定义 `OperatorChain`（逆序列表）完全一致。 -/
theorem composeOperatorChain_eq_operatorChain_reverse
    {X : Type} {bot : X} (ϕs : List (Operator X bot)) :
    composeOperatorChain ϕs = OperatorChain ϕs.reverse := by
  induction ϕs with
  | nil => rfl
  | cons ϕ rest ih =>
      ext x
      simp only [composeOperatorChain_cons, compOperator_func, ih, List.reverse_cons]
      clear ih
      induction rest.reverse generalizing x with
      | nil => rfl
      | cons ψ tail ih_rev =>
          simp [OperatorChain, Function.comp_apply, ih_rev]

/--
**义务 `HC02-D05`（中间实际像集递推定义 $U_{m+1} = \phi_m(U_m)$）**：
对算子链 `ϕs = [ϕ₁, …, ϕₖ]` 与起始定义域子集 `U₁`：
- `chainImageAt ϕs U₁ 0 = U₁`（即正文的 $U_1$）；
- `chainImageAt ϕs U₁ (m + 1) = ϕ_{m+1}(U_{m+1})`（即正文的 $U_{m+2} = \phi_{m+1}(U_{m+1})$）。
-/
def chainImageAt {X : Type} {bot : X} : List (Operator X bot) → Set X → ℕ → Set X
  | [], U, _ => U
  | _, U, 0 => U
  | ϕ :: rest, U, m + 1 => chainImageAt rest (operator_image ϕ U) m

@[simp]
theorem chainImageAt_zero {X : Type} {bot : X} (ϕs : List (Operator X bot)) (U₁ : Set X) :
    chainImageAt ϕs U₁ 0 = U₁ := by
  cases ϕs <;> rfl

@[simp]
theorem chainImageAt_cons_succ {X : Type} {bot : X}
    (ϕ : Operator X bot) (rest : List (Operator X bot)) (U₁ : Set X) (m : ℕ) :
    chainImageAt (ϕ :: rest) U₁ (m + 1) = chainImageAt rest (operator_image ϕ U₁) m := rfl

/--
**义务 `HC02-D05`（中间像集逐步递推关系 $U_{m+1} = \phi_m(U_m)$）**：
对任意步指标 $m < k$，第 $m+1$ 层的输入域等于第 $m$ 步算子在第 $m$ 层输入域上的像集。
-/
theorem chainImageAt_succ_eq_image {X : Type} {bot : X}
    (ϕs : List (Operator X bot)) (U₁ : Set X) (m : ℕ) (hm : m < ϕs.length) :
    chainImageAt ϕs U₁ (m + 1) = operator_image (ϕs[m]) (chainImageAt ϕs U₁ m) := by
  induction ϕs generalizing U₁ m with
  | nil =>
      cases hm
  | cons ϕ rest ih =>
      cases m with
      | zero =>
          simp [chainImageAt]
      | succ m' =>
          have hm' : m' < rest.length := Nat.lt_of_succ_lt_succ hm
          simp only [chainImageAt_cons_succ, List.getElem_cons_succ]
          exact ih (operator_image ϕ U₁) m' hm'

/--
**义务 `HC02-D05`（两步复合像集等于逐次像集）**：
$(\phi_2 \circ \phi_1)(U_1) = \phi_2(\phi_1(U_1))$。
-/
theorem operator_image_compOperator {X : Type} {bot : X}
    (ϕ₂ ϕ₁ : Operator X bot) (U₁ : Set X) :
    operator_image (compOperator ϕ₂ ϕ₁) U₁ = operator_image ϕ₂ (operator_image ϕ₁ U₁) := by
  ext y
  simp [operator_image, compOperator, Set.mem_image]

/--
**义务 `HC02-D05`（全复合像等于逐次像）**：
经过全部 $k$ 步递推所得的像集 `chainImageAt ϕs U₁ ϕs.length` 等于全复合算子 `composeOperatorChain ϕs` 对 `U₁` 的像集。
-/
theorem chainImageAt_length_eq_compose_image {X : Type} {bot : X}
    (ϕs : List (Operator X bot)) (U₁ : Set X) :
    chainImageAt ϕs U₁ ϕs.length = operator_image (composeOperatorChain ϕs) U₁ := by
  induction ϕs generalizing U₁ with
  | nil =>
      ext x
      simp [chainImageAt, composeOperatorChain, operator_image, idOperator]
  | cons ϕ rest ih =>
      simp only [List.length_cons, chainImageAt_cons_succ, composeOperatorChain_cons]
      rw [ih (operator_image ϕ U₁), operator_image_compOperator]

/--
**义务 `HC02-D05`（两步复合定义域包含关系）**：
若 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，则 $U_1 \subseteq \mathrm{dom}(\phi_1)$ 且 $U_2 = \phi_1(U_1) \subseteq \mathrm{dom}(\phi_2)$。
-/
theorem dom_of_subset_dom_compOperator {X : Type} {bot : X}
    {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (compOperator ϕ₂ ϕ₁)) :
    U₁ ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  constructor
  · intro x hx
    have hcomp : ϕ₂.func (ϕ₁.func x) ≠ bot := hU₁ hx
    intro h_eq
    apply hcomp
    rw [h_eq, ϕ₂.preserves_bot]
  · rintro y ⟨x, hx, rfl⟩
    exact hU₁ hx

/--
**义务 `HC02-D05`（有限复合链各步实际输入域均含于对应算子定义域）**：
若 $U_1 \subseteq \mathrm{dom}(c_k)$，则对每一步 $m < k$ 均有 $U_m \subseteq \mathrm{dom}(\phi_m)$。
-/
theorem chainImageAt_subset_dom {X : Type} {bot : X}
    (ϕs : List (Operator X bot)) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (composeOperatorChain ϕs))
    (m : ℕ) (hm : m < ϕs.length) :
    chainImageAt ϕs U₁ m ⊆ dom (ϕs[m]) := by
  induction ϕs generalizing U₁ m with
  | nil =>
      cases hm
  | cons ϕ rest ih =>
      rw [composeOperatorChain_cons] at hU₁
      rcases dom_of_subset_dom_compOperator hU₁ with ⟨hU₁_ϕ, hU₂_rest⟩
      cases m with
      | zero =>
          simpa [chainImageAt] using hU₁_ϕ
      | succ m' =>
          have hm' : m' < rest.length := Nat.lt_of_succ_lt_succ hm
          simp only [chainImageAt_cons_succ, List.getElem_cons_succ]
          exact ih hU₂_rest m' hm'

/--
**义务 `HC02-D05`（由逐步矩阵和各实际输入域上的界构造的 Lip 证书链表示）**：
只记录算子链 `ϕs`、起始域 `U₁ ⊆ dom(c_k)`、逐步矩阵 `Ls` 以及各步在实际输入域 `U_m` 上的合法性，
**不**将最终复合界作为字段。
-/
structure LipChainData {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)] where
  ϕs : List (Operator X bot)
  U₁ : Set X
  hU₁ : U₁ ⊆ dom (composeOperatorChain ϕs)
  Ls : List (GaugeMatrix I)
  hlen : Ls.length = ϕs.length
  step_valid : ∀ (m : ℕ) (hm : m < ϕs.length),
    Ls[m]'(by omega) ∈ RestrictedLipMatrices d (ϕs[m]) (chainImageAt ϕs U₁ m)

/--
**义务 `HC02-D05`（由逐步矩阵和各实际输入域上的界构造的 co-Lip 证书链表示）**：
只记录算子链 `ϕs`、起始域 `U₁ ⊆ dom(c_k)`、逐步矩阵 `Ks` 以及各步在实际输入域 `U_m` 上的合法性（含非空性），
**不**将最终复合界作为字段。
-/
structure CoLipChainData {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)] where
  ϕs : List (Operator X bot)
  U₁ : Set X
  hU₁ : U₁ ⊆ dom (composeOperatorChain ϕs)
  Ks : List (GaugeMatrix I)
  hlen : Ks.length = ϕs.length
  step_valid : ∀ (m : ℕ) (hm : m < ϕs.length),
    Ks[m]'(by omega) ∈ RestrictedCoLipMatrices d (ϕs[m]) (chainImageAt ϕs U₁ m)

/--
**义务 `HC02-D06`（有限索引路径表示）**：
对步数 $n \ge 1$，固定起止指标 $k_0 = i$、$k_n = j$，中间指标序列遍历全部 `Fin (n - 1) → I`（无任何正性约束）。
当 $n = 1$ 时，`Fin 0 → I` 仅有唯一空中间序列。
-/
abbrev IntermediateIndexSeq (I : Type) (n : ℕ) : Type := Fin (n - 1) → I

/-- $n = 1$ 时的唯一空中间指标序列。 -/
def emptyIntermediateSeq (I : Type) : IntermediateIndexSeq I 1 :=
  fun r => Fin.elim0 r

instance uniqueIntermediateIndexSeqOne (I : Type) : Unique (IntermediateIndexSeq I 1) where
  default := emptyIntermediateSeq I
  uniq ks := by
    funext r
    exact Fin.elim0 r

/--
**义务 `HC02-D06`（完整路径在第 $m$ 层（$0 \le m < n$）的输入指标 $k_m$ 与输出指标 $k_{m+1}$）**：
约定 $k_0 = i$，$k_n = j$，中间指标为 $k_1, \dots, k_{n-1}$。
-/
def pathSourceIndex {I : Type} (n : ℕ) (i : I) (ks : IntermediateIndexSeq I n) (m : Fin n) : I :=
  if h0 : m.val = 0 then i else ks ⟨m.val - 1, by omega⟩

def pathTargetIndex {I : Type} (n : ℕ) (j : I) (ks : IntermediateIndexSeq I n) (m : Fin n) : I :=
  if hlast : m.val + 1 < n then ks ⟨m.val, by omega⟩ else j

@[simp]
theorem pathSourceIndex_zero {I : Type} {n : ℕ} (hn : 0 < n) (i : I) (ks : IntermediateIndexSeq I n) :
    pathSourceIndex n i ks ⟨0, hn⟩ = i := rfl

@[simp]
theorem pathTargetIndex_last {I : Type} {n : ℕ} (hn : 0 < n) (j : I) (ks : IntermediateIndexSeq I n) :
    pathTargetIndex n j ks ⟨n - 1, by omega⟩ = j := by
  have h : ¬ (n - 1 + 1 < n) := by omega
  unfold pathTargetIndex
  exact dif_neg h

@[simp]
theorem pathSourceIndex_one {I : Type} (i : I) (ks : IntermediateIndexSeq I 1) (m : Fin 1) :
    pathSourceIndex 1 i ks m = i := by
  have hm : m.val = 0 := by omega
  unfold pathSourceIndex
  exact dif_pos hm

@[simp]
theorem pathTargetIndex_one {I : Type} (j : I) (ks : IntermediateIndexSeq I 1) (m : Fin 1) :
    pathTargetIndex 1 j ks m = j := by
  have hm : ¬ (m.val + 1 < 1) := by omega
  unfold pathTargetIndex
  exact dif_neg hm

/--
**义务 `HC02-D06`（路径在第 $m$ 步的单步矩阵条目）**：
读取 `Ms[m]` 在通道 `pathSourceIndex → pathTargetIndex` 上的条目 $[\mathbf{M}^{(m+1)}]_{k_m \to k_{m+1}}$。
-/
def pathStepEntry {I : Type} (Ms : List (GaugeMatrix I)) (i j : I)
    (ks : IntermediateIndexSeq I Ms.length) (m : Fin Ms.length) : ENNReal :=
  (Ms[m.val]'m.isLt) (pathSourceIndex Ms.length i ks m) (pathTargetIndex Ms.length j ks m)

/--
**义务 `HC02-D06`（路径权重：各层条目的乘积）**：
沿完整路径 $(i = k_0, k_1, \dots, k_{n-1}, k_n = j)$ 的各层矩阵条目乘积。
-/
noncomputable def pathWeight {I : Type} (Ms : List (GaugeMatrix I)) (i j : I)
    (ks : IntermediateIndexSeq I Ms.length) : ENNReal :=
  ∏ m : Fin Ms.length, pathStepEntry Ms i j ks m

/--
**义务 `HC02-D06`（路径含零谓词）**：
存在至少一个层级 $m \in \{1, \dots, n\}$ 使得该步条目为 $0$。
-/
def PathHasZeroEdge {I : Type} (Ms : List (GaugeMatrix I)) (i j : I)
    (ks : IntermediateIndexSeq I Ms.length) : Prop :=
  ∃ m : Fin Ms.length, pathStepEntry Ms i j ks m = 0

/--
**义务 `HC02-D06`（路径全正谓词）**：
沿该路径的所有单步矩阵条目均严格正（$> 0$）。
-/
def PathAllPositive {I : Type} (Ms : List (GaugeMatrix I)) (i j : I)
    (ks : IntermediateIndexSeq I Ms.length) : Prop :=
  ∀ m : Fin Ms.length, 0 < pathStepEntry Ms i j ks m

@[simp]
theorem pathStepEntry_singleton {I : Type} (M : GaugeMatrix I) (i j : I)
    (ks : IntermediateIndexSeq I [M].length) :
    pathStepEntry [M] i j ks ⟨0, Nat.zero_lt_succ 0⟩ = M i j := by
  simp [pathStepEntry]

@[simp]
theorem pathWeight_singleton {I : Type} (M : GaugeMatrix I) (i j : I)
    (ks : IntermediateIndexSeq I [M].length) :
    pathWeight [M] i j ks = M i j := by
  unfold pathWeight
  have h : (Finset.univ : Finset (Fin [M].length)) = {⟨0, Nat.zero_lt_succ 0⟩} := by
    ext m
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    ext
    exact Nat.lt_one_iff.mp m.isLt
  rw [h, Finset.prod_singleton, pathStepEntry_singleton]

@[simp]
theorem pathHasZeroEdge_singleton_iff {I : Type} (M : GaugeMatrix I) (i j : I)
    (ks : IntermediateIndexSeq I [M].length) :
    PathHasZeroEdge [M] i j ks ↔ M i j = 0 := by
  constructor
  · rintro ⟨m, hm⟩
    have hm0 : m = ⟨0, Nat.zero_lt_succ 0⟩ := by
      ext
      exact Nat.lt_one_iff.mp m.isLt
    subst hm0
    simpa using hm
  · intro h
    exact ⟨⟨0, Nat.zero_lt_succ 0⟩, by simpa using h⟩

@[simp]
theorem pathAllPositive_singleton_iff {I : Type} (M : GaugeMatrix I) (i j : I)
    (ks : IntermediateIndexSeq I [M].length) :
    PathAllPositive [M] i j ks ↔ 0 < M i j := by
  constructor
  · intro h
    simpa using h ⟨0, Nat.zero_lt_succ 0⟩
  · intro h m
    have hm0 : m = ⟨0, Nat.zero_lt_succ 0⟩ := by
      ext
      exact Nat.lt_one_iff.mp m.isLt
    subst hm0
    simpa using h

/-!
## 2. 分量通道、解耦结构与单通道 Lip 常数定义 (`HC02-D07` – `HC02-D08`)
-/

/--
**义务 `HC02-D07`（分量通道）**：
分量对 $(i, j) \in I \times I$，表示从输入分量 $d_i$ 到输出分量 $d_j$ 的通道。
-/
abbrev ComponentChannel (I : Type) : Type := I × I

/--
**义务 `HC02-D07`（单行稀疏谓词 $\mathrm{Row}(\mathbf{L}, i, j)$）**：
固定输出行 $j$，除输入指标 $i$ 外其余条目全为 $0$：$\forall k \neq i,\; L_{k \to j} = 0$。
-/
def IsRowSparseAt {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/--
**义务 `HC02-D07`（行解耦）**：
矩阵级行解耦为 $\exists i \in I,\; \mathrm{Row}(\mathbf{L}, i, j)$；
算子在 $U$ 上关于输出分量 $d_j$ 行解耦为存在受限证书 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 满足该条件。
-/
def MatrixRowDecoupled {I : Type} (L : GaugeMatrix I) (j : I) : Prop :=
  ∃ i : I, IsRowSparseAt L i j

def IsRowDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ RestrictedLipMatrices d ϕ U, ∃ i : I, IsRowSparseAt L i j

/--
**义务 `HC02-D07`（单列稀疏谓词 $\mathrm{Col}(\mathbf{L}, i, j)$）**：
固定输入列 $i$，除输出指标 $j$ 外其余条目全为 $0$：$\forall k \neq j,\; L_{i \to k} = 0$。
-/
def IsColSparseAt {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/--
**义务 `HC02-D07`（列解耦）**：
矩阵级列解耦为 $\exists j \in I,\; \mathrm{Col}(\mathbf{L}, i, j)$；
算子在 $U$ 上关于输入分量 $d_i$ 列解耦为存在受限证书 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 满足该条件。
-/
def MatrixColDecoupled {I : Type} (L : GaugeMatrix I) (i : I) : Prop :=
  ∃ j : I, IsColSparseAt L i j

def IsColDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ RestrictedLipMatrices d ϕ U, ∃ j : I, IsColSparseAt L i j

/--
**义务 `HC02-D07`（对角矩阵与完全解耦体系）**：
所有非对角项为 $0$：$\forall i \neq j,\; L_{i \to j} = 0$。
-/
def IsDiagonalMatrix {I : Type} (L : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

def IsFullyDecoupledCert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  L ∈ RestrictedLipMatrices d ϕ U ∧ IsDiagonalMatrix L

/--
**义务 `HC02-D08`（单通道可行标量族 $\mathcal{S}_{i \to j}(\phi; U)$）**：
对 $U \subseteq \mathrm{dom}(\phi)$，定义
$\mathcal{S}_{i \to j}(\phi; U) = \{\lambda \in \bar{\mathbb{R}}_+ \mid \forall x, y \in U,\; d_j(\phi(x), \phi(y)) \le \lambda \cdot d_i(x, y)\}$。
-/
def SingleChannelFeasibleSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { lam : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y }

/--
**义务 `HC02-D08`（单通道 Lip 常数 $\underline{L}_{i \to j}(\phi; U)$）**：
定义为可行标量族的下确界 `sInf (SingleChannelFeasibleSet d ϕ U i j)`，
当可行集合为空时按 `ENNReal` 下确界约定满足 `sInf ∅ = ⊤`（$+\infty$）。
该常数仅由单通道不等式定义，不等同于任意多分量 Lip 矩阵的条目。
-/
noncomputable def singleChannelLipConst {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (SingleChannelFeasibleSet d ϕ U i j)

@[simp]
theorem singleChannelFeasibleSet_sInf_empty :
    sInf (∅ : Set ENNReal) = ⊤ :=
  sInf_empty

theorem singleChannelLipConst_eq_top_of_feasible_empty
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hempty : SingleChannelFeasibleSet d ϕ U i j = ∅) :
    singleChannelLipConst d ϕ U i j = ⊤ := by
  simp [singleChannelLipConst, hempty]

/-!
## 3. 矩阵界、复合律与扰动界定理 (`HC02-P01` – `HC02-P17`)
-/

/--
OET anchor: h-c4369c63c86cbacf
**义务 `HC02-P01`（单分量矩阵界退化）**：
当指标集满足 $I = \{i\}$ 时，合法 Lip 矩阵条件等价于单个标量不等式
$d_i(\phi(x), \phi(y)) \le L_{i \to i} d_i(x, y)$（$\forall x, y \in \mathrm{dom}(\phi)$）。
-/
theorem lipMatrix_singleton_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (L : GaugeMatrix I) (i : I)
    (hI : ∀ k : I, k = i) :
    L ∈ LipMatrices d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    have hsum : (∑ k : I, L k i * d k x y) = L i i * d i x y := by
      apply Finset.sum_eq_single i
      · intro k _ hki
        exact False.elim (hki (hI k))
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    rwa [hsum] at h
  · intro h x hx y hy j
    have hj : j = i := hI j
    subst hj
    have hsum : (∑ k : I, L k j * d k x y) = L j j * d j x y := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        exact False.elim (hkj (hI k))
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
    rw [hsum]
    exact h x hx y hy

/--
**义务 `HC02-P02`（全域 Lip 证书可限制）**：
当 $U \subseteq \mathrm{dom}(\phi)$ 时，$\mathscr{L}(\phi) \subseteq \mathscr{L}(\phi)\big|_U$。
-/
theorem lipMatrices_subset_restrictedLipMatrices
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) :
    LipMatrices d ϕ ⊆ RestrictedLipMatrices d ϕ U := by
  intro L hL
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  exact hL x (hU hx) y (hU hy) j

/--
**义务 `HC02-P03`（缩小评估域扩大 Lip 证书族）**：
当 $U \subseteq V \subseteq \mathrm{dom}(\phi)$ 时，$\mathscr{L}(\phi)\big|_V \subseteq \mathscr{L}(\phi)\big|_U$。
-/
theorem restrictedLipMatrices_antitone
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedLipMatrices d ϕ V ⊆ RestrictedLipMatrices d ϕ U := by
  intro L hL
  refine ⟨Set.Subset.trans hUV hV, ?_⟩
  intro x hx y hy j
  exact hL.2 x (hUV hx) y (hUV hy) j

/--
**义务 `HC02-P04`（受限 Lip 证书族逐条目下确界定义）**：
$a_{i \to j}(U) := \inf\{M_{i \to j} : \mathbf{M} \in \mathscr{L}(\phi)\big|_U\}$。
-/
noncomputable def entrywiseLipInf
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf { val : ENNReal | ∃ M ∈ RestrictedLipMatrices d ϕ U, M i j = val }

/--
**义务 `HC02-P04`（逐条目下确界不增）**：
当 $U \subseteq V$（且 $V \subseteq \mathrm{dom}(\phi)$）时，$a_{i \to j}(U) \le a_{i \to j}(V)$。
-/
theorem entrywiseLipInf_mono
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (i j : I) :
    entrywiseLipInf d ϕ U i j ≤ entrywiseLipInf d ϕ V i j := by
  apply sInf_le_sInf
  rintro val ⟨M, hMV, rfl⟩
  exact ⟨M, restrictedLipMatrices_antitone d ϕ hUV hMV.1 hMV, rfl⟩

/--
OET anchor: h-193cebcc1a7f9259
**义务 `HC02-P05`（命题：两步 Lip 矩阵复合律）**：
设 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，$U_2 = \phi_1(U_1)$。
若 $\mathbf{L}_1 \in \mathscr{L}(\phi_1)\big|_{U_1}$ 且 $\mathbf{L}_2 \in \mathscr{L}(\phi_2)\big|_{U_2}$，
则 $\mathbf{L}_2 \cdot \mathbf{L}_1 \in \mathscr{L}(\phi_2 \circ \phi_1)\big|_{U_1}$。
-/
theorem restrictedLipMatrices_comp
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (compOperator ϕ₂ ϕ₁))
    {L₁ L₂ : GaugeMatrix I}
    (hL₁ : L₁ ∈ RestrictedLipMatrices d ϕ₁ U₁)
    (hL₂ : L₂ ∈ RestrictedLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul L₂ L₁ ∈ RestrictedLipMatrices d (compOperator ϕ₂ ϕ₁) U₁ := by
  refine ⟨hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  have h_step2 := hL₂.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
  have h_step1 : ∀ k : I,
      L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) ≤ L₂ k j * ∑ i : I, L₁ i k * d i x y := by
    intro k
    exact mul_le_mul_right (hL₁.2 x hx y hy k) (L₂ k j)
  calc
    d j ((compOperator ϕ₂ ϕ₁).func x) ((compOperator ϕ₂ ϕ₁).func y)
        ≤ ∑ k : I, L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := h_step2
    _ ≤ ∑ k : I, L₂ k j * ∑ i : I, L₁ i k * d i x y := Finset.sum_le_sum (fun k _ => h_step1 k)
    _ = ∑ k : I, ∑ i : I, L₂ k j * (L₁ i k * d i x y) := by
        congr 1 with k
        exact Finset.mul_sum Finset.univ (fun i => L₁ i k * d i x y) (L₂ k j)
    _ = ∑ i : I, ∑ k : I, (L₂ k j * L₁ i k) * d i x y := by
        rw [Finset.sum_comm]
        congr 1 with i
        congr 1 with k
        rw [mul_assoc]
    _ = ∑ i : I, gaugeMatrixMul L₂ L₁ i j * d i x y := by
        congr 1 with i
        rw [gaugeMatrixMul_apply, Finset.sum_mul]

/--
OET anchor: h-88784dcbfff0ea66
**义务 `HC02-P06`（注：co-Lip 通道退化的点对判据）**：
若存在 $x, y \in \mathrm{dom}(\phi)$ 使 $d_j(\phi(x), \phi(y)) = 0$ 且 $d_i(x, y) > 0$，
则任一全域 co-Lip 矩阵 $\mathbf{K} \in \mathscr{K}(\phi)\big|_{\mathrm{dom}(\phi)}$ 必满足 $K_{i \to j} = 0$。
-/
theorem coLip_entry_eq_zero_of_output_zero
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (i j : I)
    {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    (hdj : d j (ϕ.func x) (ϕ.func y) = 0)
    (hdi : 0 < d i x y)
    {K : GaugeMatrix I} (hK : K ∈ RestrictedCoLipMatrices d ϕ (dom ϕ)) :
    K i j = 0 := by
  have h_le : K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
    calc
      K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
        Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
  rw [hdj, nonpos_iff_eq_zero, mul_eq_zero] at h_le
  rcases h_le with hKij | hdixy
  · exact hKij
  · exact False.elim (ne_of_gt hdi hdixy)

/--
OET anchor: h-0f256e6f1d38a612
**义务 `HC02-P07`（命题：两步 co-Lip 矩阵复合律）**：
设 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，$U_2 = \phi_1(U_1)$。
若 $\mathbf{K}_1 \in \mathscr{K}(\phi_1)\big|_{U_1}$ 且 $\mathbf{K}_2 \in \mathscr{K}(\phi_2)\big|_{U_2}$，
则 $\mathbf{K}_2 \cdot \mathbf{K}_1 \in \mathscr{K}(\phi_2 \circ \phi_1)\big|_{U_1}$（且 $U_1$ 非空）。
-/
theorem restrictedCoLipMatrices_comp
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (compOperator ϕ₂ ϕ₁))
    {K₁ K₂ : GaugeMatrix I}
    (hK₁ : K₁ ∈ RestrictedCoLipMatrices d ϕ₁ U₁)
    (hK₂ : K₂ ∈ RestrictedCoLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul K₂ K₁ ∈ RestrictedCoLipMatrices d (compOperator ϕ₂ ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  have h_step2 := hK₂.2.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
  have h_step1 : ∀ k : I,
      K₂ k j * (∑ i : I, K₁ i k * d i x y) ≤ K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
    intro k
    exact mul_le_mul_right (hK₁.2.2 x hx y hy k) (K₂ k j)
  calc
    (∑ i : I, gaugeMatrixMul K₂ K₁ i j * d i x y)
        = ∑ i : I, ∑ k : I, (K₂ k j * K₁ i k) * d i x y := by
          congr 1 with i
          rw [gaugeMatrixMul_apply, Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, K₂ k j * (K₁ i k * d i x y) := by
          rw [Finset.sum_comm]
          congr 1 with k
          congr 1 with i
          rw [mul_assoc]
    _ = ∑ k : I, K₂ k j * ∑ i : I, K₁ i k * d i x y := by
          congr 1 with k
          exact (Finset.mul_sum Finset.univ (fun i => K₁ i k * d i x y) (K₂ k j)).symm
    _ ≤ ∑ k : I, K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := Finset.sum_le_sum (fun k _ => h_step1 k)
    _ ≤ d j ((compOperator ϕ₂ ϕ₁).func x) ((compOperator ϕ₂ ϕ₁).func y) := h_step2

/-- 公共定义域 $\mathrm{dom}(\phi_1, \phi_2) := \mathrm{dom}(\phi_1) \cap \mathrm{dom}(\phi_2)$。 -/
def commonDom {X : Type} {bot : X} (ϕ₁ ϕ₂ : Operator X bot) : Set X :=
  dom ϕ₁ ∩ dom ϕ₂

/--
OET anchor: h-b959b42f25710105
**义务 `HC02-P08`（命题 (i) 第一式：正向点对像距扰动界）**：
设 $U \subseteq \mathrm{dom}(\phi_1, \phi_2)$，若 $\forall z \in U,\; \forall j \in I,\; d_j(\phi_1(z), \phi_2(z)) \le \delta_j$，
则对任意 $x, y \in U$ 与 $j \in I$：
$d_j(\phi_2(x), \phi_2(y)) \le d_j(\phi_1(x), \phi_1(y)) + 2\delta_j = d_j(\phi_1(x), \phi_1(y)) + \delta_j + \delta_j$。
-/
theorem image_dist_perturbation_forward
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j ∧
      d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
  intro x hx y hy j
  have _ : x ∈ commonDom ϕ₁ ϕ₂ := hU hx
  have h1 : d j (ϕ₂.func x) (ϕ₁.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  have h2 : d j (ϕ₁.func y) (ϕ₂.func y) ≤ δ j := hδ y hy j
  have h_tri1 := (hd j).triangle (ϕ₂.func x) (ϕ₁.func x) (ϕ₂.func y)
  have h_tri2 := (hd j).triangle (ϕ₁.func x) (ϕ₁.func y) (ϕ₂.func y)
  have h_add : d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
    calc
      d j (ϕ₂.func x) (ϕ₂.func y)
          ≤ d j (ϕ₂.func x) (ϕ₁.func x) + d j (ϕ₁.func x) (ϕ₂.func y) := h_tri1
      _ ≤ d j (ϕ₂.func x) (ϕ₁.func x) + (d j (ϕ₁.func x) (ϕ₁.func y) + d j (ϕ₁.func y) (ϕ₂.func y)) :=
        add_le_add le_rfl h_tri2
      _ ≤ δ j + (d j (ϕ₁.func x) (ϕ₁.func y) + δ j) :=
        add_le_add h1 (add_le_add le_rfl h2)
      _ = d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
        rw [add_left_comm, add_assoc]
  refine ⟨?_, h_add⟩
  calc
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := h_add
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by rw [two_mul, add_assoc]

/--
OET anchor: h-b959b42f25710105
**义务 `HC02-P09`（命题 (i) 第二式：反向点对像距扰动界）**：
在相同扰动前提下，对任意 $x, y \in U$ 与 $j \in I$：
$d_j(\phi_1(x), \phi_1(y)) \le d_j(\phi_2(x), \phi_2(y)) + 2\delta_j = d_j(\phi_2(x), \phi_2(y)) + \delta_j + \delta_j$。
-/
theorem image_dist_perturbation_reverse
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j ∧
      d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := by
  have hU_symm : U ⊆ commonDom ϕ₂ ϕ₁ := fun z hz => ⟨(hU hz).2, (hU hz).1⟩
  have hδ_symm : ∀ z ∈ U, ∀ j : I, d j (ϕ₂.func z) (ϕ₁.func z) ≤ δ j := by
    intro z hz j
    rw [(hd j).symm]
    exact hδ z hz j
  exact image_dist_perturbation_forward d ϕ₂ ϕ₁ hU_symm δ hδ_symm

/--
OET anchor: h-b959b42f25710105
**义务 `HC02-P10`（命题 (ii)：扰动 Lip 上界桥接）**：
若另有 $\mathbf{L}_1 \in \mathscr{L}(\phi_1)\big|_U$，则
$d_j(\phi_2(x), \phi_2(y)) \le \sum_{i \in I} [\mathbf{L}_1]_{i \to j} d_i(x, y) + 2\delta_j$。
-/
theorem perturbed_lip_upper_bound
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₁ : GaugeMatrix I} (hL₁ : L₁ ∈ RestrictedLipMatrices d ϕ₁ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ₂.func x) (ϕ₂.func y) ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by
  intro x hx y hy j
  have h_fwd := (image_dist_perturbation_forward d ϕ₁ ϕ₂ hU δ hδ x hx y hy j).1
  exact le_trans h_fwd (add_le_add (hL₁.2 x hx y hy j) le_rfl)

/--
OET anchor: h-b959b42f25710105
**义务 `HC02-P11`（命题 (iii)：扰动 co-Lip 下界桥接）**：
若另有 $\mathbf{K}_1 \in \mathscr{K}(\phi_1)\big|_U$，则
$\sum_{i \in I} [\mathbf{K}_1]_{i \to j} d_i(x, y) \le d_j(\phi_2(x), \phi_2(y)) + 2\delta_j$。
-/
theorem perturbed_coLip_lower_bound
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₁ : GaugeMatrix I} (hK₁ : K₁ ∈ RestrictedCoLipMatrices d ϕ₁ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K₁ i j * d i x y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by
  intro x hx y hy j
  have h_rev := (image_dist_perturbation_reverse d ϕ₁ ϕ₂ hU δ hδ x hx y hy j).1
  exact le_trans (hK₁.2.2 x hx y hy j) h_rev

/--
OET anchor: h-c80171fa685dc795
**义务 `HC02-P12`（推论 (i)：任意正长度复合链的局部 Lip 矩阵放缩上限）**：
设 $k \ge 1$（`ϕs ≠ []`），$U_1 \subseteq \mathrm{dom}(c_k)$，$U_{m+1} = \phi_m(U_m)$。
若各单步满足 $\mathbf{L}^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$，则
$\mathbf{L}^{(k)} \cdot \cdots \cdot \mathbf{L}^{(1)} \in \mathscr{L}(c_k)\big|_{U_1}$。
-/
theorem chain_restrictedLipMatrices_prod
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕs : List (Operator X bot)) (h_ne : ϕs ≠ [])
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (composeOperatorChain ϕs))
    (Ls : List (GaugeMatrix I)) (hlen : Ls.length = ϕs.length)
    (h_steps : ∀ (m : ℕ) (hm : m < ϕs.length),
      Ls[m]'(by omega) ∈ RestrictedLipMatrices d (ϕs[m]) (chainImageAt ϕs U₁ m)) :
    gaugeMatrixChainProd Ls ∈ RestrictedLipMatrices d (composeOperatorChain ϕs) U₁ := by
  induction ϕs generalizing U₁ Ls with
  | nil =>
      exact False.elim (h_ne rfl)
  | cons ϕ rest ih =>
      cases Ls with
      | nil =>
          simp at hlen
      | cons L restL =>
          cases rest with
          | nil =>
              have hrestL : restL = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
              subst hrestL
              simpa [gaugeMatrixChainProd, composeOperatorChain, chainImageAt] using
                h_steps 0 (by simp)
          | cons ϕ₂ tail =>
              have h_ne_rest : ϕ₂ :: tail ≠ [] := List.cons_ne_nil ϕ₂ tail
              rw [composeOperatorChain_cons] at hU₁ ⊢
              rw [gaugeMatrixChainProd_cons]
              rcases dom_of_subset_dom_compOperator hU₁ with ⟨_, hU₂_dom⟩
              have hL₁ : L ∈ RestrictedLipMatrices d ϕ U₁ := by
                simpa [chainImageAt] using h_steps 0 (by simp)
              have hlen_rest : restL.length = (ϕ₂ :: tail).length := by
                simpa using hlen
              have h_steps_rest : ∀ (m : ℕ) (hm : m < (ϕ₂ :: tail).length),
                  restL[m]'(by omega) ∈
                    RestrictedLipMatrices d ((ϕ₂ :: tail)[m])
                      (chainImageAt (ϕ₂ :: tail) (operator_image ϕ U₁) m) := by
                intro m hm
                have hm_succ : m + 1 < (ϕ :: ϕ₂ :: tail).length := Nat.succ_lt_succ hm
                simpa [chainImageAt_cons_succ] using h_steps (m + 1) hm_succ
              have hL_rest := ih h_ne_rest hU₂_dom restL hlen_rest h_steps_rest
              exact restrictedLipMatrices_comp d ϕ (composeOperatorChain (ϕ₂ :: tail)) hU₁ hL₁ hL_rest

/-- 基于 `LipChainData` 封装结构的有限复合链 Lip 矩阵证书定理（`HC02-P12`）。 -/
theorem LipChainData.prod_mem_restrictedLipMatrices
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (chain : LipChainData bot d) (h_ne : chain.ϕs ≠ []) :
    gaugeMatrixChainProd chain.Ls ∈
      RestrictedLipMatrices d (composeOperatorChain chain.ϕs) chain.U₁ :=
  chain_restrictedLipMatrices_prod d chain.ϕs h_ne chain.hU₁ chain.Ls chain.hlen chain.step_valid

/--
OET anchor: h-c80171fa685dc795
**义务 `HC02-P13`（推论 (ii)：任意正长度复合链的局部 co-Lip 矩阵保距下限）**：
设 $k \ge 1$（`ϕs ≠ []`），$U_1 \subseteq \mathrm{dom}(c_k)$，$U_{m+1} = \phi_m(U_m)$。
若各单步满足 $\mathbf{K}^{(m)} \in \mathscr{K}(\phi_m)\big|_{U_m}$（均含非空性义务），则
$\mathbf{K}^{(k)} \cdot \cdots \cdot \mathbf{K}^{(1)} \in \mathscr{K}(c_k)\big|_{U_1}$。
-/
theorem chain_restrictedCoLipMatrices_prod
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕs : List (Operator X bot)) (h_ne : ϕs ≠ [])
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (composeOperatorChain ϕs))
    (Ks : List (GaugeMatrix I)) (hlen : Ks.length = ϕs.length)
    (h_steps : ∀ (m : ℕ) (hm : m < ϕs.length),
      Ks[m]'(by omega) ∈ RestrictedCoLipMatrices d (ϕs[m]) (chainImageAt ϕs U₁ m)) :
    gaugeMatrixChainProd Ks ∈ RestrictedCoLipMatrices d (composeOperatorChain ϕs) U₁ := by
  induction ϕs generalizing U₁ Ks with
  | nil =>
      exact False.elim (h_ne rfl)
  | cons ϕ rest ih =>
      cases Ks with
      | nil =>
          simp at hlen
      | cons K restK =>
          cases rest with
          | nil =>
              have hrestK : restK = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
              subst hrestK
              simpa [gaugeMatrixChainProd, composeOperatorChain, chainImageAt] using
                h_steps 0 (by simp)
          | cons ϕ₂ tail =>
              have h_ne_rest : ϕ₂ :: tail ≠ [] := List.cons_ne_nil ϕ₂ tail
              rw [composeOperatorChain_cons] at hU₁ ⊢
              rw [gaugeMatrixChainProd_cons]
              rcases dom_of_subset_dom_compOperator hU₁ with ⟨_, hU₂_dom⟩
              have hK₁ : K ∈ RestrictedCoLipMatrices d ϕ U₁ := by
                simpa [chainImageAt] using h_steps 0 (by simp)
              have hlen_rest : restK.length = (ϕ₂ :: tail).length := by
                simpa using hlen
              have h_steps_rest : ∀ (m : ℕ) (hm : m < (ϕ₂ :: tail).length),
                  restK[m]'(by omega) ∈
                    RestrictedCoLipMatrices d ((ϕ₂ :: tail)[m])
                      (chainImageAt (ϕ₂ :: tail) (operator_image ϕ U₁) m) := by
                intro m hm
                have hm_succ : m + 1 < (ϕ :: ϕ₂ :: tail).length := Nat.succ_lt_succ hm
                simpa [chainImageAt_cons_succ] using h_steps (m + 1) hm_succ
              have hK_rest := ih h_ne_rest hU₂_dom restK hlen_rest h_steps_rest
              exact restrictedCoLipMatrices_comp d ϕ (composeOperatorChain (ϕ₂ :: tail)) hU₁ hK₁ hK_rest

/-- 基于 `CoLipChainData` 封装结构的有限复合链 co-Lip 矩阵证书定理（`HC02-P13`）。 -/
theorem CoLipChainData.prod_mem_restrictedCoLipMatrices
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (chain : CoLipChainData bot d) (h_ne : chain.ϕs ≠ []) :
    gaugeMatrixChainProd chain.Ks ∈
      RestrictedCoLipMatrices d (composeOperatorChain chain.ϕs) chain.U₁ :=
  chain_restrictedCoLipMatrices_prod d chain.ϕs h_ne chain.hU₁ chain.Ks chain.hlen chain.step_valid

/-- 单位矩阵对距离加权求和的恒等式：$\sum_{i \in I} \mathbf{I}_{i \to j} d_i(x, y) = d_j(x, y)$。 -/
theorem sum_gaugeMatrixId_mul_dist
    {X I : Type} [Fintype I] (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, gaugeMatrixId I i j * d i x y) = d j x y := by
  simp [gaugeMatrixId]

/--
OET anchor: h-11006ddd8c43bfec
**义务 `HC02-P14`（注：零步复合的单位 Lip 矩阵证书）**：
当 $k = 0$ 时，$c_0 = \mathrm{id}_{\mathcal{X}}$，空复合乘积为单位矩阵 $\mathbf{I}$。
对任意非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$，单位矩阵属于 $\mathscr{L}(\mathrm{id}_{\mathcal{X}})\big|_U$。
-/
theorem zero_step_id_mem_restrictedLipMatrices
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (_hU_ne : U.Nonempty) (hU_dom : U ⊆ dom (idOperator X bot)) :
    gaugeMatrixId I ∈ RestrictedLipMatrices d (idOperator X bot) U ∧
    gaugeMatrixChainProd ([] : List (GaugeMatrix I)) ∈
      RestrictedLipMatrices d (composeOperatorChain ([] : List (Operator X bot))) U := by
  have h_mem : gaugeMatrixId I ∈ RestrictedLipMatrices d (idOperator X bot) U := by
    refine ⟨hU_dom, ?_⟩
    intro x _ y _ j
    rw [sum_gaugeMatrixId_mul_dist]
    rfl
  exact ⟨h_mem, h_mem⟩

/--
OET anchor: h-11006ddd8c43bfec
**义务 `HC02-P15`（注：零步复合的单位 co-Lip 矩阵证书）**：
对同一非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$，单位矩阵属于 $\mathscr{K}(\mathrm{id}_{\mathcal{X}})\big|_U$。
-/
theorem zero_step_id_mem_restrictedCoLipMatrices
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom (idOperator X bot)) :
    gaugeMatrixId I ∈ RestrictedCoLipMatrices d (idOperator X bot) U ∧
    gaugeMatrixChainProd ([] : List (GaugeMatrix I)) ∈
      RestrictedCoLipMatrices d (composeOperatorChain ([] : List (Operator X bot))) U := by
  have h_mem : gaugeMatrixId I ∈ RestrictedCoLipMatrices d (idOperator X bot) U := by
    refine ⟨hU_ne, hU_dom, ?_⟩
    intro x _ y _ j
    rw [sum_gaugeMatrixId_mul_dist]
    rfl
  exact ⟨h_mem, h_mem⟩

/--
将长度为 $n+2$ 的链的中间指标序列 `(k₁, k₂, …, k_{n+1})`
拆分为第一步目标指标 `k₁ : I` 与剩余链的中间指标序列 `(k₂, …, k_{n+1})` 的双射。
-/
def splitIntermediateSeqEquiv (I : Type) (n : ℕ) :
    (Fin (n + 1) → I) ≃ I × (Fin n → I) where
  toFun ks := (ks ⟨0, Nat.succ_pos n⟩, fun r => ks ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩)
  invFun p := Fin.cases p.1 p.2
  left_inv ks := by
    funext r
    refine Fin.cases ?_ ?_ r
    · rfl
    · intro r'
      rfl
  right_inv p := by
    ext
    · rfl
    · rfl

/-- 当把中间序列写为 `Fin.cases k₁ ks'` 时，第 `r.succ` 步的起点指标化简引理。 -/
theorem pathSourceIndex_cons_cons {I : Type} (M₁ M₂ : GaugeMatrix I) (tail : List (GaugeMatrix I))
    (i k₁ : I) (ks' : IntermediateIndexSeq I (M₂ :: tail).length) (r : Fin (M₂ :: tail).length) :
    pathSourceIndex (M₁ :: M₂ :: tail).length i (Fin.cases k₁ ks') r.succ =
      pathSourceIndex (M₂ :: tail).length k₁ ks' r := by
  refine Fin.cases ?_ ?_ r
  · rfl
  · intro r'
      rfl

/-- 当把中间序列写为 `Fin.cases k₁ ks'` 时，第 `r.succ` 步的终点指标化简引理。 -/
theorem pathTargetIndex_cons_cons {I : Type} (M₁ M₂ : GaugeMatrix I) (tail : List (GaugeMatrix I))
    (j k₁ : I) (ks' : IntermediateIndexSeq I (M₂ :: tail).length) (r : Fin (M₂ :: tail).length) :
    pathTargetIndex (M₁ :: M₂ :: tail).length j (Fin.cases k₁ ks') r.succ =
      pathTargetIndex (M₂ :: tail).length j ks' r := by
  unfold pathTargetIndex
  by_cases hlt : r.val + 1 < (M₂ :: tail).length
  · have hlt_succ : (r.succ : Fin (M₁ :: M₂ :: tail).length).val + 1 < (M₁ :: M₂ :: tail).length :=
      Nat.succ_lt_succ hlt
    rw [dif_pos hlt_succ, dif_pos hlt]
    rfl
  · have hlt_succ : ¬ ((r.succ : Fin (M₁ :: M₂ :: tail).length).val + 1 < (M₁ :: M₂ :: tail).length) := by
      intro h
      exact hlt (Nat.lt_of_succ_lt_succ h)
    rw [dif_neg hlt_succ, dif_neg hlt]

/-- 当把中间序列写为 `Fin.cases k₁ ks'` 时，路径权重的首步拆分引理。 -/
theorem pathWeight_cons_cons {I : Type} (M₁ M₂ : GaugeMatrix I) (tail : List (GaugeMatrix I))
    (i j k₁ : I) (ks' : IntermediateIndexSeq I (M₂ :: tail).length) :
    pathWeight (M₁ :: M₂ :: tail) i j (Fin.cases k₁ ks') =
      pathWeight (M₂ :: tail) k₁ j ks' * M₁ i k₁ := by
  unfold pathWeight
  change (∏ m : Fin ((M₂ :: tail).length + 1),
      pathStepEntry (M₁ :: M₂ :: tail) i j (Fin.cases k₁ ks') m) =
    (∏ m : Fin (M₂ :: tail).length, pathStepEntry (M₂ :: tail) k₁ j ks' m) * M₁ i k₁
  rw [Fin.prod_univ_succ, mul_comm]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro r _
  unfold pathStepEntry
  rw [pathSourceIndex_cons_cons, pathTargetIndex_cons_cons]
  rfl

/--
**有限矩阵乘积的路径展开式（命题 #h-e4154c34e95d3c23 的代数核心）**：
对任意非空矩阵列表 `Ms`（长度 $n \ge 1$），乘积矩阵在 $(i, j)$ 处的条目等于所有中间指标路径权重之和。
-/
theorem gaugeMatrixChainProd_eq_sum_pathWeight
    {I : Type} [Fintype I] (Ms : List (GaugeMatrix I)) (h_ne : Ms ≠ []) (i j : I) :
    gaugeMatrixChainProd Ms i j =
      ∑ ks : IntermediateIndexSeq I Ms.length, pathWeight Ms i j ks := by
  induction Ms generalizing i j with
  | nil =>
      exact False.elim (h_ne rfl)
  | cons M₁ rest ih =>
      cases rest with
      | nil =>
          simp [gaugeMatrixChainProd]
      | cons M₂ tail =>
          have h_ne_rest : M₂ :: tail ≠ [] := List.cons_ne_nil M₂ tail
          rw [gaugeMatrixChainProd_cons, gaugeMatrixMul_apply]
          simp only [ih h_ne_rest _ j, Finset.sum_mul]
          rw [← Fintype.sum_prod_type']
          refine Fintype.sum_equiv (splitIntermediateSeqEquiv I tail.length).symm _ _ ?_
          rintro ⟨k₁, ks'⟩
          simp [splitIntermediateSeqEquiv, pathWeight_cons_cons]

/-- 单条路径权重为 `0` 当且仅当该路径含至少一条零边。 -/
theorem pathWeight_eq_zero_iff_pathHasZeroEdge
    {I : Type} (Ms : List (GaugeMatrix I)) (i j : I)
    (ks : IntermediateIndexSeq I Ms.length) :
    pathWeight Ms i j ks = 0 ↔ PathHasZeroEdge Ms i j ks := by
  simp [pathWeight, PathHasZeroEdge, Finset.prod_eq_zero_iff]

/-- 单条路径权重严格正（`> 0`）当且仅当该路径所有边均严格正。 -/
theorem pathWeight_pos_iff_pathAllPositive
    {I : Type} (Ms : List (GaugeMatrix I)) (i j : I)
    (ks : IntermediateIndexSeq I Ms.length) :
    0 < pathWeight Ms i j ks ↔ PathAllPositive Ms i j ks := by
  simp only [pos_iff_ne_zero, ne_eq, pathWeight_eq_zero_iff_pathHasZeroEdge,
    PathHasZeroEdge, PathAllPositive, not_exists]

/--
OET anchor: h-e4154c34e95d3c23
**义务 `HC02-P16`（命题 (i)：Lip 乘积条目的零值判据）**：
在非空算子链 $c_n = \phi_n \circ \cdots \circ \phi_1$（$n \ge 1$）、$U_1 \subseteq \mathrm{dom}(c_n)$、
$U_{m+1} = \phi_m(U_m)$ 与局部证书 $\mathbf{L}^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$ 条件下，
$[\mathbf{L}^{(n)} \cdots \mathbf{L}^{(1)}]_{i \to j} = 0$ 当且仅当对任意中间指标序列 `ks` 均存在零边（`PathHasZeroEdge`）；
当 $n = 1$ 时退化为 $[\mathbf{L}^{(1)}]_{i \to j} = 0$。
-/
theorem lipChainProd_entry_eq_zero_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕs : List (Operator X bot)) (h_ne : ϕs ≠ [])
    {U₁ : Set X} (_hU₁ : U₁ ⊆ dom (composeOperatorChain ϕs))
    (Ls : List (GaugeMatrix I)) (hlen : Ls.length = ϕs.length)
    (_h_steps : ∀ (m : ℕ) (hm : m < ϕs.length),
      Ls[m]'(by omega) ∈ RestrictedLipMatrices d (ϕs[m]) (chainImageAt ϕs U₁ m))
    (i j : I) :
    gaugeMatrixChainProd Ls i j = 0 ↔
      ∀ ks : IntermediateIndexSeq I Ls.length, PathHasZeroEdge Ls i j ks := by
  have hLs_ne : Ls ≠ [] := by
    intro h_nil
    apply h_ne
    exact List.length_eq_zero_iff.mp (by simpa [h_nil] using hlen.symm)
  rw [gaugeMatrixChainProd_eq_sum_pathWeight Ls hLs_ne i j, Finset.sum_eq_zero_iff]
  constructor
  · intro h ks
    exact (pathWeight_eq_zero_iff_pathHasZeroEdge Ls i j ks).mp (h ks (Finset.mem_univ ks))
  · intro h ks _
    exact (pathWeight_eq_zero_iff_pathHasZeroEdge Ls i j ks).mpr (h ks)

/-- **义务 `HC02-P16`（$n=1$ 退化情形）**：唯一空中间序列下退化为单个矩阵条目 $[\mathbf{L}^{(1)}]_{i \to j} = 0$。 -/
theorem lipChainProd_entry_eq_zero_iff_singleton
    {I : Type} [Fintype I] (L₁ : GaugeMatrix I) (i j : I) :
    (gaugeMatrixChainProd [L₁] i j = 0 ↔ L₁ i j = 0) ∧
    ((∀ ks : IntermediateIndexSeq I [L₁].length, PathHasZeroEdge [L₁] i j ks) ↔ L₁ i j = 0) := by
  refine ⟨Iff.rfl, ?_⟩
  constructor
  · intro h
    exact (pathHasZeroEdge_singleton_iff L₁ i j (emptyIntermediateSeq I)).mp (h (emptyIntermediateSeq I))
  · intro h ks
    exact (pathHasZeroEdge_singleton_iff L₁ i j ks).mpr h

/--
OET anchor: h-e4154c34e95d3c23
**义务 `HC02-P17`（命题 (ii)：co-Lip 乘积条目的正值判据）**：
在非空算子链 $c_n = \phi_n \circ \cdots \circ \phi_1$（$n \ge 1$）、$U_1 \subseteq \mathrm{dom}(c_n)$、
$U_{m+1} = \phi_m(U_m)$ 与局部证书 $\mathbf{K}^{(m)} \in \mathscr{K}(\phi_m)\big|_{U_m}$ 条件下，
$[\mathbf{K}^{(n)} \cdots \mathbf{K}^{(1)}]_{i \to j} > 0$ 当且仅当存在至少一条全正路径（`PathAllPositive`）；
当 $n = 1$ 时对应唯一空中间序列且退化为 $[\mathbf{K}^{(1)}]_{i \to j} > 0$。
-/
theorem coLipChainProd_entry_pos_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕs : List (Operator X bot)) (h_ne : ϕs ≠ [])
    {U₁ : Set X} (_hU₁ : U₁ ⊆ dom (composeOperatorChain ϕs))
    (Ks : List (GaugeMatrix I)) (hlen : Ks.length = ϕs.length)
    (_h_steps : ∀ (m : ℕ) (hm : m < ϕs.length),
      Ks[m]'(by omega) ∈ RestrictedCoLipMatrices d (ϕs[m]) (chainImageAt ϕs U₁ m))
    (i j : I) :
    0 < gaugeMatrixChainProd Ks i j ↔
      ∃ ks : IntermediateIndexSeq I Ks.length, PathAllPositive Ks i j ks := by
  have hKs_ne : Ks ≠ [] := by
    intro h_nil
    apply h_ne
    exact List.length_eq_zero_iff.mp (by simpa [h_nil] using hlen.symm)
  rw [gaugeMatrixChainProd_eq_sum_pathWeight Ks hKs_ne i j, pos_iff_ne_zero, ne_eq,
    Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, forall_true_left, not_forall, ← pos_iff_ne_zero,
    pathWeight_pos_iff_pathAllPositive]

/-- **义务 `HC02-P17`（$n=1$ 退化情形）**：唯一空中间序列下退化为单个矩阵条目 $[\mathbf{K}^{(1)}]_{i \to j} > 0$。 -/
theorem coLipChainProd_entry_pos_iff_singleton
    {I : Type} [Fintype I] (K₁ : GaugeMatrix I) (i j : I) :
    (0 < gaugeMatrixChainProd [K₁] i j ↔ 0 < K₁ i j) ∧
    ((∃ ks : IntermediateIndexSeq I [K₁].length, PathAllPositive [K₁] i j ks) ↔ 0 < K₁ i j) := by
  refine ⟨Iff.rfl, ?_⟩
  constructor
  · rintro ⟨ks, h⟩
    exact (pathAllPositive_singleton_iff K₁ i j ks).mp h
  · intro h
    exact ⟨emptyIntermediateSeq I, (pathAllPositive_singleton_iff K₁ i j (emptyIntermediateSeq I)).mpr h⟩

/-!
## 4. 单通道 Lip 常数的分析性质与反例 (`HC02-P18` – `HC02-P24`)
-/

/--
**义务 `HC02-P18`（零输入距而正输出距使可行族为空，单通道常数为 $+\infty$）**：
若存在 $x, y \in U$ 使 $d_i(x, y) = 0$ 且 $d_j(\phi(x), \phi(y)) > 0$，
则不存在任何 $\lambda \in \bar{\mathbb{R}}_+$ 满足单通道标量界，可行集合为空且 $\underline{L}_{i \to j}(\phi; U) = +\infty$。
-/
theorem singleChannelLipConst_eq_top_of_zero_input_pos_output
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (_hU : U ⊆ dom ϕ) (i j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hdi : d i x y = 0) (hdj : 0 < d j (ϕ.func x) (ϕ.func y)) :
    (∀ lam : ENNReal, lam ∉ SingleChannelFeasibleSet d ϕ U i j) ∧
    SingleChannelFeasibleSet d ϕ U i j = ∅ ∧
    singleChannelLipConst d ϕ U i j = ⊤ := by
  have h_no_lam : ∀ lam : ENNReal, lam ∉ SingleChannelFeasibleSet d ϕ U i j := by
    intro lam hlam
    have hle := hlam x hx y hy
    rw [hdi, mul_zero, nonpos_iff_eq_zero] at hle
    exact ne_of_gt hdj hle
  have h_empty : SingleChannelFeasibleSet d ϕ U i j = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr h_no_lam
  exact ⟨h_no_lam, h_empty, singleChannelLipConst_eq_top_of_feasible_empty d ϕ U i j h_empty⟩

/--
**义务 `HC02-P20`（单通道标量可行族向上封闭）**：
若 $\lambda_0 \in \mathcal{S}_{i \to j}(\phi; U)$ 且 $\lambda_1 \ge \lambda_0$，则 $\lambda_1 \in \mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem singleChannelFeasibleSet_upper_closed
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) (i j : I)
    {lam₀ lam₁ : ENNReal}
    (h₀ : lam₀ ∈ SingleChannelFeasibleSet d ϕ U i j)
    (hle : lam₀ ≤ lam₁) :
    lam₁ ∈ SingleChannelFeasibleSet d ϕ U i j := by
  intro x hx y hy
  exact le_trans (h₀ x hx y hy) (mul_le_mul_left hle (d i x y))

/--
**义务 `HC02-P21`（正有限下确界以上的每个常数均可行）**：
在 $0 < \underline{L}_{i \to j}(\phi; U) < +\infty$ 语境下，任意 $\lambda > \underline{L}_{i \to j}(\phi; U)$（允许 $\lambda = +\infty$）
均属于可行集合 $\mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem singleChannelFeasible_of_gt_inf
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (_hU : U ⊆ dom ϕ) (i j : I)
    (_ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (_ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤)
    {lam : ENNReal} (hlam : singleChannelLipConst d ϕ U i j < lam) :
    lam ∈ SingleChannelFeasibleSet d ϕ U i j := by
  rcases sInf_lt_iff.mp hlam with ⟨lam₀, hlam₀_mem, hlam₀_lt⟩
  exact singleChannelFeasibleSet_upper_closed d ϕ U i j hlam₀_mem (le_of_lt hlam₀_lt)

/--
**义务 `HC02-P19`（正有限最优单通道下确界可被取到）**：
若 $a = \underline{L}_{i \to j}(\phi; U)$ 满足 $0 < a < +\infty$，则 $a \in \mathcal{S}_{i \to j}(\phi; U)$，
即对任意 $x, y \in U$ 均有 $d_j(\phi(x), \phi(y)) \le \underline{L}_{i \to j}(\phi; U) \cdot d_i(x, y)$。
-/
theorem singleChannelLipConst_mem_of_pos_of_lt_top
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) (i j : I)
    (ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤) :
    singleChannelLipConst d ϕ U i j ∈ SingleChannelFeasibleSet d ϕ U i j := by
  set a := singleChannelLipConst d ϕ U i j
  intro x hx y hy
  set A := d j (ϕ.func x) (ϕ.func y)
  set B := d i x y
  by_cases hB0 : B = 0
  · have ha_lt_succ : a < a + 1 := ENNReal.lt_add_right ha_lt_top.ne one_ne_zero
    have h_mem := singleChannelFeasible_of_gt_inf d ϕ hU i j ha_pos ha_lt_top ha_lt_succ
    have hle := h_mem x hx y hy
    change A ≤ (a + 1) * B at hle
    rw [hB0, mul_zero] at hle
    exact le_trans hle (zero_le (a * B))
  · by_cases hBtop : B = ⊤
    · rw [hBtop, ENNReal.mul_top ha_pos.ne']
      exact le_top
    · by_contra! h_lt
      have ha_lt_div : a < A / B := ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop) |>.mpr h_lt
      rcases exists_between ha_lt_div with ⟨lam, h_a_lt_lam, h_lam_lt_div⟩
      have h_lam_mul_lt : lam * B < A :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp h_lam_lt_div
      have h_lam_mem := singleChannelFeasible_of_gt_inf d ϕ hU i j ha_pos ha_lt_top h_a_lt_lam
      have h_A_le : A ≤ lam * B := h_lam_mem x hx y hy
      exact not_lt_of_ge h_A_le h_lam_mul_lt

/--
OET anchor: h-57de7918859a9de2
**义务 `HC02-P22`（零下确界给出所有有限正常数均为可行标量证书）**：
当 $\underline{L}_{i \to j}(\phi; U) = 0$ 时，任意满足 $0 < \lambda < +\infty$ 的常数 $\lambda$
均属于 $\mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem singleChannelFeasible_of_inf_eq_zero
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (_hU : U ⊆ dom ϕ) (i j : I)
    (ha_zero : singleChannelLipConst d ϕ U i j = 0)
    {lam : ENNReal} (hlam_pos : 0 < lam) (_hlam_lt_top : lam < ⊤) :
    lam ∈ SingleChannelFeasibleSet d ϕ U i j := by
  have h_lt : singleChannelLipConst d ϕ U i j < lam := by
    rwa [ha_zero]
  rcases sInf_lt_iff.mp h_lt with ⟨lam₀, hlam₀_mem, hlam₀_lt⟩
  exact singleChannelFeasibleSet_upper_closed d ϕ U i j hlam₀_mem (le_of_lt hlam₀_lt)

/--
**义务 `HC02-P23`（反例构造：零下确界未必由 $0$ 实现）**：
取集合 `X = Option Bool`（吸收元 `bot = none`，非吸收点 `some false`、`some true`），
单指标集 `I = Unit`，离散无穷扩展伪度量 `d () x y = if x = y then 0 else ⊤`，
恒等算子 `ϕ = idOperator (Option Bool) none`，非空合法子集 `U = dom ϕ`。
则单通道下确界 `singleChannelLipConst = 0`，但 $\lambda = 0$ 不满足该单通道标量上界。
-/
def ceSpaceBot : Option Bool := none

def ceMetric : Unit → Option Bool → Option Bool → ENNReal :=
  fun _ x y => if x = y then 0 else ⊤

instance ceExtendedPseudoMetric (i : Unit) :
    ExtendedPseudoMetric (Option Bool) ceSpaceBot (ceMetric i) where
  nonabsorbing := ⟨some false, by decide⟩
  dist_self x := by simp [ceMetric]
  symm x y := by
    dsimp [ceMetric]
    by_cases hxy : x = y
    · subst hxy
      rfl
    · have hyx : y ≠ x := Ne.symm hxy
      simp [hxy, hyx]
  triangle x y z := by
    dsimp [ceMetric]
    by_cases hxz : x = z
    · simp [hxz]
    · by_cases hxy : x = y
      · by_cases hyz : y = z
        · exact False.elim (hxz (Eq.trans hxy hyz))
        · simp [hxy, hyz]
      · simp [hxy]
  isolate_bot x hx := by
    dsimp [ceMetric, ceSpaceBot] at hx ⊢
    exact if_neg hx

def ceOperator : Operator (Option Bool) ceSpaceBot :=
  idOperator (Option Bool) ceSpaceBot

def ceSubset : Set (Option Bool) :=
  dom ceOperator

/-- **义务 `HC02-P23`（反例定理：$\underline{L} = 0$ 但 $0$ 不可行）**。 -/
theorem zero_inf_not_attained_counterexample :
    ceSubset.Nonempty ∧
    ceSubset ⊆ dom ceOperator ∧
    singleChannelLipConst ceMetric ceOperator ceSubset () () = 0 ∧
    (0 : ENNReal) ∉ SingleChannelFeasibleSet ceMetric ceOperator ceSubset () () := by
  refine ⟨⟨some false, by simp [ceSubset, dom, ceOperator, ceSpaceBot]⟩, Set.Subset.rfl, ?_, ?_⟩
  · by_contra h_ne_zero
    have ha_pos : 0 < singleChannelLipConst ceMetric ceOperator ceSubset () () :=
      pos_iff_ne_zero.mpr h_ne_zero
    rcases exists_between ha_pos with ⟨lam, hlam_pos, hlam_lt⟩
    have hlam_mem : lam ∈ SingleChannelFeasibleSet ceMetric ceOperator ceSubset () () := by
      intro x _ y _
      by_cases hxy : x = y
      · subst hxy
        simp [ceOperator, ceMetric]
      · simp [ceOperator, ceMetric, hxy, ENNReal.mul_top hlam_pos.ne']
    exact not_le_of_gt hlam_lt (sInf_le hlam_mem)
  · intro h0
    have hx : some false ∈ ceSubset := by simp [ceSubset, dom, ceOperator, ceSpaceBot]
    have hy : some true ∈ ceSubset := by simp [ceSubset, dom, ceOperator, ceSpaceBot]
    have hle := h0 (some false) hx (some true) hy
    simp [ceOperator, ceMetric] at hle

/--
OET anchor: h-57de7918859a9de2
**义务 `HC02-P24`（单通道下确界有限当且仅当存在有限可行常数）**：
无论下确界是否被取到，$\underline{L}_{i \to j}(\phi; U) < +\infty$ 等价于
存在有限常数 $\lambda < +\infty$ 满足对所有 $x, y \in U$ 有 $d_j(\phi(x), \phi(y)) \le \lambda d_i(x, y)$。
-/
theorem singleChannelLipConst_lt_top_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) (i j : I) :
    singleChannelLipConst d ϕ U i j < ⊤ ↔
      ∃ lam : ENNReal, lam < ⊤ ∧ lam ∈ SingleChannelFeasibleSet d ϕ U i j := by
  constructor
  · intro h_lt_top
    by_cases ha0 : singleChannelLipConst d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact singleChannelFeasible_of_inf_eq_zero d ϕ hU i j ha0 zero_lt_one ENNReal.one_lt_top
    · have ha_pos : 0 < singleChannelLipConst d ϕ U i j := pos_iff_ne_zero.mpr ha0
      refine ⟨singleChannelLipConst d ϕ U i j, h_lt_top, ?_⟩
      exact singleChannelLipConst_mem_of_pos_of_lt_top d ϕ hU i j ha_pos h_lt_top
  · rintro ⟨lam, hlam_lt_top, hlam_mem⟩
    exact lt_of_le_of_lt (sInf_le hlam_mem) hlam_lt_top

/-!
## 5. 分量解耦、双侧标量界与可分辨保持 (`HC02-P25` – `HC02-P32`)
-/

/--
**义务 `HC02-P25`（零系数移除该证书求和项，含 $d_i(x, y) = +\infty$ 情形）**：
当 $L_{i \to j} = 0$ 时，对任意 $x, y \in \mathcal{X}$（允许 $d_i(x, y) = +\infty$），
该项乘积 $L_{i \to j} d_i(x, y) = 0$，且输出分量 $j$ 的上界求和可直接删去输入分量 $i$ 的项。
-/
theorem zero_entry_removes_sum_term
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {L : GaugeMatrix I}
    (hL : L ∈ RestrictedLipMatrices d ϕ U) {i j : I} (hLij : L i j = 0) :
    (∀ x y : X, L i j * d i x y = 0) ∧
    (∀ x y : X, (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y) ∧
    (∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y) := by
  have h_term : ∀ x y : X, L i j * d i x y = 0 := by
    intro x y
    rw [hLij, zero_mul]
  have h_sum : ∀ x y : X, (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
    intro x y
    rw [← Finset.add_sum_erase Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i),
      h_term x y, zero_add]
  refine ⟨h_term, h_sum, ?_⟩
  intro x hx y hy
  rw [← h_sum x y]
  exact hL.2 x hx y hy j

/--
**义务 `HC02-P26`（任意唯一输入位置的单行化简）**：
设 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 且固定输出行 $j$ 满足 $\forall k \neq i,\; L_{k \to j} = 0$（唯一输入指标 $i$ 不必等于 $j$），
则对任意 $x, y \in U$ 有 $d_j(\phi(x), \phi(y)) \le L_{i \to j} \cdot d_i(x, y)$。
-/
theorem rowSparse_scalar_upper_bound
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {L : GaugeMatrix I}
    (hL : L ∈ RestrictedLipMatrices d ϕ U) {i j : I}
    (hRow : IsRowSparseAt L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have h_sum : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact (zero_entry_removes_sum_term d ϕ hL (hRow k hki)).1 x y
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [← h_sum]
  exact hL.2 x hx y hy j

/--
**义务 `HC02-P27`（任意单列支撑的证书贡献范围）**：
若所选证书 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 的固定输入列 $i$ 满足 $\forall k \neq j,\; L_{i \to k} = 0$，
则对任意输出指标 $k \neq j$ 与任意 $x, y \in U$，均有 $L_{i \to k} d_i(x, y) = 0$，
且在该上界证书中 $d_i$ 的输入差异不进入任何 $k \neq j$ 的输出上界求和（至多向输出分量 $d_j$ 贡献）。
-/
theorem colSparse_contribution_range
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {L : GaugeMatrix I}
    (hL : L ∈ RestrictedLipMatrices d ϕ U) {i j : I}
    (hCol : IsColSparseAt L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      L i k * d i x y = 0 ∧
      d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y := by
  intro k hkj x hx y hy
  have hLik : L i k = 0 := hCol k hkj
  have h_rem := zero_entry_removes_sum_term d ϕ hL hLik
  exact ⟨h_rem.1 x y, h_rem.2.2 x hx y hy⟩

/--
**义务 `HC02-P28`（对角 Lip 矩阵给出所有分量的独立标量上界）**：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 为对角矩阵（$\forall i \neq j,\; L_{i \to j} = 0$），
则对任意 $j \in I$ 和任意 $x, y \in U$ 有 $d_j(\phi(x), \phi(y)) \le L_{j \to j} d_j(x, y)$。
-/
theorem diagonal_scalar_upper_bound
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {L : GaugeMatrix I}
    (hL : L ∈ RestrictedLipMatrices d ϕ U)
    (hDiag : IsDiagonalMatrix L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  have hRow : IsRowSparseAt L j j := fun k hkj => hDiag k j hkj
  exact rowSparse_scalar_upper_bound d ϕ hL hRow

/--
OET anchor: h-6a98a58b5bc95360
**义务 `HC02-P29`（引理：对角输入项的标量双侧界，仅要求 Lip 行稀疏）**：
设 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 与 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$，
且仅假设 $\mathbf{L}$ 在输出分量 $j$ 上满足 $L_{k \to j} = 0$（$\forall k \neq j$），
则对任意 $x, y \in U$ 有标量双侧不等式：
$K_{j \to j} \cdot d_j(x, y) \le d_j(\phi(x), \phi(y)) \le L_{j \to j} \cdot d_j(x, y)$。
-/
theorem diagonal_row_bilateral_bound
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipMatrices d ϕ U)
    (hK : K ∈ RestrictedCoLipMatrices d ϕ U)
    (j : I) (hRowL : IsRowSparseAt L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, rowSparse_scalar_upper_bound d ϕ hL hRowL x hx y hy⟩
  calc
    K j j * d j x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ j)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
**义务 `HC02-P30`（逐分量标量双侧不等式及有限系数分支）**：
若对所有 $j \in I$ 均满足对角输入项 Lip 条件（$\forall k \neq j,\; L_{k \to j} = 0$），
则全部分量的双侧标量不等式同时成立；
若进一步要求 $\forall j \in I,\; L_{j \to j} < +\infty$ 且 $K_{j \to j} < +\infty$，
则得到各分量系数均有限的标量双侧放缩界。
-/
theorem componentwise_bilateral_bound
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipMatrices d ϕ U)
    (hK : K ∈ RestrictedCoLipMatrices d ϕ U)
    (hRowsL : ∀ j : I, IsRowSparseAt L j j) :
    (∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y) ∧
    ((∀ j : I, L j j < ⊤ ∧ K j j < ⊤) →
      ∀ j : I, K j j < ⊤ ∧ L j j < ⊤ ∧
        ∀ x ∈ U, ∀ y ∈ U,
          K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y) := by
  have h_all : ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
    fun j => diagonal_row_bilateral_bound d ϕ hL hK j (hRowsL j)
  refine ⟨h_all, ?_⟩
  intro h_fin j
  exact ⟨(h_fin j).2, (h_fin j).1, h_all j⟩

/--
OET anchor: h-f82672ec0dd48f28
**义务 `HC02-P31`（命题 (i)：正 co-Lip 通道保持可分辨性）**：
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若 $K_{i \to j} > 0$，则对任意 $x, y \in U$：
$d_i(x, y) > 0 \Longrightarrow d_j(\phi(x), \phi(y)) > 0$。
-/
theorem pos_coLip_preserves_distinguishability
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ RestrictedCoLipMatrices d ϕ U)
    {i j : I} (hKij : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdi
  have h_prod_pos : 0 < K i j * d i x y := ENNReal.mul_pos hKij.ne' hdi.ne'
  have h_le : K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
    calc
      K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
        Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
  exact lt_of_lt_of_le h_prod_pos h_le

/--
OET anchor: h-f82672ec0dd48f28
**义务 `HC02-P32`（命题 (ii)：正对角 co-Lip 通道反射族零距关系）**：
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若对所有 $j \in I$ 均有 $K_{j \to j} > 0$，
则 $\phi$ 在 $U$ 上反射族零距关系：对任意 $x, y \in U$，
$\phi(x) \sim_{\mathcal{G}} \phi(y) \Longrightarrow x \sim_{\mathcal{G}} y$。
-/
theorem pos_diag_coLip_reflects_gaugeZeroRelated
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ RestrictedCoLipMatrices d ϕ U)
    (hK_diag : ∀ j : I, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy h_rel j
  by_contra h_ne_zero
  have h_pos : 0 < d j x y := pos_iff_ne_zero.mpr h_ne_zero
  have h_out_pos := pos_coLip_preserves_distinguishability d ϕ hK (hK_diag j) x hx y hy h_pos
  exact ne_of_gt h_out_pos (h_rel j)

end formal_oet.vol_01.ch_02_operator_bounds
```

### 对齐清单 `alignment.json`

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "HC02-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipMatrices"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.RestrictedLipMatrices"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipMatrices_eq_restrictedLipMatrices_dom"
        }
      ],
      "representation": "在有限非空指标集 I（[Fintype I] [Nonempty I]）、扩展伪度量族 d（[∀ i : I, ExtendedPseudoMetric X bot (d i)]）与保持 bot 的算子 ϕ : Operator X bot 下，定义全域合法 Lipschitz 矩阵集 LipMatrices d ϕ 与子集受限合法 Lipschitz 矩阵集 RestrictedLipMatrices d ϕ U : Set (GaugeMatrix I)。其中受限定义包含 U ⊆ dom ϕ 及 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y，所有系数与距离均取值于 ENNReal。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.RestrictedCoLipMatrices"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroMatrix_mem_restrictedCoLipMatrices"
        }
      ],
      "representation": "定义子集受限 co-Lipschitz 证书族 RestrictedCoLipMatrices d ϕ U : Set (GaugeMatrix I)，显式包含非空性 U.Nonempty（U ≠ ∅）、定义域包含 U ⊆ dom ϕ 以及 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, (∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)；矩阵条目取值于 ENNReal，0 与 ⊤（+∞）均为合法系数。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.GaugeMatrix"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ofDisplayMatrix"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixRow"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixCol"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixMul"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_gaugeMatrixMul"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixMul_assoc"
        }
      ],
      "representation": "以 GaugeMatrix I := I → I → ENNReal 实现输入优先存储，M i j 表示输入分量 i 到输出分量 j 的条目 M_{i→j}；通过 toDisplayMatrix M j i = M i j 表示第 j 行（固定输出 j）第 i 列（固定输入 i）的通常行列显示矩阵；定义复合乘法 gaugeMatrixMul M₂ M₁ i j = ∑ k : I, M₂ k j * M₁ i k，并由 toDisplayMatrix_gaugeMatrixMul 证明其与显示矩阵的标准矩阵乘法完全对应。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixId"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixChainProd"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixChainProd_nil"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixChainProd_singleton"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixChainProd_cons"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.idOperator"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.compOperator"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.composeOperatorChain"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.composeOperatorChain_eq_operatorChain_reverse"
        }
      ],
      "representation": "定义单位矩阵 gaugeMatrixId I i j = if i = j then 1 else 0（δ_{ij}）；对按施行顺序 [ϕ₁, …, ϕₖ] 排列的算子与矩阵列表 [L₁, …, Lₖ]，定义算子复合 composeOperatorChain 与矩阵有序乘积 gaugeMatrixChainProd，满足空乘积（k=0）定义上等于单位矩阵 gaugeMatrixId I，k=1 时 gaugeMatrixChainProd [M] = M 等于该唯一矩阵，多步时对应 Lₖ ⋯ L₁。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainImageAt"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainImageAt_succ_eq_image"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.operator_image_compOperator"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainImageAt_length_eq_compose_image"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.dom_of_subset_dom_compOperator"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainImageAt_subset_dom"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipChainData"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipChainData"
        }
      ],
      "representation": "通过 chainImageAt 递归定义中间实际像集 U_{m+1} = ϕ_m(U_m)，由 chainImageAt_succ_eq_image 证明逐步递推式，由 chainImageAt_length_eq_compose_image 证明全复合像等于逐次像，由 chainImageAt_subset_dom 从 U₁ ⊆ dom(c_k) 推出每步 U_m ⊆ dom(ϕ_m)。结构 LipChainData 与 CoLipChainData 仅由算子链、U₁ ⊆ dom(c_k)、逐步矩阵及各实际输入域 U_m 上的单步证书合法性构造，不含任何最终复合界字段。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IntermediateIndexSeq"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.emptyIntermediateSeq"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.uniqueIntermediateIndexSeqOne"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathSourceIndex"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathTargetIndex"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathStepEntry"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathHasZeroEdge"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathAllPositive"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeMatrixChainProd_eq_sum_pathWeight"
        }
      ],
      "representation": "对 n ≥ 1，固定起止指标 k₀ = i、kₙ = j，以 IntermediateIndexSeq I n := Fin (n - 1) → I 无正性约束地遍历全部中间指标序列；n = 1 时由 uniqueIntermediateIndexSeqOne 给出唯一空中间序列 emptyIntermediateSeq。定义各层条目 pathStepEntry、路径乘积权重 pathWeight、含零边谓词 PathHasZeroEdge（∃ m, 条目 = 0）与全正谓词 PathAllPositive（∀ m, 条目 > 0），并证明乘积展开定理 gaugeMatrixChainProd_eq_sum_pathWeight。",
      "dependencies": [
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowSparseAt"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.MatrixRowDecoupled"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowDecoupled"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColSparseAt"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.MatrixColDecoupled"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColDecoupled"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagonalMatrix"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsFullyDecoupledCert"
        }
      ],
      "representation": "定义分量通道 ComponentChannel I := I × I；单行稀疏 IsRowSparseAt L i j 为 ∀ k ≠ i, L k j = 0，行解耦 MatrixRowDecoupled / IsRowDecoupled 为存在 i 满足单行稀疏；单列稀疏 IsColSparseAt L i j 为 ∀ k ≠ j, L i k = 0，列解耦 MatrixColDecoupled / IsColDecoupled 为存在 j 满足单列稀疏；对角矩阵 IsDiagonalMatrix L 为 ∀ i ≠ j, L i j = 0，完全解耦证书为 IsFullyDecoupledCert。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.SingleChannelFeasibleSet"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasibleSet_sInf_empty"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_eq_top_of_feasible_empty"
        }
      ],
      "representation": "定义单通道可行标量集合 SingleChannelFeasibleSet d ϕ U i j := {lam : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y} 及其下确界 singleChannelLipConst d ϕ U i j := sInf (SingleChannelFeasibleSet d ϕ U i j)，满足 sInf ∅ = ⊤，且与多分量 Lip 矩阵条目区分。",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipMatrix_singleton_iff"
        }
      ],
      "representation": "当指标集仅含单一元素 i（∀ k : I, k = i）时，证明 L ∈ LipMatrices d ϕ 等价于单分量标量不等式 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipMatrices_subset_restrictedLipMatrices"
        }
      ],
      "representation": "证明当 U ⊆ dom ϕ 时，全域合法 Lip 证书族含于受限证书族：LipMatrices d ϕ ⊆ RestrictedLipMatrices d ϕ U。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipMatrices_antitone"
        }
      ],
      "representation": "证明当 U ⊆ V 且 V ⊆ dom ϕ 时，缩小评估域会扩大可行 Lip 证书族：RestrictedLipMatrices d ϕ V ⊆ RestrictedLipMatrices d ϕ U。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.entrywiseLipInf"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.entrywiseLipInf_mono"
        }
      ],
      "representation": "定义受限证书族逐条目下确界 entrywiseLipInf d ϕ U i j := sInf {val | ∃ M ∈ RestrictedLipMatrices d ϕ U, M i j = val}，并由 restrictedLipMatrices_antitone 证明当 U ⊆ V 时 entrywiseLipInf d ϕ U i j ≤ entrywiseLipInf d ϕ V i j。",
      "dependencies": [
        "HC02-D01",
        "HC02-P03"
      ]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipMatrices_comp"
        }
      ],
      "representation": "证明命题 #h-193cebcc1a7f9259（两步 Lip 矩阵复合律）：当 U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)、L₁ ∈ RestrictedLipMatrices d ϕ₁ U₁ 且 L₂ ∈ RestrictedLipMatrices d ϕ₂ (operator_image ϕ₁ U₁) 时，gaugeMatrixMul L₂ L₁ ∈ RestrictedLipMatrices d (compOperator ϕ₂ ϕ₁) U₁。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_entry_eq_zero_of_output_zero"
        }
      ],
      "representation": "证明注 #h-88784dcbfff0ea66：若存在 x, y ∈ dom ϕ 使 d j (ϕ.func x) (ϕ.func y) = 0 且 0 < d i x y，则任意全域 co-Lip 矩阵 K ∈ RestrictedCoLipMatrices d ϕ (dom ϕ) 必满足 K i j = 0。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedCoLipMatrices_comp"
        }
      ],
      "representation": "证明命题 #h-0f256e6f1d38a612（两步 co-Lip 矩阵复合律）：当 U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)、K₁ ∈ RestrictedCoLipMatrices d ϕ₁ U₁ 且 K₂ ∈ RestrictedCoLipMatrices d ϕ₂ (operator_image ϕ₁ U₁) 时，gaugeMatrixMul K₂ K₁ ∈ RestrictedCoLipMatrices d (compOperator ϕ₂ ϕ₁) U₁（包含 U₁.Nonempty）。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.commonDom"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.image_dist_perturbation_forward"
        }
      ],
      "representation": "证明命题 #h-b959b42f25710105 (i) 正向式：在 U ⊆ commonDom ϕ₁ ϕ₂ 且 ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j 下，对任意 x, y ∈ U 与 j : I，有 d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j（及 + δ j + δ j）。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.image_dist_perturbation_reverse"
        }
      ],
      "representation": "证明命题 #h-b959b42f25710105 (i) 反向式：在相同扰动前提下，利用伪度量对称性交换 ϕ₁, ϕ₂，得 d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j（及 + δ j + δ j）。",
      "dependencies": [
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbed_lip_upper_bound"
        }
      ],
      "representation": "证明命题 #h-b959b42f25710105 (ii) Lip 上界桥接：在扰动前提与 L₁ ∈ RestrictedLipMatrices d ϕ₁ U 下，对任意 x, y ∈ U 与 j : I，有 d j (ϕ₂.func x) (ϕ₂.func y) ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j。",
      "dependencies": [
        "HC02-D01",
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbed_coLip_lower_bound"
        }
      ],
      "representation": "证明命题 #h-b959b42f25710105 (iii) co-Lip 下界桥接：在扰动前提与 K₁ ∈ RestrictedCoLipMatrices d ϕ₁ U 下，对任意 x, y ∈ U 与 j : I，有 (∑ i : I, K₁ i j * d i x y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j。",
      "dependencies": [
        "HC02-D02",
        "HC02-P09"
      ]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chain_restrictedLipMatrices_prod"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipChainData.prod_mem_restrictedLipMatrices"
        }
      ],
      "representation": "证明推论 #h-c80171fa685dc795 (i)：对任意正长度算子链 ϕs ≠ []，当 U₁ ⊆ dom(c_k) 且每步矩阵 Ls[m] 在实际递推像域 chainImageAt ϕs U₁ m 上属于 RestrictedLipMatrices 时，有序乘积 gaugeMatrixChainProd Ls 属于 RestrictedLipMatrices d (composeOperatorChain ϕs) U₁。",
      "dependencies": [
        "HC02-D01",
        "HC02-D04",
        "HC02-D05",
        "HC02-P05"
      ]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chain_restrictedCoLipMatrices_prod"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipChainData.prod_mem_restrictedCoLipMatrices"
        }
      ],
      "representation": "证明推论 #h-c80171fa685dc795 (ii)：对任意正长度算子链 ϕs ≠ []，当 U₁ ⊆ dom(c_k) 且每步矩阵 Ks[m] 在实际递推像域 chainImageAt ϕs U₁ m 上属于 RestrictedCoLipMatrices（含各步非空性）时，有序乘积 gaugeMatrixChainProd Ks 属于 RestrictedCoLipMatrices d (composeOperatorChain ϕs) U₁。",
      "dependencies": [
        "HC02-D02",
        "HC02-D04",
        "HC02-D05",
        "HC02-P07"
      ]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_gaugeMatrixId_mul_dist"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_id_mem_restrictedLipMatrices"
        }
      ],
      "representation": "证明注 #h-11006ddd8c43bfec 的 Lip 部分：当 k=0、c₀ = idOperator X bot 时，对任意非空 U ⊆ dom(idOperator X bot)，单位矩阵 gaugeMatrixId I（即空乘积 gaugeMatrixChainProd []）属于 RestrictedLipMatrices d (idOperator X bot) U。",
      "dependencies": [
        "HC02-D01",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_id_mem_restrictedCoLipMatrices"
        }
      ],
      "representation": "证明注 #h-11006ddd8c43bfec 的 co-Lip 部分：对同一非空 U ⊆ dom(idOperator X bot)，单位矩阵 gaugeMatrixId I（即空乘积 gaugeMatrixChainProd []）属于 RestrictedCoLipMatrices d (idOperator X bot) U。",
      "dependencies": [
        "HC02-D02",
        "HC02-D04",
        "HC02-P14"
      ]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight_eq_zero_iff_pathHasZeroEdge"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChainProd_entry_eq_zero_iff"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChainProd_entry_eq_zero_iff_singleton"
        }
      ],
      "representation": "证明命题 #h-e4154c34e95d3c23 (i)：在非空算子链与逐步受限 Lip 证书序列下，gaugeMatrixChainProd Ls i j = 0 当且仅当对所有中间指标序列 ks 均满足 PathHasZeroEdge Ls i j ks；并由 lipChainProd_entry_eq_zero_iff_singleton 证明 n=1 时退化为 L₁ i j = 0。",
      "dependencies": [
        "HC02-D01",
        "HC02-D04",
        "HC02-D05",
        "HC02-D06"
      ]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight_pos_iff_pathAllPositive"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChainProd_entry_pos_iff"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChainProd_entry_pos_iff_singleton"
        }
      ],
      "representation": "证明命题 #h-e4154c34e95d3c23 (ii)：在非空算子链与逐步受限 co-Lip 证书序列下，0 < gaugeMatrixChainProd Ks i j 当且仅当存在中间指标序列 ks 满足 PathAllPositive Ks i j ks；并由 coLipChainProd_entry_pos_iff_singleton 证明 n=1 时唯一空中间序列对应 0 < K₁ i j。",
      "dependencies": [
        "HC02-D02",
        "HC02-D04",
        "HC02-D05",
        "HC02-D06"
      ]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_eq_top_of_zero_input_pos_output"
        }
      ],
      "representation": "证明若存在 x, y ∈ U 使 d i x y = 0 且 0 < d j (ϕ.func x) (ϕ.func y)，则不存在任何 λ : ENNReal 属于 SingleChannelFeasibleSet d ϕ U i j，可行族为空集 ∅ 且 singleChannelLipConst d ϕ U i j = ⊤。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_mem_of_pos_of_lt_top"
        }
      ],
      "representation": "证明当 a = singleChannelLipConst d ϕ U i j 满足 0 < a 且 a < ⊤ 时，下确界可被取到：a ∈ SingleChannelFeasibleSet d ϕ U i j，即对所有 x, y ∈ U 成立 d j (ϕ.func x) (ϕ.func y) ≤ a * d i x y。",
      "dependencies": [
        "HC02-D08",
        "HC02-P21"
      ]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasibleSet_upper_closed"
        }
      ],
      "representation": "证明单通道标量可行族向上封闭：若 lam₀ ∈ SingleChannelFeasibleSet d ϕ U i j 且 lam₀ ≤ lam₁，则 lam₁ ∈ SingleChannelFeasibleSet d ϕ U i j。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasible_of_gt_inf"
        }
      ],
      "representation": "证明在 0 < singleChannelLipConst d ϕ U i j < ⊤ 语境下，任意满足 singleChannelLipConst d ϕ U i j < lam 的常数 lam : ENNReal（含 lam = ⊤）均属于 SingleChannelFeasibleSet d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P20"
      ]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasible_of_inf_eq_zero"
        }
      ],
      "representation": "证明当 singleChannelLipConst d ϕ U i j = 0 时，任意满足 0 < lam 且 lam < ⊤ 的有限正常数 lam 均属于 SingleChannelFeasibleSet d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P20"
      ]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ceSpaceBot"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ceMetric"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ceExtendedPseudoMetric"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ceOperator"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ceSubset"
        },
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_inf_not_attained_counterexample"
        }
      ],
      "representation": "显式构造合法的扩展规范空间（Option Bool 上以 none 为吸收元的离散 ⊤-扩展伪度量 ceMetric，满足 ExtendedPseudoMetric）、合法算子 ceOperator 与非空定义域子集 ceSubset，证明 singleChannelLipConst ceMetric ceOperator ceSubset () () = 0 但 0 ∉ SingleChannelFeasibleSet ceMetric ceOperator ceSubset () ()。",
      "dependencies": [
        "HC02-D04",
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_lt_top_iff"
        }
      ],
      "representation": "证明注 #h-57de7918859a9de2：singleChannelLipConst d ϕ U i j < ⊤ 当且仅当存在有限常数 lam < ⊤ 属于 SingleChannelFeasibleSet d ϕ U i j（满足全部点对单通道标量上界）。",
      "dependencies": [
        "HC02-D08",
        "HC02-P19",
        "HC02-P22"
      ]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_entry_removes_sum_term"
        }
      ],
      "representation": "证明当 L i j = 0 时，对任意 x, y（允许 d i x y = ⊤）均有 L i j * d i x y = 0，且在受限 Lip 证书 L 的第 j 个输出分量求和中可直接删去输入分量 i 的项（∑ k ∈ Finset.univ.erase i, L k j * d k x y）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.rowSparse_scalar_upper_bound"
        }
      ],
      "representation": "证明当 L ∈ RestrictedLipMatrices d ϕ U 且满足单行稀疏 IsRowSparseAt L i j（∀ k ≠ i, L k j = 0，i 不必等于 j）时，对所有 x, y ∈ U 有 d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07",
        "HC02-P25"
      ]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.colSparse_contribution_range"
        }
      ],
      "representation": "证明当 L ∈ RestrictedLipMatrices d ϕ U 且满足单列稀疏 IsColSparseAt L i j（∀ k ≠ j, L i k = 0）时，对所有 k ≠ j 与 x, y ∈ U 有 L i k * d i x y = 0，且 d k (ϕ.func x) (ϕ.func y) 的证书上界求和可删去输入 i（即输入 i 至多向输出分量 j 贡献）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07",
        "HC02-P25"
      ]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.diagonal_scalar_upper_bound"
        }
      ],
      "representation": "证明当 L ∈ RestrictedLipMatrices d ϕ U 且为对角矩阵 IsDiagonalMatrix L 时，对所有分量 j : I 与 x, y ∈ U 有 d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.diagonal_row_bilateral_bound"
        }
      ],
      "representation": "证明引理 #h-6a98a58b5bc95360：设 L ∈ RestrictedLipMatrices d ϕ U、K ∈ RestrictedCoLipMatrices d ϕ U，仅假设 L 在第 j 行满足 IsRowSparseAt L j j（∀ k ≠ j, L k j = 0），则对所有 x, y ∈ U 有双侧标量界 K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.componentwise_bilateral_bound"
        }
      ],
      "representation": "证明当 ∀ j : I, IsRowSparseAt L j j 成立时，所有分量 j : I 同时满足双侧标量界；若进一步有 ∀ j : I, L j j < ⊤ ∧ K j j < ⊤，则所有分量的双侧标量界同时具备有限上下界系数。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D07",
        "HC02-P29"
      ]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pos_coLip_preserves_distinguishability"
        }
      ],
      "representation": "证明命题 #h-f82672ec0dd48f28 (i)：当 K ∈ RestrictedCoLipMatrices d ϕ U 且 0 < K i j 时，对任意 x, y ∈ U，若 0 < d i x y 则 0 < d j (ϕ.func x) (ϕ.func y)。",
      "dependencies": [
        "HC02-D02"
      ]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pos_diag_coLip_reflects_gaugeZeroRelated"
        }
      ],
      "representation": "证明命题 #h-f82672ec0dd48f28 (ii)：当 K ∈ RestrictedCoLipMatrices d ϕ U 且 ∀ j : I, 0 < K j j 时，对任意 x, y ∈ U，GaugeZeroRelated d (ϕ.func x) (ϕ.func y) 蕴含 GaugeZeroRelated d x y。",
      "dependencies": [
        "HC02-D02",
        "HC02-P31"
      ]
    }
  ]
}
```

### 完成度与严格对齐说明

- **完整完成与严格对齐**：整章（第2章《算子界》）的全部数学内容及 [obligations.json](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/obligations.json) 中的全部 40 项义务（`HC02-D01` 至 `HC02-D08`，`HC02-P01` 至 `HC02-P32`）均已 **100% 完整形式化并严格对齐**。
- **验证状态**：[Main.lean](file:///private/tmp/math-gauge-v060-argon-gcp-20261110/attempts/HCH02/physical-5/session/work/Main.lean) 在 Lean 4.29.1 与指定 mathlib 下通过内核完整编译（0 错误、0 警告），未使用任何 `sorry`、`admit` 或新增公理；经 `#print axioms` 逐一核验，全部 99 个声明仅依赖标准逻辑公理 `propext`、`Classical.choice`、`Quot.sound`。
- **未完成或未确认的范围**：无（全部 40 项义务状态均为 `"complete"`）。