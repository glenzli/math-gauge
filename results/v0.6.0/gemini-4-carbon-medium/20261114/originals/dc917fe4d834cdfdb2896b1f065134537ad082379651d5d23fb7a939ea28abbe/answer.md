{}
以下提交第2章（《算子界》，见冻结原文 [02-operator-bounds.md](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/source/02-operator-bounds.md) 及义务清单 [obligations.json](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/obligations.json)）的完整 Lean 4.29.1 形式化源码与对齐清单：

- [MatrixBounds.lean](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/OperatorBounds/MatrixBounds.lean)：对应 §2.1 矩阵界与有限复合（`HC02-D01` 至 `HC02-D06`，`HC02-P01` 至 `HC02-P17`），直接复用未修改的前置模块 [gauge_space.lean](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean) 与 [operator_space.lean](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean)。
- [ChannelBounds.lean](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/OperatorBounds/ChannelBounds.lean)：对应 §2.2 分量解耦与通道分辨保持（`HC02-D07`、`HC02-D08`，`HC02-P18` 至 `HC02-P32`）。
- [Main.lean](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/Main.lean)：导入上述全部目标模块。
- [alignment.json](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/alignment.json)：40 项义务完整映射与依赖记录。

*理论来源署名（CC BY 4.0，详见 [ATTRIBUTION.md](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/ATTRIBUTION.md) 与 [LICENSE](file:///private/tmp/math-gauge-carbon-medium-final-lane2-20261114-v8/attempts/HCH02/physical-1/session/work/LICENSE)）：本章数学内容源自 Zhe Li (Glen Li / glenzli), ORCID `https://orcid.org/0009-0006-6536-3453`, The Operator Evolution Theory (`https://glenzli.com/books/oet/`, `https://gitlab.com/glenzli/oet-public`), CC BY 4.0（历史快照版本）。*

```lean filename=OperatorBounds/MatrixBounds.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-!
# 第2章 算子界 — §2.1 矩阵界与有限复合 (`#h-af85899693cc8750`)

本模块形式化第2章第一节的全部定义、表示与命题证明义务（`HC02-D01` 至 `HC02-D06`，
`HC02-P01` 至 `HC02-P17`）。
-/

/-! ## 基础算子辅助：恒等算子、二元复合与公共定义域 -/

/-- 底层空间上的恒等算子 $\mathrm{id}_{\mathcal{X}} \in \mathcal{X}_{\mathrm{op}}$。 -/
def idOp {X : Type} {bot : X} : Operator X bot where
  func := id
  preserves_bot := rfl

/-- 两个算子的复合 $\phi_2 \circ \phi_1 \in \mathcal{X}_{\mathrm{op}}$（先施行 $\phi_1$，再施行 $\phi_2$）。 -/
def compOp {X : Type} {bot : X} (ϕ₂ ϕ₁ : Operator X bot) : Operator X bot where
  func := ϕ₂.func ∘ ϕ₁.func
  preserves_bot := by
    simp [Function.comp, ϕ₁.preserves_bot, ϕ₂.preserves_bot]

/-- 两个算子的公共定义域 $\mathrm{dom}(\phi_1, \phi_2) = \mathrm{dom}(\phi_1) \cap \mathrm{dom}(\phi_2)$。 -/
def commonDom {X : Type} {bot : X} (ϕ₁ ϕ₂ : Operator X bot) : Set X :=
  dom ϕ₁ ∩ dom ϕ₂

/-- 若 $x \in \mathrm{dom}(\phi_2 \circ \phi_1)$，则 $x \in \mathrm{dom}(\phi_1)$。 -/
theorem dom_compOp_subset_left {X : Type} {bot : X} (ϕ₂ ϕ₁ : Operator X bot) :
    dom (compOp ϕ₂ ϕ₁) ⊆ dom ϕ₁ := by
  intro x hx hphi1
  apply hx
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [hphi1, ϕ₂.preserves_bot]

/-- 若 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，则像集 $\phi_1(U_1) \subseteq \mathrm{dom}(\phi_2)$。 -/
theorem image_subset_dom_of_subset_dom_compOp {X : Type} {bot : X}
    (ϕ₂ ϕ₁ : Operator X bot) {U₁ : Set X} (hU₁ : U₁ ⊆ dom (compOp ϕ₂ ϕ₁)) :
    operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro y ⟨x, hx, rfl⟩
  exact hU₁ hx

/-! ## HC02-D03: 输入输出指标、显示矩阵和乘法 -/

/--
**算子界矩阵（输入优先存储）** (`HC02-D03`)：
`M i j` 表示条目 $M_{i \to j} \in \bar{\mathbb{R}}_+$，其中第一个指标 `i` 为输入分量，
第二个指标 `j` 为输出分量。
-/
abbrev BoundMatrix (I : Type) : Type := I → I → ENNReal

/--
**普通行列显示矩阵表示** (`HC02-D03`)：
把 `M : BoundMatrix I` 写成通常的行列矩阵 `Matrix I I ENNReal` 时，输出指标 `j` 标记行，
输入指标 `i` 标记列，故第 `j` 行第 `i` 列的条目为 `M i j`。
-/
def toDisplayMatrix {I : Type} (M : BoundMatrix I) : Matrix I I ENNReal :=
  Matrix.of fun j i => M i j

/-- 从普通行列矩阵还原输入优先存储的算子界矩阵 (`HC02-D03`)。 -/
def ofDisplayMatrix {I : Type} (A : Matrix I I ENNReal) : BoundMatrix I :=
  fun i j => A j i

/-- 输入优先存储与普通行列矩阵（行=输出 `j`、列=输入 `i`）之间的双射等价 (`HC02-D03`)。 -/
def displayMatrixEquiv (I : Type) : BoundMatrix I ≃ Matrix I I ENNReal where
  toFun := toDisplayMatrix
  invFun := ofDisplayMatrix
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem toDisplayMatrix_apply {I : Type} (M : BoundMatrix I) (j i : I) :
    toDisplayMatrix M j i = M i j :=
  rfl

/--
**算子界矩阵复合乘法** (`HC02-D03`)：
$(\mathbf{M}_2 \cdot \mathbf{M}_1)_{i \to j} = \sum_{k \in I} (\mathbf{M}_2)_{k \to j} (\mathbf{M}_1)_{i \to k}$。
-/
noncomputable def boundMul {I : Type} [Fintype I] (M₂ M₁ : BoundMatrix I) : BoundMatrix I :=
  fun i j => ∑ k : I, M₂ k j * M₁ i k

@[simp]
theorem boundMul_apply {I : Type} [Fintype I] (M₂ M₁ : BoundMatrix I) (i j : I) :
    boundMul M₂ M₁ i j = ∑ k : I, M₂ k j * M₁ i k :=
  rfl

/--
**显示矩阵乘法对应定理** (`HC02-D03`)：
输入优先复合律 $(\mathbf{M}_2 \mathbf{M}_1)_{i \to j} = \sum_k (\mathbf{M}_2)_{k \to j} (\mathbf{M}_1)_{i \to k}$
与普通行列矩阵（第 `j` 行第 `i` 列为 $M_{i \to j}$）的标准矩阵乘法完全一致。
-/
theorem toDisplayMatrix_boundMul {I : Type} [Fintype I] (M₂ M₁ : BoundMatrix I) :
    toDisplayMatrix (boundMul M₂ M₁) = toDisplayMatrix M₂ * toDisplayMatrix M₁ := by
  ext j i
  simp [toDisplayMatrix, boundMul, Matrix.mul_apply]

theorem boundMul_assoc {I : Type} [Fintype I] (M₃ M₂ M₁ : BoundMatrix I) :
    boundMul (boundMul M₃ M₂) M₁ = boundMul M₃ (boundMul M₂ M₁) := by
  apply displayMatrixEquiv I |>.injective
  change toDisplayMatrix (boundMul (boundMul M₃ M₂) M₁) =
    toDisplayMatrix (boundMul M₃ (boundMul M₂ M₁))
  simp [toDisplayMatrix_boundMul, Matrix.mul_assoc]

/-! ## HC02-D04: 单位矩阵、空乘积和有序乘积 -/

/--
**单位矩阵** $\mathbf{I} = (\delta_{i,j})_{i,j \in I}$ (`HC02-D04`)。
-/
noncomputable def boundId {I : Type} : BoundMatrix I :=
  open Classical in
  fun i j => if i = j then 1 else 0

theorem boundId_diag {I : Type} (i : I) : boundId i i = 1 := by
  simp [boundId]

theorem boundId_offDiag {I : Type} {i j : I} (h : i ≠ j) : boundId i j = 0 := by
  simp [boundId, h]

theorem toDisplayMatrix_boundId {I : Type} [DecidableEq I] :
    toDisplayMatrix (@boundId I) = (1 : Matrix I I ENNReal) := by
  ext j i
  by_cases h : i = j
  · subst h
    simp [toDisplayMatrix, boundId]
  · have hji : j ≠ i := Ne.symm h
    simp [toDisplayMatrix, boundId, h, hji]

theorem boundMul_boundId {I : Type} [Fintype I] (M : BoundMatrix I) :
    boundMul M boundId = M := by
  ext i j
  rw [boundMul_apply, Finset.sum_eq_single i]
  · rw [boundId_diag, mul_one]
  · intro k _ hki
    rw [boundId_offDiag (Ne.symm hki), mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem boundId_boundMul {I : Type} [Fintype I] (M : BoundMatrix I) :
    boundMul boundId M = M := by
  ext i j
  rw [boundMul_apply, Finset.sum_eq_single j]
  · rw [boundId_diag, one_mul]
  · intro k _ hkj
    rw [boundId_offDiag hkj, zero_mul]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/--
**算子链与矩阵链的有序乘积** (`HC02-D04`)：
给定按施行顺序排列的单步矩阵族 `M : Fin k → BoundMatrix I`（对应第 $1, \dots, k$ 步），
定义有序乘积 $\mathbf{M}^{(k)} \cdots \mathbf{M}^{(1)}$：
- 当 $k = 0$ 时为空乘积，等于单位矩阵 `boundId`；
- 当 $k = 1$ 时等于唯一矩阵 `M 0`；
- 当 $k \ge 2$ 时递归左乘最新一步矩阵。
-/
noncomputable def orderedBoundProd {I : Type} [Fintype I] :
    (k : ℕ) → (Fin k → BoundMatrix I) → BoundMatrix I
  | 0, _ => boundId
  | 1, M => M 0
  | k + 2, M => boundMul (M (Fin.last (k + 1))) (orderedBoundProd (k + 1) (Fin.init M))

@[simp]
theorem orderedBoundProd_zero {I : Type} [Fintype I] (M : Fin 0 → BoundMatrix I) :
    orderedBoundProd 0 M = boundId :=
  rfl

@[simp]
theorem orderedBoundProd_one {I : Type} [Fintype I] (M : Fin 1 → BoundMatrix I) :
    orderedBoundProd 1 M = M 0 :=
  rfl

theorem orderedBoundProd_two {I : Type} [Fintype I] (M : Fin 2 → BoundMatrix I) :
    orderedBoundProd 2 M = boundMul (M 1) (M 0) :=
  rfl

theorem orderedBoundProd_succ {I : Type} [Fintype I] (k : ℕ) (M : Fin (k + 1) → BoundMatrix I) :
    orderedBoundProd (k + 1) M = boundMul (M (Fin.last k)) (orderedBoundProd k (Fin.init M)) := by
  cases k with
  | zero =>
      change M 0 = boundMul (M 0) boundId
      exact (boundMul_boundId (M 0)).symm
  | succ n =>
      rfl

/-! ## HC02-D01 & HC02-D02: Lip 矩阵族与 co-Lip 矩阵族 -/

section Definitions

set_option linter.unusedFintypeInType false

/--
OET anchor: h-af85899693cc8750
**定义（全域合法 Lipschitz 矩阵族 $\mathscr{L}(\phi)$）** (`HC02-D01`)：
在有限非空指标集 $I$、扩展伪度量族 $d$ 与算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 下，
$\mathbf{L} \in \mathscr{L}(\phi)$ 当且仅当对所有 $x, y \in \mathrm{dom}(\phi)$ 与 $j \in I$，
$d_j(\phi(x), \phi(y)) \le \sum_{i \in I} L_{i \to j} \cdot d_i(x, y)$。
-/
def LipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) : Set (BoundMatrix I) :=
  { L | ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y }

/--
**定义（子集受限 Lipschitz 矩阵族 $\mathscr{L}(\phi)\big|_U$）** (`HC02-D01`)：
包含域条件 $U \subseteq \mathrm{dom}(\phi)$ 以及在 $U$ 上的点对距离放缩不等式。
-/
def RestrictedLipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  { L | U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y }

/-- 全域 Lip 证书族等于在 $\mathrm{dom}(\phi)$ 上的受限 Lip 证书族 (`HC02-D01`)。 -/
theorem lipSet_eq_restrictedLipSet_dom {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) :
    LipSet d ϕ = RestrictedLipSet d ϕ (dom ϕ) := by
  ext L
  simp [LipSet, RestrictedLipSet]

/--
**定义（子集受限 co-Lipschitz 矩阵族 $\mathscr{K}(\phi)\big|_U$）** (`HC02-D02`)：
显式包含非空性条件 $U \neq \emptyset$、定义域条件 $U \subseteq \mathrm{dom}(\phi)$，
以及对所有 $x, y \in U$ 与 $j \in I$ 的下界不等式
$\sum_{i \in I} K_{i \to j} \cdot d_i(x, y) \le d_j(\phi(x), \phi(y))$。
-/
def RestrictedCoLipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  { K | U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) }

end Definitions

/-! ## HC02-P01 至 HC02-P04: 单分量退化、限制单调性与逐条目下确界 -/

section BasicLipProperties

set_option linter.unusedFintypeInType false

/--
OET anchor: h-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界）** (`HC02-P01`)：
当指标集 $I = \{i\}$ 仅含单一元素 $i$ 时，合法 Lip 矩阵条件等价于标量不等式
$d_i(\phi(x), \phi(y)) \le L_{i \to i} d_i(x, y)$（$\forall x, y \in \mathrm{dom}(\phi)$）。
-/
theorem lipSet_iff_scalar_of_singleton {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (i : I) (hI : ∀ k : I, k = i) (L : BoundMatrix I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  have hsum : ∀ x y : X, (∑ k : I, L k i * d k x y) = L i i * d i x y := by
    intro x y
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      exact False.elim (hki (hI k))
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  constructor
  · intro hL x hx y hy
    simpa [hsum x y] using hL x hx y hy i
  · intro hscalar x hx y hy j
    rw [hI j, hsum x y]
    exact hscalar x hx y hy

/--
**全域 Lip 证书可限制到定义域子集** (`HC02-P02`)：
当 $U \subseteq \mathrm{dom}(\phi)$ 时，$\mathscr{L}(\phi) \subseteq \mathscr{L}(\phi)\big|_U$。
-/
theorem lipSet_subset_restrictedLipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) :
    LipSet d ϕ ⊆ RestrictedLipSet d ϕ U := by
  intro L hL
  exact ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/--
**缩小评估域扩大受限 Lip 证书族** (`HC02-P03`)：
当 $U \subseteq V \subseteq \mathrm{dom}(\phi)$ 时，$\mathscr{L}(\phi)\big|_V \subseteq \mathscr{L}(\phi)\big|_U$。
-/
theorem restrictedLipSet_anti {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedLipSet d ϕ V ⊆ RestrictedLipSet d ϕ U := by
  intro L hL
  exact ⟨Set.Subset.trans hUV hV, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/--
**受限 Lip 证书族的逐条目下确界** (`HC02-P04`)：
$a_{i \to j}(U) := \inf\{M_{i \to j} : \mathbf{M} \in \mathscr{L}(\phi)\big|_U\}$。
-/
noncomputable def restrictedLipEntryInf {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf { v : ENNReal | ∃ M ∈ RestrictedLipSet d ϕ U, M i j = v }

/--
**逐条目下确界随评估域缩小而不增** (`HC02-P04`)：
当 $U \subseteq V$ 时，$a_{i \to j}(U) \le a_{i \to j}(V)$。
-/
theorem restrictedLipEntryInf_mono {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (i j : I) :
    restrictedLipEntryInf d ϕ U i j ≤ restrictedLipEntryInf d ϕ V i j := by
  apply sInf_le_sInf
  rintro v ⟨M, hMV, rfl⟩
  exact ⟨M, restrictedLipSet_anti d ϕ hUV hMV.1 hMV, rfl⟩

end BasicLipProperties

/-! ## HC02-P05, HC02-P06, HC02-P07: 两步复合律与 co-Lip 通道退化判据 -/

section TwoStepComposition

set_option linter.unusedFintypeInType false

/--
OET anchor: h-193cebcc1a7f9259
**命题（Lip 矩阵复合律）** (`HC02-P05`)：
设 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，$U_2 = \phi_1(U_1)$。
若 $\mathbf{L}_1 \in \mathscr{L}(\phi_1)\big|_{U_1}$ 且 $\mathbf{L}_2 \in \mathscr{L}(\phi_2)\big|_{U_2}$，
则 $\mathbf{L}_2 \cdot \mathbf{L}_1 \in \mathscr{L}(\phi_2 \circ \phi_1)\big|_{U_1}$。
-/
theorem restrictedLip_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₂ ϕ₁ : Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (compOp ϕ₂ ϕ₁))
    {L₁ L₂ : BoundMatrix I}
    (hL₁ : L₁ ∈ RestrictedLipSet d ϕ₁ U₁)
    (hL₂ : L₂ ∈ RestrictedLipSet d ϕ₂ (operator_image ϕ₁ U₁)) :
    boundMul L₂ L₁ ∈ RestrictedLipSet d (compOp ϕ₂ ϕ₁) U₁ := by
  refine ⟨hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((compOp ϕ₂ ϕ₁).func x) ((compOp ϕ₂ ϕ₁).func y)
        = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := hL₂.2 _ hx₂ _ hy₂ j
    _ ≤ ∑ k : I, L₂ k j * (∑ i : I, L₁ i k * d i x y) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_right (hL₁.2 x hx y hy k) (L₂ k j)
    _ = ∑ k : I, ∑ i : I, L₂ k j * (L₁ i k * d i x y) := by
          congr 1 with k
          rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, (L₂ k j * L₁ i k) * d i x y := by
          rw [Finset.sum_comm]
          congr 1 with i
          congr 1 with k
          rw [mul_assoc]
    _ = ∑ i : I, boundMul L₂ L₁ i j * d i x y := by
          congr 1 with i
          rw [← Finset.sum_mul, boundMul_apply]

/--
OET anchor: h-88784dcbfff0ea66
**注（co-Lip 通道退化的点对判据）** (`HC02-P06`)：
若存在 $x, y \in \mathrm{dom}(\phi)$ 使 $d_j(\phi(x), \phi(y)) = 0$ 且 $d_i(x, y) > 0$，
则任一全域 co-Lip 矩阵 $\mathbf{K} \in \mathscr{K}(\phi)\big|_{\mathrm{dom}(\phi)}$ 必满足 $K_{i \to j} = 0$。
-/
theorem global_coLip_entry_eq_zero_of_output_zero {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    {i j : I} (hdj : d j (ϕ.func x) (ϕ.func y) = 0) (hdi : 0 < d i x y)
    {K : BoundMatrix I} (hK : K ∈ RestrictedCoLipSet d ϕ (dom ϕ)) :
    K i j = 0 := by
  have hle : K i j * d i x y ≤ 0 := by
    calc
      K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
        Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
      _ = 0 := hdj
  have hmul_zero : K i j * d i x y = 0 := nonpos_iff_eq_zero.mp hle
  rcases mul_eq_zero.mp hmul_zero with hKij | hdi_zero
  · exact hKij
  · exact False.elim ((ne_of_gt hdi) hdi_zero)

/--
OET anchor: h-0f256e6f1d38a612
**命题（co-Lip 矩阵复合律）** (`HC02-P07`)：
设 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，$U_2 = \phi_1(U_1)$。
若 $\mathbf{K}_1 \in \mathscr{K}(\phi_1)\big|_{U_1}$ 且 $\mathbf{K}_2 \in \mathscr{K}(\phi_2)\big|_{U_2}$，
则 $\mathbf{K}_2 \cdot \mathbf{K}_1 \in \mathscr{K}(\phi_2 \circ \phi_1)\big|_{U_1}$（特别地 $U_1$ 非空）。
-/
theorem restrictedCoLip_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₂ ϕ₁ : Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (compOp ϕ₂ ϕ₁))
    {K₁ K₂ : BoundMatrix I}
    (hK₁ : K₁ ∈ RestrictedCoLipSet d ϕ₁ U₁)
    (hK₂ : K₂ ∈ RestrictedCoLipSet d ϕ₂ (operator_image ϕ₁ U₁)) :
    boundMul K₂ K₁ ∈ RestrictedCoLipSet d (compOp ϕ₂ ϕ₁) U₁ ∧ U₁.Nonempty := by
  have hmem : boundMul K₂ K₁ ∈ RestrictedCoLipSet d (compOp ϕ₂ ϕ₁) U₁ := by
    refine ⟨hK₁.1, hU₁, ?_⟩
    intro x hx y hy j
    have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
    have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
    calc
      ∑ i : I, boundMul K₂ K₁ i j * d i x y
          = ∑ i : I, ∑ k : I, (K₂ k j * K₁ i k) * d i x y := by
              congr 1 with i
              rw [boundMul_apply, Finset.sum_mul]
      _ = ∑ k : I, ∑ i : I, K₂ k j * (K₁ i k * d i x y) := by
              rw [Finset.sum_comm]
              congr 1 with k
              congr 1 with i
              rw [mul_assoc]
      _ = ∑ k : I, K₂ k j * (∑ i : I, K₁ i k * d i x y) := by
              congr 1 with k
              rw [Finset.mul_sum]
      _ ≤ ∑ k : I, K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_right (hK₁.2.2 x hx y hy k) (K₂ k j)
      _ ≤ d j ((compOp ϕ₂ ϕ₁).func x) ((compOp ϕ₂ ϕ₁).func y) := hK₂.2.2 _ hx₂ _ hy₂ j
  exact ⟨hmem, hK₁.1⟩

end TwoStepComposition

/-! ## HC02-P08 至 HC02-P11: 两个算子的点对像距扰动界 (`#h-b959b42f25710105`) -/

section PerturbationBounds

set_option linter.unusedFintypeInType false

/--
OET anchor: h-b959b42f25710105 (i-正向)
**命题（正向点对像距扰动）** (`HC02-P08`)：
设 $U \subseteq \mathrm{dom}(\phi_1, \phi_2)$，且对任意 $z \in U, j \in I$ 有
$d_j(\phi_1(z), \phi_2(z)) \le \delta_j$，则对任意 $x, y \in U, j \in I$，
$d_j(\phi_2(x), \phi_2(y)) \le d_j(\phi_1(x), \phi_1(y)) + 2\delta_j$。
-/
theorem pairwise_image_dist_perturb_forward {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (_hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by
  have hsymm_x : d j (ϕ₂.func x) (ϕ₁.func x) ≤ δ j := by
    rw [(hd j).symm (ϕ₂.func x) (ϕ₁.func x)]
    exact hδ x hx j
  have hy_bound : d j (ϕ₁.func y) (ϕ₂.func y) ≤ δ j := hδ y hy j
  calc
    d j (ϕ₂.func x) (ϕ₂.func y)
        ≤ d j (ϕ₂.func x) (ϕ₁.func x) + d j (ϕ₁.func x) (ϕ₂.func y) :=
          (hd j).triangle (ϕ₂.func x) (ϕ₁.func x) (ϕ₂.func y)
    _ ≤ d j (ϕ₂.func x) (ϕ₁.func x) +
          (d j (ϕ₁.func x) (ϕ₁.func y) + d j (ϕ₁.func y) (ϕ₂.func y)) :=
          add_le_add_right ((hd j).triangle (ϕ₁.func x) (ϕ₁.func y) (ϕ₂.func y)) _
    _ ≤ δ j + (d j (ϕ₁.func x) (ϕ₁.func y) + δ j) :=
          add_le_add hsymm_x (add_le_add_right hy_bound _)
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by
          rw [two_mul, add_comm (δ j), add_assoc]

/-- 正向点对像距扰动的加性展开形式 $d_j(\phi_2 x, \phi_2 y) \le d_j(\phi_1 x, \phi_1 y) + \delta_j + \delta_j$ (`HC02-P08`)。 -/
theorem pairwise_image_dist_perturb_forward_add {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
  simpa [two_mul, add_assoc] using
    pairwise_image_dist_perturb_forward d ϕ₁ ϕ₂ hU hδ hx hy j

/--
OET anchor: h-b959b42f25710105 (i-反向)
**命题（反向点对像距扰动）** (`HC02-P09`)：
在相同扰动前提下，$d_j(\phi_1(x), \phi_1(y)) \le d_j(\phi_2(x), \phi_2(y)) + 2\delta_j$。
-/
theorem pairwise_image_dist_perturb_reverse {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by
  have hU_swap : U ⊆ commonDom ϕ₂ ϕ₁ := fun z hz => ⟨(hU hz).2, (hU hz).1⟩
  have hδ_swap : ∀ z ∈ U, ∀ k : I, d k (ϕ₂.func z) (ϕ₁.func z) ≤ δ k := by
    intro z hz k
    rw [(hd k).symm (ϕ₂.func z) (ϕ₁.func z)]
    exact hδ z hz k
  exact pairwise_image_dist_perturb_forward d ϕ₂ ϕ₁ hU_swap hδ_swap hx hy j

/-- 反向点对像距扰动的加性展开形式 $d_j(\phi_1 x, \phi_1 y) \le d_j(\phi_2 x, \phi_2 y) + \delta_j + \delta_j$ (`HC02-P09`)。 -/
theorem pairwise_image_dist_perturb_reverse_add {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := by
  simpa [two_mul, add_assoc] using
    pairwise_image_dist_perturb_reverse d ϕ₁ ϕ₂ hU hδ hx hy j

/--
OET anchor: h-b959b42f25710105 (ii)
**命题（Lip 上界桥接）** (`HC02-P10`)：
若另有 $\mathbf{L}_1 \in \mathscr{L}(\phi_1)\big|_U$，则
$d_j(\phi_2(x), \phi_2(y)) \le \sum_{i \in I} [\mathbf{L}_1]_{i \to j} d_i(x, y) + 2\delta_j$。
-/
theorem perturb_lip_bridge {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₁ : BoundMatrix I} (hL₁ : L₁ ∈ RestrictedLipSet d ϕ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by
  calc
    d j (ϕ₂.func x) (ϕ₂.func y)
        ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j :=
          pairwise_image_dist_perturb_forward d ϕ₁ ϕ₂ hU hδ hx hy j
    _ ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j :=
          add_le_add_left (hL₁.2 x hx y hy j) (2 * δ j)

/-- 交换 $\phi_1, \phi_2$ 后的对称 Lip 上界桥接 (`HC02-P10`)。 -/
theorem perturb_lip_bridge_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₂ : BoundMatrix I} (hL₂ : L₂ ∈ RestrictedLipSet d ϕ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤ (∑ i : I, L₂ i j * d i x y) + 2 * δ j := by
  calc
    d j (ϕ₁.func x) (ϕ₁.func y)
        ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j :=
          pairwise_image_dist_perturb_reverse d ϕ₁ ϕ₂ hU hδ hx hy j
    _ ≤ (∑ i : I, L₂ i j * d i x y) + 2 * δ j :=
          add_le_add_left (hL₂.2 x hx y hy j) (2 * δ j)

/--
OET anchor: h-b959b42f25710105 (iii)
**命题（co-Lip 下界桥接）** (`HC02-P11`)：
若另有 $\mathbf{K}_1 \in \mathscr{K}(\phi_1)\big|_U$，则
$\sum_{i \in I} [\mathbf{K}_1]_{i \to j} d_i(x, y) \le d_j(\phi_2(x), \phi_2(y)) + 2\delta_j$。
-/
theorem perturb_coLip_bridge {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₁ : BoundMatrix I} (hK₁ : K₁ ∈ RestrictedCoLipSet d ϕ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i : I, K₁ i j * d i x y ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by
  calc
    ∑ i : I, K₁ i j * d i x y
        ≤ d j (ϕ₁.func x) (ϕ₁.func y) := hK₁.2.2 x hx y hy j
    _ ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j :=
          pairwise_image_dist_perturb_reverse d ϕ₁ ϕ₂ hU hδ hx hy j

/-- 交换 $\phi_1, \phi_2$ 后的对称 co-Lip 下界桥接 (`HC02-P11`)。 -/
theorem perturb_coLip_bridge_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom ϕ₁ ϕ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₂ : BoundMatrix I} (hK₂ : K₂ ∈ RestrictedCoLipSet d ϕ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i : I, K₂ i j * d i x y ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by
  calc
    ∑ i : I, K₂ i j * d i x y
        ≤ d j (ϕ₂.func x) (ϕ₂.func y) := hK₂.2.2 x hx y hy j
    _ ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j :=
          pairwise_image_dist_perturb_forward d ϕ₁ ϕ₂ hU hδ hx hy j

end PerturbationBounds

/-! ## HC02-D05 & HC02-P12 至 HC02-P15: 实际像域链表示与有限复合局部矩阵界 -/

/--
**有限算子复合 $c_k = \phi_k \circ \cdots \circ \phi_1$** (`HC02-D04`, `HC02-D05`)：
给定按施行顺序排列的 `ϕ : Fin k → Operator X bot`：
- 当 $k = 0$ 时，$c_0 = \mathrm{id}_{\mathcal{X}}$；
- 当 $k = 1$ 时，$c_1 = \phi_0$；
- 当 $k \ge 2$ 时，$c_k = \phi_{k-1} \circ c_{k-1}$。
-/
def chainComp {X : Type} {bot : X} :
    (k : ℕ) → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => idOp
  | 1, ϕ => ϕ 0
  | k + 2, ϕ => compOp (ϕ (Fin.last (k + 1))) (chainComp (k + 1) (Fin.init ϕ))

@[simp]
theorem chainComp_zero {X : Type} {bot : X} (ϕ : Fin 0 → Operator X bot) :
    chainComp 0 ϕ = idOp :=
  rfl

@[simp]
theorem chainComp_one {X : Type} {bot : X} (ϕ : Fin 1 → Operator X bot) :
    chainComp 1 ϕ = ϕ 0 :=
  rfl

theorem chainComp_succ {X : Type} {bot : X} (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) :
    chainComp (k + 1) ϕ = compOp (ϕ (Fin.last k)) (chainComp k (Fin.init ϕ)) := by
  cases k with
  | zero =>
      ext x
      rfl
  | succ n =>
      rfl

/--
**与第1章前置模块 `OperatorChain` 的等价对应定理** (`HC02-D04`, `HC02-D05`)：
施行顺序算子族 `ϕ : Fin k → Operator X bot`（先施行 `ϕ 0`，最后施行 `ϕ (k-1)`）的复合 `chainComp k ϕ`
等于前置模块 `OperatorChain` 作用于逆序列表 `[ϕ_{k-1}, ..., ϕ_0]`。
-/
theorem chainComp_eq_operatorChain {X : Type} {bot : X} :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot),
      chainComp k ϕ = OperatorChain ((List.finRange k).reverse.map ϕ)
  | 0, ϕ => rfl
  | k + 1, ϕ => by
      rw [chainComp_succ, List.finRange_succ_last]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.map_cons, ← List.map_reverse, List.map_map]
      have hfn : ϕ ∘ Fin.castSucc = Fin.init ϕ := rfl
      rw [hfn, OperatorChain]
      ext x
      simp [compOp, chainComp_eq_operatorChain k (Fin.init ϕ)]

/--
**递归定义的实际中间像域 $U_m$** (`HC02-D05`)：
以 $U_1$ 为第 $0$ 阶输入域，并递归定义 $U_{m+1} = \phi_m(U_m)$（`m : Fin k`）。
-/
def chainStageDomain {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U₁ : Set X) : Fin (k + 1) → Set X :=
  Fin.induction U₁ (fun m Um => operator_image (ϕ m) Um)

@[simp]
theorem chainStageDomain_zero {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    chainStageDomain ϕ U₁ 0 = U₁ :=
  rfl

@[simp]
theorem chainStageDomain_succ {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    chainStageDomain ϕ U₁ m.succ = operator_image (ϕ m) (chainStageDomain ϕ U₁ m.castSucc) :=
  rfl

theorem chainStageDomain_castSucc_init {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin (k + 1) → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) :
    chainStageDomain ϕ U₁ m.castSucc = chainStageDomain (Fin.init ϕ) U₁ m := by
  induction m using Fin.induction with
  | zero =>
      simp
  | succ r ih =>
      rw [← Fin.succ_castSucc, chainStageDomain_succ, chainStageDomain_succ, ih]
      rfl

/--
**全复合像等于逐次递归像** (`HC02-D05`)：
$U_{k+1} = c_k(U_1)$。
-/
theorem chainStageDomain_last_eq_image {X : Type} {bot : X} :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X),
      chainStageDomain ϕ U₁ (Fin.last k) = operator_image (chainComp k ϕ) U₁
  | 0, ϕ, U₁ => by
      change chainStageDomain ϕ U₁ 0 = id '' U₁
      simp
  | k + 1, ϕ, U₁ => by
      rw [← Fin.succ_last k, chainStageDomain_succ, chainStageDomain_castSucc_init,
        chainStageDomain_last_eq_image k (Fin.init ϕ) U₁, chainComp_succ]
      simp [operator_image, compOp, Set.image_image]

/--
**由 $U_1 \subseteq \mathrm{dom}(c_k)$ 推出每一步实际输入域满足 $U_m \subseteq \mathrm{dom}(\phi_m)$** (`HC02-D05`)。
-/
theorem chainStageDomain_subset_dom {X : Type} {bot : X} :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) {U₁ : Set X}
      (_hU₁ : U₁ ⊆ dom (chainComp k ϕ)) (m : Fin k),
      chainStageDomain ϕ U₁ m.castSucc ⊆ dom (ϕ m)
  | 0, _, _, _, m => Fin.elim0 m
  | k + 1, ϕ, U₁, hU₁, m => by
      rw [chainComp_succ] at hU₁
      have hU₁_init : U₁ ⊆ dom (chainComp k (Fin.init ϕ)) :=
        Set.Subset.trans hU₁ (dom_compOp_subset_left _ _)
      induction m using Fin.lastCases with
      | last =>
          rw [chainStageDomain_castSucc_init, chainStageDomain_last_eq_image]
          exact image_subset_dom_of_subset_dom_compOp _ _ hU₁
      | cast r =>
          have hr := chainStageDomain_subset_dom k (Fin.init ϕ) hU₁_init r
          have hdom_eq : chainStageDomain ϕ U₁ r.castSucc.castSucc =
              chainStageDomain (Fin.init ϕ) U₁ r.castSucc :=
            chainStageDomain_castSucc_init ϕ U₁ r.castSucc
          rw [hdom_eq]
          exact hr

section ChainCertificates

set_option linter.unusedFintypeInType false

/--
**逐步局部 Lip 证书链数据** (`HC02-D05`)：
仅记录起始定义域条件 $U_1 \subseteq \mathrm{dom}(c_k)$、单步矩阵序列 $\mathbf{L}^{(m)}$，
以及每一步在实际输入域 $U_m$ 上的局部 Lip 合法性；**不包含**最终复合算子的界作为字段。
-/
structure LipChainData {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) where
  domain_valid : U₁ ⊆ dom (chainComp k ϕ)
  stepMatrix : Fin k → BoundMatrix I
  step_valid : ∀ m : Fin k,
    stepMatrix m ∈ RestrictedLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc)

/--
**逐步局部 co-Lip 证书链数据** (`HC02-D05`)：
仅记录起始定义域条件 $U_1 \subseteq \mathrm{dom}(c_k)$、单步矩阵序列 $\mathbf{K}^{(m)}$，
以及每一步在实际输入域 $U_m$ 上的局部 co-Lip 合法性（含非空性）；**不包含**最终复合界字段。
-/
structure CoLipChainData {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) where
  domain_valid : U₁ ⊆ dom (chainComp k ϕ)
  stepMatrix : Fin k → BoundMatrix I
  step_valid : ∀ m : Fin k,
    stepMatrix m ∈ RestrictedCoLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc)

/--
OET anchor: h-c80171fa685dc795 (i)
**推论（有限复合的局部 Lip 矩阵界，$k \ge 1$）** (`HC02-P12`)：
若 $U_1 \subseteq \mathrm{dom}(c_k)$，且每一步矩阵 $\mathbf{L}^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$，
则有序乘积 $\mathbf{L}^{(k)} \cdots \mathbf{L}^{(1)} \in \mathscr{L}(c_k)\big|_{U_1}$。
-/
theorem chain_restrictedLip_prod {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)] :
    ∀ (k : ℕ) (_hk : 1 ≤ k) (ϕ : Fin k → Operator X bot) (U₁ : Set X)
      (_hU₁ : U₁ ⊆ dom (chainComp k ϕ)) (L : Fin k → BoundMatrix I)
      (_hL : ∀ m : Fin k, L m ∈ RestrictedLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc)),
      orderedBoundProd k L ∈ RestrictedLipSet d (chainComp k ϕ) U₁
  | 0, hk, _, _, _, _, _ => by omega
  | 1, _, ϕ, U₁, _, L, hL => by
      simpa using hL 0
  | n + 2, _, ϕ, U₁, hU₁, L, hL => by
      rw [chainComp_succ] at hU₁ ⊢
      rw [orderedBoundProd_succ]
      have hU₁_init : U₁ ⊆ dom (chainComp (n + 1) (Fin.init ϕ)) :=
        Set.Subset.trans hU₁ (dom_compOp_subset_left _ _)
      have hL_init : ∀ m : Fin (n + 1),
          Fin.init L m ∈ RestrictedLipSet d (Fin.init ϕ m)
            (chainStageDomain (Fin.init ϕ) U₁ m.castSucc) := by
        intro m
        have hm := hL m.castSucc
        rwa [chainStageDomain_castSucc_init] at hm
      have ih := chain_restrictedLip_prod d (n + 1) (by omega) (Fin.init ϕ) U₁ hU₁_init
        (Fin.init L) hL_init
      have hlast := hL (Fin.last (n + 1))
      rw [chainStageDomain_castSucc_init, chainStageDomain_last_eq_image] at hlast
      exact restrictedLip_comp d (ϕ (Fin.last (n + 1))) (chainComp (n + 1) (Fin.init ϕ)) U₁
        hU₁ ih hlast

/-- 基于 `LipChainData` 结构的有限复合 Lip 证书推论 (`HC02-D05`, `HC02-P12`)。 -/
theorem LipChainData.composite_mem_restrictedLipSet
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {k : ℕ} (hk : 1 ≤ k) {ϕ : Fin k → Operator X bot} {U₁ : Set X}
    (chain : LipChainData d k ϕ U₁) :
    orderedBoundProd k chain.stepMatrix ∈ RestrictedLipSet d (chainComp k ϕ) U₁ :=
  chain_restrictedLip_prod d k hk ϕ U₁ chain.domain_valid chain.stepMatrix chain.step_valid

/--
OET anchor: h-c80171fa685dc795 (ii)
**推论（有限复合的局部 co-Lip 矩阵界，$k \ge 1$）** (`HC02-P13`)：
若 $U_1 \subseteq \mathrm{dom}(c_k)$，且每一步矩阵 $\mathbf{K}^{(m)} \in \mathscr{K}(\phi_m)\big|_{U_m}$
（包含各步定义域非空性），则 $\mathbf{K}^{(k)} \cdots \mathbf{K}^{(1)} \in \mathscr{K}(c_k)\big|_{U_1}$。
-/
theorem chain_restrictedCoLip_prod {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)] :
    ∀ (k : ℕ) (_hk : 1 ≤ k) (ϕ : Fin k → Operator X bot) (U₁ : Set X)
      (_hU₁ : U₁ ⊆ dom (chainComp k ϕ)) (K : Fin k → BoundMatrix I)
      (_hK : ∀ m : Fin k, K m ∈ RestrictedCoLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc)),
      orderedBoundProd k K ∈ RestrictedCoLipSet d (chainComp k ϕ) U₁
  | 0, hk, _, _, _, _, _ => by omega
  | 1, _, ϕ, U₁, _, K, hK => by
      simpa using hK 0
  | n + 2, _, ϕ, U₁, hU₁, K, hK => by
      rw [chainComp_succ] at hU₁ ⊢
      rw [orderedBoundProd_succ]
      have hU₁_init : U₁ ⊆ dom (chainComp (n + 1) (Fin.init ϕ)) :=
        Set.Subset.trans hU₁ (dom_compOp_subset_left _ _)
      have hK_init : ∀ m : Fin (n + 1),
          Fin.init K m ∈ RestrictedCoLipSet d (Fin.init ϕ m)
            (chainStageDomain (Fin.init ϕ) U₁ m.castSucc) := by
        intro m
        have hm := hK m.castSucc
        rwa [chainStageDomain_castSucc_init] at hm
      have ih := chain_restrictedCoLip_prod d (n + 1) (by omega) (Fin.init ϕ) U₁ hU₁_init
        (Fin.init K) hK_init
      have hlast := hK (Fin.last (n + 1))
      rw [chainStageDomain_castSucc_init, chainStageDomain_last_eq_image] at hlast
      exact (restrictedCoLip_comp d (ϕ (Fin.last (n + 1))) (chainComp (n + 1) (Fin.init ϕ)) U₁
        hU₁ ih hlast).1

/-- 基于 `CoLipChainData` 结构的有限复合 co-Lip 证书推论 (`HC02-D05`, `HC02-P13`)。 -/
theorem CoLipChainData.composite_mem_restrictedCoLipSet
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {k : ℕ} (hk : 1 ≤ k) {ϕ : Fin k → Operator X bot} {U₁ : Set X}
    (chain : CoLipChainData d k ϕ U₁) :
    orderedBoundProd k chain.stepMatrix ∈ RestrictedCoLipSet d (chainComp k ϕ) U₁ :=
  chain_restrictedCoLip_prod d k hk ϕ U₁ chain.domain_valid chain.stepMatrix chain.step_valid

/-- 单位矩阵对距离的求和恒等式：$\sum_{i \in I} \mathbf{I}_{i \to j} d_i(x, y) = d_j(x, y)$。 -/
theorem sum_boundId_mul_dist {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    ∑ i : I, boundId i j * d i x y = d j x y := by
  rw [Finset.sum_eq_single j]
  · rw [boundId_diag, one_mul]
  · intro i _ hij
    rw [boundId_offDiag hij, zero_mul]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/--
OET anchor: h-11006ddd8c43bfec (Lip)
**注（零步复合的单位矩阵 Lip 证书）** (`HC02-P14`)：
当 $k = 0$ 时，$c_0 = \mathrm{id}_{\mathcal{X}}$，空乘积为单位矩阵 $\mathbf{I}$；
对任意非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$，$\mathbf{I} \in \mathscr{L}(\mathrm{id}_{\mathcal{X}})\big|_U$。
-/
theorem zero_step_boundId_mem_restrictedLipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (_hUne : U.Nonempty) (hU : U ⊆ dom (@idOp X bot))
    (ϕ : Fin 0 → Operator X bot := Fin.elim0)
    (L : Fin 0 → BoundMatrix I := Fin.elim0) :
    orderedBoundProd 0 L ∈ RestrictedLipSet d (chainComp 0 ϕ) U ∧
      boundId ∈ RestrictedLipSet d (@idOp X bot) U := by
  have hmem : boundId ∈ RestrictedLipSet d (@idOp X bot) U := by
    refine ⟨hU, ?_⟩
    intro x _ y _ j
    rw [sum_boundId_mul_dist]
    exact le_rfl
  exact ⟨hmem, hmem⟩

/--
OET anchor: h-11006ddd8c43bfec (co-Lip)
**注（零步复合的单位矩阵 co-Lip 证书）** (`HC02-P15`)：
对同一非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$，$\mathbf{I} \in \mathscr{K}(\mathrm{id}_{\mathcal{X}})\big|_U$。
-/
theorem zero_step_boundId_mem_restrictedCoLipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hUne : U.Nonempty) (hU : U ⊆ dom (@idOp X bot))
    (ϕ : Fin 0 → Operator X bot := Fin.elim0)
    (K : Fin 0 → BoundMatrix I := Fin.elim0) :
    orderedBoundProd 0 K ∈ RestrictedCoLipSet d (chainComp 0 ϕ) U ∧
      boundId ∈ RestrictedCoLipSet d (@idOp X bot) U := by
  have hmem : boundId ∈ RestrictedCoLipSet d (@idOp X bot) U := by
    refine ⟨hUne, hU, ?_⟩
    intro x _ y _ j
    rw [sum_boundId_mul_dist]
    exact le_rfl
  exact ⟨hmem, hmem⟩

end ChainCertificates

/-! ## HC02-D06, HC02-P16, HC02-P17: 有限索引路径及乘积零值/正值判据 -/

/--
**长度为 $n$（$n \ge 1$）的中间指标序列空间** (`HC02-D06`)：
记录中间指标 $(k_1, \dots, k_{n-1}) \in I^{n-1}$，不施加任何正性约束。
当 $n = 1$ 时，`Fin 0 → I` 具有唯一元素（唯一空中间序列）。
-/
abbrev IntermPath (I : Type) (n : ℕ) : Type := Fin (n - 1) → I

/-- 当 $n = 1$ 时，中间指标序列空间具有唯一空序列 (`HC02-D06`)。 -/
instance instUniqueIntermPathOne (I : Type) : Unique (IntermPath I 1) :=
  inferInstanceAs (Unique (Fin 0 → I))

/--
**完整路径节点序列 $(k_0, k_1, \dots, k_n)$** (`HC02-D06`)：
固定起点 $k_0 = i$、终点 $k_n = j$，中间节点由 `p : IntermPath I n` 给出。
-/
def pathVertex {I : Type} {n : ℕ} (_hn : 1 ≤ n) (i j : I)
    (p : IntermPath I n) (r : Fin (n + 1)) : I :=
  if h0 : r.val = 0 then
    i
  else if hlast : r.val = n then
    j
  else
    p ⟨r.val - 1, by omega⟩

@[simp]
theorem pathVertex_zero {I : Type} {n : ℕ} (hn : 1 ≤ n) (i j : I) (p : IntermPath I n) :
    pathVertex hn i j p 0 = i := by
  simp [pathVertex]

@[simp]
theorem pathVertex_last {I : Type} {n : ℕ} (hn : 1 ≤ n) (i j : I) (p : IntermPath I n) :
    pathVertex hn i j p (Fin.last n) = j := by
  have hne : n ≠ 0 := by omega
  simp [pathVertex, hne]

theorem pathVertex_interm {I : Type} {n : ℕ} (hn : 1 ≤ n) (i j : I)
    (p : IntermPath I n) (t : Fin (n - 1)) :
    pathVertex hn i j p ⟨t.val + 1, by omega⟩ = p t := by
  have hnen : t.val + 1 ≠ n := by omega
  simp [pathVertex, hnen]

/--
**路径在第 `m` 步（$m \in \{1, \dots, n\}$）的边条目** $[\mathbf{M}^{(m)}]_{k_{m-1} \to k_m}$ (`HC02-D06`)。
-/
def pathEdge {I : Type} {n : ℕ} (M : Fin n → BoundMatrix I) (hn : 1 ≤ n)
    (i j : I) (p : IntermPath I n) (m : Fin n) : ENNReal :=
  M m (pathVertex hn i j p m.castSucc) (pathVertex hn i j p m.succ)

/--
**路径权重（各层边条目的乘积）** (`HC02-D06`)：
$\prod_{m=1}^n [\mathbf{M}^{(m)}]_{k_{m-1} \to k_m}$。
-/
noncomputable def pathWeight {I : Type} {n : ℕ} (M : Fin n → BoundMatrix I) (hn : 1 ≤ n)
    (i j : I) (p : IntermPath I n) : ENNReal :=
  ∏ m : Fin n, pathEdge M hn i j p m

/-- **全正路径谓词**：沿路径的所有单步矩阵条目均严格正 (`HC02-D06`)。 -/
def PathAllPos {I : Type} {n : ℕ} (M : Fin n → BoundMatrix I) (hn : 1 ≤ n)
    (i j : I) (p : IntermPath I n) : Prop :=
  ∀ m : Fin n, 0 < pathEdge M hn i j p m

/-- **含零路径谓词**：沿路径存在至少一个层级单步矩阵条目为 $0$ (`HC02-D06`)。 -/
def PathHasZero {I : Type} {n : ℕ} (M : Fin n → BoundMatrix I) (hn : 1 ≤ n)
    (i j : I) (p : IntermPath I n) : Prop :=
  ∃ m : Fin n, pathEdge M hn i j p m = 0

/-- 当 $n = 1$ 时，唯一空中间序列的路径边即为 $[\mathbf{M}^{(1)}]_{i \to j}$ (`HC02-D06`)。 -/
@[simp]
theorem pathEdge_one {I : Type} (M : Fin 1 → BoundMatrix I) (i j : I)
    (p : IntermPath I 1) :
    pathEdge M le_rfl i j p 0 = M 0 i j := by
  simp [pathEdge]
  rfl

@[simp]
theorem pathWeight_one {I : Type} (M : Fin 1 → BoundMatrix I) (i j : I)
    (p : IntermPath I 1) :
    pathWeight M le_rfl i j p = M 0 i j := by
  simp [pathWeight]

/--
**矩阵连乘条目的完整路径展开公式** (`HC02-D06`)：
对任意 $n \ge 1$，
$[\mathbf{M}^{(n)} \cdots \mathbf{M}^{(1)}]_{i \to j} = \sum_{p \in I^{n-1}} \mathrm{pathWeight}(p)$。
-/
theorem orderedBoundProd_eq_sum_paths {I : Type} [Fintype I] :
    ∀ (n : ℕ) (hn : 1 ≤ n) (M : Fin n → BoundMatrix I) (i j : I),
      orderedBoundProd n M i j = ∑ p : IntermPath I n, pathWeight M hn i j p
  | 0, hn, _, _, _ => by omega
  | 1, hn, M, i, j => by
      rw [orderedBoundProd_one, Fintype.sum_unique]
      exact (pathWeight_one M i j default).symm
  | m + 2, hn, M, i, j => by
      have hm1 : 1 ≤ m + 1 := by omega
      rw [orderedBoundProd_succ, boundMul_apply]
      have ih : ∀ k : I, orderedBoundProd (m + 1) (Fin.init M) i k =
          ∑ q : IntermPath I (m + 1), pathWeight (Fin.init M) hm1 i k q :=
        fun k => orderedBoundProd_eq_sum_paths (m + 1) hm1 (Fin.init M) i k
      simp_rw [ih, Finset.mul_sum]
      -- 将 (k : I) × (Fin m → I) 与 IntermPath I (m + 2) = (Fin (m + 1) → I) 通过 Fin.snoc 建立双射
      let e : I × (Fin m → I) ≃ (Fin (m + 1) → I) :=
        Fin.snocEquiv fun _ : Fin (m + 1) => I
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv e _ _ ?_
      rintro ⟨k, q⟩
      change M (Fin.last (m + 1)) k j * pathWeight (Fin.init M) hm1 i k q =
        pathWeight M hn i j (Fin.snoc q k)
      unfold pathWeight
      have hlast_edge :
          pathEdge M hn i j (Fin.snoc q k) (Fin.last (m + 1)) = M (Fin.last (m + 1)) k j := by
        simp only [pathEdge]
        have hv1 : pathVertex hn i j (Fin.snoc q k) (Fin.last (m + 1)).castSucc = k := by
          simp [pathVertex, Fin.snoc]
        have hv2 : pathVertex hn i j (Fin.snoc q k) (Fin.last (m + 1)).succ = j := by
          have hlast_eq : (Fin.last (m + 1)).succ = Fin.last (m + 2) := rfl
          rw [hlast_eq, pathVertex_last]
        rw [hv1, hv2]
      have hinit_prod :
          (∏ r : Fin (m + 1), pathEdge (Fin.init M) hm1 i k q r) =
            ∏ r : Fin (m + 1), pathEdge M hn i j (Fin.snoc q k) r.castSucc := by
        refine Finset.prod_congr rfl ?_
        intro r _
        simp only [pathEdge, Fin.init]
        have hv1 : pathVertex hm1 i k q r.castSucc =
            pathVertex hn i j (Fin.snoc q k) r.castSucc.castSucc := by
          by_cases hr0 : r.val = 0
          · simp [pathVertex, hr0]
          · have hr_lt1 : r.val < m + 1 := r.isLt
            have hne1 : r.val ≠ m + 1 := by omega
            have hne2 : r.val ≠ m + 2 := by omega
            have hlt : r.val - 1 < m := by omega
            simp [pathVertex, hr0, hne1, hne2, Fin.snoc, hlt]
        have hv2 : pathVertex hm1 i k q r.succ =
            pathVertex hn i j (Fin.snoc q k) r.castSucc.succ := by
          by_cases hrs_last : r.val + 1 = m + 1
          · simp [pathVertex, hrs_last, Fin.snoc]
          · have hr_lt1 : r.val < m + 1 := r.isLt
            have hlt : r.val < m := by omega
            have hr_ne_m : r.val ≠ m := by omega
            have hr_ne_m1 : r.val ≠ m + 1 := by omega
            simp [pathVertex, Fin.snoc, hlt, hr_ne_m, hr_ne_m1]
            rfl
        rw [hv1, hv2]
      rw [Fin.prod_univ_castSucc (f := fun r => pathEdge M hn i j (Fin.snoc q k) r),
        hlast_edge, ← hinit_prod, mul_comm]

/-- 路径权重为 $0$ 当且仅当该路径含零边。 -/
theorem pathWeight_eq_zero_iff {I : Type} {n : ℕ} (M : Fin n → BoundMatrix I)
    (hn : 1 ≤ n) (i j : I) (p : IntermPath I n) :
    pathWeight M hn i j p = 0 ↔ PathHasZero M hn i j p := by
  unfold pathWeight PathHasZero
  rw [Finset.prod_eq_zero_iff]
  simp

/-- 路径权重严格正（$> 0$）当且仅当该路径全正。 -/
theorem pathWeight_pos_iff {I : Type} {n : ℕ} (M : Fin n → BoundMatrix I)
    (hn : 1 ≤ n) (i j : I) (p : IntermPath I n) :
    0 < pathWeight M hn i j p ↔ PathAllPos M hn i j p := by
  simp only [pos_iff_ne_zero, ne_eq, pathWeight_eq_zero_iff, PathHasZero, PathAllPos, not_exists]

section PathCriteria

set_option linter.unusedFintypeInType false

/--
OET anchor: h-e4154c34e95d3c23 (i)
**命题（Lip 乘积条目的零值判据）** (`HC02-P16`)：
对于任意非空有限复合 $c_n = \phi_n \circ \cdots \circ \phi_1$（$n \ge 1$），设 $U_1 \subseteq \mathrm{dom}(c_n)$，
递归定义 $U_{m+1} = \phi_m(U_m)$，并取局部证书 $\mathbf{L}^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$。
则 $[\mathbf{L}^{(n)} \cdots \mathbf{L}^{(1)}]_{i \to j} = 0$ 当且仅当每条完整中间指标序列均含至少一个零条目。
-/
theorem lip_chain_prod_eq_zero_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {n : ℕ} (hn : 1 ≤ n) (ϕ : Fin n → Operator X bot) {U₁ : Set X}
    (_hU₁ : U₁ ⊆ dom (chainComp n ϕ)) (L : Fin n → BoundMatrix I)
    (_hL : ∀ m : Fin n, L m ∈ RestrictedLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc))
    (i j : I) :
    orderedBoundProd n L i j = 0 ↔ ∀ p : IntermPath I n, PathHasZero L hn i j p := by
  rw [orderedBoundProd_eq_sum_paths n hn L i j, Finset.sum_eq_zero_iff]
  constructor
  · intro h p
    exact (pathWeight_eq_zero_iff L hn i j p).mp (h p (Finset.mem_univ p))
  · intro h p _
    exact (pathWeight_eq_zero_iff L hn i j p).mpr (h p)

/-- 当 $n = 1$ 时，Lip 乘积零值判据退化为单个矩阵条目 $[\mathbf{L}^{(1)}]_{i \to j} = 0$ (`HC02-P16`)。 -/
theorem lip_chain_prod_eq_zero_iff_one {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Fin 1 → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainComp 1 ϕ)) (L : Fin 1 → BoundMatrix I)
    (hL : ∀ m : Fin 1, L m ∈ RestrictedLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc))
    (i j : I) :
    (orderedBoundProd 1 L i j = 0 ↔ L 0 i j = 0) ∧
      ((∀ p : IntermPath I 1, PathHasZero L le_rfl i j p) ↔ L 0 i j = 0) := by
  have hchain := lip_chain_prod_eq_zero_iff d le_rfl ϕ hU₁ L hL i j
  have hp : orderedBoundProd 1 L i j = L 0 i j := rfl
  exact ⟨by rw [hp], hchain.symm.trans (by rw [hp])⟩

/--
OET anchor: h-e4154c34e95d3c23 (ii)
**命题（co-Lip 乘积条目的正值判据）** (`HC02-P17`)：
在同一非空有限复合链及局部证书 $\mathbf{K}^{(m)} \in \mathscr{K}(\phi_m)\big|_{U_m}$ 条件下，
$[\mathbf{K}^{(n)} \cdots \mathbf{K}^{(1)}]_{i \to j} > 0$ 当且仅当存在至少一条完整中间指标序列，
使得沿该路径的所有单步矩阵条目均严格正。
-/
theorem coLip_chain_prod_pos_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {n : ℕ} (hn : 1 ≤ n) (ϕ : Fin n → Operator X bot) {U₁ : Set X}
    (_hU₁ : U₁ ⊆ dom (chainComp n ϕ)) (K : Fin n → BoundMatrix I)
    (_hK : ∀ m : Fin n, K m ∈ RestrictedCoLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc))
    (i j : I) :
    0 < orderedBoundProd n K i j ↔ ∃ p : IntermPath I n, PathAllPos K hn i j p := by
  rw [orderedBoundProd_eq_sum_paths n hn K i j, pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff]
  simp only [not_forall, Finset.mem_univ, true_implies, ← pos_iff_ne_zero, pathWeight_pos_iff]

/-- 当 $n = 1$ 时，唯一空中间序列的正值判据退化为 $[\mathbf{K}^{(1)}]_{i \to j} > 0$ (`HC02-P17`)。 -/
theorem coLip_chain_prod_pos_iff_one {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Fin 1 → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainComp 1 ϕ)) (K : Fin 1 → BoundMatrix I)
    (hK : ∀ m : Fin 1, K m ∈ RestrictedCoLipSet d (ϕ m) (chainStageDomain ϕ U₁ m.castSucc))
    (i j : I) :
    (0 < orderedBoundProd 1 K i j ↔ 0 < K 0 i j) ∧
      ((∃ p : IntermPath I 1, PathAllPos K le_rfl i j p) ↔ 0 < K 0 i j) := by
  have hchain := coLip_chain_prod_pos_iff d le_rfl ϕ hU₁ K hK i j
  have hp : orderedBoundProd 1 K i j = K 0 i j := rfl
  exact ⟨by rw [hp], hchain.symm.trans (by rw [hp])⟩

end PathCriteria

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=OperatorBounds/ChannelBounds.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic
import OperatorBounds.MatrixBounds

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-!
# 第2章 算子界 — §2.2 分量解耦与通道分辨保持 (`#h-7fa97eb6e24d5527`)

本模块形式化第2章第二节的全部定义、反例与命题证明义务（`HC02-D07`、`HC02-D08`，
`HC02-P18` 至 `HC02-P32`）。
-/

/-! ## HC02-D07: 分量通道、单行/单列稀疏、行/列解耦与对角体系 -/

/--
**分量通道** (`HC02-D07`)：
序对 `(i, j) : I × I` 表示从输入分量伪度量 $d_i$ 到输出分量伪度量 $d_j$ 的一个分量通道。
-/
abbrev Channel (I : Type) : Type := I × I

/--
**单行稀疏谓词** $\mathrm{Row}(\mathbf{L}, i, j)$ (`HC02-D07`)：
固定输出指标（第 $j$ 行），除输入位置 $i$ 外其余条目全为 $0$（$\forall k \neq i,\, L_{k \to j} = 0$）。
-/
def IsRowSparseAt {I : Type} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/--
**矩阵第 $j$ 行至多一项非零** (`HC02-D07`)：$\exists i \in I,\, \mathrm{Row}(\mathbf{L}, i, j)$。
-/
def IsRowDecoupledMatrix {I : Type} (L : BoundMatrix I) (j : I) : Prop :=
  ∃ i : I, IsRowSparseAt L i j

/--
**单列稀疏谓词** $\mathrm{Col}(\mathbf{L}, i, j)$ (`HC02-D07`)：
固定输入指标（第 $i$ 列），除输出位置 $j$ 外其余条目全为 $0$（$\forall k \neq j,\, L_{i \to k} = 0$）。
-/
def IsColSparseAt {I : Type} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/--
**矩阵第 $i$ 列至多一项非零** (`HC02-D07`)：$\exists j \in I,\, \mathrm{Col}(\mathbf{L}, i, j)$。
-/
def IsColDecoupledMatrix {I : Type} (L : BoundMatrix I) (i : I) : Prop :=
  ∃ j : I, IsColSparseAt L i j

/--
**对角矩阵谓词** (`HC02-D07`)：所有非对角条目均为 $0$（$\forall i \neq j,\, L_{i \to j} = 0$）。
-/
def IsDiagonalBound {I : Type} (L : BoundMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

theorem forall_isRowSparseAt_diag_iff_isDiagonalBound {I : Type} (L : BoundMatrix I) :
    (∀ j : I, IsRowSparseAt L j j) ↔ IsDiagonalBound L := by
  constructor
  · intro h i j hij
    exact h j i hij
  · intro h j i hij
    exact h i j hij

section DecouplingDefinitions

set_option linter.unusedFintypeInType false

/--
**定义（关于输出分量 $d_j$ 的行解耦）** (`HC02-D07`)：
存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 及 $i \in I$，使得 $\forall k \neq i,\, L_{k \to j} = 0$。
-/
def IsRowDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, ∃ i : I, IsRowSparseAt L i j

/--
**定义（关于输入分量 $d_i$ 的列解耦）** (`HC02-D07`)：
存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 及 $j \in I$，使得 $\forall k \neq j,\, L_{i \to k} = 0$。
-/
def IsColDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, ∃ j : I, IsColSparseAt L i j

/--
**定义（完全解耦体系证书）** (`HC02-D07`)：
上界证书 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 为对角矩阵。
-/
def IsCompletelyDecoupledCert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I) : Prop :=
  L ∈ RestrictedLipSet d ϕ U ∧ IsDiagonalBound L

end DecouplingDefinitions

/-! ## HC02-D08 & HC02-P18 至 HC02-P24: 单通道 Lip 常数及其性质与反例 -/

section SingleChannelConstants

set_option linter.unusedFintypeInType false

/--
**定义（单通道可行标量族 $\mathcal{S}_{i \to j}(\phi; U)$）** (`HC02-D08`)：
对 $U \subseteq \mathrm{dom}(\phi)$，收集所有满足单分量点对放缩不等式
$d_j(\phi(x), \phi(y)) \le \lambda \cdot d_i(x, y)$（$\forall x, y \in U$）的常数 $\lambda \in \bar{\mathbb{R}}_+$。
-/
def ChannelFeasibleScalars {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { lam : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y }

/--
**定义（单通道 Lip 常数 $\underline{L}_{i \to j}(\phi; U)$）** (`HC02-D08`)：
定义为可行标量族 $\mathcal{S}_{i \to j}(\phi; U)$ 的下确界 `sInf`（空集下确界为 $\top = +\infty$），
不与任何多分量 Lip 矩阵的条目相混淆。
-/
noncomputable def channelLipConst {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (ChannelFeasibleScalars d ϕ U i j)

/-- 当可行标量集合为空时，按约定 $\inf \emptyset = +\infty$ (`HC02-D08`)。 -/
theorem channelLipConst_of_empty {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hempty : ChannelFeasibleScalars d ϕ U i j = ∅) :
    channelLipConst d ϕ U i j = ⊤ := by
  simp [channelLipConst, hempty]

/--
**标量可行族向上封闭** (`HC02-P20`)：
若 $\lambda_0 \in \mathcal{S}_{i \to j}(\phi; U)$ 且 $\lambda_1 \ge \lambda_0$，
则 $\lambda_1 \in \mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem channelFeasibleScalars_upward_closed {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {lam₀ lam₁ : ENNReal}
    (h₀ : lam₀ ∈ ChannelFeasibleScalars d ϕ U i j) (hle : lam₀ ≤ lam₁) :
    lam₁ ∈ ChannelFeasibleScalars d ϕ U i j := by
  intro x hx y hy
  exact le_trans (h₀ x hx y hy) (mul_le_mul_left hle (d i x y))

/--
**零输入距而正输出距使可行标量族为空且单通道常数为 $+\infty$** (`HC02-P18`)：
若存在 $x, y \in U$ 使 $d_i(x, y) = 0$ 且 $d_j(\phi(x), \phi(y)) > 0$，
则不存在任何 $\lambda \in \bar{\mathbb{R}}_+$（含 $+\infty$）满足标量界，
故 $\mathcal{S}_{i \to j}(\phi; U) = \emptyset$ 且 $\underline{L}_{i \to j}(\phi; U) = +\infty$。
-/
theorem channelFeasibleScalars_empty_of_zero_input_pos_output
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hdi : d i x y = 0) (hdj : 0 < d j (ϕ.func x) (ϕ.func y)) :
    ChannelFeasibleScalars d ϕ U i j = ∅ ∧ channelLipConst d ϕ U i j = ⊤ := by
  have hempty : ChannelFeasibleScalars d ϕ U i j = ∅ := by
    ext lam
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hlam
    have hle := hlam x hx y hy
    rw [hdi, mul_zero] at hle
    exact (not_le_of_gt hdj) hle
  exact ⟨hempty, channelLipConst_of_empty d ϕ U i j hempty⟩

/--
**正有限下确界以上的每个常数均可行** (`HC02-P21`)：
记 $a = \underline{L}_{i \to j}(\phi; U)$。当 $0 < a < +\infty$ 时，
任意 $\lambda > a$（允许 $\lambda = +\infty$）均属于 $\mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem mem_channelFeasibleScalars_of_gt_inf
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (_hpos : 0 < channelLipConst d ϕ U i j)
    (_hfin : channelLipConst d ϕ U i j < ⊤)
    {lam : ENNReal} (hgt : channelLipConst d ϕ U i j < lam) :
    lam ∈ ChannelFeasibleScalars d ϕ U i j := by
  rcases sInf_lt_iff.mp hgt with ⟨lam₀, hlam₀_mem, hlam₀_lt⟩
  exact channelFeasibleScalars_upward_closed d ϕ hU hlam₀_mem (le_of_lt hlam₀_lt)

/--
**正有限最优单通道下确界可被取到** (`HC02-P19`)：
当 $0 < \underline{L}_{i \to j}(\phi; U) < +\infty$ 时，
$\underline{L}_{i \to j}(\phi; U) \in \mathcal{S}_{i \to j}(\phi; U)$，即对任意 $x, y \in U$ 成立
$d_j(\phi(x), \phi(y)) \le \underline{L}_{i \to j}(\phi; U) \cdot d_i(x, y)$。
-/
theorem channelLipConst_mem_of_pos_of_lt_top
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (hpos : 0 < channelLipConst d ϕ U i j)
    (hfin : channelLipConst d ϕ U i j < ⊤) :
    channelLipConst d ϕ U i j ∈ ChannelFeasibleScalars d ϕ U i j ∧
      ∀ x ∈ U, ∀ y ∈ U,
        d j (ϕ.func x) (ϕ.func y) ≤ channelLipConst d ϕ U i j * d i x y := by
  have hmem : channelLipConst d ϕ U i j ∈ ChannelFeasibleScalars d ϕ U i j := by
    set a := channelLipConst d ϕ U i j
    have ha_gt : a < a + 1 := ENNReal.lt_add_right hfin.ne one_ne_zero
    have ha1_mem : a + 1 ∈ ChannelFeasibleScalars d ϕ U i j :=
      mem_channelFeasibleScalars_of_gt_inf d ϕ hU hpos hfin ha_gt
    intro x hx y hy
    set A := d j (ϕ.func x) (ϕ.func y)
    set B := d i x y
    by_cases hB0 : B = 0
    · -- B = 0 情形
      have hA_le : A ≤ 0 := by
        have h := ha1_mem x hx y hy
        simpa [A, B, hB0] using h
      rw [hB0, mul_zero]
      exact hA_le
    · by_cases hBtop : B = ⊤
      · -- B = +∞ 情形：由 a > 0 知 a * ⊤ = ⊤
        rw [hBtop, ENNReal.mul_top hpos.ne']
        exact le_top
      · -- 0 < B < +∞ 情形
        have ha1_lt_top : a + 1 < ⊤ := ENNReal.add_lt_top.mpr ⟨hfin, ENNReal.one_lt_top⟩
        have hA_lt_top : A < ⊤ :=
          lt_of_le_of_lt (ha1_mem x hx y hy) (ENNReal.mul_lt_top ha1_lt_top (lt_top_iff_ne_top.mpr hBtop))
        have hA_ne_top : A ≠ ⊤ := hA_lt_top.ne
        have ha_ne_top : a ≠ ⊤ := hfin.ne
        -- 化为有限非负实数 NNReal 验证反证法
        set a' : NNReal := a.toNNReal
        set b' : NNReal := B.toNNReal
        set A' : NNReal := A.toNNReal
        have ha_coe : (a' : ENNReal) = a := ENNReal.coe_toNNReal ha_ne_top
        have hB_coe : (b' : ENNReal) = B := ENNReal.coe_toNNReal hBtop
        have hA_coe : (A' : ENNReal) = A := ENNReal.coe_toNNReal hA_ne_top
        have hb'_pos : 0 < b' := by
          rw [← ENNReal.coe_pos, hB_coe]
          exact pos_iff_ne_zero.mpr hB0
        rw [← hA_coe, ← ha_coe, ← hB_coe, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
        by_contra hnot
        have hlt : a' * b' < A' := lt_of_not_ge hnot
        have ha'_lt_div : a' < A' / b' := (lt_div_iff₀ hb'_pos).mpr hlt
        rcases exists_between ha'_lt_div with ⟨c, hac, hcdiv⟩
        have hcb : c * b' < A' := (lt_div_iff₀ hb'_pos).mp hcdiv
        have hlam_gt : a < (c : ENNReal) := by
          rw [← ha_coe, ENNReal.coe_lt_coe]
          exact hac
        have hc_mem : (c : ENNReal) ∈ ChannelFeasibleScalars d ϕ U i j :=
          mem_channelFeasibleScalars_of_gt_inf d ϕ hU hpos hfin hlam_gt
        have hA_le_cb : A ≤ (c : ENNReal) * B := hc_mem x hx y hy
        rw [← hA_coe, ← hB_coe, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at hA_le_cb
        exact (not_le_of_gt hcb) hA_le_cb
  exact ⟨hmem, hmem⟩

/--
OET anchor: h-57de7918859a9de2 (零下确界正有限常数分支)
**注（零下确界给出所有有限正常数界）** (`HC02-P22`)：
当 $\underline{L}_{i \to j}(\phi; U) = 0$ 时，任意满足 $0 < \lambda < +\infty$ 的常数 $\lambda$
均属于 $\mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem mem_channelFeasibleScalars_of_inf_eq_zero
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (hzero : channelLipConst d ϕ U i j = 0)
    {lam : ENNReal} (hpos : 0 < lam) (_hfin : lam < ⊤) :
    lam ∈ ChannelFeasibleScalars d ϕ U i j := by
  have hgt : channelLipConst d ϕ U i j < lam := by
    rwa [hzero]
  rcases sInf_lt_iff.mp hgt with ⟨lam₀, hlam₀_mem, hlam₀_lt⟩
  exact channelFeasibleScalars_upward_closed d ϕ hU hlam₀_mem (le_of_lt hlam₀_lt)

/--
OET anchor: h-57de7918859a9de2 (有限性等价判据)
**注（单通道下确界有限当且仅当存在有限可行常数）** (`HC02-P24`)：
$\underline{L}_{i \to j}(\phi; U) < +\infty$ 当且仅当存在有限常数 $\lambda < +\infty$，
使对所有 $x, y \in U$ 有 $d_j(\phi(x), \phi(y)) \le \lambda \cdot d_i(x, y)$。
-/
theorem channelLipConst_lt_top_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) (i j : I) :
    channelLipConst d ϕ U i j < ⊤ ↔
      ∃ lam : ENNReal, lam < ⊤ ∧
        ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y := by
  constructor
  · intro hfin
    by_cases hzero : channelLipConst d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact mem_channelFeasibleScalars_of_inf_eq_zero d ϕ hU hzero zero_lt_one ENNReal.one_lt_top
    · refine ⟨channelLipConst d ϕ U i j, hfin, ?_⟩
      exact (channelLipConst_mem_of_pos_of_lt_top d ϕ hU
        (pos_iff_ne_zero.mpr hzero) hfin).1
  · rintro ⟨lam, hlam_lt, hlam_mem⟩
    exact lt_of_le_of_lt (sInf_le hlam_mem) hlam_lt

end SingleChannelConstants

/-! ### HC02-P23: 零下确界未必由 $0$ 实现的显式反例构造 -/

namespace ZeroInfCounterexample

/-- 反例底层空间的四个点：`0` 为吸收元，`1, 2, 3` 为非吸收点。 -/
abbrev CX : Type := Fin 4

/-- 反例底层吸收元 $\bot = 0$。 -/
def cbot : CX := 0

/-- 反例单分量伪度量族（指标集 `Unit`）：仅 `{2, 3}` 之间距离为 `1`，其余异点距离全为 `⊤`。 -/
def cd (_ : Unit) (x y : CX) : ENNReal :=
  if x = y then 0
  else if (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) then 1
  else ⊤

instance instExtendedPseudoMetricCounterexample (u : Unit) :
    ExtendedPseudoMetric CX cbot (cd u) where
  nonabsorbing := ⟨1, by decide⟩
  dist_self x := by simp [cd]
  symm x y := by
    fin_cases x <;> fin_cases y <;> rfl
  triangle x y z := by
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [cd]
  isolate_bot x hx := by
    fin_cases x
    · exact False.elim (hx rfl)
    · rfl
    · rfl
    · rfl

/-- 反例算子 $\phi$：保吸收元 `0 ↦ 0`，并把距离为 `⊤` 的点对 `(1, 2)` 映到距离为 `1` 的点对 `(2, 3)`。 -/
def cphi : Operator CX cbot where
  func x :=
    match x with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 2
    | ⟨2, _⟩ => 3
    | ⟨3, _⟩ => 3
  preserves_bot := rfl

/-- 反例非空评估域 $U = \{1, 2\} \subseteq \mathrm{dom}(\phi)$。 -/
def cU : Set CX := {1, 2}

theorem cU_nonempty : cU.Nonempty := ⟨1, by simp [cU]⟩

theorem cU_subset_dom : cU ⊆ dom cphi := by
  intro x hx
  rcases hx with rfl | rfl
  · change cphi.func 1 ≠ cbot
    decide
  · change cphi.func 2 ≠ cbot
    decide

theorem pos_mem_cFeasible {lam : ENNReal} (hpos : 0 < lam) :
    lam ∈ ChannelFeasibleScalars cd cphi cU () () := by
  intro x hx y hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp [cphi, cd]
  · have htop : cd () 1 2 = ⊤ := rfl
    have hout : cd () (cphi.func 1) (cphi.func 2) = 1 := rfl
    rw [htop, hout, ENNReal.mul_top hpos.ne']
    exact le_top
  · have htop : cd () 2 1 = ⊤ := rfl
    have hout : cd () (cphi.func 2) (cphi.func 1) = 1 := rfl
    rw [htop, hout, ENNReal.mul_top hpos.ne']
    exact le_top
  · simp [cphi, cd]

theorem cChannelLipConst_eq_zero :
    channelLipConst cd cphi cU () () = 0 := by
  apply le_antisymm _ (zero_le _)
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  exact sInf_le (pos_mem_cFeasible hc)

theorem zero_not_mem_cFeasible :
    (0 : ENNReal) ∉ ChannelFeasibleScalars cd cphi cU () () := by
  intro h0
  have hle := h0 1 (by simp [cU]) 2 (by simp [cU])
  have htop : cd () 1 2 = ⊤ := rfl
  have hout : cd () (cphi.func 1) (cphi.func 2) = 1 := rfl
  rw [htop, hout, zero_mul] at hle
  exact (not_le_of_gt zero_lt_one) hle

end ZeroInfCounterexample

/--
OET anchor: h-57de7918859a9de2 (零下确界不可达反例)
**反例（零下确界未必由 $\lambda = 0$ 实现）** (`HC02-P23`)：
存在合法扩展规范空间、合法算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 及非空子集 $U \subseteq \mathrm{dom}(\phi)$，
使得 $\underline{L}_{i \to j}(\phi; U) = 0$，但 $\lambda = 0 \notin \mathcal{S}_{i \to j}(\phi; U)$
（即 $0$ 不满足相应单通道标量上界）。
-/
theorem exists_zero_channelLipConst_not_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ k : I, ExtendedPseudoMetric X bot (d k))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
      channelLipConst d ϕ U i j = 0 ∧
      (0 : ENNReal) ∉ ChannelFeasibleScalars d ϕ U i j := by
  refine ⟨ZeroInfCounterexample.CX, Unit, ZeroInfCounterexample.cbot,
    inferInstance, inferInstance, ZeroInfCounterexample.cd,
    ZeroInfCounterexample.instExtendedPseudoMetricCounterexample,
    ZeroInfCounterexample.cphi, ZeroInfCounterexample.cU, (), (),
    ZeroInfCounterexample.cU_nonempty, ZeroInfCounterexample.cU_subset_dom,
    ZeroInfCounterexample.cChannelLipConst_eq_zero,
    ZeroInfCounterexample.zero_not_mem_cFeasible⟩

/-! ## HC02-P25 至 HC02-P32: 通道隔离、行列解耦、标量双侧界与可分辨保持 -/

section ChannelAndDistinguishability

set_option linter.unusedFintypeInType false

/--
**零系数移除该上界证书中的输入求和项** (`HC02-P25`)：
当 $L_{i \to j} = 0$ 时，无论 $d_i(x, y)$ 取何值（包括 $d_i(x, y) = +\infty$），
恒有 $L_{i \to j} \cdot d_i(x, y) = 0$，故输出 $d_j$ 的上界求和可直接删去 $i$-项。
-/
theorem zero_entry_removes_channel_term {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I} {i j : I}
    (hzero : L i j = 0) :
    open Classical in
    (∀ x y : X, L i j * d i x y = 0) ∧
      (∀ x y : X, (∑ k : I, L k j * d k x y) =
        ∑ k ∈ Finset.univ.erase i, L k j * d k x y) ∧
      (L ∈ RestrictedLipSet d ϕ U →
        ∀ x ∈ U, ∀ y ∈ U,
          d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y) := by
  classical
  have hterm : ∀ x y : X, L i j * d i x y = 0 := by
    intro x y
    rw [hzero, zero_mul]
  have hsum : ∀ x y : X, (∑ k : I, L k j * d k x y) =
      ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
    intro x y
    rw [← Finset.add_sum_erase Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i),
      hterm x y, zero_add]
  refine ⟨hterm, hsum, ?_⟩
  intro hL x hx y hy
  rw [← hsum x y]
  exact hL.2 x hx y hy j

/--
**任意唯一输入位置的单行化简** (`HC02-P26`)：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 且第 $j$ 行除输入 $i$ 外全为 $0$（$i$ 不必等于 $j$），
则对所有 $x, y \in U$，$d_j(\phi(x), \phi(y)) \le L_{i \to j} \cdot d_i(x, y)$。
-/
theorem restrictedLip_of_isRowSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) {i j : I} (hrow : IsRowSparseAt L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [hrow k hki, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [← hsum]
  exact hL.2 x hx y hy j

/--
**任意单列支撑的证书贡献范围** (`HC02-P27`)：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 的第 $i$ 列仅输出 $j$ 可能非零（`IsColSparseAt L i j`），
则对任意异于 $j$ 的输出分量 $k \neq j$，输入项 $L_{i \to k} d_i(x, y) = 0$，
且 $d_k(\phi(x), \phi(y))$ 的该证书上界不依赖输入分量 $d_i$。
-/
theorem restrictedLip_of_isColSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) {i j : I} (hcol : IsColSparseAt L i j) :
    open Classical in
    ∀ k : I, k ≠ j →
      (∀ x y : X, L i k * d i x y = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U,
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y) := by
  classical
  intro k hkj
  have hk_zero := zero_entry_removes_channel_term d ϕ (U := U) (L := L) (i := i) (j := k) (hcol k hkj)
  exact ⟨hk_zero.1, hk_zero.2.2 hL⟩

/--
**完全解耦（对角 Lip 矩阵）给出所有分量的独立标量放缩上界** (`HC02-P28`)：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 为对角矩阵，则对所有 $j \in I$ 与 $x, y \in U$，
$d_j(\phi(x), \phi(y)) \le L_{j \to j} \cdot d_j(x, y)$。
-/
theorem restrictedLip_of_isDiagonalBound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hdiag : IsDiagonalBound L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact restrictedLip_of_isRowSparseAt d ϕ hL (fun k hkj => hdiag k j hkj)

/--
OET anchor: h-6a98a58b5bc95360
**引理（对角输入项的标量双侧界）** (`HC02-P29`)：
给定 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 与 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$，
仅要求 $\mathbf{L}$ 在第 $j$ 行满足 $L_{k \to j} = 0$（$\forall k \neq j$，不对 $\mathbf{K}$ 施加稀疏假设），
即可对任意 $x, y \in U$ 得到
$K_{j \to j} \cdot d_j(x, y) \le d_j(\phi(x), \phi(y)) \le L_{j \to j} \cdot d_j(x, y)$。
-/
theorem diagonal_row_scalar_two_sided_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L K : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hK : K ∈ RestrictedCoLipSet d ϕ U)
    {j : I} (hrow : IsRowSparseAt L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, restrictedLip_of_isRowSparseAt d ϕ hL hrow x hx y hy⟩
  calc
    K j j * d j x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ j)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
**逐分量标量双侧界（全分量对角输入行条件）** (`HC02-P30`)：
若对所有 $j \in I$ 均满足 $L_{k \to j} = 0$（$\forall k \neq j$），则全部分量的标量双侧界同时成立。
-/
theorem componentwise_scalar_two_sided_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L K : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hK : K ∈ RestrictedCoLipSet d ϕ U)
    (hrows : ∀ j : I, IsRowSparseAt L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact diagonal_row_scalar_two_sided_bound d ϕ hL hK (hrows j)

/--
**有限标量双侧放缩界（含有限对角系数分支）** (`HC02-P30`)：
若进一步要求对所有 $j \in I$ 有 $L_{j \to j}, K_{j \to j} < +\infty$，
则存在有限非负实数标量族 $\kappa, \ell : I \to \mathbb{R}_{\ge 0}$，给出逐分量的有限标量双侧放缩界。
-/
theorem componentwise_finite_scalar_two_sided_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L K : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hK : K ∈ RestrictedCoLipSet d ϕ U)
    (hrows : ∀ j : I, IsRowSparseAt L j j)
    (hL_fin : ∀ j : I, L j j < ⊤) (hK_fin : ∀ j : I, K j j < ⊤) :
    ∃ (κ ℓ : I → NNReal),
      (∀ j : I, (κ j : ENNReal) = K j j ∧ (ℓ j : ENNReal) = L j j) ∧
      ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
        (κ j : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ (ℓ j : ENNReal) * d j x y := by
  refine ⟨fun j => (K j j).toNNReal, fun j => (L j j).toNNReal, ?_, ?_⟩
  · intro j
    exact ⟨ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne⟩
  · intro j x hx y hy
    rw [ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne]
    exact componentwise_scalar_two_sided_bound d ϕ hL hK hrows j x hx y hy

/--
**单行化简证书与单通道 Lip 常数的比较关系** (`HC02-D08`, `HC02-P26`)：
仅当 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 在第 $j$ 行关于输入 $i$ 单行稀疏时，
其条目 $L_{i \to j}$ 才构成单通道可行常数并满足 $\underline{L}_{i \to j}(\phi; U) \le L_{i \to j}$。
-/
theorem channelLipConst_le_of_isRowSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) {i j : I} (hrow : IsRowSparseAt L i j) :
    channelLipConst d ϕ U i j ≤ L i j :=
  sInf_le (restrictedLip_of_isRowSparseAt d ϕ hL hrow)

/--
**正 co-Lip 条目给出的单通道正下界传递** (`HC02-P31`，对应正文 311 行)：
若 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且 $K_{i \to j} > 0$，则该证书给出从输入分量 $d_i$
到输出分量 $d_j$ 的正系数下界 $K_{i \to j} \cdot d_i(x, y) \le d_j(\phi(x), \phi(y))$。
-/
theorem pos_coLip_channel_lower_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {K : BoundMatrix I}
    (hK : K ∈ RestrictedCoLipSet d ϕ U) {i j : I} (hKij : 0 < K i j) :
    0 < K i j ∧ ∀ x ∈ U, ∀ y ∈ U, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  refine ⟨hKij, fun x hx y hy => ?_⟩
  calc
    K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
OET anchor: h-f82672ec0dd48f28 (i)
**命题（正 co-Lip 通道的可分辨保持）** (`HC02-P31`)：
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若 $K_{i \to j} > 0$，则对任意 $x, y \in U$，
$d_i(x, y) > 0 \implies d_j(\phi(x), \phi(y)) > 0$。
-/
theorem pos_coLip_preserves_distinguishability {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {K : BoundMatrix I}
    (hK : K ∈ RestrictedCoLipSet d ϕ U) {i j : I} (hKij : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdi
  have hprod_pos : 0 < K i j * d i x y :=
    ENNReal.mul_pos hKij.ne' hdi.ne'
  have hle := (pos_coLip_channel_lower_bound d ϕ hK hKij).2 x hx y hy
  exact lt_of_lt_of_le hprod_pos hle

/--
OET anchor: h-f82672ec0dd48f28 (ii)
**命题（正对角 co-Lip 反射族零距关系）** (`HC02-P32`)：
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若对所有 $j \in I$ 均有 $K_{j \to j} > 0$，
则对任意 $x, y \in U$，$\phi(x) \sim_{\mathcal{G}} \phi(y) \implies x \sim_{\mathcal{G}} y$。
-/
theorem coLip_reflects_gaugeZeroRelated {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {K : BoundMatrix I}
    (hK : K ∈ RestrictedCoLipSet d ϕ U) (hdiag_pos : ∀ j : I, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_coLip_preserves_distinguishability d ϕ hK (hdiag_pos j) x hx y hy hpos
  exact hout_pos.ne' (hrel j)

end ChannelAndDistinguishability

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=Main.lean
import OperatorBounds.MatrixBounds
import OperatorBounds.ChannelBounds

/-!
# 第2章 算子界 (`HCH02`) — 主入口模块

本文件导入第2章全部目标形式化模块：
- `OperatorBounds.MatrixBounds`（§2.1 矩阵界与有限复合：`HC02-D01` 至 `HC02-D06`，`HC02-P01` 至 `HC02-P17`）
- `OperatorBounds.ChannelBounds`（§2.2 分量解耦与通道分辨保持：`HC02-D07`、`HC02-D08`，`HC02-P18` 至 `HC02-P32`）
-/
```

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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipSet"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.RestrictedLipSet"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipSet_eq_restrictedLipSet_dom"
        }
      ],
      "representation": "在有限非空指标集 [Fintype I] [Nonempty I]、扩展伪度量族 [∀ i : I, ExtendedPseudoMetric X bot (d i)] 与保吸收元算子 ϕ : Operator X bot 下，定义全域合法 Lip 矩阵集合 LipSet d ϕ : Set (BoundMatrix I) 与子集受限 Lip 矩阵集合 RestrictedLipSet d ϕ U : Set (BoundMatrix I)，其中系数与距离均取值于 ENNReal，RestrictedLipSet 包含 U ⊆ dom ϕ 及 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y，并证明 LipSet d ϕ = RestrictedLipSet d ϕ (dom ϕ)。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.RestrictedCoLipSet"
        }
      ],
      "representation": "在相同扩展规范空间与算子语境下，定义受限 co-Lip 矩阵证书集合 RestrictedCoLipSet d ϕ U : Set (BoundMatrix I)，显式包含非空性 U.Nonempty、定义域包含 U ⊆ dom ϕ 以及 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, ∑ i : I, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)；矩阵条目取值于 ENNReal，0 与 ⊤（+∞）均为合法系数。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.BoundMatrix"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ofDisplayMatrix"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.displayMatrixEquiv"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.boundMul"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_boundMul"
        }
      ],
      "representation": "以 BoundMatrix I := I → I → ENNReal 采用输入优先存储，M i j 表示输入分量 i 到输出分量 j 的条目 M_{i→j}；通过 toDisplayMatrix M j i = M i j 及双射 displayMatrixEquiv 与普通行列矩阵 Matrix I I ENNReal（第 j 行第 i 列为 M_{i→j}）建立精确对应；定义复合乘法 boundMul M₂ M₁ i j = ∑ k : I, M₂ k j * M₁ i k，并由 toDisplayMatrix_boundMul 证明其与显示矩阵标准乘法完全一致。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.boundId"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.boundId_diag"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.boundId_offDiag"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedBoundProd"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedBoundProd_zero"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedBoundProd_one"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedBoundProd_succ"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainComp"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainComp_eq_operatorChain"
        }
      ],
      "representation": "定义 Kronecker 单位矩阵 boundId（对角为 1、非对角为 0）；对按施行顺序索引的序列 Fin k → Operator X bot 与 Fin k → BoundMatrix I（0 到 k-1 对应原文第 1 到 k 步），定义复合算子 chainComp（并证明与前置模块 OperatorChain 逆序列表复合等价）和有序矩阵乘积 orderedBoundProd：k=0 时为空乘积等于 boundId，k=1 时等于唯一矩阵 M 0，k+1 时等于 boundMul (M (Fin.last k)) (orderedBoundProd k (Fin.init M))，即 L^{(k)}⋯L^{(1)}。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainStageDomain"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainStageDomain_zero"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainStageDomain_succ"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainStageDomain_last_eq_image"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainStageDomain_subset_dom"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipChainData"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipChainData"
        }
      ],
      "representation": "通过 Fin.induction 定义实际中间像域族 chainStageDomain ϕ U₁ : Fin (k + 1) → Set X，满足初值 U₁ 及递推 U_{m+1} = operator_image (ϕ m) U_m；由 chainStageDomain_subset_dom 在 U₁ ⊆ dom (chainComp k ϕ) 下证明每步实际输入域均满足 U_m ⊆ dom (ϕ m)，由 chainStageDomain_last_eq_image 证明全复合像 operator_image (chainComp k ϕ) U₁ 等于最终逐次像；结构 LipChainData 与 CoLipChainData 仅存储起始域条件、逐步矩阵序列及各步在实际输入域 U_m 上的局部界，不含最终复合算子界字段。",
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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IntermPath"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.instUniqueIntermPathOne"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathVertex"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathEdge"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathAllPos"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathHasZero"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedBoundProd_eq_sum_paths"
        }
      ],
      "representation": "对 1 ≤ n，定义无任何正性约束的中间指标序列类型 IntermPath I n := Fin (n - 1) → I（n=1 时由 instUniqueIntermPathOne 给出唯一空中间序列）；由 pathVertex 固定首尾指标 k_0 = i、k_n = j，pathEdge 提取第 m 步边条目 [M^{(m)}]_{k_{m-1}→k_m}，pathWeight 定义各层边条目的乘积；定义全正谓词 PathAllPos（∀ m, 0 < pathEdge）与含零谓词 PathHasZero（∃ m, pathEdge = 0），并证明矩阵连乘条目等于遍历全部中间路径的权重和 orderedBoundProd_eq_sum_paths。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.Channel"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowSparseAt"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowDecoupledMatrix"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowDecoupled"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColSparseAt"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColDecoupledMatrix"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColDecoupled"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagonalBound"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCompletelyDecoupledCert"
        }
      ],
      "representation": "定义分量通道类型 Channel I := I × I；单行稀疏谓词 IsRowSparseAt L i j := ∀ k ≠ i, L k j = 0，矩阵行解耦 IsRowDecoupledMatrix L j := ∃ i, IsRowSparseAt L i j 及算子行解耦 IsRowDecoupled d ϕ U j := ∃ L ∈ RestrictedLipSet d ϕ U, ∃ i, IsRowSparseAt L i j；单列稀疏谓词 IsColSparseAt L i j := ∀ k ≠ j, L i k = 0，矩阵列解耦 IsColDecoupledMatrix L i := ∃ j, IsColSparseAt L i j 及算子列解耦 IsColDecoupled d ϕ U i；对角谓词 IsDiagonalBound L := ∀ i j, i ≠ j → L i j = 0 及完全解耦证书谓词 IsCompletelyDecoupledCert。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ChannelFeasibleScalars"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelLipConst"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelLipConst_of_empty"
        }
      ],
      "representation": "定义单通道可行标量集合 ChannelFeasibleScalars d ϕ U i j := {lam : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y} 及其下确界 channelLipConst d ϕ U i j := sInf (ChannelFeasibleScalars d ϕ U i j)，由 channelLipConst_of_empty 确认空集下确界为 ⊤（+∞），独立于任何多分量 Lip 矩阵条目。",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipSet_iff_scalar_of_singleton"
        }
      ],
      "representation": "当指标集满足 ∀ k : I, k = i（即 I = {i}）时，证明 L ∈ LipSet d ϕ 当且仅当 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y。",
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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipSet_subset_restrictedLipSet"
        }
      ],
      "representation": "证明当 U ⊆ dom ϕ 时，全域合法 Lip 证书族包含于受限证书族：LipSet d ϕ ⊆ RestrictedLipSet d ϕ U。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipSet_anti"
        }
      ],
      "representation": "证明当 U ⊆ V 且 V ⊆ dom ϕ 时，缩小评估域扩大受限 Lip 证书族：RestrictedLipSet d ϕ V ⊆ RestrictedLipSet d ϕ U。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipEntryInf"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipEntryInf_mono"
        }
      ],
      "representation": "定义受限 Lip 矩阵族的逐条目下确界 restrictedLipEntryInf d ϕ U i j := sInf {v | ∃ M ∈ RestrictedLipSet d ϕ U, M i j = v}，并证明当 U ⊆ V 时 restrictedLipEntryInf d ϕ U i j ≤ restrictedLipEntryInf d ϕ V i j。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-P03"
      ]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLip_comp"
        }
      ],
      "representation": "对复合算子 compOp ϕ₂ ϕ₁、起始子集 U₁ ⊆ dom (compOp ϕ₂ ϕ₁) 及实际像集 U₂ = operator_image ϕ₁ U₁，证明若 L₁ ∈ RestrictedLipSet d ϕ₁ U₁ 且 L₂ ∈ RestrictedLipSet d ϕ₂ U₂，则 boundMul L₂ L₁ ∈ RestrictedLipSet d (compOp ϕ₂ ϕ₁) U₁。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.global_coLip_entry_eq_zero_of_output_zero"
        }
      ],
      "representation": "证明若存在 x, y ∈ dom ϕ 使得 d j (ϕ.func x) (ϕ.func y) = 0 且 0 < d i x y，则任一全域 co-Lip 矩阵 K ∈ RestrictedCoLipSet d ϕ (dom ϕ) 必满足 K i j = 0。",
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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedCoLip_comp"
        }
      ],
      "representation": "在与 HC02-P05 相同的 U₁ ⊆ dom (compOp ϕ₂ ϕ₁) 与实际像域 operator_image ϕ₁ U₁ 下，证明若 K₁ ∈ RestrictedCoLipSet d ϕ₁ U₁ 且 K₂ ∈ RestrictedCoLipSet d ϕ₂ (operator_image ϕ₁ U₁)，则 boundMul K₂ K₁ ∈ RestrictedCoLipSet d (compOp ϕ₂ ϕ₁) U₁ 且 U₁.Nonempty。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_forward"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_forward_add"
        }
      ],
      "representation": "设 U ⊆ commonDom ϕ₁ ϕ₂（即 dom ϕ₁ ∩ dom ϕ₂），且 ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j，对任意 x, y ∈ U 与 j : I，同时证明 2*δ_j 形式与 δ_j + δ_j 展开形式的正向像距扰动不等式 d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_reverse"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_reverse_add"
        }
      ],
      "representation": "在与 HC02-P08 完全相同的扰动前提下，利用伪度量对称性调用正向扰动界，对任意 x, y ∈ U 与 j : I 证明反向像距扰动不等式 d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j（及 + δ j + δ j 形式）。",
      "dependencies": [
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturb_lip_bridge"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturb_lip_bridge_symm"
        }
      ],
      "representation": "在扰动前提及 L₁ ∈ RestrictedLipSet d ϕ₁ U 下，对任意 x, y ∈ U 与 j : I 证明 d j (ϕ₂.func x) (ϕ₂.func y) ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j，并同时给出交换 ϕ₁, ϕ₂ 后的对称桥接结论 perturb_lip_bridge_symm。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-P08",
        "HC02-P09"
      ]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturb_coLip_bridge"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturb_coLip_bridge_symm"
        }
      ],
      "representation": "在扰动前提及 K₁ ∈ RestrictedCoLipSet d ϕ₁ U 下，对任意 x, y ∈ U 与 j : I 证明 ∑ i : I, K₁ i j * d i x y ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j，并给出交换 ϕ₁, ϕ₂ 后的对称桥接结论 perturb_coLip_bridge_symm。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-P08",
        "HC02-P09"
      ]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chain_restrictedLip_prod"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipChainData.composite_mem_restrictedLipSet"
        }
      ],
      "representation": "对任意长度 1 ≤ k 的算子链 ϕ : Fin k → Operator X bot、起始域 U₁ ⊆ dom (chainComp k ϕ) 及每步在实际中间像域 chainStageDomain ϕ U₁ m.castSucc 上合法的局部证书 L m ∈ RestrictedLipSet d (ϕ m) U_m，通过对 HC02-P05 有限归纳证明 orderedBoundProd k L ∈ RestrictedLipSet d (chainComp k ϕ) U₁（同时给出展开形式与 LipChainData 封装形式）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chain_restrictedCoLip_prod"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipChainData.composite_mem_restrictedCoLipSet"
        }
      ],
      "representation": "对任意长度 1 ≤ k 的算子链，在 U₁ ⊆ dom (chainComp k ϕ) 及每步局部 co-Lip 证书 K m ∈ RestrictedCoLipSet d (ϕ m) U_m（含非空性义务）条件下，通过对 HC02-P07 有限归纳证明 orderedBoundProd k K ∈ RestrictedCoLipSet d (chainComp k ϕ) U₁。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_boundId_mem_restrictedLipSet"
        }
      ],
      "representation": "在零步边界 k = 0（chainComp 0 ϕ = idOp，orderedBoundProd 0 L = boundId）下，对任意非空子集 U.Nonempty 且 U ⊆ dom idOp，证明单位矩阵 boundId ∈ RestrictedLipSet d idOp U。",
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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_boundId_mem_restrictedCoLipSet"
        }
      ],
      "representation": "在同一零步边界 k = 0 及非空子集 U.Nonempty、U ⊆ dom idOp 条件下，证明同一单位矩阵满足 boundId ∈ RestrictedCoLipSet d idOp U。",
      "dependencies": [
        "HC02-D02",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_chain_prod_eq_zero_iff"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_chain_prod_eq_zero_iff_one"
        }
      ],
      "representation": "在非空有限复合链 1 ≤ n、U₁ ⊆ dom (chainComp n ϕ) 及实际局部证书序列 L m ∈ RestrictedLipSet d (ϕ m) U_m 条件下，证明 orderedBoundProd n L i j = 0 ↔ ∀ p : IntermPath I n, PathHasZero L hn i j p，并由 lip_chain_prod_eq_zero_iff_one 证明 n = 1 时退化为单条目条件 L 0 i j = 0。",
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
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_chain_prod_pos_iff"
        },
        {
          "file": "OperatorBounds/MatrixBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_chain_prod_pos_iff_one"
        }
      ],
      "representation": "在同一非空有限复合链 1 ≤ n、U₁ ⊆ dom (chainComp n ϕ) 及实际局部证书序列 K m ∈ RestrictedCoLipSet d (ϕ m) U_m 条件下，证明 0 < orderedBoundProd n K i j ↔ ∃ p : IntermPath I n, PathAllPos K hn i j p，并由 coLip_chain_prod_pos_iff_one 证明 n = 1 时唯一空中间序列对应 0 < K 0 i j。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelFeasibleScalars_empty_of_zero_input_pos_output"
        }
      ],
      "representation": "在 U ⊆ dom ϕ 下，若存在 x, y ∈ U 使得 d i x y = 0 且 0 < d j (ϕ.func x) (ϕ.func y)，利用 ENNReal 中含 ⊤ * 0 = 0 的乘法性质证明 ChannelFeasibleScalars d ϕ U i j = ∅ 且 channelLipConst d ϕ U i j = ⊤。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelLipConst_mem_of_pos_of_lt_top"
        }
      ],
      "representation": "在 U ⊆ dom ϕ 且 0 < channelLipConst d ϕ U i j < ⊤ 条件下，按正文分 B=0、B=⊤ 与 0<B<⊤ 三种情形证明下确界可被取到：channelLipConst d ϕ U i j ∈ ChannelFeasibleScalars d ϕ U i j，即全部点对 x, y ∈ U 满足标量上界。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelFeasibleScalars_upward_closed"
        }
      ],
      "representation": "证明单通道可行标量集合向上封闭：若 lam₀ ∈ ChannelFeasibleScalars d ϕ U i j 且 lam₀ ≤ lam₁，则 lam₁ ∈ ChannelFeasibleScalars d ϕ U i j。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_channelFeasibleScalars_of_gt_inf"
        }
      ],
      "representation": "在 U ⊆ dom ϕ 及 0 < channelLipConst d ϕ U i j < ⊤ 语境下，对任意严格大于下确界的常数 lam（含 lam = ⊤），由下确界定义与向上封闭性 HC02-P20 证明 lam ∈ ChannelFeasibleScalars d ϕ U i j。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_channelFeasibleScalars_of_inf_eq_zero"
        }
      ],
      "representation": "在 U ⊆ dom ϕ 且 channelLipConst d ϕ U i j = 0 时，对任意满足 0 < lam < ⊤ 的有限正常数 lam，由下确界性质与 HC02-P20 证明 lam ∈ ChannelFeasibleScalars d ϕ U i j。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.exists_zero_channelLipConst_not_attained"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ZeroInfCounterexample.instExtendedPseudoMetricCounterexample"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ZeroInfCounterexample.cChannelLipConst_eq_zero"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ZeroInfCounterexample.zero_not_mem_cFeasible"
        }
      ],
      "representation": "在四点空间 Fin 4（吸收元 0）与单分量指标集 Unit 上显式构造满足全部 ExtendedPseudoMetric 公理的伪度量 cd、保吸收元算子 cphi 及非空定义域子集 cU = {1, 2} ⊆ dom cphi，使得输入距离 cd () 1 2 = ⊤ 而输出距离为 1，从而证明 channelLipConst cd cphi cU () () = 0 但 0 ∉ ChannelFeasibleScalars cd cphi cU () ()。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelLipConst_lt_top_iff"
        }
      ],
      "representation": "在 U ⊆ dom ϕ 下，结合零下确界分支 HC02-P22 与正有限下确界取到分支 HC02-P19，证明 channelLipConst d ϕ U i j < ⊤ 当且仅当存在 lam < ⊤ 使 ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_entry_removes_channel_term"
        }
      ],
      "representation": "证明当 L i j = 0 时，对任意点对 x, y（允许 d i x y = ⊤）恒有 L i j * d i x y = 0，输出分量 j 的全指标求和等于擦除指标 i 后的求和 Finset.univ.erase i，且当 L ∈ RestrictedLipSet d ϕ U 时 d j (ϕ.func x) (ϕ.func y) 受该删去 i 项的余项和控制。",
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
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLip_of_isRowSparseAt"
        }
      ],
      "representation": "证明若 L ∈ RestrictedLipSet d ϕ U 且对任意唯一输入位置 i（不必等于输出指标 j）满足 IsRowSparseAt L i j（∀ k ≠ i, L k j = 0），则 ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D07"
      ]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLip_of_isColSparseAt"
        }
      ],
      "representation": "证明若 L ∈ RestrictedLipSet d ϕ U 在固定输入列 i 上满足 IsColSparseAt L i j（∀ k ≠ j, L i k = 0），则对一切 k ≠ j 均有 L i k * d i x y = 0 且 d k (ϕ.func x) (ϕ.func y) 的证书上界求和可删去输入 i（即输入 i 至多向输出 j 贡献）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D07",
        "HC02-P25"
      ]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLip_of_isDiagonalBound"
        }
      ],
      "representation": "证明若 L ∈ RestrictedLipSet d ϕ U 满足对角条件 IsDiagonalBound L（所有非对角条目为 0），则对所有分量 j : I 及所有 x, y ∈ U 有独立标量放缩上界 d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.diagonal_row_scalar_two_sided_bound"
        }
      ],
      "representation": "给定 L ∈ RestrictedLipSet d ϕ U 与 K ∈ RestrictedCoLipSet d ϕ U，仅对上界矩阵假设第 j 行除对角项外为零 IsRowSparseAt L j j（不对 K 作稀疏假设），证明 ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.componentwise_scalar_two_sided_bound"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.componentwise_finite_scalar_two_sided_bound"
        }
      ],
      "representation": "当对所有 j : I 均满足 IsRowSparseAt L j j 时，由 componentwise_scalar_two_sided_bound 证明全部分量的标量双侧不等式同时成立；若进一步满足 ∀ j, L j j < ⊤ 且 ∀ j, K j j < ⊤，则由 componentwise_finite_scalar_two_sided_bound 提取有限非负实数标量族 κ, ℓ : I → NNReal 给出有限标量双侧放缩界。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03",
        "HC02-D07",
        "HC02-P29"
      ]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pos_coLip_channel_lower_bound"
        },
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pos_coLip_preserves_distinguishability"
        }
      ],
      "representation": "设 K ∈ RestrictedCoLipSet d ϕ U 且 0 < K i j，先由 pos_coLip_channel_lower_bound 给出通道正下界传递 K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)，进而证明对任意 x, y ∈ U，0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y)。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {
          "file": "OperatorBounds/ChannelBounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_reflects_gaugeZeroRelated"
        }
      ],
      "representation": "设 K ∈ RestrictedCoLipSet d ϕ U 且对所有 j : I 有 0 < K j j，利用前置模块的族零距关系 GaugeZeroRelated 及单通道可分辨保持 HC02-P31，证明对任意 x, y ∈ U，GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-P31"
      ]
    }
  ]
}
```

### 完成度与严格对齐说明

- **完整完成且严格对齐**：本交付已完成全部 40 项义务（`HC02-D01` 至 `HC02-D08` 及 `HC02-P01` 至 `HC02-P32`，全部状态为 `complete`），在固定 Lean 4.29.1 与给定 mathlib 环境下从零编译全部通过（零错误、零警告）。
- **内核与公理核验**：经 `Lean.collectAxioms` 对 `formal_oet.vol_01.ch_02_operator_bounds` 命名空间下全部声明逐一检查，无任何 `sorry`、`admit`、新增公理或 `Lean.ofReduceBool` 等跳过内核检查的设施，所涉逻辑公理严格限于 `propext`、`Classical.choice`、`Quot.sound`。所有涉及等价表示之处（如输入优先界矩阵与标准行列矩阵乘法、按施行顺序的有限复合与前置模块 `OperatorChain`）均在源码中给出了显式对应证明，逐步链证书结构不包含最终复合界字段。
- **未完成或未确认的范围**：无（未完成项为 0，未确认范围为 0）。
