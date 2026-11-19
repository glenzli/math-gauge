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
