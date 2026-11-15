{}
已完成第2章（[02-operator-bounds.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/source/02-operator-bounds.md)）全部数学内容与 [obligations.json](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/obligations.json) 全部40项义务的 Lean 4.29.1 形式化，保留前置冻结模块 [gauge_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean) 与 [operator_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean) 原样未改动，目标源码位于 [Main.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/Main.lean)、[matrix_bounds.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean)、[channel_decoupling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean)，对齐清单位于 [alignment.json](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/alignment.json)。以下为完整源码与对齐对象全文：

```lean filename=Main.lean
import formal_oet.vol_01.ch_02_operator_bounds.matrix_bounds
import formal_oet.vol_01.ch_02_operator_bounds.channel_decoupling
```

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

noncomputable section

/-!
## 矩阵表示、显示矩阵与有序乘积 (HC02-D03, HC02-D04)
-/

/-- 输入优先存储的通道矩阵：`M i j` 表示从输入分量 `i` 到输出分量 `j` 的系数 $M_{i \to j}$。 -/
abbrev ChannelMatrix (I : Type) : Type := I → I → ENNReal

/--
将通道矩阵转换为常规行列显示矩阵 `Matrix I I ENNReal`：
输出指标 `j` 标记行，输入指标 `i` 标记列，故第 `j` 行第 `i` 列条目为 `M i j`。
-/
def toDisplayMatrix {I : Type} (M : ChannelMatrix I) : Matrix I I ENNReal :=
  Matrix.of (fun j i => M i j)

/-- 从常规行列显示矩阵还原输入优先通道矩阵。 -/
def ofDisplayMatrix {I : Type} (A : Matrix I I ENNReal) : ChannelMatrix I :=
  fun i j => A j i

/-- 输入优先通道矩阵与常规行列显示矩阵之间的双射等价。 -/
def displayMatrixEquiv (I : Type) : ChannelMatrix I ≃ Matrix I I ENNReal where
  toFun := toDisplayMatrix
  invFun := ofDisplayMatrix
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem toDisplayMatrix_apply {I : Type} (M : ChannelMatrix I) (j i : I) :
    toDisplayMatrix M j i = M i j :=
  rfl

@[simp]
theorem ofDisplayMatrix_apply {I : Type} (A : Matrix I I ENNReal) (i j : I) :
    ofDisplayMatrix A i j = A j i :=
  rfl

/--
通道矩阵复合乘法：$(\mathbf{M}_2 \cdot \mathbf{M}_1)_{i \to j} = \sum_{k \in I} (\mathbf{M}_2)_{k \to j} (\mathbf{M}_1)_{i \to k}$。
-/
def channelMul {I : Type} [Fintype I] (M2 M1 : ChannelMatrix I) : ChannelMatrix I :=
  fun i j => ∑ k : I, M2 k j * M1 i k

@[simp]
theorem channelMul_apply {I : Type} [Fintype I] (M2 M1 : ChannelMatrix I) (i j : I) :
    channelMul M2 M1 i j = ∑ k : I, M2 k j * M1 i k :=
  rfl

/-- 通道矩阵乘法与常规行列矩阵乘法一致：`toDisplayMatrix (M2 · M1) = toDisplayMatrix M2 * toDisplayMatrix M1`。 -/
theorem toDisplayMatrix_channelMul {I : Type} [Fintype I] (M2 M1 : ChannelMatrix I) :
    toDisplayMatrix (channelMul M2 M1) = toDisplayMatrix M2 * toDisplayMatrix M1 := by
  ext j i
  simp [toDisplayMatrix, channelMul, Matrix.mul_apply]

/-- 通道矩阵乘法满足结合律。 -/
theorem channelMul_assoc {I : Type} [Fintype I] (M3 M2 M1 : ChannelMatrix I) :
    channelMul (channelMul M3 M2) M1 = channelMul M3 (channelMul M2 M1) := by
  ext i j
  simp only [channelMul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- 单位通道矩阵 $\mathbf{I}_{i \to j} = \delta_{ij}$。 -/
def channelId (I : Type) : ChannelMatrix I := by
  classical
  exact fun i j => if i = j then 1 else 0

@[simp]
theorem channelId_diag {I : Type} (i : I) : channelId I i i = 1 := by
  classical
  simp [channelId]

theorem channelId_offDiag {I : Type} {i j : I} (h : i ≠ j) : channelId I i j = 0 := by
  classical
  simp [channelId, h]

theorem toDisplayMatrix_channelId {I : Type} [DecidableEq I] :
    toDisplayMatrix (channelId I) = (1 : Matrix I I ENNReal) := by
  ext j i
  by_cases h : j = i
  · subst h
    simp [toDisplayMatrix]
  · have hij : i ≠ j := fun h' => h h'.symm
    simp [toDisplayMatrix, channelId_offDiag hij, h]

@[simp]
theorem channelMul_id_left {I : Type} [Fintype I] (M : ChannelMatrix I) :
    channelMul (channelId I) M = M := by
  ext i j
  simp only [channelMul_apply]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro k hk
    rw [channelId_offDiag hk, zero_mul]

@[simp]
theorem channelMul_id_right {I : Type} [Fintype I] (M : ChannelMatrix I) :
    channelMul M (channelId I) = M := by
  ext i j
  simp only [channelMul_apply]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro k hk
    rw [channelId_offDiag hk.symm, mul_zero]

/--
按算子施行顺序 $\phi_1, \dots, \phi_k$ 排列的矩阵族 `Ms : Fin k → ChannelMatrix I` 的有序乘积
$\mathbf{M}^{(k)} \cdot \cdots \cdot \mathbf{M}^{(1)}$。
当 $k = 0$ 时为空乘积，定义为单位矩阵 `channelId I`；当 $k = 1$ 时等于唯一矩阵 `Ms 0`。
-/
def orderedChannelProd {I : Type} [Fintype I] :
    {k : ℕ} → (Fin k → ChannelMatrix I) → ChannelMatrix I
  | 0, _ => channelId I
  | 1, Ms => Ms 0
  | k + 2, Ms => channelMul (Ms (Fin.last (k + 1))) (orderedChannelProd (Fin.init Ms))

@[simp]
theorem orderedChannelProd_zero {I : Type} [Fintype I] (Ms : Fin 0 → ChannelMatrix I) :
    orderedChannelProd Ms = channelId I :=
  rfl

@[simp]
theorem orderedChannelProd_one {I : Type} [Fintype I] (Ms : Fin 1 → ChannelMatrix I) :
    orderedChannelProd Ms = Ms 0 :=
  rfl

theorem orderedChannelProd_succ {I : Type} [Fintype I] {k : ℕ}
    (Ms : Fin (k + 1) → ChannelMatrix I) :
    orderedChannelProd Ms = channelMul (Ms (Fin.last k)) (orderedChannelProd (Fin.init Ms)) := by
  cases k with
  | zero =>
    change Ms 0 = channelMul (Ms 0) (channelId I)
    exact (channelMul_id_right (Ms 0)).symm
  | succ m =>
    rfl

theorem orderedChannelProd_two {I : Type} [Fintype I] (Ms : Fin 2 → ChannelMatrix I) :
    orderedChannelProd Ms = channelMul (Ms 1) (Ms 0) :=
  rfl

/-!
## Lipschitz 上界矩阵与复合律 (HC02-D01, HC02-P01 .. HC02-P05)
-/

/--
OET anchor: h-af85899693cc8750
**定义（Lipschitz 矩阵证书族 $\mathscr{L}(\phi)$）**
-/
def LipCertSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)] : Set (ChannelMatrix I) :=
  { L | ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y }

/--
OET anchor: h-af85899693cc8750
**定义（子集受限 Lip 矩阵证书族 $\mathscr{L}(\phi)\big|_U$）**
包含 $U \subseteq \mathrm{dom}(\phi)$ 以及 $U$ 上所有点对的距离放缩不等式。
-/
def RestrictedLipCertSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)] (U : Set X) : Set (ChannelMatrix I) :=
  { L | U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y }

@[simp]
theorem restrictedLipCertSet_dom_eq {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)] :
    RestrictedLipCertSet d ϕ (dom ϕ) = LipCertSet d ϕ := by
  ext L
  simp [RestrictedLipCertSet, LipCertSet]

/--
OET anchor: h-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界）** (HC02-P01)
当 $I = \{i\}$ 时，合法 Lip 矩阵条件等价于标量不等式 $d_i(\phi(x), \phi(y)) \le L_{i \to i} d_i(x, y)$。
-/
theorem lipCertSet_singleton_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (i : I) (hI : ∀ k : I, k = i) (L : ChannelMatrix I) :
    L ∈ LipCertSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  constructor
  · intro hL x hx y hy
    have hj := hL x hx y hy i
    rwa [Fintype.sum_eq_single i (fun k hk => False.elim (hk (hI k)))] at hj
  · intro h_scalar x hx y hy j
    rw [hI j, Fintype.sum_eq_single i (fun k hk => False.elim (hk (hI k)))]
    exact h_scalar x hx y hy

/-- 全域 Lip 证书可限制到任意定义域子集 $U \subseteq \mathrm{dom}(\phi)$ (HC02-P02)。 -/
theorem lipCertSet_subset_restricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ dom ϕ) :
    LipCertSet d ϕ ⊆ RestrictedLipCertSet d ϕ U := by
  intro L hL
  exact ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/-- 评估域缩小时，受限 Lip 证书族扩大：$U \subseteq V \subseteq \mathrm{dom}(\phi) \Rightarrow \mathscr{L}(\phi)\big|_V \subseteq \mathscr{L}(\phi)\big|_U$ (HC02-P03)。 -/
theorem restrictedLipCertSet_subset_of_subset {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedLipCertSet d ϕ V ⊆ RestrictedLipCertSet d ϕ U := by
  intro L hL
  exact ⟨Set.Subset.trans hUV hV, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- 受限 Lip 证书族关于子集包含单调反序（无需额外显式传入 $V \subseteq \mathrm{dom}(\phi)$）。 -/
theorem restrictedLipCertSet_antitone {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U V : Set X} (hUV : U ⊆ V) :
    RestrictedLipCertSet d ϕ V ⊆ RestrictedLipCertSet d ϕ U := by
  intro L hL
  exact restrictedLipCertSet_subset_of_subset d ϕ hUV hL.1 hL

/-- 受限 Lip 证书族在通道 $(i, j)$ 上的逐条目下确界 $\inf \{ M_{i \to j} : M \in \mathscr{L}(\phi)\big|_U \}$ (HC02-P04)。 -/
def entryLipInf {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun M : ChannelMatrix I => M i j) '' RestrictedLipCertSet d ϕ U)

/-- 缩小评估域 $U \subseteq V$ 时，逐条目下确界不增 (HC02-P04)。 -/
theorem entryLipInf_mono {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U V : Set X} (hUV : U ⊆ V) (i j : I) :
    entryLipInf d ϕ U i j ≤ entryLipInf d ϕ V i j := by
  apply sInf_le_sInf
  exact Set.image_mono (restrictedLipCertSet_antitone d ϕ hUV)

/-- 恒等算子 $\mathrm{id}_{\mathcal{X}}$。 -/
def idOperator {X : Type} {bot : X} : Operator X bot :=
  ⟨id, rfl⟩

/-- 两个算子的复合 $\phi_2 \circ \phi_1$。 -/
def opComp {X : Type} {bot : X} (ϕ2 ϕ1 : Operator X bot) : Operator X bot :=
  ⟨ϕ2.func ∘ ϕ1.func, by simp [ϕ1.preserves_bot, ϕ2.preserves_bot]⟩

@[simp]
theorem idOperator_func {X : Type} {bot : X} (x : X) :
    (@idOperator X bot).func x = x :=
  rfl

@[simp]
theorem opComp_func {X : Type} {bot : X} (ϕ2 ϕ1 : Operator X bot) (x : X) :
    (opComp ϕ2 ϕ1).func x = ϕ2.func (ϕ1.func x) :=
  rfl

theorem dom_opComp_subset_left {X : Type} {bot : X} {ϕ2 ϕ1 : Operator X bot}
    {U1 : Set X} (hU1 : U1 ⊆ dom (opComp ϕ2 ϕ1)) :
    U1 ⊆ dom ϕ1 := by
  intro x hx h_bot
  apply hU1 hx
  simp [opComp, h_bot, ϕ2.preserves_bot]

theorem image_subset_dom_of_subset_dom_opComp {X : Type} {bot : X} {ϕ2 ϕ1 : Operator X bot}
    {U1 : Set X} (hU1 : U1 ⊆ dom (opComp ϕ2 ϕ1)) :
    operator_image ϕ1 U1 ⊆ dom ϕ2 := by
  rintro y ⟨x, hx, rfl⟩
  exact hU1 hx

/--
OET anchor: h-193cebcc1a7f9259
**命题（Lip 矩阵复合律）** (HC02-P05)
若 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，$U_2 = \phi_1(U_1)$，
$\mathbf{L}_1 \in \mathscr{L}(\phi_1)\big|_{U_1}$ 且 $\mathbf{L}_2 \in \mathscr{L}(\phi_2)\big|_{U_2}$，
则 $\mathbf{L}_2 \cdot \mathbf{L}_1 \in \mathscr{L}(\phi_2 \circ \phi_1)\big|_{U_1}$。
-/
theorem restrictedLip_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ2 ϕ1 : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (hU1 : U1 ⊆ dom (opComp ϕ2 ϕ1))
    {L1 L2 : ChannelMatrix I}
    (hL1 : L1 ∈ RestrictedLipCertSet d ϕ1 U1)
    (hL2 : L2 ∈ RestrictedLipCertSet d ϕ2 (operator_image ϕ1 U1)) :
    channelMul L2 L1 ∈ RestrictedLipCertSet d (opComp ϕ2 ϕ1) U1 := by
  refine ⟨hU1, ?_⟩
  intro x hx y hy j
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  calc
    d j ((opComp ϕ2 ϕ1).func x) ((opComp ϕ2 ϕ1).func y)
      = d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) := rfl
    _ ≤ ∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y) := hL2.2 _ hx2 _ hy2 j
    _ ≤ ∑ k : I, L2 k j * (∑ i : I, L1 i k * d i x y) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (hL1.2 x hx y hy k) (zero_le _)
    _ = ∑ k : I, ∑ i : I, (L2 k j * L1 i k) * d i x y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
    _ = ∑ i : I, ∑ k : I, (L2 k j * L1 i k) * d i x y := Finset.sum_comm
    _ = ∑ i : I, channelMul L2 L1 i j * d i x y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [channelMul_apply, Finset.sum_mul]

/-!
## co-Lipschitz 下界矩阵与复合律 (HC02-D02, HC02-P06, HC02-P07)
-/

/--
OET anchor: h-af85899693cc8750
**定义（子集受限 co-Lipschitz 矩阵证书族 $\mathscr{K}(\phi)\big|_U$）** (HC02-D02)
显式包含非空性条件 $U \neq \emptyset$、定义域条件 $U \subseteq \mathrm{dom}(\phi)$ 与下界不等式。
-/
def RestrictedCoLipCertSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)] (U : Set X) : Set (ChannelMatrix I) :=
  { K | U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y) }

/-- 全域 co-Lip 矩阵证书族简记 $\mathscr{K}(\phi)\big|_{\mathrm{dom}(\phi)}$。 -/
abbrev GlobalCoLipCertSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)] : Set (ChannelMatrix I) :=
  RestrictedCoLipCertSet d ϕ (dom ϕ)

/--
OET anchor: h-88784dcbfff0ea66
**注（co-Lip 通道退化的点对判据）** (HC02-P06)
若存在 $x, y \in \mathrm{dom}(\phi)$ 使 $d_j(\phi(x), \phi(y)) = 0$ 且 $d_i(x, y) > 0$，
则任一全域 co-Lip 矩阵 $\mathbf{K} \in \mathscr{K}(\phi)\big|_{\mathrm{dom}(\phi)}$ 必有 $K_{i \to j} = 0$。
-/
theorem globalCoLip_entry_eq_zero_of_collapse {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    {i j : I} (h_out : d j (ϕ.func x) (ϕ.func y) = 0) (h_in : 0 < d i x y)
    {K : ChannelMatrix I} (hK : K ∈ RestrictedCoLipCertSet d ϕ (dom ϕ)) :
    K i j = 0 := by
  have h_le : K i j * d i x y ≤ 0 := by
    calc
      K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
        Finset.single_le_sum (f := fun k => K k j * d k x y)
          (fun k _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
      _ = 0 := h_out
  have h_mul_zero : K i j * d i x y = 0 := le_antisymm h_le (zero_le _)
  rcases mul_eq_zero.mp h_mul_zero with hK0 | hd0
  · exact hK0
  · exact False.elim (h_in.ne' hd0)

/--
OET anchor: h-0f256e6f1d38a612
**命题（co-Lip 矩阵复合律）** (HC02-P07)
若 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，$U_2 = \phi_1(U_1)$，
$\mathbf{K}_1 \in \mathscr{K}(\phi_1)\big|_{U_1}$ 且 $\mathbf{K}_2 \in \mathscr{K}(\phi_2)\big|_{U_2}$，
则 $\mathbf{K}_2 \cdot \mathbf{K}_1 \in \mathscr{K}(\phi_2 \circ \phi_1)\big|_{U_1}$（含 $U_1 \neq \emptyset$）。
-/
theorem restrictedCoLip_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ2 ϕ1 : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (hU1 : U1 ⊆ dom (opComp ϕ2 ϕ1))
    {K1 K2 : ChannelMatrix I}
    (hK1 : K1 ∈ RestrictedCoLipCertSet d ϕ1 U1)
    (hK2 : K2 ∈ RestrictedCoLipCertSet d ϕ2 (operator_image ϕ1 U1)) :
    channelMul K2 K1 ∈ RestrictedCoLipCertSet d (opComp ϕ2 ϕ1) U1 := by
  refine ⟨hK1.1, hU1, ?_⟩
  intro x hx y hy j
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  calc
    (∑ i : I, channelMul K2 K1 i j * d i x y)
      = ∑ i : I, ∑ k : I, (K2 k j * K1 i k) * d i x y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [channelMul_apply, Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, (K2 k j * K1 i k) * d i x y := Finset.sum_comm
    _ = ∑ k : I, K2 k j * (∑ i : I, K1 i k * d i x y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
    _ ≤ ∑ k : I, K2 k j * d k (ϕ1.func x) (ϕ1.func y) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (hK1.2.2 x hx y hy k) (zero_le _)
    _ ≤ d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) := hK2.2.2 _ hx2 _ hy2 j
    _ = d j ((opComp ϕ2 ϕ1).func x) ((opComp ϕ2 ϕ1).func y) := rfl

/-- 两步 co-Lip 复合同时给出 $U_1$ 非空性的显式合取形式 (HC02-P07)。 -/
theorem restrictedCoLip_comp_with_nonempty {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ2 ϕ1 : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (hU1 : U1 ⊆ dom (opComp ϕ2 ϕ1))
    {K1 K2 : ChannelMatrix I}
    (hK1 : K1 ∈ RestrictedCoLipCertSet d ϕ1 U1)
    (hK2 : K2 ∈ RestrictedCoLipCertSet d ϕ2 (operator_image ϕ1 U1)) :
    channelMul K2 K1 ∈ RestrictedCoLipCertSet d (opComp ϕ2 ϕ1) U1 ∧ U1.Nonempty :=
  ⟨restrictedCoLip_comp d ϕ2 ϕ1 hU1 hK1 hK2, hK1.1⟩

/-!
## 两个算子的点对像距扰动界 (HC02-P08 .. HC02-P11)
-/

/-- 两个算子的公共定义域 $\mathrm{dom}(\phi_1, \phi_2) := \mathrm{dom}(\phi_1) \cap \mathrm{dom}(\phi_2)$。 -/
def commonDom {X : Type} {bot : X} (ϕ1 ϕ2 : Operator X bot) : Set X :=
  dom ϕ1 ∩ dom ϕ2

/--
OET anchor: h-b959b42f25710105
**命题（点对像距扰动界 (i) 正向）** (HC02-P08)
-/
theorem pairwise_image_dist_perturb_forward {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (_hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j := by
  intro x hx y hy j
  have h1 : d j (ϕ2.func x) (ϕ1.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  have h2 : d j (ϕ1.func y) (ϕ2.func y) ≤ δ j := hδ y hy j
  calc
    d j (ϕ2.func x) (ϕ2.func y)
      ≤ d j (ϕ2.func x) (ϕ1.func x) + d j (ϕ1.func x) (ϕ2.func y) :=
        (hd j).triangle _ _ _
    _ ≤ d j (ϕ2.func x) (ϕ1.func x) + (d j (ϕ1.func x) (ϕ1.func y) + d j (ϕ1.func y) (ϕ2.func y)) :=
        add_le_add le_rfl ((hd j).triangle _ _ _)
    _ ≤ δ j + (d j (ϕ1.func x) (ϕ1.func y) + δ j) :=
        add_le_add h1 (add_le_add le_rfl h2)
    _ = d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j := by
        rw [← add_assoc, add_comm (δ j) (d j (ϕ1.func x) (ϕ1.func y))]

/-- 正向点对像距扰动界的 $+ 2\delta_j$ 等价形式 (HC02-P08)。 -/
theorem pairwise_image_dist_perturb_forward_two_mul {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
  intro x hx y hy j
  rw [two_mul, ← add_assoc]
  exact pairwise_image_dist_perturb_forward d ϕ1 ϕ2 hU hδ x hx y hy j

/--
OET anchor: h-b959b42f25710105
**命题（点对像距扰动界 (i) 反向）** (HC02-P09)
-/
theorem pairwise_image_dist_perturb_backward {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + δ j + δ j := by
  have hU_symm : U ⊆ commonDom ϕ2 ϕ1 := fun z hz => ⟨(hU hz).2, (hU hz).1⟩
  have hδ_symm : ∀ z ∈ U, ∀ j : I, d j (ϕ2.func z) (ϕ1.func z) ≤ δ j := by
    intro z hz j
    rw [(hd j).symm]
    exact hδ z hz j
  exact pairwise_image_dist_perturb_forward d ϕ2 ϕ1 hU_symm hδ_symm

/-- 反向点对像距扰动界的 $+ 2\delta_j$ 等价形式 (HC02-P09)。 -/
theorem pairwise_image_dist_perturb_backward_two_mul {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
  intro x hx y hy j
  rw [two_mul, ← add_assoc]
  exact pairwise_image_dist_perturb_backward d ϕ1 ϕ2 hU hδ x hx y hy j

/--
OET anchor: h-b959b42f25710105
**命题（点对像距扰动界 (ii) Lip 上界桥接）** (HC02-P10)
-/
theorem lip_bridge_of_perturb {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {L1 : ChannelMatrix I} (hL1 : L1 ∈ RestrictedLipCertSet d ϕ1 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j := by
  intro x hx y hy j
  calc
    d j (ϕ2.func x) (ϕ2.func y)
      ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j :=
        pairwise_image_dist_perturb_forward_two_mul d ϕ1 ϕ2 hU hδ x hx y hy j
    _ ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j :=
        add_le_add (hL1.2 x hx y hy j) le_rfl

/-- 交换 $\phi_1, \phi_2$ 后的 Lip 上界桥接结论。 -/
theorem lip_bridge_of_perturb_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {L2 : ChannelMatrix I} (hL2 : L2 ∈ RestrictedLipCertSet d ϕ2 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ (∑ i : I, L2 i j * d i x y) + 2 * δ j := by
  have hU_symm : U ⊆ commonDom ϕ2 ϕ1 := fun z hz => ⟨(hU hz).2, (hU hz).1⟩
  have hδ_symm : ∀ z ∈ U, ∀ j : I, d j (ϕ2.func z) (ϕ1.func z) ≤ δ j := by
    intro z hz j
    rw [(hd j).symm]
    exact hδ z hz j
  exact lip_bridge_of_perturb d ϕ2 ϕ1 hU_symm hδ_symm hL2

/--
OET anchor: h-b959b42f25710105
**命题（点对像距扰动界 (iii) co-Lip 下界桥接）** (HC02-P11)
-/
theorem coLip_bridge_of_perturb {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {K1 : ChannelMatrix I} (hK1 : K1 ∈ RestrictedCoLipCertSet d ϕ1 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K1 i j * d i x y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
  intro x hx y hy j
  calc
    (∑ i : I, K1 i j * d i x y)
      ≤ d j (ϕ1.func x) (ϕ1.func y) := hK1.2.2 x hx y hy j
    _ ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j :=
        pairwise_image_dist_perturb_backward_two_mul d ϕ1 ϕ2 hU hδ x hx y hy j

/-- 交换 $\phi_1, \phi_2$ 后的 co-Lip 下界桥接结论。 -/
theorem coLip_bridge_of_perturb_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot)
    [hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU : U ⊆ commonDom ϕ1 ϕ2)
    {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {K2 : ChannelMatrix I} (hK2 : K2 ∈ RestrictedCoLipCertSet d ϕ2 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K2 i j * d i x y) ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
  have hU_symm : U ⊆ commonDom ϕ2 ϕ1 := fun z hz => ⟨(hU hz).2, (hU hz).1⟩
  have hδ_symm : ∀ z ∈ U, ∀ j : I, d j (ϕ2.func z) (ϕ1.func z) ≤ δ j := by
    intro z hz j
    rw [(hd j).symm]
    exact hδ z hz j
  exact coLip_bridge_of_perturb d ϕ2 ϕ1 hU_symm hδ_symm hK2

/-!
## 有限复合链、实际像域与局部矩阵界 (HC02-D05, HC02-P12 .. HC02-P15)
-/

/--
按施行顺序 $\phi_1, \dots, \phi_k$ 排列的有限算子族的有序复合 $c_k = \phi_k \circ \cdots \circ \phi_1$。
当 $k = 0$ 时为恒等算子 `idOperator`；当 $k = 1$ 时等于 `ϕs 0`。
-/
def orderedOpComp {X : Type} {bot : X} :
    {k : ℕ} → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => idOperator
  | 1, ϕs => ϕs 0
  | k + 2, ϕs => opComp (ϕs (Fin.last (k + 1))) (orderedOpComp (Fin.init ϕs))

@[simp]
theorem orderedOpComp_zero {X : Type} {bot : X} (ϕs : Fin 0 → Operator X bot) :
    orderedOpComp ϕs = idOperator :=
  rfl

@[simp]
theorem orderedOpComp_one {X : Type} {bot : X} (ϕs : Fin 1 → Operator X bot) :
    orderedOpComp ϕs = ϕs 0 :=
  rfl

theorem orderedOpComp_succ {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin (k + 1) → Operator X bot) :
    orderedOpComp ϕs = opComp (ϕs (Fin.last k)) (orderedOpComp (Fin.init ϕs)) := by
  cases k with
  | zero =>
    ext x
    rfl
  | succ m =>
    rfl

theorem orderedOpComp_two {X : Type} {bot : X} (ϕs : Fin 2 → Operator X bot) :
    orderedOpComp ϕs = opComp (ϕs 1) (ϕs 0) :=
  rfl

/-- 与第1章辅助函数 `OperatorChain`（逆序列表）的精确对应。 -/
theorem orderedOpComp_eq_operatorChain {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) :
    orderedOpComp ϕs = OperatorChain ((List.ofFn ϕs).reverse) := by
  induction k with
  | zero =>
    simp [orderedOpComp, idOperator, OperatorChain]
  | succ m ih =>
    rw [orderedOpComp_succ]
    have h_ofFn : List.ofFn ϕs = List.ofFn (Fin.init ϕs) ++ [ϕs (Fin.last m)] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      rfl
    rw [h_ofFn, List.reverse_append, List.reverse_singleton, List.singleton_append]
    ext x
    simp [opComp, OperatorChain, ih (Fin.init ϕs)]

/--
递归定义有限复合链上的实际中间像域序列 $U_1, U_2, \dots, U_{k+1}$：
`chainDomain ϕs U1 0 = U1`，且 `chainDomain ϕs U1 m.succ = ϕ_m(U_m)` (HC02-D05)。
-/
def chainDomain {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U1 : Set X) : Fin (k + 1) → Set X :=
  Fin.induction (motive := fun _ => Set X) U1 (fun m Um => operator_image (ϕs m) Um)

@[simp]
theorem chainDomain_zero {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U1 : Set X) :
    chainDomain ϕs U1 0 = U1 :=
  Fin.induction_zero (motive := fun _ => Set X) U1 (fun m Um => operator_image (ϕs m) Um)

@[simp]
theorem chainDomain_succ {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U1 : Set X) (m : Fin k) :
    chainDomain ϕs U1 m.succ = operator_image (ϕs m) (chainDomain ϕs U1 m.castSucc) :=
  Fin.induction_succ (motive := fun _ => Set X) U1 (fun m Um => operator_image (ϕs m) Um) m

theorem chainDomain_castSucc_init {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin (k + 1) → Operator X bot) (U1 : Set X) (r : Fin (k + 1)) :
    chainDomain ϕs U1 r.castSucc = chainDomain (Fin.init ϕs) U1 r := by
  induction r using Fin.induction with
  | zero =>
    simp
  | succ m ih =>
    rw [Fin.castSucc_succ, chainDomain_succ, chainDomain_succ, ih]
    rfl

/-- 全复合算子在起始域 $U_1$ 上的像等于逐次递归所得终端像集 $U_{k+1}$ (HC02-D05)。 -/
theorem chainDomain_last_eq_composite_image {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U1 : Set X) :
    operator_image (orderedOpComp ϕs) U1 = chainDomain ϕs U1 (Fin.last k) := by
  induction k with
  | zero =>
    change id '' U1 = U1
    exact Set.image_id U1
  | succ m ih =>
    rw [orderedOpComp_succ, ← Fin.succ_last m, chainDomain_succ, chainDomain_castSucc_init, ← ih]
    ext y
    simp [operator_image, opComp, Set.mem_image]

/-- 由 $U_1 \subseteq \mathrm{dom}(c_k)$ 递推保证每一步实际输入域 $U_m \subseteq \mathrm{dom}(\phi_m)$ (HC02-D05)。 -/
theorem chainDomain_subset_dom {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) {U1 : Set X}
    (hU1 : U1 ⊆ dom (orderedOpComp ϕs)) (m : Fin k) :
    chainDomain ϕs U1 m.castSucc ⊆ dom (ϕs m) := by
  induction k with
  | zero =>
    exact Fin.elim0 m
  | succ n ih =>
    rw [orderedOpComp_succ] at hU1
    have hU1_init : U1 ⊆ dom (orderedOpComp (Fin.init ϕs)) :=
      dom_opComp_subset_left hU1
    have h_last_dom : operator_image (orderedOpComp (Fin.init ϕs)) U1 ⊆ dom (ϕs (Fin.last n)) :=
      image_subset_dom_of_subset_dom_opComp hU1
    refine Fin.lastCases ?_ ?_ m
    · rw [chainDomain_castSucc_init, ← chainDomain_last_eq_composite_image]
      exact h_last_dom
    · intro m'
      rw [chainDomain_castSucc_init ϕs U1 m'.castSucc]
      exact ih (Fin.init ϕs) hU1_init m'

/-- 起始域非空蕴含复合链上所有中间像域非空。 -/
theorem chainDomain_nonempty {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) {U1 : Set X} (hU1 : U1.Nonempty) (r : Fin (k + 1)) :
    (chainDomain ϕs U1 r).Nonempty := by
  induction r using Fin.induction with
  | zero =>
    simpa using hU1
  | succ m ih =>
    rw [chainDomain_succ]
    exact ih.image _

/--
局部 Lip 复合证书链数据结构 (HC02-D05)：
仅记录起始域 $U_1 \subseteq \mathrm{dom}(c_k)$、逐步矩阵与各实际输入域 $U_m$ 上的单步证书，
不以最终全复合界作为字段。
-/
structure LocalLipChain {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {k : ℕ} (ops : Fin k → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)] where
  U1 : Set X
  hU1 : U1 ⊆ dom (orderedOpComp ops)
  mats : Fin k → ChannelMatrix I
  step_certs : ∀ m : Fin k, mats m ∈ RestrictedLipCertSet d (ops m) (chainDomain ops U1 m.castSucc)

/-- 由 $U_1 \subseteq \mathrm{dom}(c_k)$、逐步矩阵及各实际输入域 $U_m$ 上的上界不等式直接构造 `LocalLipChain` (HC02-D05)。 -/
def LocalLipChain.mkOfStepBounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {k : ℕ} (ops : Fin k → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (U1 : Set X) (hU1 : U1 ⊆ dom (orderedOpComp ops))
    (mats : Fin k → ChannelMatrix I)
    (h_bounds : ∀ m : Fin k, ∀ x ∈ chainDomain ops U1 m.castSucc,
      ∀ y ∈ chainDomain ops U1 m.castSucc, ∀ j : I,
        d j ((ops m).func x) ((ops m).func y) ≤ ∑ i : I, mats m i j * d i x y) :
    LocalLipChain d ops where
  U1 := U1
  hU1 := hU1
  mats := mats
  step_certs m := ⟨chainDomain_subset_dom ops hU1 m, h_bounds m⟩

/--
局部 co-Lip 复合证书链数据结构 (HC02-D05)：
仅记录起始域 $U_1 \subseteq \mathrm{dom}(c_k)$、逐步矩阵与各实际输入域 $U_m$ 上的单步 co-Lip 证书（含非空性），
不以最终全复合界作为字段。
-/
structure LocalCoLipChain {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {k : ℕ} (ops : Fin k → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)] where
  U1 : Set X
  hU1 : U1 ⊆ dom (orderedOpComp ops)
  mats : Fin k → ChannelMatrix I
  step_certs : ∀ m : Fin k, mats m ∈ RestrictedCoLipCertSet d (ops m) (chainDomain ops U1 m.castSucc)

/-- 由非空 $U_1 \subseteq \mathrm{dom}(c_k)$、逐步矩阵及各实际输入域 $U_m$ 上的下界不等式直接构造 `LocalCoLipChain` (HC02-D05)。 -/
def LocalCoLipChain.mkOfStepBounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {k : ℕ} (ops : Fin k → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (U1 : Set X) (hU1_ne : U1.Nonempty) (hU1 : U1 ⊆ dom (orderedOpComp ops))
    (mats : Fin k → ChannelMatrix I)
    (h_bounds : ∀ m : Fin k, ∀ x ∈ chainDomain ops U1 m.castSucc,
      ∀ y ∈ chainDomain ops U1 m.castSucc, ∀ j : I,
        (∑ i : I, mats m i j * d i x y) ≤ d j ((ops m).func x) ((ops m).func y)) :
    LocalCoLipChain d ops where
  U1 := U1
  hU1 := hU1
  mats := mats
  step_certs m :=
    ⟨chainDomain_nonempty ops hU1_ne m.castSucc,
     chainDomain_subset_dom ops hU1 m,
     h_bounds m⟩

/--
OET anchor: h-c80171fa685dc795
**推论（有限复合的局部矩阵界 (i) Lip 矩阵放缩上限）** (HC02-P12)
-/
theorem finite_comp_restrictedLip {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {k : ℕ} (hk : 1 ≤ k) (ϕs : Fin k → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (hU1 : U1 ⊆ dom (orderedOpComp ϕs))
    (Ls : Fin k → ChannelMatrix I)
    (hLs : ∀ m : Fin k, Ls m ∈ RestrictedLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc)) :
    orderedChannelProd Ls ∈ RestrictedLipCertSet d (orderedOpComp ϕs) U1 := by
  induction k with
  | zero =>
    omega
  | succ n ih =>
    cases n with
    | zero =>
      simpa using hLs 0
    | succ m =>
      rw [orderedChannelProd_succ, orderedOpComp_succ]
      have hU1_comp : U1 ⊆ dom (opComp (ϕs (Fin.last (m + 1))) (orderedOpComp (Fin.init ϕs))) := by
        rwa [← orderedOpComp_succ]
      have hU1_init : U1 ⊆ dom (orderedOpComp (Fin.init ϕs)) :=
        dom_opComp_subset_left hU1_comp
      have h_init_cert : orderedChannelProd (Fin.init Ls) ∈
          RestrictedLipCertSet d (orderedOpComp (Fin.init ϕs)) U1 := by
        apply ih (Nat.succ_le_succ (Nat.zero_le m)) (Fin.init ϕs) hU1_init (Fin.init Ls)
        intro r
        have hr := hLs r.castSucc
        rwa [chainDomain_castSucc_init ϕs U1 r.castSucc] at hr
      have h_last_cert : Ls (Fin.last (m + 1)) ∈
          RestrictedLipCertSet d (ϕs (Fin.last (m + 1)))
            (operator_image (orderedOpComp (Fin.init ϕs)) U1) := by
        rw [chainDomain_last_eq_composite_image, ← chainDomain_castSucc_init]
        exact hLs (Fin.last (m + 1))
      exact restrictedLip_comp d (ϕs (Fin.last (m + 1))) (orderedOpComp (Fin.init ϕs))
        hU1_comp h_init_cert h_last_cert

/-- `LocalLipChain` 上的复合上界定理封装 (HC02-P12)。 -/
theorem LocalLipChain.composite_cert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} {ops : Fin k → Operator X bot}
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (hk : 1 ≤ k) (C : LocalLipChain d ops) :
    orderedChannelProd C.mats ∈ RestrictedLipCertSet d (orderedOpComp ops) C.U1 :=
  finite_comp_restrictedLip d hk ops C.hU1 C.mats C.step_certs

/--
OET anchor: h-c80171fa685dc795
**推论（有限复合的局部矩阵界 (ii) co-Lip 矩阵保距下限）** (HC02-P13)
-/
theorem finite_comp_restrictedCoLip {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {k : ℕ} (hk : 1 ≤ k) (ϕs : Fin k → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (hU1 : U1 ⊆ dom (orderedOpComp ϕs))
    (Ks : Fin k → ChannelMatrix I)
    (hKs : ∀ m : Fin k, Ks m ∈ RestrictedCoLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc)) :
    orderedChannelProd Ks ∈ RestrictedCoLipCertSet d (orderedOpComp ϕs) U1 := by
  induction k with
  | zero =>
    omega
  | succ n ih =>
    cases n with
    | zero =>
      simpa using hKs 0
    | succ m =>
      rw [orderedChannelProd_succ, orderedOpComp_succ]
      have hU1_comp : U1 ⊆ dom (opComp (ϕs (Fin.last (m + 1))) (orderedOpComp (Fin.init ϕs))) := by
        rwa [← orderedOpComp_succ]
      have hU1_init : U1 ⊆ dom (orderedOpComp (Fin.init ϕs)) :=
        dom_opComp_subset_left hU1_comp
      have h_init_cert : orderedChannelProd (Fin.init Ks) ∈
          RestrictedCoLipCertSet d (orderedOpComp (Fin.init ϕs)) U1 := by
        apply ih (Nat.succ_le_succ (Nat.zero_le m)) (Fin.init ϕs) hU1_init (Fin.init Ks)
        intro r
        have hr := hKs r.castSucc
        rwa [chainDomain_castSucc_init ϕs U1 r.castSucc] at hr
      have h_last_cert : Ks (Fin.last (m + 1)) ∈
          RestrictedCoLipCertSet d (ϕs (Fin.last (m + 1)))
            (operator_image (orderedOpComp (Fin.init ϕs)) U1) := by
        rw [chainDomain_last_eq_composite_image, ← chainDomain_castSucc_init]
        exact hKs (Fin.last (m + 1))
      exact restrictedCoLip_comp d (ϕs (Fin.last (m + 1))) (orderedOpComp (Fin.init ϕs))
        hU1_comp h_init_cert h_last_cert

/-- `LocalCoLipChain` 上的复合下界定理封装 (HC02-P13)。 -/
theorem LocalCoLipChain.composite_cert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} {ops : Fin k → Operator X bot}
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (hk : 1 ≤ k) (C : LocalCoLipChain d ops) :
    orderedChannelProd C.mats ∈ RestrictedCoLipCertSet d (orderedOpComp ops) C.U1 :=
  finite_comp_restrictedCoLip d hk ops C.hU1 C.mats C.step_certs

theorem sum_channelId_mul_dist {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, channelId I i j * d i x y) = d j x y := by
  rw [Fintype.sum_eq_single j]
  · simp
  · intro i hi
    rw [channelId_offDiag hi, zero_mul]

/--
OET anchor: h-11006ddd8c43bfec
**注（零步复合的单位矩阵 Lip 证书）** (HC02-P14)
当 $k = 0$ 时，$c_0 = \mathrm{id}_{\mathcal{X}}$，对任意非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$，
单位矩阵 $\mathbf{I} \in \mathscr{L}(\mathrm{id}_{\mathcal{X}})\big|_U$。
-/
theorem zero_step_id_restrictedLip {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (_hU_ne : U.Nonempty) (hU : U ⊆ dom (@idOperator X bot)) :
    channelId I ∈ RestrictedLipCertSet d (@idOperator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  rw [sum_channelId_mul_dist]
  exact le_rfl

/-- 零步链空乘积形式的单位 Lip 证书 (HC02-P14)。 -/
theorem zero_step_chain_restrictedLip {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕs : Fin 0 → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (Ls : Fin 0 → ChannelMatrix I)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (orderedOpComp ϕs)) :
    orderedChannelProd Ls ∈ RestrictedLipCertSet d (orderedOpComp ϕs) U :=
  zero_step_id_restrictedLip bot d hU_ne hU

/--
OET anchor: h-11006ddd8c43bfec
**注（零步复合的单位矩阵 co-Lip 证书）** (HC02-P15)
同一非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$ 上，
单位矩阵 $\mathbf{I} \in \mathscr{K}(\mathrm{id}_{\mathcal{X}})\big|_U$。
-/
theorem zero_step_id_restrictedCoLip {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (@idOperator X bot)) :
    channelId I ∈ RestrictedCoLipCertSet d (@idOperator X bot) U := by
  refine ⟨hU_ne, hU, ?_⟩
  intro x _ y _ j
  rw [sum_channelId_mul_dist]
  exact le_rfl

/-- 零步链空乘积形式的单位 co-Lip 证书 (HC02-P15)。 -/
theorem zero_step_chain_restrictedCoLip {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕs : Fin 0 → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    (Ks : Fin 0 → ChannelMatrix I)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (orderedOpComp ϕs)) :
    orderedChannelProd Ks ∈ RestrictedCoLipCertSet d (orderedOpComp ϕs) U :=
  zero_step_id_restrictedCoLip bot d hU_ne hU

/-- 零步恒等算子上单位矩阵同时属于受限 Lip 与受限 co-Lip 证书族的交集 (HC02-P14, HC02-P15)。 -/
theorem zero_step_id_mem_lip_inter_coLip {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (@idOperator X bot)) :
    channelId I ∈ RestrictedLipCertSet d (@idOperator X bot) U ∩
      RestrictedCoLipCertSet d (@idOperator X bot) U :=
  ⟨zero_step_id_restrictedLip bot d hU_ne hU, zero_step_id_restrictedCoLip bot d hU_ne hU⟩

/-!
## 有限索引路径表示与乘积条目零值/正值判据 (HC02-D06, HC02-P16, HC02-P17)
-/

/-- 长度 $n \ge 1$ 复合链上的完整中间指标序列 $(k_1, \dots, k_{n-1}) \in I^{n-1}$，不附加任何正性约束。 -/
abbrev IntermediatePath (I : Type) (n : ℕ) : Type := Fin (n - 1) → I

/-- $n = 1$ 时的唯一空中间指标序列。 -/
def emptyIntermediatePath (I : Type) : IntermediatePath I 1 := Fin.elim0

instance intermediatePath_one_unique (I : Type) : Unique (IntermediatePath I 1) where
  default := emptyIntermediatePath I
  uniq ks := by
    ext x
    exact Fin.elim0 x

theorem intermediatePath_one_eq_empty {I : Type} (ks : IntermediatePath I 1) :
    ks = emptyIntermediatePath I :=
  Subsingleton.elim _ _

/--
对 $n \ge 1$、固定起止指标 $k_0 = i, k_n = j$ 与中间序列 `ks : IntermediatePath I n`，
返回完整节点序列 $(k_0, k_1, \dots, k_n)$ 在位置 `r : Fin (n + 1)` 处的指标。
-/
def pathNode {I : Type} {n : ℕ} (_hn : 1 ≤ n) (i j : I)
    (ks : IntermediatePath I n) (r : Fin (n + 1)) : I :=
  if hr0 : r.val = 0 then
    i
  else if hrn : r.val = n then
    j
  else
    ks ⟨r.val - 1, by omega⟩

@[simp]
theorem pathNode_zero {I : Type} {n : ℕ} (hn : 1 ≤ n) (i j : I)
    (ks : IntermediatePath I n) :
    pathNode hn i j ks 0 = i := by
  simp [pathNode]

@[simp]
theorem pathNode_last {I : Type} {n : ℕ} (hn : 1 ≤ n) (i j : I)
    (ks : IntermediatePath I n) :
    pathNode hn i j ks (Fin.last n) = j := by
  have hne : (Fin.last n).val ≠ 0 := by
    rw [Fin.val_last]
    omega
  unfold pathNode
  rw [dif_neg hne, dif_pos (Fin.val_last n)]

/-- 沿路径 `ks` 在第 `m` 层（对应正文 $m \in \{1, \dots, n\}$）的单步矩阵条目 $[\mathbf{M}^{(m)}]_{k_{m-1} \to k_m}$。 -/
def pathEdgeEntry {I : Type} {n : ℕ} (hn : 1 ≤ n)
    (Ms : Fin n → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I n) (m : Fin n) : ENNReal :=
  Ms m (pathNode hn i j ks m.castSucc) (pathNode hn i j ks m.succ)

/-- 路径权重：沿路径各层单步矩阵条目的乘积 $\prod_{m=1}^n [\mathbf{M}^{(m)}]_{k_{m-1} \to k_m}$。 -/
def pathWeight {I : Type} {n : ℕ} (hn : 1 ≤ n)
    (Ms : Fin n → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I n) : ENNReal :=
  ∏ m : Fin n, pathEdgeEntry hn Ms i j ks m

/-- 全正路径谓词：沿该路径的所有单步矩阵条目均严格大于 $0$。 -/
def PathAllPos {I : Type} {n : ℕ} (hn : 1 ≤ n)
    (Ms : Fin n → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I n) : Prop :=
  ∀ m : Fin n, 0 < pathEdgeEntry hn Ms i j ks m

/-- 含零路径谓词：沿该路径存在至少一层单步矩阵条目等于 $0$。 -/
def PathHasZero {I : Type} {n : ℕ} (hn : 1 ≤ n)
    (Ms : Fin n → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I n) : Prop :=
  ∃ m : Fin n, pathEdgeEntry hn Ms i j ks m = 0

@[simp]
theorem pathEdgeEntry_one {I : Type} (Ms : Fin 1 → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I 1) :
    pathEdgeEntry (le_refl 1) Ms i j ks 0 = Ms 0 i j := by
  simp [pathEdgeEntry, pathNode]

@[simp]
theorem pathWeight_one {I : Type} (Ms : Fin 1 → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I 1) :
    pathWeight (le_refl 1) Ms i j ks = Ms 0 i j := by
  simp [pathWeight]

@[simp]
theorem pathHasZero_one_iff {I : Type} (Ms : Fin 1 → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I 1) :
    PathHasZero (le_refl 1) Ms i j ks ↔ Ms 0 i j = 0 := by
  simp [PathHasZero, Fin.exists_fin_one]

@[simp]
theorem pathAllPos_one_iff {I : Type} (Ms : Fin 1 → ChannelMatrix I) (i j : I)
    (ks : IntermediatePath I 1) :
    PathAllPos (le_refl 1) Ms i j ks ↔ 0 < Ms 0 i j := by
  simp [PathAllPos, Fin.forall_fin_one]

/-- 将长度 $k + 1$ 链的中间路径 `Fin k → I` 与末层中间节点 `x : I` 拼接为长度 $k + 2$ 链的中间路径 `Fin (k + 1) → I`。 -/
def snocIntermediatePath {I : Type} (k : ℕ) :
    (IntermediatePath I (k + 1) × I) ≃ IntermediatePath I (k + 2) where
  toFun p := Fin.snoc p.1 p.2
  invFun ks := (Fin.init ks, ks (Fin.last k))
  left_inv := by
    rintro ⟨ks', x⟩
    ext r
    · simp [Fin.init]
    · simp
  right_inv := by
    intro ks
    ext r
    refine Fin.lastCases ?_ ?_ r
    · simp
    · intro r'
      simp [Fin.init]

private theorem pathNode_snoc_castSucc {I : Type} (k : ℕ)
    (i j x : I) (ks' : IntermediatePath I (k + 1)) (r : Fin (k + 2)) :
    pathNode (by omega : 1 ≤ k + 2) i j (snocIntermediatePath k (ks', x)) r.castSucc =
      pathNode (by omega : 1 ≤ k + 1) i x ks' r := by
  by_cases hr0 : r.val = 0
  · unfold pathNode
    rw [dif_pos (by simp [hr0]), dif_pos hr0]
  · by_cases hrk : r.val = k + 1
    · have h_ne0 : (r.castSucc).val ≠ 0 := by simp [hr0]
      have h_nek2 : (r.castSucc).val ≠ k + 2 := by simp; omega
      unfold pathNode
      rw [dif_neg h_ne0, dif_neg h_nek2, dif_neg hr0, dif_pos hrk]
      dsimp [snocIntermediatePath]
      have hlast : (⟨r.val - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := by
        ext; simp [hrk]
      rw [hlast, Fin.snoc_last]
    · have h_lt : r.val - 1 < k := by omega
      have h_ne0 : (r.castSucc).val ≠ 0 := by simp [hr0]
      have h_nek2 : (r.castSucc).val ≠ k + 2 := by simp; omega
      unfold pathNode
      rw [dif_neg h_ne0, dif_neg h_nek2, dif_neg hr0, dif_neg hrk]
      dsimp [snocIntermediatePath]
      let idx : Fin k := ⟨r.val - 1, h_lt⟩
      have hcast : (⟨r.val - 1, by omega⟩ : Fin (k + 1)) = idx.castSucc := by
        ext; simp [idx]
      rw [hcast, Fin.snoc_castSucc]

/-- 有限有序矩阵乘积条目的完整路径展开公式。 -/
theorem orderedChannelProd_apply_eq_sum_pathWeight {I : Type} [Fintype I]
    {n : ℕ} (hn : 1 ≤ n) (Ms : Fin n → ChannelMatrix I) (i j : I) :
    orderedChannelProd Ms i j = ∑ ks : IntermediatePath I n, pathWeight hn Ms i j ks := by
  induction n generalizing i j with
  | zero =>
    omega
  | succ m ih =>
    cases m with
    | zero =>
      change Ms 0 i j = ∑ ks : IntermediatePath I 1, pathWeight (le_refl 1) Ms i j ks
      rw [Fintype.sum_unique]
      simp
    | succ k =>
      have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      rw [orderedChannelProd_succ, channelMul_apply]
      have h_rhs :
          (∑ ks : IntermediatePath I (k + 2), pathWeight hn Ms i j ks) =
            ∑ p : IntermediatePath I (k + 1) × I,
              pathWeight hn Ms i j (snocIntermediatePath k p) :=
        (Fintype.sum_equiv (snocIntermediatePath k) _ _ (fun _ => rfl)).symm
      rw [h_rhs, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [ih hk (Fin.init Ms) i x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ks' _ => ?_
      symm
      rw [pathWeight, Fin.prod_univ_castSucc, mul_comm]
      congr 1
      · simp only [pathEdgeEntry]
        have h1 := pathNode_snoc_castSucc k i j x ks' (Fin.last (k + 1))
        rw [pathNode_last] at h1
        have h2 : (Fin.last (k + 1)).succ = Fin.last (k + 2) := rfl
        rw [h1, h2, pathNode_last]
      · rw [pathWeight]
        refine Finset.prod_congr rfl fun r _ => ?_
        simp only [pathEdgeEntry, Fin.init]
        have h_start := pathNode_snoc_castSucc k i j x ks' r.castSucc
        have h_end := pathNode_snoc_castSucc k i j x ks' r.succ
        have hc2 : (r.castSucc).succ = (r.succ).castSucc := Fin.castSucc_succ r
        rw [h_start, hc2, h_end]

theorem pathWeight_eq_zero_iff {I : Type} {n : ℕ} (hn : 1 ≤ n)
    (Ms : Fin n → ChannelMatrix I) (i j : I) (ks : IntermediatePath I n) :
    pathWeight hn Ms i j ks = 0 ↔ PathHasZero hn Ms i j ks := by
  simp [pathWeight, PathHasZero, Finset.prod_eq_zero_iff]

theorem pathWeight_pos_iff {I : Type} {n : ℕ} (hn : 1 ≤ n)
    (Ms : Fin n → ChannelMatrix I) (i j : I) (ks : IntermediatePath I n) :
    0 < pathWeight hn Ms i j ks ↔ PathAllPos hn Ms i j ks := by
  unfold PathAllPos
  rw [pos_iff_ne_zero, not_iff_comm, not_forall]
  simp only [not_lt, nonpos_iff_eq_zero]
  exact (pathWeight_eq_zero_iff hn Ms i j ks).symm

theorem orderedChannelProd_eq_zero_iff_all_paths_hasZero {I : Type} [Fintype I]
    {n : ℕ} (hn : 1 ≤ n) (Ms : Fin n → ChannelMatrix I) (i j : I) :
    orderedChannelProd Ms i j = 0 ↔
      ∀ ks : IntermediatePath I n, PathHasZero hn Ms i j ks := by
  rw [orderedChannelProd_apply_eq_sum_pathWeight hn Ms i j, Finset.sum_eq_zero_iff]
  simp [pathWeight_eq_zero_iff]

theorem orderedChannelProd_pos_iff_exists_pathAllPos {I : Type} [Fintype I]
    {n : ℕ} (hn : 1 ≤ n) (Ms : Fin n → ChannelMatrix I) (i j : I) :
    0 < orderedChannelProd Ms i j ↔
      ∃ ks : IntermediatePath I n, PathAllPos hn Ms i j ks := by
  rw [pos_iff_ne_zero, not_iff_comm, not_exists]
  rw [orderedChannelProd_eq_zero_iff_all_paths_hasZero hn Ms i j]
  constructor
  · intro h_not_pos ks
    have hks := h_not_pos ks
    unfold PathAllPos at hks
    rw [not_forall] at hks
    rcases hks with ⟨m, hm⟩
    exact ⟨m, nonpos_iff_eq_zero.mp (not_lt.mp hm)⟩
  · intro h_zero ks h_all_pos
    rcases h_zero ks with ⟨m, hm⟩
    exact (h_all_pos m).ne' hm

/--
OET anchor: h-e4154c34e95d3c23
**命题（有限矩阵乘积条目的零值判据 (i)）** (HC02-P16)
在正文非空有限算子复合链与各层局部 Lip 证书条件下，
$[\mathbf{L}^{(n)} \cdots \mathbf{L}^{(1)}]_{i \to j} = 0$ 当且仅当每条完整中间指标序列均含至少一个零条目。
-/
theorem lipChain_prod_entry_eq_zero_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {n : ℕ} (hn : 1 ≤ n) (ϕs : Fin n → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (_hU1 : U1 ⊆ dom (orderedOpComp ϕs))
    (Ls : Fin n → ChannelMatrix I)
    (_hLs : ∀ m : Fin n, Ls m ∈ RestrictedLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc))
    (i j : I) :
    orderedChannelProd Ls i j = 0 ↔
      ∀ ks : IntermediatePath I n, PathHasZero hn Ls i j ks :=
  orderedChannelProd_eq_zero_iff_all_paths_hasZero hn Ls i j

/-- $n = 1$ 时 Lip 乘积零值判据退化为单矩阵条目 $[\mathbf{L}^{(1)}]_{i \to j} = 0$ (HC02-P16)。 -/
theorem lipChain_prod_entry_eq_zero_one_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕs : Fin 1 → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (hU1 : U1 ⊆ dom (orderedOpComp ϕs))
    (Ls : Fin 1 → ChannelMatrix I)
    (hLs : ∀ m : Fin 1, Ls m ∈ RestrictedLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc))
    (i j : I) :
    (orderedChannelProd Ls i j = 0 ↔ Ls 0 i j = 0) ∧
      ((∀ ks : IntermediatePath I 1, PathHasZero (le_refl 1) Ls i j ks) ↔ Ls 0 i j = 0) := by
  refine ⟨by rw [orderedChannelProd_one], ?_⟩
  rw [← lipChain_prod_entry_eq_zero_iff d (le_refl 1) ϕs hU1 Ls hLs i j, orderedChannelProd_one]

/--
OET anchor: h-e4154c34e95d3c23
**命题（有限矩阵乘积条目的正值判据 (ii)）** (HC02-P17)
在正文非空有限算子复合链与各层局部 co-Lip 证书条件下，
$[\mathbf{K}^{(n)} \cdots \mathbf{K}^{(1)}]_{i \to j} > 0$ 当且仅当存在至少一条全正完整中间指标路径。
-/
theorem coLipChain_prod_entry_pos_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) {n : ℕ} (hn : 1 ≤ n) (ϕs : Fin n → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (_hU1 : U1 ⊆ dom (orderedOpComp ϕs))
    (Ks : Fin n → ChannelMatrix I)
    (_hKs : ∀ m : Fin n, Ks m ∈ RestrictedCoLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc))
    (i j : I) :
    0 < orderedChannelProd Ks i j ↔
      ∃ ks : IntermediatePath I n, PathAllPos hn Ks i j ks :=
  orderedChannelProd_pos_iff_exists_pathAllPos hn Ks i j

/-- $n = 1$ 时 co-Lip 乘积正值判据由唯一空中间序列退化为 $[\mathbf{K}^{(1)}]_{i \to j} > 0$ (HC02-P17)。 -/
theorem coLipChain_prod_entry_pos_one_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕs : Fin 1 → Operator X bot)
    [∀ i : I, ExtendedPseudoMetric X bot (d i)]
    {U1 : Set X} (hU1 : U1 ⊆ dom (orderedOpComp ϕs))
    (Ks : Fin 1 → ChannelMatrix I)
    (hKs : ∀ m : Fin 1, Ks m ∈ RestrictedCoLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc))
    (i j : I) :
    (0 < orderedChannelProd Ks i j ↔ 0 < Ks 0 i j) ∧
      ((∃ ks : IntermediatePath I 1, PathAllPos (le_refl 1) Ks i j ks) ↔ 0 < Ks 0 i j) := by
  refine ⟨by rw [orderedChannelProd_one], ?_⟩
  rw [← coLipChain_prod_entry_pos_iff d (le_refl 1) ϕs hU1 Ks hKs i j, orderedChannelProd_one]

end

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.matrix_bounds

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

noncomputable section

/-!
## 单通道可行标量族与单通道 Lip 常数 (HC02-D08, HC02-P18 .. HC02-P24)
-/

/-- 分量通道类型：从输入分量 $i \in I$ 到输出分量 $j \in I$ 的有序对 $(i, j) \in I \times I$ (HC02-D07)。 -/
abbrev ComponentChannel (I : Type) : Type := I × I

/--
算子 $\phi$ 在作用域 $U \subseteq \mathrm{dom}(\phi)$ 上关于通道 $(i, j)$ 的单通道可行标量族：
$\mathcal{S}_{i \to j}(\phi; U) := \{\lambda \in \bar{\mathbb{R}}_+ \mid \forall x, y \in U,\; d_j(\phi(x), \phi(y)) \le \lambda \cdot d_i(x, y)\}$ (HC02-D08)。
-/
def SingleChannelFeasibleSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (i j : I) : Set ENNReal :=
  { r : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ r * d i x y }

/--
算子 $\phi$ 在作用域 $U \subseteq \mathrm{dom}(\phi)$ 上关于通道 $(i, j)$ 的单通道 Lip 常数：
$\underline{L}_{i \to j}(\phi; U) := \inf \mathcal{S}_{i \to j}(\phi; U)$，空集下确界按 `ENNReal` 约定为 `⊤` ($+\infty$) (HC02-D08)。
-/
def singleChannelLipConst {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (i j : I) : ENNReal :=
  sInf (SingleChannelFeasibleSet d ϕ U i j)

@[simp]
theorem sInf_empty_ennreal : sInf (∅ : Set ENNReal) = ⊤ :=
  sInf_empty

/--
当存在 $x, y \in U$ 使 $d_i(x, y) = 0 < d_j(\phi(x), \phi(y))$ 时，
不存在任何可行标量常数，可行集合为空且 $\underline{L}_{i \to j}(\phi; U) = +\infty$ (HC02-P18)。
-/
theorem singleChannel_empty_and_top_of_zero_input_pos_output
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_in : d i x y = 0) (h_out : 0 < d j (ϕ.func x) (ϕ.func y)) :
    (∀ r : ENNReal, r ∉ SingleChannelFeasibleSet d ϕ U i j) ∧
      SingleChannelFeasibleSet d ϕ U i j = ∅ ∧
      singleChannelLipConst d ϕ U i j = ⊤ := by
  have h_no : ∀ r : ENNReal, r ∉ SingleChannelFeasibleSet d ϕ U i j := by
    intro r hr
    have hle := hr x hx y hy
    rw [h_in, mul_zero] at hle
    exact (not_lt_of_ge hle) h_out
  have h_empty : SingleChannelFeasibleSet d ϕ U i j = ∅ := by
    ext r
    exact ⟨fun hr => False.elim (h_no r hr), False.elim⟩
  refine ⟨h_no, h_empty, ?_⟩
  simp [singleChannelLipConst, h_empty]

/-- 单通道可行标量族向上封闭：$\lambda_0 \in \mathcal{S}$ 且 $\lambda_1 \ge \lambda_0$ 时 $\lambda_1 \in \mathcal{S}$ (HC02-P20)。 -/
theorem singleChannelFeasibleSet_upward_closed
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {r0 r1 : ENNReal}
    (hr0 : r0 ∈ SingleChannelFeasibleSet d ϕ U i j) (hle : r0 ≤ r1) :
    r1 ∈ SingleChannelFeasibleSet d ϕ U i j := by
  intro x hx y hy
  exact le_trans (hr0 x hx y hy) (mul_le_mul_of_nonneg_right hle (zero_le _))

/-- 在 $0 < a < +\infty$ 语境下，任意严格大于 $a = \underline{L}_{i \to j}(\phi; U)$ 的常数（含 $+\infty$）均属于可行族 (HC02-P21)。 -/
theorem singleChannelFeasibleSet_of_gt_const
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (_ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (_ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤)
    {r : ENNReal} (hr : singleChannelLipConst d ϕ U i j < r) :
    r ∈ SingleChannelFeasibleSet d ϕ U i j := by
  unfold singleChannelLipConst at hr
  rcases sInf_lt_iff.mp hr with ⟨r0, hr0, hr0_lt⟩
  exact singleChannelFeasibleSet_upward_closed d ϕ hU hr0 hr0_lt.le

/--
当 $0 < \underline{L}_{i \to j}(\phi; U) < +\infty$ 时，单通道下确界本身可被取到，
即 $\underline{L}_{i \to j}(\phi; U) \in \mathcal{S}_{i \to j}(\phi; U)$ (HC02-P19)。
-/
theorem singleChannelLipConst_mem_of_pos_lt_top
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤) :
    singleChannelLipConst d ϕ U i j ∈ SingleChannelFeasibleSet d ϕ U i j := by
  set a := singleChannelLipConst d ϕ U i j
  intro x hx y hy
  set A := d j (ϕ.func x) (ϕ.func y)
  set B := d i x y
  by_cases hB0 : B = 0
  · have h_top_mem : (⊤ : ENNReal) ∈ SingleChannelFeasibleSet d ϕ U i j :=
      singleChannelFeasibleSet_of_gt_const d ϕ hU ha_pos ha_lt_top ha_lt_top
    have hA0 : A ≤ (⊤ : ENNReal) * B := h_top_mem x hx y hy
    rw [hB0, mul_zero] at hA0
    exact le_trans hA0 (zero_le _)
  · by_cases hBtop : B = ⊤
    · rw [hBtop, ENNReal.mul_top ha_pos.ne']
      exact le_top
    · have ha1_gt : a < a + 1 := ENNReal.lt_add_right ha_lt_top.ne one_ne_zero
      have ha1_mem : a + 1 ∈ SingleChannelFeasibleSet d ϕ U i j :=
        singleChannelFeasibleSet_of_gt_const d ϕ hU ha_pos ha_lt_top ha1_gt
      have hA_le : A ≤ (a + 1) * B := ha1_mem x hx y hy
      have ha1_ne_top : a + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha_lt_top.ne, ENNReal.one_ne_top⟩
      have hA_ne_top : A ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ha1_ne_top hBtop) hA_le
      have haB_ne_top : a * B ≠ ⊤ := ENNReal.mul_ne_top ha_lt_top.ne hBtop
      rw [← ENNReal.toReal_le_toReal hA_ne_top haB_ne_top, ENNReal.toReal_mul]
      by_contra h_not_le
      push Not at h_not_le
      have hB_real_pos : 0 < B.toReal := ENNReal.toReal_pos hB0 hBtop
      set ε : ℝ := (A.toReal - a.toReal * B.toReal) / (2 * B.toReal)
      have hε_pos : 0 < ε := div_pos (sub_pos.mpr h_not_le) (by linarith)
      have hof_pos : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε_pos
      have hr_gt : a < a + ENNReal.ofReal ε :=
        ENNReal.lt_add_right ha_lt_top.ne hof_pos.ne'
      have hr_mem : a + ENNReal.ofReal ε ∈ SingleChannelFeasibleSet d ϕ U i j :=
        singleChannelFeasibleSet_of_gt_const d ϕ hU ha_pos ha_lt_top hr_gt
      have hr_bound : A ≤ (a + ENNReal.ofReal ε) * B := hr_mem x hx y hy
      have hr_ne_top : a + ENNReal.ofReal ε ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ha_lt_top.ne, ENNReal.ofReal_ne_top⟩
      have hrB_ne_top : (a + ENNReal.ofReal ε) * B ≠ ⊤ :=
        ENNReal.mul_ne_top hr_ne_top hBtop
      have h_real_le : A.toReal ≤ ((a + ENNReal.ofReal ε) * B).toReal :=
        (ENNReal.toReal_le_toReal hA_ne_top hrB_ne_top).mpr hr_bound
      rw [ENNReal.toReal_mul, ENNReal.toReal_add ha_lt_top.ne ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε_pos.le, add_mul] at h_real_le
      have hεB : ε * B.toReal = (A.toReal - a.toReal * B.toReal) / 2 := by
        dsimp [ε]
        field_simp [hB_real_pos.ne']
      linarith

/-- 正有限单通道下确界取到时的显式逐点对标量上界形式 (HC02-P19)。 -/
theorem singleChannelLipConst_bound_of_pos_lt_top
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ singleChannelLipConst d ϕ U i j * d i x y :=
  singleChannelLipConst_mem_of_pos_lt_top d ϕ hU ha_pos ha_lt_top

/--
OET anchor: h-57de7918859a9de2
**注（零下确界给出所有有限正常数界）** (HC02-P22)
当 $\underline{L}_{i \to j}(\phi; U) = 0$ 时，任意 $0 < \lambda < +\infty$ 均属于单通道可行族。
-/
theorem singleChannelFeasibleSet_of_const_eq_zero
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (ha0 : singleChannelLipConst d ϕ U i j = 0)
    {r : ENNReal} (hr_pos : 0 < r) (_hr_lt_top : r < ⊤) :
    r ∈ SingleChannelFeasibleSet d ϕ U i j := by
  have hlt : sInf (SingleChannelFeasibleSet d ϕ U i j) < r := by
    unfold singleChannelLipConst at ha0
    rwa [ha0]
  rcases sInf_lt_iff.mp hlt with ⟨r0, hr0, hr0_lt⟩
  exact singleChannelFeasibleSet_upward_closed d ϕ hU hr0 hr0_lt.le

/--
用于证明零单通道下确界未必在 $\lambda = 0$ 处取到的五点载体空间 (HC02-P23)。
-/
inductive ZeroInfCounterX : Type
  | bot
  | x0
  | x1
  | y0
  | y1
  deriving DecidableEq

/-- 五点反例空间上的扩展伪度量：`y0` 与 `y1` 距离为 `1`，其余相异点对距离均为 `⊤`。 -/
def zeroInfCounterDist (_ : Unit) (p q : ZeroInfCounterX) : ENNReal :=
  match p, q with
  | .bot, .bot => 0
  | .x0, .x0 => 0
  | .x1, .x1 => 0
  | .y0, .y0 => 0
  | .y1, .y1 => 0
  | .y0, .y1 => 1
  | .y1, .y0 => 1
  | _, _ => ⊤

instance zeroInfCounterDist_extendedPseudoMetric :
    ∀ i : Unit, ExtendedPseudoMetric ZeroInfCounterX .bot (zeroInfCounterDist i) := by
  intro _
  refine
    { nonabsorbing := ⟨.x0, by intro h; cases h⟩
      dist_self := fun p => by cases p <;> rfl
      symm := fun p q => by cases p <;> cases q <;> rfl
      triangle := fun p q r => by
        cases p <;> cases q <;> cases r <;> simp [zeroInfCounterDist]
      isolate_bot := fun p hp => by
        cases p with
        | bot => exact False.elim (hp rfl)
        | x0 | x1 | y0 | y1 => rfl }

/-- 五点反例空间上的合法算子：将输入对 `(x0, x1)`（距离 `⊤`）映射为 `(y0, y1)`（距离 `1`）。 -/
def zeroInfCounterOp : Operator ZeroInfCounterX .bot where
  func
    | .bot => .bot
    | .x0 => .y0
    | .x1 => .y1
    | .y0 => .y0
    | .y1 => .y1
  preserves_bot := rfl

/-- 五点反例空间上的非空合法评估域 $U = \{x_0, x_1\} \subseteq \mathrm{dom}(\phi)$。 -/
def zeroInfCounterDomain : Set ZeroInfCounterX := {.x0, .x1}

/--
OET anchor: h-57de7918859a9de2
**反例（零单通道下确界未必由 $0$ 实现）** (HC02-P23)
构造合法扩展规范空间、合法算子 $\phi$ 与非空 $U \subseteq \mathrm{dom}(\phi)$，
使得 $\underline{L}_{i \to j}(\phi; U) = 0$，但 $\lambda = 0$ 不满足相应单通道标量上界。
-/
theorem zeroInfCounter_inf_zero_but_zero_not_feasible :
    zeroInfCounterDomain.Nonempty ∧
      zeroInfCounterDomain ⊆ dom zeroInfCounterOp ∧
      singleChannelLipConst zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () = 0 ∧
      (0 : ENNReal) ∉
        SingleChannelFeasibleSet zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () := by
  have h_ne : zeroInfCounterDomain.Nonempty := ⟨.x0, Or.inl rfl⟩
  have h_dom : zeroInfCounterDomain ⊆ dom zeroInfCounterOp := by
    intro x hx
    rcases hx with rfl | rfl
    · intro h; cases h
    · intro h; cases h
  have h_pos_mem :
      ∀ r : ENNReal, 0 < r →
        r ∈ SingleChannelFeasibleSet zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () := by
    intro r hr x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp [zeroInfCounterOp, zeroInfCounterDist]
    · simp [zeroInfCounterOp, zeroInfCounterDist, ENNReal.mul_top hr.ne']
    · simp [zeroInfCounterOp, zeroInfCounterDist, ENNReal.mul_top hr.ne']
    · simp [zeroInfCounterOp, zeroInfCounterDist]
  have h_inf_zero :
      singleChannelLipConst zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () = 0 := by
    by_contra h_ne_zero
    set a := singleChannelLipConst zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () ()
    have ha_pos : 0 < a := pos_iff_ne_zero.mpr h_ne_zero
    by_cases ha_top : a = ⊤
    · have h1_mem := h_pos_mem 1 zero_lt_one
      have h_le : a ≤ 1 := sInf_le h1_mem
      rw [ha_top] at h_le
      exact ENNReal.one_ne_top (le_antisymm le_top h_le)
    · have ha2_pos : 0 < a / 2 := ENNReal.div_pos ha_pos.ne' (by norm_num)
      have ha2_lt : a / 2 < a := ENNReal.half_lt_self ha_pos.ne' ha_top
      have ha2_mem := h_pos_mem (a / 2) ha2_pos
      exact (not_le_of_gt ha2_lt) (sInf_le ha2_mem)
  have h_zero_not_mem :
      (0 : ENNReal) ∉
        SingleChannelFeasibleSet zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () := by
    intro h0
    have h_bad := h0 .x0 (Or.inl rfl) .x1 (Or.inr rfl)
    simp [zeroInfCounterOp, zeroInfCounterDist] at h_bad
  exact ⟨h_ne, h_dom, h_inf_zero, h_zero_not_mem⟩

/-- 零单通道下确界未必由 $0$ 实现的存在性封装定理 (HC02-P23)。 -/
theorem exists_zero_singleChannelLipConst_not_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ k : I, ExtendedPseudoMetric X bot (d k))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
        singleChannelLipConst d ϕ U i j = 0 ∧
        (0 : ENNReal) ∉ SingleChannelFeasibleSet d ϕ U i j :=
  ⟨ZeroInfCounterX, Unit, .bot, inferInstance, inferInstance,
    zeroInfCounterDist, zeroInfCounterDist_extendedPseudoMetric,
    zeroInfCounterOp, zeroInfCounterDomain, (), (),
    zeroInfCounter_inf_zero_but_zero_not_feasible⟩

/--
用于说明单通道常数 $\underline{L}_{i \to j}(\phi; U)$ 与合法 Lip 矩阵条目 $[\mathbf{L}]_{i \to j}$ 为不同对象的双分量见证空间 (HC02-D08)。
-/
def twoBitDist (i : Bool) (p q : Option (Bool × Bool)) : ENNReal :=
  match p, q with
  | none, none => 0
  | some u, some v =>
    match i with
    | false => if u.1 = v.1 then 0 else 1
    | true => if u.2 = v.2 then 0 else 1
  | _, _ => ⊤

instance twoBitDist_extendedPseudoMetric :
    ∀ i : Bool, ExtendedPseudoMetric (Option (Bool × Bool)) none (twoBitDist i) := by
  intro i
  refine
    { nonabsorbing := ⟨some (false, false), by intro h; cases h⟩
      dist_self := fun p => by
        cases p with
        | none => rfl
        | some u => cases i <;> simp [twoBitDist]
      symm := fun p q => by
        cases p <;> cases q <;> cases i <;> simp [twoBitDist, eq_comm]
      triangle := fun p q r => by
        cases p with
        | none =>
          cases q <;> cases r <;> simp [twoBitDist]
        | some u =>
          cases r with
          | none =>
            cases q <;> simp [twoBitDist]
          | some w =>
            cases q with
            | none =>
              simp [twoBitDist]
            | some v =>
              rcases u with ⟨u1, u2⟩
              rcases v with ⟨v1, v2⟩
              rcases w with ⟨w1, w2⟩
              cases i <;>
                cases u1 <;> cases v1 <;> cases w1 <;>
                cases u2 <;> cases v2 <;> cases w2 <;>
                simp [twoBitDist]
      isolate_bot := fun p hp => by
        cases p with
        | none => exact False.elim (hp rfl)
        | some _ => rfl }

/-- 单通道常数 $\underline{L}_{i \to j}(\phi; U)$ 不等于一般合法 Lip 矩阵条目 $[\mathbf{L}]_{i \to j}$ 的具体见证 (HC02-D08)。 -/
theorem singleChannelLipConst_ne_lipMatrix_entry_witness :
    let ϕ : Operator (Option (Bool × Bool)) none := idOperator
    let U : Set (Option (Bool × Bool)) := dom ϕ
    channelId Bool ∈ RestrictedLipCertSet twoBitDist ϕ U ∧
      channelId Bool false true = 0 ∧
      singleChannelLipConst twoBitDist ϕ U false true = ⊤ ∧
      singleChannelLipConst twoBitDist ϕ U false true ≠ channelId Bool false true := by
  intro ϕ U
  have h_id_mem : channelId Bool ∈ RestrictedLipCertSet twoBitDist ϕ U := by
    refine ⟨Set.Subset.rfl, ?_⟩
    intro x _ y _ j
    rw [sum_channelId_mul_dist]
    exact le_rfl
  have h_off : channelId Bool false true = 0 :=
    channelId_offDiag (by intro h; cases h)
  have hx : some (false, false) ∈ U := by intro h; cases h
  have hy : some (false, true) ∈ U := by intro h; cases h
  have h_empty : SingleChannelFeasibleSet twoBitDist ϕ U false true = ∅ := by
    ext r
    refine ⟨fun hr => ?_, False.elim⟩
    have hle := hr _ hx _ hy
    simp [ϕ, idOperator, twoBitDist] at hle
  have h_top : singleChannelLipConst twoBitDist ϕ U false true = ⊤ := by
    simp [singleChannelLipConst, h_empty]
  refine ⟨h_id_mem, h_off, h_top, ?_⟩
  rw [h_top, h_off]
  exact ENNReal.top_ne_zero

/--
OET anchor: h-57de7918859a9de2
**注（单通道常数有限当且仅当存在有限可行标量常数）** (HC02-P24)
-/
theorem singleChannelLipConst_lt_top_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) (i j : I) :
    singleChannelLipConst d ϕ U i j < ⊤ ↔
      ∃ r : ENNReal, r < ⊤ ∧ r ∈ SingleChannelFeasibleSet d ϕ U i j := by
  constructor
  · intro ha_lt_top
    by_cases ha0 : singleChannelLipConst d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact singleChannelFeasibleSet_of_const_eq_zero d ϕ hU ha0 zero_lt_one ENNReal.one_lt_top
    · have ha_pos : 0 < singleChannelLipConst d ϕ U i j := pos_iff_ne_zero.mpr ha0
      exact ⟨singleChannelLipConst d ϕ U i j, ha_lt_top,
        singleChannelLipConst_mem_of_pos_lt_top d ϕ hU ha_pos ha_lt_top⟩
  · rintro ⟨r, hr_lt_top, hr_mem⟩
    exact lt_of_le_of_lt (sInf_le hr_mem) hr_lt_top

/-!
## 通道隔离、行/列解耦、对角体系与分辨保持 (HC02-D07, HC02-P25 .. HC02-P32)
-/

/-- 上界矩阵证书在通道 $(i, j)$ 处通道隔离：$L_{i \to j} = 0$ (HC02-D07)。 -/
def IsChannelIsolated {I : Type} (L : ChannelMatrix I) (i j : I) : Prop :=
  L i j = 0

/-- co-Lip 证书在通道 $(i, j)$ 处给出正下界传递：$K_{i \to j} > 0$ (HC02-D07)。 -/
def HasPosCoLipChannel {I : Type} (K : ChannelMatrix I) (i j : I) : Prop :=
  0 < K i j

/-- 单行稀疏谓词 `Row(L, i, j)`：固定输出行 $j$，除输入位置 $i$ 外其余条目全为 $0$ ($\forall k \ne i, L_{k \to j} = 0$) (HC02-D07)。 -/
def IsRowSparseAt {I : Type} (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- 矩阵关于输出分量 $j$ 行解耦：存在某个输入分量 $i \in I$ 使 `IsRowSparseAt L i j` 成立 (HC02-D07)。 -/
def IsRowDecoupledMatrix {I : Type} (L : ChannelMatrix I) (j : I) : Prop :=
  ∃ i : I, IsRowSparseAt L i j

/-- 算子 $\phi$ 在 $U$ 上关于输出分量 $d_j$ 行解耦：存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 使第 $j$ 行至多一项非零 (HC02-D07)。 -/
def IsRowDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (j : I) : Prop :=
  ∃ L ∈ RestrictedLipCertSet d ϕ U, IsRowDecoupledMatrix L j

/-- 单列稀疏谓词 `Col(L, i, j)`：固定输入列 $i$，除输出位置 $j$ 外其余条目全为 $0$ ($\forall k \ne j, L_{i \to k} = 0$) (HC02-D07)。 -/
def IsColSparseAt {I : Type} (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/-- 矩阵关于输入分量 $i$ 列解耦：存在某个输出分量 $j \in I$ 使 `IsColSparseAt L i j` 成立 (HC02-D07)。 -/
def IsColDecoupledMatrix {I : Type} (L : ChannelMatrix I) (i : I) : Prop :=
  ∃ j : I, IsColSparseAt L i j

/-- 算子 $\phi$ 在 $U$ 上关于输入分量 $d_i$ 列解耦：存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 使第 $i$ 列至多一项非零 (HC02-D07)。 -/
def IsColDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (i : I) : Prop :=
  ∃ L ∈ RestrictedLipCertSet d ϕ U, IsColDecoupledMatrix L i

/-- 对角通道矩阵（完全解耦体系证书）：所有非对角条目全为 $0$ ($\forall i \ne j, L_{i \to j} = 0$) (HC02-D07)。 -/
def IsDiagonalChannelMatrix {I : Type} (L : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- 给出完全解耦体系的合法受限上界证书谓词 (HC02-D07)。 -/
def IsFullyDecoupledCert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  L ∈ RestrictedLipCertSet d ϕ U ∧ IsDiagonalChannelMatrix L

theorem isDiagonalChannelMatrix_iff_forall_rowSparseAt {I : Type} (L : ChannelMatrix I) :
    IsDiagonalChannelMatrix L ↔ ∀ j : I, IsRowSparseAt L j j :=
  ⟨fun h j k hk => h k j hk, fun h i j hij => h j i hij⟩

/--
当 $L_{i \to j} = 0$ 时，允许任意扩展实数距离值（含 $d_i = +\infty$）下乘积项 $L_{i \to j} \cdot v = 0$ (HC02-P25)。
-/
theorem zero_coeff_mul_eq_zero {I : Type} {L : ChannelMatrix I} {i j : I}
    (h_iso : IsChannelIsolated L i j) (v : ENNReal) :
    L i j * v = 0 := by
  rw [h_iso, zero_mul]

/--
当 $L_{i \to j} = 0$ 时，输出分量 $j$ 的证书求和可删除输入项 $i$（允许 $d_i(x, y) = +\infty$）(HC02-P25)。
-/
theorem restrictedLip_sum_erase_of_zero_coeff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I} (hL : L ∈ RestrictedLipCertSet d ϕ U)
    {i j : I} (h_iso : IsChannelIsolated L i j) :
    (∀ x y : X, L i j * d i x y = 0) ∧
      (∀ x y : X, (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y) ∧
      (∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y) := by
  have h_term : ∀ x y : X, L i j * d i x y = 0 :=
    fun x y => zero_coeff_mul_eq_zero h_iso (d i x y)
  have h_sum : ∀ x y : X, (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
    intro x y
    rw [← Finset.add_sum_erase Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i),
      h_term x y, zero_add]
  refine ⟨h_term, h_sum, ?_⟩
  intro x hx y hy
  rw [← h_sum x y]
  exact hL.2 x hx y hy j

/--
任意唯一可能非零输入位置 $i$（不必有 $i = j$）下的单行化简：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 且 $\forall k \ne i, L_{k \to j} = 0$，
则 $\forall x, y \in U,\; d_j(\phi(x), \phi(y)) \le L_{i \to j} \cdot d_i(x, y)$ (HC02-P26)。
-/
theorem restrictedLip_bound_of_rowSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I} (hL : L ∈ RestrictedLipCertSet d ϕ U)
    {i j : I} (h_row : IsRowSparseAt L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have h := hL.2 x hx y hy j
  rwa [Fintype.sum_eq_single i (fun k hk => by rw [h_row k hk, zero_mul])] at h

/-- 行解耦算子存在给出单输入分量标量上界的受限证书 (HC02-P26)。 -/
theorem exists_single_input_bound_of_rowDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {j : I} (h_dec : IsRowDecoupled d ϕ U j) :
    ∃ L ∈ RestrictedLipCertSet d ϕ U, ∃ i : I,
      IsRowSparseAt L i j ∧ ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  rcases h_dec with ⟨L, hL, i, h_row⟩
  exact ⟨L, hL, i, h_row, restrictedLip_bound_of_rowSparseAt d ϕ hL h_row⟩

/--
任意单列支撑证书的贡献范围：若固定输入 $i$ 列仅输出 $j$ 可能非零（`IsColSparseAt L i j`），
则对一切 $k \ne j$ 恒有 $L_{i \to k} d_i(x, y) = 0$，该证书中输入 $i$ 至多向输出 $j$ 的上界贡献非零项 (HC02-P27)。
-/
theorem colSparseAt_contribution_range {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I} (hL : L ∈ RestrictedLipCertSet d ϕ U)
    {i j : I} (h_col : IsColSparseAt L i j) :
    (∀ k : I, k ≠ j → ∀ x y : X, L i k * d i x y = 0) ∧
      (∀ k : I, ∀ x y : X, L i k * d i x y ≠ 0 → k = j) ∧
      (∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y) := by
  have h_zero : ∀ k : I, k ≠ j → ∀ x y : X, L i k * d i x y = 0 := by
    intro k hkj x y
    rw [h_col k hkj, zero_mul]
  have h_only_j : ∀ k : I, ∀ x y : X, L i k * d i x y ≠ 0 → k = j := by
    intro k x y h_ne
    by_contra hkj
    exact h_ne (h_zero k hkj x y)
  refine ⟨h_zero, h_only_j, ?_⟩
  intro k hkj x hx y hy
  exact (restrictedLip_sum_erase_of_zero_coeff d ϕ hL (h_col k hkj)).2.2 x hx y hy

/--
完全解耦（对角）Lip 矩阵给出所有分量的独立标量放缩上界 (HC02-P28)。
-/
theorem diagonalLip_componentwise_upper_bounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U) (h_diag : IsDiagonalChannelMatrix L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact restrictedLip_bound_of_rowSparseAt d ϕ hL (fun k hk => h_diag k j hk)

/-- 任一合法受限 co-Lip 矩阵在任意通道 $(i, j)$ 上均给出单输入项下界 $K_{i \to j} d_i(x, y) \le d_j(\phi(x), \phi(y))$。 -/
theorem restrictedCoLip_single_channel_lower_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {K : ChannelMatrix I} (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  calc
    K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
OET anchor: h-6a98a58b5bc95360
**引理（对角输入项的标量双侧界）** (HC02-P29)
仅假设 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 在输出行 $j$ 满足 $\forall k \ne j, L_{k \to j} = 0$，
以及一般合法 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$（无需假设 $\mathbf{K}$ 行稀疏），
即得 $K_{j \to j} d_j(x, y) \le d_j(\phi(x), \phi(y)) \le L_{j \to j} d_j(x, y)$。
-/
theorem scalar_two_sided_bound_of_diag_lip_row {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {j : I}
    {L K : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U)
    (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (h_row : IsRowSparseAt L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  exact ⟨restrictedCoLip_single_channel_lower_bound d ϕ hK j j x hx y hy,
    restrictedLip_bound_of_rowSparseAt d ϕ hL h_row x hx y hy⟩

/--
当对角输入项 Lip 行条件对所有 $j \in I$ 成立时，全部分量同时满足标量双侧不等式 (HC02-P30)。
-/
theorem componentwise_two_sided_bounds_of_all_diag_lip_rows
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L K : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U)
    (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (h_rows : ∀ j : I, IsRowSparseAt L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  fun j => scalar_two_sided_bound_of_diag_lip_row d ϕ hL hK (h_rows j)

/--
逐分量双侧界的有限标量系数分支：若另有 $\forall j \in I,\; L_{j \to j}, K_{j \to j} < +\infty$，
则可提取有限非负实数标量族 `k_fin l_fin : I → NNReal` 实现全部分量的有限标量双侧放缩界 (HC02-P30)。
-/
theorem finite_componentwise_two_sided_bounds
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L K : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U)
    (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (h_rows : ∀ j : I, IsRowSparseAt L j j)
    (h_fin : ∀ j : I, L j j < ⊤ ∧ K j j < ⊤) :
    ∃ (k_fin l_fin : I → NNReal),
      (∀ j : I, (k_fin j : ENNReal) = K j j ∧ (l_fin j : ENNReal) = L j j) ∧
      (∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
        (k_fin j : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ (l_fin j : ENNReal) * d j x y) := by
  refine ⟨fun j => (K j j).toNNReal, fun j => (L j j).toNNReal, ?_, ?_⟩
  · intro j
    exact ⟨ENNReal.coe_toNNReal (h_fin j).2.ne, ENNReal.coe_toNNReal (h_fin j).1.ne⟩
  · intro j x hx y hy
    rw [ENNReal.coe_toNNReal (h_fin j).2.ne, ENNReal.coe_toNNReal (h_fin j).1.ne]
    exact componentwise_two_sided_bounds_of_all_diag_lip_rows d ϕ hL hK h_rows j x hx y hy

/--
OET anchor: h-f82672ec0dd48f28
**命题（正 co-Lip 通道的可分辨保持 (i)）** (HC02-P31)
若 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且 $K_{i \to j} > 0$，
则对任意 $x, y \in U$，$d_i(x, y) > 0 \Rightarrow d_j(\phi(x), \phi(y)) > 0$。
-/
theorem pos_coLip_channel_preserves_distinguishability
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {K : ChannelMatrix I} (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    {i j : I} (hK_pos : HasPosCoLipChannel K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hd_pos
  have h_prod_pos : 0 < K i j * d i x y := ENNReal.mul_pos hK_pos.ne' hd_pos.ne'
  exact lt_of_lt_of_le h_prod_pos
    (restrictedCoLip_single_channel_lower_bound d ϕ hK i j x hx y hy)

/--
OET anchor: h-f82672ec0dd48f28
**命题（正 co-Lip 对角通道反射族零距关系 (ii)）** (HC02-P32)
若 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且对所有 $j \in I$ 有 $K_{j \to j} > 0$，
则对任意 $x, y \in U$，$\phi(x) \sim_{\mathcal{G}} \phi(y) \Rightarrow x \sim_{\mathcal{G}} y$。
-/
theorem pos_diag_coLip_reflects_gaugeZeroRelated
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {K : ChannelMatrix I} (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (hK_diag : ∀ j : I, HasPosCoLipChannel K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy h_img_zero j
  by_contra h_ne
  have hd_pos : 0 < d j x y := pos_iff_ne_zero.mpr h_ne
  have h_out_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_coLip_channel_preserves_distinguishability d ϕ hK (hK_diag j) x hx y hy hd_pos
  exact h_out_pos.ne' (h_img_zero j)

end

end formal_oet.vol_01.ch_02_operator_bounds
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipCertSet"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.RestrictedLipCertSet"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipCertSet_dom_eq"
        }
      ],
      "representation": "在有限非空指标集 `[Fintype I] [Nonempty I]`、扩展伪度量族 `[∀ i : I, ExtendedPseudoMetric X bot (d i)]` 与保持 `bot` 的算子 `ϕ : Operator X bot` 下，定义全域证书集合 `LipCertSet d ϕ`（对所有 `x, y ∈ dom ϕ` 与 `j : I`，`d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y`）与子集受限证书集合 `RestrictedLipCertSet d ϕ U`（包含 `U ⊆ dom ϕ` 及 `U` 上全部点对的距离上界不等式），系数与距离均取 `ENNReal`，并证 `RestrictedLipCertSet d ϕ (dom ϕ) = LipCertSet d ϕ`。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.RestrictedCoLipCertSet"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.GlobalCoLipCertSet"
        }
      ],
      "representation": "定义受限 co-Lipschitz 证书族 `RestrictedCoLipCertSet d ϕ U`，显式包含非空性 `U.Nonempty`、定义域条件 `U ⊆ dom ϕ` 以及对所有 `x, y ∈ U` 和 `j : I` 的下界不等式 `(∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)`；矩阵条目类型为 `ENNReal`，故 `0` 与 `⊤`（`+∞`）均为合法系数；`GlobalCoLipCertSet` 为 `U = dom ϕ` 时的简记。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ChannelMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.displayMatrixEquiv"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_apply"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelMul"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_channelMul"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelMul_assoc"
        }
      ],
      "representation": "`ChannelMatrix I := I → I → ENNReal` 采用输入优先存储，`M i j` 表示 $M_{i \\to j}$（输入分量 `i` 到输出分量 `j`）；`toDisplayMatrix` 与 `displayMatrixEquiv` 建立与常规行列矩阵 `Matrix I I ENNReal` 的双射对应，满足第 `j` 行第 `i` 列条目 `toDisplayMatrix M j i = M i j`；`channelMul M2 M1 i j = ∑ k : I, M2 k j * M1 i k`，且 `toDisplayMatrix_channelMul` 证明其与普通矩阵乘法严格一致。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelId"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelId_diag"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelId_offDiag"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_channelId"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedChannelProd"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedChannelProd_zero"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedChannelProd_one"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedChannelProd_succ"
        }
      ],
      "representation": "`channelId I` 定义 Kronecker 单位矩阵 $\\delta_{ij}$ 并证左右单位元性质及与 `1 : Matrix I I ENNReal` 的对应；对按施行顺序 $\\phi_1, \\dots, \\phi_k$ 索引的矩阵族 `Ms : Fin k → ChannelMatrix I`，`orderedChannelProd` 将 $k=0$ 空乘积定义为 `channelId I`，$k=1$ 定义为唯一矩阵 `Ms 0`，递推式 `orderedChannelProd_succ` 对应有序连乘 $\\mathbf{L}_k \\cdots \\mathbf{L}_1$。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.idOperator"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.opComp"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedOpComp"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedOpComp_eq_operatorChain"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain_subset_dom"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain_last_eq_composite_image"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LocalLipChain"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LocalLipChain.mkOfStepBounds"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LocalCoLipChain"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LocalCoLipChain.mkOfStepBounds"
        }
      ],
      "representation": "`orderedOpComp` 定义施行顺序下的复合算子 $c_k = \\phi_k \\circ \\cdots \\circ \\phi_1$ 并证明与第1章 `OperatorChain` 逆序列表相等；`chainDomain` 递归定义 $U_1$ 与 $U_{m+1} = \\phi_m(U_m)$；`chainDomain_subset_dom` 由 $U_1 \\subseteq \\mathrm{dom}(c_k)$ 证明每步 $U_m \\subseteq \\mathrm{dom}(\\phi_m)$，`chainDomain_last_eq_composite_image` 证明全复合像 $c_k(U_1)$ 等于逐次终端像 $U_{k+1}$；`LocalLipChain` 与 `LocalCoLipChain`（含构造子 `mkOfStepBounds`）仅由起始域条件、逐步矩阵和各实际输入域 $U_m$ 上的单步不等式构造，不含任何最终复合界字段。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IntermediatePath"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.emptyIntermediatePath"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.intermediatePath_one_unique"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.intermediatePath_one_eq_empty"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathNode"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathEdgeEntry"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathAllPos"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathHasZero"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedChannelProd_apply_eq_sum_pathWeight"
        }
      ],
      "representation": "对 $n \\ge 1$，`IntermediatePath I n := Fin (n - 1) → I` 遍历无任何正性约束的全部中间指标序列 $(k_1, \\dots, k_{n-1})$；`pathNode` 固定端点 $k_0 = i, k_n = j$；`pathWeight` 定义各层条目乘积 $\\prod_{m=1}^n [\\mathbf{M}^{(m)}]_{k_{m-1} \\to k_m}$ 并由 `orderedChannelProd_apply_eq_sum_pathWeight` 证明乘积展开公式；`PathAllPos` 表示所有单步条目 $> 0$，`PathHasZero` 表示存在某层单步条目 $= 0$；当 $n = 1$ 时由 `intermediatePath_one_unique` 证明存在唯一空中间序列。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsChannelIsolated"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.HasPosCoLipChannel"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowSparseAt"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowDecoupledMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowDecoupled"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColSparseAt"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColDecoupledMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColDecoupled"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagonalChannelMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsFullyDecoupledCert"
        }
      ],
      "representation": "`ComponentChannel I := I × I` 表示输入到输出的分量通道；`IsRowSparseAt L i j` 定义 `∀ k ≠ i, L k j = 0`，`IsRowDecoupledMatrix L j := ∃ i, IsRowSparseAt L i j` 与算子级 `IsRowDecoupled` 刻画行解耦；`IsColSparseAt L i j` 定义 `∀ k ≠ j, L i k = 0`，`IsColDecoupledMatrix L i := ∃ j, IsColSparseAt L i j` 与算子级 `IsColDecoupled` 刻画列解耦；`IsDiagonalChannelMatrix L` 定义 `∀ i ≠ j, L i j = 0`（对角矩阵/完全解耦体系）。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.SingleChannelFeasibleSet"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.sInf_empty_ennreal"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_ne_lipMatrix_entry_witness"
        }
      ],
      "representation": "定义单通道可行标量集合 `SingleChannelFeasibleSet d ϕ U i j := { r : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ r * d i x y }` 及其下确界 `singleChannelLipConst d ϕ U i j := sInf (SingleChannelFeasibleSet d ϕ U i j)`，`sInf_empty_ennreal` 核验空集下确界为 `⊤`（`+∞`）；不将其等同于任何矩阵条目，并由 `singleChannelLipConst_ne_lipMatrix_entry_witness` 给出二者严格相异的具体双分量见证。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipCertSet_singleton_iff"
        }
      ],
      "representation": "在单分量条件 `∀ k : I, k = i`（即 $I = \\{i\\}$）下，证明 `L ∈ LipCertSet d ϕ` 当且仅当对所有 `x, y ∈ dom ϕ` 成立标量不等式 `d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipCertSet_subset_restricted"
        }
      ],
      "representation": "证明当 `U ⊆ dom ϕ` 时，`LipCertSet d ϕ ⊆ RestrictedLipCertSet d ϕ U`，即全域合法 Lip 证书在任意定义域子集上保持合法。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipCertSet_subset_of_subset"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipCertSet_antitone"
        }
      ],
      "representation": "证明当 `U ⊆ V` 且 `V ⊆ dom ϕ` 时（以及无需单独显式传入 `V ⊆ dom ϕ` 的反调版本），`RestrictedLipCertSet d ϕ V ⊆ RestrictedLipCertSet d ϕ U`。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.entryLipInf"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.entryLipInf_mono"
        }
      ],
      "representation": "定义受限证书族在通道 `(i, j)` 上的逐条目下确界 `entryLipInf d ϕ U i j := sInf ((fun M => M i j) '' RestrictedLipCertSet d ϕ U)`，并证明当 `U ⊆ V` 时 `entryLipInf d ϕ U i j ≤ entryLipInf d ϕ V i j`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLip_comp"
        }
      ],
      "representation": "证明对复合算子 `opComp ϕ2 ϕ1` 与 `U1 ⊆ dom (opComp ϕ2 ϕ1)`，记实际像集 `U2 = operator_image ϕ1 U1`，若 `L1 ∈ RestrictedLipCertSet d ϕ1 U1` 且 `L2 ∈ RestrictedLipCertSet d ϕ2 U2`，则 `channelMul L2 L1 ∈ RestrictedLipCertSet d (opComp ϕ2 ϕ1) U1`。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D05"
      ]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.globalCoLip_entry_eq_zero_of_collapse"
        }
      ],
      "representation": "证明若存在 `x, y ∈ dom ϕ` 满足 `d j (ϕ.func x) (ϕ.func y) = 0` 且 `0 < d i x y`，则任意全域 co-Lip 证书 `K ∈ RestrictedCoLipCertSet d ϕ (dom ϕ)` 必满足 `K i j = 0`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedCoLip_comp"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedCoLip_comp_with_nonempty"
        }
      ],
      "representation": "在与 P05 相同的起始域 `U1 ⊆ dom (opComp ϕ2 ϕ1)` 与实际像集 `operator_image ϕ1 U1` 下，若 `K1`、`K2` 分别为对应域上的合法受限 co-Lip 矩阵，证明 `channelMul K2 K1 ∈ RestrictedCoLipCertSet d (opComp ϕ2 ϕ1) U1` 且 `U1.Nonempty`。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D05"
      ]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.commonDom"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_forward"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_forward_two_mul"
        }
      ],
      "representation": "设 `U ⊆ commonDom ϕ1 ϕ2`（即 `dom ϕ1 ∩ dom ϕ2`），且对所有 `z ∈ U`、`j : I` 有 `d j (ϕ1.func z) (ϕ2.func z) ≤ δ j`，由伪度量对称性与三角不等式证明对任意 `x, y ∈ U`、`j : I` 有 `d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j`（并给出等价的 `+ 2 * δ j` 形式）。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_backward"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pairwise_image_dist_perturb_backward_two_mul"
        }
      ],
      "representation": "在与 P08 相同的公共定义域和逐点像距扰动前提下，交换 `ϕ1, ϕ2` 证明对任意 `x, y ∈ U`、`j : I` 有 `d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + δ j + δ j`（及等价的 `+ 2 * δ j` 形式）。",
      "dependencies": [
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_bridge_of_perturb"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_bridge_of_perturb_symm"
        }
      ],
      "representation": "在点对像距扰动前提及 `L1 ∈ RestrictedLipCertSet d ϕ1 U` 下，证明对所有 `x, y ∈ U`、`j : I` 有 `d j (ϕ2.func x) (ϕ2.func y) ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j`，并同时给出交换 `ϕ1, ϕ2` 后的对称桥接定理。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_bridge_of_perturb"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_bridge_of_perturb_symm"
        }
      ],
      "representation": "在点对像距扰动前提及 `K1 ∈ RestrictedCoLipCertSet d ϕ1 U` 下，证明对所有 `x, y ∈ U`、`j : I` 有 `(∑ i : I, K1 i j * d i x y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j`，并同时给出交换 `ϕ1, ϕ2` 后的对称桥接定理。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.finite_comp_restrictedLip"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LocalLipChain.composite_cert"
        }
      ],
      "representation": "对任意正长度 `1 ≤ k` 的算子序列 `ϕs : Fin k → Operator X bot`、`U1 ⊆ dom (orderedOpComp ϕs)` 与递归像集 `chainDomain ϕs U1`，若每步 `Ls m ∈ RestrictedLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc)`，通过有限归纳证明有序连乘 `orderedChannelProd Ls ∈ RestrictedLipCertSet d (orderedOpComp ϕs) U1`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.finite_comp_restrictedCoLip"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LocalCoLipChain.composite_cert"
        }
      ],
      "representation": "对任意正长度 `1 ≤ k` 的算子序列、`U1 ⊆ dom (orderedOpComp ϕs)` 与递归像集 `chainDomain ϕs U1`，若每步 `Ks m ∈ RestrictedCoLipCertSet d (ϕs m) (chainDomain ϕs U1 m.castSucc)`（含各步非空性），通过有限归纳证明 `orderedChannelProd Ks ∈ RestrictedCoLipCertSet d (orderedOpComp ϕs) U1`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_id_restrictedLip"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_chain_restrictedLip"
        }
      ],
      "representation": "在边界情形 $k = 0$、$c_0 = \\mathrm{id}_{\\mathcal{X}}$（`idOperator` / `orderedOpComp (k := 0)`）下，对任意非空 `U.Nonempty` 且 `U ⊆ dom idOperator`，证明单位矩阵 `channelId I`（即空乘积 `orderedChannelProd`）属于 `RestrictedLipCertSet d idOperator U`。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D04",
        "HC02-D05"
      ]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_id_restrictedCoLip"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_chain_restrictedCoLip"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_id_mem_lip_inter_coLip"
        }
      ],
      "representation": "在同一非空 `U ⊆ dom idOperator` 上，证明单位矩阵 `channelId I` 属于 `RestrictedCoLipCertSet d idOperator U`，并给出零步链形式及属于 `RestrictedLipCertSet ∩ RestrictedCoLipCertSet` 的交集定理。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03",
        "HC02-D04",
        "HC02-D05",
        "HC02-P14"
      ]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedChannelProd_eq_zero_iff_all_paths_hasZero"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChain_prod_entry_eq_zero_iff"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChain_prod_entry_eq_zero_one_iff"
        }
      ],
      "representation": "在正文非空算子复合链 `1 ≤ n`、`U1 ⊆ dom (orderedOpComp ϕs)` 及实际中间域上的局部 Lip 证书序列 `Ls` 条件下，证明 `orderedChannelProd Ls i j = 0` 当且仅当对所有完整中间路径 `ks : IntermediatePath I n` 成立 `PathHasZero hn Ls i j ks`；并由 `lipChain_prod_entry_eq_zero_one_iff` 证明 $n = 1$ 时退化为 `Ls 0 i j = 0`。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedChannelProd_pos_iff_exists_pathAllPos"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChain_prod_entry_pos_iff"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/matrix_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChain_prod_entry_pos_one_iff"
        }
      ],
      "representation": "在同一正文非空算子链与实际中间域上的局部 co-Lip 证书序列 `Ks` 条件下，证明 `0 < orderedChannelProd Ks i j` 当且仅当存在完整中间路径 `ks : IntermediatePath I n` 满足 `PathAllPos hn Ks i j ks`；并由 `coLipChain_prod_entry_pos_one_iff` 证明 $n = 1$ 时对应唯一空中间序列退化为 `0 < Ks 0 i j`。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D04",
        "HC02-D05",
        "HC02-D06",
        "HC02-P16"
      ]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannel_empty_and_top_of_zero_input_pos_output"
        }
      ],
      "representation": "在 `U ⊆ dom ϕ` 下，若存在 `x, y ∈ U` 使得 `d i x y = 0` 且 `0 < d j (ϕ.func x) (ϕ.func y)`，证明不存在任何 `r : ENNReal` 属于可行标量族，`SingleChannelFeasibleSet d ϕ U i j = ∅` 且 `singleChannelLipConst d ϕ U i j = ⊤`。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_mem_of_pos_lt_top"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_bound_of_pos_lt_top"
        }
      ],
      "representation": "在 `U ⊆ dom ϕ` 下，若 `a := singleChannelLipConst d ϕ U i j` 满足 `0 < a` 且 `a < ⊤`，分 `d i x y = 0`、`d i x y = ⊤` 与 `0 < d i x y < ⊤` 三种情形证明 `a ∈ SingleChannelFeasibleSet d ϕ U i j`，即对所有 `x, y ∈ U` 成立 `d j (ϕ.func x) (ϕ.func y) ≤ a * d i x y`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasibleSet_upward_closed"
        }
      ],
      "representation": "在 `U ⊆ dom ϕ` 下，证明若 `r0 ∈ SingleChannelFeasibleSet d ϕ U i j` 且 `r0 ≤ r1`，则 `r1 ∈ SingleChannelFeasibleSet d ϕ U i j`（向上封闭性）。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasibleSet_of_gt_const"
        }
      ],
      "representation": "在 `U ⊆ dom ϕ` 及 `0 < a < ⊤`（`a = singleChannelLipConst d ϕ U i j`）语境下，对任意 `r : ENNReal` 满足 `a < r`（允许 `r = ⊤`），由下确界性质与向上封闭性证明 `r ∈ SingleChannelFeasibleSet d ϕ U i j`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasibleSet_of_const_eq_zero"
        }
      ],
      "representation": "在 `U ⊆ dom ϕ` 下，若 `singleChannelLipConst d ϕ U i j = 0`，证明任意满足 `0 < r` 且 `r < ⊤` 的有限正数 `r : ENNReal` 均属于 `SingleChannelFeasibleSet d ϕ U i j`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ZeroInfCounterX"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroInfCounterDist"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroInfCounterDist_extendedPseudoMetric"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroInfCounterOp"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroInfCounterDomain"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroInfCounter_inf_zero_but_zero_not_feasible"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.exists_zero_singleChannelLipConst_not_attained"
        }
      ],
      "representation": "显式构造五点载体空间 `ZeroInfCounterX`、满足全部扩展伪度量公理的 `zeroInfCounterDist`（输入对 `(x0, x1)` 距离为 `⊤`，输出对 `(y0, y1)` 距离为 `1`）、保 `bot` 算子 `zeroInfCounterOp` 及非空子集 `zeroInfCounterDomain = {x0, x1} ⊆ dom zeroInfCounterOp`，证明单通道下确界为 `0`，但因 `0 * ⊤ = 0 < 1` 故 `0 ∉ SingleChannelFeasibleSet`。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConst_lt_top_iff"
        }
      ],
      "representation": "在 `U ⊆ dom ϕ` 下，利用 P19（正有限下确界取到）与 P22（零下确界给出有限正常数）证明 `singleChannelLipConst d ϕ U i j < ⊤` 当且仅当存在 `r < ⊤` 属于 `SingleChannelFeasibleSet d ϕ U i j`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_coeff_mul_eq_zero"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLip_sum_erase_of_zero_coeff"
        }
      ],
      "representation": "证明当 `IsChannelIsolated L i j`（即 `L i j = 0`）时，对任意 `ENNReal` 距离（含 `d i x y = ⊤`）均有 `L i j * d i x y = 0`，且在受限 Lip 证书 `L` 对输出 `j` 的求和中可直接删去输入项 `i`（求和域缩减为 `Finset.univ.erase i`）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D07"
      ]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLip_bound_of_rowSparseAt"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.exists_single_input_bound_of_rowDecoupled"
        }
      ],
      "representation": "对任意 `L ∈ RestrictedLipCertSet d ϕ U` 及任意指标对 `i, j : I`（不要求 `i = j`），证明在单行稀疏条件 `IsRowSparseAt L i j`（`∀ k ≠ i, L k j = 0`）下，对所有 `x, y ∈ U` 成立 `d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.colSparseAt_contribution_range"
        }
      ],
      "representation": "对 `L ∈ RestrictedLipCertSet d ϕ U` 与单列稀疏条件 `IsColSparseAt L i j`（固定输入列 `i` 满足 `∀ k ≠ j, L i k = 0`），证明对一切 `k ≠ j` 及任意 `x, y` 有 `L i k * d i x y = 0`、若 `L i k * d i x y ≠ 0` 则必有 `k = j`，且每个其余输出分量 `k ≠ j` 的上界求和均可剔除输入 `i`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.diagonalLip_componentwise_upper_bounds"
        }
      ],
      "representation": "证明若 `L ∈ RestrictedLipCertSet d ϕ U` 为对角矩阵（`IsDiagonalChannelMatrix L`），则对所有 `j : I` 与所有 `x, y ∈ U` 成立 `d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedCoLip_single_channel_lower_bound"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound_of_diag_lip_row"
        }
      ],
      "representation": "给定 `L ∈ RestrictedLipCertSet d ϕ U` 与 `K ∈ RestrictedCoLipCertSet d ϕ U`，仅假设 `L` 在输出分量 `j` 行满足对角行稀疏 `IsRowSparseAt L j j`（不对 `K` 附加任何稀疏性假设），证明对所有 `x, y ∈ U` 成立双侧界 `K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y`。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.componentwise_two_sided_bounds_of_all_diag_lip_rows"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.finite_componentwise_two_sided_bounds"
        }
      ],
      "representation": "证明当 `∀ j : I, IsRowSparseAt L j j` 成立时，全部分量同时满足标量双侧界；若进一步有 `∀ j : I, L j j < ⊤ ∧ K j j < ⊤`，则 `finite_componentwise_two_sided_bounds` 提取有限标量族 `k_fin l_fin : I → NNReal` 给出有限标量双侧放缩界。",
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pos_coLip_channel_preserves_distinguishability"
        }
      ],
      "representation": "证明若 `K ∈ RestrictedCoLipCertSet d ϕ U` 且 `HasPosCoLipChannel K i j`（即 `0 < K i j`），则对所有 `x, y ∈ U`，`0 < d i x y` 蕴含 `0 < d j (ϕ.func x) (ϕ.func y)`。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D07",
        "HC02-P29"
      ]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/channel_decoupling.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pos_diag_coLip_reflects_gaugeZeroRelated"
        }
      ],
      "representation": "证明若 `K ∈ RestrictedCoLipCertSet d ϕ U` 且对所有 `j : I` 有 `HasPosCoLipChannel K j j`（`0 < K j j`），则对所有 `x, y ∈ U`，`GaugeZeroRelated d (ϕ.func x) (ϕ.func y)` 蕴含 `GaugeZeroRelated d x y`（反射族零距关系 $\\sim_{\\mathcal{G}}$）。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D07",
        "HC02-P31"
      ]
    }
  ]
}
```

### 完成与严格对齐声明

- **整章完成与严格对齐情况**：已经**完整完成且严格对齐**第2章（[02-operator-bounds.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/source/02-operator-bounds.md)）的全部数学定义、记号对应、命题、引理、推论及全部正文注记/无独立编号事实，覆盖 [obligations.json](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/HCH02/physical-1/session/work/obligations.json) 中全部 40 项义务（`HC02-D01` 至 `HC02-D08`、`HC02-P01` 至 `HC02-P32`），40 项状态均为 `complete`。
- **内核与公理核验**：全部目标模块在指定 Lean 4.29.1 与固定 Mathlib（`5e932f97dd25535344f80f9dd8da3aab83df0fe6`）环境下零错误、零警告通过内核类型检查；未使用任何 `sorry`、`admit`、自定义公理或跳过内核检查的机制，经 `CollectAxioms` 核验所有声明仅依赖标准逻辑公理 `{propext, Classical.choice, Quot.sound}`。
- **未完成或未确认的范围**：**无**（没有任何未完成项、降级项或未确认范围）。
