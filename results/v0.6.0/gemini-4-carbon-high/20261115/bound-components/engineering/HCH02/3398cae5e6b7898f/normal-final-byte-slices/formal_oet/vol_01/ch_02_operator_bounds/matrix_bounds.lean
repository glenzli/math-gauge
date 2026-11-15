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
