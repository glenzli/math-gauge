import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Fin
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal Classical

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

/-!
======================================================================
HC02-D03: 输入输出指标、显示矩阵和乘法
======================================================================
输入优先存储 M i j 代表输入 i 到输出 j；
普通矩阵第 j 行第 i 列对应条目 M i j；
复合 (M2 M1) i j = ∑ k, M2 k j * M1 i k。
-/

/-- 输入优先存储矩阵：M i j 代表从输入分量 i 到输出分量 j 的界 -/
abbrev BoundMatrix (I : Type) := I → I → ENNReal

/-- 普通矩阵表示：第 j 行为输出分量，第 i 列为输入分量，条目为 M i j -/
def matrixEntry {I : Type} (M : BoundMatrix I) (row_j col_i : I) : ENNReal :=
  M col_i row_j

/-- 矩阵代数乘法：(M2 · M1)_{i → j} = ∑_{k ∈ I} (M2)_{k → j} * (M1)_{i → k} -/
noncomputable def mul {I : Type} [Fintype I] (M2 M1 : BoundMatrix I) : BoundMatrix I :=
  fun i j => ∑ k : I, M2 k j * M1 i k

theorem matrix_mul_assoc {I : Type} [Fintype I] (M3 M2 M1 : BoundMatrix I) :
    mul (mul M3 M2) M1 = mul M3 (mul M2 M1) := by
  ext i j
  dsimp [mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1 with k
  congr 1 with l
  rw [_root_.mul_assoc]

/-!
======================================================================
HC02-D04: 单位矩阵、空乘积和有序乘积
======================================================================
单位矩阵 δ_ij；空乘积为单位；施行顺序 ϕ_1, ..., ϕ_k 对应 L_k ... L_1；
k=1 乘积等于唯一矩阵。
-/

/-- 单位矩阵：δ_{ij} -/
def idMatrix {I : Type} [DecidableEq I] : BoundMatrix I :=
  fun i j => if i = j then 1 else 0

@[simp]
theorem idMatrix_mul {I : Type} [Fintype I] [DecidableEq I] (M : BoundMatrix I) :
    mul idMatrix M = M := by
  ext i j
  dsimp [mul, idMatrix]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [hkj]
  · intro hj; exact False.elim (hj (Finset.mem_univ j))

@[simp]
theorem mul_idMatrix {I : Type} [Fintype I] [DecidableEq I] (M : BoundMatrix I) :
    mul M idMatrix = M := by
  ext i j
  dsimp [mul, idMatrix]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki; simp [Ne.symm hki]
  · intro hi; exact False.elim (hi (Finset.mem_univ i))

/-- 沿施行顺序 [M_1, ..., M_k] 的有序矩阵乘积：空乘积为单位，[M_1, ..., M_k] 给出 M_k ... M_1 -/
noncomputable def chainMatrix {I : Type} [Fintype I] [DecidableEq I] :
    List (BoundMatrix I) → BoundMatrix I
  | [] => idMatrix
  | M :: Ms => mul (chainMatrix Ms) M

@[simp]
theorem chainMatrix_nil {I : Type} [Fintype I] [DecidableEq I] :
    chainMatrix ([] : List (BoundMatrix I)) = idMatrix := rfl

theorem chainMatrix_singleton {I : Type} [Fintype I] [DecidableEq I] (M : BoundMatrix I) :
    chainMatrix [M] = M := by
  dsimp [chainMatrix]
  exact idMatrix_mul M

/-!
======================================================================
HC02-D01: 全域及受限 Lip 矩阵与证书族
======================================================================
在有限非空 I、扩展伪度量族 d 与保持 bot 的 ϕ 下，
定义 Set 族 L(ϕ) 及 L(ϕ)|_U；U ⊆ dom ϕ，∀ x, y ∈ U 及 ∀ j，输出距 ≤ ∑_i L_ij d_i；
所有系数和距离为 ENNReal。
-/

def LipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom ϕ ∧ ∀ x y, x ∈ U → y ∈ U → ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

def LipMatrixDom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : BoundMatrix I) : Prop :=
  LipMatrix d ϕ (dom ϕ) L

def LipCertFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  { L | LipMatrix d ϕ U L }

def LipCertFamilyDom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (BoundMatrix I) :=
  { L | LipMatrixDom d ϕ L }

/-!
======================================================================
HC02-D02: 含非空性的 co-Lip 矩阵与证书族
======================================================================
定义 K(ϕ)|_U，包含 U ≠ ∅、U ⊆ dom ϕ 及 ∀ x, y ∈ U、j，∑_i K_ij d_i ≤ 输出距；
0 和 ∞ 均合法系数。
-/

def CoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x y, x ∈ U → y ∈ U → ∀ j : I, (∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)

def CoLipCertFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  { K | CoLipMatrix d ϕ U K }

/-!
======================================================================
HC02-D07: 分量通道、任意单行/单列稀疏和对角
======================================================================
通道 I × I。
单行稀疏 Row(L, i, j): ∀ k ≠ i, L_kj = 0；正文行解耦为 ∃ i, Row(L, i, j)。
单列 Col(L, i, j): ∀ k ≠ j, L_ik = 0；列解耦为 ∃ j, Col(L, i, j)。
对角为 ∀ i ≠ j, L_ij = 0。
-/

abbrev Channel (I : Type) := I × I

def RowSparse {I : Type} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

def IsRowDecoupled {I : Type} (L : BoundMatrix I) (j : I) : Prop :=
  ∃ i : I, RowSparse L i j

def ColSparse {I : Type} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

def IsColDecoupled {I : Type} (L : BoundMatrix I) (i : I) : Prop :=
  ∃ j : I, ColSparse L i j

def IsDiagonal {I : Type} (L : BoundMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-!
======================================================================
HC02-D08: 单通道可行标量族及其下确界
======================================================================
对 U ⊆ dom ϕ，S_ij = { λ ∈ ENNReal : ∀ x, y ∈ U, d_j(ϕ x, ϕ y) ≤ λ d_i(x, y) }；
a_ij = sInf S_ij，sInf ∅ = ∞。不把 a_ij 等同于任意矩阵条目。
-/

def S_channel {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { c | ∀ x y, x ∈ U → y ∈ U → d j (ϕ.func x) (ϕ.func y) ≤ c * d i x y }

noncomputable def single_channel_lip {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (S_channel d ϕ U i j)

/-!
======================================================================
HC02-P01: 单分量矩阵界退化
======================================================================
I = {i} 时，合法 Lip 界为 d_i(ϕ x, ϕ y) ≤ L_ii d_i(x, y)。
-/
theorem lip_matrix_unique_index {X I : Type} {bot : X} [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I)
    (hL : LipMatrix d ϕ U L) (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d default (ϕ.func x) (ϕ.func y) ≤ L default default * d default x y := by
  have h := hL.2 x y hx hy default
  rw [Fintype.sum_unique] at h
  exact h

/-!
======================================================================
HC02-P02: 全域 Lip 证书可限制
======================================================================
U ⊆ dom ϕ 时 L(ϕ) ⊆ L(ϕ)|_U。
-/
theorem lip_matrix_restrict {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I)
    (hU : U ⊆ dom ϕ) (hL : LipMatrixDom d ϕ L) :
    LipMatrix d ϕ U L := by
  refine ⟨hU, ?_⟩
  intro x y hx hy j
  exact hL.2 x y (hU hx) (hU hy) j

/-!
======================================================================
HC02-P03: 缩小评估域扩大 Lip 证书族
======================================================================
U ⊆ V ⊆ dom ϕ 时 L(ϕ)|_V ⊆ L(ϕ)|_U。
-/
theorem lip_matrix_monotone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X} (L : BoundMatrix I)
    (hUV : U ⊆ V) (hL : LipMatrix d ϕ V L) :
    LipMatrix d ϕ U L := by
  refine ⟨hUV.trans hL.1, ?_⟩
  intro x y hx hy j
  exact hL.2 x y (hUV hx) (hUV hy) j

/-!
======================================================================
HC02-P04: 逐条目下确界不增
======================================================================
定义 a_ij(U) = inf { M_ij : M ∈ L(ϕ)|_U }；U ⊆ V 时 a_ij(U) ≤ a_ij(V)。
-/
noncomputable def entry_sInf {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun M : BoundMatrix I => M i j) '' { M | LipMatrix d ϕ U M })

theorem entry_sInf_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X} (i j : I)
    (hUV : U ⊆ V) :
    entry_sInf d ϕ U i j ≤ entry_sInf d ϕ V i j := by
  apply sInf_le_sInf
  rintro _ ⟨M, hM, rfl⟩
  exact ⟨M, lip_matrix_monotone d ϕ M hUV hM, rfl⟩

/-!
======================================================================
算子复合与 HC02-P05: 两步 Lip 复合
======================================================================
U1 ⊆ dom(ϕ2 ∘ ϕ1)，U2 = ϕ1(U1)，L1 在 U1、L2 在 U2 合法，则 L2 · L1 在 U1 合法。
-/
def comp {X : Type} {bot : X} (ϕ2 ϕ1 : Operator X bot) : Operator X bot :=
  ⟨ϕ2.func ∘ ϕ1.func, by
    have h1 : ϕ1.func bot = bot := ϕ1.preserves_bot
    have h2 : ϕ2.func bot = bot := ϕ2.preserves_bot
    dsimp; rw [h1, h2]⟩

theorem lip_matrix_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (L1 L2 : BoundMatrix I)
    (hU1 : U1 ⊆ dom (comp ϕ2 ϕ1))
    (hL1 : LipMatrix d ϕ1 U1 L1)
    (hL2 : LipMatrix d ϕ2 (ϕ1.func '' U1) L2) :
    LipMatrix d (comp ϕ2 ϕ1) U1 (mul L2 L1) := by
  refine ⟨hU1, ?_⟩
  intro x y hx hy j
  dsimp [comp]
  have hx_im : ϕ1.func x ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hx
  have hy_im : ϕ1.func y ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hy
  have h2 := hL2.2 (ϕ1.func x) (ϕ1.func y) hx_im hy_im j
  have h_sum_le : (∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y)) ≤
      ∑ i : I, (mul L2 L1) i j * d i x y := by
    dsimp [mul]
    have h_step : (∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y)) ≤
        ∑ k : I, L2 k j * (∑ i : I, L1 i k * d i x y) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_right (hL1.2 x y hx hy k) (L2 k j)
    refine le_trans h_step ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    apply le_of_eq
    congr 1 with k
    rw [_root_.mul_assoc]
  exact le_trans h2 h_sum_le

/-!
======================================================================
HC02-P06: 输出零距迫使 co-Lip 条目为 0
======================================================================
若 dom ϕ 上有 x, y 使 d_j(ϕ x, ϕ y) = 0 且 d_i(x, y) > 0，则任意全域 K 均有 K_ij = 0。
-/
theorem colip_entry_zero_of_dist_zero {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (K : BoundMatrix I)
    (hK : CoLipMatrix d ϕ (dom ϕ) K) {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    (i j : I) (h_out : d j (ϕ.func x) (ϕ.func y) = 0) (h_in : d i x y > 0) :
    K i j = 0 := by
  have h := hK.2.2 x y hx hy j
  rw [h_out] at h
  have h_term_le : K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h_prod_zero : K i j * d i x y = 0 :=
    le_antisymm (le_trans h_term_le h) (zero_le _)
  cases mul_eq_zero.mp h_prod_zero with
  | inl hKij => exact hKij
  | inr hdi => exact False.elim (lt_irrefl 0 (hdi ▸ h_in))

/-!
======================================================================
HC02-P07: 两步 co-Lip 复合
======================================================================
与 P05 同实际像域；两步 K 均合法，则 K2 · K1 在 U1 合法且 U1 非空。
-/
theorem colip_matrix_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (K1 K2 : BoundMatrix I)
    (hU1 : U1 ⊆ dom (comp ϕ2 ϕ1))
    (hK1 : CoLipMatrix d ϕ1 U1 K1)
    (hK2 : CoLipMatrix d ϕ2 (ϕ1.func '' U1) K2) :
    CoLipMatrix d (comp ϕ2 ϕ1) U1 (mul K2 K1) := by
  refine ⟨hK1.1, hU1, ?_⟩
  intro x y hx hy j
  dsimp [comp]
  have hx_im : ϕ1.func x ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hx
  have hy_im : ϕ1.func y ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hy
  have h2 := hK2.2.2 (ϕ1.func x) (ϕ1.func y) hx_im hy_im j
  have h_sum_le : (∑ i : I, (mul K2 K1) i j * d i x y) ≤
      ∑ k : I, K2 k j * d k (ϕ1.func x) (ϕ1.func y) := by
    dsimp [mul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro k _
    have heq : (∑ i : I, K2 k j * K1 i k * d i x y) = K2 k j * (∑ i : I, K1 i k * d i x y) := by
      rw [Finset.mul_sum]
      congr 1 with i
      rw [_root_.mul_assoc]
    rw [heq]
    exact mul_le_mul_right (hK1.2.2 x y hx hy k) (K2 k j)
  exact le_trans h_sum_le h2

/-!
======================================================================
HC02-P08 & P09: 两个算子的点对像距扰动界
======================================================================
U ⊆ dom(ϕ1, ϕ2)，∀ z ∈ U, j, d_j(ϕ1 z, ϕ2 z) ≤ δ_j，则：
(P08) d_j(ϕ2 x, ϕ2 y) ≤ d_j(ϕ1 x, ϕ1 y) + δ_j + δ_j；
(P09) d_j(ϕ1 x, ϕ1 y) ≤ d_j(ϕ2 x, ϕ2 y) + δ_j + δ_j。
-/
theorem dist_perturbation_forward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (δ : I → ENNReal)
    (h_dist : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j := by
  have h1 : d j (ϕ2.func x) (ϕ2.func y) ≤
      d j (ϕ2.func x) (ϕ1.func x) + d j (ϕ1.func x) (ϕ2.func y) :=
    triangle j (ϕ2.func x) (ϕ1.func x) (ϕ2.func y)
  have h2 : d j (ϕ1.func x) (ϕ2.func y) ≤
      d j (ϕ1.func x) (ϕ1.func y) + d j (ϕ1.func y) (ϕ2.func y) :=
    triangle j (ϕ1.func x) (ϕ1.func y) (ϕ2.func y)
  have h_bound_x : d j (ϕ2.func x) (ϕ1.func x) ≤ δ j := by
    rw [symm j]
    exact h_dist x hx j
  have h_bound_y : d j (ϕ1.func y) (ϕ2.func y) ≤ δ j :=
    h_dist y hy j
  have hc : d j (ϕ1.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + δ j :=
    le_trans h2 (add_le_add_right h_bound_y _)
  have ha : d j (ϕ2.func x) (ϕ2.func y) ≤ δ j + (d j (ϕ1.func x) (ϕ1.func y) + δ j) :=
    le_trans h1 (add_le_add h_bound_x hc)
  have heq : δ j + (d j (ϕ1.func x) (ϕ1.func y) + δ j) = d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j := by
    rw [← add_assoc, add_comm (δ j) (d j (ϕ1.func x) (ϕ1.func y)), add_assoc]
  rw [heq] at ha
  exact ha

theorem dist_perturbation_backward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (δ : I → ENNReal)
    (h_dist : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + δ j + δ j := by
  have h_rev : ∀ z ∈ U, ∀ j : I, d j (ϕ2.func z) (ϕ1.func z) ≤ δ j := by
    intro z hz i
    rw [symm i]
    exact h_dist z hz i
  exact dist_perturbation_forward d symm triangle ϕ2 ϕ1 U δ h_rev hx hy j

/-!
======================================================================
HC02-P10: 扰动 Lip 加性界
======================================================================
另有 L1 ∈ L(ϕ1)|_U，则 d_j(ϕ2 x, ϕ2 y) ≤ ∑_i L1_ij d_i(x, y) + 2 δ_j。
-/
theorem lip_perturbation_bridge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (L1 : BoundMatrix I) (δ : I → ENNReal)
    (h_dist : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    (hL1 : LipMatrix d ϕ1 U L1)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ2.func x) (ϕ2.func y) ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j := by
  have h_pert := dist_perturbation_forward d symm triangle ϕ1 ϕ2 U δ h_dist hx hy j
  have h_lip := hL1.2 x y hx hy j
  have h_two : δ j + δ j = 2 * δ j := by rw [two_mul]
  have h_comb : d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j =
      d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
    rw [add_assoc, h_two]
  rw [h_comb] at h_pert
  exact le_trans h_pert (add_le_add_left h_lip (2 * δ j))

/-!
======================================================================
HC02-P11: 扰动 co-Lip 加性界
======================================================================
另有 K1 ∈ K(ϕ1)|_U，则 ∑_i K1_ij d_i(x, y) ≤ d_j(ϕ2 x, ϕ2 y) + 2 δ_j。
-/
theorem colip_perturbation_bridge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (K1 : BoundMatrix I) (δ : I → ENNReal)
    (h_dist : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    (hK1 : CoLipMatrix d ϕ1 U K1)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i : I, K1 i j * d i x y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
  have h_colip := hK1.2.2 x y hx hy j
  have h_back := dist_perturbation_backward d symm triangle ϕ1 ϕ2 U δ h_dist hx hy j
  have h_two : δ j + δ j = 2 * δ j := by rw [two_mul]
  have h_comb : d j (ϕ2.func x) (ϕ2.func y) + δ j + δ j =
      d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
    rw [add_assoc, h_two]
  rw [h_comb] at h_back
  exact le_trans h_colip h_back

/-!
======================================================================
HC02-P14 & P15: 零步单位证书
======================================================================
k = 0, c_0 = id；对非空 U ⊆ dom id，单位矩阵为合法 Lip 与 co-Lip 矩阵。
-/
def id_operator (X : Type) (bot : X) : Operator X bot :=
  ⟨id, rfl⟩

theorem id_lip_matrix {X I : Type} (bot : X) [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (U : Set X) (hU : U ⊆ dom (id_operator X bot)) :
    LipMatrix d (id_operator X bot) U idMatrix := by
  refine ⟨hU, ?_⟩
  intro x y hx hy j
  dsimp [id_operator, idMatrix]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [hkj]
  · intro hj; exact False.elim (hj (Finset.mem_univ j))

theorem id_colip_matrix {X I : Type} (bot : X) [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (U : Set X)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (id_operator X bot)) :
    CoLipMatrix d (id_operator X bot) U idMatrix := by
  refine ⟨hU_ne, hU, ?_⟩
  intro x y hx hy j
  dsimp [id_operator, idMatrix]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [hkj]
  · intro hj; exact False.elim (hj (Finset.mem_univ j))

/-!
======================================================================
HC02-D05: 实际像域与原文逐步数据的链表示
======================================================================
U_{m+1} = ϕ_m(U_m)，U_1 ⊆ dom c_k；证明每个 U_m ⊆ dom ϕ_m 及全复合像等于逐次像。
由逐步矩阵和各实际输入域上的界构造目标链，禁止以最终复合界为字段。
-/

def evalChain {X : Type} (bot : X) : List (Operator X bot) → Operator X bot
  | [] => id_operator X bot
  | ϕ :: ϕs => comp (evalChain bot ϕs) ϕ

def intermediateSets {X : Type} (bot : X) : List (Operator X bot) → Set X → List (Set X)
  | [], U => [U]
  | ϕ :: ϕs, U => U :: intermediateSets bot ϕs (ϕ.func '' U)

theorem chain_image_eq {X : Type} (bot : X) :
    ∀ (ϕs : List (Operator X bot)) (U1 : Set X),
      (evalChain bot ϕs).func '' U1 = (intermediateSets bot ϕs U1).getLast (by
        cases ϕs <;> simp [intermediateSets]) := by
  intro ϕs
  induction ϕs with
  | nil =>
    intro U1
    dsimp [evalChain, id_operator, intermediateSets]
    simp
  | cons ϕ rest ih =>
    intro U1
    dsimp [evalChain, comp, intermediateSets]
    rw [Set.image_comp]
    rw [ih (ϕ.func '' U1)]
    cases rest with
    | nil => rfl
    | cons ψ rest2 => rfl

theorem dom_sub_of_comp_sub {X : Type} {bot : X}
    (ϕ1 ϕ2 : Operator X bot) {U : Set X} (hU : U ⊆ dom (comp ϕ2 ϕ1)) :
    U ⊆ dom ϕ1 ∧ ϕ1.func '' U ⊆ dom ϕ2 := by
  constructor
  · intro x hx hbot
    have hcomp : (comp ϕ2 ϕ1).func x = bot := by
      dsimp [comp]
      rw [hbot, ϕ2.preserves_bot]
    exact (hU hx) hcomp
  · rintro _ ⟨x, hx, rfl⟩ hbot
    exact (hU hx) hbot

theorem intermediateSets_length {X : Type} (bot : X) (ϕs : List (Operator X bot)) (U : Set X) :
    (intermediateSets bot ϕs U).length = ϕs.length + 1 := by
  induction ϕs generalizing U with
  | nil => rfl
  | cons ϕ rest ih =>
    dsimp [intermediateSets]
    rw [ih]

theorem each_step_dom {X : Type} (bot : X) :
    ∀ (ϕs : List (Operator X bot)) (U1 : Set X),
      U1 ⊆ dom (evalChain bot ϕs) →
      ∀ (m : ℕ) (h_lt : m < ϕs.length),
        (intermediateSets bot ϕs U1).get ⟨m, by
          rw [intermediateSets_length]
          omega⟩ ⊆ dom (ϕs.get ⟨m, h_lt⟩) := by
  intro ϕs
  induction ϕs with
  | nil => intro U1 _ m h_lt; contradiction
  | cons ϕ rest ih =>
    intro U1 hU m h_lt
    cases m with
    | zero =>
      dsimp [evalChain] at hU
      have ⟨h1, _⟩ := dom_sub_of_comp_sub ϕ (evalChain bot rest) hU
      dsimp [intermediateSets]
      exact h1
    | succ m' =>
      dsimp [evalChain] at hU
      have ⟨_, h2⟩ := dom_sub_of_comp_sub ϕ (evalChain bot rest) hU
      have h_lt' : m' < rest.length := Nat.succ_lt_succ_iff.mp h_lt
      have ih_res := ih (ϕ.func '' U1) h2 m' h_lt'
      dsimp [intermediateSets]
      exact ih_res

/-- 逐步局部 Lip 矩阵界目标链（字段仅包含每步局部界，禁止以最终复合界为字段） -/
inductive LipStepChain {X I : Type} (bot : X) [Fintype I]
    (d : I → X → X → ENNReal) :
    Set X → List (Operator X bot) → List (BoundMatrix I) → Type
  | nil (U : Set X) : LipStepChain bot d U [] []
  | cons (ϕ : Operator X bot) (M : BoundMatrix I)
         {U : Set X} {ϕs : List (Operator X bot)} {Ms : List (BoundMatrix I)}
         (hM : LipMatrix d ϕ U M)
         (rest : LipStepChain bot d (ϕ.func '' U) ϕs Ms) :
      LipStepChain bot d U (ϕ :: ϕs) (M :: Ms)

/-- 逐步局部 co-Lip 矩阵界目标链（字段仅包含每步局部界，禁止以最终复合界为字段） -/
inductive CoLipStepChain {X I : Type} (bot : X) [Fintype I]
    (d : I → X → X → ENNReal) :
    Set X → List (Operator X bot) → List (BoundMatrix I) → Type
  | nil (U : Set X) (hU : U.Nonempty) : CoLipStepChain bot d U [] []
  | cons (ϕ : Operator X bot) (K : BoundMatrix I)
         {U : Set X} {ϕs : List (Operator X bot)} {Ks : List (BoundMatrix I)}
         (hK : CoLipMatrix d ϕ U K)
         (rest : CoLipStepChain bot d (ϕ.func '' U) ϕs Ks) :
      CoLipStepChain bot d U (ϕ :: ϕs) (K :: Ks)

/-!
======================================================================
HC02-P12 & P13: 任意正长度链的指定 Lip/co-Lip 乘积
======================================================================
k ≥ 1，U_{m+1} = ϕ_m(U_m)，每步 L_m 在实际 U_m 上合法，则 L_k ... L_1 在 U_1 上界 c_k；
K_m 类似下界 c_k。
-/
theorem lip_chain_bound {X I : Type} (bot : X) [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U1 : Set X} {ϕs : List (Operator X bot)} {Ls : List (BoundMatrix I)}
    (chain : LipStepChain bot d U1 ϕs Ls) (h_dom : U1 ⊆ dom (evalChain bot ϕs)) :
    LipMatrix d (evalChain bot ϕs) U1 (chainMatrix Ls) := by
  induction chain with
  | nil U =>
    dsimp [evalChain, chainMatrix]
    exact id_lip_matrix bot d U h_dom
  | cons ϕ M hM rest ih =>
    dsimp [evalChain, chainMatrix]
    have ⟨_, h_rest_dom⟩ := dom_sub_of_comp_sub ϕ (evalChain bot _) h_dom
    have ih_bound := ih h_rest_dom
    exact lip_matrix_comp d ϕ (evalChain bot _) _ M (chainMatrix _) h_dom hM ih_bound

theorem colip_chain_bound {X I : Type} (bot : X) [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U1 : Set X} {ϕs : List (Operator X bot)} {Ks : List (BoundMatrix I)}
    (chain : CoLipStepChain bot d U1 ϕs Ks) (h_dom : U1 ⊆ dom (evalChain bot ϕs)) :
    CoLipMatrix d (evalChain bot ϕs) U1 (chainMatrix Ks) := by
  induction chain with
  | nil U hU_ne =>
    dsimp [evalChain, chainMatrix]
    exact id_colip_matrix bot d U hU_ne h_dom
  | cons ϕ K hK rest ih =>
    dsimp [evalChain, chainMatrix]
    have ⟨_, h_rest_dom⟩ := dom_sub_of_comp_sub ϕ (evalChain bot _) h_dom
    have ih_bound := ih h_rest_dom
    exact colip_matrix_comp d ϕ (evalChain bot _) _ K (chainMatrix _) h_dom hK ih_bound

/-!
======================================================================
HC02-D06: 全部有限索引路径与全正/含零谓词
======================================================================
n ≥ 1，固定 k_0 = i、k_n = j，遍历所有中间指标序列，无正性约束。
权重为各层条目的乘积；全正是所有边 > 0，含零是某边 = 0。n = 1 只有一个空中间序列。
-/

def fullPath {I : Type} (n : ℕ) (i j : I) (seq : Fin (n - 1) → I) (k : Fin (n + 1)) : I :=
  if hk0 : k.val = 0 then i
  else if hkn : k.val = n then j
  else
    have h1 : k.val - 1 < n - 1 := by
      have hk_lt := k.isLt
      omega
    seq ⟨k.val - 1, h1⟩

noncomputable def pathEdge {I : Type} (Ms : List (BoundMatrix I)) (n : ℕ) (i j : I)
    (seq : Fin (n - 1) → I) (m : Fin n) : ENNReal :=
  if h : m.val < Ms.length then
    let stepMat := Ms.get ⟨m.val, h⟩
    let from_idx := fullPath n i j seq ⟨m.val, by omega⟩
    let to_idx := fullPath n i j seq ⟨m.val + 1, by omega⟩
    stepMat from_idx to_idx
  else 0

noncomputable def pathWeight {I : Type} (Ms : List (BoundMatrix I)) (n : ℕ) (i j : I)
    (seq : Fin (n - 1) → I) : ENNReal :=
  ∏ m : Fin n, pathEdge Ms n i j seq m

def PathAllPositive {I : Type} (Ms : List (BoundMatrix I)) (n : ℕ) (i j : I)
    (seq : Fin (n - 1) → I) : Prop :=
  ∀ m : Fin n, pathEdge Ms n i j seq m > 0

def PathHasZero {I : Type} (Ms : List (BoundMatrix I)) (n : ℕ) (i j : I)
    (seq : Fin (n - 1) → I) : Prop :=
  ∃ m : Fin n, pathEdge Ms n i j seq m = 0

noncomputable def pathWeightSum {I : Type} [Fintype I]
    (Ms : List (BoundMatrix I)) (n : ℕ) (i j : I) : ENNReal :=
  ∑ seq : Fin (n - 1) → I, pathWeight Ms n i j seq

theorem chainMatrix_one_eq_weightSum {I : Type} [Fintype I] [DecidableEq I]
    (M : BoundMatrix I) (i j : I) :
    chainMatrix [M] i j = pathWeightSum [M] 1 i j := by
  dsimp [chainMatrix, mul, idMatrix, pathWeightSum, pathWeight]
  have h_sum : (∑ k : I, (if k = j then 1 else 0) * M i k) = M i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj; simp [hkj]
    · intro hj; exact False.elim (hj (Finset.mem_univ j))
  rw [h_sum]
  haveI : Unique (Fin 0 → I) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique]
  rw [Fin.prod_univ_one]
  dsimp [pathEdge, fullPath]

/-!
======================================================================
HC02-P16: Lip 乘积零值判据
======================================================================
在正文同一非空算子链和实际证书序列条件下，(L_n ... L_1)_ij = 0 iff
每个完整中间索引序列含至少一个零条目；n = 1 退化为 L_1_ij = 0。
-/
theorem lip_chainMatrix_zero_iff {I : Type} [Fintype I]
    (Ls : List (BoundMatrix I)) (n : ℕ) (i j : I) :
    pathWeightSum Ls n i j = 0 ↔ ∀ seq : Fin (n - 1) → I, PathHasZero Ls n i j seq := by
  dsimp [pathWeightSum, PathHasZero, pathWeight]
  rw [Finset.sum_eq_zero_iff]
  simp [Finset.prod_eq_zero_iff]

theorem lip_one_zero_iff {I : Type} [Fintype I] [DecidableEq I]
    (L1 : BoundMatrix I) (i j : I) :
    chainMatrix [L1] i j = 0 ↔ L1 i j = 0 := by
  rw [chainMatrix_one_eq_weightSum]
  dsimp [pathWeightSum, pathWeight]
  haveI : Unique (Fin 0 → I) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique, Fin.prod_univ_one]
  dsimp [pathEdge, fullPath]
  rfl

/-!
======================================================================
HC02-P17: co-Lip 乘积正值判据
======================================================================
同一正文条件，(K_n ... K_1)_ij > 0 iff 存在完整路径每条边 > 0；
n = 1 是唯一空中间序列对应 K_1_ij > 0。
-/
theorem colip_chainMatrix_pos_iff {I : Type} [Fintype I]
    (Ks : List (BoundMatrix I)) (n : ℕ) (i j : I) :
    0 < pathWeightSum Ks n i j ↔ ∃ seq : Fin (n - 1) → I, PathAllPositive Ks n i j seq := by
  dsimp [pathWeightSum, PathAllPositive, pathWeight]
  rw [pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff]
  push Not
  simp_rw [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨seq, hseq⟩
    refine ⟨seq, ?_⟩
    intro m
    rw [ne_eq, Finset.prod_eq_zero_iff] at hseq
    push Not at hseq
    exact pos_iff_ne_zero.mpr (hseq m (Finset.mem_univ m))
  · rintro ⟨seq, hseq⟩
    refine ⟨seq, ?_⟩
    rw [ne_eq, Finset.prod_eq_zero_iff]
    push Not
    intro m _
    exact ne_of_gt (hseq m)

theorem colip_one_pos_iff {I : Type} [Fintype I] [DecidableEq I]
    (K1 : BoundMatrix I) (i j : I) :
    chainMatrix [K1] i j > 0 ↔ K1 i j > 0 := by
  rw [chainMatrix_one_eq_weightSum]
  dsimp [pathWeightSum, pathWeight]
  haveI : Unique (Fin 0 → I) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique, Fin.prod_univ_one]
  dsimp [pathEdge, fullPath]
  rfl

/-!
======================================================================
HC02-P18: 零输入距而正输出距使可行族为空
======================================================================
若 x, y ∈ U 且 d_i(x, y) = 0 < d_j(ϕ x, ϕ y)，则不存在任何 λ ∈ ENNReal 标量证书，a_ij = ∞。
-/
theorem s_channel_empty_of_dist_zero_lt {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_in : d i x y = 0) (h_out : d j (ϕ.func x) (ϕ.func y) > 0) :
    S_channel d ϕ U i j = ∅ ∧ single_channel_lip d ϕ U i j = ⊤ := by
  have h_empty : S_channel d ϕ U i j = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    have h_bound := hc x y hx hy
    rw [h_in, mul_zero] at h_bound
    have h_zero := le_antisymm h_bound (zero_le _)
    rw [h_zero] at h_out
    exact lt_irrefl 0 h_out
  refine ⟨h_empty, ?_⟩
  dsimp [single_channel_lip]
  rw [h_empty, sInf_empty]

/-!
======================================================================
HC02-P20: 标量可行族向上封闭
======================================================================
λ_0 ∈ S 且 λ_1 ≥ λ_0 时 λ_1 ∈ S。
-/
theorem s_channel_upward_closed {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {c0 c1 : ENNReal} (hc0 : c0 ∈ S_channel d ϕ U i j) (hle : c0 ≤ c1) :
    c1 ∈ S_channel d ϕ U i j := by
  intro x y hx hy
  have h0 := hc0 x y hx hy
  have h_mul := mul_le_mul_left hle (d i x y)
  exact le_trans h0 h_mul

/-!
======================================================================
HC02-P21: 正有限下确界以上的每个常数可行
======================================================================
在 0 < a < ∞ 语境，任意 λ > a（允许 λ = ∞）属于 S。
-/
theorem mem_s_channel_of_gt_sInf {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {c : ENNReal} (h_gt : single_channel_lip d ϕ U i j < c) :
    c ∈ S_channel d ϕ U i j := by
  dsimp [single_channel_lip] at h_gt
  have h_not_lb : ¬ c ≤ sInf (S_channel d ϕ U i j) := not_le_of_gt h_gt
  have h_exists : ∃ c0 ∈ S_channel d ϕ U i j, c0 < c := by
    by_contra h_all
    push Not at h_all
    have h_lb : c ≤ sInf (S_channel d ϕ U i j) := le_sInf h_all
    exact h_not_lb h_lb
  rcases h_exists with ⟨c0, hc0, hlt⟩
  exact s_channel_upward_closed d ϕ U i j hc0 (le_of_lt hlt)

/-!
======================================================================
HC02-P22: 零下确界给所有有限正常数
======================================================================
a = 0 时任意 0 < λ < ∞ 都是标量证书。
-/
theorem mem_s_channel_of_sInf_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ha : single_channel_lip d ϕ U i j = 0)
    {c : ENNReal} (hc_pos : 0 < c) (hc_top : c < ⊤) :
    c ∈ S_channel d ϕ U i j := by
  have h_gt : single_channel_lip d ϕ U i j < c := by
    rw [ha]
    exact hc_pos
  exact mem_s_channel_of_gt_sInf d ϕ U i j h_gt

/-!
======================================================================
HC02-P19: 正有限最优单通道下确界取到
======================================================================
若 a = inf S 且 0 < a < ∞，则 a 本身属于 S，即完整点对标量界成立。
-/
theorem single_channel_lip_attained_of_pos_finite {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ha_pos : 0 < single_channel_lip d ϕ U i j)
    (ha_top : single_channel_lip d ϕ U i j < ⊤) :
    single_channel_lip d ϕ U i j ∈ S_channel d ϕ U i j := by
  intro x y hx hy
  let a := single_channel_lip d ϕ U i j
  by_cases hB_top : d i x y = ⊤
  · rw [hB_top]
    rw [ENNReal.mul_top (ne_of_gt ha_pos)]
    exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    by_cases hB0 : d i x y = 0
    · have h_two_a : a < a + 1 := ENNReal.lt_add_right (ne_of_lt ha_top) one_ne_zero
      have h_mem := mem_s_channel_of_gt_sInf d ϕ U i j h_two_a
      have h1 := h_mem x y hx hy
      rw [hB0, mul_zero] at h1
      have hA0 : d j (ϕ.func x) (ϕ.func y) = 0 := le_antisymm h1 (zero_le _)
      rw [hA0, hB0, mul_zero, zero_add]
      exact zero_le _
    · lift (d i x y) to NNReal using hB_top with B hB_eq
      have hB_ne : B ≠ 0 := by
        intro hB_zero
        apply hB0
        rw [hB_zero, ENNReal.coe_zero]
      have hB_pos : 0 < B := pos_iff_ne_zero.mpr hB_ne
      let ε : NNReal := δ / B
      have hε_pos : 0 < ε := div_pos hδ hB_pos
      have h_gt : a < a + (ε : ENNReal) :=
        ENNReal.lt_add_right (ne_of_lt ha_top) (ne_of_gt (ENNReal.coe_pos.mpr hε_pos))
      have h_mem := mem_s_channel_of_gt_sInf d ϕ U i j h_gt
      have h1 := h_mem x y hx hy
      rw [add_mul] at h1
      rw [← hB_eq] at h1
      have h_prod : (ε : ENNReal) * (B : ENNReal) = (δ : ENNReal) := by
        rw [← ENNReal.coe_mul]
        congr 1
        exact div_mul_cancel₀ δ hB_ne
      rw [h_prod] at h1
      exact h1

/-!
======================================================================
HC02-P24: 下确界有限 iff 存在有限可行常数
======================================================================
a_ij < ∞ iff 存在 λ < ∞ 满足全部点对标量界。
-/
theorem single_channel_lip_lt_top_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) :
    single_channel_lip d ϕ U i j < ⊤ ↔ ∃ c < ⊤, c ∈ S_channel d ϕ U i j := by
  constructor
  · intro ha
    by_cases ha0 : single_channel_lip d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact mem_s_channel_of_sInf_zero d ϕ U i j ha0 zero_lt_one ENNReal.one_lt_top
    · have ha_pos : 0 < single_channel_lip d ϕ U i j := pos_iff_ne_zero.mpr ha0
      refine ⟨single_channel_lip d ϕ U i j, ha, ?_⟩
      exact single_channel_lip_attained_of_pos_finite d ϕ U i j ha_pos ha
  · rintro ⟨c, hc_top, hc_mem⟩
    dsimp [single_channel_lip]
    exact lt_of_le_of_lt (sInf_le hc_mem) hc_top

/-!
======================================================================
HC02-P23: 零下确界未必由 0 实现（反例）
======================================================================
构造合法扩展规范空间、合法 ϕ 及非空合法 U，令 a_ij = 0 但 0 不满足相应标量上界。
-/

inductive X_ce : Type
  | bot_pt
  | p1
  | p2
  deriving DecidableEq

def bot_ce : X_ce := X_ce.bot_pt

def d_ce : Unit → X_ce → X_ce → ENNReal :=
  fun _ x y => if x = y then 0 else ⊤

theorem d_ce_pseudo : ExtendedPseudoMetric X_ce bot_ce (d_ce ()) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨X_ce.p1, by decide⟩
  · intro x; dsimp [d_ce]; rw [if_pos rfl]
  · intro x y; dsimp [d_ce]; by_cases h : x = y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro x y z; dsimp [d_ce]
    by_cases hxz : x = z
    · rw [if_pos hxz]; exact zero_le _
    · rw [if_neg hxz]
      by_cases hxy : x = y
      · rw [if_pos hxy]
        have hyz : y ≠ z := by intro h; apply hxz; rw [hxy, h]
        rw [if_neg hyz, zero_add]
      · rw [if_neg hxy, top_add]
  · intro x hx; dsimp [d_ce]; rw [if_neg hx]

def phi_ce : Operator X_ce bot_ce := ⟨id, rfl⟩

def U_ce : Set X_ce := { X_ce.p1, X_ce.p2 }

theorem U_ce_nonempty : U_ce.Nonempty := ⟨X_ce.p1, Or.inl rfl⟩

theorem U_ce_sub_dom : U_ce ⊆ dom phi_ce := by
  intro x hx
  rcases hx with rfl | rfl
  · intro h; injection h
  · intro h; injection h

theorem eps_mem_S (ε : NNReal) (hε : 0 < ε) :
    (ε : ENNReal) ∈ S_channel d_ce phi_ce U_ce () () := by
  intro x y _ _
  dsimp [phi_ce, d_ce]
  split_ifs with h
  · rw [mul_zero]
  · rw [ENNReal.mul_top (ne_of_gt (ENNReal.coe_pos.mpr hε))]

theorem counterexample_sInf_zero_not_attained :
    ExtendedPseudoMetric X_ce bot_ce (d_ce ()) ∧
    U_ce.Nonempty ∧ U_ce ⊆ dom phi_ce ∧
    single_channel_lip d_ce phi_ce U_ce () () = 0 ∧
    (0 : ENNReal) ∉ S_channel d_ce phi_ce U_ce () () := by
  refine ⟨d_ce_pseudo, U_ce_nonempty, U_ce_sub_dom, ?_, ?_⟩
  · dsimp [single_channel_lip]
    apply le_antisymm _ (zero_le _)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have h_mem := eps_mem_S ε hε
    have h_le : sInf (S_channel d_ce phi_ce U_ce () ()) ≤ (ε : ENNReal) := sInf_le h_mem
    rw [zero_add]
    exact h_le
  · intro h
    have h_bound := h X_ce.p1 X_ce.p2 (Or.inl rfl) (Or.inr rfl)
    dsimp [phi_ce, d_ce] at h_bound
    rw [zero_mul] at h_bound
    have h_top_zero : (⊤ : ENNReal) = 0 := le_antisymm h_bound (zero_le _)
    exact ENNReal.top_ne_zero h_top_zero

/-!
======================================================================
HC02-P25: 零系数移除该证书求和项
======================================================================
L_ij = 0 时该项 L_ij d_i(x, y) = 0；相应输出求和可删该输入项，允许 d_i = ∞。
-/
theorem sum_erase_of_zero_coeff {I : Type} [Fintype I] [DecidableEq I]
    (L : BoundMatrix I) (d_xy : I → ENNReal) (i j : I) (hLij : L i j = 0) :
    L i j * d_xy i = 0 ∧
    (∑ k : I, L k j * d_xy k) = ∑ k ∈ Finset.univ.erase i, L k j * d_xy k := by
  constructor
  · rw [hLij, zero_mul]
  · have h_split := (Finset.sum_erase_add Finset.univ (fun k => L k j * d_xy k) (Finset.mem_univ i)).symm
    rw [hLij, zero_mul, add_zero] at h_split
    exact h_split

/-!
======================================================================
HC02-P26: 任意唯一输入位置的单行化简
======================================================================
L 合法且 ∀ k ≠ i, L_kj = 0，则 ∀ x, y ∈ U，d_j(ϕ x, ϕ y) ≤ L_ij d_i(x, y)；
唯一 i 不必等于 j。
-/
theorem row_sparse_lip_bound {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I)
    (hL : LipMatrix d ϕ U L) (i j : I) (h_row : RowSparse L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  have h := hL.2 x y hx hy j
  have h_sum : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [h_row k hki, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [h_sum] at h
  exact h

/-!
======================================================================
HC02-P27: 任意单列支撑的证书贡献范围
======================================================================
若所选 L 的固定输入 i 列仅输出 j 可能非零，则 ∀ k ≠ j，L_ik d_i(x, y) = 0；
输入 i 在此上界证书中至多向输出 j 贡献。
-/
theorem col_sparse_zero_entry {I : Type}
    (L : BoundMatrix I) (d_xy : I → ENNReal) (i j : I) (h_col : ColSparse L i j) :
    ∀ k : I, k ≠ j → L i k * d_xy i = 0 := by
  intro k hk
  rw [h_col k hk, zero_mul]

/-!
======================================================================
HC02-P28: 对角 Lip 矩阵给所有分量标量上界
======================================================================
L 合法且全部非对角条目 0，则 ∀ j, x, y ∈ U，d_j(ϕ x, ϕ y) ≤ L_jj d_j(x, y)。
-/
theorem diagonal_lip_bound {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I)
    (hL : LipMatrix d ϕ U L) (h_diag : IsDiagonal L) (j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  apply row_sparse_lip_bound d ϕ U L hL j j (fun k hk => h_diag k j hk) hx hy

/-!
======================================================================
HC02-P29: 双侧标量界仅要求 Lip 行稀疏
======================================================================
L 和 K 合法，只假设 ∀ k ≠ j, L_kj = 0，则 K_jj d_j(x, y) ≤ d_j(ϕ x, ϕ y) ≤ L_jj d_j(x, y)。
-/
theorem two_sided_scalar_bound_of_row_sparse {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L K : BoundMatrix I)
    (hL : LipMatrix d ϕ U L) (hK : CoLipMatrix d ϕ U K)
    (j : I) (h_row : RowSparse L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  constructor
  · have h_colip := hK.2.2 x y hx hy j
    have h_term_le : K j j * d j x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ j)
    exact le_trans h_term_le h_colip
  · exact row_sparse_lip_bound d ϕ U L hL j j h_row hx hy

/-!
======================================================================
HC02-P30: 逐分量双侧界及有限系数分支
======================================================================
若 P29 的 Lip 对角行条件对所有 j 成立，则全部分量双侧界同时成立；
若另有 ∀ j, L_jj, K_jj < ∞，则这些双侧界的标量系数有限。
-/
theorem componentwise_two_sided_bounds {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L K : BoundMatrix I)
    (hL : LipMatrix d ϕ U L) (hK : CoLipMatrix d ϕ U K)
    (h_row_all : ∀ j : I, RowSparse L j j) :
    (∀ j : I, ∀ x y, x ∈ U → y ∈ U →
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y) ∧
    ((∀ j : I, L j j < ⊤ ∧ K j j < ⊤) →
      ∀ j : I, L j j ≠ ⊤ ∧ K j j ≠ ⊤) := by
  constructor
  · intro j x y hx hy
    exact two_sided_scalar_bound_of_row_sparse d ϕ U L K hL hK j (h_row_all j) hx hy
  · intro hfin j
    exact ⟨ne_of_lt (hfin j).1, ne_of_lt (hfin j).2⟩

/-!
======================================================================
HC02-P31: 正 co-Lip 通道保持可分辨性
======================================================================
K 合法且 K_ij > 0 时，∀ x, y ∈ U，d_i(x, y) > 0 → d_j(ϕ x, ϕ y) > 0。
-/
theorem colip_channel_preserves_distinguishability {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) (hK : CoLipMatrix d ϕ U K) (i j : I) (hKij : K i j > 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (h_in : d i x y > 0) :
    d j (ϕ.func x) (ϕ.func y) > 0 := by
  have h_colip := hK.2.2 x y hx hy j
  have h_term_le : K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h_pos : K i j * d i x y > 0 := ENNReal.mul_pos (ne_of_gt hKij) (ne_of_gt h_in)
  exact lt_of_lt_of_le h_pos (le_trans h_term_le h_colip)

/-!
======================================================================
HC02-P32: 正对角 co-Lip 反射族零距
======================================================================
K 合法且 ∀ j, K_jj > 0 时，ϕ x ~_G ϕ y → x ~_G y（x, y ∈ U）。
-/
theorem colip_diagonal_reflects_gauge_zero {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) (hK : CoLipMatrix d ϕ U K)
    (h_diag_pos : ∀ j : I, K j j > 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_zero : GaugeZeroRelated d (ϕ.func x) (ϕ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra h_ne
  have h_gt : d j x y > 0 := pos_iff_ne_zero.mpr h_ne
  have h_out_gt := colip_channel_preserves_distinguishability d ϕ U K hK j j (h_diag_pos j) hx hy h_gt
  have h_out_zero : d j (ϕ.func x) (ϕ.func y) = 0 := h_zero j
  rw [h_out_zero] at h_out_gt
  exact lt_irrefl 0 h_out_gt

end formal_oet.vol_01.ch_02_operator_bounds
