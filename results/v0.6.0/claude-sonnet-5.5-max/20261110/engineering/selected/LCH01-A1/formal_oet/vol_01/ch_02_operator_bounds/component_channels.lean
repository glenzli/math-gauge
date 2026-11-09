import Mathlib.Data.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-!
# 第 2 章 §2.2：分量通道、单输入通道（单行稀疏）与对角特例（CH02-D07、CH02-P19）

* `ComponentChannel I = I × I`：分量通道 `(i, j)`，从输入分量 `d_i` 到输出分量 `d_j`；
* `IsSingleInputChannel L (i, j)`：第 `j` 行除 `L_{i→j}` 外均为零（单输入通道 / 单行稀疏）；
* 对角矩阵用 Mathlib 的 `Matrix.IsDiag`；`isDiag_iff_forall_sameComponent_singleInput`
  说明它恰为"每个同分量通道 `(i, i)` 都是单输入通道"；
* `lip_single_input_reduction`、`lip_diagonal_reduction`（P19）给出受限 Lip 证书的行化简。
-/

section ChannelDefinitions

variable {X I : Type}

/--
OET anchor: h-7fa97eb6e24d5527
**分量通道**：对 `i, j ∈ I`，有序对 `(i, j)` 称为从输入分量 `d_i` 到输出分量 `d_j` 的分量通道。
-/
abbrev ComponentChannel (I : Type) : Type := I × I

/-- 通道 `c = (i, j)` 在矩阵 `M` 中的系数 `M_{i→j}`。 -/
def ComponentChannel.coeff (M : Matrix I I ENNReal) (c : ComponentChannel I) : ENNReal :=
  chanEntry M c.1 c.2

/-- **同分量通道** `(i, i)`。 -/
def ComponentChannel.IsSameComponent (c : ComponentChannel I) : Prop := c.1 = c.2

/--
OET anchor: h-7fa97eb6e24d5527
**单输入通道（单行稀疏）**：对通道 `(i, j)`，第 `j` 行除 `L_{i→j}` 外均为零，
即 `L_{k→j} = 0`（`∀ k ≠ i`）；此时输入分量 `d_i` 是输出分量 `d_j` 的唯一输入项。
-/
def IsSingleInputChannel (L : Matrix I I ENNReal) (c : ComponentChannel I) : Prop :=
  ∀ k : I, k ≠ c.1 → chanEntry L k c.2 = 0

/-- 通道 `(i, j)` 的系数 `L_{i→j}` 即 `chanEntry L i j`。 -/
theorem ComponentChannel.coeff_eq (M : Matrix I I ENNReal) (i j : I) :
    ComponentChannel.coeff M (i, j) = chanEntry M i j := rfl

/-- 系数为零的输入项不参与该输出分量的上界：`L_{i→j} = 0` 时 `L_{i→j} · d_i(x, y) = 0`。 -/
theorem term_eq_zero_of_coeff_zero (d : I → X → X → ENNReal) {L : Matrix I I ENNReal}
    {i j : I} (hij : chanEntry L i j = 0) (x y : X) : chanEntry L i j * d i x y = 0 := by
  rw [hij, zero_mul]

/-- 对角矩阵恰为"每个 `(i, i)` 都是单输入通道"：
`L` 对角 `⟺` 对每个 `i`，第 `i` 行除 `L_{i→i}` 外均为零。 -/
theorem isDiag_iff_forall_singleInput_self (L : Matrix I I ENNReal) :
    L.IsDiag ↔ ∀ i : I, IsSingleInputChannel L (i, i) := by
  constructor
  · intro hL i k hk
    exact hL (Ne.symm hk)
  · intro h a b hab
    exact h a b (Ne.symm hab)

/-- 对角矩阵恰为"每个同分量通道都是单输入通道"。 -/
theorem isDiag_iff_forall_sameComponent_singleInput (L : Matrix I I ENNReal) :
    L.IsDiag ↔ ∀ c : ComponentChannel I, c.IsSameComponent → IsSingleInputChannel L c := by
  rw [isDiag_iff_forall_singleInput_self]
  constructor
  · rintro h ⟨i, j⟩ (hc : i = j)
    subst hc
    exact h i
  · intro h i
    exact h (i, i) rfl

/-- 对角矩阵的非对角条目（跨分量通道的系数）为零。 -/
theorem chanEntry_eq_zero_of_isDiag {L : Matrix I I ENNReal} (hL : L.IsDiag) {i j : I}
    (hij : i ≠ j) : chanEntry L i j = 0 :=
  hL (Ne.symm hij)

/-- 系数为零的输入项不参与该输出分量的上界：`L_{i→j} = 0` 时，求和中去掉第 `i` 项不改变上界。 -/
theorem sum_erase_eq_sum_of_coeff_zero [Fintype I] [DecidableEq I] {L : Matrix I I ENNReal}
    {i j : I} (hij : chanEntry L i j = 0) (v : I → ENNReal) :
    ∑ k ∈ Finset.univ.erase i, chanEntry L k j * v k = ∑ k : I, chanEntry L k j * v k :=
  Finset.sum_erase _ (by rw [hij, zero_mul])

end ChannelDefinitions

section Reductions

variable {X I : Type} {bot : X} [Fintype I]

/-- 单输入通道 `(i, j)` 下，第 `j` 行的和式只剩一项：`∑ₖ L_{k→j} v_k = L_{i→j} v_i`。 -/
theorem sum_eq_single_input_term {L : Matrix I I ENNReal} {i j : I}
    (h : IsSingleInputChannel L (i, j)) (v : I → ENNReal) :
    ∑ k : I, chanEntry L k j * v k = chanEntry L i j * v i := by
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
  rw [h k hk, zero_mul]

/-! ### P19：单一输入项行化简；包含对角特例 -/

/-- 第 `j` 行为单输入通道 `(i, j)` 时，第 `j` 行的 Lip 条件**等价于**化简后的标量不等式。 -/
theorem lipIneq_row_iff_of_single_input {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {L : Matrix I I ENNReal} {i j : I} (hrow : IsSingleInputChannel L (i, j)) :
    (∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ ∑ k : I, chanEntry L k j * d k x y) ↔
      ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ chanEntry L i j * d i x y := by
  simp only [sum_eq_single_input_term hrow]

/--
OET anchor: h-7fa97eb6e24d5527
**单一输入项行化简**：设 `L ∈ 𝓛(φ)|_U`（其中含 `U ⊆ dom φ`）。若第 `j` 行除 `L_{i→j}` 外均为零，
则对任意 `x, y ∈ U`，Lip 不等式化为
`d_j(φ(x), φ(y)) ≤ ∑ₖ L_{k→j} d_k(x, y) = L_{i→j} d_i(x, y)`。
-/
theorem lip_single_input_reduction {d : I → X → X → ENNReal} {φ : Operator X bot} {U : Set X}
    {L : Matrix I I ENNReal} (hL : L ∈ lipFamilyOn d φ U) {i j : I}
    (hrow : IsSingleInputChannel L (i, j)) :
    ∀ x ∈ U, ∀ y ∈ U,
      ∑ k : I, chanEntry L k j * d k x y = chanEntry L i j * d i x y ∧
      d j (φ.func x) (φ.func y) ≤ chanEntry L i j * d i x y := by
  intro x hx y hy
  have hsum := sum_eq_single_input_term hrow (fun k => d k x y)
  exact ⟨hsum, hsum ▸ hL.2 x hx y hy j⟩

/--
OET anchor: h-7fa97eb6e24d5527
**对角特例**：设 `L ∈ 𝓛(φ)|_U` 为对角矩阵，则上述化简对每个同分量通道 `(i, i)` 均成立：
对任意 `i ∈ I` 与 `x, y ∈ U`，
`d_i(φ(x), φ(y)) ≤ ∑ₖ L_{k→i} d_k(x, y) = L_{i→i} d_i(x, y)`。
-/
theorem lip_diagonal_reduction {d : I → X → X → ENNReal} {φ : Operator X bot} {U : Set X}
    {L : Matrix I I ENNReal} (hL : L ∈ lipFamilyOn d φ U) (hdiag : L.IsDiag) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      ∑ k : I, chanEntry L k i * d k x y = chanEntry L i i * d i x y ∧
      d i (φ.func x) (φ.func y) ≤ chanEntry L i i * d i x y :=
  fun i => lip_single_input_reduction hL
    ((isDiag_iff_forall_singleInput_self L).1 hdiag i)

/-- 对角矩阵 `L` 是 `U` 上的受限 Lip 证书，当且仅当 `U ⊆ dom φ` 且每个同分量通道上
`d_i(φ(x), φ(y)) ≤ L_{i→i} d_i(x, y)`（`x, y ∈ U`）。 -/
theorem mem_lipFamilyOn_iff_of_isDiag {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {L : Matrix I I ENNReal} (hdiag : L.IsDiag) :
    L ∈ lipFamilyOn d φ U ↔
      U ⊆ dom φ ∧ ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
        d i (φ.func x) (φ.func y) ≤ chanEntry L i i * d i x y := by
  constructor
  · intro hL
    exact ⟨hL.1, fun i x hx y hy => (lip_diagonal_reduction hL hdiag i x hx y hy).2⟩
  · rintro ⟨hU, h⟩
    refine ⟨hU, fun x hx y hy j => ?_⟩
    rw [sum_eq_single_input_term ((isDiag_iff_forall_singleInput_self L).1 hdiag j)]
    exact h j x hx y hy

end Reductions

end formal_oet.vol_01.ch_02_operator_bounds
