import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix

/-!
# 第 2 章 算子界：分量通道、单行稀疏与单一输入项行化简

形式化正文 § 2.2 的分量通道记号（义务 CH02-D07）与单一输入项
行化简命题（义务 CH02-P19）：条目 `L_{i→j}` 作为输入分量 `d_i`
在输出分量 `d_j` 上界中的系数；零条目不参与该上界；若第 `j` 行
除 `L_{i→j}` 外均为零，Lip 不等式化为单通道项，对角矩阵时
化简对每个同分量通道 `(j, j)` 均成立。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/--
OET anchor: oet-7fa97eb6e24d5527
**定义（分量通道）**
对 `i, j ∈ I`，有序对 `(i, j)` 为从输入分量 `d_i` 到输出分量 `d_j`
的一个分量通道。 -/
abbrev ComponentChannel (I : Type) : Type := I × I

section Channels

variable {I : Type}

/-- 分量通道的输入分量。 -/
def channelInput (c : ComponentChannel I) : I := c.1

/-- 分量通道的输出分量。 -/
def channelOutput (c : ComponentChannel I) : I := c.2

@[simp] theorem channelInput_apply (i j : I) :
    channelInput (i, j) = i := rfl

@[simp] theorem channelOutput_apply (i j : I) :
    channelOutput (i, j) = j := rfl

/-- 同分量通道 `(i, i)`：输入与输出为同一分量的通道。 -/
def IsSameComponentChannel (c : ComponentChannel I) : Prop := c.1 = c.2

@[simp] theorem isSameComponentChannel_iff {i j : I} :
    IsSameComponentChannel (i, j) ↔ i = j := Iff.rfl

/--
OET anchor: oet-7fa97eb6e24d5527
**单输入通道 / 单行稀疏**：第 `j` 行除 `L_{i→j}` 外均为零，
即通道 `(i, j)` 是第 `j` 行唯一可能非零的条目来源。 -/
def IsSingleInputRow (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/--
OET anchor: oet-7fa97eb6e24d5527
**对角特例（结构部分）**：`L` 为对角矩阵，
即所有异分量通道条目均为零。 -/
def IsDiagonalMatrix (L : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- 对角矩阵的第 `j` 行是只含同分量通道 `(j, j)` 的单输入行。 -/
theorem IsDiagonalMatrix.singleInputRow {L : ChannelMatrix I}
    (h : IsDiagonalMatrix L) (j : I) : IsSingleInputRow L j j :=
  fun k hk => h k j hk

/--
OET anchor: oet-7fa97eb6e24d5527
**零条目不参与上界**：条目 `L_{k→j}` 是输入分量 `d_k` 在输出分量
`d_j` 上界中的系数；若其为零，相应项便不参与该上界——
第 `j` 行的右端和式只须对非零条目求和。 -/
theorem lipRowSum_nonzero_entries {X : Type} {I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : ChannelMatrix I) (j : I) (x y : X) :
    (∑ k : I, L k j * d k x y)
      = ∑ k ∈ Finset.univ.filter (fun k => L k j ≠ 0), L k j * d k x y := by
  refine (Finset.sum_filter_of_ne
    (f := fun k => L k j * d k x y)
    (p := fun k => L k j ≠ 0) ?_).symm
  intro k _ hne h0
  refine hne ?_
  show L k j * d k x y = 0
  rw [h0, zero_mul]

end Channels

section SingleInputRowReduction

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-7fa97eb6e24d5527
**单一输入项行化简（和式形式）**
若第 `j` 行除 `L_{i→j}` 外均为零，则该行右端和式化为单通道项：
`∑_{k∈I} L_{k→j} · f k = L_{i→j} · f i`。 -/
theorem singleInputRow_sum {L : ChannelMatrix I} {i j : I}
    (h : IsSingleInputRow L i j) (f : I → ENNReal) :
    (∑ k : I, L k j * f k) = L i j * f i :=
  Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun k _ hk => by rw [h k hk, zero_mul])

/--
OET anchor: oet-7fa97eb6e24d5527
**单一输入项行化简（证书形式）**
设 `φ ∈ X_op`，`U ⊆ dom(φ)`，受限 Lip 证书 `L ∈ 𝓛(φ)|_U`。
若第 `j` 行除 `L_{i→j}` 外均为零，则对任意 `x, y ∈ U`，Lip 不等式化为
`d_j(φ(x), φ(y)) ≤ ∑_{k∈I} L_{k→j} · d_k(x,y) = L_{i→j} · d_i(x, y)`。 -/
theorem lip_singleInputRow_bound (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsLipMatrixOn d φ L U) (hrow : IsSingleInputRow L i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  calc d j (φ.func x) (φ.func y) ≤ ∑ k : I, L k j * d k x y :=
        hL.lip_bound hx hy j
    _ = L i j * d i x y := singleInputRow_sum hrow _

/--
OET anchor: oet-7fa97eb6e24d5527
**对角特例（化简形式）**
若 `L` 为对角矩阵，上述化简对每个同分量通道 `(j, j)` 均成立：
对任意 `x, y ∈ U` 与 `j ∈ I`，
`d_j(φ(x), φ(y)) ≤ L_{j→j} · d_j(x, y)`。 -/
theorem lip_diagonal_bound (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (hL : IsLipMatrixOn d φ L U)
    (hdiag : IsDiagonalMatrix L) (j : I)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  lip_singleInputRow_bound d φ U L j j hL (hdiag.singleInputRow j) x y hx hy

set_option linter.unusedVariables false in
/--
OET anchor: oet-7fa97eb6e24d5527
**（正文语境封装）** 在扩展规范空间正文语境（`I` 有限非空，`d` 为
扩展伪度量族）下，§ 2.2 单一输入项行化简的原文形式。
底座公理在证明中不使用，一般形式见 `lip_singleInputRow_bound`。 -/
theorem lip_singleInputRow_bound_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I) (hU : U ⊆ dom φ)
    (hL : L ∈ lipFamilyOn d φ U) (hrow : IsSingleInputRow L i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y :=
  lip_singleInputRow_bound d φ U L i j hL hrow x y hx hy

set_option linter.unusedVariables false in
/--
OET anchor: oet-7fa97eb6e24d5527
**（正文语境封装）** 在扩展规范空间正文语境下，
§ 2.2 对角特例的原文形式。 -/
theorem lip_diagonal_bound_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (hU : U ⊆ dom φ)
    (hL : L ∈ lipFamilyOn d φ U) (hdiag : IsDiagonalMatrix L) (j : I)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  lip_diagonal_bound d φ U L hL hdiag j x y hx hy

end SingleInputRowReduction

end formal_oet.vol_01.ch_02_operator_bounds
