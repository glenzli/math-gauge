import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families
import formal_oet.vol_01.ch_02_operator_bounds.component_channels
import formal_oet.vol_01.ch_02_operator_bounds.colip_distinguishability
import formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-!
# 正文同形封装（P19、P20、P21、P25）

核心定理（见各模块）只用到 Lip/co-Lip 不等式的代数结构，因而不依赖伪度量公理与 `I` 的非空性。
本文件按正文语境逐一重述：有限非空指标集 `I`（`[Fintype I] [Nonempty I]`）上的一族扩展伪度量
`d_i`（`hd : ∀ i, ExtendedPseudoMetric X bot (d i)`），算子 `φ`，`U ⊆ dom(φ)`，
以及所给的 Lip/co-Lip 证书。这些语境假设（以下划线命名）在证明中不被使用，
因此各封装只是对应核心定理的特例。
-/

section TextbookForms

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-7fa97eb6e24d5527
**单一输入项行化简（正文同形）**：设 `φ ∈ 𝒳_op`，`U ⊆ dom(φ)`，`L ∈ 𝓛(φ)|_U`。
若第 `j` 行除 `L_{i→j}` 外均为零（`L_{k→j} = 0`，`∀ k ≠ i`），则对任意 `x, y ∈ U`，
`d_j(φ(x), φ(y)) ≤ ∑ₖ L_{k→j} d_k(x, y) = L_{i→j} d_i(x, y)`。
-/
theorem lip_single_input_reduction_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (L : Matrix I I ENNReal) (hL : L ∈ lipFamilyOn d φ U) (i j : I)
    (hrow : ∀ k : I, k ≠ i → chanEntry L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ ∑ k : I, chanEntry L k j * d k x y ∧
      ∑ k : I, chanEntry L k j * d k x y = chanEntry L i j * d i x y := by
  intro x hx y hy
  obtain ⟨hsum, _⟩ := lip_single_input_reduction hL (i := i) (j := j) hrow x hx y hy
  exact ⟨hL.2 x hx y hy j, hsum⟩

/--
OET anchor: h-7fa97eb6e24d5527
**对角特例（正文同形）**：设 `L ∈ 𝓛(φ)|_U` 为对角矩阵，则对每个同分量通道 `(i, i)`
与任意 `x, y ∈ U`，`d_i(φ(x), φ(y)) ≤ ∑ₖ L_{k→i} d_k(x, y) = L_{i→i} d_i(x, y)`。
-/
theorem lip_diagonal_reduction_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (L : Matrix I I ENNReal) (hL : L ∈ lipFamilyOn d φ U) (hdiag : L.IsDiag) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ ∑ k : I, chanEntry L k i * d k x y ∧
      ∑ k : I, chanEntry L k i * d k x y = chanEntry L i i * d i x y := by
  intro i x hx y hy
  obtain ⟨hsum, _⟩ := lip_diagonal_reduction hL hdiag i x hx y hy
  exact ⟨hL.2 x hx y hy i, hsum⟩

/--
OET anchor: h-f82672ec0dd48f28
**命题 2.8 (i)（正文同形）**：设 `K ∈ 𝓚(φ)|_U`。若 `K_{i→j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x, y) > 0 ⟹ d_j(φ(x), φ(y)) > 0`。
-/
theorem colip_pos_channel_preserves_pos_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (K : Matrix I I ENNReal) (hK : K ∈ coLipFamilyOn d φ U) (i j : I)
    (hKij : 0 < chanEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (φ.func x) (φ.func y) :=
  colip_pos_channel_preserves_pos hK hKij

/--
OET anchor: h-f82672ec0dd48f28
**命题 2.8 (ii)（正文同形）**：设 `K ∈ 𝓚(φ)|_U`。若 `K_{j→j} > 0` 对所有 `j ∈ I` 成立，
则 `φ` 反射族零距关系：对任意 `x, y ∈ U`，`φ(x) ∼_𝒢 φ(y) ⟹ x ∼_𝒢 y`。
不预设族分离性，结论不是点相等。
-/
theorem colip_diag_pos_reflects_zeroRelated_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (K : Matrix I I ENNReal) (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ j : I, 0 < chanEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y :=
  colip_diag_pos_reflects_zeroRelated hK hdiag

/--
OET anchor: h-6a98a58b5bc95360
**习题 2.2（正文同形）**：设 `φ ∈ 𝒳_op`，`U ⊆ dom(φ)`，`j ∈ I`，`L ∈ 𝓛(φ)|_U`，`K ∈ 𝓚(φ)|_U`。
若 `L_{k→j} = 0`（`∀ k ≠ j`），则对任意 `x, y ∈ U`，
`K_{j→j} · d_j(x, y) ≤ d_j(φ(x), φ(y)) ≤ L_{j→j} · d_j(x, y)`。
-/
theorem scalar_two_sided_bound_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ) (j : I)
    (L : Matrix I I ENNReal) (hL : L ∈ lipFamilyOn d φ U)
    (K : Matrix I I ENNReal) (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ k : I, k ≠ j → chanEntry L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      chanEntry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ chanEntry L j j * d j x y :=
  scalar_two_sided_bound hL hK hdiag

end TextbookForms

end formal_oet.vol_01.ch_02_operator_bounds
