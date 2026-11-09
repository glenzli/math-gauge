import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.colip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.component_channel
import formal_oet.vol_01.ch_02_operator_bounds.colip_reflection

/-!
# 第 2 章习题 2.2：对角输入项的标量双侧界（义务 CH02-P25）

设 `φ ∈ X_op`，`U ⊆ dom(φ)`，`j ∈ I`，给定 `L ∈ 𝓛(φ)|_U` 与
`K ∈ 𝓚(φ)|_U`。若 `L` 的第 `j` 行只保留对角输入项
（`L_{k→j} = 0`，`∀ k ≠ j`），则对任意 `x, y ∈ U` 有标量双侧不等式
`K_{j→j} · d_j(x,y) ≤ d_j(φ(x),φ(y)) ≤ L_{j→j} · d_j(x,y)`。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section Exercise0202

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-6a98a58b5bc95360
**习题 2.2（对角输入项的标量双侧界）**
设 `φ ∈ X_op`，`U ⊆ dom(φ)`，`j ∈ I`。给定 `L ∈ 𝓛(φ)|_U` 与
`K ∈ 𝓚(φ)|_U`。若 `φ` 在 `U` 上关于输出分量 `d_j` 满足只保留对角
输入项的 Lip 上界 `L_{k→j} = 0`（`∀ k ≠ j`），则对任意 `x, y ∈ U`
有标量双侧不等式：
`K_{j→j} · d_j(x, y) ≤ d_j(φ(x), φ(y)) ≤ L_{j→j} · d_j(x, y)`。 -/
theorem scalar_two_sided_bound (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L K : ChannelMatrix I) (j : I)
    (hL : IsLipMatrixOn d φ L U) (hK : IsCoLipMatrixOn d φ K U)
    (hsparse : IsSingleInputRow L j j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y)
      ∧ d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · exact hK.channel_term_le hx hy j j
  · calc d j (φ.func x) (φ.func y) ≤ ∑ k : I, L k j * d k x y :=
        hL.lip_bound hx hy j
    _ = L j j * d j x y := singleInputRow_sum hsparse _

set_option linter.unusedVariables false in
/--
OET anchor: oet-6a98a58b5bc95360
**（正文语境封装）** 在扩展规范空间正文语境（`I` 有限非空，`d` 为
扩展伪度量族）下，习题 2.2 的原文形式。 -/
theorem scalar_two_sided_bound_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (L K : ChannelMatrix I) (j : I) (hU : U ⊆ dom φ)
    (hL : L ∈ lipFamilyOn d φ U) (hK : K ∈ coLipFamilyOn d φ U)
    (hsparse : ∀ k : I, k ≠ j → L k j = 0)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y)
      ∧ d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  scalar_two_sided_bound d φ U L K j hL hK hsparse x y hx hy

end Exercise0202

end formal_oet.vol_01.ch_02_operator_bounds
