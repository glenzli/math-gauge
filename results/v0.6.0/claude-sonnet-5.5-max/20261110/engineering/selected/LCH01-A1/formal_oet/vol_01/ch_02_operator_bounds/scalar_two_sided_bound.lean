import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families
import formal_oet.vol_01.ch_02_operator_bounds.component_channels

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-!
# 习题 2.2：对角输入项的标量双侧界（CH02-P25）

设 `L ∈ 𝓛(φ)|_U`、`K ∈ 𝓚(φ)|_U`（成员资格已含 `U ⊆ dom φ`，co-Lip 情形另含 `U ≠ ∅`）。
若 `L_{k→j} = 0`（`∀ k ≠ j`，即 `IsSingleInputChannel L (j, j)`），则对任意 `x, y ∈ U`，
`K_{j→j} · d_j(x,y) ≤ d_j(φ x, φ y) ≤ L_{j→j} · d_j(x,y)`。
上界取自 P19 的单一输入项行化简，下界取自 co-Lip 不等式的单项估计。
-/

section ScalarBound

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-6a98a58b5bc95360
**习题 2.2（对角输入项的标量双侧界）**：设 `φ ∈ 𝒳_op`，`U ⊆ dom(φ)`，`j ∈ I`，
`L ∈ 𝓛(φ)|_U`，`K ∈ 𝓚(φ)|_U`。若 `L_{k→j} = 0`（`∀ k ≠ j`），则对任意 `x, y ∈ U`，
`K_{j→j} · d_j(x, y) ≤ d_j(φ(x), φ(y)) ≤ L_{j→j} · d_j(x, y)`。
-/
theorem scalar_two_sided_bound {d : I → X → X → ENNReal} {φ : Operator X bot} {U : Set X}
    {j : I} {L K : Matrix I I ENNReal} (hL : L ∈ lipFamilyOn d φ U)
    (hK : K ∈ coLipFamilyOn d φ U) (hdiag : ∀ k : I, k ≠ j → chanEntry L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      chanEntry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ chanEntry L j j * d j x y := by
  intro x hx y hy
  exact ⟨single_term_le_of_mem_coLipFamilyOn hK j j x hx y hy,
    (lip_single_input_reduction hL (i := j) (j := j) hdiag x hx y hy).2⟩

end ScalarBound

end formal_oet.vol_01.ch_02_operator_bounds
