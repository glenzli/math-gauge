import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.colip_matrix

/-!
# 第 2 章 算子界：正 co-Lip 通道与族零距反射（义务 CH02-P20、CH02-P21）

形式化正文 § 2.2 命题 2.8：
(i) 正 co-Lip 通道保持正距离；
(ii) 全对角正 co-Lip 矩阵使算子反射族零距关系 `∼_G`。
按 § 1.1 约定，正文不预设族分离性，故 (ii) 的结论只能是
族零距关系而不能加强为点相等；文件末尾给出验证此事的反例模型。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section PositiveChannel

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-f82672ec0dd48f28
co-Lip 不等式中的单通道项下界（命题 2.8 证明中的链式放缩）：
`K_{i→j} · d_i(x,y) ≤ ∑_{k∈I} K_{k→j} · d_k(x,y) ≤ d_j(φ(x), φ(y))`。 -/
theorem IsCoLipMatrixOn.channel_term_le
    {d : I → X → X → ENNReal} {φ : Operator X bot} {K : ChannelMatrix I}
    {U : Set X} (hK : IsCoLipMatrixOn d φ K U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  calc K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
        Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
          (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.colip_bound hx hy j

/--
OET anchor: oet-f82672ec0dd48f28
**命题 2.8 (i)（正 co-Lip 通道保持正距离）**
设 `K ∈ 𝓚(φ)|_U`。若 `K_{i→j} > 0`，则对任意 `x, y ∈ U`：
`d_i(x, y) > 0 ⟹ d_j(φ(x), φ(y)) > 0`。 -/
theorem coLip_pos_channel_preserves_pos (d : I → X → X → ENNReal)
    (φ : Operator X bot) (K : ChannelMatrix I) (U : Set X)
    (hK : IsCoLipMatrixOn d φ K U) (i j : I) (hpos : 0 < K i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hdi : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hprod : K i j * d i x y ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact hpos.ne' h1
    · exact hdi.ne' h2
  calc (0 : ENNReal) < K i j * d i x y :=
        lt_of_le_of_ne (zero_le _) (Ne.symm hprod)
    _ ≤ d j (φ.func x) (φ.func y) := hK.channel_term_le hx hy i j

/--
OET anchor: oet-f82672ec0dd48f28
**命题 2.8 (ii)（全对角正 co-Lip 反射族零距关系）**
设 `K ∈ 𝓚(φ)|_U`。若 `K_{j→j} > 0` 对所有 `j ∈ I` 成立，则 `φ` 反射
族零距关系：对任意 `x, y ∈ U`，`φ(x) ∼_G φ(y) ⟹ x ∼_G y`。 -/
theorem coLip_diag_pos_reflects_zero_related (d : I → X → X → ENNReal)
    (φ : Operator X bot) (K : ChannelMatrix I) (U : Set X)
    (hK : IsCoLipMatrixOn d φ K U) (hdiag : ∀ j : I, 0 < K j j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hxy : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  rcases eq_or_ne (d j x y) 0 with h0 | h0
  · exact h0
  · exact absurd (hxy j) (ne_of_gt
      (coLip_pos_channel_preserves_pos d φ K U hK j j (hdiag j) x y hx hy
        (lt_of_le_of_ne (zero_le _) (Ne.symm h0))))

set_option linter.unusedVariables false in
/--
OET anchor: oet-f82672ec0dd48f28
**（正文语境封装）** 在扩展规范空间正文语境（`I` 有限非空，`d` 为
扩展伪度量族）下，命题 2.8 (i) 的原文形式。
底座公理在证明中不使用，一般形式见 `coLip_pos_channel_preserves_pos`。 -/
theorem coLip_pos_channel_preserves_pos_textbook {X : Type} {bot : X} {I : Type}
    [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) (hK : K ∈ coLipFamilyOn d φ U)
    (i j : I) (hpos : 0 < K i j) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hdi : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  coLip_pos_channel_preserves_pos d φ K U hK i j hpos x y hx hy hdi

set_option linter.unusedVariables false in
/--
OET anchor: oet-f82672ec0dd48f28
**（正文语境封装）** 在扩展规范空间正文语境下，命题 2.8 (ii) 的
原文形式。底座公理在证明中不使用。 -/
theorem coLip_diag_pos_reflects_zero_related_textbook {X : Type} {bot : X}
    {I : Type} [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ j : I, 0 < K j j) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hxy : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y :=
  coLip_diag_pos_reflects_zero_related d φ K U hK hdiag x y hx hy hxy

end PositiveChannel

/-! ### 命题 2.8 (ii) 的结论不能加强为点相等：反例模型 -/

namespace ReflectionNotStrengthenable

/-- 反例底座 `X = {⊥, a, b}`：以 `Option (Fin 2)` 实现，`none` 为吸收元。 -/
abbrev Xc : Type := Option (Fin 2)

/-- 吸收元 `⊥`。 -/
def botc : Xc := none

/-- 单分量指标集。 -/
abbrev Ic : Type := Fin 1

/--
唯一分量上的扩展伪度量：两个非吸收点之间距离为 `0`，与吸收元的
距离为 `⊤`。该规范族不分离：`some 0 ∼_G some 1` 但两点不同。 -/
def dc : Ic → Xc → Xc → ENNReal := fun _ x y =>
  if x.isNone = y.isNone then 0 else ⊤

/-- 恒等算子 `id_X ∈ X_op`。 -/
def phic : Operator Xc botc := operator_identity

/-- 受限域 `U = {a, b}`（不含吸收元）。 -/
def Uc : Set Xc := {some 0, some 1}

/-- 单分量下的全 `1` 矩阵：`φ = id` 的 co-Lip 证书。 -/
def Kc : ChannelMatrix Ic := fun _ _ => 1

/-- 反射结论中不可加强为相等的两个点。 -/
def xc : Xc := some 0

def yc : Xc := some 1

theorem Uc_nonempty : Uc.Nonempty := ⟨some 0, by simp [Uc]⟩

theorem Uc_subset_dom : Uc ⊆ dom phic := by
  intro x hx
  simp [Uc] at hx
  rcases hx with rfl | rfl
  · exact Option.some_ne_none 0
  · exact Option.some_ne_none 1

theorem dc_is_gauge : ∀ i : Ic, ExtendedPseudoMetric Xc botc (dc i) := by
  intro i
  refine
    { nonabsorbing := ⟨some 0, by simp [botc]⟩
      dist_self := fun x => by simp [dc]
      symm := fun x y => by
        rcases hx : x.isNone with _ | _ <;> rcases hy : y.isNone with _ | _ <;>
          simp [dc, hx, hy]
      triangle := fun x y z => by
        rcases hx : x.isNone with _ | _ <;> rcases hy : y.isNone with _ | _ <;>
          rcases hz : z.isNone with _ | _ <;>
          simp [dc, hx, hy, hz, add_top]
      isolate_bot := fun x hx => by
        cases x with
        | none => exact (hx rfl).elim
        | some v => simp [dc, botc] }

theorem Kc_is_coLip : IsCoLipMatrixOn dc phic Kc Uc := by
  refine ⟨Uc_nonempty, Uc_subset_dom, ?_⟩
  intro x _hx y _hy j
  fin_cases j
  simp only [Fin.sum_univ_one, Kc, one_mul]
  exact le_rfl

theorem Kc_diag_pos : ∀ j : Ic, 0 < Kc j j := fun _ => by simp [Kc]

theorem xc_mem : xc ∈ Uc := by simp [xc, Uc]

theorem yc_mem : yc ∈ Uc := by simp [yc, Uc]

theorem phic_zero_related : GaugeZeroRelated dc (phic.func xc) (phic.func yc) := by
  intro i
  show dc i (some 0) (some 1) = 0
  simp [dc]

theorem xc_ne_yc : xc ≠ yc := by simp [xc, yc]

/--
OET anchor: oet-f82672ec0dd48f28
**命题 2.8 (ii) 的结论不能加强为点相等**
本模型满足正文全部语境与命题 2.8 (ii) 的全部前提：
`(Xc, dc, botc)` 是真正的（非分离）扩展规范空间，`Kc ∈ 𝓚(phic)|_{Uc}`，
全对角条目为正，`xc, yc ∈ Uc`，且 `phic(xc) ∼_G phic(yc)`。
由命题 2.8 (ii) 得 `xc ∼_G yc`，但 `xc ≠ yc`。
因此反射结论只能是族零距关系 `x ∼_G y`，不能加强为点相等 `x = y`。 -/
theorem coLip_reflection_not_strengthenable :
    (∀ i : Ic, ExtendedPseudoMetric Xc botc (dc i))
      ∧ IsCoLipMatrixOn dc phic Kc Uc
      ∧ (∀ j : Ic, 0 < Kc j j)
      ∧ xc ∈ Uc
      ∧ yc ∈ Uc
      ∧ GaugeZeroRelated dc (phic.func xc) (phic.func yc)
      ∧ GaugeZeroRelated dc xc yc
      ∧ xc ≠ yc :=
  ⟨dc_is_gauge, Kc_is_coLip, Kc_diag_pos, xc_mem, yc_mem, phic_zero_related,
    coLip_diag_pos_reflects_zero_related dc phic Kc Uc Kc_is_coLip Kc_diag_pos
      xc yc xc_mem yc_mem phic_zero_related,
    xc_ne_yc⟩

end ReflectionNotStrengthenable

end formal_oet.vol_01.ch_02_operator_bounds
