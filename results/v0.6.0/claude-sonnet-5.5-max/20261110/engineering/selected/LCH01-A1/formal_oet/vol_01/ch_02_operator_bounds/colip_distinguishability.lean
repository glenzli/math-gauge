import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-!
# 第 2 章 §2.2：正 co-Lip 通道保持可分辨性（CH02-P20、CH02-P21）

* `colip_pos_channel_preserves_pos`（命题 2.8 (i)）：`K_{i→j} > 0` 时，
  `d_i(x,y) > 0 ⟹ d_j(φ x, φ y) > 0`；
* `colip_diag_pos_reflects_zeroRelated`（命题 2.8 (ii)）：对角条目全正时，`φ` 反射族零距关系
  `φ(x) ∼_𝒢 φ(y) ⟹ x ∼_𝒢 y`（`∼_𝒢` 即冻结模块的 `GaugeZeroRelated d`）。
  结论**不**加强为点相等 `x = y`：正文不预设族分离性。末尾给出：
  分离时可得点相等（`colip_diag_pos_eq_of_isSeparating`），
  以及非分离规范空间中的实例说明点相等的加强一般不成立
  （`colip_reflection_not_pointEquality`）。
-/

section PositiveChannels

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-f82672ec0dd48f28
**命题 2.8 (i)**：设 `K ∈ 𝓚(φ)|_U`。若 `K_{i→j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x, y) > 0 ⟹ d_j(φ(x), φ(y)) > 0`。
-/
theorem colip_pos_channel_preserves_pos {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (hK : K ∈ coLipFamilyOn d φ U) {i j : I}
    (hKij : 0 < chanEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (φ.func x) (φ.func y) := by
  intro x hx y hy hxy
  exact lt_of_lt_of_le (ENNReal.mul_pos hKij.ne' hxy.ne')
    (single_term_le_of_mem_coLipFamilyOn hK i j x hx y hy)

/--
OET anchor: h-f82672ec0dd48f28
**命题 2.8 (ii)**：设 `K ∈ 𝓚(φ)|_U`。若 `K_{j→j} > 0` 对所有 `j ∈ I` 成立，则 `φ` 反射族零距关系：
对任意 `x, y ∈ U`，`φ(x) ∼_𝒢 φ(y) ⟹ x ∼_𝒢 y`。结论是族零距关系，而非点相等。
-/
theorem colip_diag_pos_reflects_zeroRelated {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ j : I, 0 < chanEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hne
  have hpos := colip_pos_channel_preserves_pos hK (hdiag j) x hx y hy (pos_iff_ne_zero.2 hne)
  exact hpos.ne' (hzero j)

/-- 仅当规范族分离时才得到点相等：对角条目全正且 `d` 分离时，`φ(x) ∼_𝒢 φ(y) ⟹ x = y`。 -/
theorem colip_diag_pos_eq_of_isSeparating {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ j : I, 0 < chanEntry K j j) (hsep : IsSeparating d) :
    ∀ x ∈ U, ∀ y ∈ U, GaugeZeroRelated d (φ.func x) (φ.func y) → x = y :=
  fun x hx y hy h => hsep x y (colip_diag_pos_reflects_zeroRelated hK hdiag x hx y hy h)

end PositiveChannels

/-! ### 不加强为点相等：非分离规范空间中的实例 -/

namespace NonSeparatingExample

/-- 实例空间 `𝒳 = Option Bool`，`⊥ = none`，单一分量：吸收元与其余点相距 `+∞`，
其余两点（`some true`、`some false`）零距。 -/
def exDist : Unit → Option Bool → Option Bool → ENNReal :=
  fun _ x y => if (x = none ↔ y = none) then 0 else ⊤

/-- `exDist` 满足扩展伪度量的四条公理及非吸收点存在性。 -/
theorem exDist_extendedPseudoMetric (i : Unit) :
    ExtendedPseudoMetric (Option Bool) none (exDist i) where
  nonabsorbing := ⟨some true, by simp⟩
  dist_self x := by simp [exDist]
  symm x y := by
    cases x <;> cases y <;> simp [exDist]
  triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp [exDist]
  isolate_bot x hx := by
    cases x with
    | none => exact absurd rfl hx
    | some a => simp [exDist]

/-- 受限域 `U = {some true, some false}`。 -/
def exSet : Set (Option Bool) := {some true, some false}

/-- 对角（单位）矩阵 `K = 𝐈`。 -/
def exK : Matrix Unit Unit ENNReal := 1

/-- 恒等算子在 `U` 上以单位矩阵为 co-Lip 证书。 -/
theorem exK_mem_coLipFamilyOn :
    exK ∈ coLipFamilyOn exDist (operator_identity : Operator (Option Bool) none) exSet := by
  refine ⟨⟨some true, by simp [exSet]⟩, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, operator_identity]
  · intro x hx y hy j
    simp [exK, chanEntry, operator_identity]

/-- 该规范族不分离：`some true` 与 `some false` 全分量零距但不相等。 -/
theorem exDist_nonSeparating : IsNonSeparating exDist := by
  intro hsep
  have h : (some true : Option Bool) = some false :=
    hsep (some true) (some false) (fun i => by simp [exDist])
  simp at h

/--
**反射结论不能加强为点相等**：存在（非分离的）扩展规范空间、算子 `φ`、受限域 `U`
及对角条目全正的 `K ∈ 𝓚(φ)|_U`，但"`φ(x) ∼_𝒢 φ(y) ⟹ x = y`（`x, y ∈ U`）"不成立。
-/
theorem colip_reflection_not_pointEquality :
    ∃ (φ : Operator (Option Bool) none) (U : Set (Option Bool)) (K : Matrix Unit Unit ENNReal),
      K ∈ coLipFamilyOn exDist φ U ∧ (∀ j : Unit, 0 < chanEntry K j j) ∧
      ¬ ∀ x ∈ U, ∀ y ∈ U, GaugeZeroRelated exDist (φ.func x) (φ.func y) → x = y := by
  refine ⟨operator_identity, exSet, exK, exK_mem_coLipFamilyOn, ?_, ?_⟩
  · intro j
    simp [exK, chanEntry]
  · intro h
    have h' := h (some true) (by simp [exSet]) (some false) (by simp [exSet])
      (fun i => by simp [exDist, operator_identity])
    simp at h'

end NonSeparatingExample

end formal_oet.vol_01.ch_02_operator_bounds
