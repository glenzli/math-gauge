import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix

/-!
# 第 2 章 算子界：含非空条件的受限 co-Lip 矩阵及证书族（义务 CH02-D02）

形式化正文 § 2.1 的子集受限 co-Lipschitz 下界矩阵：
对 `φ ∈ X_op` 与非空子集 `U ⊆ dom(φ)`，谓词 `K ∈ 𝓚(φ)|_U` 及
下界证书族 `𝓚(φ)|_U`。按正文约定，凡出现 `𝓚(φ)|_U` 均包含
非空性条件 `U ≠ ∅`。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section CoLipCertificates

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-af85899693cc8750
co-Lip 下界不等式在子集 `U` 上的纯不等式形式：
对所有 `x, y ∈ U` 与所有 `j ∈ I`，
`∑_{i∈I} K_{i→j} · d_i(x, y) ≤ d_j(φ(x), φ(y))`。 -/
def CoLipBoundOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (K : ChannelMatrix I) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, K i j * d i x y ≤ d j (φ.func x) (φ.func y)

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 co-Lipschitz 矩阵）**
对 `φ ∈ X_op` 与给定的非空子集 `U ⊆ dom(φ)`，称非负矩阵 `K`
（条目 `K_{i→j} ∈ ℝ̄₊`）为 `φ` 在 `U` 上的合法受限 co-Lipschitz
矩阵（`K ∈ 𝓚(φ)|_U`），若对所有 `x, y ∈ U` 和所有 `j ∈ I`：
`d_j(φ(x), φ(y)) ≥ ∑_{i∈I} K_{i→j} · d_i(x, y)`。
按正文约定，凡出现 `𝓚(φ)|_U` 均包含非空性条件 `U ≠ ∅`，
故谓词合并 `U.Nonempty`、`U ⊆ dom(φ)` 与不等式三部分。 -/
def IsCoLipMatrixOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (K : ChannelMatrix I) (U : Set X) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ CoLipBoundOn d φ K U

/--
OET anchor: oet-af85899693cc8750
`φ` 在 `U` 上的全体合法受限 co-Lip 矩阵之集 `𝓚(φ)|_U`
（下界证书族）。本章把它视为下界证书族使用，不预设其中存在
同时实现所有条目上确界的指定矩阵。 -/
def coLipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) := { K | IsCoLipMatrixOn d φ K U }

theorem mem_coLipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} :
    K ∈ coLipFamilyOn d φ U ↔ IsCoLipMatrixOn d φ K U := Iff.rfl

theorem IsCoLipMatrixOn.nonempty {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} (h : IsCoLipMatrixOn d φ K U) :
    U.Nonempty := h.1

theorem IsCoLipMatrixOn.subset_dom {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} (h : IsCoLipMatrixOn d φ K U) :
    U ⊆ dom φ := h.2.1

theorem IsCoLipMatrixOn.colip_bound {d : I → X → X → ENNReal} {φ : Operator X bot}
    {K : ChannelMatrix I} {U : Set X} (h : IsCoLipMatrixOn d φ K U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i : I, K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  h.2.2 x hx y hy j

end CoLipCertificates

end formal_oet.vol_01.ch_02_operator_bounds
