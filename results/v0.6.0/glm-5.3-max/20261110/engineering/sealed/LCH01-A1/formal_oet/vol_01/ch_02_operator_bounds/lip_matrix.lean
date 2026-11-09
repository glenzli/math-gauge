import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix

/-!
# 第 2 章 算子界：全域/受限 Lip 矩阵谓词与证书族（义务 CH02-D01）

形式化正文 § 2.1 的 Lipschitz 上界矩阵：
全域合法 Lipschitz 矩阵（`L ∈ 𝓛(φ)`）、子集受限 Lip 矩阵
（`L ∈ 𝓛(φ)|_U`，`U ⊆ dom(φ)`）及对应证书族。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

section LipCertificates

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/--
OET anchor: oet-af85899693cc8750
Lip 距离放缩不等式在子集 `U` 上的纯不等式形式：
对所有 `x, y ∈ U` 与所有 `j ∈ I`，
`d_j(φ(x), φ(y)) ≤ ∑_{i∈I} L_{i→j} · d_i(x, y)`。 -/
def LipBoundOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y

/--
OET anchor: oet-af85899693cc8750
**定义（Lipschitz 矩阵）**
对 `φ ∈ X_op`，称非负矩阵 `L`（条目 `L_{i→j} ∈ ℝ̄₊`）为 `φ` 的
合法 Lipschitz 矩阵（`L ∈ 𝓛(φ)`），若对所有 `x, y ∈ dom(φ)` 和所有
`j ∈ I`：
`d_j(φ(x), φ(y)) ≤ ∑_{i∈I} L_{i→j} · d_i(x, y)`。 -/
def IsLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  LipBoundOn d φ L (dom φ)

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 Lip 矩阵）**
对子集 `U ⊆ dom(φ)`，若对任意 `x, y ∈ U` 均满足上述距离放缩不等式，
则称 `L` 为 `φ` 在 `U` 上的受限 Lip 矩阵（`L ∈ 𝓛(φ)|_U`）。
正文记号 `𝓛(φ)|_U` 以 `U ⊆ dom(φ)` 为前提，故谓词合并该侧条件。 -/
def IsLipMatrixOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) (U : Set X) : Prop :=
  U ⊆ dom φ ∧ LipBoundOn d φ L U

/--
OET anchor: oet-af85899693cc8750
`φ` 的全体合法 Lip 矩阵之集 `𝓛(φ)`（上界证书族）。
本章把它作为证书族使用，不预设其中存在同时实现所有条目下确界的矩阵。 -/
def lipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (ChannelMatrix I) := { L | IsLipMatrix d φ L }

/--
OET anchor: oet-af85899693cc8750
`φ` 在 `U` 上的全体合法受限 Lip 矩阵之集 `𝓛(φ)|_U`
（受限上界证书族）。 -/
def lipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) := { L | IsLipMatrixOn d φ L U }

theorem mem_lipFamily {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} :
    L ∈ lipFamily d φ ↔ IsLipMatrix d φ L := Iff.rfl

theorem mem_lipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} {U : Set X} :
    L ∈ lipFamilyOn d φ U ↔ IsLipMatrixOn d φ L U := Iff.rfl

theorem IsLipMatrix.lip_bound {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} (h : IsLipMatrix d φ L)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (j : I) :
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y :=
  h x hx y hy j

theorem IsLipMatrixOn.subset_dom {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} {U : Set X} (h : IsLipMatrixOn d φ L U) :
    U ⊆ dom φ := h.1

theorem IsLipMatrixOn.lip_bound {d : I → X → X → ENNReal} {φ : Operator X bot}
    {L : ChannelMatrix I} {U : Set X} (h : IsLipMatrixOn d φ L U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y :=
  h.2 x hx y hy j

/--
全域证书族即限制在 `dom(φ)` 上的受限证书族：`𝓛(φ) = 𝓛(φ)|_{dom(φ)}`。 -/
theorem lipFamily_eq_lipFamilyOn_dom (d : I → X → X → ENNReal)
    (φ : Operator X bot) :
    lipFamily d φ = lipFamilyOn d φ (dom φ) := by
  ext L
  exact ⟨fun h => ⟨fun _ hx => hx, h⟩, fun h => h.2⟩

end LipCertificates

end formal_oet.vol_01.ch_02_operator_bounds
