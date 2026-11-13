import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# 第 2 章 算子界：规范矩阵与 Lip / co-Lip 证书族

对应 `source/02-operator-bounds.md` §2.1（锚点 `oet-af85899693cc8750`）：
- `CH02-D03`：输入/输出矩阵指标约定（输出为行指标、输入为列指标）与矩阵乘法
- `CH02-D01`：全域/受限 Lipschitz 矩阵谓词与证书族 `ℒ(ϕ)`、`ℒ(ϕ)|_U`
- `CH02-D02`：含非空条件的受限 co-Lipschitz 矩阵谓词与证书族 `𝒦(ϕ)|_U`
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-! ## CH02-D03：输入/输出矩阵指标约定与乘法 -/

/--
规范矩阵：条目取值于 `ENNReal`（即 `ℝ̄₊ = [0, +∞]`）。
按正文约定，以输出分量 `j` 为行指标、输入分量 `i` 为列指标，
即矩阵第 `j` 行第 `i` 列存储条目 `M_{i → j}`。
-/
abbrev GaugeMatrix (I : Type) : Type := Matrix I I ENNReal

/--
箭头指标条目读取：`channelEntry M i j` 表示 `M_{i → j} = (M)_{j i}`，
即从输入分量 `i` 指向输出分量 `j` 的系数。
-/
def channelEntry {I : Type} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

/--
由箭头指标函数 `f i j = M_{i → j}` 构造规范矩阵（第 `j` 行第 `i` 列取 `f i j`）。
-/
def ofChannelEntries {I : Type} (f : I → I → ENNReal) : GaugeMatrix I :=
  Matrix.of (fun j i => f i j)

@[simp]
theorem channelEntry_ofChannelEntries {I : Type} (f : I → I → ENNReal) (i j : I) :
    channelEntry (ofChannelEntries f) i j = f i j := rfl

@[ext]
theorem gaugeMatrix_ext {I : Type} {M₁ M₂ : GaugeMatrix I}
    (h : ∀ i j : I, channelEntry M₁ i j = channelEntry M₂ i j) :
    M₁ = M₂ := by
  ext j i
  exact h i j

/-- 规范矩阵乘法 `(M₂ * M₁)` 在箭头指标下的展开式：`(M₂ * M₁)_{i → j} = ∑ k, (M₂)_{k → j} * (M₁)_{i → k}`。 -/
theorem channelEntry_mul {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) (i j : I) :
    channelEntry (M₂ * M₁) i j = ∑ k : I, channelEntry M₂ k j * channelEntry M₁ i k := by
  simp [channelEntry, Matrix.mul_apply]

/-- 单位规范矩阵在箭头指标下的值：对角元为 `1`，非对角元为 `0`。 -/
theorem channelEntry_one {I : Type} [DecidableEq I] (i j : I) :
    channelEntry (1 : GaugeMatrix I) i j = if j = i then 1 else 0 := by
  simp [channelEntry, Matrix.one_apply]

/-- 规范矩阵乘法满足结合律。 -/
theorem gaugeMatrix_mul_assoc {I : Type} [Fintype I] (M₃ M₂ M₁ : GaugeMatrix I) :
    (M₃ * M₂) * M₁ = M₃ * (M₂ * M₁) :=
  Matrix.mul_assoc M₃ M₂ M₁

/-- 单位规范矩阵是规范矩阵乘法的双侧单位元。 -/
theorem gaugeMatrix_one_mul {I : Type} [Fintype I] [DecidableEq I] (M : GaugeMatrix I) :
    (1 : GaugeMatrix I) * M = M :=
  Matrix.one_mul M

theorem gaugeMatrix_mul_one {I : Type} [Fintype I] [DecidableEq I] (M : GaugeMatrix I) :
    M * (1 : GaugeMatrix I) = M :=
  Matrix.mul_one M

/-! ## CH02-D01：全域/受限 Lip 矩阵谓词与证书族 -/

/--
全域 Lipschitz 矩阵谓词：
对所有 `x, y ∈ dom ϕ` 与所有输出分量 `j ∈ I`，满足
`d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L_{i → j} * d i x y`。
-/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/-- 全域合法 Lip 矩阵证书族 `ℒ(ϕ)`。 -/
def lipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/--
子集受限 Lipschitz 矩阵谓词：
要求 `U ⊆ dom ϕ`，且对所有 `x, y ∈ U` 与所有输出分量 `j ∈ I`，满足
`d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L_{i → j} * d i x y`。
-/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/-- 子集受限合法 Lip 矩阵证书族 `ℒ(ϕ)|_U`。 -/
def restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem mem_lipMatrices_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    L ∈ lipMatrices d ϕ ↔ IsLipMatrix d ϕ L :=
  Iff.rfl

theorem mem_restrictedLipMatrices_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) :
    L ∈ restrictedLipMatrices d ϕ U ↔ IsRestrictedLipMatrix d ϕ U L :=
  Iff.rfl

theorem restrictedLipMatrices_subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {L : GaugeMatrix I}
    (hL : L ∈ restrictedLipMatrices d ϕ U) : U ⊆ dom ϕ :=
  hL.1

theorem isRestrictedLipMatrix_dom_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsRestrictedLipMatrix d ϕ (dom ϕ) L ↔ IsLipMatrix d ϕ L :=
  ⟨fun h => h.2, fun h => ⟨Set.Subset.rfl, h⟩⟩

theorem restrictedLipMatrices_dom_eq {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedLipMatrices d ϕ (dom ϕ) = lipMatrices d ϕ := by
  ext L
  exact isRestrictedLipMatrix_dom_iff d ϕ L

/-- 引理 2.1（受限 Lip 矩阵族的单调性）：若 `U ⊆ V ⊆ dom ϕ`，则 `ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U`。 -/
theorem restrictedLipMatrices_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    restrictedLipMatrices d ϕ V ⊆ restrictedLipMatrices d ϕ U := by
  intro L hL
  refine ⟨Set.Subset.trans hUV hV, ?_⟩
  intro x hx y hy j
  exact hL.2 x (hUV hx) y (hUV hy) j

/-- 引理 2.1 推论：对任意 `U ⊆ dom ϕ`，有 `ℒ(ϕ) ⊆ ℒ(ϕ)|_U`。 -/
theorem lipMatrices_subset_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) :
    lipMatrices d ϕ ⊆ restrictedLipMatrices d ϕ U := by
  rw [← restrictedLipMatrices_dom_eq d ϕ]
  exact restrictedLipMatrices_antitone d ϕ hU Set.Subset.rfl

/-! ## CH02-D02：含非空条件的受限 co-Lip 矩阵及证书族 -/

/--
子集受限 co-Lipschitz 矩阵谓词：
包含非空性条件 `U.Nonempty`、定义域条件 `U ⊆ dom ϕ`，以及对所有 `x, y ∈ U` 与 `j ∈ I`：
`∑ i : I, K_{i → j} * d i x y ≤ d j (ϕ.func x) (ϕ.func y)`。
-/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- 子集受限合法 co-Lip 矩阵证书族 `𝒦(ϕ)|_U`（蕴含 `U.Nonempty` 与 `U ⊆ dom ϕ`）。 -/
def restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

theorem mem_restrictedCoLipMatrices_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) :
    K ∈ restrictedCoLipMatrices d ϕ U ↔ IsRestrictedCoLipMatrix d ϕ U K :=
  Iff.rfl

theorem restrictedCoLipMatrices_nonempty {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) : U.Nonempty :=
  hK.1

theorem restrictedCoLipMatrices_subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) : U ⊆ dom ϕ :=
  hK.2.1

@[simp]
theorem restrictedCoLipMatrices_empty {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedCoLipMatrices d ϕ ∅ = ∅ := by
  ext K
  simp [restrictedCoLipMatrices, IsRestrictedCoLipMatrix]

/-- 引理 2.3（受限 co-Lip 矩阵族的单调性）：若 `∅ ≠ U ⊆ V ⊆ dom ϕ`，则 `𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U`。 -/
theorem restrictedCoLipMatrices_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    restrictedCoLipMatrices d ϕ V ⊆ restrictedCoLipMatrices d ϕ U := by
  intro K hK
  refine ⟨hUne, Set.Subset.trans hUV hV, ?_⟩
  intro x hx y hy j
  exact hK.2.2 x (hUV hx) y (hUV hy) j

end LCH01
