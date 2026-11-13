I have inspected the workspace and `formal_oet` dependencies, analyzed all 8 obligations in `obligations.json`, and launched the background compilation of the frozen `formal_oet` foundation modules into `.tmp/olean` (without modifying `formal_oet/`). Waiting for that compilation task to complete before writing and checking the new Lean modules.
`GaugeMatrix.lean` compiled; `ComponentChannel.lean` is currently compiling in background task `task-26` and showed minor `Finset.single_le_sum` / unused-simp diagnostics. Waiting for `task-26` to finish so I can inspect all diagnostics and fix them cleanly.
{}
已完成 `obligations.json` 中全部 8 项义务（`CH02-D01`, `CH02-D02`, `CH02-D03`, `CH02-D07`, `CH02-P19`, `CH02-P20`, `CH02-P21`, `CH02-P25`）在 Lean 4.29.1 下的完整形式化，且未修改或覆盖冻结前置模块 `formal_oet/`。

### 验证结果摘要
- 工作区交付文件：[GaugeMatrix.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/LCH01/physical-4/session/work/GaugeMatrix.lean)、[ComponentChannel.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/LCH01/physical-4/session/work/ComponentChannel.lean)、[Main.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/LCH01/physical-4/session/work/Main.lean)、[alignment.json](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/LCH01/physical-4/session/work/alignment.json)。
- 在冻结环境（`LEAN_ENV.sh`、Lean 4.29.1）下编译 `GaugeMatrix.lean`、`ComponentChannel.lean` 与 `Main.lean` 均退出码 `0`、无报错与警告；`lean Main.lean` 检查通过。
- 对 `GaugeMatrix.lean` 与 `ComponentChannel.lean` 中全部 34 条定理执行 `#print axioms`，均仅依赖 `[propext, Classical.choice, Quot.sound]`，无 `sorry`、`admit` 或新增公理。
- 经验证 `alignment.json` 覆盖 `obligations.json` 全部 8 项义务，且全部声明名均已在 `Main` 环境中 `#check` 通过。

---

```lean filename=GaugeMatrix.lean
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
```

```lean filename=ComponentChannel.lean
import GaugeMatrix

/-!
# 第 2 章 算子界：分量通道、通道可分辨性与标量双侧界

对应 `source/02-operator-bounds.md` §2.2 与 §2.3 习题 2.2：
- `CH02-D07`（锚点 `oet-7fa97eb6e24d5527`）：单输入通道、单行稀疏与对角特例
- `CH02-P19`（锚点 `oet-7fa97eb6e24d5527`）：单一输入项行化简（含对角特例）
- `CH02-P20`（锚点 `oet-f82672ec0dd48f28`）：命题 2.8(i)，正 co-Lip 通道保持正距离
- `CH02-P21`（锚点 `oet-f82672ec0dd48f28`）：命题 2.8(ii)，全对角正 co-Lip 反射族零距（不加强为点相等）
- `CH02-P25`（锚点 `oet-6a98a58b5bc95360`）：习题 2.2，对角输入项的标量双侧界
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-! ## CH02-D07：单输入通道、单行稀疏与对角特例 -/

/--
分量通道：从输入分量 `d_{input}` 到输出分量 `d_{output}` 的有序对 `(input, output)`。
-/
@[ext]
structure ComponentChannel (I : Type) where
  input : I
  output : I
  deriving DecidableEq

/-- 同分量通道 `(i, i)`。 -/
def sameComponentChannel {I : Type} (i : I) : ComponentChannel I :=
  ⟨i, i⟩

/-- 规范矩阵 `M` 在分量通道 `c` 上对应的系数 `M_{c.input → c.output}`。 -/
def channelCoeff {I : Type} (M : GaugeMatrix I) (c : ComponentChannel I) : ENNReal :=
  channelEntry M c.input c.output

@[simp]
theorem channelCoeff_mk {I : Type} (M : GaugeMatrix I) (i j : I) :
    channelCoeff M ⟨i, j⟩ = channelEntry M i j := rfl

@[simp]
theorem channelCoeff_sameComponentChannel {I : Type} (M : GaugeMatrix I) (i : I) :
    channelCoeff M (sameComponentChannel i) = channelEntry M i i := rfl

/--
通道零系数谓词：`M_{c.input → c.output} = 0`，表示该输入分量不参与对应输出分量的上界。
-/
def IsInactiveChannel {I : Type} (M : GaugeMatrix I) (c : ComponentChannel I) : Prop :=
  channelCoeff M c = 0

/--
单行稀疏 / 单一输入项谓词：
矩阵 `M` 的第 `j` 行（对应输出分量 `d_j`）除通道 `(i, j)` 的条目 `M_{i → j}` 外均为零。
-/
def IsSingleInputRow {I : Type} (M : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → channelEntry M k j = 0

/--
第 `j` 行仅保留对角输入项 `M_{j → j}` 的特殊情形：`∀ k ≠ j, M_{k → j} = 0`。
-/
abbrev IsDiagonalInputRow {I : Type} (M : GaugeMatrix I) (j : I) : Prop :=
  IsSingleInputRow M j j

/--
对角规范矩阵谓词：所有非对角分量通道 `(i, j)` (`i ≠ j`) 均取零。
-/
def IsDiagonalMatrix {I : Type} (M : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → channelEntry M i j = 0

/-- 由对角权函数 `w : I → ENNReal` 构造对角规范矩阵。 -/
def diagonalGaugeMatrix {I : Type} [DecidableEq I] (w : I → ENNReal) : GaugeMatrix I :=
  Matrix.diagonal w

@[simp]
theorem channelEntry_diagonalGaugeMatrix {I : Type} [DecidableEq I]
    (w : I → ENNReal) (i j : I) :
    channelEntry (diagonalGaugeMatrix w) i j = if j = i then w i else 0 := by
  by_cases h : j = i
  · subst h
    simp [channelEntry, diagonalGaugeMatrix]
  · simp [channelEntry, diagonalGaugeMatrix, h]

theorem diagonalGaugeMatrix_isDiagonal {I : Type} [DecidableEq I] (w : I → ENNReal) :
    IsDiagonalMatrix (diagonalGaugeMatrix w) := by
  intro i j hij
  simp [hij.symm]

theorem one_isDiagonalMatrix {I : Type} [DecidableEq I] :
    IsDiagonalMatrix (1 : GaugeMatrix I) := by
  intro i j hij
  simp [channelEntry_one, hij.symm]

/-- 矩阵为对角矩阵当且仅当每一行均仅保留同分量（对角）输入项。 -/
theorem isDiagonalMatrix_iff_forall_singleInputRow {I : Type} (M : GaugeMatrix I) :
    IsDiagonalMatrix M ↔ ∀ i : I, IsSingleInputRow M i i := by
  constructor
  · intro hdiag i k hki
    exact hdiag k i hki
  · intro hrows i j hij
    exact hrows j i hij

/-! ## CH02-P19：单一输入项行化简；包含对角特例 -/

/--
零条目不参与输出上界求和：若 `M_{c.input → c.output} = 0`，
则从全指标和中剔除 `c.input` 后和不变。
-/
theorem sum_omit_of_inactive_channel {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (M : GaugeMatrix I) (c : ComponentChannel I)
    (hc : IsInactiveChannel M c) (x y : X) :
    ∑ k : I, channelEntry M k c.output * d k x y =
      ∑ k ∈ Finset.univ.erase c.input, channelEntry M k c.output * d k x y := by
  have hterm : channelEntry M c.input c.output * d c.input x y = 0 := by
    have hc' : channelEntry M c.input c.output = 0 := hc
    simp [hc']
  rw [← Finset.add_sum_erase Finset.univ (fun k => channelEntry M k c.output * d k x y)
    (Finset.mem_univ c.input), hterm, zero_add]

/--
单行稀疏矩阵求和坍缩引理：
若第 `j` 行除 `L_{i → j}` 外均为零，则 `∑ k, L_{k → j} * d_k(x, y) = L_{i → j} * d_i(x, y)`。
-/
theorem sum_eq_single_of_singleInputRow {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) (i j : I)
    (hrow : IsSingleInputRow L i j) (x y : X) :
    ∑ k : I, channelEntry L k j * d k x y = channelEntry L i j * d i x y := by
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/--
单一输入项行化简：
设 `L ∈ ℒ(ϕ)|_U`，且第 `j` 行除 `L_{i → j}` 外均为零，则对任意 `x, y ∈ U`，
Lip 不等式化为 `d_j(ϕ(x), ϕ(y)) ≤ ∑ k, L_{k → j} * d_k(x, y) = L_{i → j} * d_i(x, y)`
及直接标量上界 `d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} * d_i(x, y)`。
-/
theorem singleInputRow_lip_reduction {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (i j : I) (hL : L ∈ restrictedLipMatrices d ϕ U) (hrow : IsSingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k j * d k x y ∧
      ∑ k : I, channelEntry L k j * d k x y = channelEntry L i j * d i x y ∧
      d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L i j * d i x y := by
  intro x hx y hy
  have hlip : d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k j * d k x y :=
    hL.2 x hx y hy j
  have hsum : ∑ k : I, channelEntry L k j * d k x y = channelEntry L i j * d i x y :=
    sum_eq_single_of_singleInputRow d L i j hrow x y
  refine ⟨hlip, hsum, ?_⟩
  rw [← hsum]
  exact hlip

/--
对角特例化简：
若 `L ∈ ℒ(ϕ)|_U` 为对角矩阵，则对每个同分量通道 `(i, i)` 与任意 `x, y ∈ U`，
均有 `d_i(ϕ(x), ϕ(y)) ≤ ∑ k, L_{k → i} * d_k(x, y) = L_{i → i} * d_i(x, y)`
及直接标量上界 `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} * d_i(x, y)`。
-/
theorem diagonal_lip_reduction {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipMatrices d ϕ U) (hdiag : IsDiagonalMatrix L) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k i * d k x y ∧
      ∑ k : I, channelEntry L k i * d k x y = channelEntry L i i * d i x y ∧
      d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  intro i
  have hrow : IsSingleInputRow L i i :=
    (isDiagonalMatrix_iff_forall_singleInputRow L).mp hdiag i
  exact singleInputRow_lip_reduction d ϕ U L i i hL hrow

/-! ## CH02-P20 与 CH02-P21：命题 2.8（正 co-Lip 通道保持可分辨性与反射族零距） -/

/--
**命题 2.8(i)（正 co-Lip 通道保持正距离）**
设 `K ∈ 𝒦(ϕ)|_U`。若 `K_{i → j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x, y) > 0 → d_j(ϕ(x), ϕ(y)) > 0`。
-/
theorem pos_colip_channel_preserves_pos_dist {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (i j : I) (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hKpos : 0 < channelEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdpos
  have hcolip : ∑ k : I, channelEntry K k j * d k x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    hK.2.2 x hx y hy j
  have hterm : channelEntry K i j * d i x y ≤ ∑ k : I, channelEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k => channelEntry K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have hmul : 0 < channelEntry K i j * d i x y :=
    ENNReal.mul_pos hKpos.ne' hdpos.ne'
  exact lt_of_lt_of_le hmul (le_trans hterm hcolip)

/-- 命题 2.8(i) 的 `ComponentChannel` 形式封装。 -/
theorem pos_colip_componentChannel_preserves_pos_dist {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (c : ComponentChannel I) (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hcpos : 0 < channelCoeff K c) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d c.input x y → 0 < d c.output (ϕ.func x) (ϕ.func y) :=
  pos_colip_channel_preserves_pos_dist d ϕ U K c.input c.output hK hcpos

/--
**命题 2.8(ii)（全对角正 co-Lip 反射族零距关系）**
设 `K ∈ 𝒦(ϕ)|_U`。若 `K_{j → j} > 0` 对所有 `j ∈ I` 成立，则 `ϕ` 在 `U` 上反射族零距关系：
对任意 `x, y ∈ U`，`GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y`。
按正文约定不预设族分离性，结论不加强为 `x = y`。
-/
theorem diag_pos_colip_reflects_gauge_zero_related {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hdiag : ∀ j : I, 0 < channelEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hne
  have hdpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have himgpos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_colip_channel_preserves_pos_dist d ϕ U K j j hK (hdiag j) x hx y hy hdpos
  exact himgpos.ne' (hzero j)

/--
不加强为点相等的反例验证：
在完全满足 `ExtendedPseudoMetric` 与有限非空指标族 `I` 的扩展规范空间上，
即使存在 `K ∈ 𝒦(ϕ)|_U` 且所有对角元 `K_{j → j} > 0`，对满足 `ϕ(x) ∼_𝒢 ϕ(y)` 的 `x, y ∈ U`
仍不能推出 `x = y`。
-/
theorem diag_pos_colip_not_implies_eq :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i : I, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I),
      K ∈ restrictedCoLipMatrices d ϕ U ∧
      (∀ j : I, 0 < channelEntry K j j) ∧
      ∃ x ∈ U, ∃ y ∈ U, GaugeZeroRelated d (ϕ.func x) (ϕ.func y) ∧ x ≠ y := by
  let bot : Fin 3 := 2
  let d : Unit → Fin 3 → Fin 3 → ENNReal := fun _ x y =>
    if x = y then 0 else if x = bot ∨ y = bot then ⊤ else 0
  have hd : ∀ i : Unit, ExtendedPseudoMetric (Fin 3) bot (d i) := fun _ =>
    { nonabsorbing := ⟨0, by decide⟩
      dist_self := fun x => by simp [d]
      symm := fun x y => by
        dsimp [d]
        by_cases hxy : x = y
        · subst hxy; simp
        · have hyx : y ≠ x := Ne.symm hxy
          simp [hxy, hyx, or_comm]
      triangle := fun x y z => by
        fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [d, bot]
      isolate_bot := fun x hx => by
        fin_cases x <;> simp_all [d, bot] }
  let ϕ : Operator (Fin 3) bot := operator_identity
  let U : Set (Fin 3) := {0, 1}
  let K : GaugeMatrix Unit := 1
  refine ⟨Fin 3, Unit, bot, inferInstance, inferInstance, d, hd, ϕ, U, K, ?_, ?_, ?_⟩
  · refine ⟨⟨0, by simp [U]⟩, ?_, ?_⟩
    · intro x hx
      rcases hx with rfl | rfl <;> simp [dom, ϕ, operator_identity, bot]
    · intro x hx y hy j
      simp [K, channelEntry, ϕ, operator_identity]
  · intro j
    simp [K, channelEntry]
  · refine ⟨0, by simp [U], 1, by simp [U], ?_, by decide⟩
    intro i
    simp [d, ϕ, operator_identity, bot]

/-! ## CH02-P25：习题 2.2（对角输入项的标量双侧界） -/

/--
**习题 2.2（对角输入项的标量双侧界）**
设 `L ∈ ℒ(ϕ)|_U` 与 `K ∈ 𝒦(ϕ)|_U`（均已蕴含 `U ⊆ dom ϕ`，且 `K` 蕴含 `U.Nonempty`）。
若第 `j` 行仅保留对角输入项（`∀ k ≠ j, L_{k → j} = 0`），则对任意 `x, y ∈ U`：
`K_{j → j} * d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} * d_j(x, y)`。
-/
theorem scalar_two_sided_bound_of_diagonal_input {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L K : GaugeMatrix I) (j : I)
    (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hdiag_row : IsDiagonalInputRow L j) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L j j * d j x y := by
  intro x hx y hy
  constructor
  · have hterm : channelEntry K j j * d j x y ≤ ∑ k : I, channelEntry K k j * d k x y :=
      Finset.single_le_sum (f := fun k => channelEntry K k j * d k x y)
        (fun _ _ => zero_le _) (Finset.mem_univ j)
    exact le_trans hterm (hK.2.2 x hx y hy j)
  · exact (singleInputRow_lip_reduction d ϕ U L j j hL hdiag_row x hx y hy).2.2

end LCH01
```

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import GaugeMatrix
import ComponentChannel

/-!
# LCH01 主入口模块

导入全部冻结前置模块及本任务自建模块（`GaugeMatrix`、`ComponentChannel`），
覆盖 `obligations.json` 中的全部 8 项义务：
`CH02-D01`, `CH02-D02`, `CH02-D03`, `CH02-D07`,
`CH02-P19`, `CH02-P20`, `CH02-P21`, `CH02-P25`。
-/
```

```json filename=alignment.json
{
  "case_id": "LCH01",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        { "file": "GaugeMatrix.lean", "name": "LCH01.IsLipMatrix" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.lipMatrices" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.IsRestrictedLipMatrix" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedLipMatrices" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedLipMatrices_subset_dom" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.isRestrictedLipMatrix_dom_iff" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedLipMatrices_dom_eq" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedLipMatrices_antitone" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.lipMatrices_subset_restrictedLipMatrices" }
      ],
      "representation": "在底层空间 `(X : Type)`、吸收元 `(bot : X)`、有限指标集 `(I : Type)` (`[Fintype I]`) 与规范族 `(d : I → X → X → ENNReal)` 及算子 `(ϕ : Operator X bot)` 上：`IsLipMatrix d ϕ L` 对应全域 Lipschitz 矩阵谓词，全称量化 `∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y`；`lipMatrices d ϕ` 对应证书族 `ℒ(ϕ)`。`IsRestrictedLipMatrix d ϕ U L` 对应受限 Lipschitz 矩阵谓词，显式合取定义域条件 `U ⊆ dom ϕ` 与在 `U` 上全称量化的同一距离放缩不等式；`restrictedLipMatrices d ϕ U` 对应证书族 `ℒ(ϕ)|_U`。`isRestrictedLipMatrix_dom_iff`、`restrictedLipMatrices_dom_eq`、`restrictedLipMatrices_antitone` 与 `lipMatrices_subset_restrictedLipMatrices` 进一步刻画了全域与 `dom ϕ` 受限情形的一致性及引理 2.1 的单调性。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        { "file": "GaugeMatrix.lean", "name": "LCH01.IsRestrictedCoLipMatrix" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedCoLipMatrices" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedCoLipMatrices_nonempty" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedCoLipMatrices_subset_dom" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedCoLipMatrices_empty" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.restrictedCoLipMatrices_antitone" }
      ],
      "representation": "针对算子 `(ϕ : Operator X bot)` 与子集 `(U : Set X)`：`IsRestrictedCoLipMatrix d ϕ U K` 显式合取非空条件 `U.Nonempty`、定义域条件 `U ⊆ dom ϕ`，以及对所有 `x, y ∈ U` 与所有输出分量 `j : I` 的 co-Lipschitz 下界不等式 `∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)`；`restrictedCoLipMatrices d ϕ U` 定义为满足该谓词的矩阵集合，即证书族 `𝒦(ϕ)|_U`。由于非空性直接内置于谓词，任意 `K ∈ restrictedCoLipMatrices d ϕ U` 均自动蕴含 `U.Nonempty`（`restrictedCoLipMatrices_nonempty`）与 `U ⊆ dom ϕ`（`restrictedCoLipMatrices_subset_dom`），且空集上的证书族恒为空集（`restrictedCoLipMatrices_empty`）。`restrictedCoLipMatrices_antitone` 刻画了引理 2.3 的单调性。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        { "file": "GaugeMatrix.lean", "name": "LCH01.GaugeMatrix" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.channelEntry" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.ofChannelEntries" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.channelEntry_ofChannelEntries" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.gaugeMatrix_ext" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.channelEntry_mul" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.channelEntry_one" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.gaugeMatrix_mul_assoc" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.gaugeMatrix_one_mul" },
        { "file": "GaugeMatrix.lean", "name": "LCH01.gaugeMatrix_mul_one" }
      ],
      "representation": "`GaugeMatrix I` 定义为 `Matrix I I ENNReal`，条目取值于扩展非负实数 `ENNReal`（满足 `0 * ⊤ = 0` 与 `⊤ * 0 = 0` 的标准 `ℝ̄₊` 算术），矩阵第一指标（行）对应输出分量 `j`，第二指标（列）对应输入分量 `i`。`channelEntry M i j := M j i` 严格对应原文箭头记号 `M_{i → j} = (M)_{j i}`；`ofChannelEntries` 由箭头函数 `i → j ↦ ENNReal` 构造矩阵。矩阵乘法直接使用 `Matrix I I ENNReal` 上的标准乘法 `M₂ * M₁`，`channelEntry_mul` 证明了其箭头条目公式 `(M₂ * M₁)_{i → j} = ∑ k : I, (M₂)_{k → j} * (M₁)_{i → k}`；`channelEntry_one` 与结合律、单位律定理一并给出完整代数刻画。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        { "file": "ComponentChannel.lean", "name": "LCH01.ComponentChannel" },
        { "file": "ComponentChannel.lean", "name": "LCH01.sameComponentChannel" },
        { "file": "ComponentChannel.lean", "name": "LCH01.channelCoeff" },
        { "file": "ComponentChannel.lean", "name": "LCH01.IsInactiveChannel" },
        { "file": "ComponentChannel.lean", "name": "LCH01.IsSingleInputRow" },
        { "file": "ComponentChannel.lean", "name": "LCH01.IsDiagonalInputRow" },
        { "file": "ComponentChannel.lean", "name": "LCH01.IsDiagonalMatrix" },
        { "file": "ComponentChannel.lean", "name": "LCH01.diagonalGaugeMatrix" },
        { "file": "ComponentChannel.lean", "name": "LCH01.channelEntry_diagonalGaugeMatrix" },
        { "file": "ComponentChannel.lean", "name": "LCH01.diagonalGaugeMatrix_isDiagonal" },
        { "file": "ComponentChannel.lean", "name": "LCH01.one_isDiagonalMatrix" },
        { "file": "ComponentChannel.lean", "name": "LCH01.isDiagonalMatrix_iff_forall_singleInputRow" }
      ],
      "representation": "`ComponentChannel I` 将从输入分量 `d_i` 到输出分量 `d_j` 的有序对 `(i, j)` 形式化为含 `input : I` 与 `output : I` 的记录结构；`sameComponentChannel i` 表示同分量通道 `(i, i)`，`channelCoeff M c` 读取条目 `M_{c.input → c.output}`。`IsInactiveChannel M c` 表示零系数通道 `M_{c.input → c.output} = 0`。`IsSingleInputRow M i j` 形式化第 `j` 行单行稀疏条件 `∀ k : I, k ≠ i → channelEntry M k j = 0`（除 `M_{i → j}` 外全为零）；`IsDiagonalInputRow M j` 为 `IsSingleInputRow M j j`。`IsDiagonalMatrix M` 形式化对角矩阵条件 `∀ i j : I, i ≠ j → channelEntry M i j = 0`，`diagonalGaugeMatrix` 构造对角矩阵，且 `isDiagonalMatrix_iff_forall_singleInputRow` 证明了对角矩阵等价于每一行均仅保留同分量对角输入项。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        { "file": "ComponentChannel.lean", "name": "LCH01.sum_omit_of_inactive_channel" },
        { "file": "ComponentChannel.lean", "name": "LCH01.sum_eq_single_of_singleInputRow" },
        { "file": "ComponentChannel.lean", "name": "LCH01.singleInputRow_lip_reduction" },
        { "file": "ComponentChannel.lean", "name": "LCH01.diagonal_lip_reduction" }
      ],
      "representation": "`sum_omit_of_inactive_channel` 证明零条目 `M_{c.input → c.output} = 0` 不参与输出分量的加权求和上界。`sum_eq_single_of_singleInputRow` 在 `IsSingleInputRow L i j` 前提下证明求和坍缩等式 `∑ k : I, channelEntry L k j * d k x y = channelEntry L i j * d i x y`。`singleInputRow_lip_reduction` 对任意 `L ∈ restrictedLipMatrices d ϕ U`（已包含 `U ⊆ dom ϕ`）与 `IsSingleInputRow L i j`，对所有 `x, y ∈ U` 同时给出原文不等式链 `d j (ϕ.func x) (ϕ.func y) ≤ ∑ k, L_{k → j} * d k x y`、中间等式 `∑ k, L_{k → j} * d k x y = L_{i → j} * d i x y` 与化简结论 `d j (ϕ.func x) (ϕ.func y) ≤ L_{i → j} * d i x y`。`diagonal_lip_reduction` 在 `IsDiagonalMatrix L` 前提下对所有同分量通道 `(i, i)` 全称量化证明该化简成立。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        { "file": "ComponentChannel.lean", "name": "LCH01.pos_colip_channel_preserves_pos_dist" },
        { "file": "ComponentChannel.lean", "name": "LCH01.pos_colip_componentChannel_preserves_pos_dist" }
      ],
      "representation": "形式化命题 2.8(i)：设 `K ∈ restrictedCoLipMatrices d ϕ U`（其内部已含 `U.Nonempty` 与 `U ⊆ dom ϕ`）且对给定通道 `(i, j)`（或 `c : ComponentChannel I`）有严格正条件 `0 < channelEntry K i j`（或 `0 < channelCoeff K c`），则对所有 `x ∈ U, y ∈ U`，结论严格保留原文蕴含强度 `0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y)`。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        { "file": "ComponentChannel.lean", "name": "LCH01.diag_pos_colip_reflects_gauge_zero_related" },
        { "file": "ComponentChannel.lean", "name": "LCH01.diag_pos_colip_not_implies_eq" }
      ],
      "representation": "形式化命题 2.8(ii)：在 `K ∈ restrictedCoLipMatrices d ϕ U` 且对所有分量 `∀ j : I, 0 < channelEntry K j j` 的前提下（不引入 `IsSeparating d`），`diag_pos_colip_reflects_gauge_zero_related` 对任意 `x, y ∈ U` 得出 `GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y`，直接复用前置模块 `formal_oet.vol_01.ch_01_foundations.GaugeZeroRelated`，结论不加强为点相等 `x = y`。此外，`diag_pos_colip_not_implies_eq` 构造了一个满足全部 `ExtendedPseudoMetric` 公理与 `[Fintype I] [Nonempty I]` 的显式非分离空间反例，严格证明在相同前提下不能推出 `x = y`。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        { "file": "ComponentChannel.lean", "name": "LCH01.scalar_two_sided_bound_of_diagonal_input" }
      ],
      "representation": "形式化习题 2.2：固定算子 `ϕ : Operator X bot`、子集 `U : Set X` 与输出分量 `j : I`，前提 `hL : L ∈ restrictedLipMatrices d ϕ U`（蕴含 `U ⊆ dom ϕ`）、`hK : K ∈ restrictedCoLipMatrices d ϕ U`（蕴含 `U.Nonempty` 与 `U ⊆ dom ϕ`）以及单行对角保留条件 `hdiag_row : IsDiagonalInputRow L j`（即 `∀ k ≠ j, L_{k → j} = 0`）；结论对所有 `x, y ∈ U` 给出标量双侧界 `channelEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧ d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L j j * d j x y`。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```
