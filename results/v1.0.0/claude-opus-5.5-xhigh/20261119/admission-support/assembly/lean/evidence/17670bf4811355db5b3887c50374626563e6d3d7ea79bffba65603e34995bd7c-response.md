8 项义务已全部完成，均为 complete，放在一个文件 `Main.lean` 里。用 `lake env lean Main.lean` 编译通过，没有错误也没有警告。对全部 35 个定理跑过 `#print axioms`，依赖的只有 `propext`、`Classical.choice`、`Quot.sound`。文件里没有 `sorry`、`admit`，也没有新增公理。

几点说明：

- **单文件**：所有内容放在 `Main.lean` 一个文件里。它只导入固定版本 mathlib 和冻结的 `formal_oet` 模块，所以用现有 lakefile 就能编译，不需要另建 Lean 库。冻结模块没有改动。
- **前提比原文弱，结论不变**：主定理只要求 `[Fintype I]` 和任意一族 `d : I → X → X → ENNReal`，不需要伪度量公理，也不需要 `I` 非空，因此比原文更强。另外附了 `*_textbook` 版本，把原文的完整前提补回来：`[Nonempty I]`、`∀ i, ExtendedPseudoMetric X bot (d i)`，以及 `U ⊆ dom ϕ`（如原文有此前提）。
- **定义域条件写进谓词**：受限 Lip 谓词包含 `U ⊆ dom ϕ`；受限 co-Lip 谓词同时包含 `U ⊆ dom ϕ` 和 `U.Nonempty`。所以 `U` 为空时 co-Lip 证书族是空集。
- **CH02-P21 附加了一个反例（不在义务清单内）**：在非分离空间里，命题 2.8(ii) 的结论不能加强为点相等。构造是 `Option Bool`，恒等算子取单位矩阵 `1` 作 co-Lip 证书，两个不同的点距离为零。

```lean filename=Main.lean
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# LCH01 · 通道接口节群（第 2 章 §2.1 矩阵界定义、§2.2 分量通道、习题 2.2）

Source: Zhe Li (Glen Li / glenzli), *The Operator Evolution Theory*, Volume I,
`source/02-operator-bounds.md`, CC BY 4.0.

本文件形式化 `obligations.json` 中的 8 项义务：

* CH02-D01 全域/受限 Lip 矩阵谓词与证书族；
* CH02-D02 含非空条件的受限 co-Lip 矩阵及证书族；
* CH02-D03 输入/输出矩阵指标约定与乘法；
* CH02-D07 单输入通道、单行稀疏与对角特例；
* CH02-P19 单一输入项行化简（含对角特例）；
* CH02-P20 正 co-Lip 通道保持正距离；
* CH02-P21 全对角正 co-Lip 反射族零距（不加强为点相等）；
* CH02-P25 习题 2.2：标量双侧界。

约定：规范族 `{d_i}_{i ∈ I}` 表示为 `d : I → X → X → ENNReal`，
`ENNReal` 即 `[0, +∞]`，其乘法满足 `0 · (+∞) = 0`；
有限指标集用 `[Fintype I]` 表示。各主定理不需要伪度量公理，
因而对任意分量族成立；`*_textbook` 版本补回正文的全部规范空间语境。
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

set_option linter.style.longLine false

/-! ## CH02-D03：输入/输出矩阵指标约定与乘法 -/

/--
以 `I` 为指标集的扩展非负矩阵 `(L_{i→j})`，条目取值于 `[0, +∞]`。
采用 mathlib 的 `Matrix I I ENNReal`：第一个下标为行（输出分量），
第二个下标为列（输入分量），即 `(𝐋)_{ji} = L_{i→j}`。
-/
abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

/-- 条目 `L_{i→j}`：从输入分量 `d_i` 到输出分量 `d_j` 的系数，位于第 `j` 行、第 `i` 列。 -/
def entry {I : Type} (M : BoundMatrix I) (i j : I) : ENNReal := M j i

/-- 行列约定：`L_{i→j} = (𝐋)_{ji}`。 -/
@[simp] theorem entry_apply {I : Type} (M : BoundMatrix I) (i j : I) :
    entry M i j = M j i := rfl

/-- 第 `j` 行汇集指向输出分量 `d_j` 的全部系数 `(L_{i→j})_{i}`。 -/
theorem row_eq_entries {I : Type} (M : BoundMatrix I) (j : I) :
    M j = fun i => entry M i j := rfl

/-- 第 `i` 列汇集从输入分量 `d_i` 出发的全部系数 `(L_{i→j})_{j}`。 -/
theorem col_eq_entries {I : Type} (M : BoundMatrix I) (i : I) :
    (fun j => M j i) = fun j => entry M i j := rfl

/--
正文 `I = {1,2,3}` 的示例（`Fin 3` 中 `0,1,2` 依次对应 `d_1,d_2,d_3`）：
矩阵按通常行列形式写为
`(L_{1→1} L_{2→1} L_{3→1}; L_{1→2} L_{2→2} L_{3→2}; L_{1→3} L_{2→3} L_{3→3})`。
-/
theorem fin_three_layout (M : BoundMatrix (Fin 3)) :
    M = !![entry M 0 0, entry M 1 0, entry M 2 0;
           entry M 0 1, entry M 1 1, entry M 2 1;
           entry M 0 2, entry M 1 2, entry M 2 2] := by
  ext j i
  fin_cases j <;> fin_cases i <;> rfl

/-- 示例：`L_{2→1}` 位于第一行、第二列。 -/
theorem fin_three_entry_two_to_one (a₁₁ a₂₁ a₃₁ a₁₂ a₂₂ a₃₂ a₁₃ a₂₃ a₃₃ : ENNReal) :
    entry !![a₁₁, a₂₁, a₃₁; a₁₂, a₂₂, a₃₂; a₁₃, a₂₃, a₃₃] 1 0 = a₂₁ := rfl

/--
矩阵乘法的条目公式：
`(𝐋^{(2)} · 𝐋^{(1)})_{i→j} = ∑_{k∈I} L^{(2)}_{k→j} · L^{(1)}_{i→k}`，
乘法即 mathlib 的矩阵乘法 `M₂ * M₁`。
-/
theorem entry_mul {I : Type} [Fintype I] (M₂ M₁ : BoundMatrix I) (i j : I) :
    entry (M₂ * M₁) i j = ∑ k, entry M₂ k j * entry M₁ i k := by
  simp [entry, Matrix.mul_apply]

/-- 单位矩阵（空复合乘积）的条目：`𝐈_{i→j} = 1` 当 `i = j`，否则为 `0`。 -/
theorem entry_one {I : Type} [DecidableEq I] (i j : I) :
    entry (1 : BoundMatrix I) i j = if i = j then 1 else 0 := by
  simp [entry, Matrix.one_apply, eq_comm]

/--
指标约定与乘法相容：先以 `𝐋^{(1)}` 再以 `𝐋^{(2)}` 作用于输入距离向量 `v`，
交换有限和次序后恰为乘积矩阵 `𝐋^{(2)} · 𝐋^{(1)}` 作用于 `v`
（在 `[0,+∞]` 中，`0·(+∞)=0` 下分配律成立）。
-/
theorem sum_entry_mul_sum {I : Type} [Fintype I] (M₂ M₁ : BoundMatrix I)
    (v : I → ENNReal) (j : I) :
    ∑ k, entry M₂ k j * (∑ i, entry M₁ i k * v i) =
      ∑ i, entry (M₂ * M₁) i j * v i := by
  simp only [entry_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- `[0,+∞]` 算术约定：`0 · (+∞) = 0`，以及 `a > 0 ⇒ a · (+∞) = +∞`、`a + (+∞) = +∞`。 -/
theorem ennreal_conventions (a : ENNReal) :
    (0 : ENNReal) * ⊤ = 0 ∧ (a ≠ 0 → a * ⊤ = ⊤) ∧ a + ⊤ = ⊤ :=
  ⟨zero_mul _, fun ha => ENNReal.mul_top ha, add_top a⟩

variable {X I : Type} {bot : X} [Fintype I]

/-! ## CH02-D01：全域/受限 Lip 矩阵谓词与证书族 -/

/--
**定义（Lipschitz 矩阵）**：`L` 是 `ϕ` 的合法 Lip 矩阵，当且仅当对所有
`x, y ∈ dom(ϕ)` 与所有 `j ∈ I`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i∈I} L_{i→j} · d_i(x, y)`。
-/
def IsLipMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : BoundMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, entry L i j * d i x y

/-- 全体合法 Lip 矩阵之集（证书族）`𝓛(ϕ)`。 -/
def lipMatrices (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (BoundMatrix I) :=
  {L | IsLipMatrix d ϕ L}

/--
**定义（子集受限 Lip 矩阵）**：对子集 `U ⊆ dom(ϕ)`，若对任意 `x, y ∈ U`
与所有 `j ∈ I` 满足 Lip 不等式，则称 `L` 为 `ϕ` 在 `U` 上的受限 Lip 矩阵。
正文的前提 `U ⊆ dom(ϕ)` 作为谓词的第一个合取项记录。
-/
structure IsRestrictedLipMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop where
  subset_dom : U ⊆ dom ϕ
  le : ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, entry L i j * d i x y

/-- 受限合法 Lip 矩阵之集（证书族）`𝓛(ϕ)|_U`。 -/
def restrictedLipMatrices (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (BoundMatrix I) :=
  {L | IsRestrictedLipMatrix d ϕ U L}

theorem mem_lipMatrices_iff (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : BoundMatrix I) :
    L ∈ lipMatrices d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
        d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, entry L i j * d i x y :=
  Iff.rfl

theorem mem_restrictedLipMatrices_iff (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) :
    L ∈ restrictedLipMatrices d ϕ U ↔
      U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
        d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, entry L i j * d i x y :=
  ⟨fun h => ⟨h.subset_dom, h.le⟩, fun h => ⟨h.1, h.2⟩⟩

/-- 全域证书族即在 `U = dom(ϕ)` 上的受限证书族。 -/
theorem restrictedLipMatrices_dom (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedLipMatrices d ϕ (dom ϕ) = lipMatrices d ϕ := by
  ext L
  exact ⟨fun h => h.le, fun h => ⟨subset_rfl, h⟩⟩

omit [Fintype I] in
/--
**约定（广义 Lip）**：条目 `L_{i→j} = +∞` 但 `d_i(x,y) = 0` 时，该项对右端和的贡献为零。
-/
theorem lip_term_eq_zero_of_dist_eq_zero (d : I → X → X → ENNReal) (L : BoundMatrix I)
    {i : I} (j : I) {x y : X} (h : d i x y = 0) :
    entry L i j * d i x y = 0 := by
  rw [h, mul_zero]

/--
**约定（广义 Lip）**：当 `L_{i→j} = +∞` 且 `d_i(x,y) > 0` 时，该项为 `+∞`，
`d_j` 输出的 Lip 不等式平凡成立。
-/
theorem lip_ineq_of_entry_eq_top (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (L : BoundMatrix I) {i j : I} {x y : X} (hL : entry L i j = ⊤) (hd : 0 < d i x y) :
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ k, entry L k j * d k x y := by
  have hterm : entry L i j * d i x y = ⊤ := by
    rw [hL]
    exact ENNReal.top_mul hd.ne'
  have hsum : ∑ k, entry L k j * d k x y = ⊤ := by
    apply top_le_iff.mp
    rw [← hterm]
    exact Finset.single_le_sum (f := fun k => entry L k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  rw [hsum]
  exact le_top

/-! ## CH02-D02：含非空条件的受限 co-Lip 矩阵及证书族 -/

/--
**定义（子集受限 co-Lipschitz 矩阵）**：对非空子集 `U ⊆ dom(ϕ)`，
`K` 是 `ϕ` 在 `U` 上的合法受限 co-Lip 矩阵，当且仅当对所有 `x, y ∈ U`
与所有 `j ∈ I`，`d_j(ϕ(x), ϕ(y)) ≥ ∑_{i∈I} K_{i→j} · d_i(x, y)`。
正文的定义域前提 `U ⊆ dom(ϕ)` 与非空性条件 `U ≠ ∅` 均作为谓词的合取项记录。
-/
structure IsRestrictedCoLipMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) : Prop where
  subset_dom : U ⊆ dom ϕ
  nonempty : U.Nonempty
  ge : ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i, entry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- 受限合法 co-Lip 矩阵之集（下界证书族）`𝓚(ϕ)|_U`。 -/
def restrictedCoLipMatrices (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (BoundMatrix I) :=
  {K | IsRestrictedCoLipMatrix d ϕ U K}

theorem mem_restrictedCoLipMatrices_iff (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) :
    K ∈ restrictedCoLipMatrices d ϕ U ↔
      U ⊆ dom ϕ ∧ U.Nonempty ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
        ∑ i, entry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) :=
  ⟨fun h => ⟨h.subset_dom, h.nonempty, h.ge⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- 凡出现 `𝓚(ϕ)|_U`，均含非空性条件 `U ≠ ∅`。 -/
theorem nonempty_of_mem_restrictedCoLipMatrices {d : I → X → X → ENNReal}
    {ϕ : Operator X bot} {U : Set X} {K : BoundMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) : U.Nonempty :=
  hK.nonempty

/-- 空集上没有合法受限 co-Lip 矩阵。 -/
theorem restrictedCoLipMatrices_empty (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedCoLipMatrices d ϕ ∅ = (∅ : Set (BoundMatrix I)) := by
  ext K
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hK
  exact Set.not_nonempty_empty (nonempty_of_mem_restrictedCoLipMatrices hK)

/-! ## CH02-D07：单输入通道、单行稀疏与对角特例 -/

/-- **定义（分量通道）**：有序对 `(i, j)`，从输入分量 `d_i` 到输出分量 `d_j`。 -/
abbrev ComponentChannel (I : Type) := I × I

/-- 通道的输入分量指标 `i`。 -/
def ComponentChannel.input {I : Type} (c : ComponentChannel I) : I := c.1

/-- 通道的输出分量指标 `j`。 -/
def ComponentChannel.output {I : Type} (c : ComponentChannel I) : I := c.2

/-- 矩阵在通道 `(i, j)` 上的系数 `L_{i→j}`。 -/
def channelCoeff {I : Type} (M : BoundMatrix I) (c : ComponentChannel I) : ENNReal :=
  entry M c.input c.output

@[simp] theorem channelCoeff_mk {I : Type} (M : BoundMatrix I) (i j : I) :
    channelCoeff M (i, j) = entry M i j := rfl

/--
单输入通道系数为零时，相应项不参与 `d_j` 输出的上界：
`∑_{k∈I} L_{k→j} d_k(x,y) = ∑_{k≠i} L_{k→j} d_k(x,y)`。
-/
theorem bound_sum_eq_sum_erase_of_channelCoeff_eq_zero [DecidableEq I]
    (d : I → X → X → ENNReal) (M : BoundMatrix I) {i j : I}
    (h : channelCoeff M (i, j) = 0) (x y : X) :
    ∑ k, entry M k j * d k x y = ∑ k ∈ Finset.univ.erase i, entry M k j * d k x y := by
  symm
  apply Finset.sum_erase
  rw [← channelCoeff_mk, h, zero_mul]

/-- **单行稀疏**：第 `j` 行除 `L_{i→j}` 外均为零，即 `L_{k→j} = 0`（`∀ k ≠ i`）。 -/
def RowSingleInput {I : Type} (M : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → entry M k j = 0

/--
**对角特例**：mathlib 的 `Matrix.IsDiag`（非对角条目全为零）恰等价于
每个输出分量 `j` 所在行只保留同分量通道 `(j, j)`。
-/
theorem isDiag_iff_forall_rowSingleInput {I : Type} (M : BoundMatrix I) :
    M.IsDiag ↔ ∀ j : I, RowSingleInput M j j := by
  constructor
  · intro h j k hk
    exact h (Ne.symm hk)
  · intro h j k hjk
    exact h j k (Ne.symm hjk)

/-! ## CH02-P19：单一输入项行化简（含对角特例） -/

/-- 行化简的代数核心：第 `j` 行仅含 `L_{i→j}` 时，`∑_k L_{k→j} v_k = L_{i→j} v_i`。 -/
theorem row_sum_eq_single {M : BoundMatrix I} {i j : I} (hrow : RowSingleInput M i j)
    (v : I → ENNReal) :
    ∑ k, entry M k j * v k = entry M i j * v i := by
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [hrow k hk, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/--
**§2.2（单一输入项行化简）**：设 `U ⊆ dom(ϕ)`，`L ∈ 𝓛(ϕ)|_U`。若第 `j` 行除 `L_{i→j}`
外均为零，则对任意 `x, y ∈ U`，
`d_j(ϕ(x),ϕ(y)) ≤ ∑_{k∈I} L_{k→j} d_k(x,y) = L_{i→j} d_i(x,y)`。
-/
theorem lip_row_single_input {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L : BoundMatrix I} (hL : L ∈ restrictedLipMatrices d ϕ U) {i j : I}
    (hrow : RowSingleInput L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k, entry L k j * d k x y ∧
        ∑ k, entry L k j * d k x y = entry L i j * d i x y := by
  intro x hx y hy
  exact ⟨hL.le x hx y hy j, row_sum_eq_single hrow (fun k => d k x y)⟩

/-- `lip_row_single_input` 的化简后形式：`d_j(ϕ(x),ϕ(y)) ≤ L_{i→j} d_i(x,y)`。 -/
theorem lip_row_single_input_le {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L : BoundMatrix I} (hL : L ∈ restrictedLipMatrices d ϕ U) {i j : I}
    (hrow : RowSingleInput L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ entry L i j * d i x y := by
  intro x hx y hy
  obtain ⟨hle, heq⟩ := lip_row_single_input hL hrow x hx y hy
  exact heq ▸ hle

/--
**§2.2（对角特例）**：若 `L ∈ 𝓛(ϕ)|_U` 为对角矩阵，则上述化简对每个同分量通道
`(i, i)` 成立：`d_i(ϕ(x),ϕ(y)) ≤ ∑_k L_{k→i} d_k(x,y) = L_{i→i} d_i(x,y)`。
-/
theorem lip_diagonal {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L : BoundMatrix I} (hL : L ∈ restrictedLipMatrices d ϕ U) (hdiag : L.IsDiag) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k, entry L k i * d k x y ∧
        ∑ k, entry L k i * d k x y = entry L i i * d i x y := by
  intro i
  exact lip_row_single_input hL ((isDiag_iff_forall_rowSingleInput L).mp hdiag i)

set_option linter.unusedVariables false in
/-- P19 的正文同形版本：保留有限非空指标族、规范空间公理与 `U ⊆ dom(ϕ)` 的完整语境。 -/
theorem lip_row_single_input_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) (L : BoundMatrix I) (hL : L ∈ restrictedLipMatrices d ϕ U) :
    (∀ i j : I, RowSingleInput L i j → ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k, entry L k j * d k x y ∧
        ∑ k, entry L k j * d k x y = entry L i j * d i x y) ∧
    (L.IsDiag → ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k, entry L k i * d k x y ∧
        ∑ k, entry L k i * d k x y = entry L i i * d i x y) :=
  ⟨fun _ _ hrow => lip_row_single_input hL hrow, fun hdiag => lip_diagonal hL hdiag⟩

/-! ## CH02-P20：正 co-Lip 通道保持正距离 -/

/-- co-Lip 不等式与非负性：`d_j(ϕ(x),ϕ(y)) ≥ ∑_k K_{k→j} d_k(x,y) ≥ K_{i→j} d_i(x,y)`。 -/
theorem coLip_single_term_le {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {K : BoundMatrix I} (hK : K ∈ restrictedCoLipMatrices d ϕ U) (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K i j * d i x y ≤ ∑ k, entry K k j * d k x y ∧
        ∑ k, entry K k j * d k x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  refine ⟨?_, hK.ge x hx y hy j⟩
  exact Finset.single_le_sum (f := fun k => entry K k j * d k x y)
    (fun _ _ => zero_le _) (Finset.mem_univ i)

/--
**命题 2.8 (i)**：设 `K ∈ 𝓚(ϕ)|_U`。若 `K_{i→j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x,y) > 0 ⇒ d_j(ϕ(x),ϕ(y)) > 0`。
-/
theorem coLip_pos_channel {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {K : BoundMatrix I} (hK : K ∈ restrictedCoLipMatrices d ϕ U) {i j : I}
    (hij : 0 < entry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hxy
  obtain ⟨h₁, h₂⟩ := coLip_single_term_le hK i j x hx y hy
  exact lt_of_lt_of_le (ENNReal.mul_pos hij.ne' hxy.ne') (h₁.trans h₂)

set_option linter.unusedVariables false in
/-- 命题 2.8 (i) 的正文同形版本：保留规范空间的完整语境。 -/
theorem coLip_pos_channel_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) (hK : K ∈ restrictedCoLipMatrices d ϕ U) (i j : I)
    (hij : 0 < entry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) :=
  coLip_pos_channel hK hij

/-! ## CH02-P21：全对角正 co-Lip 反射族零距（不加强为点相等） -/

/--
**命题 2.8 (ii)**：设 `K ∈ 𝓚(ϕ)|_U`。若 `K_{j→j} > 0` 对所有 `j ∈ I` 成立，则 `ϕ` 在 `U`
上反射族零距关系：`ϕ(x) ∼_𝒢 ϕ(y) ⇒ x ∼_𝒢 y`（结论是族零距关系，而非点相等）。
-/
theorem coLip_reflects_gaugeZeroRelated {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {K : BoundMatrix I} (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hdiag : ∀ j : I, 0 < entry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hj
  have hpos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    coLip_pos_channel hK (hdiag j) x hx y hy (pos_iff_ne_zero.mpr hj)
  exact hpos.ne' (hrel j)

set_option linter.unusedVariables false in
/-- 命题 2.8 (ii) 的正文同形版本：保留规范空间的完整语境。 -/
theorem coLip_reflects_gaugeZeroRelated_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hdiag : ∀ j : I, 0 < entry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y :=
  coLip_reflects_gaugeZeroRelated hK hdiag

/-! ### 不加强为点相等：非分离规范空间中的反例 -/

/-- 反例空间 `Option Bool`，吸收元为 `none`；两点 `some false ≠ some true` 零距。 -/
def ceDist : Unit → Option Bool → Option Bool → ENNReal
  | _, none, none => 0
  | _, some _, some _ => 0
  | _, _, _ => ⊤

theorem ceDist_isExtendedPseudoMetric (i : Unit) :
    ExtendedPseudoMetric (Option Bool) none (ceDist i) where
  nonabsorbing := ⟨some true, by simp⟩
  dist_self x := by cases x <;> rfl
  symm x y := by cases x <;> cases y <;> rfl
  triangle x y z := by cases x <;> cases y <;> cases z <;> simp [ceDist]
  isolate_bot x hx := by
    cases x with
    | none => exact absurd rfl hx
    | some _ => rfl

/-- 反例算子：恒等算子。 -/
def ceOp : Operator (Option Bool) none := ⟨id, rfl⟩

/-- 反例评估域：两个零距但不同的非吸收点。 -/
def ceDom : Set (Option Bool) := {some false, some true}

/-- 恒等算子在 `ceDom` 上以单位矩阵为合法受限 co-Lip 矩阵。 -/
theorem ce_one_mem_restrictedCoLipMatrices :
    (1 : BoundMatrix Unit) ∈ restrictedCoLipMatrices ceDist ceOp ceDom := by
  refine ⟨?_, ⟨some false, Or.inl rfl⟩, ?_⟩
  · rintro x (rfl | rfl) <;> simp [dom, ceOp]
  · intro x _ y _ j
    simp [entry, ceOp]

/--
命题 2.8 (ii) 的结论不能加强为点相等：存在规范空间、算子 `ϕ`、非空 `U ⊆ dom(ϕ)` 与
全对角正的 `K ∈ 𝓚(ϕ)|_U`，以及 `x, y ∈ U` 使 `ϕ(x) ∼_𝒢 ϕ(y)` 但 `x ≠ y`。
-/
theorem coLip_reflects_not_point_eq :
    (∀ i : Unit, ExtendedPseudoMetric (Option Bool) none (ceDist i)) ∧
    (1 : BoundMatrix Unit) ∈ restrictedCoLipMatrices ceDist ceOp ceDom ∧
    (∀ j : Unit, 0 < entry (1 : BoundMatrix Unit) j j) ∧
    ∃ x ∈ ceDom, ∃ y ∈ ceDom,
      GaugeZeroRelated ceDist (ceOp.func x) (ceOp.func y) ∧ x ≠ y := by
  refine ⟨ceDist_isExtendedPseudoMetric, ce_one_mem_restrictedCoLipMatrices, ?_, ?_⟩
  · intro j
    simp [entry]
  · refine ⟨some false, Or.inl rfl, some true, Or.inr rfl, ?_, by simp⟩
    intro i
    rfl

/-! ## CH02-P25：习题 2.2（对角输入项的标量双侧界） -/

/--
**习题 2.2**：设 `ϕ ∈ 𝒳_op`，`U ⊆ dom(ϕ)`，`j ∈ I`，`L ∈ 𝓛(ϕ)|_U`，`K ∈ 𝓚(ϕ)|_U`。
若 `L_{k→j} = 0`（`∀ k ≠ j`），则对任意 `x, y ∈ U`，
`K_{j→j} · d_j(x,y) ≤ d_j(ϕ(x),ϕ(y)) ≤ L_{j→j} · d_j(x,y)`。
-/
theorem scalar_two_sided_bound {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L K : BoundMatrix I} (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) (j : I)
    (hrow : ∀ k : I, k ≠ j → entry L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ entry L j j * d j x y := by
  intro x hx y hy
  obtain ⟨h₁, h₂⟩ := coLip_single_term_le hK j j x hx y hy
  exact ⟨h₁.trans h₂, lip_row_single_input_le hL hrow x hx y hy⟩

set_option linter.unusedVariables false in
/-- 习题 2.2 的正文同形版本：保留规范空间语境与前提 `U ⊆ dom(ϕ)`。 -/
theorem scalar_two_sided_bound_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) (j : I) (L K : BoundMatrix I) (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) (hrow : ∀ k : I, k ≠ j → entry L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ entry L j j * d j x y :=
  scalar_two_sided_bound hL hK j hrow

end LCH01
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
        {"file": "Main.lean", "name": "LCH01.IsLipMatrix"},
        {"file": "Main.lean", "name": "LCH01.lipMatrices"},
        {"file": "Main.lean", "name": "LCH01.IsRestrictedLipMatrix"},
        {"file": "Main.lean", "name": "LCH01.restrictedLipMatrices"},
        {"file": "Main.lean", "name": "LCH01.mem_lipMatrices_iff"},
        {"file": "Main.lean", "name": "LCH01.mem_restrictedLipMatrices_iff"},
        {"file": "Main.lean", "name": "LCH01.restrictedLipMatrices_dom"},
        {"file": "Main.lean", "name": "LCH01.lip_term_eq_zero_of_dist_eq_zero"},
        {"file": "Main.lean", "name": "LCH01.lip_ineq_of_entry_eq_top"}
      ],
      "representation": "对象：X 为带吸收元 bot 的类型，算子 ϕ : Operator X bot（冻结模块），dom ϕ 为冻结模块的定义域，规范族 {d_i} 为 d : I → X → X → ENNReal，有限指标集为 [Fintype I]，矩阵 L : BoundMatrix I = Matrix I I ENNReal（条目在 [0,+∞]，自动非负，允许 +∞），条目 L_{i→j} = entry L i j。全域 Lip 谓词 IsLipMatrix d ϕ L：∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j, d j (ϕ x) (ϕ y) ≤ ∑ i, entry L i j * d i x y，与正文量词与不等式一致；证书族 𝓛(ϕ) = lipMatrices d ϕ（集合）。受限谓词 IsRestrictedLipMatrix d ϕ U L：正文前提 U ⊆ dom(ϕ)（字段 subset_dom）且 ∀ x y ∈ U, ∀ j 同一不等式（字段 le）；证书族 𝓛(ϕ)|_U = restrictedLipMatrices d ϕ U（U ⊄ dom ϕ 时为空集，属全函数化处理）。mem_*_iff 给出展开形式；restrictedLipMatrices_dom 证明 𝓛(ϕ)|_{dom ϕ} = 𝓛(ϕ)。广义 Lip 约定（0·(+∞)=0；L_{i→j}=+∞ 且 d_i>0 时不等式平凡成立）由 lip_term_eq_zero_of_dist_eq_zero、lip_ineq_of_entry_eq_top 形式化。这里只定义集合，不预设存在实现下确界的指定矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "LCH01.IsRestrictedCoLipMatrix"},
        {"file": "Main.lean", "name": "LCH01.restrictedCoLipMatrices"},
        {"file": "Main.lean", "name": "LCH01.mem_restrictedCoLipMatrices_iff"},
        {"file": "Main.lean", "name": "LCH01.nonempty_of_mem_restrictedCoLipMatrices"},
        {"file": "Main.lean", "name": "LCH01.restrictedCoLipMatrices_empty"}
      ],
      "representation": "受限 co-Lip 谓词 IsRestrictedCoLipMatrix d ϕ U K 有三个字段：subset_dom : U ⊆ dom ϕ；nonempty : U.Nonempty（即正文的 U ≠ ∅）；ge : ∀ x ∈ U, ∀ y ∈ U, ∀ j, ∑ i, entry K i j * d i x y ≤ d j (ϕ x) (ϕ y)（即 d_j(ϕx,ϕy) ≥ ∑_i K_{i→j} d_i(x,y)）。下界证书族 𝓚(ϕ)|_U = restrictedCoLipMatrices d ϕ U。正文要求凡出现 𝓚(ϕ)|_U 均含非空条件：由 nonempty_of_mem_restrictedCoLipMatrices 体现，restrictedCoLipMatrices_empty 证明 𝓚(ϕ)|_∅ = ∅。mem_restrictedCoLipMatrices_iff 给出展开的合取形式。不预设存在实现上确界的指定矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "LCH01.BoundMatrix"},
        {"file": "Main.lean", "name": "LCH01.entry"},
        {"file": "Main.lean", "name": "LCH01.entry_apply"},
        {"file": "Main.lean", "name": "LCH01.row_eq_entries"},
        {"file": "Main.lean", "name": "LCH01.col_eq_entries"},
        {"file": "Main.lean", "name": "LCH01.fin_three_layout"},
        {"file": "Main.lean", "name": "LCH01.fin_three_entry_two_to_one"},
        {"file": "Main.lean", "name": "LCH01.entry_mul"},
        {"file": "Main.lean", "name": "LCH01.entry_one"},
        {"file": "Main.lean", "name": "LCH01.sum_entry_mul_sum"},
        {"file": "Main.lean", "name": "LCH01.ennreal_conventions"}
      ],
      "representation": "以输出分量为行、输入分量为列：BoundMatrix I = Matrix I I ENNReal，entry M i j := M j i，即 (𝐋)_{ji} = L_{i→j}（entry_apply）。第 j 行汇集指向输出 d_j 的系数（row_eq_entries），第 i 列汇集来自输入 d_i 的系数（col_eq_entries）。I={1,2,3} 的行列排布示例用 Fin 3（0,1,2 对应 d_1,d_2,d_3）给出：fin_three_layout 是 3×3 排布，fin_three_entry_two_to_one 说明 L_{2→1} 位于第一行第二列。乘法取 mathlib 矩阵乘法 M₂ * M₁，entry_mul 证明 (𝐋^{(2)}·𝐋^{(1)})_{i→j} = ∑_k L^{(2)}_{k→j} L^{(1)}_{i→k}；entry_one 给出单位矩阵条目；sum_entry_mul_sum 证明先用 𝐋^{(1)} 再用 𝐋^{(2)} 作用于向量 v，等于乘积矩阵直接作用（在 [0,+∞] 中交换有限和）。ennreal_conventions 记录 [0,+∞] 算术约定：0·∞=0，a>0 时 a·∞=∞，a+∞=∞。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "LCH01.ComponentChannel"},
        {"file": "Main.lean", "name": "LCH01.ComponentChannel.input"},
        {"file": "Main.lean", "name": "LCH01.ComponentChannel.output"},
        {"file": "Main.lean", "name": "LCH01.channelCoeff"},
        {"file": "Main.lean", "name": "LCH01.channelCoeff_mk"},
        {"file": "Main.lean", "name": "LCH01.bound_sum_eq_sum_erase_of_channelCoeff_eq_zero"},
        {"file": "Main.lean", "name": "LCH01.RowSingleInput"},
        {"file": "Main.lean", "name": "LCH01.isDiag_iff_forall_rowSingleInput"}
      ],
      "representation": "分量通道 (i,j) 表示为有序对 ComponentChannel I := I × I，input 取第一分量 i（输入 d_i），output 取第二分量 j（输出 d_j）。通道系数 channelCoeff M (i,j) = L_{i→j}（channelCoeff_mk）。正文“系数为零时相应项不参与该上界”由 bound_sum_eq_sum_erase_of_channelCoeff_eq_zero 形式化：∑_k L_{k→j} d_k = ∑_{k≠i} L_{k→j} d_k。单行稀疏“第 j 行除 L_{i→j} 外均为零”为 RowSingleInput M i j := ∀ k ≠ i, entry M k j = 0。对角矩阵取 mathlib 的 Matrix.IsDiag（Pairwise，非对角条目为 0）；isDiag_iff_forall_rowSingleInput 证明它等价于每个输出 j 的行只保留同分量通道 (j,j)。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "LCH01.row_sum_eq_single"},
        {"file": "Main.lean", "name": "LCH01.lip_row_single_input"},
        {"file": "Main.lean", "name": "LCH01.lip_row_single_input_le"},
        {"file": "Main.lean", "name": "LCH01.lip_diagonal"},
        {"file": "Main.lean", "name": "LCH01.lip_row_single_input_textbook"}
      ],
      "representation": "前提：L ∈ restrictedLipMatrices d ϕ U（即 𝓛(ϕ)|_U，已含 U ⊆ dom ϕ），以及 RowSingleInput L i j（第 j 行除 L_{i→j} 外为零）。结论（lip_row_single_input）：∀ x ∈ U, ∀ y ∈ U, d_j(ϕx,ϕy) ≤ ∑_k L_{k→j} d_k(x,y) 且 ∑_k L_{k→j} d_k(x,y) = L_{i→j} d_i(x,y)，与正文的不等式-等式链一致；lip_row_single_input_le 是合并后的 d_j(ϕx,ϕy) ≤ L_{i→j} d_i(x,y)。代数核心为 row_sum_eq_single。对角特例 lip_diagonal：若 L.IsDiag，则对每个 i 和所有 x,y ∈ U，链式结论对通道 (i,i) 成立。主定理对任意分量族 d 成立，不需要伪度量公理；lip_row_single_input_textbook 补回原文完整语境（[Nonempty I]、∀ i, ExtendedPseudoMetric X bot (d i)、U ⊆ dom ϕ），并同时给出一般行化简与对角特例。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "LCH01.coLip_single_term_le"},
        {"file": "Main.lean", "name": "LCH01.coLip_pos_channel"},
        {"file": "Main.lean", "name": "LCH01.coLip_pos_channel_textbook"}
      ],
      "representation": "命题 2.8(i)。前提：K ∈ restrictedCoLipMatrices d ϕ U（即 𝓚(ϕ)|_U，含 U ⊆ dom ϕ 与 U 非空），以及 0 < entry K i j（K_{i→j} > 0）。结论：∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ x) (ϕ y)。证明路线与原文一致：coLip_single_term_le 给出 K_{i→j} d_i(x,y) ≤ ∑_k K_{k→j} d_k(x,y) ≤ d_j(ϕx,ϕy)（co-Lip 不等式加非负性），再由 ENNReal.mul_pos 得到严格正。主定理对任意分量族成立；coLip_pos_channel_textbook 补回规范空间语境（[Nonempty I] 与伪度量公理）。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "LCH01.coLip_reflects_gaugeZeroRelated"},
        {"file": "Main.lean", "name": "LCH01.coLip_reflects_gaugeZeroRelated_textbook"},
        {"file": "Main.lean", "name": "LCH01.ceDist"},
        {"file": "Main.lean", "name": "LCH01.ceDist_isExtendedPseudoMetric"},
        {"file": "Main.lean", "name": "LCH01.ceOp"},
        {"file": "Main.lean", "name": "LCH01.ceDom"},
        {"file": "Main.lean", "name": "LCH01.ce_one_mem_restrictedCoLipMatrices"},
        {"file": "Main.lean", "name": "LCH01.coLip_reflects_not_point_eq"}
      ],
      "representation": "命题 2.8(ii)。前提：K ∈ 𝓚(ϕ)|_U，且 ∀ j, 0 < entry K j j（全部对角条目 K_{j→j} > 0）。结论（coLip_reflects_gaugeZeroRelated）：∀ x ∈ U, ∀ y ∈ U, GaugeZeroRelated d (ϕ x) (ϕ y) → GaugeZeroRelated d x y，即 ϕ(x) ∼_𝒢 ϕ(y) ⇒ x ∼_𝒢 y。族零距关系使用冻结模块的 GaugeZeroRelated。结论只到族零距关系，没有加强为 x = y。证明同原文：固定 j，若 d_j(x,y) > 0，则由 P20 用通道 (j,j) 得到矛盾。附加的反例 coLip_reflects_not_point_eq 说明点相等确实不成立：非分离空间 Option Bool（bot = none，ceDist 满足 ExtendedPseudoMetric），ceOp 为恒等算子，ceDom = {some false, some true} ⊆ dom，单位矩阵 1 ∈ 𝓚(ceOp)|_{ceDom} 且对角为正，但 some false ∼ some true 且两点不同。textbook 版本补回规范空间语境。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "LCH01.scalar_two_sided_bound"},
        {"file": "Main.lean", "name": "LCH01.scalar_two_sided_bound_textbook"}
      ],
      "representation": "习题 2.2。对象：ϕ : Operator X bot，U : Set X，j : I，L ∈ restrictedLipMatrices d ϕ U（𝓛(ϕ)|_U），K ∈ restrictedCoLipMatrices d ϕ U（𝓚(ϕ)|_U）。前提：∀ k ≠ j, entry L k j = 0（L_{k→j} = 0，定义上等于 RowSingleInput L j j）。正文的 U ⊆ dom(ϕ) 已包含在两个证书族的成员关系中；textbook 版本另外把它和规范空间公理作为显式前提列出。结论：∀ x ∈ U, ∀ y ∈ U, K_{j→j}·d_j(x,y) ≤ d_j(ϕx,ϕy) ∧ d_j(ϕx,ϕy) ≤ L_{j→j}·d_j(x,y)。证明：上界取 P19 中 i = j 的单行化简（lip_row_single_input_le）；下界用 P20 中的 coLip_single_term_le（单项 ≤ 和 ≤ 像距）。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19", "CH02-P20"]
    }
  ]
}
```