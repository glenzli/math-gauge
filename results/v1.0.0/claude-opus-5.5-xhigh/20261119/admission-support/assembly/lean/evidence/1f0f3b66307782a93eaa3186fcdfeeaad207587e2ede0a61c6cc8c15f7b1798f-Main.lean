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
