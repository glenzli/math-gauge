8 项义务都已形式化完成，没有 `sorry`、`admit` 或新增公理。

我在原工作区和一份只含冻结前置模块与我的文件的全新副本里，都用 `lake build formal_oet` 全量编译，再用 `lake env lean Main.lean` 编译 `Main.lean`，均零警告通过。逐一检查所列的 60 个声明，只依赖 `propext`、`Classical.choice`、`Quot.sound`。冻结模块未改动。

新增模块放在 `formal_oet/vol_01/ch_02_operator_bounds/` 下，这样现有 `lakefile.toml` 里的 `formal_oet.+` 会收录它们。注意，不带参数的 `lake build` 在这个工作区里不构建任何目标，需要 `lake build formal_oet`。

两点表示选择：

- **成员资格含前置条件：** `L ∈ lipFamilyOn d φ U` 已含 `U ⊆ dom φ`，`K ∈ coLipFamilyOn d φ U` 另含 `U.Nonempty`，这是正文对 𝓛(φ)|_U 与 𝓚(φ)|_U 的前置条件。
- **核心定理与 `*_textbook` 封装并存：** 核心定理不假设伪度量公理与 `I` 非空，因为证明不用它们。`textbook_forms.lean` 把这些语境假设按正文补回，用下划线命名，是核心定理的特例。

P21 的结论保持为 `GaugeZeroRelated`，没有加强为 `x = y`。我另外证明了两点：加上 `IsSeparating d` 才得到点相等；并给出一个非分离的具体实例，说明点相等的加强不成立。

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_02_operator_bounds

/-!
# 第 2 章 §2.1：输入/输出矩阵指标约定与矩阵乘法（CH02-D03）

扩展非负矩阵用 `Matrix I I ENNReal` 表示（条目取值于 `[0, +∞]`）。
按正文约定，书写矩阵时以**输出分量为行指标、输入分量为列指标**：
条目 `L_{i→j}`（输入 `i`，输出 `j`）位于第 `j` 行、第 `i` 列，即 `(L)_{ji} = L_{i→j}`。
`chanEntry L i j` 即 `L_{i→j}`。矩阵乘积用 Mathlib 的 `Matrix` 乘法，
其条目公式恰为正文的 `(M₂ · M₁)_{i→j} = ∑ₖ (M₂)_{k→j} (M₁)_{i→k}`。
-/

section ChannelMatrix

variable {I : Type}

/--
OET anchor: h-af85899693cc8750
**指标约定**：条目 `M_{i→j}`（输入分量 `i`、输出分量 `j`）。
矩阵以输出分量为行指标、输入分量为列指标，故 `M_{i→j}` 位于第 `j` 行、第 `i` 列，
即 `(M)_{ji} = M_{i→j}`。
-/
def chanEntry (M : Matrix I I ENNReal) (i j : I) : ENNReal := M j i

/-- `(M)_{ji} = M_{i→j}`：条目 `M_{i→j}` 位于第 `j` 行、第 `i` 列。 -/
theorem chanEntry_eq_apply (M : Matrix I I ENNReal) (i j : I) :
    chanEntry M i j = M j i := rfl

/-- 第 `j` 行汇集指向输出分量 `d_j` 的全部系数 `L_{i→j}`（`i ∈ I`）。 -/
theorem row_eq_coefficients_into_output (M : Matrix I I ENNReal) (j : I) :
    (fun i => M j i) = fun i => chanEntry M i j := rfl

/-- 第 `i` 列汇集从输入分量 `d_i` 出发的全部系数 `L_{i→j}`（`j ∈ I`）。 -/
theorem col_eq_coefficients_from_input (M : Matrix I I ENNReal) (i : I) :
    (fun j => M j i) = fun j => chanEntry M i j := rfl

/--
正文中 `I = {1,2,3}` 时的展示：第一行汇集指向输出 `d₁` 的系数，第一列汇集从输入 `d₁` 出发的系数，
例如 `L_{2→1}` 位于第一行、第二列。此处以 `Fin 3` 的 `0, 1, 2` 表示分量 `1, 2, 3`。
-/
theorem matrix_display_fin3 (L : Matrix (Fin 3) (Fin 3) ENNReal) :
    L = !![chanEntry L 0 0, chanEntry L 1 0, chanEntry L 2 0;
           chanEntry L 0 1, chanEntry L 1 1, chanEntry L 2 1;
           chanEntry L 0 2, chanEntry L 1 2, chanEntry L 2 2] := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

/--
OET anchor: h-af85899693cc8750（行列约定）；h-193cebcc1a7f9259（命题 2.2 证明中的乘法条目）
**矩阵乘积的条目公式**：`(M₂ · M₁)_{i→j} = ∑ₖ (M₂)_{k→j} · (M₁)_{i→k}`。
先作用的矩阵 `M₁` 写在右侧。
-/
theorem chanEntry_mul [Fintype I] (M₂ M₁ : Matrix I I ENNReal) (i j : I) :
    chanEntry (M₂ * M₁) i j = ∑ k : I, chanEntry M₂ k j * chanEntry M₁ i k := by
  simp only [chanEntry, Matrix.mul_apply]

/-- 单位矩阵的条目：`𝐈_{i→j} = 1`（`i = j`），否则为 `0`。 -/
theorem chanEntry_one [DecidableEq I] (i j : I) :
    chanEntry (1 : Matrix I I ENNReal) i j = if i = j then 1 else 0 := by
  simp only [chanEntry, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- 矩阵作用于输入分量量值向量 `v`：`∑ᵢ M_{i→j} · v_i` 是通常的矩阵-向量乘积的第 `j` 个分量。 -/
theorem sum_chanEntry_mul_eq_mulVec [Fintype I] (M : Matrix I I ENNReal) (v : I → ENNReal)
    (j : I) :
    ∑ i : I, chanEntry M i j * v i = (M.mulVec v) j := by
  simp [Matrix.mulVec, dotProduct, chanEntry]

/--
**乘积作用于向量**：`∑ᵢ (M₂ · M₁)_{i→j} v_i = ∑ₖ (M₂)_{k→j} · (∑ᵢ (M₁)_{i→k} v_i)`。
这是两步系数先后作用与矩阵乘积一致所需的代数恒等式（有限和交换次序）。
-/
theorem sum_chanEntry_mul [Fintype I] (M₂ M₁ : Matrix I I ENNReal) (v : I → ENNReal) (j : I) :
    ∑ i : I, chanEntry (M₂ * M₁) i j * v i
      = ∑ k : I, chanEntry M₂ k j * ∑ i : I, chanEntry M₁ i k * v i := by
  have h := congrFun (Matrix.mulVec_mulVec v M₂ M₁) j
  rw [sum_chanEntry_mul_eq_mulVec, ← h, Matrix.mulVec, dotProduct]
  simp [Matrix.mulVec, dotProduct, chanEntry]

/-- 条目取值于 `[0, +∞]`：Lip/co-Lip 矩阵是非负矩阵。 -/
theorem chanEntry_nonneg (M : Matrix I I ENNReal) (i j : I) : 0 ≤ chanEntry M i j :=
  zero_le _

end ChannelMatrix

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-!
# 第 2 章 §2.1：Lip 矩阵与 co-Lip 矩阵的谓词与证书族（CH02-D01、CH02-D02）

规范族记作 `d : I → X → X → ENNReal`（`d i x y = d_i(x,y)`），`I` 为有限指标集（`[Fintype I]`）。
算子 `φ : Operator X bot` 来自冻结前置模块。矩阵的行列约定见 `channel_matrix.lean`：
`chanEntry L i j = L_{i→j}`，右端和式 `∑ i, chanEntry L i j * d i x y` 中的 `ENNReal` 算术
即正文的 `ℝ̄₊` 算术（`0 · ∞ = 0`，`a · ∞ = ∞`（`a > 0`），`a + ∞ = ∞`）。

* `lipFamily d φ`     是全体合法 Lip 矩阵之集 `𝓛(φ)`；
* `lipFamilyOn d φ U` 是全体受限 Lip 矩阵之集 `𝓛(φ)|_U`（要求 `U ⊆ dom φ`）；
* `coLipFamilyOn d φ U` 是全体合法受限 co-Lip 矩阵之集 `𝓚(φ)|_U`（要求 `U ≠ ∅` 且 `U ⊆ dom φ`）。

它们都是矩阵的**集合**（证书族），不预设其中存在实现所有条目下（上）确界的指定矩阵。
定义中的前置条件（`U ⊆ dom φ`、`U ≠ ∅`）作为成员资格的合取支，因此 `L ∈ 𝓛(φ)|_U` 与
`K ∈ 𝓚(φ)|_U` 已蕴含这些条件。
-/

section Families

variable {X I : Type} {bot : X} [Fintype I]

/--
**Lip 距离放缩不等式**：对所有 `x, y ∈ U` 与所有 `j ∈ I`，
`d_j(φ(x), φ(y)) ≤ ∑_{i∈I} L_{i→j} · d_i(x, y)`。
-/
def LipIneq (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : Matrix I I ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, chanEntry L i j * d i x y

/--
OET anchor: h-af85899693cc8750
**合法 Lipschitz 矩阵（全域谓词）**：对所有 `x, y ∈ dom(φ)` 与所有 `j ∈ I`，
`d_j(φ(x), φ(y)) ≤ ∑_{i∈I} L_{i→j} · d_i(x, y)`。
-/
def IsLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot) (L : Matrix I I ENNReal) : Prop :=
  LipIneq d φ (dom φ) L

/--
OET anchor: h-af85899693cc8750
**受限 Lip 矩阵（谓词）**：对子集 `U ⊆ dom(φ)`，若在 `U` 上对任意 `x, y ∈ U`
均满足上述距离放缩不等式，则称 `L` 为 `φ` 在 `U` 上的一个受限 Lip 矩阵。
-/
def IsLipMatrixOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : Matrix I I ENNReal) : Prop :=
  U ⊆ dom φ ∧ LipIneq d φ U L

/-- OET anchor: h-af85899693cc8750
`φ` 的全体合法 Lip 矩阵之集 `𝓛(φ)`（证书族）。 -/
def lipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Matrix I I ENNReal) :=
  {L | IsLipMatrix d φ L}

/-- OET anchor: h-af85899693cc8750
`φ` 在 `U ⊆ dom(φ)` 上的全体受限 Lip 矩阵之集 `𝓛(φ)|_U`（证书族）。 -/
def lipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {L | IsLipMatrixOn d φ U L}

/--
**co-Lipschitz 距离放缩不等式**：对所有 `x, y ∈ U` 与所有 `j ∈ I`，
`d_j(φ(x), φ(y)) ≥ ∑_{i∈I} K_{i→j} · d_i(x, y)`。
-/
def CoLipIneq (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : Matrix I I ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, chanEntry K i j * d i x y ≤ d j (φ.func x) (φ.func y)

/--
OET anchor: h-af85899693cc8750
**合法受限 co-Lipschitz 矩阵（谓词）**：对给定的**非空**子集 `U ⊆ dom(φ)`，
`K` 在 `U` 上满足上述 co-Lip 不等式。非空性条件 `U ≠ ∅` 是定义的一部分。
-/
def IsCoLipMatrixOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : Matrix I I ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ CoLipIneq d φ U K

/-- OET anchor: h-af85899693cc8750
`φ` 在非空子集 `U ⊆ dom(φ)` 上的全体合法 co-Lip 矩阵之集 `𝓚(φ)|_U`（下界证书族）。 -/
def coLipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {K | IsCoLipMatrixOn d φ U K}

/-! ### 谓词与证书族的基本性质 -/

/-- 全域证书族就是 `U = dom(φ)` 的受限证书族：`𝓛(φ) = 𝓛(φ)|_{dom(φ)}`。 -/
theorem lipFamily_eq_lipFamilyOn_dom (d : I → X → X → ENNReal) (φ : Operator X bot) :
    lipFamily d φ = lipFamilyOn d φ (dom φ) := by
  ext L
  exact ⟨fun h => ⟨subset_rfl, h⟩, fun h => h.2⟩

/-- 逐点展开 `L ∈ 𝓛(φ)`。 -/
theorem mem_lipFamily_iff (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : Matrix I I ENNReal) :
    L ∈ lipFamily d φ ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
        d j (φ.func x) (φ.func y) ≤ ∑ i : I, chanEntry L i j * d i x y := Iff.rfl

/-- 逐点展开 `L ∈ 𝓛(φ)|_U`：`U ⊆ dom(φ)` 且 Lip 不等式在 `U` 上成立。 -/
theorem mem_lipFamilyOn_iff (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : Matrix I I ENNReal) :
    L ∈ lipFamilyOn d φ U ↔
      U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
        d j (φ.func x) (φ.func y) ≤ ∑ i : I, chanEntry L i j * d i x y := Iff.rfl

/-- 逐点展开 `K ∈ 𝓚(φ)|_U`：`U` 非空、`U ⊆ dom(φ)` 且 co-Lip 不等式在 `U` 上成立。 -/
theorem mem_coLipFamilyOn_iff (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : Matrix I I ENNReal) :
    K ∈ coLipFamilyOn d φ U ↔
      U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
        ∑ i : I, chanEntry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := Iff.rfl

/-- 受限 Lip 证书的定义域条件：`L ∈ 𝓛(φ)|_U` 蕴含 `U ⊆ dom(φ)`。 -/
theorem subset_dom_of_mem_lipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {L : Matrix I I ENNReal} (h : L ∈ lipFamilyOn d φ U) : U ⊆ dom φ := h.1

/-- 受限 co-Lip 证书的定义域条件：`K ∈ 𝓚(φ)|_U` 蕴含 `U ⊆ dom(φ)`。 -/
theorem subset_dom_of_mem_coLipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (h : K ∈ coLipFamilyOn d φ U) : U ⊆ dom φ := h.2.1

/-- **非空性条件**：`K ∈ 𝓚(φ)|_U` 蕴含 `U ≠ ∅`。 -/
theorem nonempty_of_mem_coLipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (h : K ∈ coLipFamilyOn d φ U) : U.Nonempty := h.1

/-- **非空性条件**（`U ≠ ∅` 形式）：`K ∈ 𝓚(φ)|_U` 蕴含 `U ≠ ∅`。 -/
theorem ne_empty_of_mem_coLipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (h : K ∈ coLipFamilyOn d φ U) : U ≠ ∅ :=
  h.1.ne_empty

/-- 空集上没有任何 co-Lip 证书：`𝓚(φ)|_∅ = ∅`（非空性条件被计入定义）。 -/
theorem coLipFamilyOn_empty (d : I → X → X → ENNReal) (φ : Operator X bot) :
    coLipFamilyOn d φ (∅ : Set X) = ∅ := by
  ext K
  exact ⟨fun h => (Set.not_nonempty_empty h.1).elim, fun h => h.elim⟩

/-- 空集上 Lip 不等式平凡成立，故 `𝓛(φ)|_∅` 是全体矩阵（与 co-Lip 情形对照）。 -/
theorem lipFamilyOn_empty (d : I → X → X → ENNReal) (φ : Operator X bot) :
    lipFamilyOn d φ (∅ : Set X) = Set.univ := by
  ext L
  exact ⟨fun _ => trivial,
    fun _ => ⟨Set.empty_subset _, fun x hx => (Set.notMem_empty x hx).elim⟩⟩

/-- co-Lip 证书的单项下界：对每个通道 `(i, j)`，
`K_{i→j} · d_i(x, y) ≤ ∑ₖ K_{k→j} · d_k(x, y) ≤ d_j(φ(x), φ(y))`（`x, y ∈ U`）。 -/
theorem single_term_le_of_mem_coLipFamilyOn {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (hK : K ∈ coLipFamilyOn d φ U) (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U, chanEntry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  intro x hx y hy
  exact le_trans
    (Finset.single_le_sum (f := fun k => chanEntry K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i))
    (hK.2.2 x hx y hy j)

/-! ### 广义 Lip 约定（条目可取 `+∞`；`0 · (+∞) = 0`） -/

/-- 若 `L_{i→j} = +∞` 且 `d_i(x, y) > 0`，则该项为 `+∞`，从而右端求和为 `+∞`。 -/
theorem sum_chanEntry_mul_dist_eq_top (d : I → X → X → ENNReal) {L : Matrix I I ENNReal}
    {i j : I} {x y : X} (hL : chanEntry L i j = ⊤) (hxy : 0 < d i x y) :
    ∑ k : I, chanEntry L k j * d k x y = ⊤ := by
  rw [ENNReal.sum_eq_top]
  exact ⟨i, Finset.mem_univ i, by rw [hL, ENNReal.top_mul hxy.ne']⟩

/-- 若 `L_{i→j} = +∞` 且 `d_i(x, y) > 0`，则 `j` 行的 Lip 不等式平凡成立。 -/
theorem lipIneq_trivial_of_top_entry (d : I → X → X → ENNReal) (φ : Operator X bot)
    {L : Matrix I I ENNReal} {i j : I} {x y : X} (hL : chanEntry L i j = ⊤)
    (hxy : 0 < d i x y) :
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, chanEntry L k j * d k x y := by
  rw [sum_chanEntry_mul_dist_eq_top d hL hxy]
  exact le_top

end Families

section ExtendedArithmetic

variable {X I : Type}

/-- 若 `L_{i→j} = +∞` 但 `d_i(x, y) = 0`，则该项对右端求和的贡献为零
（`+∞ · 0 = 0` 的约定）。 -/
theorem chanEntry_top_mul_dist_zero (d : I → X → X → ENNReal) {L : Matrix I I ENNReal}
    {i j : I} {x y : X} (hL : chanEntry L i j = ⊤) (hxy : d i x y = 0) :
    chanEntry L i j * d i x y = 0 := by
  rw [hL, hxy, mul_zero]

end ExtendedArithmetic

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-!
# 第 2 章 §2.2：分量通道、单输入通道（单行稀疏）与对角特例（CH02-D07、CH02-P19）

* `ComponentChannel I = I × I`：分量通道 `(i, j)`，从输入分量 `d_i` 到输出分量 `d_j`；
* `IsSingleInputChannel L (i, j)`：第 `j` 行除 `L_{i→j}` 外均为零（单输入通道 / 单行稀疏）；
* 对角矩阵用 Mathlib 的 `Matrix.IsDiag`；`isDiag_iff_forall_sameComponent_singleInput`
  说明它恰为"每个同分量通道 `(i, i)` 都是单输入通道"；
* `lip_single_input_reduction`、`lip_diagonal_reduction`（P19）给出受限 Lip 证书的行化简。
-/

section ChannelDefinitions

variable {X I : Type}

/--
OET anchor: h-7fa97eb6e24d5527
**分量通道**：对 `i, j ∈ I`，有序对 `(i, j)` 称为从输入分量 `d_i` 到输出分量 `d_j` 的分量通道。
-/
abbrev ComponentChannel (I : Type) : Type := I × I

/-- 通道 `c = (i, j)` 在矩阵 `M` 中的系数 `M_{i→j}`。 -/
def ComponentChannel.coeff (M : Matrix I I ENNReal) (c : ComponentChannel I) : ENNReal :=
  chanEntry M c.1 c.2

/-- **同分量通道** `(i, i)`。 -/
def ComponentChannel.IsSameComponent (c : ComponentChannel I) : Prop := c.1 = c.2

/--
OET anchor: h-7fa97eb6e24d5527
**单输入通道（单行稀疏）**：对通道 `(i, j)`，第 `j` 行除 `L_{i→j}` 外均为零，
即 `L_{k→j} = 0`（`∀ k ≠ i`）；此时输入分量 `d_i` 是输出分量 `d_j` 的唯一输入项。
-/
def IsSingleInputChannel (L : Matrix I I ENNReal) (c : ComponentChannel I) : Prop :=
  ∀ k : I, k ≠ c.1 → chanEntry L k c.2 = 0

/-- 通道 `(i, j)` 的系数 `L_{i→j}` 即 `chanEntry L i j`。 -/
theorem ComponentChannel.coeff_eq (M : Matrix I I ENNReal) (i j : I) :
    ComponentChannel.coeff M (i, j) = chanEntry M i j := rfl

/-- 系数为零的输入项不参与该输出分量的上界：`L_{i→j} = 0` 时 `L_{i→j} · d_i(x, y) = 0`。 -/
theorem term_eq_zero_of_coeff_zero (d : I → X → X → ENNReal) {L : Matrix I I ENNReal}
    {i j : I} (hij : chanEntry L i j = 0) (x y : X) : chanEntry L i j * d i x y = 0 := by
  rw [hij, zero_mul]

/-- 对角矩阵恰为"每个 `(i, i)` 都是单输入通道"：
`L` 对角 `⟺` 对每个 `i`，第 `i` 行除 `L_{i→i}` 外均为零。 -/
theorem isDiag_iff_forall_singleInput_self (L : Matrix I I ENNReal) :
    L.IsDiag ↔ ∀ i : I, IsSingleInputChannel L (i, i) := by
  constructor
  · intro hL i k hk
    exact hL (Ne.symm hk)
  · intro h a b hab
    exact h a b (Ne.symm hab)

/-- 对角矩阵恰为"每个同分量通道都是单输入通道"。 -/
theorem isDiag_iff_forall_sameComponent_singleInput (L : Matrix I I ENNReal) :
    L.IsDiag ↔ ∀ c : ComponentChannel I, c.IsSameComponent → IsSingleInputChannel L c := by
  rw [isDiag_iff_forall_singleInput_self]
  constructor
  · rintro h ⟨i, j⟩ (hc : i = j)
    subst hc
    exact h i
  · intro h i
    exact h (i, i) rfl

/-- 对角矩阵的非对角条目（跨分量通道的系数）为零。 -/
theorem chanEntry_eq_zero_of_isDiag {L : Matrix I I ENNReal} (hL : L.IsDiag) {i j : I}
    (hij : i ≠ j) : chanEntry L i j = 0 :=
  hL (Ne.symm hij)

/-- 系数为零的输入项不参与该输出分量的上界：`L_{i→j} = 0` 时，求和中去掉第 `i` 项不改变上界。 -/
theorem sum_erase_eq_sum_of_coeff_zero [Fintype I] [DecidableEq I] {L : Matrix I I ENNReal}
    {i j : I} (hij : chanEntry L i j = 0) (v : I → ENNReal) :
    ∑ k ∈ Finset.univ.erase i, chanEntry L k j * v k = ∑ k : I, chanEntry L k j * v k :=
  Finset.sum_erase _ (by rw [hij, zero_mul])

end ChannelDefinitions

section Reductions

variable {X I : Type} {bot : X} [Fintype I]

/-- 单输入通道 `(i, j)` 下，第 `j` 行的和式只剩一项：`∑ₖ L_{k→j} v_k = L_{i→j} v_i`。 -/
theorem sum_eq_single_input_term {L : Matrix I I ENNReal} {i j : I}
    (h : IsSingleInputChannel L (i, j)) (v : I → ENNReal) :
    ∑ k : I, chanEntry L k j * v k = chanEntry L i j * v i := by
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
  rw [h k hk, zero_mul]

/-! ### P19：单一输入项行化简；包含对角特例 -/

/-- 第 `j` 行为单输入通道 `(i, j)` 时，第 `j` 行的 Lip 条件**等价于**化简后的标量不等式。 -/
theorem lipIneq_row_iff_of_single_input {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {L : Matrix I I ENNReal} {i j : I} (hrow : IsSingleInputChannel L (i, j)) :
    (∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ ∑ k : I, chanEntry L k j * d k x y) ↔
      ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ chanEntry L i j * d i x y := by
  simp only [sum_eq_single_input_term hrow]

/--
OET anchor: h-7fa97eb6e24d5527
**单一输入项行化简**：设 `L ∈ 𝓛(φ)|_U`（其中含 `U ⊆ dom φ`）。若第 `j` 行除 `L_{i→j}` 外均为零，
则对任意 `x, y ∈ U`，Lip 不等式化为
`d_j(φ(x), φ(y)) ≤ ∑ₖ L_{k→j} d_k(x, y) = L_{i→j} d_i(x, y)`。
-/
theorem lip_single_input_reduction {d : I → X → X → ENNReal} {φ : Operator X bot} {U : Set X}
    {L : Matrix I I ENNReal} (hL : L ∈ lipFamilyOn d φ U) {i j : I}
    (hrow : IsSingleInputChannel L (i, j)) :
    ∀ x ∈ U, ∀ y ∈ U,
      ∑ k : I, chanEntry L k j * d k x y = chanEntry L i j * d i x y ∧
      d j (φ.func x) (φ.func y) ≤ chanEntry L i j * d i x y := by
  intro x hx y hy
  have hsum := sum_eq_single_input_term hrow (fun k => d k x y)
  exact ⟨hsum, hsum ▸ hL.2 x hx y hy j⟩

/--
OET anchor: h-7fa97eb6e24d5527
**对角特例**：设 `L ∈ 𝓛(φ)|_U` 为对角矩阵，则上述化简对每个同分量通道 `(i, i)` 均成立：
对任意 `i ∈ I` 与 `x, y ∈ U`，
`d_i(φ(x), φ(y)) ≤ ∑ₖ L_{k→i} d_k(x, y) = L_{i→i} d_i(x, y)`。
-/
theorem lip_diagonal_reduction {d : I → X → X → ENNReal} {φ : Operator X bot} {U : Set X}
    {L : Matrix I I ENNReal} (hL : L ∈ lipFamilyOn d φ U) (hdiag : L.IsDiag) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      ∑ k : I, chanEntry L k i * d k x y = chanEntry L i i * d i x y ∧
      d i (φ.func x) (φ.func y) ≤ chanEntry L i i * d i x y :=
  fun i => lip_single_input_reduction hL
    ((isDiag_iff_forall_singleInput_self L).1 hdiag i)

/-- 对角矩阵 `L` 是 `U` 上的受限 Lip 证书，当且仅当 `U ⊆ dom φ` 且每个同分量通道上
`d_i(φ(x), φ(y)) ≤ L_{i→i} d_i(x, y)`（`x, y ∈ U`）。 -/
theorem mem_lipFamilyOn_iff_of_isDiag {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {L : Matrix I I ENNReal} (hdiag : L.IsDiag) :
    L ∈ lipFamilyOn d φ U ↔
      U ⊆ dom φ ∧ ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
        d i (φ.func x) (φ.func y) ≤ chanEntry L i i * d i x y := by
  constructor
  · intro hL
    exact ⟨hL.1, fun i x hx y hy => (lip_diagonal_reduction hL hdiag i x hx y hy).2⟩
  · rintro ⟨hU, h⟩
    refine ⟨hU, fun x hx y hy j => ?_⟩
    rw [sum_eq_single_input_term ((isDiag_iff_forall_singleInput_self L).1 hdiag j)]
    exact h j x hx y hy

end Reductions

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean
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
```

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/scalar_two_sided_bound.lean
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
```

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/textbook_forms.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families
import formal_oet.vol_01.ch_02_operator_bounds.component_channels
import formal_oet.vol_01.ch_02_operator_bounds.colip_distinguishability
import formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-!
# 正文同形封装（P19、P20、P21、P25）

核心定理（见各模块）只用到 Lip/co-Lip 不等式的代数结构，因而不依赖伪度量公理与 `I` 的非空性。
本文件按正文语境逐一重述：有限非空指标集 `I`（`[Fintype I] [Nonempty I]`）上的一族扩展伪度量
`d_i`（`hd : ∀ i, ExtendedPseudoMetric X bot (d i)`），算子 `φ`，`U ⊆ dom(φ)`，
以及所给的 Lip/co-Lip 证书。这些语境假设（以下划线命名）在证明中不被使用，
因此各封装只是对应核心定理的特例。
-/

section TextbookForms

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-7fa97eb6e24d5527
**单一输入项行化简（正文同形）**：设 `φ ∈ 𝒳_op`，`U ⊆ dom(φ)`，`L ∈ 𝓛(φ)|_U`。
若第 `j` 行除 `L_{i→j}` 外均为零（`L_{k→j} = 0`，`∀ k ≠ i`），则对任意 `x, y ∈ U`，
`d_j(φ(x), φ(y)) ≤ ∑ₖ L_{k→j} d_k(x, y) = L_{i→j} d_i(x, y)`。
-/
theorem lip_single_input_reduction_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (L : Matrix I I ENNReal) (hL : L ∈ lipFamilyOn d φ U) (i j : I)
    (hrow : ∀ k : I, k ≠ i → chanEntry L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ ∑ k : I, chanEntry L k j * d k x y ∧
      ∑ k : I, chanEntry L k j * d k x y = chanEntry L i j * d i x y := by
  intro x hx y hy
  obtain ⟨hsum, _⟩ := lip_single_input_reduction hL (i := i) (j := j) hrow x hx y hy
  exact ⟨hL.2 x hx y hy j, hsum⟩

/--
OET anchor: h-7fa97eb6e24d5527
**对角特例（正文同形）**：设 `L ∈ 𝓛(φ)|_U` 为对角矩阵，则对每个同分量通道 `(i, i)`
与任意 `x, y ∈ U`，`d_i(φ(x), φ(y)) ≤ ∑ₖ L_{k→i} d_k(x, y) = L_{i→i} d_i(x, y)`。
-/
theorem lip_diagonal_reduction_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (L : Matrix I I ENNReal) (hL : L ∈ lipFamilyOn d φ U) (hdiag : L.IsDiag) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ ∑ k : I, chanEntry L k i * d k x y ∧
      ∑ k : I, chanEntry L k i * d k x y = chanEntry L i i * d i x y := by
  intro i x hx y hy
  obtain ⟨hsum, _⟩ := lip_diagonal_reduction hL hdiag i x hx y hy
  exact ⟨hL.2 x hx y hy i, hsum⟩

/--
OET anchor: h-f82672ec0dd48f28
**命题 2.8 (i)（正文同形）**：设 `K ∈ 𝓚(φ)|_U`。若 `K_{i→j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x, y) > 0 ⟹ d_j(φ(x), φ(y)) > 0`。
-/
theorem colip_pos_channel_preserves_pos_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (K : Matrix I I ENNReal) (hK : K ∈ coLipFamilyOn d φ U) (i j : I)
    (hKij : 0 < chanEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (φ.func x) (φ.func y) :=
  colip_pos_channel_preserves_pos hK hKij

/--
OET anchor: h-f82672ec0dd48f28
**命题 2.8 (ii)（正文同形）**：设 `K ∈ 𝓚(φ)|_U`。若 `K_{j→j} > 0` 对所有 `j ∈ I` 成立，
则 `φ` 反射族零距关系：对任意 `x, y ∈ U`，`φ(x) ∼_𝒢 φ(y) ⟹ x ∼_𝒢 y`。
不预设族分离性，结论不是点相等。
-/
theorem colip_diag_pos_reflects_zeroRelated_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ)
    (K : Matrix I I ENNReal) (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ j : I, 0 < chanEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y :=
  colip_diag_pos_reflects_zeroRelated hK hdiag

/--
OET anchor: h-6a98a58b5bc95360
**习题 2.2（正文同形）**：设 `φ ∈ 𝒳_op`，`U ⊆ dom(φ)`，`j ∈ I`，`L ∈ 𝓛(φ)|_U`，`K ∈ 𝓚(φ)|_U`。
若 `L_{k→j} = 0`（`∀ k ≠ j`），则对任意 `x, y ∈ U`，
`K_{j→j} · d_j(x, y) ≤ d_j(φ(x), φ(y)) ≤ L_{j→j} · d_j(x, y)`。
-/
theorem scalar_two_sided_bound_textbook [Nonempty I]
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (_hU : U ⊆ dom φ) (j : I)
    (L : Matrix I I ENNReal) (hL : L ∈ lipFamilyOn d φ U)
    (K : Matrix I I ENNReal) (hK : K ∈ coLipFamilyOn d φ U)
    (hdiag : ∀ k : I, k ≠ j → chanEntry L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      chanEntry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ chanEntry L j j * d j x y :=
  scalar_two_sided_bound hL hK hdiag

end TextbookForms

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=Main.lean
import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families
import formal_oet.vol_01.ch_02_operator_bounds.component_channels
import formal_oet.vol_01.ch_02_operator_bounds.colip_distinguishability
import formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound
import formal_oet.vol_01.ch_02_operator_bounds.textbook_forms

/-!
# LCH01：第 2 章（算子界）选段形式化

模块与义务对应：

* `channel_matrix`            ：CH02-D03（输入/输出矩阵指标约定与乘法）
* `lip_colip_families`        ：CH02-D01（Lip 谓词与证书族）、CH02-D02（含非空条件的 co-Lip 谓词与证书族）
* `component_channels`        ：CH02-D07（分量通道、单输入通道、对角特例）、CH02-P19（单一输入项行化简）
* `colip_distinguishability`  ：CH02-P20（正 co-Lip 通道保持正距离）、
                                 CH02-P21（全对角正 co-Lip 反射族零距；不加强为点相等）
* `scalar_two_sided_bound`    ：CH02-P25（习题 2.2：标量双侧界）
* `textbook_forms`            ：P19、P20、P21、P25 的正文同形封装（含有限非空指标集与伪度量语境）
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
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.LipIneq"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrix"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrixOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamily"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamily_eq_lipFamilyOn_dom"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_lipFamily_iff"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_lipFamilyOn_iff"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.subset_dom_of_mem_lipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamilyOn_empty"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.chanEntry_top_mul_dist_zero"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_chanEntry_mul_dist_eq_top"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipIneq_trivial_of_top_entry"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.chanEntry_nonneg"}
      ],
      "representation": "【对象】规范族 𝒢={d_i}_{i∈I} ↦ d : I → X → X → ENNReal（d i x y = d_i(x,y)）；ℝ̄₊ ↦ ENNReal（其加法/乘法即正文约定 a+∞=∞、0·∞=0、a·∞=∞(a>0)）；有限指标集 I ↦ [Fintype I]；算子 φ∈𝒳_op ↦ 冻结模块 Operator X bot；dom(φ) ↦ 冻结模块 dom φ；非负矩阵 L（L_{i→j}∈ℝ̄₊）↦ Matrix I I ENNReal，L_{i→j} ↦ chanEntry L i j（行列约定见 CH02-D03）。【谓词】LipIneq d φ U L := ∀x∈U ∀y∈U ∀j∈I, d j (φ x) (φ y) ≤ ∑ i, chanEntry L i j * d i x y；全域合法 Lip 矩阵 IsLipMatrix d φ L := LipIneq d φ (dom φ) L（x,y∈dom φ）；受限 Lip 矩阵 IsLipMatrixOn d φ U L := U ⊆ dom φ ∧ LipIneq d φ U L（正文仅对 U⊆dom(φ) 定义受限矩阵，该前置条件作为合取支）。【证书族】lipFamily d φ = {L | IsLipMatrix d φ L} ↦ 𝓛(φ)，lipFamilyOn d φ U = {L | IsLipMatrixOn d φ U L} ↦ 𝓛(φ)|_U；均为 Set (Matrix I I ENNReal)，未选取任何指定矩阵或逐项下确界，对应『作为证书族使用、不预设极值矩阵』。【辅助结论】lipFamily_eq_lipFamilyOn_dom：𝓛(φ)=𝓛(φ)|_{dom φ}；mem_lipFamily_iff / mem_lipFamilyOn_iff / subset_dom_of_mem_lipFamilyOn：逐点展开；lipFamilyOn_empty：空受限域上全体矩阵都是证书；广义 Lip 约定：chanEntry_top_mul_dist_zero（L_{i→j}=∞ 且 d_i(x,y)=0 时该项贡献 0）、sum_chanEntry_mul_dist_eq_top 与 lipIneq_trivial_of_top_entry（L_{i→j}=∞ 且 d_i(x,y)>0 时右端和为 ∞、不等式平凡成立）；chanEntry_nonneg：条目非负。【强度】均为定义及其基本等价式/约定引理，不依赖伪度量公理，也不要求 I 非空。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipIneq"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCoLipMatrixOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_coLipFamilyOn_iff"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.subset_dom_of_mem_coLipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.nonempty_of_mem_coLipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ne_empty_of_mem_coLipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipFamilyOn_empty"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/lip_colip_families.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.single_term_le_of_mem_coLipFamilyOn"}
      ],
      "representation": "【对象】同 CH02-D01；下界矩阵 K（K_{i→j}∈ℝ̄₊）↦ Matrix I I ENNReal，K_{i→j} ↦ chanEntry K i j。【谓词】CoLipIneq d φ U K := ∀x∈U ∀y∈U ∀j∈I, ∑ i, chanEntry K i j * d i x y ≤ d j (φ x) (φ y)（正文 d_j(φx,φy) ≥ ∑ K_{i→j} d_i(x,y)）；IsCoLipMatrixOn d φ U K := U.Nonempty ∧ U ⊆ dom φ ∧ CoLipIneq d φ U K。正文对『给定的非空子集 U⊆dom(φ)』定义合法受限 co-Lip 矩阵，并声明『凡出现 𝓚(φ)|_U，均包含非空性条件 U≠∅』，故非空性与 U⊆dom φ 作为成员资格的合取支。【证书族】coLipFamilyOn d φ U = {K | IsCoLipMatrixOn d φ U K} ↦ 𝓚(φ)|_U（全域情形取 U = dom φ），为 Set，不预设指定的上确界矩阵。【辅助结论】nonempty_of_mem_coLipFamilyOn / ne_empty_of_mem_coLipFamilyOn：K∈𝓚(φ)|_U ⇒ U≠∅；coLipFamilyOn_empty：𝓚(φ)|_∅=∅（与 lipFamilyOn_empty 对照）；mem_coLipFamilyOn_iff、subset_dom_of_mem_coLipFamilyOn：逐点展开；single_term_le_of_mem_coLipFamilyOn：K_{i→j}d_i(x,y) ≤ ∑_k K_{k→j}d_k(x,y) ≤ d_j(φx,φy)。【强度】定义与基本引理，不依赖伪度量公理。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.chanEntry"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.chanEntry_eq_apply"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.row_eq_coefficients_into_output"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.col_eq_coefficients_from_input"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matrix_display_fin3"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.chanEntry_mul"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.chanEntry_one"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_chanEntry_mul_eq_mulVec"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/channel_matrix.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_chanEntry_mul"}
      ],
      "representation": "【对象】扩展非负矩阵 ↦ Matrix I I ENNReal；条目 M_{i→j}（输入分量 i、输出分量 j）↦ chanEntry M i j := M j i。【约定】行指标为输出分量、列指标为输入分量，(M)_{ji}=M_{i→j}（chanEntry_eq_apply，rfl）；row_eq_coefficients_into_output：第 j 行汇集指向输出 d_j 的系数；col_eq_coefficients_from_input：第 i 列汇集从输入 d_i 出发的系数；matrix_display_fin3：I={1,2,3}（Fin 3 的 0,1,2）时矩阵恰按正文 3×3 展示排列（如 L_{2→1} 位于第一行第二列）。【乘法】取 Matrix 的通常乘积，chanEntry_mul：(M₂*M₁)_{i→j}=∑_k (M₂)_{k→j}(M₁)_{i→k}（后作用的矩阵在左）；chanEntry_one：单位矩阵条目；sum_chanEntry_mul_eq_mulVec：Lip/co-Lip 右端和式 ∑_i M_{i→j}v_i 就是 M 作用于输入距离向量 v 的第 j 分量；sum_chanEntry_mul：乘积矩阵的作用等于两步先后作用（有限和交换次序）。【强度】恒等式，无额外假设（仅需 Fintype I；单位矩阵另需 DecidableEq I）。",
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel.coeff"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel.IsSameComponent"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsSingleInputChannel"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel.coeff_eq"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.term_eq_zero_of_coeff_zero"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_erase_eq_sum_of_coeff_zero"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.isDiag_iff_forall_singleInput_self"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.isDiag_iff_forall_sameComponent_singleInput"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.chanEntry_eq_zero_of_isDiag"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_eq_single_input_term"}
      ],
      "representation": "【对象】分量通道 ↦ ComponentChannel I := I × I（有序对 (i,j)：从输入分量 d_i 到输出分量 d_j）；通道系数 ComponentChannel.coeff M (i,j) = chanEntry M i j（coeff_eq）；同分量通道 (i,i) ↦ ComponentChannel.IsSameComponent。【单输入通道/单行稀疏】IsSingleInputChannel L (i,j) := ∀k≠i, chanEntry L k j = 0，即第 j 行除 L_{i→j} 外均为零（L_{i→j} 本身不受限）。【对角特例】对角矩阵 ↦ Mathlib 的 Matrix.IsDiag；isDiag_iff_forall_singleInput_self 与 isDiag_iff_forall_sameComponent_singleInput：L 对角 ⟺ 每个同分量通道 (i,i) 都是单输入通道；chanEntry_eq_zero_of_isDiag：非对角（跨分量）系数为 0。【零系数项】term_eq_zero_of_coeff_zero：L_{i→j}=0 时该项为 0；sum_erase_eq_sum_of_coeff_zero：去掉该项不改变和（『相应项不参与该上界』）；sum_eq_single_input_term：单输入通道下 ∑_k L_{k→j}v_k = L_{i→j}v_i。【强度】定义与代数引理，不依赖伪度量公理。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_single_input_reduction"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_diagonal_reduction"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipIneq_row_iff_of_single_input"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/component_channels.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.mem_lipFamilyOn_iff_of_isDiag"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/textbook_forms.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_single_input_reduction_textbook"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/textbook_forms.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_diagonal_reduction_textbook"}
      ],
      "representation": "【前提】φ : Operator X bot；U : Set X；L ∈ lipFamilyOn d φ U（即 L∈𝓛(φ)|_U，成员资格已含 U⊆dom φ）；Fintype I。【单一输入项行化简】lip_single_input_reduction：若 IsSingleInputChannel L (i,j)（第 j 行除 L_{i→j} 外均为零），则 ∀x∈U ∀y∈U，∑_k chanEntry L k j * d k x y = chanEntry L i j * d i x y ∧ d j (φ x) (φ y) ≤ chanEntry L i j * d i x y，即 d_j(φx,φy) ≤ ∑_k L_{k→j}d_k(x,y) = L_{i→j}d_i(x,y)。【对角特例】lip_diagonal_reduction：L.IsDiag 时对每个 i∈I 及 x,y∈U，∑_k L_{k→i}d_k(x,y)=L_{i→i}d_i(x,y) 且 d_i(φx,φy) ≤ L_{i→i}d_i(x,y)，即对每个同分量通道 (i,i) 成立。【加强的等价形式】lipIneq_row_iff_of_single_input：单输入行的 Lip 条件 ⟺ 标量不等式；mem_lipFamilyOn_iff_of_isDiag：对角 L∈𝓛(φ)|_U ⟺ U⊆dom φ ∧ 各 (i,i) 标量不等式。【正文同形封装】*_textbook 补上正文语境 [Fintype I][Nonempty I]、hd : ∀i, ExtendedPseudoMetric X bot (d i)、U⊆dom φ，并把结论写成正文链式 d_j(φx,φy) ≤ ∑_k L_{k→j}d_k(x,y) = L_{i→j}d_i(x,y)（语境假设在证明中不使用，封装是核心定理的特例；核心定理对这些假设不作要求，故不弱于正文）。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_pos_channel_preserves_pos"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/textbook_forms.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_pos_channel_preserves_pos_textbook"}
      ],
      "representation": "【前提】K ∈ coLipFamilyOn d φ U（K∈𝓚(φ)|_U，含 U≠∅ 与 U⊆dom φ）；i j : I；0 < chanEntry K i j（K_{i→j}>0）。【结论】∀x∈U ∀y∈U，0 < d i x y → 0 < d j (φ x) (φ y)，即 d_i(x,y)>0 ⇒ d_j(φ(x),φ(y))>0。【证明思路】co-Lip 不等式给出 d_j(φx,φy) ≥ ∑_k K_{k→j}d_k(x,y) ≥ K_{i→j}d_i(x,y)（single_term_le_of_mem_coLipFamilyOn），ENNReal 中两个非零因子之积为正（含 ⊤）。【封装】colip_pos_channel_preserves_pos 不需要伪度量公理；_textbook 版补入正文语境 [Fintype I][Nonempty I]、hd、U⊆dom φ（不使用；i j 显式）。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_diag_pos_reflects_zeroRelated"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_diag_pos_eq_of_isSeparating"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.NonSeparatingExample.exDist_extendedPseudoMetric"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.NonSeparatingExample.exDist_nonSeparating"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.NonSeparatingExample.exK_mem_coLipFamilyOn"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/colip_distinguishability.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.NonSeparatingExample.colip_reflection_not_pointEquality"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/textbook_forms.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_diag_pos_reflects_zeroRelated_textbook"}
      ],
      "representation": "【前提】K ∈ coLipFamilyOn d φ U；hdiag : ∀j, 0 < chanEntry K j j（K_{j→j}>0 对所有 j∈I）。【结论】∀x∈U ∀y∈U，GaugeZeroRelated d (φ x) (φ y) → GaugeZeroRelated d x y；GaugeZeroRelated 是冻结模块中的族零距关系 ∼_𝒢（∀i, d i x y = 0），故结论是『φ 反射族零距关系』，未加强为点相等，也未假设族分离性。【证明】对每个 j 用 CH02-P20 的通道 (j,j)：若 d_j(x,y)>0 则 d_j(φx,φy)>0，与 φ(x)∼φ(y) 矛盾。【不加强为点相等】colip_diag_pos_eq_of_isSeparating：仅在额外假设 IsSeparating d 时才得到 x=y；NonSeparatingExample（X=Option Bool，⊥=none，I=Unit，exDist 满足全部扩展伪度量公理并且不分离，φ=恒等算子，K=单位矩阵，U={some true, some false}）中的 colip_reflection_not_pointEquality 证明在所有前提成立时『∀x,y∈U, φ(x)∼φ(y) → x=y』不成立。【封装】_textbook 版补入正文语境 [Fintype I][Nonempty I]、hd、U⊆dom φ（不使用）。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/scalar_two_sided_bound.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound"},
        {"file": "formal_oet/vol_01/ch_02_operator_bounds/textbook_forms.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound_textbook"}
      ],
      "representation": "【前提】φ : Operator X bot，U⊆dom φ，j : I，L ∈ lipFamilyOn d φ U（L∈𝓛(φ)|_U），K ∈ coLipFamilyOn d φ U（K∈𝓚(φ)|_U，含 U≠∅），hdiag : ∀k, k≠j → chanEntry L k j = 0（只保留对角输入项的 Lip 上界 L_{k→j}=0 (∀k≠j)，即 IsSingleInputChannel L (j,j)）。【结论】∀x∈U ∀y∈U，chanEntry K j j * d j x y ≤ d j (φ x) (φ y) ∧ d j (φ x) (φ y) ≤ chanEntry L j j * d j x y，即 K_{j→j}·d_j(x,y) ≤ d_j(φ(x),φ(y)) ≤ L_{j→j}·d_j(x,y)。【证明】上界取自 CH02-P19 的单一输入项行化简（i=j）；下界取自 co-Lip 不等式的单项估计 single_term_le_of_mem_coLipFamilyOn（CH02-D02）。【封装】核心定理中的 U⊆dom φ 由成员资格给出；scalar_two_sided_bound_textbook 把 U⊆dom φ、[Fintype I][Nonempty I]、hd 作为正文语境显式列出（不使用）。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```