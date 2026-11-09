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
