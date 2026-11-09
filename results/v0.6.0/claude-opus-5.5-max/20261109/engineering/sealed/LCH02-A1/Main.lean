import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# LCH02 · 第 2 章 算子界：矩阵界与有限复合（选段形式化）

来源：Zhe Li (Glen Li / glenzli), *The Operator Evolution Theory*, Vol. I, 第 2 章 §2.1
（CC BY 4.0）。本文件只形式化 `obligations.json` 列出的 20 项义务。

表示约定：
* 规范结构 `{d_i}_{i ∈ I}` 表示为 `d : I → X → X → ENNReal`，`I` 为 `Fintype`。
  所列结论均不使用扩展伪度量公理与 `I` 的非空性，因此陈述对任意分量族成立，
  特别地对每个扩展规范空间 `(X, {d_i}, ⊥)` 成立。
* 矩阵为 `Matrix I I ENNReal`，以输出分量为行、输入分量为列：
  `L_{i→j} = arrowEntry L i j = L j i`。
* 第 `m` 步（`m = 1, …, k`）的对象以 `Fin k` 的元素 `⟨m - 1, _⟩` 编号。
-/

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

/-! ## 矩阵指标约定与乘法（CH02-D03） -/

section MatrixConvention

variable {I : Type}

/--
OET anchor: h-af85899693cc8750
**约定（矩阵行列）**：`L_{i→j}` 是输入分量 `d_i` 在输出分量 `d_j` 上界中的系数。
矩阵以输出分量为行指标、输入分量为列指标，故 `L_{i→j}` 位于第 `j` 行、第 `i` 列：
`(L)_{ji} = L_{i→j}`。
-/
def arrowEntry (L : Matrix I I ENNReal) (i j : I) : ENNReal := L j i

theorem arrowEntry_apply (L : Matrix I I ENNReal) (i j : I) :
    arrowEntry L i j = L j i := rfl

/-- `I = {1,2,3}`（以 `Fin 3` 的 `0,1,2` 编号）时的行列排布：第一行汇集指向输出分量 `d_1`
的系数，第一列汇集从输入分量 `d_1` 出发的系数；`L_{2→1}` 位于第一行第二列。 -/
theorem matrix_layout_fin_three (L : Matrix (Fin 3) (Fin 3) ENNReal) :
    L = !![arrowEntry L 0 0, arrowEntry L 1 0, arrowEntry L 2 0;
           arrowEntry L 0 1, arrowEntry L 1 1, arrowEntry L 2 1;
           arrowEntry L 0 2, arrowEntry L 1 2, arrowEntry L 2 2] :=
  Matrix.eta_fin_three L

variable [Fintype I]

/-- 矩阵乘法在箭头记号下的条目：`(L₂ · L₁)_{i→j} = ∑_k L₂_{k→j} · L₁_{i→k}`。 -/
theorem arrowEntry_mul (L₂ L₁ : Matrix I I ENNReal) (i j : I) :
    arrowEntry (L₂ * L₁) i j = ∑ k, arrowEntry L₂ k j * arrowEntry L₁ i k := by
  simp [arrowEntry, Matrix.mul_apply]

/-- Lip/co-Lip 不等式右端 `∑_i L_{i→j} v_i` 是矩阵作用于输入向量后的第 `j` 个输出分量。 -/
theorem sum_arrowEntry_mul_eq_mulVec (L : Matrix I I ENNReal) (v : I → ENNReal) (j : I) :
    ∑ i, arrowEntry L i j * v i = L.mulVec v j := by
  simp [arrowEntry, Matrix.mulVec, dotProduct]

/-- 交换有限和次序：`∑_k L₂_{k→j} (∑_i L₁_{i→k} v_i) = ∑_i (L₂ · L₁)_{i→j} v_i`。 -/
theorem sum_arrowEntry_mul_sum (L₂ L₁ : Matrix I I ENNReal) (v : I → ENNReal) (j : I) :
    ∑ k, arrowEntry L₂ k j * ∑ i, arrowEntry L₁ i k * v i =
      ∑ i, arrowEntry (L₂ * L₁) i j * v i := by
  simp only [arrowEntry_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end MatrixConvention

/-! ## 单位矩阵、空乘积与有序乘积（CH02-D04） -/

section OrderedProduct

/--
OET anchor: h-11006ddd8c43bfec
**有序有限乘积** `a_n ⋯ a_1`：`a ⟨m - 1, _⟩` 是第 `m` 个因子，后出现的因子乘在左侧；
`n = 0` 时为空乘积 `1`。对矩阵即 `M^{(n)} ⋯ M^{(1)}`；对算子幺半群即 `ϕ_n ∘ ⋯ ∘ ϕ_1`。
-/
def orderedProd {α : Type*} [Monoid α] : (n : ℕ) → (Fin n → α) → α
  | 0, _ => 1
  | n + 1, a => orderedProd n (fun m => a m.succ) * a 0

variable {α : Type*} [Monoid α]

/-- 空乘积为单位元。 -/
@[simp] theorem orderedProd_zero (a : Fin 0 → α) : orderedProd 0 a = 1 := rfl

/-- 剥离第一个因子：`a_{n+1} ⋯ a_1 = (a_{n+1} ⋯ a_2) · a_1`。 -/
theorem orderedProd_succ (n : ℕ) (a : Fin (n + 1) → α) :
    orderedProd (n + 1) a = orderedProd n (fun m => a m.succ) * a 0 := rfl

/-- 有序乘积等于逆序列表 `[a_n, …, a_1]` 的乘积。 -/
theorem orderedProd_eq_prod_reverse_ofFn :
    ∀ (n : ℕ) (a : Fin n → α), orderedProd n a = (List.ofFn a).reverse.prod
  | 0, _ => rfl
  | n + 1, a => by
      rw [orderedProd_succ, orderedProd_eq_prod_reverse_ofFn n, List.ofFn_succ,
        List.reverse_cons, List.prod_append, List.prod_singleton]

/-- 剥离最后一个因子：`a_{n+1} ⋯ a_1 = a_{n+1} · (a_n ⋯ a_1)`。 -/
theorem orderedProd_succ' (n : ℕ) (a : Fin (n + 1) → α) :
    orderedProd (n + 1) a = a (Fin.last n) * orderedProd n (fun m => a m.castSucc) := by
  rw [orderedProd_eq_prod_reverse_ofFn, orderedProd_eq_prod_reverse_ofFn, List.ofFn_succ',
    List.concat_eq_append, List.reverse_concat, List.prod_cons]

/-- 单因子有序乘积就是该因子。 -/
@[simp] theorem orderedProd_one (a : Fin 1 → α) : orderedProd 1 a = a 0 := by
  simp [orderedProd]

/-- 两因子有序乘积：`a_2 · a_1`。 -/
theorem orderedProd_two (a : Fin 2 → α) : orderedProd 2 a = a 1 * a 0 := by
  simp [orderedProd]

/-- 单位矩阵在箭头记号下的条目：`𝐈_{i→j} = 1`（`i = j`），否则为 `0`。 -/
theorem arrowEntry_one {I : Type} [DecidableEq I] (i j : I) :
    arrowEntry (1 : Matrix I I ENNReal) i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [arrowEntry]
  · simp [arrowEntry, h, Ne.symm h]

/-- 单位矩阵满足 `∑_i 𝐈_{i→j} v_i = v_j`。 -/
theorem sum_arrowEntry_one_mul {I : Type} [Fintype I] [DecidableEq I] (v : I → ENNReal) (j : I) :
    ∑ i, arrowEntry (1 : Matrix I I ENNReal) i j * v i = v j := by
  simp [arrowEntry, Matrix.one_apply]

end OrderedProduct

/-! ## Lip 矩阵谓词与证书族（CH02-D01）、co-Lip 矩阵谓词与证书族（CH02-D02） -/

section Certificates

variable {X : Type} {bot : X} {I : Type} [Fintype I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-af85899693cc8750
**定义（Lipschitz 矩阵）**：`L` 是 `ϕ` 的合法 Lip 矩阵，当且仅当对所有 `x, y ∈ dom(ϕ)`
与所有输出分量 `j ∈ I`，`d_j(ϕ(x), ϕ(y)) ≤ ∑_i L_{i→j} · d_i(x, y)`。
条目取值于 `ENNReal`（允许 `+∞`，并按 `+∞ · 0 = 0` 计算）。
-/
def IsLipMatrix (ϕ : Operator X bot) (L : Matrix I I ENNReal) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y

/-- 全体合法 Lip 矩阵之集（证书族）`𝓛(ϕ)`。 -/
def lipSet (ϕ : Operator X bot) : Set (Matrix I I ENNReal) :=
  {L | IsLipMatrix d ϕ L}

/--
OET anchor: h-af85899693cc8750
**定义（子集受限 Lip 矩阵）**：对子集 `U ⊆ dom(ϕ)`，`L` 在 `U` 上满足 Lip 不等式。
定义所要求的 `U ⊆ dom(ϕ)` 作为谓词的第一个分量保留。
-/
structure IsRestrictedLipMatrix (ϕ : Operator X bot) (U : Set X) (L : Matrix I I ENNReal) :
    Prop where
  subset_dom : U ⊆ dom ϕ
  bound : ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y

/-- 受限合法 Lip 矩阵之集（证书族）`𝓛(ϕ)|_U`。 -/
def restrictedLipSet (ϕ : Operator X bot) (U : Set X) : Set (Matrix I I ENNReal) :=
  {L | IsRestrictedLipMatrix d ϕ U L}

/--
OET anchor: h-af85899693cc8750
**定义（子集受限 co-Lipschitz 矩阵）**：对非空子集 `U ⊆ dom(ϕ)`，`K` 是 `ϕ` 在 `U` 上的
合法受限 co-Lip 矩阵，当且仅当对所有 `x, y ∈ U` 与 `j ∈ I`，
`d_j(ϕ(x), ϕ(y)) ≥ ∑_i K_{i→j} · d_i(x, y)`。
非空性条件 `U ≠ ∅` 与 `U ⊆ dom(ϕ)` 都是谓词的组成部分。
-/
structure IsRestrictedCoLipMatrix (ϕ : Operator X bot) (U : Set X) (K : Matrix I I ENNReal) :
    Prop where
  nonempty : U.Nonempty
  subset_dom : U ⊆ dom ϕ
  bound : ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i, arrowEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- 受限合法 co-Lip 矩阵之集（下界证书族）`𝒦(ϕ)|_U`，含非空性条件。 -/
def restrictedCoLipSet (ϕ : Operator X bot) (U : Set X) : Set (Matrix I I ENNReal) :=
  {K | IsRestrictedCoLipMatrix d ϕ U K}

variable {d}

theorem mem_lipSet_iff {ϕ : Operator X bot} {L : Matrix I I ENNReal} :
    L ∈ lipSet d ϕ ↔ ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y := Iff.rfl

/-- 向量形式：以输出分量为行时，Lip 条件即逐分量的距离向量不等式
`(d_j(ϕ(x), ϕ(y)))_j ≤ L *ᵥ (d_i(x, y))_i`。 -/
theorem mem_lipSet_iff_mulVec {ϕ : Operator X bot} {L : Matrix I I ENNReal} :
    L ∈ lipSet d ϕ ↔ ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
      (fun j => d j (ϕ.func x) (ϕ.func y)) ≤ L.mulVec (fun i => d i x y) := by
  simp only [mem_lipSet_iff, Pi.le_def, sum_arrowEntry_mul_eq_mulVec]

theorem mem_restrictedLipSet_iff {ϕ : Operator X bot} {U : Set X} {L : Matrix I I ENNReal} :
    L ∈ restrictedLipSet d ϕ U ↔ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y :=
  ⟨fun h => ⟨h.subset_dom, h.bound⟩, fun h => ⟨h.1, h.2⟩⟩

theorem mem_restrictedCoLipSet_iff {ϕ : Operator X bot} {U : Set X} {K : Matrix I I ENNReal} :
    K ∈ restrictedCoLipSet d ϕ U ↔ U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i, arrowEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) :=
  ⟨fun h => ⟨h.nonempty, h.subset_dom, h.bound⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- 全域 Lip 证书族就是在 `dom(ϕ)` 上的受限证书族：`𝓛(ϕ) = 𝓛(ϕ)|_{dom(ϕ)}`。 -/
theorem lipSet_eq_restrictedLipSet_dom (ϕ : Operator X bot) :
    lipSet d ϕ = restrictedLipSet d ϕ (dom ϕ) := by
  ext L
  exact ⟨fun h => ⟨subset_rfl, h⟩, fun h => h.bound⟩

/-- 非空性条件是 `𝒦(ϕ)|_U` 的一部分：空集上不存在合法受限 co-Lip 矩阵。 -/
theorem restrictedCoLipSet_empty (ϕ : Operator X bot) :
    restrictedCoLipSet d ϕ (∅ : Set X) = ∅ := by
  ext K
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  exact Set.not_nonempty_empty h.nonempty

end Certificates

/-! ## 单分量情形（CH02-P01） -/

section SingleComponent

variable {X : Type} {bot : X} {I : Type} [Fintype I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界）**：当 `I = {i}`（从而 `|I| = 1`）时，Lip 矩阵条件退化为
单个标量不等式 `d_i(ϕ(x), ϕ(y)) ≤ L_{i→i} · d_i(x, y)`（`x, y ∈ dom(ϕ)`）。
-/
theorem mem_lipSet_iff_scalar (i : I) (hI : ∀ j : I, j = i) (ϕ : Operator X bot)
    (L : Matrix I I ENNReal) :
    L ∈ lipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ arrowEntry L i i * d i x y := by
  have huniv : (Finset.univ : Finset I) = {i} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ i, fun j _ => hI j⟩
  have hsum : ∀ (j : I) (x y : X),
      ∑ k, arrowEntry L k j * d k x y = arrowEntry L i j * d i x y := by
    intro j x y
    rw [huniv, Finset.sum_singleton]
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    rwa [hsum] at h
  · intro h x hx y hy j
    rw [hI j, hsum]
    exact h x hx y hy

/-- `|I| = 1` 的基数形式：存在唯一分量 `i`，使 Lip 矩阵条件等价于标量不等式。 -/
theorem exists_mem_lipSet_iff_scalar_of_card_eq_one (hI : Fintype.card I = 1) :
    ∃ i : I, ∀ (ϕ : Operator X bot) (L : Matrix I I ENNReal),
      L ∈ lipSet d ϕ ↔
        ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ arrowEntry L i i * d i x y := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hI
  exact ⟨i, fun ϕ L => mem_lipSet_iff_scalar d i hi ϕ L⟩

end SingleComponent

/-! ## 证书族的单调性（CH02-P02, P03, P05, P06）与 co-Lip 零条目判据（CH02-P07） -/

section Monotonicity

variable {X : Type} {bot : X} {I : Type} [Fintype I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-4ff5c58d71e1651f
**引理 2.1（受限 Lip 矩阵族的单调性）**：若 `U ⊆ V ⊆ dom(ϕ)`，则 `𝓛(ϕ)|_V ⊆ 𝓛(ϕ)|_U`。
-/
theorem restrictedLipSet_anti {ϕ : Operator X bot} {U V : Set X} (hUV : U ⊆ V)
    (hV : V ⊆ dom ϕ) :
    restrictedLipSet d ϕ V ⊆ restrictedLipSet d ϕ U :=
  fun _ hL => ⟨hUV.trans hV, fun x hx y hy j => hL.bound x (hUV hx) y (hUV hy) j⟩

/--
OET anchor: h-4ff5c58d71e1651f
**引理 2.1（全域证书可限制）**：对任意 `U ⊆ dom(ϕ)`，`𝓛(ϕ) ⊆ 𝓛(ϕ)|_U`。
-/
theorem lipSet_subset_restrictedLipSet {ϕ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ) :
    lipSet d ϕ ⊆ restrictedLipSet d ϕ U := by
  rw [lipSet_eq_restrictedLipSet_dom]
  exact restrictedLipSet_anti d hU subset_rfl

/--
OET anchor: h-893b1d33535f7245
**引理 2.3（受限 co-Lip 矩阵族的单调性）**：若 `∅ ≠ U ⊆ V ⊆ dom(ϕ)`，
则 `𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U`。
-/
theorem restrictedCoLipSet_anti {ϕ : Operator X bot} {U V : Set X} (hU : U.Nonempty)
    (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    restrictedCoLipSet d ϕ V ⊆ restrictedCoLipSet d ϕ U :=
  fun _ hK => ⟨hU, hUV.trans hV, fun x hx y hy j => hK.bound x (hUV hx) y (hUV hy) j⟩

/--
OET anchor: h-893b1d33535f7245
**引理 2.3（全域 co-Lip 证书可限制）**：对任意非空 `U ⊆ dom(ϕ)`，
`𝒦(ϕ)|_{dom(ϕ)} ⊆ 𝒦(ϕ)|_U`。
-/
theorem restrictedCoLipSet_dom_subset {ϕ : Operator X bot} {U : Set X} (hU : U.Nonempty)
    (hUdom : U ⊆ dom ϕ) :
    restrictedCoLipSet d ϕ (dom ϕ) ⊆ restrictedCoLipSet d ϕ U :=
  restrictedCoLipSet_anti d hU hUdom subset_rfl

/-- 受限形式：若 `x, y ∈ U`、`d_j(ϕ(x), ϕ(y)) = 0` 且 `d_i(x, y) > 0`，
则任一 `K ∈ 𝒦(ϕ)|_U` 满足 `K_{i→j} = 0`。 -/
theorem arrowEntry_eq_zero_of_mem_restrictedCoLipSet {ϕ : Operator X bot} {U : Set X}
    {K : Matrix I I ENNReal} (hK : K ∈ restrictedCoLipSet d ϕ U) {i j : I} {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (hout : d j (ϕ.func x) (ϕ.func y) = 0) (hin : 0 < d i x y) :
    arrowEntry K i j = 0 := by
  have h1 : arrowEntry K i j * d i x y ≤ ∑ k, arrowEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k => arrowEntry K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h2 := hK.bound x hx y hy j
  rw [hout] at h2
  have h3 : arrowEntry K i j * d i x y = 0 := le_antisymm (h1.trans h2) (zero_le _)
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd h hin.ne'

/--
OET anchor: h-88784dcbfff0ea66
**注（co-Lip 条目为零的充分条件）**：若存在 `x, y ∈ dom(ϕ)` 使 `d_j(ϕ(x), ϕ(y)) = 0` 且
`d_i(x, y) > 0`，则任一全域 co-Lip 矩阵 `K ∈ 𝒦(ϕ)|_{dom(ϕ)}` 满足 `K_{i→j} = 0`。
-/
theorem arrowEntry_eq_zero_of_coLip_dom {ϕ : Operator X bot} {i j : I}
    (h : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y) :
    ∀ K ∈ restrictedCoLipSet d ϕ (dom ϕ), arrowEntry K i j = 0 := by
  intro K hK
  obtain ⟨x, hx, y, hy, hout, hin⟩ := h
  exact arrowEntry_eq_zero_of_mem_restrictedCoLipSet d hK hx hy hout hin

end Monotonicity

/-! ## 两步复合（CH02-P04, CH02-P08） -/

section TwoStep

variable {X : Type} {bot : X} {I : Type} [Fintype I]
variable (d : I → X → X → ENNReal)

/-- 复合定义域落在内层算子定义域中：`dom(ϕ₂ ∘ ϕ₁) ⊆ dom(ϕ₁)`。 -/
theorem dom_mul_subset_dom_right (ϕ₂ ϕ₁ : Operator X bot) : dom (ϕ₂ * ϕ₁) ⊆ dom ϕ₁ := by
  intro x hx h
  apply hx
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [h, ϕ₂.preserves_bot]

/-- 由复合定义直接保证 `U₂ = ϕ₁(U₁) ⊆ dom(ϕ₂)`。 -/
theorem operator_image_subset_dom_of_subset_dom_mul {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) : operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU₁ hx

/-- 中间像域非空当且仅当起始域非空：`ϕ₁(U₁) ≠ ∅ ↔ U₁ ≠ ∅`。 -/
theorem operator_image_nonempty_iff (ϕ₁ : Operator X bot) (U₁ : Set X) :
    (operator_image ϕ₁ U₁).Nonempty ↔ U₁.Nonempty :=
  Set.image_nonempty

/--
OET anchor: h-193cebcc1a7f9259
**命题 2.2（Lip 矩阵复合律）**：取 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，中间域精确取为像集
`U₂ = ϕ₁(U₁)`。若 `L⁽¹⁾ ∈ 𝓛(ϕ₁)|_{U₁}` 且 `L⁽²⁾ ∈ 𝓛(ϕ₂)|_{U₂}`，
则 `L⁽²⁾ · L⁽¹⁾ ∈ 𝓛(ϕ₂ ∘ ϕ₁)|_{U₁}`。算子乘法 `ϕ₂ * ϕ₁` 即 `ϕ₂ ∘ ϕ₁`。
-/
theorem mul_mem_restrictedLipSet_mul {ϕ₁ ϕ₂ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) {L₁ L₂ : Matrix I I ENNReal}
    (h₁ : L₁ ∈ restrictedLipSet d ϕ₁ U₁)
    (h₂ : L₂ ∈ restrictedLipSet d ϕ₂ (operator_image ϕ₁ U₁)) :
    L₂ * L₁ ∈ restrictedLipSet d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hx' : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
      = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k, arrowEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := h₂.bound _ hx' _ hy' j
    _ ≤ ∑ k, arrowEntry L₂ k j * ∑ i, arrowEntry L₁ i k * d i x y := by
        gcongr with k
        exact h₁.bound x hx y hy k
    _ = ∑ i, arrowEntry (L₂ * L₁) i j * d i x y := sum_arrowEntry_mul_sum L₂ L₁ _ j

/--
OET anchor: h-0f256e6f1d38a612
**命题 2.4（co-Lip 矩阵复合律）**：取 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，中间域精确取为像集
`U₂ = ϕ₁(U₁)`。若 `K⁽¹⁾ ∈ 𝒦(ϕ₁)|_{U₁}` 且 `K⁽²⁾ ∈ 𝒦(ϕ₂)|_{U₂}`（两者均含非空性），
则 `K⁽²⁾ · K⁽¹⁾ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}`。
-/
theorem mul_mem_restrictedCoLipSet_mul {ϕ₁ ϕ₂ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) {K₁ K₂ : Matrix I I ENNReal}
    (h₁ : K₁ ∈ restrictedCoLipSet d ϕ₁ U₁)
    (h₂ : K₂ ∈ restrictedCoLipSet d ϕ₂ (operator_image ϕ₁ U₁)) :
    K₂ * K₁ ∈ restrictedCoLipSet d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨h₁.nonempty, hU₁, fun x hx y hy j => ?_⟩
  have hx' : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc ∑ i, arrowEntry (K₂ * K₁) i j * d i x y
      = ∑ k, arrowEntry K₂ k j * ∑ i, arrowEntry K₁ i k * d i x y :=
        (sum_arrowEntry_mul_sum K₂ K₁ _ j).symm
    _ ≤ ∑ k, arrowEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
        gcongr with k
        exact h₁.bound x hx y hy k
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := h₂.bound _ hx' _ hy' j
    _ = d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) := rfl

end TwoStep

/-! ## 有限复合与实际中间像域（CH02-D05） -/

section Chain

variable {X : Type} {bot : X}

/--
OET anchor: h-c80171fa685dc795
**有限复合** `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`：`ϕ ⟨m - 1, _⟩` 为第 `m` 步算子，`c_0 = id_X`。
它只使用算子幺半群结构（算子乘法即函数复合）。
-/
abbrev chainComp (k : ℕ) (ϕ : Fin k → Operator X bot) : Operator X bot :=
  orderedProd k ϕ

/-- `c_0 = id_X`（即冻结模块中的 `operator_identity`）。 -/
theorem chainComp_zero (ϕ : Fin 0 → Operator X bot) :
    chainComp 0 ϕ = operator_identity := rfl

/-- `c_{k+1} = (ϕ_{k+1} ∘ ⋯ ∘ ϕ_2) ∘ ϕ_1`。 -/
theorem chainComp_succ (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) :
    chainComp (k + 1) ϕ = chainComp k (fun m => ϕ m.succ) * ϕ 0 := rfl

/-- `c_{k+1} = ϕ_{k+1} ∘ c_k`。 -/
theorem chainComp_succ' (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) :
    chainComp (k + 1) ϕ = ϕ (Fin.last k) * chainComp k (fun m => ϕ m.castSucc) :=
  orderedProd_succ' k ϕ

/-- 逐点形式：`c_{k+1}(x) = ϕ_{k+1}(c_k(x))`。 -/
theorem chainComp_succ_func (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) (x : X) :
    (chainComp (k + 1) ϕ).func x =
      (ϕ (Fin.last k)).func ((chainComp k (fun m => ϕ m.castSucc)).func x) := by
  rw [chainComp_succ']
  rfl

/-- 与冻结模块链表示的对应：`c_k = OperatorChain [ϕ_k, …, ϕ_1]`（表头最后作用）。 -/
theorem chainComp_eq_operatorChain (k : ℕ) (ϕ : Fin k → Operator X bot) :
    chainComp k ϕ = OperatorChain (List.ofFn ϕ).reverse := by
  rw [operator_chain_eq_prod]
  exact orderedProd_eq_prod_reverse_ofFn k ϕ

/--
OET anchor: h-c80171fa685dc795
**实际中间像域** `U_1, …, U_{k+1}`（索引 `0, …, k`）：起始域 `U_1` 位于索引 `0`，
并按 `U_{m+1} = ϕ_m(U_m)` 递推（见 `imageDomains_succ`）。
-/
def imageDomains : (k : ℕ) → (Fin k → Operator X bot) → Set X → Fin (k + 1) → Set X
  | 0, _, U => fun _ => U
  | k + 1, ϕ, U => Fin.cons U (imageDomains k (fun m => ϕ m.succ) (operator_image (ϕ 0) U))

/-- 索引 `0` 处为起始域 `U_1`。 -/
@[simp] theorem imageDomains_zero (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X) :
    imageDomains k ϕ U 0 = U := by
  cases k <;> simp [imageDomains]

/-- 去掉第一步后的链在 `U_2 = ϕ_1(U_1)` 上的中间像域即原链的 `U_2, …, U_{k+2}`。 -/
theorem imageDomains_cons_succ (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) (U : Set X)
    (m : Fin (k + 1)) :
    imageDomains (k + 1) ϕ U m.succ =
      imageDomains k (fun t => ϕ t.succ) (operator_image (ϕ 0) U) m := by
  simp [imageDomains]

/-- 递推式 `U_{m+1} = ϕ_m(U_m)`（`m = 1, …, k`）。 -/
theorem imageDomains_succ :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X) (m : Fin k),
      imageDomains k ϕ U m.succ = operator_image (ϕ m) (imageDomains k ϕ U m.castSucc)
  | 0, _, _, m => m.elim0
  | k + 1, ϕ, U, m => by
      cases m using Fin.cases with
      | zero =>
          rw [imageDomains_cons_succ, imageDomains_zero, Fin.castSucc_zero, imageDomains_zero]
      | succ t =>
          rw [imageDomains_cons_succ, imageDomains_succ k _ _ t, ← Fin.succ_castSucc,
            imageDomains_cons_succ]

/-- 递推式唯一确定中间像域：满足 `V_1 = U` 与 `V_{m+1} = ϕ_m(V_m)` 的族就是 `imageDomains`。 -/
theorem imageDomains_unique (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X)
    (V : Fin (k + 1) → Set X) (h0 : V 0 = U)
    (hsucc : ∀ m : Fin k, V m.succ = operator_image (ϕ m) (V m.castSucc)) :
    V = imageDomains k ϕ U := by
  funext m
  induction m using Fin.induction with
  | zero => rw [h0, imageDomains_zero]
  | succ t ih => rw [hsucc, ih, imageDomains_succ]

/-- 最后一个中间像域是整条链的像：`U_{k+1} = c_k(U_1)`。 -/
theorem imageDomains_last :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X),
      imageDomains k ϕ U (Fin.last k) = operator_image (chainComp k ϕ) U
  | 0, _, U => (Set.image_id' U).symm
  | k + 1, ϕ, U => by
      rw [← Fin.succ_last, imageDomains_cons_succ, imageDomains_last k]
      exact Set.image_image _ _ _

/-- 与链表示的对应：`U_{m+1} = c_m(U_1)`，其中 `c_m = ϕ_m ∘ ⋯ ∘ ϕ_1` 是前 `m` 步的复合。 -/
theorem imageDomains_eq_image_prefix (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X)
    (m : Fin (k + 1)) :
    imageDomains k ϕ U m =
      operator_image
        (chainComp m (fun t => ϕ (Fin.castLE (Nat.lt_succ_iff.mp m.isLt) t))) U := by
  induction m using Fin.induction with
  | zero =>
      rw [imageDomains_zero]
      exact (Set.image_id U).symm
  | succ t ih =>
      rw [imageDomains_succ, ih]
      change _ = operator_image (chainComp (t.1 + 1) _) U
      rw [chainComp_succ']
      exact Set.image_image _ _ _

/--
OET anchor: h-c80171fa685dc795
实际输入域落在各步定义域内：由 `U_1 ⊆ dom(c_k)` 得 `U_m ⊆ dom(ϕ_m)`（`m = 1, …, k`）。
-/
theorem imageDomains_subset_dom :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X), U ⊆ dom (chainComp k ϕ) →
      ∀ m : Fin k, imageDomains k ϕ U m.castSucc ⊆ dom (ϕ m)
  | 0, _, _, _, m => m.elim0
  | k + 1, ϕ, U, hU, m => by
      rw [chainComp_succ] at hU
      cases m using Fin.cases with
      | zero =>
          rw [Fin.castSucc_zero, imageDomains_zero]
          intro x hx h
          apply hU hx
          change (chainComp k fun t => ϕ t.succ).func ((ϕ 0).func x) = bot
          rw [h, Operator.preserves_bot]
      | succ t =>
          rw [← Fin.succ_castSucc, imageDomains_cons_succ]
          refine imageDomains_subset_dom k _ _ ?_ t
          rintro _ ⟨x, hx, rfl⟩
          exact hU hx

/-- 起始域非空时，所有中间像域非空。 -/
theorem imageDomains_nonempty (k : ℕ) (ϕ : Fin k → Operator X bot) {U : Set X}
    (hU : U.Nonempty) (m : Fin (k + 1)) : (imageDomains k ϕ U m).Nonempty := by
  induction m using Fin.induction with
  | zero => simpa using hU
  | succ t ih =>
      rw [imageDomains_succ]
      exact Set.image_nonempty.mpr ih

end Chain

/-! ## 零步复合的单位矩阵证书（CH02-P11, CH02-P12） -/

section ZeroStep

variable {X : Type} {bot : X} {I : Type} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- 恒等算子的定义域是全部非吸收点。 -/
theorem dom_operator_identity : dom (operator_identity : Operator X bot) = {x | x ≠ bot} := rfl

/-- 单位矩阵是恒等算子的全域 Lip 矩阵：`𝐈 ∈ 𝓛(id_X)`。 -/
theorem one_mem_lipSet_id :
    (1 : Matrix I I ENNReal) ∈ lipSet d (operator_identity : Operator X bot) := by
  intro x _ y _ j
  rw [sum_arrowEntry_one_mul (fun i => d i x y) j]
  exact le_rfl

/--
OET anchor: h-11006ddd8c43bfec
**注（零步复合的单位矩阵证书，Lip 部分）**：对 `U ⊆ dom(id_X)`（特别是任意非空的这类 `U`），
`𝐈 ∈ 𝓛(id_X)|_U`。
-/
theorem one_mem_restrictedLipSet_id {U : Set X}
    (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    (1 : Matrix I I ENNReal) ∈ restrictedLipSet d (operator_identity : Operator X bot) U :=
  ⟨hU, fun x hx y hy j => one_mem_lipSet_id d x (hU hx) y (hU hy) j⟩

/--
OET anchor: h-11006ddd8c43bfec
**注（零步复合的单位矩阵证书，co-Lip 部分）**：对任意非空 `U ⊆ dom(id_X)`，
`𝐈 ∈ 𝒦(id_X)|_U`。
-/
theorem one_mem_restrictedCoLipSet_id {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    (1 : Matrix I I ENNReal) ∈ restrictedCoLipSet d (operator_identity : Operator X bot) U := by
  refine ⟨hne, hU, fun x _ y _ j => ?_⟩
  rw [sum_arrowEntry_one_mul (fun i => d i x y) j]
  exact le_rfl

/-- 注的完整形式：对任意非空 `U ⊆ dom(id_X)`，`𝐈 ∈ 𝓛(id_X)|_U ∩ 𝒦(id_X)|_U`；
其中 `𝐈` 是矩阵空乘积、`id_X = c_0` 是零步复合。 -/
theorem orderedProd_zero_mem_inter (L : Fin 0 → Matrix I I ENNReal)
    (ϕ : Fin 0 → Operator X bot) {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (chainComp 0 ϕ)) :
    orderedProd 0 L ∈ restrictedLipSet d (chainComp 0 ϕ) U ∩
      restrictedCoLipSet d (chainComp 0 ϕ) U :=
  ⟨one_mem_restrictedLipSet_id d hU, one_mem_restrictedCoLipSet_id d hne hU⟩

end ZeroStep

/-! ## 有限复合的局部矩阵界（CH02-P09, CH02-P10） -/

section ChainBounds

variable {X : Type} {bot : X} {I : Type} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- Lip 链证书（任意长度 `k ≥ 0`；`k = 0` 即单位矩阵证书）。 -/
theorem orderedProd_mem_restrictedLipSet_chainComp :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X), U ⊆ dom (chainComp k ϕ) →
      ∀ L : Fin k → Matrix I I ENNReal,
        (∀ m : Fin k, L m ∈ restrictedLipSet d (ϕ m) (imageDomains k ϕ U m.castSucc)) →
        orderedProd k L ∈ restrictedLipSet d (chainComp k ϕ) U
  | 0, _, _, hU, _, _ => one_mem_restrictedLipSet_id d hU
  | k + 1, ϕ, U, hU, L, hL => by
      rw [chainComp_succ] at hU ⊢
      rw [orderedProd_succ]
      have hL0 : L 0 ∈ restrictedLipSet d (ϕ 0) U := by
        simpa using hL 0
      have ih := orderedProd_mem_restrictedLipSet_chainComp k (fun m => ϕ m.succ)
        (operator_image (ϕ 0) U) (operator_image_subset_dom_of_subset_dom_mul hU)
        (fun m => L m.succ) (fun m => by
          have h := hL m.succ
          rwa [← Fin.succ_castSucc, imageDomains_cons_succ] at h)
      exact mul_mem_restrictedLipSet_mul d hU hL0 ih

/--
OET anchor: h-c80171fa685dc795
**推论 2.5 (i)（Lip 上界）**：设 `k ≥ 1`，`U_1 ⊆ dom(c_k)`，`U_{m+1} = ϕ_m(U_m)`。
若 `L⁽ᵐ⁾ ∈ 𝓛(ϕ_m)|_{U_m}`（`m = 1, …, k`），则 `L⁽ᵏ⁾ ⋯ L⁽¹⁾ ∈ 𝓛(c_k)|_{U_1}`。
-/
theorem chain_lip_bound :
    ∀ k : ℕ, 1 ≤ k → ∀ (ϕ : Fin k → Operator X bot) (U₁ : Set X), U₁ ⊆ dom (chainComp k ϕ) →
      ∀ L : Fin k → Matrix I I ENNReal,
        (∀ m : Fin k, L m ∈ restrictedLipSet d (ϕ m) (imageDomains k ϕ U₁ m.castSucc)) →
        orderedProd k L ∈ restrictedLipSet d (chainComp k ϕ) U₁ :=
  fun k _ ϕ U₁ hU₁ L hL => orderedProd_mem_restrictedLipSet_chainComp d k ϕ U₁ hU₁ L hL

/-- 推论 2.5 (i) 的等价形式：逐步只需验证实际输入域 `U_m` 上的 Lip 不等式；
`U_m ⊆ dom(ϕ_m)` 由 `U_1 ⊆ dom(c_k)` 自动给出（`imageDomains_subset_dom`）。 -/
theorem chain_lip_bound_of_bounds (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (chainComp k ϕ)) (L : Fin k → Matrix I I ENNReal)
    (hL : ∀ m : Fin k, ∀ x ∈ imageDomains k ϕ U₁ m.castSucc,
      ∀ y ∈ imageDomains k ϕ U₁ m.castSucc, ∀ j : I,
        d j ((ϕ m).func x) ((ϕ m).func y) ≤ ∑ i, arrowEntry (L m) i j * d i x y) :
    orderedProd k L ∈ restrictedLipSet d (chainComp k ϕ) U₁ :=
  orderedProd_mem_restrictedLipSet_chainComp d k ϕ U₁ hU₁ L
    (fun m => ⟨imageDomains_subset_dom k ϕ U₁ hU₁ m, hL m⟩)

/-- co-Lip 链证书（任意长度 `k ≥ 0`，起始域非空；`k = 0` 即单位矩阵证书）。 -/
theorem orderedProd_mem_restrictedCoLipSet_chainComp_of_nonempty :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) (U : Set X), U.Nonempty →
      U ⊆ dom (chainComp k ϕ) → ∀ K : Fin k → Matrix I I ENNReal,
        (∀ m : Fin k, K m ∈ restrictedCoLipSet d (ϕ m) (imageDomains k ϕ U m.castSucc)) →
        orderedProd k K ∈ restrictedCoLipSet d (chainComp k ϕ) U
  | 0, _, _, hne, hU, _, _ => one_mem_restrictedCoLipSet_id d hne hU
  | k + 1, ϕ, U, hne, hU, K, hK => by
      rw [chainComp_succ] at hU ⊢
      rw [orderedProd_succ]
      have hK0 : K 0 ∈ restrictedCoLipSet d (ϕ 0) U := by
        simpa using hK 0
      have hU₂ : operator_image (ϕ 0) U ⊆ dom (chainComp k fun m => ϕ m.succ) := by
        rintro _ ⟨x, hx, rfl⟩
        exact hU hx
      have ih := orderedProd_mem_restrictedCoLipSet_chainComp_of_nonempty k (fun m => ϕ m.succ)
        (operator_image (ϕ 0) U) ((operator_image_nonempty_iff _ _).mpr hne) hU₂
        (fun m => K m.succ) (fun m => by
          have h := hK m.succ
          rwa [← Fin.succ_castSucc, imageDomains_cons_succ] at h)
      exact mul_mem_restrictedCoLipSet_mul d hU hK0 ih

/--
OET anchor: h-c80171fa685dc795
**推论 2.5 (ii)（co-Lip 下界）**：设 `k ≥ 1`，`U_1 ⊆ dom(c_k)`，`U_{m+1} = ϕ_m(U_m)`。
若 `K⁽ᵐ⁾ ∈ 𝒦(ϕ_m)|_{U_m}`（`m = 1, …, k`，各含非空性），则 `K⁽ᵏ⁾ ⋯ K⁽¹⁾ ∈ 𝒦(c_k)|_{U_1}`。
-/
theorem chain_coLip_bound :
    ∀ k : ℕ, 1 ≤ k → ∀ (ϕ : Fin k → Operator X bot) (U₁ : Set X), U₁ ⊆ dom (chainComp k ϕ) →
      ∀ K : Fin k → Matrix I I ENNReal,
        (∀ m : Fin k, K m ∈ restrictedCoLipSet d (ϕ m) (imageDomains k ϕ U₁ m.castSucc)) →
        orderedProd k K ∈ restrictedCoLipSet d (chainComp k ϕ) U₁ := by
  intro k hk ϕ U₁ hU₁ K hK
  have hne : U₁.Nonempty := by
    simpa using (hK ⟨0, hk⟩).nonempty
  exact orderedProd_mem_restrictedCoLipSet_chainComp_of_nonempty d k ϕ U₁ hne hU₁ K hK

/-- 推论 2.5 (ii) 的等价形式：起始域非空时，逐步只需验证实际输入域 `U_m` 上的 co-Lip
不等式；各 `U_m` 的非空性与 `U_m ⊆ dom(ϕ_m)` 均自动成立。 -/
theorem chain_coLip_bound_of_bounds (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X)
    (hne : U₁.Nonempty) (hU₁ : U₁ ⊆ dom (chainComp k ϕ)) (K : Fin k → Matrix I I ENNReal)
    (hK : ∀ m : Fin k, ∀ x ∈ imageDomains k ϕ U₁ m.castSucc,
      ∀ y ∈ imageDomains k ϕ U₁ m.castSucc, ∀ j : I,
        ∑ i, arrowEntry (K m) i j * d i x y ≤ d j ((ϕ m).func x) ((ϕ m).func y)) :
    orderedProd k K ∈ restrictedCoLipSet d (chainComp k ϕ) U₁ :=
  orderedProd_mem_restrictedCoLipSet_chainComp_of_nonempty d k ϕ U₁ hne hU₁ K
    (fun m => ⟨imageDomains_nonempty k ϕ hne m.castSucc,
      imageDomains_subset_dom k ϕ U₁ hU₁ m, hK m⟩)

end ChainBounds

/-! ## 有限指标路径与乘积条目判据（CH02-D06, CH02-P13, CH02-P14） -/

section Paths

variable {I : Type}

/--
OET anchor: h-e4154c34e95d3c23
**有限指标路径**：长度为 `n` 的路径 `(k_0, k_1, …, k_n)` 表示为 `k : Fin (n + 1) → I`；
从 `i` 到 `j` 指起止约定 `k_0 = i`、`k_n = j`，中间指标 `(k_1, …, k_{n-1})` 任意。
-/
def IsIndexPath (n : ℕ) (i j : I) (k : Fin (n + 1) → I) : Prop :=
  k 0 = i ∧ k (Fin.last n) = j

/-- 路径第 `m` 层（`m = 1, …, n`，索引 `⟨m - 1, _⟩`）的单步因子 `[M^{(m)}]_{k_{m-1} → k_m}`。 -/
def pathFactor {n : ℕ} (M : Fin n → Matrix I I ENNReal) (k : Fin (n + 1) → I) (m : Fin n) :
    ENNReal :=
  arrowEntry (M m) (k m.castSucc) (k m.succ)

/-- 路径含零因子：存在层级 `m` 使 `[M^{(m)}]_{k_{m-1} → k_m} = 0`。 -/
def HasZeroFactor {n : ℕ} (M : Fin n → Matrix I I ENNReal) (k : Fin (n + 1) → I) : Prop :=
  ∃ m : Fin n, pathFactor M k m = 0

/--
OET anchor: h-e4154c34e95d3c23
**全正路径**：沿路径的所有单步矩阵条目均严格为正。
-/
def IsPositivePath {n : ℕ} (M : Fin n → Matrix I I ENNReal) (k : Fin (n + 1) → I) : Prop :=
  ∀ m : Fin n, 0 < pathFactor M k m

/-- 由中间指标序列 `(k_1, …, k_{n-1})`（此处 `n = N + 1`）与约定 `k_0 = i`、`k_n = j`
得到的完整路径。`N = 0` 时中间序列为唯一的空序列。 -/
def intermediatePath (i j : I) {N : ℕ} (κ : Fin N → I) : Fin (N + 2) → I :=
  Fin.cons i (Fin.snoc κ j : Fin (N + 1) → I)

theorem intermediatePath_isIndexPath (i j : I) {N : ℕ} (κ : Fin N → I) :
    IsIndexPath (N + 1) i j (intermediatePath i j κ) := by
  refine ⟨rfl, ?_⟩
  simp [intermediatePath, ← Fin.succ_last]

/-- 中间指标序列与从 `i` 到 `j` 的路径一一对应。 -/
theorem isIndexPath_iff_exists_intermediatePath (i j : I) {N : ℕ} (k : Fin (N + 2) → I) :
    IsIndexPath (N + 1) i j k ↔ ∃ κ : Fin N → I, k = intermediatePath i j κ := by
  constructor
  · rintro ⟨h0, hlast⟩
    refine ⟨Fin.init (Fin.tail k), ?_⟩
    have htail : Fin.tail k (Fin.last N) = j := by
      rw [Fin.tail, Fin.succ_last]; exact hlast
    rw [intermediatePath, ← h0, ← htail, Fin.snoc_init_self, Fin.cons_self_tail]
  · rintro ⟨κ, rfl⟩
    exact intermediatePath_isIndexPath i j κ

theorem intermediatePath_injective (i j : I) {N : ℕ} :
    Function.Injective (intermediatePath i j (N := N)) := by
  intro κ₁ κ₂ h
  funext t
  have := congrFun h t.castSucc.succ
  simpa [intermediatePath] using this

theorem isIndexPath_cons {n : ℕ} (i j a : I) (q : Fin (n + 1) → I) :
    IsIndexPath (n + 1) i j (Fin.cons a q : Fin (n + 2) → I) ↔ a = i ∧ q (Fin.last n) = j := by
  simp [IsIndexPath, ← Fin.succ_last]

theorem hasZeroFactor_cons {n : ℕ} (M : Fin (n + 1) → Matrix I I ENNReal) (a : I)
    (q : Fin (n + 1) → I) :
    HasZeroFactor M (Fin.cons a q : Fin (n + 2) → I) ↔
      arrowEntry (M 0) a (q 0) = 0 ∨ HasZeroFactor (fun m => M m.succ) q := by
  simp only [HasZeroFactor, Fin.exists_fin_succ, pathFactor]
  simp

variable [Fintype I] [DecidableEq I]

/-- 零值判据（任意 `n ≥ 0` 的完整路径形式；`n = 0` 时对应单位矩阵）：
`[M^{(n)} ⋯ M^{(1)}]_{i→j} = 0` 当且仅当每条从 `i` 到 `j` 的路径都含零因子。 -/
theorem arrowEntry_orderedProd_eq_zero_iff (n : ℕ) (M : Fin n → Matrix I I ENNReal) (i j : I) :
    arrowEntry (orderedProd n M) i j = 0 ↔
      ∀ k : Fin (n + 1) → I, IsIndexPath n i j k → HasZeroFactor M k := by
  induction n generalizing i with
  | zero =>
      simp only [orderedProd_zero, arrowEntry_one, IsIndexPath, HasZeroFactor, Fin.last_zero,
        IsEmpty.exists_iff, imp_false, not_and]
      constructor
      · intro h k hk hkj
        rw [← hk, ← hkj] at h
        simp at h
      · intro h
        have hij : i ≠ j := fun hij => h (fun _ => i) rfl hij
        simp [hij]
  | succ n ih =>
      rw [orderedProd_succ, arrowEntry_mul, Finset.sum_eq_zero_iff, Fin.forall_fin_succ_pi]
      simp only [Finset.mem_univ, true_implies, mul_eq_zero, isIndexPath_cons, hasZeroFactor_cons]
      constructor
      · rintro h a q ⟨rfl, hq⟩
        rcases h (q 0) with h1 | h1
        · exact Or.inr ((ih _ (q 0)).mp h1 q ⟨rfl, hq⟩)
        · exact Or.inl h1
      · intro h l
        by_cases hl : arrowEntry (M 0) i l = 0
        · exact Or.inr hl
        · refine Or.inl ((ih _ l).mpr ?_)
          rintro q ⟨hq0, hq⟩
          rcases h i q ⟨rfl, hq⟩ with h1 | h1
          · exact absurd (hq0 ▸ h1) hl
          · exact h1

/-- 正值判据（任意 `n ≥ 0` 的完整路径形式）：`[M^{(n)} ⋯ M^{(1)}]_{i→j} > 0` 当且仅当
存在一条从 `i` 到 `j` 的全正路径。 -/
theorem arrowEntry_orderedProd_pos_iff (n : ℕ) (M : Fin n → Matrix I I ENNReal) (i j : I) :
    0 < arrowEntry (orderedProd n M) i j ↔
      ∃ k : Fin (n + 1) → I, IsIndexPath n i j k ∧ IsPositivePath M k := by
  rw [pos_iff_ne_zero, Ne, arrowEntry_orderedProd_eq_zero_iff]
  simp only [IsPositivePath, HasZeroFactor, pos_iff_ne_zero]
  push Not
  rfl

/--
OET anchor: h-e4154c34e95d3c23
**命题 2.6 (i)（零值判据）**：设 `n = N + 1 ≥ 1`。`[M^{(n)} ⋯ M^{(1)}]_{i→j} = 0`
当且仅当对任意中间指标序列 `(k_1, …, k_{n-1})`，存在层级 `m ∈ {1, …, n}` 使
`[M^{(m)}]_{k_{m-1} → k_m} = 0`（约定 `k_0 = i`、`k_n = j`）。`N = 0` 即 `n = 1`。
-/
theorem orderedProd_entry_eq_zero_iff (N : ℕ) (M : Fin (N + 1) → Matrix I I ENNReal)
    (i j : I) :
    arrowEntry (orderedProd (N + 1) M) i j = 0 ↔
      ∀ κ : Fin N → I, ∃ m : Fin (N + 1), pathFactor M (intermediatePath i j κ) m = 0 := by
  rw [arrowEntry_orderedProd_eq_zero_iff]
  constructor
  · intro h κ
    exact h _ (intermediatePath_isIndexPath i j κ)
  · intro h k hk
    obtain ⟨κ, rfl⟩ := (isIndexPath_iff_exists_intermediatePath i j k).mp hk
    exact h κ

/--
OET anchor: h-e4154c34e95d3c23
**命题 2.6 (ii)（正值判据）**：设 `n = N + 1 ≥ 1`。`[M^{(n)} ⋯ M^{(1)}]_{i→j} > 0`
当且仅当存在至少一条中间指标序列 `(k_1, …, k_{n-1})`，沿该路径所有单步条目
`[M^{(m)}]_{k_{m-1} → k_m}`（`m = 1, …, n`，`k_0 = i`、`k_n = j`）均严格为正。
-/
theorem orderedProd_entry_pos_iff (N : ℕ) (M : Fin (N + 1) → Matrix I I ENNReal) (i j : I) :
    0 < arrowEntry (orderedProd (N + 1) M) i j ↔
      ∃ κ : Fin N → I, IsPositivePath M (intermediatePath i j κ) := by
  rw [arrowEntry_orderedProd_pos_iff]
  constructor
  · rintro ⟨k, hk, hpos⟩
    obtain ⟨κ, rfl⟩ := (isIndexPath_iff_exists_intermediatePath i j k).mp hk
    exact ⟨κ, hpos⟩
  · rintro ⟨κ, hpos⟩
    exact ⟨_, intermediatePath_isIndexPath i j κ, hpos⟩

/-- `n = 1` 时唯一的（空）中间序列给出路径 `(k_0, k_1) = (i, j)`，零值判据退化为
`[M^{(1)}]_{i→j} = 0`。 -/
theorem orderedProd_one_entry_eq_zero_iff (M : Fin 1 → Matrix I I ENNReal) (i j : I) :
    arrowEntry (orderedProd 1 M) i j = 0 ↔ arrowEntry (M 0) i j = 0 := by
  rw [orderedProd_entry_eq_zero_iff]
  simp [pathFactor, intermediatePath, Fin.exists_fin_one, Fin.snoc]

/-- `n = 1` 时正值判据退化为 `[M^{(1)}]_{i→j} > 0`。 -/
theorem orderedProd_one_entry_pos_iff (M : Fin 1 → Matrix I I ENNReal) (i j : I) :
    0 < arrowEntry (orderedProd 1 M) i j ↔ 0 < arrowEntry (M 0) i j := by
  rw [orderedProd_entry_pos_iff]
  simp [IsPositivePath, pathFactor, intermediatePath, Fin.forall_fin_one, Fin.snoc]

end Paths

end LCH02
