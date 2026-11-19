import Mathlib
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# 第 2 章 算子界（§ 2.1 矩阵界与有限复合）

对应 `source/02-operator-bounds.md` 中义务清单 LCH02 的全部 20 项。

表示约定：
* 规范族 `𝒢 = {d_i}_{i∈I}` 表示为 `d : I → X → X → ENNReal`，`I` 带 `[Fintype I]`；
  本文件的结论都不需要伪度量公理或 `I` 非空，因此对任意距离族陈述（特别地适用于
  扩展规范空间）。
* 算子 `ϕ ∈ 𝒳_op` 为前置模块中的 `Operator X bot`；复合 `ϕ₂ ∘ ϕ₁` 为幺半群乘法 `ϕ₂ * ϕ₁`；
  像集 `ϕ(U)` 为 `operator_image ϕ U`；定义域为 `dom ϕ`。
* 矩阵为 `Matrix I I ENNReal`，以输出分量为行、输入分量为列：`L_{i→j} = L j i`。
-/

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open Finset

/-! ## D03 输入/输出矩阵指标约定与乘法 -/

section MatrixConvention

variable {I : Type}

/-- 条目 `M_{i→j}`：第 `j` 行（输出分量）、第 `i` 列（输入分量），即 `(M)_{ji} = M_{i→j}`。 -/
def arrowEntry (M : Matrix I I ENNReal) (i j : I) : ENNReal := M j i

/-- 行列约定：矩阵第 `j` 行第 `i` 列的元素就是 `M_{i→j}`。 -/
theorem matrix_apply_eq_arrowEntry (M : Matrix I I ENNReal) (i j : I) :
    M j i = arrowEntry M i j := rfl

/-- 矩阵乘法在箭头记号下：`(A · B)_{i→j} = ∑_k A_{k→j} B_{i→k}`。 -/
theorem arrowEntry_mul [Fintype I] (A B : Matrix I I ENNReal) (i j : I) :
    arrowEntry (A * B) i j = ∑ k, arrowEntry A k j * arrowEntry B i k := by
  simp [arrowEntry, Matrix.mul_apply]

/-- 单位矩阵的条目：`𝐈_{i→j} = 1`（`i = j`），否则为 `0`。 -/
theorem arrowEntry_one [DecidableEq I] (i j : I) :
    arrowEntry (1 : Matrix I I ENNReal) i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [arrowEntry]
  · simp [arrowEntry, h, Matrix.one_apply_ne (Ne.symm h)]

/-- 单位矩阵按行求和：`∑_i 𝐈_{i→j} f(i) = f(j)`。 -/
theorem sum_arrowEntry_one_mul [Fintype I] [DecidableEq I] (f : I → ENNReal) (j : I) :
    ∑ i, arrowEntry (1 : Matrix I I ENNReal) i j * f i = f j := by
  simp [arrowEntry_one, ite_mul]

/-- `I = {1,2,3}`（此处为 `Fin 3`，指标 `0,1,2`）时的行列形式：第一行汇集指向输出分量 `d₁`
的系数，例如 `L_{2→1}` 位于第一行、第二列。 -/
theorem arrowEntry_fin_three (a₁₁ a₂₁ a₃₁ a₁₂ a₂₂ a₃₂ a₁₃ a₂₃ a₃₃ : ENNReal) :
    let L : Matrix (Fin 3) (Fin 3) ENNReal :=
      !![a₁₁, a₂₁, a₃₁; a₁₂, a₂₂, a₃₂; a₁₃, a₂₃, a₃₃]
    arrowEntry L 1 0 = a₂₁ ∧ arrowEntry L 0 1 = a₁₂ ∧ arrowEntry L 2 0 = a₃₁ ∧
      arrowEntry L 0 2 = a₁₃ := by
  simp [arrowEntry]

end MatrixConvention

/-! ## D04 单位矩阵、空乘积及有序非空乘积 -/

section OrderedProduct

variable {α : Type*} [Monoid α]

/-- 有序乘积 `M^{(n)} ⋯ M^{(1)}`，其中 `M^{(m)} = M (m-1)`（`Fin` 指标从 `0` 起）；
空乘积（`n = 0`）为单位元。 -/
def finOrderedProd : {n : ℕ} → (Fin n → α) → α
  | 0, _ => 1
  | n + 1, M => M (Fin.last n) * finOrderedProd (fun m : Fin n => M m.castSucc)

/-- 空乘积为单位元。 -/
@[simp] theorem finOrderedProd_zero (M : Fin 0 → α) : finOrderedProd M = 1 := rfl

/-- 有序乘积的递推：`M^{(n+1)} ⋯ M^{(1)} = M^{(n+1)} · (M^{(n)} ⋯ M^{(1)})`。 -/
theorem finOrderedProd_succ {n : ℕ} (M : Fin (n + 1) → α) :
    finOrderedProd M = M (Fin.last n) * finOrderedProd (fun m : Fin n => M m.castSucc) := rfl

/-- 单项乘积即该项本身。 -/
@[simp] theorem finOrderedProd_one (M : Fin 1 → α) : finOrderedProd M = M 0 := by
  simp [finOrderedProd_succ]

/-- 有序乘积等于按 `M^{(n)}, …, M^{(1)}` 次序排列的列表乘积。 -/
theorem finOrderedProd_eq_list_prod {n : ℕ} (M : Fin n → α) :
    finOrderedProd M = (List.ofFn M).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [finOrderedProd_succ, ih, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp

/-- 有序乘积的另一递推：`M^{(n+1)} ⋯ M^{(1)} = (M^{(n+1)} ⋯ M^{(2)}) · M^{(1)}`。 -/
theorem finOrderedProd_succ' {n : ℕ} (M : Fin (n + 1) → α) :
    finOrderedProd M = finOrderedProd (fun m : Fin n => M m.succ) * M 0 := by
  rw [finOrderedProd_eq_list_prod, finOrderedProd_eq_list_prod, List.ofFn_succ]
  simp

end OrderedProduct

/-- 以 `I` 为指标的扩展非负单位矩阵就是空有序乘积。 -/
theorem finOrderedProd_matrix_zero {I : Type} [Fintype I] [DecidableEq I]
    (M : Fin 0 → Matrix I I ENNReal) : finOrderedProd M = 1 := rfl

/-! ## D01 全域/受限 Lip 矩阵谓词与证书族 -/

section Certificates

variable {X : Type} {bot : X} {I : Type} [Fintype I]

/-- `L` 是 `ϕ` 的合法 Lipschitz 矩阵：对所有 `x, y ∈ dom ϕ` 与 `j ∈ I`，
`d_j(ϕ x, ϕ y) ≤ ∑_i L_{i→j} d_i(x, y)`。 -/
def IsLipMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : Matrix I I ENNReal) :
    Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y

/-- 全体合法 Lip 矩阵之集 `𝓛(ϕ)`。 -/
def lipSet (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (Matrix I I ENNReal) :=
  {L | IsLipMatrix d ϕ L}

/-- `L` 是 `ϕ` 在子集 `U ⊆ dom ϕ` 上的受限 Lip 矩阵（定义域条件 `U ⊆ dom ϕ` 计入谓词）。 -/
def IsLipMatrixOn (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : Matrix I I ENNReal) : Prop :=
  U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y

/-- 受限合法 Lip 矩阵之集 `𝓛(ϕ)|_U`。 -/
def lipSetOn (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {L | IsLipMatrixOn d ϕ U L}

/-- 全域证书族即在 `U = dom ϕ` 上的受限证书族。 -/
theorem lipSet_eq_lipSetOn_dom (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    lipSet d ϕ = lipSetOn d ϕ (dom ϕ) := by
  ext L
  exact ⟨fun h => ⟨subset_rfl, h⟩, fun h => h.2⟩

/-! ## D02 含非空条件的受限 co-Lip 矩阵及证书族 -/

/-- `K` 是 `ϕ` 在非空子集 `U ⊆ dom ϕ` 上的合法受限 co-Lipschitz 矩阵：
对所有 `x, y ∈ U` 与 `j ∈ I`，`d_j(ϕ x, ϕ y) ≥ ∑_i K_{i→j} d_i(x, y)`。
非空性 `U ≠ ∅` 与 `U ⊆ dom ϕ` 计入谓词。 -/
def IsCoLipMatrixOn (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : Matrix I I ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i, arrowEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- 受限合法 co-Lip 矩阵之集 `𝒦(ϕ)|_U`。 -/
def coLipSetOn (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {K | IsCoLipMatrixOn d ϕ U K}

/-- 凡 `𝒦(ϕ)|_U` 非空，`U` 必非空。 -/
theorem nonempty_of_mem_coLipSetOn {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {K : Matrix I I ENNReal} (hK : K ∈ coLipSetOn d ϕ U) : U.Nonempty :=
  hK.1

/-! ## P01 单分量求和退化为标量 Lip 界 -/

/-- 受限形式：当 `I = {i}` 时，受限 Lip 矩阵条件退化为单个标量不等式。 -/
theorem lipSetOn_single_component (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i : I) (hI : ∀ k : I, k = i) (L : Matrix I I ENNReal) :
    L ∈ lipSetOn d ϕ U ↔
      U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U,
        d i (ϕ.func x) (ϕ.func y) ≤ arrowEntry L i i * d i x y := by
  have hsum : ∀ f : I → ENNReal, ∑ k, f k = f i := fun f => by
    rw [Finset.sum_eq_single i (fun k _ hk => absurd (hI k) hk) (fun h => absurd (mem_univ i) h)]
  simp only [lipSetOn, IsLipMatrixOn, Set.mem_setOf_eq, hsum]
  refine and_congr_right fun _ => ⟨fun h x hx y hy => h x hx y hy i, fun h x hx y hy j => ?_⟩
  rw [hI j]
  exact h x hx y hy

/-- **注（单分量情形下的标量 Lip 界）**：当 `I = {i}` 时，`L ∈ 𝓛(ϕ)` 当且仅当
`d_i(ϕ x, ϕ y) ≤ L_{i→i} d_i(x, y)` 对所有 `x, y ∈ dom ϕ` 成立。 -/
theorem lipSet_single_component (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i : I) (hI : ∀ k : I, k = i) (L : Matrix I I ENNReal) :
    L ∈ lipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d i (ϕ.func x) (ϕ.func y) ≤ arrowEntry L i i * d i x y := by
  rw [lipSet_eq_lipSetOn_dom, lipSetOn_single_component d ϕ (dom ϕ) i hI L]
  exact ⟨fun h => h.2, fun h => ⟨subset_rfl, h⟩⟩

/-! ## P02 受限 Lip 矩阵族反单调；P03 全域 Lip 证书可限制 -/

/-- **引理 2.1**：若 `U ⊆ V ⊆ dom ϕ`，则 `𝓛(ϕ)|_V ⊆ 𝓛(ϕ)|_U`。 -/
theorem lipSetOn_antitone (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    lipSetOn d ϕ V ⊆ lipSetOn d ϕ U := by
  rintro L ⟨-, hL⟩
  exact ⟨hUV.trans hV, fun x hx y hy j => hL x (hUV hx) y (hUV hy) j⟩

/-- **引理 2.1（特别情形）**：对任意 `U ⊆ dom ϕ`，`𝓛(ϕ) ⊆ 𝓛(ϕ)|_U`。 -/
theorem lipSet_subset_lipSetOn (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom ϕ) :
    lipSet d ϕ ⊆ lipSetOn d ϕ U := by
  rw [lipSet_eq_lipSetOn_dom]
  exact lipSetOn_antitone d ϕ hU subset_rfl

/-! ## P05 非空受限 co-Lip 矩阵族反单调；P06 全域 co-Lip 证书可限制 -/

/-- **引理 2.3**：若 `∅ ≠ U ⊆ V ⊆ dom ϕ`，则 `𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U`。 -/
theorem coLipSetOn_antitone (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hU : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    coLipSetOn d ϕ V ⊆ coLipSetOn d ϕ U := by
  rintro K ⟨-, -, hK⟩
  exact ⟨hU, hUV.trans hV, fun x hx y hy j => hK x (hUV hx) y (hUV hy) j⟩

/-- **引理 2.3（特别情形）**：对任意非空 `U ⊆ dom ϕ`，`𝒦(ϕ)|_{dom ϕ} ⊆ 𝒦(ϕ)|_U`。 -/
theorem coLipSetOn_dom_subset (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU : U.Nonempty) (hUdom : U ⊆ dom ϕ) :
    coLipSetOn d ϕ (dom ϕ) ⊆ coLipSetOn d ϕ U :=
  coLipSetOn_antitone d ϕ hU hUdom subset_rfl

/-! ## P07 输出零距且输入正距迫使对应 co-Lip 条目为 0 -/

/-- **注（co-Lip 条目为零的充分条件）**：若存在 `x, y ∈ dom ϕ` 使
`d_j(ϕ x, ϕ y) = 0` 且 `d_i(x, y) > 0`，则任一 `K ∈ 𝒦(ϕ)|_{dom ϕ}` 满足 `K_{i→j} = 0`。 -/
theorem coLip_entry_eq_zero (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I)
    (h : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y) :
    ∀ K ∈ coLipSetOn d ϕ (dom ϕ), arrowEntry K i j = 0 := by
  rintro K ⟨-, -, hK⟩
  obtain ⟨x, hx, y, hy, hzero, hpos⟩ := h
  have hle : arrowEntry K i j * d i x y ≤ 0 :=
    calc arrowEntry K i j * d i x y
        ≤ ∑ k, arrowEntry K k j * d k x y :=
          Finset.single_le_sum (f := fun k => arrowEntry K k j * d k x y)
            (fun _ _ => zero_le _) (mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK x hx y hy j
      _ = 0 := hzero
  have hprod : arrowEntry K i j * d i x y = 0 := le_antisymm hle (zero_le _)
  rcases mul_eq_zero.mp hprod with hK0 | hd0
  · exact hK0
  · exact absurd hd0 hpos.ne'

/-! ## P04 两步 Lip 复合；P08 两步 co-Lip 复合 -/

/-- 复合定义域落在内层算子的定义域内：`dom(ϕ₂ ∘ ϕ₁) ⊆ dom ϕ₁`。 -/
theorem dom_mul_subset_right (ϕ₂ ϕ₁ : Operator X bot) : dom (ϕ₂ * ϕ₁) ⊆ dom ϕ₁ := by
  intro x hx h
  apply hx
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [h, ϕ₂.preserves_bot]

/-- 复合定义直接保证 `U₂ = ϕ₁(U₁) ⊆ dom ϕ₂`（当 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`）。 -/
theorem image_subset_dom_of_subset_dom_mul {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) : operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU₁ hx

/-- 非空集合的像集非空。 -/
theorem operator_image_nonempty {ϕ : Operator X bot} {U : Set X} (hU : U.Nonempty) :
    (operator_image ϕ U).Nonempty :=
  hU.image ϕ.func

/-- **命题 2.2（Lip 矩阵复合律）**：设 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，`U₂ = ϕ₁(U₁)`。
若 `L₁ ∈ 𝓛(ϕ₁)|_{U₁}`、`L₂ ∈ 𝓛(ϕ₂)|_{U₂}`，则 `L₂ · L₁ ∈ 𝓛(ϕ₂ ∘ ϕ₁)|_{U₁}`。 -/
theorem lip_comp (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) (L₁ L₂ : Matrix I I ENNReal)
    (h₁ : L₁ ∈ lipSetOn d ϕ₁ U₁) (h₂ : L₂ ∈ lipSetOn d ϕ₂ (operator_image ϕ₁ U₁)) :
    L₂ * L₁ ∈ lipSetOn d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hx' : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
      = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k, arrowEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := h₂.2 _ hx' _ hy' j
    _ ≤ ∑ k, arrowEntry L₂ k j * ∑ i, arrowEntry L₁ i k * d i x y := by
        gcongr with k
        exact h₁.2 x hx y hy k
    _ = ∑ i, arrowEntry (L₂ * L₁) i j * d i x y := by
        simp only [arrowEntry_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm

/-- **命题 2.4（co-Lip 矩阵复合律）**：设 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，`U₂ = ϕ₁(U₁)`。
若 `K₁ ∈ 𝒦(ϕ₁)|_{U₁}`、`K₂ ∈ 𝒦(ϕ₂)|_{U₂}`，则 `K₂ · K₁ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}`
（非空性条件由 `K₁ ∈ 𝒦(ϕ₁)|_{U₁}` 继承）。 -/
theorem coLip_comp (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) (K₁ K₂ : Matrix I I ENNReal)
    (h₁ : K₁ ∈ coLipSetOn d ϕ₁ U₁) (h₂ : K₂ ∈ coLipSetOn d ϕ₂ (operator_image ϕ₁ U₁)) :
    K₂ * K₁ ∈ coLipSetOn d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨h₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hx' : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc ∑ i, arrowEntry (K₂ * K₁) i j * d i x y
      = ∑ k, arrowEntry K₂ k j * ∑ i, arrowEntry K₁ i k * d i x y := by
        simp only [arrowEntry_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ ≤ ∑ k, arrowEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
        gcongr with k
        exact h₁.2.2 x hx y hy k
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := h₂.2.2 _ hx' _ hy' j
    _ = d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) := rfl

/-! ## P11 / P12 零步恒等算子的单位矩阵证书 -/

/-- 恒等算子 `id_𝒳`（幺半群单位元）的定义域为全体非吸收点。 -/
theorem dom_one : dom (1 : Operator X bot) = {x | x ≠ bot} := rfl

variable [DecidableEq I]

/-- 单位矩阵是恒等算子在任意 `U ⊆ dom(id_𝒳)` 上的 Lip 矩阵：`𝐈 ∈ 𝓛(id_𝒳)|_U`。 -/
theorem one_mem_lipSetOn_one (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (1 : Operator X bot)) :
    (1 : Matrix I I ENNReal) ∈ lipSetOn d (1 : Operator X bot) U := by
  refine ⟨hU, fun x _ y _ j => ?_⟩
  rw [sum_arrowEntry_one_mul (fun i => d i x y) j]
  exact le_rfl

/-- 单位矩阵是恒等算子在任意非空 `U ⊆ dom(id_𝒳)` 上的 co-Lip 矩阵：`𝐈 ∈ 𝒦(id_𝒳)|_U`。 -/
theorem one_mem_coLipSetOn_one (d : I → X → X → ENNReal) {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    (1 : Matrix I I ENNReal) ∈ coLipSetOn d (1 : Operator X bot) U := by
  refine ⟨hne, hU, fun x _ y _ j => ?_⟩
  rw [sum_arrowEntry_one_mul (fun i => d i x y) j]
  exact le_rfl

/-- **注（零步复合的单位矩阵证书）**：`c₀ = id_𝒳` 为空复合，矩阵空复合乘积为 `𝐈`；
对任意非空 `U ⊆ dom(id_𝒳)`，`𝐈 ∈ 𝓛(id_𝒳)|_U ∩ 𝒦(id_𝒳)|_U`。 -/
theorem zero_step_certificate (d : I → X → X → ENNReal) (ϕ : Fin 0 → Operator X bot)
    (M : Fin 0 → Matrix I I ENNReal) {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (finOrderedProd ϕ)) :
    finOrderedProd M ∈ lipSetOn d (finOrderedProd ϕ) U ∩ coLipSetOn d (finOrderedProd ϕ) U :=
  ⟨one_mem_lipSetOn_one d hU, one_mem_coLipSetOn_one d hne hU⟩

end Certificates

/-! ## D05 实际中间像域与链表示对应 -/

section Chains

variable {X : Type} {bot : X}

/-- 零步复合 `c₀` 是恒等算子 `id_𝒳`。 -/
theorem finOrderedProd_operator_zero (ϕ : Fin 0 → Operator X bot) :
    finOrderedProd ϕ = operator_identity := rfl

/-- 有限复合的作用：`c_{k+1} = ϕ_{k+1} ∘ c_k`（函数复合意义）。 -/
theorem finOrderedProd_operator_func_succ {k : ℕ} (ϕ : Fin (k + 1) → Operator X bot) :
    (finOrderedProd ϕ).func =
      (ϕ (Fin.last k)).func ∘ (finOrderedProd (fun m : Fin k => ϕ m.castSucc)).func := rfl

/-- `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1` 与前置模块的链表示 `OperatorChain [ϕ_k, …, ϕ_1]` 一致。 -/
theorem finOrderedProd_eq_operatorChain {k : ℕ} (ϕ : Fin k → Operator X bot) :
    finOrderedProd ϕ = OperatorChain (List.ofFn ϕ).reverse := by
  rw [operator_chain_eq_prod, finOrderedProd_eq_list_prod]

/-- 实际中间像域：`U_1 = U₁`，`U_{m+1} = ϕ_m(U_m)`（`Fin` 指标从 `0` 起：
`chainDomain ϕ U₁ m` 表示 `U_{m+1}`，第 `m` 步算子 `ϕ m` 的输入域为 `chainDomain ϕ U₁ m.castSucc`）。 -/
def chainDomain {k : ℕ} (ϕ : Fin k → Operator X bot) (U₁ : Set X) : Fin (k + 1) → Set X :=
  Fin.induction U₁ (fun m Um => operator_image (ϕ m) Um)

@[simp] theorem chainDomain_zero {k : ℕ} (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    chainDomain ϕ U₁ 0 = U₁ := by
  simp [chainDomain]

theorem chainDomain_succ {k : ℕ} (ϕ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    chainDomain ϕ U₁ m.succ = operator_image (ϕ m) (chainDomain ϕ U₁ m.castSucc) := by
  simp [chainDomain]

/-- 截去最后一步后，前面各步的中间像域不变。 -/
theorem chainDomain_init {k : ℕ} (ϕ : Fin (k + 1) → Operator X bot) (U₁ : Set X)
    (m : Fin (k + 1)) :
    chainDomain (fun i : Fin k => ϕ i.castSucc) U₁ m = chainDomain ϕ U₁ m.castSucc := by
  induction m using Fin.induction with
  | zero => simp
  | succ m ih =>
    rw [chainDomain_succ, ih, ← Fin.succ_castSucc, chainDomain_succ]

/-- 末端像域是全复合的像：`U_{k+1} = c_k(U₁)`。 -/
theorem chainDomain_last {k : ℕ} (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    chainDomain ϕ U₁ (Fin.last k) = operator_image (finOrderedProd ϕ) U₁ := by
  induction k with
  | zero =>
    show U₁ = id '' U₁
    rw [Set.image_id]
  | succ k ih =>
    rw [← Fin.succ_last, chainDomain_succ, ← chainDomain_init, ih]
    simp only [operator_image, finOrderedProd_operator_func_succ, Set.image_comp]

/-- 一般地，`U_{m+1} = c_m(U₁)`：第 `m+1` 个像域是前 `m` 步部分复合的像。 -/
theorem chainDomain_eq_image_partial {k : ℕ} (ϕ : Fin k → Operator X bot) (U₁ : Set X)
    (m : Fin (k + 1)) :
    chainDomain ϕ U₁ m =
      operator_image (finOrderedProd (fun i : Fin m => ϕ (Fin.castLE (Nat.lt_succ_iff.mp m.isLt) i)))
        U₁ := by
  induction m using Fin.induction with
  | zero =>
    show U₁ = id '' U₁
    rw [Set.image_id]
  | succ m ih =>
    rw [chainDomain_succ, ih]
    simp only [operator_image, Fin.val_succ, finOrderedProd_operator_func_succ, Set.image_comp]
    rfl

/-- 由 `U₁ ⊆ dom(c_k)` 逐步递推得 `U_m ⊆ dom(ϕ_m)`（`m = 1, …, k`）。 -/
theorem chainDomain_subset_dom {k : ℕ} (ϕ : Fin k → Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (finOrderedProd ϕ)) (m : Fin k) :
    chainDomain ϕ U₁ m.castSucc ⊆ dom (ϕ m) := by
  induction k with
  | zero => exact m.elim0
  | succ k ih =>
    have hinit : U₁ ⊆ dom (finOrderedProd (fun i : Fin k => ϕ i.castSucc)) :=
      hU₁.trans (dom_mul_subset_right _ _)
    induction m using Fin.lastCases with
    | last =>
      rw [← chainDomain_init, chainDomain_last]
      exact image_subset_dom_of_subset_dom_mul hU₁
    | cast m =>
      rw [← chainDomain_init]
      exact ih (fun i => ϕ i.castSucc) hinit m

end Chains

/-! ## P09 / P10 任意正长度链的 Lip / co-Lip 连乘界 -/

section ChainBounds

variable {X : Type} {bot : X} {I : Type} [Fintype I] [DecidableEq I]

/-- Lip 连乘界（对所有 `k ≥ 0` 成立的归纳形式）。 -/
theorem lip_chain_certificate_general (d : I → X → X → ENNReal) {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U₁ : Set X) (hU₁ : U₁ ⊆ dom (finOrderedProd ϕ))
    (L : Fin k → Matrix I I ENNReal)
    (hL : ∀ m : Fin k, L m ∈ lipSetOn d (ϕ m) (chainDomain ϕ U₁ m.castSucc)) :
    finOrderedProd L ∈ lipSetOn d (finOrderedProd ϕ) U₁ := by
  induction k with
  | zero => exact one_mem_lipSetOn_one d hU₁
  | succ k ih =>
    have hinit : U₁ ⊆ dom (finOrderedProd (fun i : Fin k => ϕ i.castSucc)) :=
      hU₁.trans (dom_mul_subset_right _ _)
    refine lip_comp d _ _ U₁ hU₁ _ _ ?_ ?_
    · refine ih (fun i => ϕ i.castSucc) hinit (fun i => L i.castSucc) fun m => ?_
      rw [chainDomain_init]
      exact hL m.castSucc
    · have h := hL (Fin.last k)
      rwa [← chainDomain_init, chainDomain_last] at h

/-- **推论 2.5 (i)（有限复合的局部 Lip 矩阵界）**：设 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`（`k ≥ 1`），
`U₁ ⊆ dom(c_k)`，`U_{m+1} = ϕ_m(U_m)`。若 `L^{(m)} ∈ 𝓛(ϕ_m)|_{U_m}` 对每步成立，则
`L^{(k)} ⋯ L^{(1)} ∈ 𝓛(c_k)|_{U₁}`。
（前提 `1 ≤ k` 按原文保留；证明不需要它，`k = 0` 情形见 `lip_chain_certificate_general`。） -/
theorem lip_chain_certificate (d : I → X → X → ENNReal) {k : ℕ} (_hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) (U₁ : Set X) (hU₁ : U₁ ⊆ dom (finOrderedProd ϕ))
    (L : Fin k → Matrix I I ENNReal)
    (hL : ∀ m : Fin k, L m ∈ lipSetOn d (ϕ m) (chainDomain ϕ U₁ m.castSucc)) :
    finOrderedProd L ∈ lipSetOn d (finOrderedProd ϕ) U₁ := by
  exact lip_chain_certificate_general d ϕ U₁ hU₁ L hL

/-- co-Lip 连乘界（在 `U₁` 非空时对所有 `k ≥ 0` 成立的归纳形式）。 -/
theorem coLip_chain_certificate_of_nonempty (d : I → X → X → ENNReal) {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U₁ : Set X) (hne : U₁.Nonempty)
    (hU₁ : U₁ ⊆ dom (finOrderedProd ϕ))
    (K : Fin k → Matrix I I ENNReal)
    (hK : ∀ m : Fin k, K m ∈ coLipSetOn d (ϕ m) (chainDomain ϕ U₁ m.castSucc)) :
    finOrderedProd K ∈ coLipSetOn d (finOrderedProd ϕ) U₁ := by
  induction k with
  | zero => exact one_mem_coLipSetOn_one d hne hU₁
  | succ k ih =>
    have hinit : U₁ ⊆ dom (finOrderedProd (fun i : Fin k => ϕ i.castSucc)) :=
      hU₁.trans (dom_mul_subset_right _ _)
    refine coLip_comp d _ _ U₁ hU₁ _ _ ?_ ?_
    · refine ih (fun i => ϕ i.castSucc) hinit (fun i => K i.castSucc) fun m => ?_
      rw [chainDomain_init]
      exact hK m.castSucc
    · have h := hK (Fin.last k)
      rwa [← chainDomain_init, chainDomain_last] at h

/-- **推论 2.5 (ii)（有限复合的局部 co-Lip 矩阵界）**：设 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`（`k ≥ 1`），
`U₁ ⊆ dom(c_k)`，`U_{m+1} = ϕ_m(U_m)`。若 `K^{(m)} ∈ 𝒦(ϕ_m)|_{U_m}` 对每步成立，则
`K^{(k)} ⋯ K^{(1)} ∈ 𝒦(c_k)|_{U₁}`。 -/
theorem coLip_chain_certificate (d : I → X → X → ENNReal) {k : ℕ} (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) (U₁ : Set X) (hU₁ : U₁ ⊆ dom (finOrderedProd ϕ))
    (K : Fin k → Matrix I I ENNReal)
    (hK : ∀ m : Fin k, K m ∈ coLipSetOn d (ϕ m) (chainDomain ϕ U₁ m.castSucc)) :
    finOrderedProd K ∈ coLipSetOn d (finOrderedProd ϕ) U₁ := by
  have hne : U₁.Nonempty := by
    have h := (hK ⟨0, hk⟩).1
    have h0 : (⟨0, hk⟩ : Fin k).castSucc = 0 := rfl
    rwa [h0, chainDomain_zero] at h
  exact coLip_chain_certificate_of_nonempty d ϕ U₁ hne hU₁ K hK

end ChainBounds

/-! ## D06 有限指标路径与全正路径谓词 -/

section Paths

variable {I : Type}

/-- 由起点 `k₀ = i`、终点 `k_n = j` 与中间指标序列 `(k₁, …, k_{n-1})`（`n = N + 1`）
拼成的完整指标路径 `(k₀, k₁, …, k_n)`。 -/
def indexPath (i j : I) {N : ℕ} (p : Fin N → I) : Fin (N + 2) → I :=
  Fin.cons i (Fin.snoc p j)

@[simp] theorem indexPath_zero (i j : I) {N : ℕ} (p : Fin N → I) : indexPath i j p 0 = i := by
  simp [indexPath]

@[simp] theorem indexPath_last (i j : I) {N : ℕ} (p : Fin N → I) :
    indexPath i j p (Fin.last (N + 1)) = j := by
  rw [← Fin.succ_last]
  simp [indexPath]

/-- 中间指标：`k_m = p (m-1)`（`1 ≤ m ≤ n-1`）。 -/
@[simp] theorem indexPath_succ_castSucc (i j : I) {N : ℕ} (p : Fin N → I) (m : Fin N) :
    indexPath i j p m.castSucc.succ = p m := by
  simp [indexPath]

/-- 任一满足 `k₀ = i`、`k_n = j` 的完整路径都唯一地来自某个中间指标序列。 -/
theorem existsUnique_indexPath (i j : I) {N : ℕ} (k : Fin (N + 2) → I) (hi : k 0 = i)
    (hj : k (Fin.last (N + 1)) = j) : ∃! p : Fin N → I, indexPath i j p = k := by
  refine ⟨fun m => k m.castSucc.succ, ?_, ?_⟩
  · funext t
    induction t using Fin.cases with
    | zero => simp [hi]
    | succ t =>
      induction t using Fin.lastCases with
      | last => rw [Fin.succ_last, indexPath_last, hj]
      | cast m => simp
  · intro p hp
    funext m
    rw [← hp, indexPath_succ_castSucc]

/-- 路径上第 `t+1` 步（`t : Fin n`）的因子 `[M^{(t+1)}]_{k_t → k_{t+1}}`。 -/
def pathFactor {N : ℕ} (M : Fin (N + 1) → Matrix I I ENNReal) (i j : I) (p : Fin N → I)
    (t : Fin (N + 1)) : ENNReal :=
  arrowEntry (M t) (indexPath i j p t.castSucc) (indexPath i j p t.succ)

/-- 全正路径：沿该路径的所有单步矩阵条目均严格正。 -/
def IsAllPositivePath {N : ℕ} (M : Fin (N + 1) → Matrix I I ENNReal) (i j : I)
    (p : Fin N → I) : Prop :=
  ∀ t : Fin (N + 1), 0 < pathFactor M i j p t

/-- 路径含零因子：存在至少一个层级，其单步矩阵条目为 `0`。 -/
def HasZeroFactor {N : ℕ} (M : Fin (N + 1) → Matrix I I ENNReal) (i j : I)
    (p : Fin N → I) : Prop :=
  ∃ t : Fin (N + 1), pathFactor M i j p t = 0

theorem indexPath_snoc_castSucc (i j k : I) {N : ℕ} (p : Fin N → I) (u : Fin (N + 2)) :
    indexPath i j (Fin.snoc p k : Fin (N + 1) → I) u.castSucc = indexPath i k p u := by
  induction u using Fin.cases with
  | zero => simp
  | succ v =>
    rw [← Fin.succ_castSucc]
    simp [indexPath]

theorem pathFactor_snoc_castSucc {N : ℕ} (M : Fin (N + 2) → Matrix I I ENNReal)
    (i j k : I) (p : Fin N → I) (t : Fin (N + 1)) :
    pathFactor M i j (Fin.snoc p k : Fin (N + 1) → I) t.castSucc =
      pathFactor (fun m : Fin (N + 1) => M m.castSucc) i k p t := by
  simp only [pathFactor]
  rw [Fin.succ_castSucc, indexPath_snoc_castSucc, indexPath_snoc_castSucc]

theorem pathFactor_snoc_last {N : ℕ} (M : Fin (N + 2) → Matrix I I ENNReal)
    (i j k : I) (p : Fin N → I) :
    pathFactor M i j (Fin.snoc p k : Fin (N + 1) → I) (Fin.last (N + 1)) =
      arrowEntry (M (Fin.last (N + 1))) k j := by
  simp only [pathFactor]
  rw [indexPath_snoc_castSucc, indexPath_last, Fin.succ_last, indexPath_last]

/-- `n = 1` 时的展开式：唯一空中间序列的路径因子就是 `[M^{(1)}]_{i→j}`。 -/
theorem pathFactor_one (M : Fin 1 → Matrix I I ENNReal) (i j : I) (p : Fin 0 → I) :
    pathFactor M i j p 0 = arrowEntry (M 0) i j := by
  simp only [pathFactor]
  rw [show (0 : Fin 1).succ = Fin.last 1 from rfl, indexPath_last, Fin.castSucc_zero,
    indexPath_zero]

end Paths

/-! ## P13 / P14 有限非空矩阵乘积条目的零值与正值判据 -/

section PathCriteria

variable {I : Type} [Fintype I] [DecidableEq I]

/-- 路径展开：`[M^{(n)} ⋯ M^{(1)}]_{i→j} = ∑_{k₁,…,k_{n-1}} ∏_m [M^{(m)}]_{k_{m-1}→k_m}`。 -/
theorem arrowEntry_finOrderedProd_eq_sum_paths {N : ℕ} (M : Fin (N + 1) → Matrix I I ENNReal)
    (i j : I) :
    arrowEntry (finOrderedProd M) i j = ∑ p : Fin N → I, ∏ t, pathFactor M i j p t := by
  induction N generalizing j with
  | zero =>
    rw [finOrderedProd_one, Fintype.sum_unique, Fin.prod_univ_one, pathFactor_one]
  | succ N ih =>
    rw [finOrderedProd_succ, arrowEntry_mul]
    simp_rw [ih (fun m => M m.castSucc)]
    rw [← (Fin.snocEquiv (fun _ => I)).sum_comp, Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
    change _ = ∏ t, pathFactor M i j (Fin.snoc p k : Fin (N + 1) → I) t
    rw [mul_comm]
    conv_rhs => rw [Fin.prod_univ_castSucc]
    rw [pathFactor_snoc_last]
    congr 1
    exact Finset.prod_congr rfl fun t _ => (pathFactor_snoc_castSucc M i j k p t).symm

/-- **命题 2.6 (i)（零值判据）**：对 `n = N + 1 ≥ 1` 个扩展非负矩阵，
`[M^{(n)} ⋯ M^{(1)}]_{i→j} = 0` 当且仅当每条指标序列 `(k₁,…,k_{n-1})` 上都有零因子。 -/
theorem finOrderedProd_entry_eq_zero_iff {N : ℕ} (M : Fin (N + 1) → Matrix I I ENNReal)
    (i j : I) :
    arrowEntry (finOrderedProd M) i j = 0 ↔ ∀ p : Fin N → I, HasZeroFactor M i j p := by
  rw [arrowEntry_finOrderedProd_eq_sum_paths, Finset.sum_eq_zero_iff]
  simp only [mem_univ, true_implies, HasZeroFactor, Finset.prod_eq_zero_iff, true_and]

/-- **命题 2.6 (ii)（正值判据）**：`[M^{(n)} ⋯ M^{(1)}]_{i→j} > 0` 当且仅当存在至少一条
指标序列 `(k₁,…,k_{n-1})`，沿其所有单步条目严格正。 -/
theorem finOrderedProd_entry_pos_iff {N : ℕ} (M : Fin (N + 1) → Matrix I I ENNReal)
    (i j : I) :
    0 < arrowEntry (finOrderedProd M) i j ↔ ∃ p : Fin N → I, IsAllPositivePath M i j p := by
  rw [pos_iff_ne_zero, Ne, finOrderedProd_entry_eq_zero_iff]
  simp only [HasZeroFactor, IsAllPositivePath, not_forall, not_exists, pos_iff_ne_zero, Ne]

/-- 命题 2.6 (i) 的 `n = 1` 情形：唯一的空中间序列上，判据退化为 `[M^{(1)}]_{i→j} = 0`。 -/
theorem finOrderedProd_entry_eq_zero_iff_one (M : Fin 1 → Matrix I I ENNReal) (i j : I) :
    (arrowEntry (finOrderedProd M) i j = 0 ↔ ∀ p : Fin 0 → I, HasZeroFactor M i j p) ∧
      (arrowEntry (finOrderedProd M) i j = 0 ↔ arrowEntry (M 0) i j = 0) := by
  refine ⟨finOrderedProd_entry_eq_zero_iff M i j, ?_⟩
  rw [finOrderedProd_one]

/-- 命题 2.6 (ii) 的 `n = 1` 情形：判据退化为 `[M^{(1)}]_{i→j} > 0`。 -/
theorem finOrderedProd_entry_pos_iff_one (M : Fin 1 → Matrix I I ENNReal) (i j : I) :
    (0 < arrowEntry (finOrderedProd M) i j ↔ ∃ p : Fin 0 → I, IsAllPositivePath M i j p) ∧
      (0 < arrowEntry (finOrderedProd M) i j ↔ 0 < arrowEntry (M 0) i j) := by
  refine ⟨finOrderedProd_entry_pos_iff M i j, ?_⟩
  rw [finOrderedProd_one]

end PathCriteria

end LCH02
