import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lch02_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lch02_bounds

/-!
# LCH02 · 第 2 章 · 两步复合、有限复合链与零步恒等算子

（原文：Zhe Li 著 *The Operator Evolution Theory*，CC BY 4.0；署名与改动说明见 `Main.lean`。）

对应 `source/02-operator-bounds.md` §2.1 中的

* 实际中间像域与链表示对应（`CH02-D05`）；
* 命题 2.2：两步 Lip 复合（`CH02-P04`）；命题 2.4：两步 co-Lip 复合（`CH02-P08`）；
* 推论 2.5：任意正长度链的 Lip / co-Lip 连乘界（`CH02-P09`、`CH02-P10`）；
* 注（零步复合的单位矩阵证书）：恒等算子的单位 Lip / co-Lip 矩阵（`CH02-P11`、`CH02-P12`）。

**表示约定**

* 复合 `ϕ₂ ∘ ϕ₁` 取冻结模块 `operator_space` 的幺半群乘积 `ϕ₂ * ϕ₁`
  （`(ϕ₂ * ϕ₁).func x = ϕ₂.func (ϕ₁.func x)`，左侧算子后作用）；恒等算子 `id_𝒳` 即 `1`。
* 有限族 `ϕ_1, …, ϕ_k` 取 `ϕ : ℕ → Operator X bot`，**下标从 1 开始，与正文一致**，只有
  `ϕ 1, …, ϕ k` 参与结论。复合链 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1` 记为 `chainComp ϕ k`，`c_0 = id_𝒳`。
* 中间像集 `U_m`（`m ≥ 1`）记为 `intermediateImage ϕ U₁ m`：`U_1 = U₁`，`U_{m+1} = ϕ_m(U_m)`，
  即每一步在其**实际输入域**（精确像集，而非任一上集）上取证书。
* 逐步证书 `𝐋^(m)`、`𝐊^(m)` 取 `L K : ℕ → Matrix I I ENNReal`（下标亦从 1 开始），
  连乘 `𝐋^(k) ⋯ 𝐋^(1)` 即 `orderedProd L k`。
* 与 `lch02_bounds` 相同，定理中保留正文标准语境（`I` 有限非空、`d i` 为扩展伪度量），
  证明不使用这些公理。
-/

set_option linter.unusedVariables false

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-! ### CH02-D05 · 实际中间像域与链表示对应 -/

/-- 复合在 `func` 上就是函数复合：`(ψ * ϕ).func x = ψ.func (ϕ.func x)`。 -/
theorem mul_func_apply (ψ ϕ : Operator X bot) (x : X) :
    (ψ * ϕ).func x = ψ.func (ϕ.func x) := rfl

/-- 恒等算子 `id_𝒳 = 1` 的 `func` 是恒等函数。 -/
theorem one_func_apply (x : X) : (1 : Operator X bot).func x = x := rfl

/-- 幺半群的单位元就是冻结模块中的恒等算子 `operator_identity`。 -/
theorem one_eq_operator_identity : (1 : Operator X bot) = operator_identity := rfl

/-- 像集 `ϕ(U)`（冻结模块 `operator_image`）就是 `ϕ.func '' U`。 -/
theorem operator_image_eq (ϕ : Operator X bot) (U : Set X) :
    operator_image ϕ U = ϕ.func '' U := rfl

/-- `x ∈ U` 蕴含 `ϕ x ∈ ϕ(U)`。 -/
theorem mem_operator_image_of_mem {ϕ : Operator X bot} {U : Set X} {x : X} (hx : x ∈ U) :
    ϕ.func x ∈ operator_image ϕ U := ⟨x, hx, rfl⟩

/--
OET anchor: h-c80171fa685dc795 （CH02-D05）
**有限复合链**：`chainComp ϕ k = ϕ_k ∘ ⋯ ∘ ϕ_1`，`k = 0` 时取 `c_0 = id_𝒳`；
递推 `c_{k+1} = ϕ_{k+1} ∘ c_k`。
-/
def chainComp (ϕ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => 1
  | k + 1 => ϕ (k + 1) * chainComp ϕ k

section chainComp

variable (ϕ : ℕ → Operator X bot)

@[simp] theorem chainComp_zero : chainComp ϕ 0 = 1 := rfl

theorem chainComp_succ (k : ℕ) : chainComp ϕ (k + 1) = ϕ (k + 1) * chainComp ϕ k := rfl

/-- 单步复合链就是该算子本身。 -/
@[simp] theorem chainComp_one : chainComp ϕ 1 = ϕ 1 := by
  simp [chainComp]

/--
链表示：`c_k` 对应列表 `[ϕ_k, …, ϕ_1]`（表头最后作用）；`chainList ϕ k` 即该列表。
这与冻结模块 `OperatorChain`（`ϕ :: tail ↦ ϕ ∘ OperatorChain tail`）及幺半群 `List.prod` 的次序一致。
-/
def chainList (k : ℕ) : List (Operator X bot) :=
  (List.range k).reverse.map fun m => ϕ (m + 1)

theorem chainList_succ (k : ℕ) : chainList ϕ (k + 1) = ϕ (k + 1) :: chainList ϕ k := by
  simp [chainList, List.range_succ]

/-- `c_k` 是列表 `[ϕ_k, …, ϕ_1]` 在算子幺半群中的乘积。 -/
theorem chainComp_eq_list_prod (k : ℕ) : chainComp ϕ k = (chainList ϕ k).prod := by
  induction k with
  | zero => simp [chainList]
  | succ k ih => rw [chainList_succ, List.prod_cons, chainComp_succ, ih]

/-- `c_k` 与冻结模块中的 `OperatorChain [ϕ_k, …, ϕ_1]` 一致。 -/
theorem chainComp_eq_operatorChain (k : ℕ) :
    chainComp ϕ k = OperatorChain (chainList ϕ k) := by
  rw [operator_chain_eq_prod, chainComp_eq_list_prod]

end chainComp

/-- 复合的定义域落在右因子的定义域内（`ϕ(⊥) = ⊥`）。 -/
theorem dom_mul_subset_dom_right (ψ ϕ : Operator X bot) : dom (ψ * ϕ) ⊆ dom ϕ := by
  intro x hx hx'
  apply hx
  show ψ.func (ϕ.func x) = bot
  rw [hx', ψ.preserves_bot]

/-- `x ∈ dom (ψ ∘ ϕ)` 当且仅当 `ϕ x ∈ dom ψ`。 -/
theorem mem_dom_mul_iff (ψ ϕ : Operator X bot) (x : X) : x ∈ dom (ψ * ϕ) ↔ ϕ.func x ∈ dom ψ :=
  Iff.rfl

/--
OET anchor: h-193cebcc1a7f9259 （CH02-D05）
"由复合定义直接保证 `U₂ ⊆ dom(ϕ₂)`"：若 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，则像集 `U₂ = ϕ₁(U₁) ⊆ dom ϕ₂`。
-/
theorem image_subset_dom_of_subset_dom_mul {ϕ₁ ϕ₂ : Operator X bot} {U₁ : Set X}
    (h : U₁ ⊆ dom (ϕ₂ * ϕ₁)) : operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact h hx

/-- 非空域的像集非空：`U ≠ ∅ ⟹ ϕ(U) ≠ ∅`。 -/
theorem nonempty_operator_image {ϕ : Operator X bot} {U : Set X} (h : U.Nonempty) :
    (operator_image ϕ U).Nonempty :=
  h.image _

/--
OET anchor: h-0f256e6f1d38a612 （CH02-P08 的非空性）
精确中间像域的非空性：若 `𝐊⁽¹⁾ ∈ 𝒦(ϕ₁)|_{U₁}`（成员含 `U₁ ≠ ∅`），则 `U₂ = ϕ₁(U₁)` 非空，
故 `𝒦(ϕ₂)|_{U₂}` 的非空前提与 `𝒦(ϕ₁)|_{U₁}` 相容。
-/
theorem nonempty_operator_image_of_mem_coLipCertsOn [Fintype I] (d : I → X → X → ENNReal)
    {ϕ₁ : Operator X bot} {U₁ : Set X} {K₁ : Matrix I I ENNReal}
    (hK₁ : K₁ ∈ coLipCertsOn d ϕ₁ U₁) : (operator_image ϕ₁ U₁).Nonempty :=
  nonempty_operator_image hK₁.1

/-- 链的定义域随长度递减：`m ≤ k` 时 `dom(c_k) ⊆ dom(c_m)`。 -/
theorem dom_chainComp_subset (ϕ : ℕ → Operator X bot) {m k : ℕ} (h : m ≤ k) :
    dom (chainComp ϕ k) ⊆ dom (chainComp ϕ m) := by
  induction k, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k hk ih => exact (dom_mul_subset_dom_right _ _).trans ih

/--
OET anchor: h-c80171fa685dc795 （CH02-D05）
**中间像集**：给定起始定义域子集 `U₁`，递归定义 `U_1 = U₁`、`U_{m+1} = ϕ_m(U_m)`；
`intermediateImage ϕ U₁ m` 即 `U_m`（`m ≥ 1`，下标 `0` 处的值仅为占位，不参与任何结论）。
-/
def intermediateImage (ϕ : ℕ → Operator X bot) (U₁ : Set X) : ℕ → Set X
  | 0 => U₁
  | 1 => U₁
  | m + 2 => operator_image (ϕ (m + 1)) (intermediateImage ϕ U₁ (m + 1))

section intermediateImage

variable (ϕ : ℕ → Operator X bot) (U₁ : Set X)

@[simp] theorem intermediateImage_one : intermediateImage ϕ U₁ 1 = U₁ := rfl

/-- 递归式 `U_{m+1} = ϕ_m(U_m)`（`m ≥ 1`），其中 `ϕ_m(U_m)` 是冻结模块的像集 `operator_image`。 -/
theorem intermediateImage_succ {m : ℕ} (hm : 1 ≤ m) :
    intermediateImage ϕ U₁ (m + 1) = operator_image (ϕ m) (intermediateImage ϕ U₁ m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

/--
链表示对应：`U_{m+1} = c_m(U_1)`，即第 `m + 1` 步的实际输入域恰是起始域在前 `m` 步复合下的像。
-/
theorem intermediateImage_succ_eq_image_chainComp (m : ℕ) :
    intermediateImage ϕ U₁ (m + 1) = operator_image (chainComp ϕ m) U₁ := by
  induction m with
  | zero => simp [chainComp, operator_image, one_func_apply]
  | succ m ih =>
    rw [intermediateImage_succ ϕ U₁ (Nat.succ_pos m), ih]
    simp only [operator_image, Set.image_image]
    rfl

/-- 链表示对应的列表形式：`U_{m+1}` 是起始域在 `OperatorChain [ϕ_m, …, ϕ_1]` 下的像。 -/
theorem intermediateImage_succ_eq_image_operatorChain (m : ℕ) :
    intermediateImage ϕ U₁ (m + 1) = operator_image (OperatorChain (chainList ϕ m)) U₁ := by
  rw [intermediateImage_succ_eq_image_chainComp, chainComp_eq_operatorChain]

/-- 同一结论的 "`U_m = c_{m-1}(U_1)`" 形式（`m ≥ 1`）。 -/
theorem intermediateImage_eq_image_chainComp {m : ℕ} (hm : 1 ≤ m) :
    intermediateImage ϕ U₁ m = operator_image (chainComp ϕ (m - 1)) U₁ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simpa using intermediateImage_succ_eq_image_chainComp ϕ U₁ m'

/--
OET anchor: h-c80171fa685dc795 （CH02-D05）
**由 `U₁ ⊆ dom(c_k)` 逐步递推 `U_m ⊆ dom(ϕ_m)`（`m = 1, …, k`）**：
每一步的实际输入域都落在该步算子的定义域内。
-/
theorem intermediateImage_subset_dom {k : ℕ} (hU₁ : U₁ ⊆ dom (chainComp ϕ k)) {m : ℕ}
    (hm1 : 1 ≤ m) (hmk : m ≤ k) : intermediateImage ϕ U₁ m ⊆ dom (ϕ m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [intermediateImage_succ_eq_image_chainComp]
  exact image_subset_dom_of_subset_dom_mul (ϕ₁ := chainComp ϕ m') (ϕ₂ := ϕ (m' + 1))
    (hU₁.trans (dom_chainComp_subset ϕ hmk))

end intermediateImage

/-! ### CH02-P04 · 命题 2.2（Lip 矩阵复合律） -/

/--
OET anchor: h-193cebcc1a7f9259 （CH02-P04）
**命题 2.2（Lip 矩阵复合律）**：设起始定义域局部子集 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，取**精确**中间像集
`U₂ = ϕ₁(U₁)`。若 `𝐋⁽¹⁾ ∈ ℒ(ϕ₁)|_{U₁}` 且 `𝐋⁽²⁾ ∈ ℒ(ϕ₂)|_{U₂}`，
则 `𝐋⁽²⁾ · 𝐋⁽¹⁾ ∈ ℒ(ϕ₂ ∘ ϕ₁)|_{U₁}`（乘积次序：`𝐋⁽²⁾` 在左，即 `L₂ * L₁`）。
-/
theorem lip_comp [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) {ϕ₁ ϕ₂ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) {L₁ L₂ : Matrix I I ENNReal}
    (hL₁ : L₁ ∈ lipCertsOn d ϕ₁ U₁) (hL₂ : L₂ ∈ lipCertsOn d ϕ₂ (operator_image ϕ₁ U₁)) :
    L₂ * L₁ ∈ lipCertsOn d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have h2 := hL₂.2 (ϕ₁.func x) (mem_operator_image_of_mem hx) (ϕ₁.func y)
    (mem_operator_image_of_mem hy) j
  calc d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
      = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k, arrowEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := h2
    _ ≤ ∑ k, arrowEntry L₂ k j * ∑ i, arrowEntry L₁ i k * d i x y := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul' le_rfl (hL₁.2 x hx y hy k)
    _ = ∑ i, arrowEntry (L₂ * L₁) i j * d i x y :=
        (sum_arrowEntry_mul_mul L₂ L₁ j fun i => d i x y).symm

/-! ### CH02-P08 · 命题 2.4（co-Lip 矩阵复合律） -/

/--
OET anchor: h-0f256e6f1d38a612 （CH02-P08）
**命题 2.4（co-Lip 矩阵复合律）**：设起始定义域局部子集 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，取**精确**中间像集
`U₂ = ϕ₁(U₁)`。若 `𝐊⁽¹⁾ ∈ 𝒦(ϕ₁)|_{U₁}` 且 `𝐊⁽²⁾ ∈ 𝒦(ϕ₂)|_{U₂}`，
则 `𝐊⁽²⁾ · 𝐊⁽¹⁾ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}`。非空性：`U₁ ≠ ∅` 来自 `𝐊⁽¹⁾ ∈ 𝒦(ϕ₁)|_{U₁}`
（成员谓词含非空条件），结论中的非空条件由它给出。
-/
theorem coLip_comp [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) {ϕ₁ ϕ₂ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) {K₁ K₂ : Matrix I I ENNReal}
    (hK₁ : K₁ ∈ coLipCertsOn d ϕ₁ U₁) (hK₂ : K₂ ∈ coLipCertsOn d ϕ₂ (operator_image ϕ₁ U₁)) :
    K₂ * K₁ ∈ coLipCertsOn d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, fun x hx y hy j => ?_⟩
  have h2 := hK₂.2.2 (ϕ₁.func x) (mem_operator_image_of_mem hx) (ϕ₁.func y)
    (mem_operator_image_of_mem hy) j
  calc ∑ i, arrowEntry (K₂ * K₁) i j * d i x y
      = ∑ k, arrowEntry K₂ k j * ∑ i, arrowEntry K₁ i k * d i x y :=
        sum_arrowEntry_mul_mul K₂ K₁ j fun i => d i x y
    _ ≤ ∑ k, arrowEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul' le_rfl (hK₁.2.2 x hx y hy k)
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := h2
    _ = d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) := rfl

/-! ### CH02-P09 / CH02-P10 · 推论 2.5（有限复合的局部矩阵界） -/

/--
OET anchor: h-c80171fa685dc795 （CH02-P09）
**推论 2.5 (i)（Lip 上界）**：设 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`（`k ≥ 1`），`U₁ ⊆ dom(c_k)`，
`U_1 = U₁`、`U_{m+1} = ϕ_m(U_m)`。若各单步具有合法矩阵
`𝐋⁽ᵐ⁾ ∈ ℒ(ϕ_m)|_{U_m}`（`m = 1, …, k`），则 `𝐋⁽ᵏ⁾ ⋯ 𝐋⁽¹⁾ ∈ ℒ(c_k)|_{U₁}`。
对 `k` 做归纳（以 `k = 1` 为基，归纳步用命题 2.2）。
-/
theorem chain_lip [Fintype I] [Nonempty I] [DecidableEq I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : ℕ → Operator X bot)
    (L : ℕ → Matrix I I ENNReal) {k : ℕ} (hk : 1 ≤ k) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainComp ϕ k))
    (hL : ∀ m, 1 ≤ m → m ≤ k → L m ∈ lipCertsOn d (ϕ m) (intermediateImage ϕ U₁ m)) :
    orderedProd L k ∈ lipCertsOn d (chainComp ϕ k) U₁ := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 := hL 1 le_rfl le_rfl
    rw [intermediateImage_one] at h1
    simpa using h1
  | succ k hk ih =>
    have hU : U₁ ⊆ dom (chainComp ϕ k) := by
      rw [chainComp_succ] at hU₁
      exact hU₁.trans (dom_mul_subset_dom_right _ _)
    have ih' := ih hU (fun m h1 h2 => hL m h1 (Nat.le_succ_of_le h2))
    have h2 := hL (k + 1) (Nat.succ_pos k) le_rfl
    rw [intermediateImage_succ_eq_image_chainComp] at h2
    rw [chainComp_succ] at hU₁ ⊢
    rw [orderedProd_succ]
    exact lip_comp d hd (ϕ₁ := chainComp ϕ k) (ϕ₂ := ϕ (k + 1)) hU₁ ih' h2

/--
OET anchor: h-c80171fa685dc795 （CH02-P10）
**推论 2.5 (ii)（co-Lip 下界）**：设 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`（`k ≥ 1`），`U₁ ⊆ dom(c_k)`，
`U_1 = U₁`、`U_{m+1} = ϕ_m(U_m)`。若各单步具有合法矩阵
`𝐊⁽ᵐ⁾ ∈ 𝒦(ϕ_m)|_{U_m}`（`m = 1, …, k`），则 `𝐊⁽ᵏ⁾ ⋯ 𝐊⁽¹⁾ ∈ 𝒦(c_k)|_{U₁}`。
对 `k` 做归纳（以 `k = 1` 为基，归纳步用命题 2.4；`U₁ ≠ ∅` 由 `𝐊⁽¹⁾ ∈ 𝒦(ϕ_1)|_{U₁}` 给出）。
-/
theorem chain_coLip [Fintype I] [Nonempty I] [DecidableEq I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : ℕ → Operator X bot)
    (K : ℕ → Matrix I I ENNReal) {k : ℕ} (hk : 1 ≤ k) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainComp ϕ k))
    (hK : ∀ m, 1 ≤ m → m ≤ k → K m ∈ coLipCertsOn d (ϕ m) (intermediateImage ϕ U₁ m)) :
    orderedProd K k ∈ coLipCertsOn d (chainComp ϕ k) U₁ := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 := hK 1 le_rfl le_rfl
    rw [intermediateImage_one] at h1
    simpa using h1
  | succ k hk ih =>
    have hU : U₁ ⊆ dom (chainComp ϕ k) := by
      rw [chainComp_succ] at hU₁
      exact hU₁.trans (dom_mul_subset_dom_right _ _)
    have ih' := ih hU (fun m h1 h2 => hK m h1 (Nat.le_succ_of_le h2))
    have h2 := hK (k + 1) (Nat.succ_pos k) le_rfl
    rw [intermediateImage_succ_eq_image_chainComp] at h2
    rw [chainComp_succ] at hU₁ ⊢
    rw [orderedProd_succ]
    exact coLip_comp d hd (ϕ₁ := chainComp ϕ k) (ϕ₂ := ϕ (k + 1)) hU₁ ih' h2

/--
OET anchor: h-c80171fa685dc795 （CH02-P09 的链表示形式，CH02-D05）
推论 2.5 (i)，用冻结模块的 `OperatorChain [ϕ_k, …, ϕ_1]` 表示链 `c_k`（`chainComp_eq_operatorChain`）。
-/
theorem chain_lip_operatorChain [Fintype I] [Nonempty I] [DecidableEq I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : ℕ → Operator X bot)
    (L : ℕ → Matrix I I ENNReal) {k : ℕ} (hk : 1 ≤ k) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (OperatorChain (chainList ϕ k)))
    (hL : ∀ m, 1 ≤ m → m ≤ k → L m ∈ lipCertsOn d (ϕ m) (intermediateImage ϕ U₁ m)) :
    orderedProd L k ∈ lipCertsOn d (OperatorChain (chainList ϕ k)) U₁ := by
  rw [← chainComp_eq_operatorChain] at hU₁ ⊢
  exact chain_lip d hd ϕ L hk hU₁ hL

/--
OET anchor: h-c80171fa685dc795 （CH02-P10 的链表示形式，CH02-D05）
推论 2.5 (ii)，用冻结模块的 `OperatorChain [ϕ_k, …, ϕ_1]` 表示链 `c_k`。
-/
theorem chain_coLip_operatorChain [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : ℕ → Operator X bot) (K : ℕ → Matrix I I ENNReal) {k : ℕ} (hk : 1 ≤ k) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (OperatorChain (chainList ϕ k)))
    (hK : ∀ m, 1 ≤ m → m ≤ k → K m ∈ coLipCertsOn d (ϕ m) (intermediateImage ϕ U₁ m)) :
    orderedProd K k ∈ coLipCertsOn d (OperatorChain (chainList ϕ k)) U₁ := by
  rw [← chainComp_eq_operatorChain] at hU₁ ⊢
  exact chain_coLip d hd ϕ K hk hU₁ hK

/-! ### CH02-P11 / CH02-P12 · 零步复合的单位矩阵证书 -/

/-- 恒等算子的定义域是 `{x | x ≠ ⊥}`。 -/
theorem dom_one : dom (1 : Operator X bot) = {x | x ≠ bot} := rfl

/--
OET anchor: h-11006ddd8c43bfec （CH02-P11）
**注（零步复合的单位矩阵证书）之 Lip 部分**：对任意 `U ⊆ dom(id_𝒳)`，
单位矩阵 `𝐈 ∈ ℒ(id_𝒳)|_U`（这里不要求 `U` 非空；非空时即正文所述情形）。
-/
theorem identity_mem_lipCertsOn [Fintype I] [Nonempty I] [DecidableEq I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) {U : Set X}
    (hU : U ⊆ dom (1 : Operator X bot)) :
    (1 : Matrix I I ENNReal) ∈ lipCertsOn d (1 : Operator X bot) U := by
  refine ⟨hU, fun x hx y hy j => ?_⟩
  rw [sum_arrowEntry_one_mul j fun i => d i x y]
  exact le_rfl

/--
OET anchor: h-11006ddd8c43bfec （CH02-P12）
**注（零步复合的单位矩阵证书）之 co-Lip 部分**：对任意非空 `U ⊆ dom(id_𝒳)`，
单位矩阵 `𝐈 ∈ 𝒦(id_𝒳)|_U`。
-/
theorem identity_mem_coLipCertsOn [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X bot)) :
    (1 : Matrix I I ENNReal) ∈ coLipCertsOn d (1 : Operator X bot) U := by
  refine ⟨hne, hU, fun x hx y hy j => ?_⟩
  rw [sum_arrowEntry_one_mul j fun i => d i x y]
  exact le_rfl

/--
OET anchor: h-11006ddd8c43bfec （CH02-P11 ∧ CH02-P12，合并形式）
正文原样：对任意非空 `U ⊆ dom(id_𝒳)`，`𝐈 ∈ ℒ(id_𝒳)|_U ∩ 𝒦(id_𝒳)|_U`。
-/
theorem identity_mem_lipCertsOn_inter_coLipCertsOn [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X bot)) :
    (1 : Matrix I I ENNReal) ∈
      lipCertsOn d (1 : Operator X bot) U ∩ coLipCertsOn d (1 : Operator X bot) U :=
  ⟨identity_mem_lipCertsOn d hd hU, identity_mem_coLipCertsOn d hd hne hU⟩

/--
OET anchor: h-11006ddd8c43bfec （CH02-P11 的链形式，`k = 0`）
零步链：`c_0 = id_𝒳`，矩阵空乘积为 `𝐈`；对 `U₁ ⊆ dom(c_0)`，`𝐈 ∈ ℒ(c_0)|_{U₁}`。
-/
theorem chain_lip_zero [Fintype I] [Nonempty I] [DecidableEq I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : ℕ → Operator X bot)
    (L : ℕ → Matrix I I ENNReal) {U₁ : Set X} (hU₁ : U₁ ⊆ dom (chainComp ϕ 0)) :
    orderedProd L 0 ∈ lipCertsOn d (chainComp ϕ 0) U₁ :=
  identity_mem_lipCertsOn d hd hU₁

/--
OET anchor: h-11006ddd8c43bfec （CH02-P12 的链形式，`k = 0`）
零步链：对非空 `U₁ ⊆ dom(c_0)`，`𝐈 ∈ 𝒦(c_0)|_{U₁}`。
-/
theorem chain_coLip_zero [Fintype I] [Nonempty I] [DecidableEq I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : ℕ → Operator X bot)
    (K : ℕ → Matrix I I ENNReal) {U₁ : Set X} (hne : U₁.Nonempty)
    (hU₁ : U₁ ⊆ dom (chainComp ϕ 0)) :
    orderedProd K 0 ∈ coLipCertsOn d (chainComp ϕ 0) U₁ :=
  identity_mem_coLipCertsOn d hd hne hU₁

end formal_oet.vol_01.ch_02_operator_bounds
