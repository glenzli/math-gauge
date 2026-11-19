import Mathlib
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# 第 2 章 算子界（Lipschitz / co-Lipschitz 矩阵界）

本文件形式化 `source/02-operator-bounds.md` 的全部数学内容。

表示约定（与原文的对应）：
* 系数矩阵以“输入优先”方式存储：`M i j` 即原文的 `M_{i→j}`（输入 `i`，输出 `j`）。
  `toDisplay M` 给出通常的行列矩阵（第 `j` 行第 `i` 列为 `M i j`）。
* 有限算子链、矩阵序列与像域序列均以 `ℕ` 为下标、从 `0` 开始：
  Lean 的 `ϕ m`、`L m`、`imageSeq ϕ U m` 分别对应原文的 `φ_{m+1}`、`L^{(m+1)}`、`U_{m+1}`；
  长度为 `k` 的链只使用下标 `m < k` 的数据。
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open Finset

variable {X I : Type} {bot : X}

/-! ## 0. 算子复合与有限链（第 1 章幺半群结构的显式化） -/

/-- 恒等算子 `id_X ∈ X_op`。 -/
def idOp : Operator X bot := ⟨id, rfl⟩

/-- 两个算子的复合 `ψ ∘ ϕ ∈ X_op`。 -/
def opComp (ψ ϕ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ ϕ.func, by simp [ϕ.preserves_bot, ψ.preserves_bot]⟩

@[simp] theorem idOp_func : (idOp : Operator X bot).func = id := rfl

@[simp] theorem opComp_func (ψ ϕ : Operator X bot) :
    (opComp ψ ϕ).func = ψ.func ∘ ϕ.func := rfl

/-- 与第 1 章 `OperatorChain` 的对应：`ψ ∘ ϕ` 即长度 2 的链。 -/
theorem opComp_eq_operatorChain (ψ ϕ : Operator X bot) :
    opComp ψ ϕ = OperatorChain [ψ, ϕ] := by
  ext x
  rfl

/-- `dom(ψ ∘ ϕ) = {x ∈ dom ϕ | ϕ x ∈ dom ψ}`。 -/
theorem mem_dom_opComp_iff {ψ ϕ : Operator X bot} {x : X} :
    x ∈ dom (opComp ψ ϕ) ↔ x ∈ dom ϕ ∧ ϕ.func x ∈ dom ψ := by
  simp only [dom, Set.mem_setOf_eq, opComp_func, Function.comp_apply]
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro hx
    rw [hx, ψ.preserves_bot] at h
    exact h rfl
  · exact fun h => h.2

/-- 复合定义直接保证：`U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)` 蕴含 `U₁ ⊆ dom ϕ₁` 且 `U₂ = ϕ₁(U₁) ⊆ dom ϕ₂`。 -/
theorem subset_dom_of_subset_dom_opComp {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (h : U₁ ⊆ dom (opComp ϕ₂ ϕ₁)) :
    U₁ ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  refine ⟨fun x hx => (mem_dom_opComp_iff.1 (h hx)).1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_dom_opComp_iff.1 (h hx)).2

/-- 有限复合 `c_k = φ_k ∘ ⋯ ∘ φ_1`（0 起下标：`chainComp ϕ k = ϕ (k-1) ∘ ⋯ ∘ ϕ 0`），
`c_0 = id_X`。 -/
def chainComp (ϕ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => idOp
  | k + 1 => opComp (ϕ k) (chainComp ϕ k)

/-- 与第 1 章 `OperatorChain` 的对应：`c_k = OperatorChain [φ_k, …, φ_1]`。 -/
theorem chainComp_eq_operatorChain (ϕ : ℕ → Operator X bot) (k : ℕ) :
    chainComp ϕ k = OperatorChain (((List.range k).map ϕ).reverse) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.reverse_append]
    ext x
    simp only [chainComp, opComp_func, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, OperatorChain, ih]

/-- 递归像域 `U_1 = U`，`U_{m+1} = φ_m(U_m)`（0 起下标）。 -/
def imageSeq (ϕ : ℕ → Operator X bot) (U : Set X) : ℕ → Set X
  | 0 => U
  | m + 1 => operator_image (ϕ m) (imageSeq ϕ U m)

/-- 全复合的像等于逐次像：`c_m(U_1) = U_{m+1}`。 -/
theorem chainComp_image (ϕ : ℕ → Operator X bot) (U : Set X) (m : ℕ) :
    operator_image (chainComp ϕ m) U = imageSeq ϕ U m := by
  induction m with
  | zero => simp [operator_image, chainComp, imageSeq]
  | succ m ih =>
    simp only [operator_image, chainComp, imageSeq, opComp_func] at ih ⊢
    rw [Set.image_comp, ih]

/-- `m ≤ k` 时 `dom c_k ⊆ dom c_m`。 -/
theorem dom_chainComp_anti (ϕ : ℕ → Operator X bot) {m k : ℕ} (h : m ≤ k) :
    dom (chainComp ϕ k) ⊆ dom (chainComp ϕ m) := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k hmk ih =>
    intro x hx
    exact ih (mem_dom_opComp_iff.1 hx).1

/-- 由 `U_1 ⊆ dom c_k` 逐步递推：`U_m ⊆ dom φ_m`（`m = 1, …, k`；0 起下标为 `m < k`）。 -/
theorem imageSeq_subset_dom (ϕ : ℕ → Operator X bot) {U : Set X} {k : ℕ}
    (hU : U ⊆ dom (chainComp ϕ k)) {m : ℕ} (hm : m < k) :
    imageSeq ϕ U m ⊆ dom (ϕ m) := by
  rw [← chainComp_image]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ dom (chainComp ϕ (m + 1)) := dom_chainComp_anti ϕ hm (hU hx)
  exact (mem_dom_opComp_iff.1 hx').2

/-- 递推中间像域落在下一步复合的定义域内。 -/
theorem subset_dom_chainComp_of_le (ϕ : ℕ → Operator X bot) {U : Set X} {k m : ℕ}
    (hU : U ⊆ dom (chainComp ϕ k)) (hm : m ≤ k) : U ⊆ dom (chainComp ϕ m) :=
  hU.trans (dom_chainComp_anti ϕ hm)

/-! ## 1. 系数矩阵：输入优先存储、显示矩阵、乘法、单位与有序乘积 -/

/-- 非负（`ℝ≥0∞` 值）系数矩阵，输入优先存储：`M i j = M_{i→j}`。 -/
abbrev CoefMat (I : Type) := I → I → ENNReal

/-- 通常行列矩阵显示：第 `j` 行第 `i` 列为 `M_{i→j}`。 -/
def toDisplay (M : CoefMat I) : Matrix I I ENNReal := Matrix.of fun j i => M i j

@[simp] theorem toDisplay_apply (M : CoefMat I) (j i : I) : toDisplay M j i = M i j := rfl

theorem toDisplay_injective : Function.Injective (toDisplay : CoefMat I → Matrix I I ENNReal) := by
  intro M N h
  funext i j
  have := congrFun (congrFun h j) i
  simpa using this

/-- 复合乘法 `(M₂ M₁)_{i→j} = Σ_k (M₂)_{k→j} (M₁)_{i→k}`。 -/
def matComp [Fintype I] (M₂ M₁ : CoefMat I) : CoefMat I :=
  fun i j => ∑ k, M₂ k j * M₁ i k

/-- 输入优先的复合乘法与通常矩阵乘法在显示矩阵下一致。 -/
theorem toDisplay_matComp [Fintype I] (M₂ M₁ : CoefMat I) :
    toDisplay (matComp M₂ M₁) = toDisplay M₂ * toDisplay M₁ := by
  ext j i
  simp [matComp, Matrix.mul_apply]

/-- 单位矩阵 `δ_{ij}`。 -/
def idMat [DecidableEq I] : CoefMat I := fun i j => if i = j then 1 else 0

theorem toDisplay_idMat [DecidableEq I] : toDisplay (idMat : CoefMat I) = 1 := by
  ext j i
  simp [idMat, Matrix.one_apply, eq_comm]

theorem sum_idMat_mul [Fintype I] [DecidableEq I] (D : I → ENNReal) (j : I) :
    ∑ i, (idMat : CoefMat I) i j * D i = D j := by
  simp [idMat]

theorem matComp_idMat_right [Fintype I] [DecidableEq I] (M : CoefMat I) :
    matComp M idMat = M := by
  funext i j
  simp [matComp, idMat]

theorem matComp_idMat_left [Fintype I] [DecidableEq I] (M : CoefMat I) :
    matComp idMat M = M := by
  funext i j
  simp [matComp, idMat]

/-- 有序乘积：`matProd M k = M_k ⋯ M_1`（0 起下标为 `M (k-1) ⋯ M 0`），空乘积为单位矩阵。
施行顺序 `φ_1, …, φ_k` 对应左乘顺序 `L_k ⋯ L_1`。 -/
def matProd [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) : ℕ → CoefMat I
  | 0 => idMat
  | k + 1 => matComp (M k) (matProd M k)

@[simp] theorem matProd_zero [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) :
    matProd M 0 = idMat := rfl

theorem matProd_succ [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) (k : ℕ) :
    matProd M (k + 1) = matComp (M k) (matProd M k) := rfl

/-- `k = 1` 时乘积就是唯一的矩阵。 -/
theorem matProd_one [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) :
    matProd M 1 = M 0 := by
  rw [matProd_succ, matProd_zero, matComp_idMat_right]

/-- 有序乘积的显示矩阵就是通常矩阵乘积 `M_k ⋯ M_1`（列表从左到右为 `M_k, …, M_1`）。 -/
theorem toDisplay_matProd [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) (k : ℕ) :
    toDisplay (matProd M k) = (((List.range k).map fun m => toDisplay (M m)).reverse).prod := by
  induction k with
  | zero => simp [toDisplay_idMat]
  | succ k ih =>
    rw [matProd_succ, toDisplay_matComp, ih, List.range_succ, List.map_append,
      List.reverse_append]
    simp

/-- 复合求和的交换次序：`Σ_k M₂_{k→j} Σ_i M₁_{i→k} D_i = Σ_i (M₂ M₁)_{i→j} D_i`。 -/
theorem sum_matComp_mul [Fintype I] (M₂ M₁ : CoefMat I) (D : I → ENNReal) (j : I) :
    ∑ k, M₂ k j * ∑ i, M₁ i k * D i = ∑ i, matComp M₂ M₁ i j * D i := by
  simp only [matComp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-! ## 2. Lipschitz 与 co-Lipschitz 证书族 -/

/-- 受限 Lip 证书族 `𝓛(φ)|_U`：`U ⊆ dom φ`，且对所有 `x, y ∈ U`、`j ∈ I`，
`d_j(φx, φy) ≤ Σ_i L_{i→j} d_i(x, y)`。 -/
def LipSetOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (CoefMat I) :=
  {L | U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, L i j * d i x y}

/-- 全域 Lip 证书族 `𝓛(φ) = 𝓛(φ)|_{dom φ}`。 -/
def LipSet [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (CoefMat I) :=
  LipSetOn d ϕ (dom ϕ)

theorem mem_LipSet_iff [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : CoefMat I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, L i j * d i x y := by
  simp [LipSet, LipSetOn]

/-- 受限 co-Lip 证书族 `𝓚(φ)|_U`：含非空性 `U ≠ ∅`、`U ⊆ dom φ`，
且对所有 `x, y ∈ U`、`j ∈ I`，`Σ_i K_{i→j} d_i(x, y) ≤ d_j(φx, φy)`。 -/
def CoLipSetOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (CoefMat I) :=
  {K | U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, ∑ i, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)}

/-- 系数 `0` 合法：零矩阵是任意非空 `U ⊆ dom φ` 上的 co-Lip 证书。 -/
theorem zero_mem_CoLipSetOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hne : U.Nonempty) (hU : U ⊆ dom ϕ) : (0 : CoefMat I) ∈ CoLipSetOn d ϕ U :=
  ⟨hne, hU, fun x _ y _ j => by simp⟩

/-- 系数 `+∞` 合法：若某输入分量在 `U` 上处处为零距，则其 `+∞` 系数在 co-Lip 求和中贡献为零
（`0 · ∞ = 0`），故把该列改为 `+∞` 仍是 co-Lip 证书。 -/
theorem update_top_mem_CoLipSetOn [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) {U : Set X} {K : CoefMat I} (hK : K ∈ CoLipSetOn d ϕ U) (i₀ : I)
    (hzero : ∀ x ∈ U, ∀ y ∈ U, d i₀ x y = 0) :
    Function.update K i₀ (fun _ => ⊤) ∈ CoLipSetOn d ϕ U := by
  refine ⟨hK.1, hK.2.1, fun x hx y hy j => ?_⟩
  refine le_trans (le_of_eq ?_) (hK.2.2 x hx y hy j)
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h
    simp [hzero x hx y hy]
  · simp [Function.update_of_ne h]

/-! ### 单分量退化 -/

/-- **注 #h-c4369c63c86cbacf**：`I = {i}` 时 Lip 矩阵条件退化为单个标量不等式。 -/
theorem lipSetOn_single_iff [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i : I) (hI : ∀ k : I, k = i) (L : CoefMat I) :
    L ∈ LipSetOn d ϕ U ↔
      U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  have hsum : ∀ (j : I) (x y : X), ∑ k, L k j * d k x y = L i j * d i x y := by
    intro j x y
    exact Fintype.sum_eq_single i fun k hk => absurd (hI k) hk
  constructor
  · rintro ⟨hU, h⟩
    refine ⟨hU, fun x hx y hy => ?_⟩
    simpa [hsum] using h x hx y hy i
  · rintro ⟨hU, h⟩
    refine ⟨hU, fun x hx y hy j => ?_⟩
    rw [hI j, hsum]
    exact h x hx y hy

/-- **注 #h-c4369c63c86cbacf（全域形式）**。 -/
theorem lipSet_single_iff [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i : I) (hI : ∀ k : I, k = i) (L : CoefMat I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  rw [LipSet, lipSetOn_single_iff d ϕ _ i hI]
  simp

/-! ### 限制与证书族单调性 -/

/-- `U ⊆ dom φ` 时 `𝓛(φ) ⊆ 𝓛(φ)|_U`。 -/
theorem lipSet_subset_lipSetOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hU : U ⊆ dom ϕ) : LipSet d ϕ ⊆ LipSetOn d ϕ U := by
  rintro L ⟨-, h⟩
  exact ⟨hU, fun x hx y hy j => h x (hU hx) y (hU hy) j⟩

/-- `U ⊆ V ⊆ dom φ` 时 `𝓛(φ)|_V ⊆ 𝓛(φ)|_U`：评估域缩小，证书族只会扩大。 -/
theorem lipSetOn_anti [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) : LipSetOn d ϕ V ⊆ LipSetOn d ϕ U := by
  rintro L ⟨-, h⟩
  exact ⟨hUV.trans hV, fun x hx y hy j => h x (hUV hx) y (hUV hy) j⟩

/-- 逐条目下确界 `a_{ij}(U) = inf {M_{i→j} : M ∈ 𝓛(φ)|_U}`。 -/
noncomputable def lipEntryInf [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun M : CoefMat I => M i j) '' LipSetOn d ϕ U)

/-- 评估域缩小时逐条目下确界不增：`U ⊆ V ⊆ dom φ` 时 `a_{ij}(U) ≤ a_{ij}(V)`。 -/
theorem lipEntryInf_mono [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) (i j : I) :
    lipEntryInf d ϕ U i j ≤ lipEntryInf d ϕ V i j :=
  sInf_le_sInf (Set.image_mono (lipSetOn_anti d ϕ hUV hV))

/-! ### 两步复合律 -/

/-- **命题 #h-193cebcc1a7f9259（Lip 矩阵复合律）**：`U₁ ⊆ dom(φ₂ ∘ φ₁)`，`U₂ = φ₁(U₁)`，
`L₁ ∈ 𝓛(φ₁)|_{U₁}`、`L₂ ∈ 𝓛(φ₂)|_{U₂}` 蕴含 `L₂ L₁ ∈ 𝓛(φ₂ ∘ φ₁)|_{U₁}`。 -/
theorem lip_comp [Fintype I] (d : I → X → X → ENNReal) {ϕ₁ ϕ₂ : Operator X bot}
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp ϕ₂ ϕ₁)) {L₁ L₂ : CoefMat I}
    (hL₁ : L₁ ∈ LipSetOn d ϕ₁ U₁) (hL₂ : L₂ ∈ LipSetOn d ϕ₂ (operator_image ϕ₁ U₁)) :
    matComp L₂ L₁ ∈ LipSetOn d (opComp ϕ₂ ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hx' : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc d j ((opComp ϕ₂ ϕ₁).func x) ((opComp ϕ₂ ϕ₁).func y)
      ≤ ∑ k, L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := hL₂.2 _ hx' _ hy' j
    _ ≤ ∑ k, L₂ k j * ∑ i, L₁ i k * d i x y := by
        gcongr with k
        exact hL₁.2 x hx y hy k
    _ = ∑ i, matComp L₂ L₁ i j * d i x y := sum_matComp_mul L₂ L₁ _ j

/-- **注 #h-88784dcbfff0ea66（co-Lip 通道退化的点对判据）**。 -/
theorem coLip_entry_eq_zero_of_pair [Fintype I] (d : I → X → X → ENNReal) {ϕ : Operator X bot}
    {i j : I} {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    (hout : d j (ϕ.func x) (ϕ.func y) = 0) (hin : 0 < d i x y) :
    ∀ K ∈ CoLipSetOn d ϕ (dom ϕ), K i j = 0 := by
  intro K hK
  have h1 : ∑ k, K k j * d k x y ≤ 0 := hout ▸ hK.2.2 x hx y hy j
  have h2 : K i j * d i x y ≤ ∑ k, K k j * d k x y :=
    Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h3 : K i j * d i x y = 0 := le_antisymm (h2.trans h1) (zero_le _)
  rcases mul_eq_zero.1 h3 with h | h
  · exact h
  · exact absurd h hin.ne'

/-- **命题 #h-0f256e6f1d38a612（co-Lip 矩阵复合律）**：同一实际像域设定下，
`K₁ ∈ 𝓚(φ₁)|_{U₁}`、`K₂ ∈ 𝓚(φ₂)|_{U₂}` 蕴含 `K₂ K₁ ∈ 𝓚(φ₂ ∘ φ₁)|_{U₁}`（含 `U₁ ≠ ∅`）。 -/
theorem coLip_comp [Fintype I] (d : I → X → X → ENNReal) {ϕ₁ ϕ₂ : Operator X bot}
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp ϕ₂ ϕ₁)) {K₁ K₂ : CoefMat I}
    (hK₁ : K₁ ∈ CoLipSetOn d ϕ₁ U₁) (hK₂ : K₂ ∈ CoLipSetOn d ϕ₂ (operator_image ϕ₁ U₁)) :
    matComp K₂ K₁ ∈ CoLipSetOn d (opComp ϕ₂ ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hx' : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc ∑ i, matComp K₂ K₁ i j * d i x y
      = ∑ k, K₂ k j * ∑ i, K₁ i k * d i x y := (sum_matComp_mul K₂ K₁ _ j).symm
    _ ≤ ∑ k, K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
        gcongr with k
        exact hK₁.2.2 x hx y hy k
    _ ≤ d j ((opComp ϕ₂ ϕ₁).func x) ((opComp ϕ₂ ϕ₁).func y) := hK₂.2.2 _ hx' _ hy' j


/-! ### 两个算子的点对像距扰动界 -/

/-- 扰动核心：`d_j(φ_a z, φ_b z) ≤ δ_j` 蕴含 `d_j(φ_b x, φ_b y) ≤ d_j(φ_a x, φ_a y) + 2 δ_j`。 -/
theorem perturb_core {d : I → X → X → ENNReal} (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕa ϕb : Operator X bot} {U : Set X} {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕa.func z) (ϕb.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕb.func x) (ϕb.func y) ≤ d j (ϕa.func x) (ϕa.func y) + 2 * δ j := by
  calc d j (ϕb.func x) (ϕb.func y)
      ≤ d j (ϕb.func x) (ϕa.func x) + d j (ϕa.func x) (ϕb.func y) := (hd j).triangle _ _ _
    _ ≤ d j (ϕb.func x) (ϕa.func x) +
          (d j (ϕa.func x) (ϕa.func y) + d j (ϕa.func y) (ϕb.func y)) := by
        gcongr
        exact (hd j).triangle _ _ _
    _ ≤ δ j + (d j (ϕa.func x) (ϕa.func y) + δ j) := by
        gcongr
        · rw [(hd j).symm]
          exact hδ x hx j
        · exact hδ y hy j
    _ = d j (ϕa.func x) (ϕa.func y) + 2 * δ j := by ring

/-- 扰动前提的对称形式 `d_j(φ₂ z, φ₁ z) ≤ δ_j`。 -/
theorem perturb_symm {d : I → X → X → ENNReal} (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕ₁ ϕ₂ : Operator X bot} {U : Set X} {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j) :
    ∀ z ∈ U, ∀ j, d j (ϕ₂.func z) (ϕ₁.func z) ≤ δ j := by
  intro z hz j
  rw [(hd j).symm]
  exact hδ z hz j

/-- 在 `ℝ≥0∞` 中 `2 δ = δ + δ`。 -/
theorem two_mul_eq_add_self (δ : ENNReal) : 2 * δ = δ + δ := two_mul δ

/-- **命题 #h-b959b42f25710105 (i)，第一式（正向点对像距扰动）**：
`U ⊆ dom(φ₁, φ₂)`，`d_j(φ₁ z, φ₂ z) ≤ δ_j`（`z ∈ U`）蕴含
`d_j(φ₂ x, φ₂ y) ≤ d_j(φ₁ x, φ₁ y) + 2 δ_j`（`= … + δ_j + δ_j`）。 -/
theorem perturb_forward {d : I → X → X → ENNReal} (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕ₁ ϕ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ₁ ∩ dom ϕ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j ∧
      d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
  intro x hx y hy j
  have h := perturb_core hd hδ hx hy j
  refine ⟨h, ?_⟩
  rwa [two_mul, ← add_assoc] at h

/-- **命题 #h-b959b42f25710105 (i)，第二式（反向点对像距扰动）**：
同一前提下 `d_j(φ₁ x, φ₁ y) ≤ d_j(φ₂ x, φ₂ y) + 2 δ_j`。 -/
theorem perturb_backward {d : I → X → X → ENNReal} (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕ₁ ϕ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ₁ ∩ dom ϕ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j ∧
      d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := by
  intro x hx y hy j
  have h := perturb_core hd (perturb_symm hd hδ) hx hy j
  refine ⟨h, ?_⟩
  rwa [two_mul, ← add_assoc] at h

/-- **命题 #h-b959b42f25710105 (ii)（Lip 上界桥接）**。 -/
theorem perturb_lip_bridge [Fintype I] {d : I → X → X → ENNReal}
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕ₁ ϕ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ₁ ∩ dom ϕ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₁ : CoefMat I} (hL₁ : L₁ ∈ LipSetOn d ϕ₁ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ₂.func x) (ϕ₂.func y) ≤ ∑ i, L₁ i j * d i x y + 2 * δ j := by
  intro x hx y hy j
  calc d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j :=
        (perturb_forward hd hU hδ x hx y hy j).1
    _ ≤ ∑ i, L₁ i j * d i x y + 2 * δ j := by
        gcongr
        exact hL₁.2 x hx y hy j

/-- **命题 #h-b959b42f25710105 (iii)（co-Lip 下界桥接）**。 -/
theorem perturb_coLip_bridge [Fintype I] {d : I → X → X → ENNReal}
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕ₁ ϕ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ₁ ∩ dom ϕ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₁ : CoefMat I} (hK₁ : K₁ ∈ CoLipSetOn d ϕ₁ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i, K₁ i j * d i x y ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by
  intro x hx y hy j
  calc ∑ i, K₁ i j * d i x y ≤ d j (ϕ₁.func x) (ϕ₁.func y) := hK₁.2.2 x hx y hy j
    _ ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := (perturb_backward hd hU hδ x hx y hy j).1

/-- **命题 #h-b959b42f25710105（交换 φ₁, φ₂ 的 Lip 桥接）**：`φ₂` 的 Lip 证书控制 `φ₁`。 -/
theorem perturb_lip_bridge_swap [Fintype I] {d : I → X → X → ENNReal}
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕ₁ ϕ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ₁ ∩ dom ϕ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₂ : CoefMat I} (hL₂ : L₂ ∈ LipSetOn d ϕ₂ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ₁.func x) (ϕ₁.func y) ≤ ∑ i, L₂ i j * d i x y + 2 * δ j :=
  perturb_lip_bridge hd (by rwa [Set.inter_comm]) (perturb_symm hd hδ) hL₂

/-- **命题 #h-b959b42f25710105（交换 φ₁, φ₂ 的 co-Lip 桥接）**：`φ₂` 的 co-Lip 证书桥接到 `φ₁`。 -/
theorem perturb_coLip_bridge_swap [Fintype I] {d : I → X → X → ENNReal}
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {ϕ₁ ϕ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ₁ ∩ dom ϕ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₂ : CoefMat I} (hK₂ : K₂ ∈ CoLipSetOn d ϕ₂ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i, K₂ i j * d i x y ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j :=
  perturb_coLip_bridge hd (by rwa [Set.inter_comm]) (perturb_symm hd hδ) hK₂

/-! ## 3. 有限复合的局部矩阵界 -/

/-- 单位矩阵满足等式 `Σ_i I_{i→j} d_i(x,y) = d_j(x,y)`。 -/
theorem sum_idMat_dist [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal) (x y : X) (j : I) :
    ∑ i, (idMat : CoefMat I) i j * d i x y = d j x y :=
  sum_idMat_mul (fun i => d i x y) j

/-- **注 #h-11006ddd8c43bfec（Lip 部分）**：`U ⊆ dom(id_X)` 上单位矩阵是合法 Lip 矩阵
（原文要求 `U` 非空；此处不需要非空性）。 -/
theorem idMat_mem_LipSetOn [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)
    {U : Set X} (hU : U ⊆ dom (idOp : Operator X bot)) :
    (idMat : CoefMat I) ∈ LipSetOn d (idOp : Operator X bot) U :=
  ⟨hU, fun x _ y _ j => by simp only [idOp_func, id, sum_idMat_dist]; exact le_rfl⟩

/-- **注 #h-11006ddd8c43bfec（co-Lip 部分）**：非空 `U ⊆ dom(id_X)` 上单位矩阵是合法 co-Lip 矩阵。 -/
theorem idMat_mem_CoLipSetOn [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)
    {U : Set X} (hne : U.Nonempty) (hU : U ⊆ dom (idOp : Operator X bot)) :
    (idMat : CoefMat I) ∈ CoLipSetOn d (idOp : Operator X bot) U :=
  ⟨hne, hU, fun x _ y _ j => by simp only [idOp_func, id, sum_idMat_dist]; exact le_rfl⟩

/-- **注 #h-11006ddd8c43bfec**：零步复合 `c_0 = id_X`、空乘积 `= I`，对非空 `U ⊆ dom(id_X)`，
`I ∈ 𝓛(id_X)|_U ∩ 𝓚(id_X)|_U`。 -/
theorem zero_step_certificate [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)
    (ϕ : ℕ → Operator X bot) (L : ℕ → CoefMat I)
    {U : Set X} (hne : U.Nonempty) (hU : U ⊆ dom (chainComp ϕ 0)) :
    chainComp ϕ 0 = idOp ∧ matProd L 0 = idMat ∧
    matProd L 0 ∈ LipSetOn d (chainComp ϕ 0) U ∩ CoLipSetOn d (chainComp ϕ 0) U :=
  ⟨rfl, rfl, idMat_mem_LipSetOn d hU, idMat_mem_CoLipSetOn d hne hU⟩

/-- 复合链的 Lip 数据：逐步矩阵及其在各实际输入域 `U_m` 上的局部证书（不含最终复合界）。 -/
structure LipChain {X : Type} (bot : X) {I : Type} [Fintype I] (d : I → X → X → ENNReal)
    (k : ℕ) where
  /-- 算子 `φ_1, …, φ_k`（0 起下标，只用 `m < k`）。 -/
  ops : ℕ → Operator X bot
  /-- 逐步证书 `L^{(1)}, …, L^{(k)}`（0 起下标）。 -/
  mats : ℕ → CoefMat I
  /-- 起始子集 `U_1`。 -/
  start : Set X
  start_sub_dom : start ⊆ dom (chainComp ops k)
  step_mem : ∀ m < k, mats m ∈ LipSetOn d (ops m) (imageSeq ops start m)

/-- 复合链的 co-Lip 数据：逐步 co-Lip 证书（每步含非空性义务）。 -/
structure CoLipChain {X : Type} (bot : X) {I : Type} [Fintype I] (d : I → X → X → ENNReal)
    (k : ℕ) where
  ops : ℕ → Operator X bot
  mats : ℕ → CoefMat I
  start : Set X
  start_sub_dom : start ⊆ dom (chainComp ops k)
  step_mem : ∀ m < k, mats m ∈ CoLipSetOn d (ops m) (imageSeq ops start m)

/-- 有限复合的 Lip 乘积（对所有 `k`，含 `k = 0`）。 -/
theorem lip_matProd_mem [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)
    (ϕ : ℕ → Operator X bot) (L : ℕ → CoefMat I) (U : Set X) :
    ∀ k : ℕ, U ⊆ dom (chainComp ϕ k) →
      (∀ m < k, L m ∈ LipSetOn d (ϕ m) (imageSeq ϕ U m)) →
      matProd L k ∈ LipSetOn d (chainComp ϕ k) U := by
  intro k
  induction k with
  | zero => intro hU _; exact idMat_mem_LipSetOn d hU
  | succ k ih =>
    intro hU hL
    have hU' : U ⊆ dom (chainComp ϕ k) := subset_dom_chainComp_of_le ϕ hU (Nat.le_succ k)
    have hprev := ih hU' fun m hm => hL m (Nat.lt_succ_of_lt hm)
    have hstep : L k ∈ LipSetOn d (ϕ k) (operator_image (chainComp ϕ k) U) := by
      rw [chainComp_image]; exact hL k (Nat.lt_succ_self k)
    exact lip_comp d hU hprev hstep

/-- 有限复合的 co-Lip 乘积（非空起始域，对所有 `k`）。 -/
theorem coLip_matProd_mem_of_nonempty [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)
    (ϕ : ℕ → Operator X bot) (K : ℕ → CoefMat I) (U : Set X) (hne : U.Nonempty) :
    ∀ k : ℕ, U ⊆ dom (chainComp ϕ k) →
      (∀ m < k, K m ∈ CoLipSetOn d (ϕ m) (imageSeq ϕ U m)) →
      matProd K k ∈ CoLipSetOn d (chainComp ϕ k) U := by
  intro k
  induction k with
  | zero => intro hU _; exact idMat_mem_CoLipSetOn d hne hU
  | succ k ih =>
    intro hU hK
    have hU' : U ⊆ dom (chainComp ϕ k) := subset_dom_chainComp_of_le ϕ hU (Nat.le_succ k)
    have hprev := ih hU' fun m hm => hK m (Nat.lt_succ_of_lt hm)
    have hstep : K k ∈ CoLipSetOn d (ϕ k) (operator_image (chainComp ϕ k) U) := by
      rw [chainComp_image]; exact hK k (Nat.lt_succ_self k)
    exact coLip_comp d hU hprev hstep

/-- **推论 #h-c80171fa685dc795 (i)**：`k ≥ 1`，`U_{m+1} = φ_m(U_m)`，各步 `L^{(m)} ∈ 𝓛(φ_m)|_{U_m}`，
则 `L^{(k)} ⋯ L^{(1)} ∈ 𝓛(c_k)|_{U_1}`。 -/
theorem LipChain.prod_mem [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal} {k : ℕ}
    (C : LipChain bot d k) (hk : 1 ≤ k) :
    matProd C.mats k ∈ LipSetOn d (chainComp C.ops k) C.start :=
  lip_matProd_mem d C.ops C.mats C.start k C.start_sub_dom C.step_mem

/-- **推论 #h-c80171fa685dc795 (ii)**：`k ≥ 1`，各步 `K^{(m)} ∈ 𝓚(φ_m)|_{U_m}`（含非空性），
则 `K^{(k)} ⋯ K^{(1)} ∈ 𝓚(c_k)|_{U_1}`。 -/
theorem CoLipChain.prod_mem [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal} {k : ℕ}
    (C : CoLipChain bot d k) (hk : 1 ≤ k) :
    matProd C.mats k ∈ CoLipSetOn d (chainComp C.ops k) C.start := by
  have hne : C.start.Nonempty := (C.step_mem 0 hk).1
  exact coLip_matProd_mem_of_nonempty d C.ops C.mats C.start hne k C.start_sub_dom C.step_mem

/-- 链的实际像域性质（推论证明的第一步）：`U_m ⊆ dom φ_m`（`m < k`）且 `c_k(U_1) = U_{k+1}`。 -/
theorem LipChain.imageSeq_props [Fintype I] {d : I → X → X → ENNReal} {k : ℕ}
    (C : LipChain bot d k) :
    (∀ m < k, imageSeq C.ops C.start m ⊆ dom (C.ops m)) ∧
    operator_image (chainComp C.ops k) C.start = imageSeq C.ops C.start k :=
  ⟨fun _ hm => imageSeq_subset_dom C.ops C.start_sub_dom hm, chainComp_image C.ops C.start k⟩

theorem CoLipChain.imageSeq_props [Fintype I] {d : I → X → X → ENNReal} {k : ℕ}
    (C : CoLipChain bot d k) :
    (∀ m < k, imageSeq C.ops C.start m ⊆ dom (C.ops m)) ∧
    operator_image (chainComp C.ops k) C.start = imageSeq C.ops C.start k :=
  ⟨fun _ hm => imageSeq_subset_dom C.ops C.start_sub_dom hm, chainComp_image C.ops C.start k⟩

/-! ## 4. 有限矩阵乘积条目的路径展开与零/正判据 -/

/-- 完整指标路径（`n = m + 1` 层）：`k_0 = i`，`k_1, …, k_m = s`（中间指标序列，无约束），
`k_{m+1} = j`。 -/
def fullPath {m : ℕ} (i j : I) (s : Fin m → I) : Fin (m + 2) → I :=
  Fin.cons (α := fun _ => I) i (Fin.snoc (α := fun _ => I) s j)

@[simp] theorem fullPath_zero {m : ℕ} (i j : I) (s : Fin m → I) : fullPath i j s 0 = i := by
  simp [fullPath]

@[simp] theorem fullPath_last {m : ℕ} (i j : I) (s : Fin m → I) :
    fullPath i j s (Fin.last (m + 1)) = j := by
  rw [← Fin.succ_last]
  simp [fullPath]

theorem fullPath_succ_castSucc {m : ℕ} (i j : I) (s : Fin m → I) (t : Fin m) :
    fullPath i j s t.castSucc.succ = s t := by
  simp [fullPath]

/-- `n = 1`（`m = 0`）：唯一的空中间序列给出路径 `k_0 = i, k_1 = j`。 -/
theorem fullPath_length_one (i j : I) (s : Fin 0 → I) : fullPath i j s = ![i, j] := by
  funext t
  fin_cases t
  · simp
  · exact fullPath_last i j s

theorem fullPath_snoc_castSucc {m : ℕ} (i j k : I) (s : Fin m → I) (u : Fin (m + 2)) :
    fullPath i j (Fin.snoc (α := fun _ => I) s k) u.castSucc = fullPath i k s u := by
  refine Fin.cases ?_ (fun v => ?_) u
  · simp [fullPath]
  · rw [← Fin.succ_castSucc]
    simp [fullPath]

/-- 第 `t` 层（原文第 `t+1` 层）的边条目 `[M^{(t+1)}]_{k_t → k_{t+1}}`。 -/
def pathEdge (M : ℕ → CoefMat I) {m : ℕ} (i j : I) (s : Fin m → I) (t : Fin (m + 1)) : ENNReal :=
  M t (fullPath i j s t.castSucc) (fullPath i j s t.succ)

/-- 路径权重：各层条目的乘积。 -/
def pathWeight (M : ℕ → CoefMat I) {m : ℕ} (i j : I) (s : Fin m → I) : ENNReal :=
  ∏ t : Fin (m + 1), pathEdge M i j s t

/-- 路径全正：所有边 `> 0`。 -/
def PathAllPos (M : ℕ → CoefMat I) {m : ℕ} (i j : I) (s : Fin m → I) : Prop :=
  ∀ t : Fin (m + 1), 0 < pathEdge M i j s t

/-- 路径含零：某条边 `= 0`。 -/
def PathHasZero (M : ℕ → CoefMat I) {m : ℕ} (i j : I) (s : Fin m → I) : Prop :=
  ∃ t : Fin (m + 1), pathEdge M i j s t = 0

theorem pathWeight_snoc (M : ℕ → CoefMat I) {m : ℕ} (i j k : I) (s : Fin m → I) :
    pathWeight M i j (Fin.snoc (α := fun _ => I) s k) = pathWeight M i k s * M (m + 1) k j := by
  unfold pathWeight pathEdge
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun t _ => ?_
    rw [fullPath_snoc_castSucc, Fin.succ_castSucc, fullPath_snoc_castSucc]
    simp
  · rw [fullPath_snoc_castSucc, fullPath_last, Fin.succ_last, fullPath_last]
    simp

/-- 乘积条目的路径展开：`(M_{m+1} ⋯ M_1)_{i→j} = Σ_{中间序列 s} Π_t [M^{(t)}]_{k_{t-1}→k_t}`。 -/
theorem matProd_apply_eq_sum_paths [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) (m : ℕ)
    (i j : I) : matProd M (m + 1) i j = ∑ s : Fin m → I, pathWeight M i j s := by
  induction m generalizing j with
  | zero =>
    rw [matProd_one]
    simp [pathWeight, pathEdge, fullPath_length_one]
  | succ m ih =>
    rw [matProd_succ]
    simp only [matComp, ih, Finset.mul_sum]
    rw [← (Fin.snocEquiv fun _ => I).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
    have : (Fin.snocEquiv fun _ => I) (k, s) = Fin.snoc (α := fun _ => I) s k := rfl
    rw [this, pathWeight_snoc, mul_comm]

/-- **命题 #h-e4154c34e95d3c23 的代数核心 (i)**：乘积条目为零当且仅当每条完整路径含零边。 -/
theorem matProd_apply_eq_zero_iff [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) (m : ℕ)
    (i j : I) : matProd M (m + 1) i j = 0 ↔ ∀ s : Fin m → I, PathHasZero M i j s := by
  rw [matProd_apply_eq_sum_paths, Finset.sum_eq_zero_iff]
  simp [pathWeight, PathHasZero, Finset.prod_eq_zero_iff]

/-- **命题 #h-e4154c34e95d3c23 的代数核心 (ii)**：乘积条目为正当且仅当存在全正路径。 -/
theorem matProd_apply_pos_iff [Fintype I] [DecidableEq I] (M : ℕ → CoefMat I) (m : ℕ)
    (i j : I) : 0 < matProd M (m + 1) i j ↔ ∃ s : Fin m → I, PathAllPos M i j s := by
  rw [pos_iff_ne_zero, Ne, matProd_apply_eq_zero_iff]
  simp only [PathHasZero, PathAllPos, not_forall, not_exists, pos_iff_ne_zero]

/-- **命题 #h-e4154c34e95d3c23 (i)**：沿 `n = m + 1 ≥ 1` 步的算子链与实际局部 Lip 证书，
`[L^{(n)} ⋯ L^{(1)}]_{i→j} = 0` 当且仅当每个中间指标序列都有某层条目为零。 -/
theorem LipChain.prod_entry_eq_zero_iff [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}
    {m : ℕ} (C : LipChain bot d (m + 1)) (i j : I) :
    matProd C.mats (m + 1) i j = 0 ↔ ∀ s : Fin m → I, PathHasZero C.mats i j s :=
  matProd_apply_eq_zero_iff C.mats m i j

/-- **命题 #h-e4154c34e95d3c23 (ii)**：`[K^{(n)} ⋯ K^{(1)}]_{i→j} > 0` 当且仅当存在一条全正路径。 -/
theorem CoLipChain.prod_entry_pos_iff [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}
    {m : ℕ} (C : CoLipChain bot d (m + 1)) (i j : I) :
    0 < matProd C.mats (m + 1) i j ↔ ∃ s : Fin m → I, PathAllPos C.mats i j s :=
  matProd_apply_pos_iff C.mats m i j

/-- **命题 #h-e4154c34e95d3c23 (i)，`n ≥ 1` 字面形式**：中间指标序列为 `Fin (n-1) → I`。 -/
theorem LipChain.prod_entry_eq_zero_iff' [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}
    {n : ℕ} (C : LipChain bot d n) (hn : 1 ≤ n) (i j : I) :
    matProd C.mats n i j = 0 ↔ ∀ s : Fin (n - 1) → I, PathHasZero C.mats i j s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact matProd_apply_eq_zero_iff C.mats m i j

/-- **命题 #h-e4154c34e95d3c23 (ii)，`n ≥ 1` 字面形式**。 -/
theorem CoLipChain.prod_entry_pos_iff' [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}
    {n : ℕ} (C : CoLipChain bot d n) (hn : 1 ≤ n) (i j : I) :
    0 < matProd C.mats n i j ↔ ∃ s : Fin (n - 1) → I, PathAllPos C.mats i j s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact matProd_apply_pos_iff C.mats m i j

/-- `n = 1` 退化：唯一空中间序列，判据成为 `[L^{(1)}]_{i→j} = 0`。 -/
theorem pathHasZero_length_one (M : ℕ → CoefMat I) (i j : I) (s : Fin 0 → I) :
    PathHasZero M i j s ↔ M 0 i j = 0 := by
  simp [PathHasZero, pathEdge, fullPath_length_one]

/-- `n = 1` 退化：判据成为 `[K^{(1)}]_{i→j} > 0`。 -/
theorem pathAllPos_length_one (M : ℕ → CoefMat I) (i j : I) (s : Fin 0 → I) :
    PathAllPos M i j s ↔ 0 < M 0 i j := by
  simp [PathAllPos, pathEdge, fullPath_length_one]

/-- `n = 1` 时中间序列唯一。 -/
theorem intermediate_length_one_unique (s t : Fin 0 → I) : s = t := Subsingleton.elim s t

theorem LipChain.prod_entry_eq_zero_iff_one [Fintype I] [DecidableEq I]
    {d : I → X → X → ENNReal} (C : LipChain bot d 1) (i j : I) :
    matProd C.mats 1 i j = 0 ↔ C.mats 0 i j = 0 := by
  rw [matProd_one]

theorem CoLipChain.prod_entry_pos_iff_one [Fintype I] [DecidableEq I]
    {d : I → X → X → ENNReal} (C : CoLipChain bot d 1) (i j : I) :
    0 < matProd C.mats 1 i j ↔ 0 < C.mats 0 i j := by
  rw [matProd_one]


/-! ## 5. 分量通道与单通道 Lip 常数 -/

/-- 分量通道 `(i, j) ∈ I × I`：从输入分量 `d_i` 到输出分量 `d_j`。 -/
abbrev Channel (I : Type) := I × I

/-- 单通道可行标量族 `S_{ij} = {λ ∈ ℝ≥0∞ | ∀ x, y ∈ U, d_j(φx, φy) ≤ λ d_i(x, y)}`。 -/
def chanFeasible (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) :
    Set ENNReal :=
  {c | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ c * d i x y}

/-- 单通道 Lip 常数 `L̲_{i→j}(φ; U) = inf S_{ij}`（`inf ∅ = +∞`）。 -/
def chanLip (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (chanFeasible d ϕ U i j)

/-- 以通道为参数的单通道 Lip 常数。 -/
def channelLip (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (c : Channel I) :
    ENNReal :=
  chanLip d ϕ U c.1 c.2

/-- `inf ∅ = +∞` 约定。 -/
theorem chanLip_eq_top_of_empty {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {i j : I} (h : chanFeasible d ϕ U i j = ∅) : chanLip d ϕ U i j = ⊤ := by
  rw [chanLip, h, sInf_empty]

/-- 零输入距而正输出距的点对使可行族为空，从而 `L̲_{i→j}(φ; U) = +∞`。 -/
theorem chanFeasible_empty_of_pair {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {i j : I} {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : d i x y = 0)
    (hout : 0 < d j (ϕ.func x) (ϕ.func y)) :
    (∀ c : ENNReal, c ∉ chanFeasible d ϕ U i j) ∧ chanFeasible d ϕ U i j = ∅ ∧
      chanLip d ϕ U i j = ⊤ := by
  have hno : ∀ c : ENNReal, c ∉ chanFeasible d ϕ U i j := by
    intro c hc
    have h := hc x hx y hy
    rw [hin, mul_zero] at h
    exact absurd (le_antisymm h (zero_le _)) hout.ne'
  have hempty : chanFeasible d ϕ U i j = ∅ := Set.eq_empty_iff_forall_notMem.2 hno
  exact ⟨hno, hempty, chanLip_eq_top_of_empty hempty⟩

/-- 可行族向上封闭：`λ₀ ∈ S`、`λ₀ ≤ λ₁` 蕴含 `λ₁ ∈ S`。 -/
theorem chanFeasible_upward {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {i j : I} {c₀ c₁ : ENNReal} (h₀ : c₀ ∈ chanFeasible d ϕ U i j) (h : c₀ ≤ c₁) :
    c₁ ∈ chanFeasible d ϕ U i j := by
  intro x hx y hy
  calc d j (ϕ.func x) (ϕ.func y) ≤ c₀ * d i x y := h₀ x hx y hy
    _ ≤ c₁ * d i x y := by gcongr

/-- 下确界以上的每个常数（允许 `λ = +∞`）都可行；特别地在 `0 < a < +∞` 语境中成立。 -/
theorem mem_chanFeasible_of_chanLip_lt {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {i j : I} {c : ENNReal} (h : chanLip d ϕ U i j < c) :
    c ∈ chanFeasible d ϕ U i j := by
  obtain ⟨c₀, hc₀, hlt⟩ := sInf_lt_iff.1 h
  exact chanFeasible_upward hc₀ hlt.le

/-- 原文语境形式：`0 < a < +∞` 时任意 `λ > a`（含 `λ = +∞`）属于 `S`。 -/
theorem mem_chanFeasible_of_gt_of_pos_finite {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {i j : I} (h0 : 0 < chanLip d ϕ U i j) (htop : chanLip d ϕ U i j < ⊤)
    {c : ENNReal} (h : chanLip d ϕ U i j < c) : c ∈ chanFeasible d ϕ U i j :=
  mem_chanFeasible_of_chanLip_lt h

/-- 正有限下确界可被取到：`0 < a < +∞` 时 `a ∈ S`，即完整点对标量界成立。 -/
theorem chanLip_mem_of_pos_of_lt_top {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {i j : I} (h0 : 0 < chanLip d ϕ U i j) (htop : chanLip d ϕ U i j < ⊤) :
    chanLip d ϕ U i j ∈ chanFeasible d ϕ U i j := by
  intro x hx y hy
  have hS : ∀ c, chanLip d ϕ U i j < c →
      d j (ϕ.func x) (ϕ.func y) ≤ c * d i x y :=
    fun c hc => mem_chanFeasible_of_chanLip_lt hc x hx y hy
  by_cases hB0 : d i x y = 0
  · have h := hS ⊤ htop
    rw [hB0, mul_zero] at h ⊢
    exact h
  by_cases hBtop : d i x y = ⊤
  · rw [hBtop, ENNReal.mul_top h0.ne']
    exact le_top
  by_contra hlt
  push Not at hlt
  have h1 : chanLip d ϕ U i j < d j (ϕ.func x) (ϕ.func y) / d i x y :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).2 hlt
  obtain ⟨c, hac, hcA⟩ := exists_between h1
  have h2 : c * d i x y < d j (ϕ.func x) (ϕ.func y) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).1 hcA
  exact absurd (hS c hac) (not_le.2 h2)

/-- 正有限下确界的完整点对标量界形式。 -/
theorem chanLip_bound_of_pos_of_lt_top {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {i j : I} (h0 : 0 < chanLip d ϕ U i j) (htop : chanLip d ϕ U i j < ⊤) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ chanLip d ϕ U i j * d i x y :=
  chanLip_mem_of_pos_of_lt_top h0 htop

/-- 零下确界：任意有限正数 `0 < λ < +∞` 都是标量证书。 -/
theorem mem_chanFeasible_of_chanLip_eq_zero {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {i j : I} (h : chanLip d ϕ U i j = 0) {c : ENNReal} (hc0 : 0 < c)
    (hctop : c < ⊤) : c ∈ chanFeasible d ϕ U i j :=
  mem_chanFeasible_of_chanLip_lt (h ▸ hc0)

/-- 下确界有限当且仅当存在有限可行常数。 -/
theorem chanLip_lt_top_iff {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {i j : I} :
    chanLip d ϕ U i j < ⊤ ↔
      ∃ c : ENNReal, c < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ c * d i x y := by
  rw [chanLip, sInf_lt_iff]
  constructor
  · rintro ⟨c, hc, hlt⟩
    exact ⟨c, hlt, hc⟩
  · rintro ⟨c, hlt, hc⟩
    exact ⟨c, hc, hlt⟩

/-- 下确界有限当且仅当存在有限（`ℝ≥0`）常数 `λ` 使单分量上界成立。 -/
theorem chanLip_lt_top_iff_nnreal {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {i j : I} :
    chanLip d ϕ U i j < ⊤ ↔
      ∃ c : NNReal, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ (c : ENNReal) * d i x y := by
  rw [chanLip_lt_top_iff]
  constructor
  · rintro ⟨c, hlt, hc⟩
    refine ⟨c.toNNReal, ?_⟩
    rwa [ENNReal.coe_toNNReal hlt.ne]
  · rintro ⟨c, hc⟩
    exact ⟨c, ENNReal.coe_lt_top, hc⟩

/-- 单通道常数与矩阵条目是不同对象；二者的唯一一般联系：若合法证书 `L` 的第 `j` 行
仅在输入 `i` 处可能非零，则 `L_{i→j}` 是可行标量，故 `L̲_{i→j}(φ; U) ≤ L_{i→j}`。 -/
theorem chanLip_le_of_rowSparse [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {L : CoefMat I} (hL : L ∈ LipSetOn d ϕ U) {i j : I}
    (hrow : ∀ k, k ≠ i → L k j = 0) : chanLip d ϕ U i j ≤ L i j := by
  refine sInf_le ?_
  intro x hx y hy
  have hsum : ∑ k, L k j * d k x y = L i j * d i x y :=
    Fintype.sum_eq_single i fun k hk => by rw [hrow k hk, zero_mul]
  exact hsum ▸ hL.2 x hx y hy j

/-! ### 反例：零下确界未必由 `0` 实现 -/

/-- 离散 `{0, +∞}` 值距离。 -/
def discreteTopDist {Y : Type} [DecidableEq Y] (x y : Y) : ENNReal := if x = y then 0 else ⊤

/-- `Fin 3`（吸收元 `0`）上的离散 `{0, +∞}` 距离是扩展伪度量（满足公理 (i)–(iv) 与非吸收部分非空）。 -/
theorem discreteTopDist_extendedPseudoMetric :
    ExtendedPseudoMetric (Fin 3) 0 (discreteTopDist (Y := Fin 3)) where
  nonabsorbing := ⟨1, by decide⟩
  dist_self x := by simp [discreteTopDist]
  symm x y := by
    by_cases h : x = y
    · subst h; rfl
    · simp [discreteTopDist, h, Ne.symm h]
  triangle x y z := by
    unfold discreteTopDist
    by_cases hxz : x = z
    · simp [hxz]
    · by_cases hxy : x = y
      · subst hxy; simp [hxz]
      · simp [hxy]
  isolate_bot x hx := by simp [discreteTopDist, hx]

/-- 反例的单分量规范族（`I = Unit`）。 -/
def cexDist : Unit → Fin 3 → Fin 3 → ENNReal := fun _ => discreteTopDist

/-- 反例的评估域 `U = {1, 2}`。 -/
def cexU : Set (Fin 3) := {1, 2}

theorem cex_chanLip_eq_zero :
    chanLip cexDist (idOp : Operator (Fin 3) 0) cexU () () = 0 := by
  have hmem : ∀ c : ENNReal, 0 < c → c ∈ chanFeasible cexDist (idOp : Operator (Fin 3) 0) cexU () () := by
    intro c hc x _ y _
    simp only [cexDist, idOp_func, id]
    unfold discreteTopDist
    by_cases h : x = y
    · simp [h]
    · simp [h, ENNReal.mul_top hc.ne']
  refine le_antisymm ?_ (zero_le _)
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  exact sInf_le (hmem c hc)

theorem cex_zero_not_mem :
    (0 : ENNReal) ∉ chanFeasible cexDist (idOp : Operator (Fin 3) 0) cexU () () := by
  intro h
  have := h 1 (by simp [cexU]) 2 (by simp [cexU])
  simp [cexDist, discreteTopDist] at this

/-- **反例（零下确界未必由 `0` 实现）**：存在合法扩展规范空间、合法算子 `φ` 与非空合法
`U ⊆ dom φ`，使 `L̲_{i→j}(φ; U) = 0` 而 `λ = 0` 不满足相应标量上界。 -/
theorem chanLip_zero_not_attained :
    ∃ (X : Type) (bot : X) (I : Type) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧ chanLip d ϕ U i j = 0 ∧ (0 : ENNReal) ∉ chanFeasible d ϕ U i j := by
  refine ⟨Fin 3, 0, Unit, inferInstance, inferInstance, cexDist,
    fun _ => discreteTopDist_extendedPseudoMetric, idOp, cexU, (), (), ⟨1, by simp [cexU]⟩,
    ?_, cex_chanLip_eq_zero, cex_zero_not_mem⟩
  intro x hx
  simp only [cexU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> simp [dom, idOp]

/-! ## 6. 矩阵证书的通道结构：零系数、行/列解耦、对角 -/

/-- 单行稀疏 `Row(L, i, j)`：第 `j` 行除输入位置 `i` 外全为零（`∀ k ≠ i, L_{k→j} = 0`）。 -/
def RowSparse (L : CoefMat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0

/-- 矩阵第 `j` 行至多一项非零：`∃ i, Row(L, i, j)`。 -/
def RowSingle (L : CoefMat I) (j : I) : Prop := ∃ i, RowSparse L i j

/-- 单列稀疏 `Col(L, i, j)`：第 `i` 列除输出位置 `j` 外全为零（`∀ k ≠ j, L_{i→k} = 0`）。 -/
def ColSparse (L : CoefMat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0

/-- 矩阵第 `i` 列至多一项非零：`∃ j, Col(L, i, j)`。 -/
def ColSingle (L : CoefMat I) (i : I) : Prop := ∃ j, ColSparse L i j

/-- 对角：所有非对角项为零。 -/
def IsDiagonal (L : CoefMat I) : Prop := ∀ i j, i ≠ j → L i j = 0

/-- 行解耦：存在 `L ∈ 𝓛(φ)|_U` 使第 `j` 行至多一项非零。 -/
def RowDecoupled [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (j : I) : Prop :=
  ∃ L ∈ LipSetOn d ϕ U, RowSingle L j

/-- 列解耦：存在 `L ∈ 𝓛(φ)|_U` 使第 `i` 列至多一项非零。 -/
def ColDecoupled [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (i : I) : Prop :=
  ∃ L ∈ LipSetOn d ϕ U, ColSingle L i

/-- 完全解耦体系：给定的上界证书为对角矩阵。 -/
def FullyDecoupledCert [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : CoefMat I) : Prop :=
  L ∈ LipSetOn d ϕ U ∧ IsDiagonal L

/-- 行列方向：`Row(L, i, j)` 即显示矩阵第 `j` 行除第 `i` 列外为零。 -/
theorem rowSparse_iff_display (L : CoefMat I) (i j : I) :
    RowSparse L i j ↔ ∀ k, k ≠ i → toDisplay L j k = 0 := Iff.rfl

/-- 行列方向：`Col(L, i, j)` 即显示矩阵第 `i` 列除第 `j` 行外为零。 -/
theorem colSparse_iff_display (L : CoefMat I) (i j : I) :
    ColSparse L i j ↔ ∀ k, k ≠ j → toDisplay L k i = 0 := Iff.rfl

/-- 对角性与显示矩阵对角性一致。 -/
theorem isDiagonal_iff_display (L : CoefMat I) : IsDiagonal L ↔ (toDisplay L).IsDiag := by
  constructor
  · intro h j i hji
    exact h i j (Ne.symm hji)
  · intro h i j hij
    exact h (Ne.symm hij)

/-- “第 `j` 行至多有一项非零”与 `∃ i, Row(L, i, j)` 等价（`I` 非空）。 -/
theorem rowSingle_iff_atMostOne [Nonempty I] (L : CoefMat I) (j : I) :
    RowSingle L j ↔ ∀ k k', L k j ≠ 0 → L k' j ≠ 0 → k = k' := by
  constructor
  · rintro ⟨i, hi⟩ k k' hk hk'
    have h1 : k = i := by by_contra h; exact hk (hi k h)
    have h2 : k' = i := by by_contra h; exact hk' (hi k' h)
    rw [h1, h2]
  · intro h
    by_cases hex : ∃ k, L k j ≠ 0
    · obtain ⟨k, hk⟩ := hex
      refine ⟨k, fun k' hk' => ?_⟩
      by_contra hne
      exact hk' (h k' k hne hk)
    · push Not at hex
      exact ⟨Classical.arbitrary I, fun k _ => hex k⟩

/-- “第 `i` 列至多有一项非零”与 `∃ j, Col(L, i, j)` 等价（`I` 非空）。 -/
theorem colSingle_iff_atMostOne [Nonempty I] (L : CoefMat I) (i : I) :
    ColSingle L i ↔ ∀ k k', L i k ≠ 0 → L i k' ≠ 0 → k = k' := by
  constructor
  · rintro ⟨j, hj⟩ k k' hk hk'
    have h1 : k = j := by by_contra h; exact hk (hj k h)
    have h2 : k' = j := by by_contra h; exact hk' (hj k' h)
    rw [h1, h2]
  · intro h
    by_cases hex : ∃ k, L i k ≠ 0
    · obtain ⟨k, hk⟩ := hex
      refine ⟨k, fun k' hk' => ?_⟩
      by_contra hne
      exact hk' (h k' k hne hk)
    · push Not at hex
      exact ⟨Classical.arbitrary I, fun k _ => hex k⟩

/-- 零系数移除求和项：`L_{i→j} = 0` 时 `L_{i→j} d_i(x,y) = 0`（允许 `d_i = +∞`），
且输出求和可删去该输入项。 -/
theorem zero_coef_term [Fintype I] [DecidableEq I] (L : CoefMat I) {i j : I} (h : L i j = 0)
    (D : I → ENNReal) :
    L i j * D i = 0 ∧ ∑ k, L k j * D k = ∑ k ∈ Finset.univ.erase i, L k j * D k := by
  refine ⟨by rw [h, zero_mul], ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), h, zero_mul, zero_add]

/-- **(i) 通道隔离**：`L_{i→j} = 0` 时，该证书的 `d_j` 输出上界中 `d_i` 项不参与。 -/
theorem lip_bound_erase_of_zero [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}
    {ϕ : Operator X bot} {U : Set X} {L : CoefMat I} (hL : L ∈ LipSetOn d ϕ U) {i j : I}
    (h : L i j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      L i j * d i x y = 0 ∧
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  intro x hx y hy
  obtain ⟨h1, h2⟩ := zero_coef_term L h (fun k => d k x y)
  exact ⟨h1, h2 ▸ hL.2 x hx y hy j⟩

/-- **(ii) 行解耦的化简**：`L` 合法且 `∀ k ≠ i, L_{k→j} = 0`（`i` 不必等于 `j`），
则 `d_j(φx, φy) ≤ L_{i→j} d_i(x, y)`。 -/
theorem rowSparse_bound [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {L : CoefMat I} (hL : L ∈ LipSetOn d ϕ U) {i j : I} (hrow : RowSparse L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have hsum : ∑ k, L k j * d k x y = L i j * d i x y :=
    Fintype.sum_eq_single i fun k hk => by rw [hrow k hk, zero_mul]
  exact hsum ▸ hL.2 x hx y hy j

/-- 行解耦（存在形式）给出单输入分量上界。 -/
theorem RowDecoupled.bound [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {j : I} (h : RowDecoupled d ϕ U j) :
    ∃ L ∈ LipSetOn d ϕ U, ∃ i, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  obtain ⟨L, hL, i, hi⟩ := h
  exact ⟨L, hL, i, rowSparse_bound hL hi⟩

/-- **(iii) 列解耦的贡献范围**：所选 `L` 的第 `i` 列仅输出 `j` 可能非零，则对每个 `k ≠ j`，
`L_{i→k} d_i(x, y) = 0`，从而输出 `k` 的上界可删去输入 `i`。 -/
theorem colSparse_contribution [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}
    {ϕ : Operator X bot} {U : Set X} {L : CoefMat I} (hL : L ∈ LipSetOn d ϕ U) {i j : I}
    (hcol : ColSparse L i j) :
    ∀ k, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      L i k * d i x y = 0 ∧
      d k (ϕ.func x) (ϕ.func y) ≤ ∑ l ∈ Finset.univ.erase i, L l k * d l x y :=
  fun k hk => lip_bound_erase_of_zero hL (hcol k hk)

/-- **(iv) 完全解耦体系**：对角合法证书给出所有分量的标量上界。 -/
theorem diagonal_bound [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {L : CoefMat I} (hL : L ∈ LipSetOn d ϕ U) (hdiag : IsDiagonal L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  fun j => rowSparse_bound hL fun k hk => hdiag k j hk

/-- **引理 #h-6a98a58b5bc95360（对角输入项的标量双侧界）**：只假设 Lip 行稀疏
`∀ k ≠ j, L_{k→j} = 0`，则 `K_{j→j} d_j(x,y) ≤ d_j(φx, φy) ≤ L_{j→j} d_j(x,y)`。 -/
theorem diag_two_sided [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {L K : CoefMat I} (hL : L ∈ LipSetOn d ϕ U) (hK : K ∈ CoLipSetOn d ϕ U)
    {j : I} (hrow : ∀ k, k ≠ j → L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, rowSparse_bound hL hrow x hx y hy⟩
  calc K j j * d j x y ≤ ∑ k, K k j * d k x y :=
        Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _)
          (Finset.mem_univ j)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/-- 逐分量双侧界：对角输入项条件对所有 `j` 成立时，全部分量双侧界同时成立；
若另有 `L_{j→j}, K_{j→j} < +∞`，则双侧界的标量系数为有限（`ℝ≥0`）常数。 -/
theorem all_two_sided [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {L K : CoefMat I} (hL : L ∈ LipSetOn d ϕ U) (hK : K ∈ CoLipSetOn d ϕ U)
    (hrow : ∀ j k, k ≠ j → L k j = 0) :
    (∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y) ∧
    ((∀ j, L j j < ⊤ ∧ K j j < ⊤) →
      ∀ j : I, ∃ c C : NNReal, (c : ENNReal) = K j j ∧ (C : ENNReal) = L j j ∧
        ∀ x ∈ U, ∀ y ∈ U,
          (c : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ (C : ENNReal) * d j x y) := by
  have hall : ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
    fun j => diag_two_sided hL hK (hrow j)
  refine ⟨hall, fun hfin j => ?_⟩
  refine ⟨(K j j).toNNReal, (L j j).toNNReal, ENNReal.coe_toNNReal (hfin j).2.ne,
    ENNReal.coe_toNNReal (hfin j).1.ne, ?_⟩
  rw [ENNReal.coe_toNNReal (hfin j).2.ne, ENNReal.coe_toNNReal (hfin j).1.ne]
  exact hall j

/-! ## 7. 正 co-Lip 通道的可分辨保持 -/

/-- **(i) 正下界传递**：`K ∈ 𝓚(φ)|_U` 给出 `K_{i→j} d_i(x, y) ≤ d_j(φx, φy)`。 -/
theorem coLip_single_lower [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {K : CoefMat I} (hK : K ∈ CoLipSetOn d ϕ U) (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  calc K i j * d i x y ≤ ∑ k, K k j * d k x y :=
        Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _)
          (Finset.mem_univ i)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/-- **命题 #h-f82672ec0dd48f28 (i)**：`K_{i→j} > 0` 时 `d_i(x,y) > 0 ⟹ d_j(φx, φy) > 0`。 -/
theorem coLip_pos_preserves [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {K : CoefMat I} (hK : K ∈ CoLipSetOn d ϕ U) {i j : I} (hij : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hd
  exact lt_of_lt_of_le (ENNReal.mul_pos hij.ne' hd.ne') (coLip_single_lower hK i j x hx y hy)

/-- **命题 #h-f82672ec0dd48f28 (ii)**：全部 `K_{j→j} > 0` 时 `φ` 反射族零距关系。 -/
theorem coLip_reflects_gaugeZero [Fintype I] {d : I → X → X → ENNReal} {ϕ : Operator X bot}
    {U : Set X} {K : CoefMat I} (hK : K ∈ CoLipSetOn d ϕ U) (hdiag : ∀ j, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U, GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have := coLip_pos_preserves hK (hdiag j) x hx y hy (pos_iff_ne_zero.2 hne)
  exact this.ne' (hrel j)

end formal_oet.vol_01.ch_02_operator_bounds

end
