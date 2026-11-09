import Mathlib
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# 第 2 章 算子界（Lipschitz 上界矩阵、co-Lipschitz 下界矩阵与有限复合）

OET anchor: h-5d30f7f93769bbd7

本文件把 `source/02-operator-bounds.md` 的全部定义、表示与命题形式化到前置模块
`formal_oet.vol_01.ch_01_foundations.{gauge_space, operator_space}` 之上。

约定（与前置模块一致）：
* 点空间 `X : Type`，吸收元 `bot : X`，分量伪度量族 `d : I → X → X → ENNReal`，
  `I` 为有限类型（`[Fintype I]`）；
* 算子 `Operator X bot`，定义域 `dom`；
* 所有系数、距离、和与积均在 `ENNReal`（即 `[0, +∞]`，`0 * ⊤ = 0`）中计算。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 0. 算子的恒等、复合与有限复合链 -/

section Operators

variable {X : Type} {bot : X}

/-- 恒等算子 `id_X ∈ X_op`。 -/
def opId : Operator X bot := ⟨id, rfl⟩

/-- 算子复合 `ψ ∘ φ`（先作用 `φ`，再作用 `ψ`）；
封闭性来自 `(ψ ∘ φ)(⊥) = ψ(⊥) = ⊥`。 -/
def opComp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp only [Function.comp_apply, φ.preserves_bot, ψ.preserves_bot]⟩

@[simp] theorem opId_func : (opId : Operator X bot).func = id := rfl

@[simp] theorem opComp_func (ψ φ : Operator X bot) :
    (opComp ψ φ).func = ψ.func ∘ φ.func := rfl

/-- `x ∈ dom φ` 即 `φ x ≠ ⊥`。 -/
theorem mem_dom_iff {φ : Operator X bot} {x : X} : x ∈ dom φ ↔ φ.func x ≠ bot := Iff.rfl

/-- 吸收元不在任何算子的定义域中。 -/
theorem bot_notMem_dom (φ : Operator X bot) : bot ∉ dom φ := fun h => h φ.preserves_bot

/-- 复合的定义域：`x ∈ dom (ψ ∘ φ)` 当且仅当 `x ∈ dom φ` 且 `φ x ∈ dom ψ`。 -/
theorem mem_dom_opComp {ψ φ : Operator X bot} {x : X} :
    x ∈ dom (opComp ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro hx
    apply h
    simp only [opComp_func, Function.comp_apply, hx, ψ.preserves_bot]
  · exact fun h => h.2

theorem dom_opId : dom (opId : Operator X bot) = {x | x ≠ bot} := rfl

/-- 有限复合 `c_k = φ_k ∘ ⋯ ∘ φ_1`，`c_0 = id_X`。
第 `m` 个算子取 `φ m`（`m = 1, …, k`），`φ 0` 不参与。 -/
def chainOp (φ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => opId
  | k + 1 => opComp (φ (k + 1)) (chainOp φ k)

@[simp] theorem chainOp_zero (φ : ℕ → Operator X bot) : chainOp φ 0 = opId := rfl

@[simp] theorem chainOp_succ (φ : ℕ → Operator X bot) (k : ℕ) :
    chainOp φ (k + 1) = opComp (φ (k + 1)) (chainOp φ k) := rfl

/-- 与前置模块 `OperatorChain`（表头为最后作用者）的对应：施行顺序 `φ_1, …, φ_k` 对应
列表 `[φ_k, …, φ_1]`。 -/
def chainList (φ : ℕ → Operator X bot) (k : ℕ) : List (Operator X bot) :=
  ((List.range k).map fun m => φ (m + 1)).reverse

theorem chainOp_eq_operatorChain (φ : ℕ → Operator X bot) (k : ℕ) :
    chainOp φ k = OperatorChain (chainList φ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : chainList φ (k + 1) = φ (k + 1) :: chainList φ k := by
      simp [chainList, List.range_succ]
    rw [this, chainOp_succ, ih]
    rfl

/-- 复合链的定义域递减：`a ≤ b` 时 `dom c_b ⊆ dom c_a`。 -/
theorem dom_chainOp_antitone (φ : ℕ → Operator X bot) {a b : ℕ} (h : a ≤ b) :
    dom (chainOp φ b) ⊆ dom (chainOp φ a) := by
  induction b, h using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ b _ ih =>
    intro x hx
    exact ih (mem_dom_opComp.1 hx).1

/-- 逐步像集（`1` 起编号）：`U_1 = U₁`，`U_{m+1} = φ_m(U_m)`；`m = 0` 处取值不使用（取 `U₁`）。 -/
def stepImg (φ : ℕ → Operator X bot) (U₁ : Set X) : ℕ → Set X
  | 0 => U₁
  | 1 => U₁
  | m + 2 => (φ (m + 1)).func '' stepImg φ U₁ (m + 1)

theorem stepImg_one (φ : ℕ → Operator X bot) (U₁ : Set X) : stepImg φ U₁ 1 = U₁ := rfl

theorem stepImg_succ (φ : ℕ → Operator X bot) (U₁ : Set X) {m : ℕ} (hm : 1 ≤ m) :
    stepImg φ U₁ (m + 1) = (φ m).func '' stepImg φ U₁ m := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rfl

/-- 全复合像等于逐次像：`U_{m+1} = c_m(U_1)`（`m ≤ k`）。 -/
theorem stepImg_eq_image_chainOp (φ : ℕ → Operator X bot) {k : ℕ} {U : ℕ → Set X}
    (hU : ∀ m, 1 ≤ m → m ≤ k → U (m + 1) = (φ m).func '' U m) :
    ∀ m, m ≤ k → U (m + 1) = (chainOp φ m).func '' U 1 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [hU (m + 1) (by omega) hm, ih (by omega), Set.image_image]
    rfl

/-- 每个实际输入域落在对应算子的定义域内：`U_1 ⊆ dom c_k` 蕴含 `U_m ⊆ dom φ_m`（`1 ≤ m ≤ k`）。 -/
theorem stepImg_subset_dom (φ : ℕ → Operator X bot) {k : ℕ} {U : ℕ → Set X}
    (hdom : U 1 ⊆ dom (chainOp φ k))
    (hU : ∀ m, 1 ≤ m → m ≤ k → U (m + 1) = (φ m).func '' U m) :
    ∀ m, 1 ≤ m → m ≤ k → U m ⊆ dom (φ m) := by
  intro m hm1 hmk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm1
  have hm : m + 1 ≤ k := hmk
  have himg := stepImg_eq_image_chainOp φ hU m (by omega)
  rw [show U (m + 1) = (chainOp φ m).func '' U 1 from by
    simpa using himg]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ dom (chainOp φ (m + 1)) := dom_chainOp_antitone φ hm (hdom hx)
  exact (mem_dom_opComp.1 hx').2

/-- 递归定义的逐步像集满足：全复合像等于逐次像 `U_{m+1} = c_m(U_1)`（对所有 `m`）。 -/
theorem stepImg_eq_image (φ : ℕ → Operator X bot) (U₁ : Set X) (m : ℕ) :
    stepImg φ U₁ (m + 1) = (chainOp φ m).func '' U₁ :=
  stepImg_eq_image_chainOp φ (k := m) (U := stepImg φ U₁)
    (fun _ hm _ => stepImg_succ φ U₁ hm) m le_rfl

/-- 递归定义的逐步像集：`U_1 ⊆ dom c_k` 时每个 `U_m ⊆ dom φ_m`（`1 ≤ m ≤ k`）。 -/
theorem stepImg_subset_dom_of_subset (φ : ℕ → Operator X bot) {k : ℕ} {U₁ : Set X}
    (hdom : U₁ ⊆ dom (chainOp φ k)) :
    ∀ m, 1 ≤ m → m ≤ k → stepImg φ U₁ m ⊆ dom (φ m) :=
  stepImg_subset_dom φ (U := stepImg φ U₁) hdom (fun _ hm _ => stepImg_succ φ U₁ hm)

/-- 任何满足递推的像集序列在 `1 ≤ m ≤ k+1` 上都等于由 `U 1` 递归定义的 `stepImg`。 -/
theorem eq_stepImg_of_rec (φ : ℕ → Operator X bot) {k : ℕ} {U : ℕ → Set X}
    (hU : ∀ m, 1 ≤ m → m ≤ k → U (m + 1) = (φ m).func '' U m) :
    ∀ m, 1 ≤ m → m ≤ k + 1 → U m = stepImg φ (U 1) m := by
  intro m hm1 hmk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm1
  rw [stepImg_eq_image, stepImg_eq_image_chainOp φ hU m (by omega)]

end Operators


/-! ## 1. 系数矩阵的输入优先存储、乘法与有序乘积 -/

section Matrices

variable {I : Type} [Fintype I]

/-- 输入优先存储的 `ENNReal` 系数矩阵：`M i j` 即条目 `M_{i→j}`
（`i` 为输入分量，`j` 为输出分量）。 -/
abbrev CoeffMat (I : Type) : Type := I → I → ENNReal

/-- 通常的行列矩阵：输出指标 `j` 标记行、输入指标 `i` 标记列，
即第 `j` 行第 `i` 列的条目为 `M_{i→j}`。 -/
def toMatrix (M : CoeffMat I) : Matrix I I ENNReal := Matrix.of fun j i => M i j

/-- 复合乘法：`(M₂ M₁)_{i→j} = ∑_{k∈I} (M₂)_{k→j} (M₁)_{i→k}`（先 `M₁` 后 `M₂`）。 -/
def mmul (M₂ M₁ : CoeffMat I) : CoeffMat I := fun i j => ∑ k, M₂ k j * M₁ i k

/-- 单位矩阵 `𝐈_{i→j} = δ_{ij}`。 -/
def idMat [DecidableEq I] : CoeffMat I := fun i j => if i = j then 1 else 0

@[simp] theorem toMatrix_apply (M : CoeffMat I) (j i : I) : toMatrix M j i = M i j := rfl

theorem toMatrix_injective : Function.Injective (toMatrix : CoeffMat I → Matrix I I ENNReal) := by
  intro M N h
  funext i j
  exact congrFun (congrFun h j) i

theorem toMatrix_surjective : Function.Surjective (toMatrix : CoeffMat I → Matrix I I ENNReal) :=
  fun A => ⟨fun i j => A j i, rfl⟩

/-- 输入优先存储与通常行列矩阵一一对应。 -/
theorem toMatrix_bijective : Function.Bijective (toMatrix : CoeffMat I → Matrix I I ENNReal) :=
  ⟨toMatrix_injective, toMatrix_surjective⟩

/-- 复合乘法对应通常的矩阵乘法：`toMatrix (M₂ M₁) = toMatrix M₂ * toMatrix M₁`。 -/
theorem toMatrix_mmul (M₂ M₁ : CoeffMat I) :
    toMatrix (mmul M₂ M₁) = toMatrix M₂ * toMatrix M₁ := by
  ext j i
  simp [toMatrix, mmul, Matrix.mul_apply]

theorem toMatrix_idMat [DecidableEq I] : toMatrix (idMat : CoeffMat I) = 1 := by
  ext j i
  simp [toMatrix, idMat, Matrix.one_apply, eq_comm]

theorem mmul_assoc (A B C : CoeffMat I) : mmul (mmul A B) C = mmul A (mmul B C) := by
  apply toMatrix_injective
  simp only [toMatrix_mmul, Matrix.mul_assoc]

theorem mmul_idMat [DecidableEq I] (A : CoeffMat I) : mmul A idMat = A := by
  apply toMatrix_injective
  simp [toMatrix_mmul, toMatrix_idMat]

theorem idMat_mmul [DecidableEq I] (A : CoeffMat I) : mmul idMat A = A := by
  apply toMatrix_injective
  simp [toMatrix_mmul, toMatrix_idMat]

/-- 有序乘积 `M_k ⋯ M_1`：`k = 0` 为单位矩阵（空乘积），
`M_{k+1} ⋯ M_1 = M_{k+1} · (M_k ⋯ M_1)`；施行顺序 `φ_1, …, φ_k` 对应 `M_k ⋯ M_1`。
第 `m` 个矩阵取 `M m`（`m = 1, …, k`），`M 0` 不参与。 -/
def orderedProd [DecidableEq I] (M : ℕ → CoeffMat I) : ℕ → CoeffMat I
  | 0 => idMat
  | k + 1 => mmul (M (k + 1)) (orderedProd M k)

@[simp] theorem orderedProd_zero [DecidableEq I] (M : ℕ → CoeffMat I) :
    orderedProd M 0 = idMat := rfl

@[simp] theorem orderedProd_succ [DecidableEq I] (M : ℕ → CoeffMat I) (k : ℕ) :
    orderedProd M (k + 1) = mmul (M (k + 1)) (orderedProd M k) := rfl

/-- `k = 1` 时乘积就是唯一的那个矩阵。 -/
theorem orderedProd_one [DecidableEq I] (M : ℕ → CoeffMat I) : orderedProd M 1 = M 1 := by
  simp [mmul_idMat]

/-- 有序乘积在行列矩阵下读作 `M_k ⋯ M_1`（列表 `[M_k, …, M_1]` 的乘积）。 -/
theorem toMatrix_orderedProd [DecidableEq I] (M : ℕ → CoeffMat I) (k : ℕ) :
    toMatrix (orderedProd M k) =
      (((List.range k).map fun m => toMatrix (M (m + 1))).reverse).prod := by
  induction k with
  | zero => simp [toMatrix_idMat]
  | succ k ih =>
    rw [orderedProd_succ, toMatrix_mmul, ih]
    simp [List.range_succ]

end Matrices


/-! ## 2. Lipschitz / co-Lipschitz 矩阵证书族 -/

section Certificates

variable {X I : Type} {bot : X} [Fintype I]

/-- OET anchor: h-af85899693cc8750
全域合法 Lipschitz 矩阵集 `𝓛(φ)`：对所有 `x y ∈ dom φ` 与 `j`，
`d_j(φ x, φ y) ≤ ∑_i L_{i→j} · d_i(x, y)`。 -/
def LipSet (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (CoeffMat I) :=
  {L | ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j, d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * d i x y}

/-- OET anchor: h-af85899693cc8750
子集受限 Lipschitz 矩阵集 `𝓛(φ)|_U`：要求 `U ⊆ dom φ`，并在 `U` 上成立同一不等式。 -/
def LipSetOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (CoeffMat I) :=
  {L | U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j, d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * d i x y}

/-- OET anchor: h-af85899693cc8750
子集受限 co-Lipschitz 矩阵集 `𝓚(φ)|_U`：包含 `U ≠ ∅`、`U ⊆ dom φ`，
且对所有 `x y ∈ U` 与 `j`，`∑_i K_{i→j} · d_i(x, y) ≤ d_j(φ x, φ y)`。 -/
def CoLipSetOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (CoeffMat I) :=
  {K | U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j, ∑ i, K i j * d i x y ≤ d j (φ.func x) (φ.func y)}

variable (d : I → X → X → ENNReal) (φ : Operator X bot)

/-- 全域集即 `U = dom φ` 时的受限集。 -/
theorem lipSetOn_dom : LipSetOn d φ (dom φ) = LipSet d φ := by
  ext L
  exact ⟨fun h x hx y hy j => h.2 x hx y hy j, fun h => ⟨subset_rfl, h⟩⟩

/-- OET anchor: h-c4369c63c86cbacf
P01 单分量退化（全域）：`I = {i}` 时 Lip 矩阵条件化为 `d_i(φ x, φ y) ≤ L_{i→i} d_i(x, y)`。 -/
theorem mem_lipSet_single (i : I) (hI : ∀ k : I, k = i) (L : CoeffMat I) :
    L ∈ LipSet d φ ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hsum : ∀ f : I → ENNReal, ∑ k, f k = f i := fun f =>
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun k _ hk => absurd (hI k) hk)
  constructor
  · intro h x hx y hy
    simpa [hsum] using h x hx y hy i
  · intro h x hx y hy j
    obtain rfl := hI j
    simpa [hsum] using h x hx y hy

/-- P01 单分量退化（受限于 `U`）。 -/
theorem mem_lipSetOn_single (i : I) (hI : ∀ k : I, k = i) (L : CoeffMat I) (U : Set X) :
    L ∈ LipSetOn d φ U ↔
      U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hsum : ∀ f : I → ENNReal, ∑ k, f k = f i := fun f =>
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun k _ hk => absurd (hI k) hk)
  constructor
  · intro h
    refine ⟨h.1, fun x hx y hy => ?_⟩
    simpa [hsum] using h.2 x hx y hy i
  · intro h
    refine ⟨h.1, fun x hx y hy j => ?_⟩
    obtain rfl := hI j
    simpa [hsum] using h.2 x hx y hy

/-- P02 全域 Lip 证书可限制到任意 `U ⊆ dom φ`。 -/
theorem lipSet_subset_lipSetOn {U : Set X} (hU : U ⊆ dom φ) :
    LipSet d φ ⊆ LipSetOn d φ U :=
  fun _ hL => ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/-- P03 缩小评估域扩大 Lip 证书族：`U ⊆ V ⊆ dom φ` 时 `𝓛(φ)|_V ⊆ 𝓛(φ)|_U`。 -/
theorem lipSetOn_antitone {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    LipSetOn d φ V ⊆ LipSetOn d φ U :=
  fun _ hL => ⟨hUV.trans hV, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- 逐条目下确界 `a_{ij}(U) = inf {M_{ij} : M ∈ 𝓛(φ)|_U}`。 -/
def lipEntryInf (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun L : CoeffMat I => L i j) '' LipSetOn d φ U)

/-- P04 逐条目下确界在评估域缩小时不增：`U ⊆ V ⊆ dom φ` 时 `a_{ij}(U) ≤ a_{ij}(V)`。 -/
theorem lipEntryInf_mono {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom φ) (i j : I) :
    lipEntryInf d φ U i j ≤ lipEntryInf d φ V i j :=
  sInf_le_sInf (Set.image_mono (lipSetOn_antitone d φ hUV hV))

variable {d φ}

/-- OET anchor: h-193cebcc1a7f9259
P05 两步 Lip 复合：`U₁ ⊆ dom (φ₂ ∘ φ₁)`，`U₂ = φ₁(U₁)`，`L₁ ∈ 𝓛(φ₁)|_{U₁}`，
`L₂ ∈ 𝓛(φ₂)|_{U₂}`，则 `L₂ L₁ ∈ 𝓛(φ₂ ∘ φ₁)|_{U₁}`。 -/
theorem mmul_mem_lipSetOn_comp {φ₁ φ₂ : Operator X bot} {U₁ : Set X} {L₁ L₂ : CoeffMat I}
    (hdom : U₁ ⊆ dom (opComp φ₂ φ₁))
    (h₁ : L₁ ∈ LipSetOn d φ₁ U₁) (h₂ : L₂ ∈ LipSetOn d φ₂ (φ₁.func '' U₁)) :
    mmul L₂ L₁ ∈ LipSetOn d (opComp φ₂ φ₁) U₁ := by
  refine ⟨hdom, fun x hx y hy j => ?_⟩
  have hx' : φ₁.func x ∈ φ₁.func '' U₁ := ⟨x, hx, rfl⟩
  have hy' : φ₁.func y ∈ φ₁.func '' U₁ := ⟨y, hy, rfl⟩
  calc d j ((opComp φ₂ φ₁).func x) ((opComp φ₂ φ₁).func y)
      = d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := rfl
    _ ≤ ∑ k, L₂ k j * d k (φ₁.func x) (φ₁.func y) := h₂.2 _ hx' _ hy' j
    _ ≤ ∑ k, L₂ k j * ∑ i, L₁ i k * d i x y := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_right (h₁.2 x hx y hy k) _
    _ = ∑ i, mmul L₂ L₁ i j * d i x y := by
        simp only [mmul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm

/-- OET anchor: h-0f256e6f1d38a612
P07 两步 co-Lip 复合（同一实际像域）；非空性随 `K₁` 的证书保留。 -/
theorem mmul_mem_coLipSetOn_comp {φ₁ φ₂ : Operator X bot} {U₁ : Set X} {K₁ K₂ : CoeffMat I}
    (hdom : U₁ ⊆ dom (opComp φ₂ φ₁))
    (h₁ : K₁ ∈ CoLipSetOn d φ₁ U₁) (h₂ : K₂ ∈ CoLipSetOn d φ₂ (φ₁.func '' U₁)) :
    mmul K₂ K₁ ∈ CoLipSetOn d (opComp φ₂ φ₁) U₁ := by
  refine ⟨h₁.1, hdom, fun x hx y hy j => ?_⟩
  have hx' : φ₁.func x ∈ φ₁.func '' U₁ := ⟨x, hx, rfl⟩
  have hy' : φ₁.func y ∈ φ₁.func '' U₁ := ⟨y, hy, rfl⟩
  calc ∑ i, mmul K₂ K₁ i j * d i x y
      = ∑ k, K₂ k j * ∑ i, K₁ i k * d i x y := by
        simp only [mmul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ ≤ ∑ k, K₂ k j * d k (φ₁.func x) (φ₁.func y) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_right (h₁.2.2 x hx y hy k) _
    _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := h₂.2.2 _ hx' _ hy' j
    _ = d j ((opComp φ₂ φ₁).func x) ((opComp φ₂ φ₁).func y) := rfl

/-- OET anchor: h-88784dcbfff0ea66
P06 输出零距迫使 co-Lip 条目为 `0`：若 `x y ∈ dom φ` 满足 `d_j(φ x, φ y) = 0` 而
`d_i(x, y) > 0`，则任一全域 co-Lip 矩阵 `K ∈ 𝓚(φ)|_{dom φ}` 有 `K_{i→j} = 0`。 -/
theorem coLip_entry_eq_zero {K : CoeffMat I} (hK : K ∈ CoLipSetOn d φ (dom φ))
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have h1 : K i j * d i x y ≤ ∑ k, K k j * d k x y :=
    Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h2 := hK.2.2 x hx y hy j
  rw [hout] at h2
  have h3 : K i j * d i x y = 0 := le_antisymm (h1.trans h2) (zero_le _)
  rcases mul_eq_zero.1 h3 with h | h
  · exact h
  · exact absurd h hin.ne'

end Certificates


/-! ## 3. 两个算子的点对像距扰动界 -/

section Perturbation

variable {X I : Type} {bot : X} [Fintype I] {d : I → X → X → ENNReal}

/-- 扰动前提的对称化：`d_j(φ₂ z, φ₁ z) ≤ δ_j`。 -/
theorem perturb_symm (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {φ₁ φ₂ : Operator X bot}
    {U : Set X} {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j) :
    ∀ z ∈ U, ∀ j, d j (φ₂.func z) (φ₁.func z) ≤ δ j := by
  intro z hz j
  rw [(hd j).symm]
  exact hδ z hz j

/-- OET anchor: h-b959b42f25710105
P08 正向点对像距扰动：`d_j(φ₂ x, φ₂ y) ≤ d_j(φ₁ x, φ₁ y) + δ_j + δ_j`。 -/
theorem pair_dist_perturb_forward (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ₁ φ₂ : Operator X bot} {U : Set X} (_hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₂.func x) (φ₂.func y) ≤ d j (φ₁.func x) (φ₁.func y) + δ j + δ j := by
  have hδ' := perturb_symm hd hδ
  calc d j (φ₂.func x) (φ₂.func y)
      ≤ d j (φ₂.func x) (φ₁.func x) + d j (φ₁.func x) (φ₂.func y) := (hd j).triangle _ _ _
    _ ≤ d j (φ₂.func x) (φ₁.func x) + (d j (φ₁.func x) (φ₁.func y) + d j (φ₁.func y) (φ₂.func y)) :=
        add_le_add le_rfl ((hd j).triangle _ _ _)
    _ ≤ δ j + (d j (φ₁.func x) (φ₁.func y) + δ j) :=
        add_le_add (hδ' x hx j) (add_le_add le_rfl (hδ y hy j))
    _ = d j (φ₁.func x) (φ₁.func y) + δ j + δ j := by ring

/-- OET anchor: h-b959b42f25710105
P09 反向点对像距扰动：`d_j(φ₁ x, φ₁ y) ≤ d_j(φ₂ x, φ₂ y) + δ_j + δ_j`。 -/
theorem pair_dist_perturb_backward (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₁.func x) (φ₁.func y) ≤ d j (φ₂.func x) (φ₂.func y) + δ j + δ j :=
  pair_dist_perturb_forward hd (by rw [Set.inter_comm]; exact hU) (perturb_symm hd hδ) hx hy j

/-- P08/P09 的 `2δ_j` 写法（`2 * δ_j = δ_j + δ_j`）。 -/
theorem pair_dist_perturb (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₂.func x) (φ₂.func y) ≤ d j (φ₁.func x) (φ₁.func y) + 2 * δ j ∧
    d j (φ₁.func x) (φ₁.func y) ≤ d j (φ₂.func x) (φ₂.func y) + 2 * δ j := by
  have h1 := pair_dist_perturb_forward hd hU hδ hx hy j
  have h2 := pair_dist_perturb_backward hd hU hδ hx hy j
  simp only [add_assoc, ← two_mul] at h1 h2
  exact ⟨h1, h2⟩

/-- OET anchor: h-b959b42f25710105
P10 扰动 Lip 加性界（Lip 上界桥接）：`L₁ ∈ 𝓛(φ₁)|_U` 时
`d_j(φ₂ x, φ₂ y) ≤ ∑_i [L₁]_{i→j} d_i(x, y) + 2 δ_j`。 -/
theorem lip_perturb (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {L₁ : CoeffMat I} (hL : L₁ ∈ LipSetOn d φ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₂.func x) (φ₂.func y) ≤ ∑ i, L₁ i j * d i x y + 2 * δ j := by
  have h1 := pair_dist_perturb_forward hd hU hδ hx hy j
  have h2 := hL.2 x hx y hy j
  calc d j (φ₂.func x) (φ₂.func y)
      ≤ d j (φ₁.func x) (φ₁.func y) + δ j + δ j := h1
    _ = d j (φ₁.func x) (φ₁.func y) + 2 * δ j := by rw [add_assoc, ← two_mul]
    _ ≤ ∑ i, L₁ i j * d i x y + 2 * δ j := add_le_add h2 le_rfl

/-- OET anchor: h-b959b42f25710105
P11 扰动 co-Lip 加性界（co-Lip 下界桥接）：`K₁ ∈ 𝓚(φ₁)|_U` 时
`∑_i [K₁]_{i→j} d_i(x, y) ≤ d_j(φ₂ x, φ₂ y) + 2 δ_j`。 -/
theorem coLip_perturb (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {K₁ : CoeffMat I} (hK : K₁ ∈ CoLipSetOn d φ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i, K₁ i j * d i x y ≤ d j (φ₂.func x) (φ₂.func y) + 2 * δ j := by
  have h1 := pair_dist_perturb_backward hd hU hδ hx hy j
  have h2 := hK.2.2 x hx y hy j
  calc ∑ i, K₁ i j * d i x y
      ≤ d j (φ₁.func x) (φ₁.func y) := h2
    _ ≤ d j (φ₂.func x) (φ₂.func y) + δ j + δ j := h1
    _ = d j (φ₂.func x) (φ₂.func y) + 2 * δ j := by rw [add_assoc, ← two_mul]

/-- P10 的交换版本：`L₂ ∈ 𝓛(φ₂)|_U` 对 `φ₁` 的桥接。 -/
theorem lip_perturb_swap (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {L₂ : CoeffMat I} (hL : L₂ ∈ LipSetOn d φ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₁.func x) (φ₁.func y) ≤ ∑ i, L₂ i j * d i x y + 2 * δ j :=
  lip_perturb hd (by rw [Set.inter_comm]; exact hU) (perturb_symm hd hδ) hL hx hy j

/-- P11 的交换版本：`K₂ ∈ 𝓚(φ₂)|_U` 对 `φ₁` 的桥接。 -/
theorem coLip_perturb_swap (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {K₂ : CoeffMat I} (hK : K₂ ∈ CoLipSetOn d φ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i, K₂ i j * d i x y ≤ d j (φ₁.func x) (φ₁.func y) + 2 * δ j :=
  coLip_perturb hd (by rw [Set.inter_comm]; exact hU) (perturb_symm hd hδ) hK hx hy j

end Perturbation

/-! ## 4. 分量通道、解耦与通道分辨保持 -/

section Decoupling

variable {X I : Type} {bot : X} [Fintype I]
  {d : I → X → X → ENNReal} {φ : Operator X bot}

/-- OET anchor: h-7fa97eb6e24d5527
分量通道 `(i, j) ∈ I × I`：从输入分量 `d_i` 到输出分量 `d_j`。 -/
abbrev Channel (I : Type) : Type := I × I

/-- 单行稀疏 `Row(L, i, j)`：固定输出 `j`，除输入 `i` 外 `L_{k→j} = 0`。 -/
def RowSparse (L : CoeffMat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0

/-- 单列稀疏 `Col(L, i, j)`：固定输入 `i`，除输出 `j` 外 `L_{i→k} = 0`。 -/
def ColSparse (L : CoeffMat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0

/-- 对角矩阵：所有非对角条目为 `0`。 -/
def IsDiagonal (L : CoeffMat I) : Prop := ∀ i j, i ≠ j → L i j = 0

/-- 矩阵的第 `j` 行至多一项非零（`∃ i, Row(L, i, j)`）。 -/
def RowAtMostOne (L : CoeffMat I) (j : I) : Prop := ∃ i, RowSparse L i j

/-- 矩阵的第 `i` 列至多一项非零（`∃ j, Col(L, i, j)`）。 -/
def ColAtMostOne (L : CoeffMat I) (i : I) : Prop := ∃ j, ColSparse L i j

/-- `φ` 在 `U` 上关于输出分量 `d_j` 行解耦：存在 `L ∈ 𝓛(φ)|_U` 使第 `j` 行至多一项非零。 -/
def RowDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ LipSetOn d φ U, RowAtMostOne L j

/-- `φ` 在 `U` 上关于输入分量 `d_i` 列解耦：存在 `L ∈ 𝓛(φ)|_U` 使第 `i` 列至多一项非零。 -/
def ColDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ LipSetOn d φ U, ColAtMostOne L i

/-- 完全解耦体系：合法 Lip 证书 `L` 为对角矩阵。 -/
def FullyDecoupledCert (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : CoeffMat I) : Prop :=
  L ∈ LipSetOn d φ U ∧ IsDiagonal L

/-- P25（零系数项）：`L_{i→j} = 0` 时该项 `L_{i→j} d_i(x, y) = 0`（即使 `d_i(x, y) = +∞`）。 -/
theorem coeff_mul_dist_eq_zero {L : CoeffMat I} {i j : I} (h : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by
  rw [h, zero_mul]

/-- P25（`d_i(x, y) = +∞` 的情形）：`0 · ∞ = 0`，零系数项不贡献。 -/
theorem coeff_zero_mul_top {L : CoeffMat I} {i j : I} (h : L i j = 0) : L i j * (⊤ : ENNReal) = 0 := by
  rw [h, zero_mul]

/-- P25（求和删项）：`L_{i→j} = 0` 时输出 `j` 的求和可删去输入 `i` 这一项。 -/
theorem sum_eq_sum_erase_of_coeff_zero [DecidableEq I] {L : CoeffMat I} {i j : I} (h : L i j = 0) (x y : X) :
    ∑ k, L k j * d k x y = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), coeff_mul_dist_eq_zero h, zero_add]

/-- P25（上界证书中删项）。 -/
theorem lip_bound_erase_of_coeff_zero [DecidableEq I] {L : CoeffMat I} {U : Set X} (hL : L ∈ LipSetOn d φ U)
    {i j : I} (h : L i j = 0) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  rw [← sum_eq_sum_erase_of_coeff_zero h]
  exact hL.2 x hx y hy j

/-- P26 任意唯一输入位置的单行化简：`L ∈ 𝓛(φ)|_U` 且 `∀ k ≠ i, L_{k→j} = 0` 时
`d_j(φ x, φ y) ≤ L_{i→j} d_i(x, y)`；唯一的输入位置 `i` 不必等于 `j`。 -/
theorem lip_row_sparse {L : CoeffMat I} {U : Set X} (hL : L ∈ LipSetOn d φ U) {i j : I}
    (hrow : RowSparse L i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  have h := hL.2 x hx y hy j
  rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun k _ hk => by rw [hrow k hk, zero_mul])] at h

/-- 行解耦的结论：存在输入位置 `i` 与证书 `L` 使 `d_j(φ x, φ y) ≤ L_{i→j} d_i(x, y)`。 -/
theorem RowDecoupled.bound {U : Set X} {j : I} (h : RowDecoupled d φ U j) :
    ∃ L ∈ LipSetOn d φ U, ∃ i, ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  obtain ⟨L, hL, i, hi⟩ := h
  exact ⟨L, hL, i, fun x hx y hy => lip_row_sparse hL hi hx hy⟩

/-- P27 任意单列支撑的证书贡献范围：若所选 `L` 的第 `i` 列仅输出 `j` 可能非零，
则对 `k ≠ j` 有 `L_{i→k} d_i(x, y) = 0`，且输出 `k` 的上界中不含输入 `i`。 -/
theorem lip_col_sparse [DecidableEq I] {L : CoeffMat I} {U : Set X} (hL : L ∈ LipSetOn d φ U) {i j : I}
    (hcol : ColSparse L i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (∀ k, k ≠ j → L i k * d i x y = 0) ∧
    (∀ k, k ≠ j →
      d k (φ.func x) (φ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y) :=
  ⟨fun k hk => coeff_mul_dist_eq_zero (hcol k hk) x y,
   fun k hk => lip_bound_erase_of_coeff_zero hL (hcol k hk) hx hy⟩

/-- P28 对角 Lip 矩阵给出所有分量的标量上界：
`d_j(φ x, φ y) ≤ L_{j→j} d_j(x, y)`。 -/
theorem lip_diagonal {L : CoeffMat I} {U : Set X} (hL : L ∈ LipSetOn d φ U)
    (hdiag : IsDiagonal L) (j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  lip_row_sparse hL (fun k hk => hdiag k j hk) hx hy

/-- 完全解耦体系：各分量独立满足标量放缩 `d_i(φ x, φ y) ≤ L_{i→i} d_i(x, y)`。 -/
theorem FullyDecoupledCert.scalar {U : Set X} {L : CoeffMat I}
    (h : FullyDecoupledCert d φ U L) (i : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y :=
  lip_diagonal h.1 h.2 i hx hy

/-- 列解耦：存在证书使输入 `d_i` 的差异至多进入单一输出分量 `d_j` 的上界。 -/
theorem ColDecoupled.contribution [DecidableEq I] {U : Set X} {i : I}
    (h : ColDecoupled d φ U i) :
    ∃ L ∈ LipSetOn d φ U, ∃ j, ∀ x ∈ U, ∀ y ∈ U, ∀ k, k ≠ j →
      L i k * d i x y = 0 ∧
        d k (φ.func x) (φ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y := by
  obtain ⟨L, hL, j, hj⟩ := h
  exact ⟨L, hL, j, fun x hx y hy k hk =>
    ⟨(lip_col_sparse hL hj hx hy).1 k hk, (lip_col_sparse hL hj hx hy).2 k hk⟩⟩

/-- OET anchor: h-6a98a58b5bc95360
P29 双侧标量界仅要求 Lip 行稀疏：只假设 `∀ k ≠ j, L_{k→j} = 0` 时
`K_{j→j} d_j(x, y) ≤ d_j(φ x, φ y) ≤ L_{j→j} d_j(x, y)`。 -/
theorem two_sided_scalar {L K : CoeffMat I} {U : Set X} (hL : L ∈ LipSetOn d φ U)
    (hK : K ∈ CoLipSetOn d φ U) {j : I} (hrow : RowSparse L j j) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  refine ⟨?_, lip_row_sparse hL hrow hx hy⟩
  exact (Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _)
    (Finset.mem_univ j)).trans (hK.2.2 x hx y hy j)

/-- P30（逐分量）：Lip 对角行条件对所有 `j` 成立时，全部分量的双侧界同时成立。 -/
theorem two_sided_scalar_all {L K : CoeffMat I} {U : Set X} (hL : L ∈ LipSetOn d φ U)
    (hK : K ∈ CoLipSetOn d φ U) (hrow : ∀ j, RowSparse L j j) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j _ hx _ hy => two_sided_scalar hL hK (hrow j) hx hy

/-- P30（有限系数分支）：若进一步 `∀ j, L_{j→j} < ∞` 且 `K_{j→j} < ∞`，
则双侧界的标量系数是有限实数（`NNReal`）。 -/
theorem two_sided_scalar_finite {L K : CoeffMat I} {U : Set X} (hL : L ∈ LipSetOn d φ U)
    (hK : K ∈ CoLipSetOn d φ U) (hrow : ∀ j, RowSparse L j j)
    (hLfin : ∀ j, L j j < ⊤) (hKfin : ∀ j, K j j < ⊤) :
    ∀ j, ∃ ℓ κ : NNReal, L j j = ℓ ∧ K j j = κ ∧
      ∀ x ∈ U, ∀ y ∈ U, (κ : ENNReal) * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ (ℓ : ENNReal) * d j x y := by
  intro j
  refine ⟨(L j j).toNNReal, (K j j).toNNReal, (ENNReal.coe_toNNReal (hLfin j).ne).symm,
    (ENNReal.coe_toNNReal (hKfin j).ne).symm, fun x hx y hy => ?_⟩
  rw [ENNReal.coe_toNNReal (hLfin j).ne, ENNReal.coe_toNNReal (hKfin j).ne]
  exact two_sided_scalar_all hL hK hrow j x hx y hy

/-- OET anchor: h-f82672ec0dd48f28
P31 正 co-Lip 通道保持可分辨性：`K ∈ 𝓚(φ)|_U` 且 `K_{i→j} > 0` 时，
`d_i(x, y) > 0 → d_j(φ x, φ y) > 0`。 -/
theorem coLip_pos_channel {K : CoeffMat I} {U : Set X} (hK : K ∈ CoLipSetOn d φ U) {i j : I}
    (hij : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hxy : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have h1 : K i j * d i x y ≤ ∑ k, K k j * d k x y :=
    Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  exact lt_of_lt_of_le (ENNReal.mul_pos hij.ne' hxy.ne') (h1.trans (hK.2.2 x hx y hy j))

/-- OET anchor: h-f82672ec0dd48f28
P32 正对角 co-Lip 反射族零距关系：`K ∈ 𝓚(φ)|_U` 且 `∀ j, K_{j→j} > 0` 时，
`φ x ∼_𝒢 φ y → x ∼_𝒢 y`（`x y ∈ U`）。 -/
theorem coLip_pos_diag_reflects {K : CoeffMat I} {U : Set X} (hK : K ∈ CoLipSetOn d φ U)
    (hdiag : ∀ j, 0 < K j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : GaugeZeroRelated d (φ.func x) (φ.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.2 hne
  have := coLip_pos_channel hK (hdiag j) hx hy hpos
  exact absurd (h j) this.ne'

end Decoupling


/-! ## 5. 有限复合的局部矩阵界 -/

section Chains

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}

/-- OET anchor: h-11006ddd8c43bfec
P14 零步单位 Lip 证书：`𝐈 ∈ 𝓛(id)|_U`。 -/
theorem idMat_mem_lipSetOn {U : Set X} (hU : U ⊆ dom (opId : Operator X bot)) :
    (idMat : CoeffMat I) ∈ LipSetOn d (opId : Operator X bot) U := by
  refine ⟨hU, fun x hx y hy j => ?_⟩
  simp [idMat]

/-- OET anchor: h-11006ddd8c43bfec
P15 零步单位 co-Lip 证书：非空 `U ⊆ dom id` 上 `𝐈 ∈ 𝓚(id)|_U`。 -/
theorem idMat_mem_coLipSetOn {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (opId : Operator X bot)) :
    (idMat : CoeffMat I) ∈ CoLipSetOn d (opId : Operator X bot) U := by
  refine ⟨hne, hU, fun x hx y hy j => ?_⟩
  simp [idMat]

/-- P14（链语境）：`k = 0` 时 `c₀ = id`，空乘积为单位矩阵，仍是合法 Lip 证书。 -/
theorem lip_chain_zero (φ : ℕ → Operator X bot) (L : ℕ → CoeffMat I) {U : Set X}
    (hU : U ⊆ dom (chainOp φ 0)) : orderedProd L 0 ∈ LipSetOn d (chainOp φ 0) U :=
  idMat_mem_lipSetOn hU

/-- P15（链语境）：`k = 0` 时空乘积在非空 `U` 上也是合法 co-Lip 证书。 -/
theorem coLip_chain_zero (φ : ℕ → Operator X bot) (K : ℕ → CoeffMat I) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (chainOp φ 0)) :
    orderedProd K 0 ∈ CoLipSetOn d (chainOp φ 0) U :=
  idMat_mem_coLipSetOn hne hU

/-- OET anchor: h-c80171fa685dc795
P12 任意长度链的指定 Lip 乘积：`c_k = φ_k ∘ ⋯ ∘ φ_1`，`U_1 ⊆ dom c_k`，
`U_{m+1} = φ_m(U_m)`，每步 `L^{(m)} ∈ 𝓛(φ_m)|_{U_m}`，则 `L^{(k)} ⋯ L^{(1)} ∈ 𝓛(c_k)|_{U_1}`。
（对 `k = 0` 亦成立，即 P14。） -/
theorem lip_chain (φ : ℕ → Operator X bot) (L : ℕ → CoeffMat I) {k : ℕ} {U : ℕ → Set X}
    (hdom : U 1 ⊆ dom (chainOp φ k))
    (hU : ∀ m, 1 ≤ m → m ≤ k → U (m + 1) = (φ m).func '' U m)
    (hL : ∀ m, 1 ≤ m → m ≤ k → L m ∈ LipSetOn d (φ m) (U m)) :
    orderedProd L k ∈ LipSetOn d (chainOp φ k) (U 1) := by
  have himg := stepImg_eq_image_chainOp φ hU
  suffices h : ∀ n, n ≤ k → orderedProd L n ∈ LipSetOn d (chainOp φ n) (U 1) from h k le_rfl
  intro n
  induction n with
  | zero => exact fun _ => lip_chain_zero φ L (hdom.trans (dom_chainOp_antitone φ (Nat.zero_le k)))
  | succ n ih =>
    intro hn
    have hdom' : U 1 ⊆ dom (chainOp φ (n + 1)) := hdom.trans (dom_chainOp_antitone φ hn)
    refine mmul_mem_lipSetOn_comp hdom' (ih (by omega)) ?_
    rw [← himg n (by omega)]
    exact hL (n + 1) (by omega) hn

/-- OET anchor: h-c80171fa685dc795
P13 任意正长度链的指定 co-Lip 乘积（每步证书含非空性）：
`K^{(k)} ⋯ K^{(1)} ∈ 𝓚(c_k)|_{U_1}`。 -/
theorem coLip_chain (φ : ℕ → Operator X bot) (K : ℕ → CoeffMat I) {k : ℕ} (hk : 1 ≤ k)
    {U : ℕ → Set X}
    (hdom : U 1 ⊆ dom (chainOp φ k))
    (hU : ∀ m, 1 ≤ m → m ≤ k → U (m + 1) = (φ m).func '' U m)
    (hK : ∀ m, 1 ≤ m → m ≤ k → K m ∈ CoLipSetOn d (φ m) (U m)) :
    orderedProd K k ∈ CoLipSetOn d (chainOp φ k) (U 1) := by
  have himg := stepImg_eq_image_chainOp φ hU
  have hne : (U 1).Nonempty := (hK 1 le_rfl hk).1
  suffices h : ∀ n, n ≤ k → orderedProd K n ∈ CoLipSetOn d (chainOp φ n) (U 1) from h k le_rfl
  intro n
  induction n with
  | zero =>
    exact fun _ => coLip_chain_zero φ K hne (hdom.trans (dom_chainOp_antitone φ (Nat.zero_le k)))
  | succ n ih =>
    intro hn
    have hdom' : U 1 ⊆ dom (chainOp φ (n + 1)) := hdom.trans (dom_chainOp_antitone φ hn)
    refine mmul_mem_coLipSetOn_comp hdom' (ih (by omega)) ?_
    rw [← himg n (by omega)]
    exact hK (n + 1) (by omega) hn

/-- P12，使用递归定义的逐步像集 `stepImg`。 -/
theorem lip_chain_stepImg (φ : ℕ → Operator X bot) (L : ℕ → CoeffMat I) {k : ℕ} {U₁ : Set X}
    (hdom : U₁ ⊆ dom (chainOp φ k))
    (hL : ∀ m, 1 ≤ m → m ≤ k → L m ∈ LipSetOn d (φ m) (stepImg φ U₁ m)) :
    orderedProd L k ∈ LipSetOn d (chainOp φ k) U₁ :=
  lip_chain φ L (U := stepImg φ U₁) hdom (fun _ hm _ => stepImg_succ φ U₁ hm) hL

/-- P13，使用递归定义的逐步像集 `stepImg`。 -/
theorem coLip_chain_stepImg (φ : ℕ → Operator X bot) (K : ℕ → CoeffMat I) {k : ℕ} (hk : 1 ≤ k)
    {U₁ : Set X} (hdom : U₁ ⊆ dom (chainOp φ k))
    (hK : ∀ m, 1 ≤ m → m ≤ k → K m ∈ CoLipSetOn d (φ m) (stepImg φ U₁ m)) :
    orderedProd K k ∈ CoLipSetOn d (chainOp φ k) U₁ :=
  coLip_chain φ K hk (U := stepImg φ U₁) hdom (fun _ hm _ => stepImg_succ φ U₁ hm) hK

end Chains


/-! ## 6. 有限矩阵乘积条目的路径展开与零值/正值判据 -/

section Paths

variable {I : Type} [Fintype I] [DecidableEq I]

/-- 由起点 `i = k_0`、中间指标序列 `s = (k_1, …, k_N)`、终点 `j = k_{N+1}` 拼成的完整指标序列
`(k_0, k_1, …, k_{N+1})`；对应 `n = N + 1` 层的复合，`n = 1`（`N = 0`）时中间序列唯一且为空。 -/
def fullPath {N : ℕ} (i j : I) (s : Fin N → I) : Fin (N + 2) → I :=
  Fin.cons i (Fin.snoc s j)

@[simp] theorem fullPath_zero {N : ℕ} (i j : I) (s : Fin N → I) : fullPath i j s 0 = i := by
  simp [fullPath]

@[simp] theorem fullPath_last {N : ℕ} (i j : I) (s : Fin N → I) :
    fullPath i j s (Fin.last (N + 1)) = j := by
  simp [fullPath, ← Fin.succ_last]

@[simp] theorem fullPath_succ_castSucc {N : ℕ} (i j : I) (s : Fin N → I) (m : Fin N) :
    fullPath i j s m.castSucc.succ = s m := by
  simp [fullPath]

/-- 起止指标固定（`k_0 = i`，`k_n = j`）的完整指标序列与中间指标序列一一对应。 -/
theorem existsUnique_fullPath {N : ℕ} (i j : I) (k : Fin (N + 2) → I) (h0 : k 0 = i)
    (hl : k (Fin.last (N + 1)) = j) : ∃! s : Fin N → I, fullPath i j s = k := by
  refine ⟨fun m => k m.castSucc.succ, ?_, ?_⟩
  · funext m
    refine Fin.cases ?_ (fun m' => ?_) m
    · simp [h0]
    · refine Fin.lastCases ?_ (fun m'' => ?_) m'
      · rw [Fin.succ_last, fullPath_last, hl]
      · rw [fullPath_succ_castSucc]
  · intro s' hs'
    funext m
    rw [← fullPath_succ_castSucc i j s' m, hs']

/-- 沿完整路径 `k = (k_0, …, k_n)` 的第 `m` 层（`m = 1, …, n`，以 `Fin n` 中的 `m - 1` 表示）
边条目 `M^{(m)}_{k_{m-1} → k_m}`。 -/
def edgeEntry (M : ℕ → CoeffMat I) {n : ℕ} (k : Fin (n + 1) → I) (m : Fin n) : ENNReal :=
  M (m.val + 1) (k m.castSucc) (k m.succ)

/-- 路径权重：各层边条目之乘积。 -/
def pathWeight (M : ℕ → CoeffMat I) {n : ℕ} (k : Fin (n + 1) → I) : ENNReal :=
  ∏ m : Fin n, edgeEntry M k m

/-- 含零路径：某一层的边条目为 `0`。 -/
def PathHasZero (M : ℕ → CoeffMat I) {n : ℕ} (k : Fin (n + 1) → I) : Prop :=
  ∃ m : Fin n, edgeEntry M k m = 0

/-- 全正路径：所有层的边条目严格为正。 -/
def PathAllPos (M : ℕ → CoeffMat I) {n : ℕ} (k : Fin (n + 1) → I) : Prop :=
  ∀ m : Fin n, 0 < edgeEntry M k m

theorem fullPath_snoc_castSucc {N : ℕ} (i j c : I) (s : Fin N → I) (m : Fin (N + 2)) :
    fullPath i j (Fin.snoc s c : Fin (N + 1) → I) m.castSucc = fullPath i c s m := by
  refine Fin.cases ?_ (fun m' => ?_) m
  · simp
  · rw [← Fin.succ_castSucc]
    simp [fullPath]

theorem pathWeight_snoc {N : ℕ} (M : ℕ → CoeffMat I) (i j c : I) (s : Fin N → I) :
    pathWeight M (fullPath i j (Fin.snoc s c : Fin (N + 1) → I)) =
      pathWeight M (fullPath i c s) * M (N + 2) c j := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    simp only [edgeEntry, Fin.val_castSucc]
    rw [Fin.succ_castSucc, fullPath_snoc_castSucc, fullPath_snoc_castSucc]
  · simp only [edgeEntry, Fin.val_last]
    rw [Fin.succ_last, fullPath_snoc_castSucc]
    simp

/-- 乘积条目的展开式：`(M^{(N+1)} ⋯ M^{(1)})_{i→j} = ∑_{(k_1,…,k_N)} ∏_{m=1}^{N+1} M^{(m)}_{k_{m-1}→k_m}`
（`k_0 = i`，`k_{N+1} = j`，对所有中间指标序列求和，无任何正性约束）。 -/
theorem orderedProd_eq_sum_paths (M : ℕ → CoeffMat I) : ∀ (N : ℕ) (i j : I),
    orderedProd M (N + 1) i j = ∑ s : Fin N → I, pathWeight M (fullPath i j s) := by
  intro N
  induction N with
  | zero =>
    intro i j
    simp [orderedProd, mmul, idMat, pathWeight, edgeEntry, fullPath, Fin.snoc]
  | succ N ih =>
    intro i j
    rw [orderedProd_succ]
    simp only [mmul, ih, Finset.mul_sum]
    rw [← (Fin.snocEquiv (fun _ : Fin (N + 1) => I)).sum_comp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
    rw [mul_comm]
    exact (pathWeight_snoc M i j c s).symm

theorem pathWeight_eq_zero_iff (M : ℕ → CoeffMat I) {n : ℕ} (k : Fin (n + 1) → I) :
    pathWeight M k = 0 ↔ PathHasZero M k := by
  simp [pathWeight, PathHasZero, Finset.prod_eq_zero_iff]

theorem pathWeight_pos_iff (M : ℕ → CoeffMat I) {n : ℕ} (k : Fin (n + 1) → I) :
    0 < pathWeight M k ↔ PathAllPos M k := by
  rw [pos_iff_ne_zero, Ne, pathWeight_eq_zero_iff]
  simp [PathHasZero, PathAllPos, pos_iff_ne_zero]

/-- OET anchor: h-e4154c34e95d3c23
P16 Lip 乘积条目的零值判据：`(L^{(N+1)} ⋯ L^{(1)})_{i→j} = 0` 当且仅当
对每个中间指标序列，沿该路径至少有一层的边条目为 `0`。 -/
theorem orderedProd_eq_zero_iff (M : ℕ → CoeffMat I) (N : ℕ) (i j : I) :
    orderedProd M (N + 1) i j = 0 ↔ ∀ s : Fin N → I, PathHasZero M (fullPath i j s) := by
  rw [orderedProd_eq_sum_paths, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, forall_true_left, pathWeight_eq_zero_iff]

/-- OET anchor: h-e4154c34e95d3c23
P17 co-Lip 乘积条目的正值判据：`(K^{(N+1)} ⋯ K^{(1)})_{i→j} > 0` 当且仅当
存在一条中间指标序列，使沿该路径的所有边条目严格为正。 -/
theorem orderedProd_pos_iff (M : ℕ → CoeffMat I) (N : ℕ) (i j : I) :
    0 < orderedProd M (N + 1) i j ↔ ∃ s : Fin N → I, PathAllPos M (fullPath i j s) := by
  rw [pos_iff_ne_zero, Ne, orderedProd_eq_zero_iff]
  push Not
  simp only [PathHasZero, PathAllPos, not_exists, pos_iff_ne_zero]

/-- `n = 1` 时的退化：中间指标序列只有唯一的空序列，零值判据化为 `M¹_{i→j} = 0`。 -/
theorem orderedProd_one_eq_zero_iff (M : ℕ → CoeffMat I) (i j : I) :
    M 1 i j = 0 ↔ ∀ s : Fin 0 → I, PathHasZero M (fullPath i j s) := by
  rw [← orderedProd_eq_zero_iff, orderedProd_one]

/-- `n = 1` 时的退化：正值判据化为 `M¹_{i→j} > 0`。 -/
theorem orderedProd_one_pos_iff (M : ℕ → CoeffMat I) (i j : I) :
    0 < M 1 i j ↔ ∃ s : Fin 0 → I, PathAllPos M (fullPath i j s) := by
  rw [← orderedProd_pos_iff, orderedProd_one]

/-- `n = 1` 时中间指标序列唯一（空序列）。 -/
theorem card_intermediate_one : Fintype.card (Fin 0 → I) = 1 := by simp

/-- `n = 1` 时完整指标序列就是 `(k_0, k_1) = (i, j)`。 -/
theorem fullPath_of_empty (i j : I) (s : Fin 0 → I) : fullPath i j s = ![i, j] := by
  funext m
  fin_cases m <;> simp [fullPath, Fin.snoc]

end Paths

/-! ## 7. 链语境下的合并结论 -/

section ChainPaths

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I] {d : I → X → X → ENNReal}

/-- 正文推论 + 命题的合并：在 `c_{N+1} = φ_{N+1} ∘ ⋯ ∘ φ_1`、`U_1 ⊆ dom c_{N+1}`、
`U_{m+1} = φ_m(U_m)`、逐步 Lip/co-Lip 局部证书的同一条件下，
Lip/co-Lip 乘积是合法证书，且其条目满足路径零值/正值判据。 -/
theorem chain_certificates_and_path_criteria (φ : ℕ → Operator X bot) (L K : ℕ → CoeffMat I)
    (N : ℕ) {U : ℕ → Set X} (hdom : U 1 ⊆ dom (chainOp φ (N + 1)))
    (hU : ∀ m, 1 ≤ m → m ≤ N + 1 → U (m + 1) = (φ m).func '' U m)
    (hL : ∀ m, 1 ≤ m → m ≤ N + 1 → L m ∈ LipSetOn d (φ m) (U m))
    (hK : ∀ m, 1 ≤ m → m ≤ N + 1 → K m ∈ CoLipSetOn d (φ m) (U m)) :
    orderedProd L (N + 1) ∈ LipSetOn d (chainOp φ (N + 1)) (U 1) ∧
    orderedProd K (N + 1) ∈ CoLipSetOn d (chainOp φ (N + 1)) (U 1) ∧
    (∀ i j : I, orderedProd L (N + 1) i j = 0 ↔
      ∀ s : Fin N → I, PathHasZero L (fullPath i j s)) ∧
    (∀ i j : I, 0 < orderedProd K (N + 1) i j ↔
      ∃ s : Fin N → I, PathAllPos K (fullPath i j s)) :=
  ⟨lip_chain φ L hdom hU hL, coLip_chain φ K (Nat.succ_pos N) hdom hU hK,
   fun i j => orderedProd_eq_zero_iff L N i j, fun i j => orderedProd_pos_iff K N i j⟩

end ChainPaths


/-! ## 8. 单通道 Lip 常数 -/

section Channel

variable {X I : Type} {bot : X} (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
  (i j : I)

/-- OET anchor: h-57de7918859a9de2
分量通道 `(i, j)` 的可行标量族
`S_{ij} = {λ ∈ [0, ∞] : ∀ x y ∈ U, d_j(φ x, φ y) ≤ λ · d_i(x, y)}`。 -/
def scalarFeasible : Set ENNReal :=
  {c | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ c * d i x y}

/-- 单通道 Lip 常数 `a_{ij} = inf S_{ij}`（可行族为空时 `sInf ∅ = ⊤`）；
它与任何 Lip 矩阵条目 `[L]_{i→j}` 是不同的对象。 -/
def channelLip : ENNReal := sInf (scalarFeasible d φ U i j)

variable {d φ U i j}

/-- P18 零输入距而正输出距使可行族为空：若 `x y ∈ U`，`d_i(x, y) = 0 < d_j(φ x, φ y)`，
则不存在任何 `λ ∈ [0, ∞]` 的标量证书。 -/
theorem scalarFeasible_eq_empty {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : d i x y = 0)
    (hout : 0 < d j (φ.func x) (φ.func y)) : scalarFeasible d φ U i j = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun c hc => ?_
  have h := hc x hx y hy
  rw [hin, mul_zero] at h
  exact absurd h (not_le.2 hout)

/-- P18：此时单通道 Lip 常数为 `+∞`。 -/
theorem channelLip_eq_top {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : d i x y = 0)
    (hout : 0 < d j (φ.func x) (φ.func y)) : channelLip d φ U i j = ⊤ := by
  unfold channelLip
  rw [scalarFeasible_eq_empty hx hy hin hout, sInf_empty]

/-- P20 标量可行族向上封闭。 -/
theorem scalarFeasible_upward {c₀ c₁ : ENNReal} (h₀ : c₀ ∈ scalarFeasible d φ U i j)
    (h : c₀ ≤ c₁) : c₁ ∈ scalarFeasible d φ U i j :=
  fun x hx y hy => (h₀ x hx y hy).trans (by gcongr)

/-- P21 下确界以上的每个常数可行（含 `λ = +∞`）：`a < λ → λ ∈ S`。
（对一般的 `a`（含 `0 < a < ∞` 语境）成立。） -/
theorem mem_scalarFeasible_of_gt {c : ENNReal} (h : channelLip d φ U i j < c) :
    c ∈ scalarFeasible d φ U i j := by
  obtain ⟨c₀, hc₀, hlt⟩ := sInf_lt_iff.1 h
  exact scalarFeasible_upward hc₀ hlt.le

/-- P19 正有限最优单通道下确界取到：`0 < a < ∞` 时 `a ∈ S`，
即对所有 `x y ∈ U` 有 `d_j(φ x, φ y) ≤ a · d_i(x, y)`。 -/
theorem channelLip_mem_scalarFeasible (h0 : 0 < channelLip d φ U i j)
    (htop : channelLip d φ U i j < ⊤) :
    channelLip d φ U i j ∈ scalarFeasible d φ U i j := by
  intro x hx y hy
  by_cases hB0 : d i x y = 0
  · have h := mem_scalarFeasible_of_gt (c := ⊤) htop x hx y hy
    rw [hB0, mul_zero] at h ⊢
    exact h
  by_cases hBt : d i x y = ⊤
  · rw [hBt, ENNReal.mul_top h0.ne']
    exact le_top
  · have key : ∀ c, channelLip d φ U i j < c → d j (φ.func x) (φ.func y) ≤ c * d i x y :=
      fun c hc => mem_scalarFeasible_of_gt hc x hx y hy
    have hdiv : d j (φ.func x) (φ.func y) / d i x y ≤ channelLip d φ U i j :=
      le_of_forall_gt_imp_ge_of_dense fun c hc => (ENNReal.div_le_iff hB0 hBt).2 (key c hc)
    exact (ENNReal.div_le_iff hB0 hBt).1 hdiv

/-- P22 零下确界给出所有正常数（特别地所有有限正常数 `0 < λ < ∞`）作为标量证书。 -/
theorem mem_scalarFeasible_of_channelLip_eq_zero (h : channelLip d φ U i j = 0) {c : ENNReal}
    (hc : 0 < c) : c ∈ scalarFeasible d φ U i j :=
  mem_scalarFeasible_of_gt (by rw [h]; exact hc)

/-- P24 下确界有限当且仅当存在有限可行常数。 -/
theorem channelLip_lt_top_iff :
    channelLip d φ U i j < ⊤ ↔ ∃ c : ENNReal, c < ⊤ ∧ c ∈ scalarFeasible d φ U i j := by
  constructor
  · intro h
    obtain ⟨c, hc, hlt⟩ := sInf_lt_iff.1 h
    exact ⟨c, hlt, hc⟩
  · rintro ⟨c, hc, hmem⟩
    exact lt_of_le_of_lt (sInf_le hmem) hc

/-- 单通道常数与矩阵条目的关系：当 `L ∈ 𝓛(φ)|_U` 且第 `j` 行仅 `i` 位置可能非零时，
`L_{i→j}` 是可行标量，故 `a_{ij} ≤ L_{i→j}`；一般情形下二者无此关系。 -/
theorem channelLip_le_of_rowSparse [Fintype I] {L : CoeffMat I} (hL : L ∈ LipSetOn d φ U)
    (hrow : RowSparse L i j) : channelLip d φ U i j ≤ L i j :=
  sInf_le fun _ hx _ hy => lip_row_sparse hL hrow hx hy

end Channel

/-! ## 9. 反例：零下确界未必由 `0` 实现 -/

section Counterexample

/-- 反例空间 `Option Bool`（`⊥ = none`）上的离散扩展度量（单分量，指标集 `Unit`）。 -/
def cexDist : Unit → Option Bool → Option Bool → ENNReal :=
  fun _ x y => if x = y then 0 else ⊤

/-- 反例中的 `cexDist` 满足扩展伪度量四条公理与非吸收部分非空。 -/
theorem cexDist_isExtendedPseudoMetric (i : Unit) :
    ExtendedPseudoMetric (Option Bool) (none : Option Bool) (cexDist i) where
  nonabsorbing := ⟨some true, by simp⟩
  dist_self := fun x => by simp [cexDist]
  symm := fun x y => by
    by_cases h : x = y
    · subst h; rfl
    · simp [cexDist, h, Ne.symm h]
  triangle := fun x y z => by
    by_cases hxz : x = z
    · simp [cexDist, hxz]
    · have : x ≠ y ∨ y ≠ z := by
        by_contra hcon
        push Not at hcon
        exact hxz (hcon.1.trans hcon.2)
      rcases this with h | h <;> simp [cexDist, hxz, h]
  isolate_bot := fun x hx => by simp [cexDist, hx]

/-- 反例中的作用域 `U = {some false, some true}`。 -/
def cexU : Set (Option Bool) := {some false, some true}

/-- 反例算子：恒等算子。 -/
def cexOp : Operator (Option Bool) (none : Option Bool) := opId

theorem cexU_nonempty : cexU.Nonempty := ⟨some false, by simp [cexU]⟩

theorem cexU_subset_dom : cexU ⊆ dom cexOp := by
  intro x hx
  simp only [cexU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> simp [dom, cexOp]

/-- 反例中，任何正常数都是可行标量。 -/
theorem cex_pos_mem {c : ENNReal} (hc : 0 < c) :
    c ∈ scalarFeasible cexDist cexOp cexU () () := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp [cexDist]
  · have : cexDist () (cexOp.func x) (cexOp.func y) = ⊤ := by
      simp [cexDist, cexOp, hxy]
    rw [this]
    have h2 : cexDist () x y = ⊤ := by simp [cexDist, hxy]
    rw [h2, ENNReal.mul_top hc.ne']

/-- 反例中，`0` 不是可行标量（`d_i(x, y) = ∞` 而 `d_j(φ x, φ y) > 0`，但 `0 · ∞ = 0`）。 -/
theorem cex_zero_not_mem : (0 : ENNReal) ∉ scalarFeasible cexDist cexOp cexU () () := by
  intro h
  have := h (some false) (by simp [cexU]) (some true) (by simp [cexU])
  simp [cexDist, cexOp] at this

/-- P23 零下确界未必由 `0` 实现：存在合法扩展规范空间（有限非空指标集、四条公理、
非吸收部分非空）、合法算子 `φ` 与非空 `U ⊆ dom φ`，使 `a_{ij} = 0` 而 `0` 不满足标量上界。 -/
theorem channelLip_zero_not_attained :
    ∃ (X : Type) (bot : X) (I : Type) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i, ExtendedPseudoMetric X bot (d i))
      (φ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom φ ∧ channelLip d φ U i j = 0 ∧
        (0 : ENNReal) ∉ scalarFeasible d φ U i j := by
  refine ⟨Option Bool, none, Unit, inferInstance, inferInstance, cexDist,
    cexDist_isExtendedPseudoMetric, cexOp, cexU, (), (), cexU_nonempty, cexU_subset_dom,
    ?_, cex_zero_not_mem⟩
  refine le_antisymm ?_ (zero_le _)
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  exact sInf_le (cex_pos_mem ha)

end Counterexample

end

end formal_oet.vol_01.ch_02_operator_bounds
