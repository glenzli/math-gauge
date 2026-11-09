import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

/-!
# LCH02 · 第 2 章 · 矩阵约定、有限乘积与路径判据

（原文：Zhe Li 著 *The Operator Evolution Theory*，CC BY 4.0；署名与改动说明见 `Main.lean`。）

本文件只涉及以有限指标集 `I` 为指标的扩展非负矩阵（条目取值于 `ENNReal = [0, +∞]`），
对应 `source/02-operator-bounds.md` 中的

* 矩阵行列约定与矩阵乘法（`CH02-D03`）；
* 单位矩阵、空乘积与有序非空乘积（`CH02-D04`）；
* 有限指标路径与全正路径谓词（`CH02-D06`）；
* 命题 2.6：有限矩阵乘积条目的正值判据（`CH02-P14`）与零值判据（`CH02-P13`）。

**表示约定**

* 矩阵取为 Mathlib 的 `Matrix I I ENNReal`；正文的 `L_{i→j}`（输入分量 `i`、输出分量 `j`）
  位于第 `j` 行、第 `i` 列，即 `(L)_{ji} = L_{i→j}`，在 Lean 中为 `arrowEntry L i j = L j i`。
* 有限族 `M^(1), …, M^(n)` 取为 `M : ℕ → Matrix I I ENNReal`，**下标从 1 开始，与正文一致**，
  只有 `M 1, …, M n` 参与结论（`M 0` 与 `M m`（`m > n`）不参与任何结论）。
* 有序乘积 `M^(n) ⋯ M^(1)` 记为 `orderedProd M n`（先作用的 `M 1` 在最右）。
* 指标路径 `(k_0, k_1, …, k_n)`（`k_0 = i`、`k_n = j`）取为 `k : Fin (n + 1) → I`。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

variable {I : Type}

/-! ### CH02-D03 · 输入/输出矩阵指标约定与乘法 -/

/--
OET anchor: h-af85899693cc8750 （CH02-D03）
**矩阵指标约定**：书写矩阵 `L` 时以输出分量为行指标、输入分量为列指标，
`L_{i→j}`（输入分量 `i`、输出分量 `j`）位于第 `j` 行、第 `i` 列，即 `(L)_{ji} = L_{i→j}`。
`arrowEntry L i j` 即正文的 `L_{i→j}`。
-/
def arrowEntry (L : Matrix I I ENNReal) (i j : I) : ENNReal := L j i

/-- `L_{i→j}` 就是第 `j` 行、第 `i` 列的条目。 -/
@[simp] theorem arrowEntry_def (L : Matrix I I ENNReal) (i j : I) :
    arrowEntry L i j = L j i := rfl

/-- 以 `L_{i→j}` 为条目重新组装的矩阵就是原矩阵：行列约定是一一对应。 -/
theorem matrix_ext_arrowEntry {L L' : Matrix I I ENNReal}
    (h : ∀ i j, arrowEntry L i j = arrowEntry L' i j) : L = L' := by
  ext j i
  exact h i j

/--
OET anchor: h-af85899693cc8750 （CH02-D03）
**矩阵乘法的条目公式**：对 `Matrix` 乘积 `L₂ * L₁`（左因子在输出一侧），
`(L₂ · L₁)_{i→j} = ∑_{k} (L₂)_{k→j} (L₁)_{i→k}`。
这正是命题 2.2 与命题 2.4 证明中 "内部加和即为矩阵乘法元素" 所用的定义。
-/
theorem arrowEntry_mul [Fintype I] (L₂ L₁ : Matrix I I ENNReal) (i j : I) :
    arrowEntry (L₂ * L₁) i j = ∑ k, arrowEntry L₂ k j * arrowEntry L₁ i k := by
  simp [arrowEntry, Matrix.mul_apply]

/--
OET anchor: h-193cebcc1a7f9259 / h-0f256e6f1d38a612 （CH02-D03 的使用形式）
乘积矩阵作用在任意 "分量距离向量" `f : I → ENNReal` 上，等于逐次作用：
`∑_i (L₂ · L₁)_{i→j} f_i = ∑_k (L₂)_{k→j} (∑_i (L₁)_{i→k} f_i)`。
这是命题 2.2 / 2.4 证明中 "交换求和次序" 一步在 `ℝ̄₊` 上的代数内容。
-/
theorem sum_arrowEntry_mul_mul [Fintype I] (L₂ L₁ : Matrix I I ENNReal) (j : I)
    (f : I → ENNReal) :
    ∑ i, arrowEntry (L₂ * L₁) i j * f i =
      ∑ k, arrowEntry L₂ k j * ∑ i, arrowEntry L₁ i k * f i := by
  simp only [arrowEntry_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-! ### CH02-D04 · 单位矩阵、空乘积及有序非空乘积 -/

/--
OET anchor: h-11006ddd8c43bfec （CH02-D04）
**单位矩阵的条目**：`𝐈_{i→j} = 1`（`i = j`），`= 0`（`i ≠ j`）。
单位矩阵取 Mathlib 的 `(1 : Matrix I I ENNReal)`。
-/
theorem arrowEntry_one [DecidableEq I] (i j : I) :
    arrowEntry (1 : Matrix I I ENNReal) i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [arrowEntry]
  · simp [arrowEntry, h, Ne.symm h]

/--
OET anchor: h-11006ddd8c43bfec （CH02-D04）
单位矩阵作用在任意 "分量距离向量" `f : I → ENNReal` 上不改变它：
`∑_i 𝐈_{i→j} f_i = f_j`（`ℝ̄₊` 中 `0 * a = 0`、`1 * a = a`）。
-/
theorem sum_arrowEntry_one_mul [Fintype I] [DecidableEq I] (j : I) (f : I → ENNReal) :
    ∑ i, arrowEntry (1 : Matrix I I ENNReal) i j * f i = f j := by
  simp only [arrowEntry_one, ite_mul, one_mul, zero_mul]
  simp

/--
OET anchor: h-11006ddd8c43bfec / h-c80171fa685dc795 （CH02-D04）
**有序乘积** `M^(n) · ⋯ · M^(1)`：`orderedProd M n` 是 `M 1, …, M n` 的乘积，
先作用的矩阵 `M 1` 在最右；`n = 0` 时取空乘积，约定为单位矩阵 `𝐈`。
-/
noncomputable def orderedProd [Fintype I] [DecidableEq I] (M : ℕ → Matrix I I ENNReal) :
    ℕ → Matrix I I ENNReal
  | 0 => 1
  | n + 1 => M (n + 1) * orderedProd M n

section orderedProd

variable [Fintype I] [DecidableEq I] (M : ℕ → Matrix I I ENNReal)

/-- 空乘积是单位矩阵。 -/
@[simp] theorem orderedProd_zero : orderedProd M 0 = 1 := rfl

/-- 递推：`M^(n+1) · (M^(n) ⋯ M^(1))`，新矩阵加在乘积左侧。 -/
theorem orderedProd_succ (n : ℕ) : orderedProd M (n + 1) = M (n + 1) * orderedProd M n := rfl

/-- 单项乘积就是该矩阵本身。 -/
@[simp] theorem orderedProd_one : orderedProd M 1 = M 1 := by
  simp [orderedProd]

/-- 两项乘积：`M^(2) · M^(1)`。 -/
theorem orderedProd_two : orderedProd M 2 = M 2 * M 1 := by
  simp [orderedProd]

/-- 有序乘积对应 `List.prod`：列表 `[M n, …, M 1]` 的（从左到右）乘积。 -/
theorem orderedProd_eq_list_prod (n : ℕ) :
    orderedProd M n = ((List.range n).reverse.map fun m => M (m + 1)).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orderedProd_succ, ih, List.range_succ]
    simp

end orderedProd

/-! ### CH02-D06 · 有限指标路径与全正路径谓词 -/

/--
OET anchor: h-e4154c34e95d3c23 （CH02-D06）
**有限指标路径**：`k = (k_0, k_1, …, k_n)` 是从 `i` 到 `j` 的长度 `n` 的指标路径，
即 `k_0 = i`、`k_n = j`，中间指标 `(k_1, …, k_{n-1})` 任意。
-/
def IsIndexPath {n : ℕ} (i j : I) (k : Fin (n + 1) → I) : Prop :=
  k 0 = i ∧ k (Fin.last n) = j

/--
OET anchor: h-e4154c34e95d3c23 （CH02-D06）
**全正路径**：沿路径 `k` 所有单步矩阵条目均严格为正，
`∀ m ∈ {1,…,n}, [M^(m)]_{k_{m-1} → k_m} > 0`。
Lean 中 `m : Fin n` 对应正文的层级 `m + 1`。
-/
def IsPositivePath (M : ℕ → Matrix I I ENNReal) {n : ℕ} (k : Fin (n + 1) → I) : Prop :=
  ∀ m : Fin n, 0 < arrowEntry (M ((m : ℕ) + 1)) (k m.castSucc) (k m.succ)

/--
OET anchor: h-e4154c34e95d3c23 （CH02-D06）
**含零因子的路径**：存在层级 `m ∈ {1,…,n}` 使 `[M^(m)]_{k_{m-1} → k_m} = 0`。
-/
def HasZeroFactor (M : ℕ → Matrix I I ENNReal) {n : ℕ} (k : Fin (n + 1) → I) : Prop :=
  ∃ m : Fin n, arrowEntry (M ((m : ℕ) + 1)) (k m.castSucc) (k m.succ) = 0

/-- `ℝ̄₊` 中条目为零当且仅当它不严格为正（条目非负）。 -/
theorem eq_zero_iff_not_pos (x : ENNReal) : x = 0 ↔ ¬ 0 < x := by
  rw [pos_iff_ne_zero, not_not]

/-- 路径含零因子当且仅当它不是全正路径（`ℝ̄₊` 中条目非负）。 -/
theorem hasZeroFactor_iff_not_isPositivePath (M : ℕ → Matrix I I ENNReal) {n : ℕ}
    (k : Fin (n + 1) → I) : HasZeroFactor M k ↔ ¬ IsPositivePath M k := by
  unfold HasZeroFactor IsPositivePath
  rw [not_forall]
  refine exists_congr fun m => ?_
  rw [not_lt, nonpos_iff_eq_zero]

/-! ### 命题 2.6 · 有限矩阵乘积条目的零值与正值判据 -/

/-- `ℝ̄₊` 中，有限和 `∑_l f_l g_l` 为 `0` 当且仅当每一项的某个因子为 `0`。 -/
theorem sum_mul_eq_zero_iff [Fintype I] (f g : I → ENNReal) :
    ∑ l, f l * g l = 0 ↔ ∀ l, f l = 0 ∨ g l = 0 := by
  rw [Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero]

/-- `ℝ̄₊` 中，有限和 `∑_l f_l g_l` 严格为正当且仅当某一项的两个因子均严格为正。 -/
theorem sum_mul_pos_iff [Fintype I] (f g : I → ENNReal) :
    0 < ∑ l, f l * g l ↔ ∃ l, 0 < f l ∧ 0 < g l := by
  rw [pos_iff_ne_zero, Ne, sum_mul_eq_zero_iff]
  push Not
  simp only [pos_iff_ne_zero]

/--
命题 2.6 (ii) 的证明主体，对所有 `n`（含 `n = 0`）成立：
`[M^(n) ⋯ M^(1)]_{i→j} > 0` 当且仅当存在从 `i` 到 `j` 的全正路径。
-/
theorem prodEntry_pos_iff_exists_positivePath_aux [Fintype I] [DecidableEq I]
    (M : ℕ → Matrix I I ENNReal) :
    ∀ (n : ℕ) (i j : I), 0 < arrowEntry (orderedProd M n) i j ↔
      ∃ k : Fin (n + 1) → I, IsIndexPath i j k ∧ IsPositivePath M k := by
  intro n
  induction n with
  | zero =>
    intro i j
    simp only [orderedProd, arrowEntry_one, IsIndexPath, IsPositivePath]
    constructor
    · intro h
      by_cases hij : i = j
      · exact ⟨fun _ => i, ⟨rfl, hij⟩, fun m => m.elim0⟩
      · simp [hij] at h
    · rintro ⟨k, ⟨hk0, hkj⟩, -⟩
      have : i = j := by
        rw [← hk0, ← hkj]
        rfl
      simp [this]
  | succ n ih =>
    intro i j
    rw [orderedProd, arrowEntry_mul, sum_mul_pos_iff]
    constructor
    · rintro ⟨l, hl1, hl2⟩
      obtain ⟨k', ⟨hk0, hkl⟩, hpos⟩ := (ih i l).1 hl2
      refine ⟨Fin.snoc (α := fun _ => I) k' j, ⟨?_, ?_⟩, ?_⟩
      · have : (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) := rfl
        rw [this, Fin.snoc_castSucc]
        exact hk0
      · simp
      · intro m
        refine Fin.lastCases ?_ (fun m' => ?_) m
        · simpa [Fin.succ_last, hkl] using hl1
        · have := hpos m'
          rw [Fin.succ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.val_castSucc]
          exact this
    · rintro ⟨k, ⟨hk0, hkj⟩, hpos⟩
      refine ⟨k (Fin.last n).castSucc, ?_, ?_⟩
      · have := hpos (Fin.last n)
        simpa [Fin.succ_last, hkj] using this
      · rw [ih]
        refine ⟨Fin.init k, ⟨?_, rfl⟩, ?_⟩
        · exact hk0
        · intro m
          have := hpos m.castSucc
          rw [Fin.succ_castSucc, Fin.val_castSucc] at this
          exact this

/--
OET anchor: h-e4154c34e95d3c23 （CH02-P14）
**命题 2.6 (ii)（正值判据）**：设 `M^(1), …, M^(n)`（`n ≥ 1`）为以 `I` 为指标集的扩展非负矩阵，
则对任意 `i j : I`，`[M^(n) ⋯ M^(1)]_{i→j} > 0` 当且仅当存在至少一条指标序列
`(k_1, …, k_{n-1})`（即从 `i` 到 `j` 的指标路径 `k`），使沿该路径的所有单步矩阵条目均严格为正。
`n = 1` 的情形包含在内（见 `prodEntry_pos_iff_one`）。
-/
theorem prodEntry_pos_iff_exists_positivePath [Fintype I] [DecidableEq I]
    (M : ℕ → Matrix I I ENNReal) {n : ℕ} (_hn : 1 ≤ n) (i j : I) :
    0 < arrowEntry (orderedProd M n) i j ↔
      ∃ k : Fin (n + 1) → I, IsIndexPath i j k ∧ IsPositivePath M k :=
  prodEntry_pos_iff_exists_positivePath_aux M n i j

/--
OET anchor: h-e4154c34e95d3c23 （CH02-P13）
**命题 2.6 (i)（零值判据）**：设 `M^(1), …, M^(n)`（`n ≥ 1`）为以 `I` 为指标集的扩展非负矩阵，
则对任意 `i j : I`，`[M^(n) ⋯ M^(1)]_{i→j} = 0` 当且仅当对任意指标序列 `(k_1, …, k_{n-1})`
（即任意从 `i` 到 `j` 的指标路径 `k`），必存在层级 `m ∈ {1,…,n}` 使
`[M^(m)]_{k_{m-1} → k_m} = 0`。`n = 1` 的情形包含在内（见 `prodEntry_eq_zero_iff_one`）。
-/
theorem prodEntry_eq_zero_iff_forall_path_hasZeroFactor [Fintype I] [DecidableEq I]
    (M : ℕ → Matrix I I ENNReal) {n : ℕ} (hn : 1 ≤ n) (i j : I) :
    arrowEntry (orderedProd M n) i j = 0 ↔
      ∀ k : Fin (n + 1) → I, IsIndexPath i j k → HasZeroFactor M k := by
  have h := prodEntry_pos_iff_exists_positivePath M hn i j
  rw [eq_zero_iff_not_pos, h]
  simp only [hasZeroFactor_iff_not_isPositivePath, not_exists, not_and]

/-! ### `n = 1`：中间指标序列为空，两条判据退化为单个矩阵条目 -/

/-- `n = 1` 时，从 `i` 到 `j` 的全正路径存在当且仅当单个条目 `[M^(1)]_{i→j} > 0`。 -/
theorem exists_positivePath_one_iff (M : ℕ → Matrix I I ENNReal) (i j : I) :
    (∃ k : Fin 2 → I, IsIndexPath i j k ∧ IsPositivePath M k) ↔ 0 < arrowEntry (M 1) i j := by
  constructor
  · rintro ⟨k, ⟨hk0, hk1⟩, hpos⟩
    have := hpos 0
    simpa [hk0, ← hk1] using this
  · intro h
    refine ⟨![i, j], ⟨rfl, rfl⟩, ?_⟩
    intro m
    have hm : m = 0 := Subsingleton.elim m 0
    subst hm
    simpa using h

/-- `n = 1` 时，"每条从 `i` 到 `j` 的路径含零因子" 当且仅当单个条目 `[M^(1)]_{i→j} = 0`。 -/
theorem forall_path_hasZeroFactor_one_iff (M : ℕ → Matrix I I ENNReal) (i j : I) :
    (∀ k : Fin 2 → I, IsIndexPath i j k → HasZeroFactor M k) ↔ arrowEntry (M 1) i j = 0 := by
  have h := exists_positivePath_one_iff M i j
  rw [eq_zero_iff_not_pos, ← h]
  simp only [hasZeroFactor_iff_not_isPositivePath, not_exists, not_and]

/--
OET anchor: h-e4154c34e95d3c23 （CH02-P14 的 `n = 1` 情形）
`n = 1` 时中间指标序列为空，唯一序列满足 `k_0 = i`、`k_1 = j`，
正值判据退化为单个矩阵条目 `[M^(1)]_{i→j} > 0`
（与 `exists_positivePath_one_iff` 合用即得路径形式）。
-/
theorem prodEntry_pos_iff_one [Fintype I] [DecidableEq I] (M : ℕ → Matrix I I ENNReal) (i j : I) :
    0 < arrowEntry (orderedProd M 1) i j ↔ 0 < arrowEntry (M 1) i j := by
  rw [orderedProd_one]

/--
OET anchor: h-e4154c34e95d3c23 （CH02-P13 的 `n = 1` 情形）
`n = 1` 时零值判据退化为单个矩阵条目 `[M^(1)]_{i→j} = 0`。
-/
theorem prodEntry_eq_zero_iff_one [Fintype I] [DecidableEq I] (M : ℕ → Matrix I I ENNReal)
    (i j : I) :
    arrowEntry (orderedProd M 1) i j = 0 ↔ arrowEntry (M 1) i j = 0 := by
  rw [orderedProd_one]

end formal_oet.vol_01.ch_02_operator_bounds
