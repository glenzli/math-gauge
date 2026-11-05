{}
本任务已将 `obligations.json` 中指定的全部 20 项形式化义务完整形式化并通过 Lean 4 内核检查，无任何 `sorry` 或未检查公理，仅依赖标准逻辑公理（`propext`、`Classical.choice`、`Quot.sound`）。

### 交付文件列表

- [`OperatorBounds.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/LCH02-A1/1/work/OperatorBounds.lean)：包含全部 20 项义务（6 项定义谓词与证书族、14 项定理及推论证明）。
- [`Main.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/LCH02-A1/1/work/Main.lean)：导入目标模块并完成入口定义。
- [`alignment.json`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/LCH02-A1/1/work/alignment.json)：严格对应清单 20 项义务的对齐记录。

```lean filename=OperatorBounds.lean
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {X : Type} (bot : X) {I : Type} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-!
### 2.1 矩阵界与有限复合
-/

/--
OET anchor: oet-af85899693cc8750
输入/输出矩阵指标约定：
以输出分量为行指标、输入分量为列指标。
因此，从输入分量 i 到输出分量 j 的条目 L_{i → j} 位于第 j 行、第 i 列，即 (L)_{ji}。
-/
def entry (M : Matrix I I ENNReal) (i j : I) : ENNReal :=
  M j i

/--
OET anchor: oet-af85899693cc8750
矩阵乘积按输入/输出指标条目的展开式：
(A · B)_{i → j} = ∑_{k ∈ I} A_{k → j} · B_{i → k}。
-/
theorem entry_mul (A B : Matrix I I ENNReal) (i j : I) :
    entry (A * B) i j = ∑ k : I, entry A k j * entry B i k := by
  dsimp [entry]
  rw [Matrix.mul_apply]

/-!
### 零步复合与单位矩阵
-/

/--
OET anchor: oet-11006ddd8c43bfec
单位矩阵：输出分量与输入分量相等处为 1，其余处为 0。
-/
def mat_id : Matrix I I ENNReal := 1

/-- 单位矩阵的输入/输出条目。 -/
theorem entry_one (i j : I) : entry (mat_id : Matrix I I ENNReal) i j = if i = j then 1 else 0 := by
  dsimp [mat_id, entry]
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have hne : j ≠ i := Ne.symm h
    simp [h, hne]

/-- 乘以单位矩阵条目的求和公式。 -/
theorem sum_entry_one_mul (j : I) (v : I → ENNReal) :
    (∑ i : I, entry (mat_id : Matrix I I ENNReal) i j * v i) = v j := by
  simp_rw [entry_one]
  have : (fun i => (if i = j then (1 : ENNReal) else 0) * v i) =
         (fun i => if i = j then v j else 0) := by
    ext i
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]
  rw [this]
  rw [Finset.sum_ite_eq']
  simp

/--
OET anchor: oet-11006ddd8c43bfec
矩阵列表的有序乘积（空列表乘积为单位矩阵）。
-/
noncomputable def matrixProd (Ms : List (Matrix I I ENNReal)) : Matrix I I ENNReal :=
  Ms.prod

/-- 空列表的矩阵乘积为单位矩阵。 -/
theorem matrixProd_nil : matrixProd ([] : List (Matrix I I ENNReal)) = mat_id := rfl

/--
OET anchor: oet-e4154c34e95d3c23
长度为 n 的有序矩阵链乘积 M^(n) ⋯ M^(1)。
-/
noncomputable def matrixChainProd {n : ℕ} (M : Fin n → Matrix I I ENNReal) : Matrix I I ENNReal :=
  ((List.ofFn M).reverse).prod

/-- 长度为 0 的矩阵链乘积为单位矩阵。 -/
theorem matrixChainProd_zero (M : Fin 0 → Matrix I I ENNReal) :
    matrixChainProd M = mat_id := by
  dsimp [matrixChainProd, mat_id]
  simp

/-- 长度为 n + 1 的矩阵链乘积递归剥离最高项。 -/
theorem matrixChainProd_succ {n : ℕ} (M : Fin (n + 1) → Matrix I I ENNReal) :
    matrixChainProd M = M (Fin.last n) * matrixChainProd (fun k : Fin n => M k.castSucc) := by
  dsimp [matrixChainProd]
  rw [List.ofFn_succ_last]
  rw [List.reverse_concat]
  rw [List.prod_cons]

/-- 长度为 1 的矩阵链乘积即为其唯一矩阵。 -/
theorem matrixChainProd_one (M : Fin 1 → Matrix I I ENNReal) :
    matrixChainProd M = M 0 := by
  dsimp [matrixChainProd]
  have h : List.ofFn M = [M 0] := by ext; simp
  rw [h]; simp

/-!
### Lipschitz 上界矩阵与证书族
-/

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 Lip 矩阵）**：如果在 U 上对任意 x, y ∈ U 均满足距离放缩不等式，
则称 L 为 ϕ 在 U 上的一个受限 Lip 矩阵。
-/
def IsRestrictedLip (ϕ : Operator X bot) (U : Set X) (L : Matrix I I ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, entry L i j * d i x y

/--
OET anchor: oet-af85899693cc8750
ϕ 在 U 上的全体合法受限 Lip 矩阵之集 ℒ(ϕ)|_U。
-/
def restrictedLipSet (ϕ : Operator X bot) (U : Set X) : Set (Matrix I I ENNReal) :=
  { L | IsRestrictedLip bot d ϕ U L }

/--
OET anchor: oet-af85899693cc8750
**定义（Lipschitz 矩阵）**：对所有 x, y ∈ dom(ϕ) 均满足距离放缩不等式。
-/
def IsLip (ϕ : Operator X bot) (L : Matrix I I ENNReal) : Prop :=
  IsRestrictedLip bot d ϕ (dom ϕ) L

/--
OET anchor: oet-af85899693cc8750
ϕ 的全体合法 Lip 矩阵之集 ℒ(ϕ) = ℒ(ϕ)|_{dom(ϕ)}。
-/
def lipSet (ϕ : Operator X bot) : Set (Matrix I I ENNReal) :=
  restrictedLipSet bot d ϕ (dom ϕ)

/-!
### co-Lipschitz 下界矩阵与证书族
-/

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 co-Lipschitz 矩阵）**：对给定的非空子集 U ⊆ dom(ϕ)，
若对所有 x, y ∈ U 满足距离下界不等式，则称 K 为受限 co-Lip 矩阵。
凡出现受限 co-Lip 矩阵，均包含非空性条件 U ≠ ∅。
-/
def IsRestrictedCoLip (ϕ : Operator X bot) (U : Set X) (K : Matrix I I ENNReal) : Prop :=
  U.Nonempty ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, ∑ i : I, entry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/--
OET anchor: oet-af85899693cc8750
ϕ 在 U 上的全体合法 co-Lip 矩阵之集 𝒦(ϕ)|_U。
-/
def restrictedCoLipSet (ϕ : Operator X bot) (U : Set X) : Set (Matrix I I ENNReal) :=
  { K | IsRestrictedCoLip bot d ϕ U K }

/-- 全域 co-Lipschitz 矩阵谓词：要求 dom(ϕ) 非空且在 dom(ϕ) 上满足距离下界。 -/
def IsCoLip (ϕ : Operator X bot) (K : Matrix I I ENNReal) : Prop :=
  IsRestrictedCoLip bot d ϕ (dom ϕ) K

/-- 全域合法 co-Lip 矩阵证书族 𝒦(ϕ)|_{dom(ϕ)}。 -/
def globalCoLipSet (ϕ : Operator X bot) : Set (Matrix I I ENNReal) :=
  restrictedCoLipSet bot d ϕ (dom ϕ)

/-!
### 链表示与中间像域
-/

/-- 算子有限复合链的复合算子：c_k = ϕ_k ∘ ⋯ ∘ ϕ_1。 -/
def operatorChainProd {n : ℕ} (ϕ : Fin n → Operator X bot) : Operator X bot :=
  ((List.ofFn ϕ).reverse).prod

/-- 长度为 n + 1 的算子链递归剥离最高项。 -/
theorem operatorChainProd_succ {n : ℕ} (ϕ : Fin (n + 1) → Operator X bot) :
    operatorChainProd bot ϕ = ϕ (Fin.last n) * operatorChainProd bot (fun k : Fin n => ϕ k.castSucc) := by
  dsimp [operatorChainProd]
  rw [List.ofFn_succ_last]
  rw [List.reverse_concat]
  rw [List.prod_cons]

/-- 两步复合的精确中间像域属于下游算子定义域。 -/
theorem image_subset_dom_of_comp_dom {ϕ1 ϕ2 : Operator X bot} {U1 : Set X}
    (hU1 : U1 ⊆ dom (ϕ2 * ϕ1)) :
    operator_image ϕ1 U1 ⊆ dom ϕ2 := by
  rintro y ⟨x, hx, rfl⟩
  exact hU1 hx

/--
OET anchor: oet-c80171fa685dc795
复合算子链的受限 Lip 证书归纳结构：每一步在实际输入域上选取局部证书。
-/
inductive ValidLipChain (U1 : Set X) :
    List (Operator X bot) → List (Matrix I I ENNReal) → Prop
  | single (ϕ : Operator X bot) (L : Matrix I I ENNReal) :
      L ∈ restrictedLipSet bot d ϕ U1 →
      ValidLipChain U1 [ϕ] [L]
  | cons (ϕ : Operator X bot) (L : Matrix I I ENNReal) (ϕs : List (Operator X bot)) (Ls : List (Matrix I I ENNReal)) :
      ValidLipChain U1 ϕs Ls →
      L ∈ restrictedLipSet bot d ϕ (operator_image (OperatorChain ϕs) U1) →
      ValidLipChain U1 (ϕ :: ϕs) (L :: Ls)

/--
OET anchor: oet-c80171fa685dc795
复合算子链的受限 co-Lip 证书归纳结构：每一步在实际输入域上选取局部证书。
-/
inductive ValidCoLipChain (U1 : Set X) :
    List (Operator X bot) → List (Matrix I I ENNReal) → Prop
  | single (ϕ : Operator X bot) (K : Matrix I I ENNReal) :
      K ∈ restrictedCoLipSet bot d ϕ U1 →
      ValidCoLipChain U1 [ϕ] [K]
  | cons (ϕ : Operator X bot) (K : Matrix I I ENNReal) (ϕs : List (Operator X bot)) (Ks : List (Matrix I I ENNReal)) :
      ValidCoLipChain U1 ϕs Ks →
      K ∈ restrictedCoLipSet bot d ϕ (operator_image (OperatorChain ϕs) U1) →
      ValidCoLipChain U1 (ϕ :: ϕs) (K :: Ks)

/-!
### 有限指标路径
-/

/--
OET anchor: oet-e4154c34e95d3c23
长度为 n 的指标路径：从起点 i 到终点 j 的指标序列 (k_0, ..., k_n)。
-/
structure IndexPath (I : Type) (n : ℕ) (i j : I) where
  node : Fin (n + 1) → I
  start_eq : node 0 = i
  end_eq : node (Fin.last n) = j

/-- 全正路径谓词：沿路径的所有单步矩阵条目均严格正。 -/
def IsAllPositivePath {n : ℕ} (M : Fin n → Matrix I I ENNReal) {i j : I} (p : IndexPath I n i j) : Prop :=
  ∀ m : Fin n, entry (M m) (p.node m.castSucc) (p.node m.succ) > 0

/-- 含零单步路径谓词：沿路径至少存在一个单步矩阵条目为零。 -/
def HasZeroStep {n : ℕ} (M : Fin n → Matrix I I ENNReal) {i j : I} (p : IndexPath I n i j) : Prop :=
  ∃ m : Fin n, entry (M m) (p.node m.castSucc) (p.node m.succ) = 0

/-- 路径扩展构造：通过在末端追加节点 j 将长度为 n 的路径扩展为长度为 n + 1 的路径。 -/
def extendPath {n : ℕ} {i k : I} (p : IndexPath I n i k) (j : I) : IndexPath I (n + 1) i j := {
  node := Fin.lastCases j p.node
  start_eq := by
    have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
    rw [h0, Fin.lastCases_castSucc]
    exact p.start_eq
  end_eq := Fin.lastCases_last
}

/-- 路径限制构造：截取前 n 步得到长度为 n 的前缀路径。 -/
def restrictPath {n : ℕ} {i j : I} (p : IndexPath I (n + 1) i j) :
    IndexPath I n i (p.node (Fin.castSucc (Fin.last n))) := {
  node := fun m => p.node m.castSucc
  start_eq := by
    have h0 : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := rfl
    rw [h0]
    exact p.start_eq
  end_eq := rfl
}

theorem isAllPositive_extendPath {n : ℕ} {i k : I} (p : IndexPath I n i k) (j : I)
    (M : Fin (n + 1) → Matrix I I ENNReal) :
    IsAllPositivePath M (extendPath p j) ↔
      entry (M (Fin.last n)) k j > 0 ∧ IsAllPositivePath (fun m0 => M m0.castSucc) p := by
  constructor
  · intro hp
    constructor
    · have h_last := hp (Fin.last n)
      dsimp [extendPath] at h_last
      rw [Fin.lastCases_castSucc, Fin.lastCases_last, p.end_eq] at h_last
      exact h_last
    · intro m0
      have h_m0 := hp m0.castSucc
      dsimp [extendPath] at h_m0
      rw [Fin.lastCases_castSucc, ← Fin.castSucc_succ, Fin.lastCases_castSucc] at h_m0
      exact h_m0
  · rintro ⟨h_last, hp⟩ m
    refine Fin.lastCases ?_ ?_ m
    · dsimp [extendPath]
      rw [Fin.lastCases_castSucc, Fin.lastCases_last, p.end_eq]
      exact h_last
    · intro m0
      dsimp [extendPath]
      rw [Fin.lastCases_castSucc, ← Fin.castSucc_succ, Fin.lastCases_castSucc]
      exact hp m0

theorem isAllPositive_restrictPath {n : ℕ} {i j : I} (p : IndexPath I (n + 1) i j)
    (M : Fin (n + 1) → Matrix I I ENNReal) (hp : IsAllPositivePath M p) :
    entry (M (Fin.last n)) (p.node (Fin.castSucc (Fin.last n))) j > 0 ∧
    IsAllPositivePath (fun m0 => M m0.castSucc) (restrictPath p) := by
  constructor
  · have h_last := hp (Fin.last n)
    have : (Fin.last n : Fin (n + 1)).succ = Fin.last (n + 1) := rfl
    rw [this, p.end_eq] at h_last
    exact h_last
  · intro m0
    have h_m0 := hp m0.castSucc
    dsimp [restrictPath]
    rw [← Fin.castSucc_succ]
    exact h_m0

theorem not_isAllPositive_iff_hasZeroStep {n : ℕ} (M : Fin n → Matrix I I ENNReal) {i j : I}
    (p : IndexPath I n i j) :
    ¬ IsAllPositivePath M p ↔ HasZeroStep M p := by
  dsimp [IsAllPositivePath, HasZeroStep]
  constructor
  · intro h
    by_contra h_none
    apply h
    intro m
    by_contra hm
    have : entry (M m) (p.node m.castSucc) (p.node m.succ) = 0 := by
      rwa [not_lt, nonpos_iff_eq_zero] at hm
    exact h_none ⟨m, this⟩
  · rintro ⟨m, hm⟩ hp
    have hm_pos := hp m
    rw [hm] at hm_pos
    exact lt_irrefl 0 hm_pos

/-!
### 命题证明
-/

/--
OET anchor: oet-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界）**：
当 |I| = 1 且 I = {i} 时，受限 Lip 矩阵条件退化为单个标量不等式。
-/
theorem restricted_lip_singleton (ϕ : Operator X bot) (U : Set X) (L : Matrix I I ENNReal)
    (i : I) (h_single : ∀ j : I, j = i) :
    IsRestrictedLip bot d ϕ U L ↔
      ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) ≤ entry L i i * d i x y := by
  constructor
  · intro h x hx y hy
    have h_eval := h x hx y hy i
    have h_sum : (∑ k : I, entry L k i * d k x y) = entry L i i * d i x y := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        exact False.elim (hk (h_single k))
      · simp
    rw [h_sum] at h_eval
    exact h_eval
  · intro h x hx y hy j
    have hj : j = i := h_single j
    rw [hj]
    have h_eval := h x hx y hy
    have h_sum : (∑ k : I, entry L k i * d k x y) = entry L i i * d i x y := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        exact False.elim (hk (h_single k))
      · simp
    rw [h_sum]
    exact h_eval

/--
OET anchor: oet-c4369c63c86cbacf
单分量情形下的全域标量 Lip 界。
-/
theorem lip_singleton (ϕ : Operator X bot) (L : Matrix I I ENNReal)
    (i : I) (h_single : ∀ j : I, j = i) :
    IsLip bot d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ entry L i i * d i x y :=
  restricted_lip_singleton bot d ϕ (dom ϕ) L i h_single

/--
OET anchor: oet-4ff5c58d71e1651f
**引理 2.1（受限 Lip 矩阵族的单调性）**：若 U ⊆ V ⊆ dom(ϕ)，则 ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U。
-/
theorem restricted_lip_antitone {ϕ : Operator X bot} {U V : Set X} (hUV : U ⊆ V) :
    restrictedLipSet bot d ϕ V ⊆ restrictedLipSet bot d ϕ U := by
  intro L hL x hx y hy j
  exact hL x (hUV hx) y (hUV hy) j

/--
OET anchor: oet-4ff5c58d71e1651f
**引理 2.1（全域 Lip 证书可限制）**：对任意 U ⊆ dom(ϕ)，有 ℒ(ϕ) ⊆ ℒ(ϕ)|_U。
-/
theorem lip_subset_restricted {ϕ : Operator X bot} {U : Set X} (hU : U ⊆ dom ϕ) :
    lipSet bot d ϕ ⊆ restrictedLipSet bot d ϕ U :=
  restricted_lip_antitone bot d hU

/--
OET anchor: oet-193cebcc1a7f9259
**命题 2.2（Lip 矩阵复合律）**：
若 L^(1) ∈ ℒ(ϕ_1)|_{U_1} 且 L^(2) ∈ ℒ(ϕ_2)|_{ϕ_1(U_1)}，则 L^(2) · L^(1) ∈ ℒ(ϕ_2 ∘ ϕ_1)|_{U_1}。
-/
theorem lip_comp_two (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    {L1 L2 : Matrix I I ENNReal}
    (h1 : L1 ∈ restrictedLipSet bot d ϕ1 U1)
    (h2 : L2 ∈ restrictedLipSet bot d ϕ2 (operator_image ϕ1 U1)) :
    L2 * L1 ∈ restrictedLipSet bot d (ϕ2 * ϕ1) U1 := by
  intro x hx y hy j
  change d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) ≤ ∑ i : I, entry (L2 * L1) i j * d i x y
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  have step2 := h2 (ϕ1.func x) hx2 (ϕ1.func y) hy2 j
  apply le_trans step2
  have h_step : ∑ k : I, entry L2 k j * d k (ϕ1.func x) (ϕ1.func y) ≤
      ∑ k : I, entry L2 k j * ∑ i : I, entry L1 i k * d i x y := by
    gcongr with k
    exact h1 x hx y hy k
  apply le_trans h_step
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [entry_mul]

/--
OET anchor: oet-893b1d33535f7245
**引理 2.3（受限 co-Lip 矩阵族的单调性）**：若 ∅ ≠ U ⊆ V ⊆ dom(ϕ)，则 𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U。
-/
theorem restricted_co_lip_antitone {ϕ : Operator X bot} {U V : Set X}
    (hU_nonempty : U.Nonempty) (hUV : U ⊆ V) :
    restrictedCoLipSet bot d ϕ V ⊆ restrictedCoLipSet bot d ϕ U := by
  intro K hK
  refine ⟨hU_nonempty, ?_⟩
  intro x hx y hy j
  exact hK.2 x (hUV hx) y (hUV hy) j

/--
OET anchor: oet-893b1d33535f7245
**引理 2.3（全域 co-Lip 证书可限制）**：对任意非空子集 U ⊆ dom(ϕ)，有 𝒦(ϕ)|_{dom(ϕ)} ⊆ 𝒦(ϕ)|_U。
-/
theorem co_lip_subset_restricted {ϕ : Operator X bot} {U : Set X}
    (hU_nonempty : U.Nonempty) (hU : U ⊆ dom ϕ) :
    globalCoLipSet bot d ϕ ⊆ restrictedCoLipSet bot d ϕ U :=
  restricted_co_lip_antitone bot d hU_nonempty hU

/--
OET anchor: oet-88784dcbfff0ea66
**注（co-Lip 条目为零的充分条件）**：
若存在 x, y ∈ dom(ϕ) 使 d_j(ϕ(x), ϕ(y)) = 0 且 d_i(x, y) > 0，则任一全域 co-Lip 矩阵必满足 K_{i → j} = 0。
-/
theorem co_lip_entry_eq_zero_of_dist_zero (ϕ : Operator X bot)
    {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ) (i j : I)
    (h_out : d j (ϕ.func x) (ϕ.func y) = 0)
    (h_in : d i x y > 0)
    {K : Matrix I I ENNReal}
    (hK : K ∈ globalCoLipSet bot d ϕ) :
    entry K i j = 0 := by
  have h_ineq := hK.2 x hx y hy j
  rw [h_out] at h_ineq
  have h_term_le : entry K i j * d i x y ≤ ∑ k : I, entry K k j * d k x y :=
    Finset.single_le_sum (f := fun k => entry K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h_zero : entry K i j * d i x y = 0 := by
    exact le_antisymm (le_trans h_term_le h_ineq) (zero_le _)
  cases mul_eq_zero.mp h_zero with
  | inl h => exact h
  | inr h =>
    have : ¬ (d i x y > 0) := by rw [h]; exact lt_irrefl 0
    exact False.elim (this h_in)

/--
OET anchor: oet-0f256e6f1d38a612
**命题 2.4（co-Lip 矩阵复合律）**：
若 K^(1) ∈ 𝒦(ϕ_1)|_{U_1} 且 K^(2) ∈ 𝒦(ϕ_2)|_{ϕ_1(U_1)}，则 K^(2) · K^(1) ∈ 𝒦(ϕ_2 ∘ ϕ_1)|_{U_1}。
-/
theorem co_lip_comp_two (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    {K1 K2 : Matrix I I ENNReal}
    (h1 : K1 ∈ restrictedCoLipSet bot d ϕ1 U1)
    (h2 : K2 ∈ restrictedCoLipSet bot d ϕ2 (operator_image ϕ1 U1)) :
    K2 * K1 ∈ restrictedCoLipSet bot d (ϕ2 * ϕ1) U1 := by
  refine ⟨h1.1, ?_⟩
  intro x hx y hy j
  change ∑ i : I, entry (K2 * K1) i j * d i x y ≤ d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y))
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  have step2 := h2.2 (ϕ1.func x) hx2 (ϕ1.func y) hy2 j
  apply le_trans _ step2
  have h_eq : ∑ i : I, entry (K2 * K1) i j * d i x y =
      ∑ k : I, entry K2 k j * ∑ i : I, entry K1 i k * d i x y := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    rw [entry_mul]
  rw [h_eq]
  gcongr with k
  exact h1.2 x hx y hy k

/--
OET anchor: oet-c80171fa685dc795
**推论 2.5(i)（有限复合的局部 Lip 矩阵界）**：
若各单步具有合法矩阵 L^(m) ∈ ℒ(ϕ_m)|_{U_m}，则全复合满足 L^(k) ⋯ L^(1) ∈ ℒ(c_k)|_{U_1}。
-/
theorem valid_lip_chain_prod {U1 : Set X} {ϕs : List (Operator X bot)} {Ls : List (Matrix I I ENNReal)}
    (h : ValidLipChain bot d U1 ϕs Ls) :
    Ls.prod ∈ restrictedLipSet bot d (OperatorChain ϕs) U1 := by
  induction h with
  | single ϕ L hL =>
      simp [OperatorChain]
      exact hL
  | cons ϕ L ϕs Ls _ hL ih =>
      rw [List.prod_cons]
      change (L * Ls.prod) ∈ restrictedLipSet bot d (ϕ * OperatorChain ϕs) U1
      exact lip_comp_two bot d (OperatorChain ϕs) ϕ U1 ih hL

/--
OET anchor: oet-c80171fa685dc795
**推论 2.5(ii)（有限复合的局部 co-Lip 矩阵界）**：
若各单步具有合法矩阵 K^(m) ∈ 𝒦(ϕ_m)|_{U_m}，则全复合满足 K^(k) ⋯ K^(1) ∈ 𝒦(c_k)|_{U_1}。
-/
theorem valid_co_lip_chain_prod {U1 : Set X} {ϕs : List (Operator X bot)} {Ks : List (Matrix I I ENNReal)}
    (h : ValidCoLipChain bot d U1 ϕs Ks) :
    Ks.prod ∈ restrictedCoLipSet bot d (OperatorChain ϕs) U1 := by
  induction h with
  | single ϕ K hK =>
      simp [OperatorChain]
      exact hK
  | cons ϕ K ϕs Ks _ hK ih =>
      rw [List.prod_cons]
      change (K * Ks.prod) ∈ restrictedCoLipSet bot d (ϕ * OperatorChain ϕs) U1
      exact co_lip_comp_two bot d (OperatorChain ϕs) ϕ U1 ih hK

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步复合的单位矩阵证书，Lip）**：
对任意 U ⊆ dom(id)，单位矩阵 I ∈ ℒ(id)|_U。
-/
theorem identity_is_restricted_lip (U : Set X) :
    (mat_id : Matrix I I ENNReal) ∈ restrictedLipSet bot d operator_identity U := by
  intro x _ y _ j
  change d j x y ≤ ∑ i : I, entry mat_id i j * d i x y
  rw [sum_entry_one_mul]

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步复合的单位矩阵证书，co-Lip）**：
对任意非空 U ⊆ dom(id)，单位矩阵 I ∈ 𝒦(id)|_U。
-/
theorem identity_is_restricted_co_lip (U : Set X) (hU : U.Nonempty) :
    (mat_id : Matrix I I ENNReal) ∈ restrictedCoLipSet bot d operator_identity U := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  change ∑ i : I, entry mat_id i j * d i x y ≤ d j x y
  rw [sum_entry_one_mul]

/-- 有限和为正当且仅当存在严格正的求和项。 -/
theorem sum_pos_iff_exists_pos {α : Type} [Fintype α] (f : α → ENNReal) :
    (0 < ∑ x, f x) ↔ ∃ x, 0 < f x := by
  rw [pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    by_contra h_all
    apply h
    intro x _
    by_contra hx
    apply h_all
    exact ⟨x, pos_iff_ne_zero.mpr hx⟩
  · rintro ⟨x, hx⟩
    intro h_all
    have := h_all x (Finset.mem_univ x)
    exact (ne_of_gt hx) this

/-- ENNReal 乘积严格正当且仅当两因子均严格正。 -/
theorem ennreal_mul_pos (a b : ENNReal) : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp [pos_iff_ne_zero]

/--
OET anchor: oet-e4154c34e95d3c23
长度为 1 的矩阵链正值判据：单个条目严格正当且仅当唯一的长度 1 路径全正。
-/
theorem pos_criterion_one (M : Fin 1 → Matrix I I ENNReal) (i j : I) :
    entry (matrixChainProd M) i j > 0 ↔ ∃ p : IndexPath I 1 i j, IsAllPositivePath M p := by
  rw [matrixChainProd_one]
  constructor
  · intro h
    let p : IndexPath I 1 i j := {
      node := fun x => if x = 0 then i else j
      start_eq := by simp
      end_eq := by
        have : Fin.last 1 = (1 : Fin 2) := rfl
        rw [this]
        simp
    }
    refine ⟨p, ?_⟩
    intro m
    fin_cases m
    have hcast : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
    have hsucc : (0 : Fin 1).succ = (1 : Fin 2) := rfl
    have h0 : p.node 0 = i := p.start_eq
    have h1 : p.node 1 = j := by
      have : (Fin.last 1 : Fin 2) = 1 := rfl
      rw [← this]
      exact p.end_eq
    change entry (M 0) (p.node 0) (p.node 1) > 0
    rw [h0, h1]
    exact h
  · rintro ⟨p, hp⟩
    have hm : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
    have hs : (0 : Fin 1).succ = (1 : Fin 2) := rfl
    have h0 : p.node 0 = i := p.start_eq
    have h1 : p.node 1 = j := by
      have : (Fin.last 1 : Fin 2) = 1 := rfl
      rw [← this]
      exact p.end_eq
    have hp0 := hp 0
    rw [hm, hs, h0, h1] at hp0
    exact hp0

/--
OET anchor: oet-e4154c34e95d3c23
**命题 2.6(ii)（正值判据）**：
[M^(n) ⋯ M^(1)]_{i → j} > 0 当且仅当存在至少一条沿线单步矩阵条目均严格正的指标路径；包含 n = 1。
-/
theorem pos_criterion (n : ℕ) : ∀ (M : Fin (n + 1) → Matrix I I ENNReal) (i j : I),
    entry (matrixChainProd M) i j > 0 ↔ ∃ p : IndexPath I (n + 1) i j, IsAllPositivePath M p := by
  induction n with
  | zero =>
      intro M i j
      exact pos_criterion_one M i j
  | succ n ih =>
      intro M i j
      rw [matrixChainProd_succ]
      rw [entry_mul]
      change (0 < ∑ k : I, entry (M (Fin.last (n + 1))) k j * entry (matrixChainProd (fun m0 => M m0.castSucc)) i k) ↔ _
      rw [sum_pos_iff_exists_pos]
      simp_rw [ennreal_mul_pos]
      constructor
      · rintro ⟨k, h_last, h_prev⟩
        have h_p := (ih (fun m0 => M m0.castSucc) i k).mp h_prev
        rcases h_p with ⟨p_prev, hp_prev⟩
        refine ⟨extendPath p_prev j, ?_⟩
        rw [isAllPositive_extendPath]
        exact ⟨h_last, hp_prev⟩
      · rintro ⟨p, hp⟩
        have h_split := isAllPositive_restrictPath p M hp
        let k := p.node (Fin.castSucc (Fin.last (n + 1)))
        refine ⟨k, h_split.1, ?_⟩
        apply (ih (fun m0 => M m0.castSucc) i k).mpr
        exact ⟨restrictPath p, h_split.2⟩

/--
OET anchor: oet-e4154c34e95d3c23
**命题 2.6(i)（零值判据）**：
[M^(n) ⋯ M^(1)]_{i → j} = 0 当且仅当对任意指标路径必然存在至少一个单步条目为零；包含 n = 1。
-/
theorem zero_criterion (n : ℕ) (M : Fin (n + 1) → Matrix I I ENNReal) (i j : I) :
    entry (matrixChainProd M) i j = 0 ↔ ∀ p : IndexPath I (n + 1) i j, HasZeroStep M p := by
  have h_pos := pos_criterion n M i j
  constructor
  · intro h p
    by_contra hp
    have hp_pos : IsAllPositivePath M p := by
      by_contra h_not_pos
      exact hp ((not_isAllPositive_iff_hasZeroStep M p).mp h_not_pos)
    have h_gt : entry (matrixChainProd M) i j > 0 := h_pos.mpr ⟨p, hp_pos⟩
    rw [h] at h_gt
    exact lt_irrefl 0 h_gt
  · intro h_all
    by_contra h_ne
    have h_gt : entry (matrixChainProd M) i j > 0 := pos_iff_ne_zero.mpr h_ne
    rcases h_pos.mp h_gt with ⟨p, hp⟩
    have h_zero := h_all p
    have h_not := (not_isAllPositive_iff_hasZeroStep M p).mpr h_zero
    exact h_not hp

end formal_oet.vol_01.ch_02_operator_bounds

export formal_oet.vol_01.ch_02_operator_bounds (
  entry entry_mul mat_id entry_one sum_entry_one_mul matrixProd matrixProd_nil
  matrixChainProd matrixChainProd_zero matrixChainProd_succ matrixChainProd_one
  IsRestrictedLip restrictedLipSet IsLip lipSet
  IsRestrictedCoLip restrictedCoLipSet IsCoLip globalCoLipSet
  operatorChainProd operatorChainProd_succ image_subset_dom_of_comp_dom
  ValidLipChain ValidCoLipChain
  IndexPath IsAllPositivePath HasZeroStep extendPath restrictPath
  isAllPositive_extendPath isAllPositive_restrictPath not_isAllPositive_iff_hasZeroStep
  restricted_lip_singleton lip_singleton restricted_lip_antitone lip_subset_restricted
  lip_comp_two restricted_co_lip_antitone co_lip_subset_restricted
  co_lip_entry_eq_zero_of_dist_zero co_lip_comp_two
  valid_lip_chain_prod valid_co_lip_chain_prod
  identity_is_restricted_lip identity_is_restricted_co_lip
  pos_criterion_one pos_criterion zero_criterion
)
```

```lean filename=Main.lean
import OperatorBounds

open formal_oet.vol_01.ch_02_operator_bounds

def main : IO Unit := do
  IO.println "LCH02 obligations complete."
```

```json filename=alignment.json
{
  "case_id": "LCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedLip",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.restrictedLipSet",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.IsLip",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.lipSet"
      ],
      "representation": "对应正文 §2.1 受限与全域 Lipschitz 矩阵界定义。IsRestrictedLip bot d ϕ U L 定义为 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, d j (ϕ(x), ϕ(y)) ≤ ∑ i : I, entry L i j * d i x y；restrictedLipSet 为其证书集 ℒ(ϕ)|_U；IsLip 与 lipSet 为 U = dom(ϕ) 时的特化。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedCoLip",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.restrictedCoLipSet",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.IsCoLip",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.globalCoLipSet"
      ],
      "representation": "对应正文 §2.1 含非空条件的受限 co-Lipschitz 矩阵界定义。IsRestrictedCoLip bot d ϕ U K 要求 U.Nonempty 并且 ∀ x y ∈ U, ∀ j, ∑ i, entry K i j * d i x y ≤ d j (ϕ(x), ϕ(y))；restrictedCoLipSet 为其证书族 𝒦(ϕ)|_U；IsCoLip 与 globalCoLipSet 为 U = dom(ϕ) 时的特化。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.entry",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.entry_mul"
      ],
      "representation": "对应正文 §2.1 输入/输出矩阵指标约定与乘法：以输出分量为行指标、输入分量为列指标，entry M i j 定义为 M j i，表示 M_{i → j}；entry_mul 证明代数矩阵乘积条目与 (A · B)_{i → j} = ∑_k A_{k → j} B_{i → k} 的严格等价。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.mat_id",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.matrixProd",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.matrixChainProd"
      ],
      "representation": "对应正文 §2.1 与注 oet-11006ddd8c43bfec：mat_id 为单位矩阵 I；matrixProd 定义列表矩阵有序乘积（空列表乘积为 I）；matrixChainProd 定义有限族 M^(n) ⋯ M^(1) 的有序链乘积。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.operatorChainProd",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.ValidLipChain",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.ValidCoLipChain"
      ],
      "representation": "对应推论 2.5 实际中间像域 U_{m+1} = ϕ_m(U_m) 与链表示 c_k = ϕ_k ∘ ⋯ ∘ ϕ_1 的对应。ValidLipChain 与 ValidCoLipChain 以归纳谓词形式精确刻画各步在实际中间像域上选取证书的有限链结构。",
      "dependencies": [
        "CH02-D01",
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.IndexPath",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.IsAllPositivePath",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.HasZeroStep"
      ],
      "representation": "对应命题 2.6 有限指标路径结构。IndexPath I n i j 为节点映射 node : Fin (n + 1) → I 满足起止端点 node 0 = i 与 node (Fin.last n) = j；IsAllPositivePath 为沿线所有单步条目严格正；HasZeroStep 为存在单步条目等于 0。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.restricted_lip_singleton",
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.lip_singleton"
      ],
      "representation": "对应注 oet-c4369c63c86cbacf 单分量情形下的标量 Lip 界退化：当指标集 I 退化为单点 {i} 时，受限/全域 Lip 矩阵条件充要等价于单个标量不等式 d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} * d_i(x, y)。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.restricted_lip_antitone"
      ],
      "representation": "对应引理 2.1 受限 Lip 矩阵族的单调性：若 U ⊆ V ⊆ dom(ϕ)，则 ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U。",
      "dependencies": [
        "CH02-D01"
      ]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.lip_comp_two"
      ],
      "representation": "对应命题 2.2 两步 Lip 复合律：若 L^(1) ∈ ℒ(ϕ_1)|_{U_1} 且 L^(2) ∈ ℒ(ϕ_2)|_{ϕ_1(U_1)}，则代数矩阵乘积 L^(2) · L^(1) ∈ ℒ(ϕ_2 ∘ ϕ_1)|_{U_1}。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.restricted_co_lip_antitone"
      ],
      "representation": "对应引理 2.3 受限 co-Lip 矩阵族的单调性：若 ∅ ≠ U ⊆ V ⊆ dom(ϕ)，则 𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U。",
      "dependencies": [
        "CH02-D02"
      ]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.co_lip_entry_eq_zero_of_dist_zero"
      ],
      "representation": "对应注 oet-88784dcbfff0ea66 co-Lip 条目为零的充分条件：若存在 x, y ∈ dom(ϕ) 使 d_j(ϕ(x), ϕ(y)) = 0 且 d_i(x, y) > 0，则任意全域 co-Lip 矩阵 K 均满足 K_{i → j} = 0。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.co_lip_comp_two"
      ],
      "representation": "对应命题 2.4 两步 co-Lip 复合律：若 K^(1) ∈ 𝒦(ϕ_1)|_{U_1} 且 K^(2) ∈ 𝒦(ϕ_2)|_{ϕ_1(U_1)}，则 K^(2) · K^(1) ∈ 𝒦(ϕ_2 ∘ ϕ_1)|_{U_1}；包含非空性从 U_1 继承到 ϕ_1(U_1)。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.identity_is_restricted_lip"
      ],
      "representation": "对应注 oet-11006ddd8c43bfec 零步复合单位矩阵证书（Lip）：对任意 U ⊆ dom(id)，单位矩阵 I ∈ ℒ(id)|_U。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D04"
      ]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.identity_is_restricted_co_lip"
      ],
      "representation": "对应注 oet-11006ddd8c43bfec 零步复合单位矩阵证书（co-Lip）：对任意非空 U ⊆ dom(id)，单位矩阵 I ∈ 𝒦(id)|_U。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-D04"
      ]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.pos_criterion"
      ],
      "representation": "对应命题 2.6(ii) 有限矩阵乘积正值判据：对任意 n ≥ 1，[M^(n) ⋯ M^(1)]_{i → j} > 0 当且仅当存在一条指标路径 p 使得所有单步条目严格为正；包含 n = 1。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06"
      ]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.lip_subset_restricted"
      ],
      "representation": "对应引理 2.1 全域 Lip 证书可限制特例：若 U ⊆ dom(ϕ)，则 ℒ(ϕ) ⊆ ℒ(ϕ)|_U。",
      "dependencies": [
        "CH02-D01",
        "CH02-P02"
      ]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.co_lip_subset_restricted"
      ],
      "representation": "对应引理 2.3 全域 co-Lip 证书可限制特例：对任意非空子集 U ⊆ dom(ϕ)，有 𝒦(ϕ)|_{dom(ϕ)} ⊆ 𝒦(ϕ)|_U。",
      "dependencies": [
        "CH02-D02",
        "CH02-P05"
      ]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.valid_lip_chain_prod"
      ],
      "representation": "对应推论 2.5(i) 任意正长度链的 Lip 连乘界：从逐步证书归纳构造链证书，全复合算子链具有矩阵连乘证书 L^(k) ⋯ L^(1) ∈ ℒ(c_k)|_{U_1}。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P04"
      ]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.valid_co_lip_chain_prod"
      ],
      "representation": "对应推论 2.5(ii) 任意正长度链的 co-Lip 连乘界：从逐步证书归纳构造链证书，全复合算子链具有矩阵连乘证书 K^(k) ⋯ K^(1) ∈ 𝒦(c_k)|_{U_1}。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P08"
      ]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        "OperatorBounds.lean/formal_oet.vol_01.ch_02_operator_bounds.zero_criterion"
      ],
      "representation": "对应命题 2.6(i) 有限矩阵乘积零值判据：对任意 n ≥ 1，[M^(n) ⋯ M^(1)]_{i → j} = 0 当且仅当对任意指标路径 p，存在层级 m 使得单步条目为 0；包含 n = 1。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06",
        "CH02-P14"
      ]
    }
  ]
}
```
