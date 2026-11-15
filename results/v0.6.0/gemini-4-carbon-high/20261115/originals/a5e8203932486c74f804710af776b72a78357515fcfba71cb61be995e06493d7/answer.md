{}
以下完整交付 `LCH02`（有限复合与路径节群）全部 20 项义务的 Lean 4.29.1 形式化源码与对齐清单：

- [LCH02/MatrixProducts.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/LCH02/physical-1/session/work/LCH02/MatrixProducts.lean)：扩展非负矩阵通道指标约定、矩阵乘法、单位矩阵与空/非空有序连乘、有限指标路径与零值/正值路径判据（含 $n=1$ 退化）。
- [LCH02/OperatorBounds.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/LCH02/physical-1/session/work/LCH02/OperatorBounds.lean)：全域与受限 Lip 矩阵族、含非空条件的受限 co-Lip 矩阵族、单分量标量退化、受限单调性与全域限制、两步复合律、正长度链连乘界（含同前置 `OperatorChain` 的双向对应与实际中间像域递推）及零步单位矩阵双侧证书。
- [Main.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/LCH02/physical-1/session/work/Main.lean)：项目总入口，导入全部自建目标模块。
- [alignment.json](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/LCH02/physical-1/session/work/alignment.json)：覆盖全部 20 项义务的对齐说明与依赖关系。

> Source attribution: Zhe Li (also known as Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution Theory*, https://glenzli.com/books/oet/, licensed under CC BY 4.0.

```lean filename=LCH02/MatrixProducts.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace LCH02

open scoped BigOperators

/--
OET anchor: oet-af85899693cc8750
扩展非负规范界矩阵（`CH02-D03`）：
遵循正文行列约定，以输出分量为行指标（第一参数 `j`）、输入分量为列指标（第二参数 `i`），
因此 `M j i` 表示矩阵第 `j` 行、第 `i` 列元素 `(M)_{ji}`。
-/
abbrev GaugeMatrix (I : Type*) := Matrix I I ENNReal

/--
OET anchor: oet-af85899693cc8750
通道条目记号 `M_{i → j}`（`CH02-D03`）：
从输入分量 `i` 指向输出分量 `j` 的矩阵系数，按正文约定位于第 `j` 行、第 `i` 列，
即 `(M)_{ji} = M_{i → j}`。
-/
def channelEntry {I : Type*} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

@[simp]
theorem channelEntry_apply {I : Type*} (M : GaugeMatrix I) (i j : I) :
    channelEntry M i j = M j i := rfl

/--
OET anchor: oet-af85899693cc8750
扩展非负矩阵乘法 `(M₂ · M₁)`（`CH02-D03`）：
在行指标为输出分量、列指标为输入分量的约定下，标准矩阵乘法 `M₂ * M₁` 恰好给出
`(M₂ · M₁)_{i → j} = ∑_{k ∈ I} (M₂)_{k → j} · (M₁)_{i → k}`。
-/
noncomputable def gaugeMatrixMul {I : Type*} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) : GaugeMatrix I :=
  M₂ * M₁

@[simp]
theorem gaugeMatrixMul_eq_mul {I : Type*} [Fintype I] (M₂ M₁ : GaugeMatrix I) :
    gaugeMatrixMul M₂ M₁ = M₂ * M₁ := rfl

@[simp]
theorem channelEntry_mul {I : Type*} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    channelEntry (gaugeMatrixMul M₂ M₁) i j =
      ∑ k : I, channelEntry M₂ k j * channelEntry M₁ i k := by
  simp [channelEntry, gaugeMatrixMul, Matrix.mul_apply]

theorem gaugeMatrixMul_assoc {I : Type*} [Fintype I]
    (M₃ M₂ M₁ : GaugeMatrix I) :
    gaugeMatrixMul (gaugeMatrixMul M₃ M₂) M₁ =
      gaugeMatrixMul M₃ (gaugeMatrixMul M₂ M₁) :=
  Matrix.mul_assoc M₃ M₂ M₁

/--
OET anchor: oet-11006ddd8c43bfec
扩展非负单位矩阵 `I`（`CH02-D04`）。
-/
def identityMatrix {I : Type*} [DecidableEq I] : GaugeMatrix I :=
  1

@[simp]
theorem channelEntry_identityMatrix {I : Type*} [DecidableEq I] (i j : I) :
    channelEntry (identityMatrix (I := I)) i j = if i = j then 1 else 0 := by
  simp [channelEntry, identityMatrix, Matrix.one_apply, eq_comm]

/--
OET anchor: oet-11006ddd8c43bfec
带空乘积边界的有限矩阵有序连乘 `M^{(k)} · ⋯ · M^{(1)}`（`CH02-D04`）：
当 `k = 0` 时，空复合乘积定义为单位矩阵 `identityMatrix`；
当 `k ≥ 1` 时，按复合次序计算 `M^{(k)} · ⋯ · M^{(1)}`。
-/
noncomputable def matrixChainProd {I : Type*} [Fintype I] [DecidableEq I] :
    (k : ℕ) → (Fin k → GaugeMatrix I) → GaugeMatrix I
  | 0, _ => identityMatrix
  | 1, M => M 0
  | k + 2, M =>
      gaugeMatrixMul (M (Fin.last (k + 1)))
        (matrixChainProd (k + 1) (M ∘ Fin.castSucc))

@[simp]
theorem matrixChainProd_zero {I : Type*} [Fintype I] [DecidableEq I]
    (M : Fin 0 → GaugeMatrix I) :
    matrixChainProd 0 M = identityMatrix := rfl

@[simp]
theorem matrixChainProd_one {I : Type*} [Fintype I] [DecidableEq I]
    (M : Fin 1 → GaugeMatrix I) :
    matrixChainProd 1 M = M 0 := rfl

theorem matrixChainProd_succ {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (M : Fin (k + 1) → GaugeMatrix I) :
    matrixChainProd (k + 1) M =
      gaugeMatrixMul (M (Fin.last k)) (matrixChainProd k (M ∘ Fin.castSucc)) := by
  cases k with
  | zero =>
      simp [matrixChainProd, gaugeMatrixMul, identityMatrix]
  | succ m =>
      rfl

theorem matrixChainProd_eq_reverse_prod {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (M : Fin k → GaugeMatrix I) :
    matrixChainProd k M = ((List.ofFn M).reverse).prod := by
  induction k with
  | zero =>
      simp [matrixChainProd, identityMatrix]
  | succ m ih =>
      rw [matrixChainProd_succ, ih, List.ofFn_succ']
      simp [List.concat_eq_append, gaugeMatrixMul]
      rfl

/--
OET anchor: oet-11006ddd8c43bfec
有序非空矩阵连乘 `M^{(n)} · ⋯ · M^{(1)}`（`n ≥ 1`，`CH02-D04`）：
不依赖指标集的可判定相等性，`n = 1` 时直接退化为单个矩阵 `M^{(1)}`。
-/
noncomputable def nonemptyMatrixProd {I : Type*} [Fintype I] :
    (n : ℕ) → (hn : 1 ≤ n) → (Fin n → GaugeMatrix I) → GaugeMatrix I
  | 0, hn, _ => absurd hn (Nat.not_succ_le_zero 0)
  | 1, _, M => M 0
  | k + 2, _, M =>
      gaugeMatrixMul (M (Fin.last (k + 1)))
        (nonemptyMatrixProd (k + 1) (Nat.succ_pos k) (M ∘ Fin.castSucc))

@[simp]
theorem nonemptyMatrixProd_one {I : Type*} [Fintype I]
    (hn : 1 ≤ 1) (M : Fin 1 → GaugeMatrix I) :
    nonemptyMatrixProd 1 hn M = M 0 := rfl

theorem nonemptyMatrixProd_succ {I : Type*} [Fintype I]
    {n : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n + 1) (M : Fin (n + 1) → GaugeMatrix I) :
    nonemptyMatrixProd (n + 1) hn' M =
      gaugeMatrixMul (M (Fin.last n)) (nonemptyMatrixProd n hn (M ∘ Fin.castSucc)) := by
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ k => rfl

theorem nonemptyMatrixProd_eq_matrixChainProd {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) :
    nonemptyMatrixProd n hn M = matrixChainProd n M := by
  induction n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ k ih =>
      cases k with
      | zero => rfl
      | succ m =>
          have hm : 1 ≤ m + 1 := Nat.succ_pos m
          rw [nonemptyMatrixProd_succ hm (Nat.succ_pos (m + 1)),
              matrixChainProd_succ (m + 1), ih hm]

/--
OET anchor: oet-e4154c34e95d3c23
有限矩阵乘积的中间指标序列 `(k_1, k_2, ..., k_{n-1})`（`CH02-D06`）。
当 `n = 1` 时，`Fin (1 - 1) = Fin 0`，中间指标序列唯一为空序列。
-/
abbrev IntermediateSeq (I : Type*) (n : ℕ) : Type _ :=
  Fin (n - 1) → I

/--
OET anchor: oet-e4154c34e95d3c23
带起止指标约定 `k_0 = i`、`k_n = j` 的完整路径节点序列 `(k_0, k_1, ..., k_n)`（`CH02-D06`）。
-/
def pathVertex {I : Type*} {n : ℕ} (_hn : 1 ≤ n) (i j : I)
    (ks : IntermediateSeq I n) (r : Fin (n + 1)) : I :=
  if _h0 : r.val = 0 then i
  else if _hn_eq : r.val = n then j
  else ks ⟨r.val - 1, by omega⟩

@[simp]
theorem pathVertex_zero {I : Type*} {n : ℕ} (hn : 1 ≤ n) (i j : I)
    (ks : IntermediateSeq I n) :
    pathVertex hn i j ks 0 = i := by
  simp [pathVertex]

@[simp]
theorem pathVertex_last {I : Type*} {n : ℕ} (hn : 1 ≤ n) (i j : I)
    (ks : IntermediateSeq I n) :
    pathVertex hn i j ks (Fin.last n) = j := by
  have hne : (n : ℕ) ≠ 0 := by omega
  simp [pathVertex, Fin.last, hne]

theorem pathVertex_intermediate {I : Type*} {n : ℕ} (hn : 1 ≤ n) (i j : I)
    (ks : IntermediateSeq I n) (r : Fin (n - 1)) :
    pathVertex hn i j ks ⟨r.val + 1, by omega⟩ = ks r := by
  have h1 : r.val + 1 ≠ n := by omega
  simp [pathVertex, h1]

/--
OET anchor: oet-e4154c34e95d3c23
沿指标路径在第 `m` 步层级上的单步矩阵条目 `[M^{(m)}]_{k_{m-1} → k_m}`（`CH02-D06`）。
-/
def pathStepEntry {I : Type*} {n : ℕ} (hn : 1 ≤ n)
    (M : Fin n → GaugeMatrix I) (i j : I) (ks : IntermediateSeq I n) (m : Fin n) : ENNReal :=
  channelEntry (M m)
    (pathVertex hn i j ks m.castSucc)
    (pathVertex hn i j ks m.succ)

@[simp]
theorem pathStepEntry_one {I : Type*} (hn : 1 ≤ 1)
    (M : Fin 1 → GaugeMatrix I) (i j : I) (ks : IntermediateSeq I 1) :
    pathStepEntry hn M i j ks 0 = channelEntry (M 0) i j := by
  change channelEntry (M 0) (pathVertex hn i j ks 0) (pathVertex hn i j ks (Fin.last 1)) = _
  rw [pathVertex_zero, pathVertex_last]

/--
OET anchor: oet-e4154c34e95d3c23
全正路径谓词（`CH02-D06`）：沿路径的所有单步矩阵条目均严格大于零。
-/
def IsPositivePath {I : Type*} {n : ℕ} (hn : 1 ≤ n)
    (M : Fin n → GaugeMatrix I) (i j : I) (ks : IntermediateSeq I n) : Prop :=
  ∀ m : Fin n, 0 < pathStepEntry hn M i j ks m

/--
OET anchor: oet-e4154c34e95d3c23
含零因子路径谓词（`CH02-D06`）：路径上存在至少一个层级单步矩阵条目等于零。
-/
def HasZeroStep {I : Type*} {n : ℕ} (hn : 1 ≤ n)
    (M : Fin n → GaugeMatrix I) (i j : I) (ks : IntermediateSeq I n) : Prop :=
  ∃ m : Fin n, pathStepEntry hn M i j ks m = 0

/-- 沿单条指标序列的逐层条目乘积权重。 -/
noncomputable def pathWeight {I : Type*} {n : ℕ} (hn : 1 ≤ n)
    (M : Fin n → GaugeMatrix I) (i j : I) (ks : IntermediateSeq I n) : ENNReal :=
  ∏ m : Fin n, pathStepEntry hn M i j ks m

/-- 辅助等价：`1 ≤ n` 时，`(n + 1)` 步中间指标序列等价于前 `n` 步中间序列与第 `n` 个中间指标 `x : I` 的二元组。 -/
def intermediateSeqSuccEquiv (I : Type*) {n : ℕ} (hn : 1 ≤ n) :
    (IntermediateSeq I n × I) ≃ IntermediateSeq I (n + 1) where
  toFun p idx :=
    if hlt : idx.val < n - 1 then p.1 ⟨idx.val, hlt⟩ else p.2
  invFun ks :=
    (fun idx => ks ⟨idx.val, by omega⟩, ks ⟨n - 1, by omega⟩)
  left_inv := by
    rintro ⟨ks₀, x⟩
    ext idx
    · simp [idx.isLt]
    · simp
  right_inv := by
    intro ks
    ext idx
    by_cases hlt : idx.val < n - 1
    · simp [hlt]
    · simp only [hlt, ↓reduceDIte]
      congr 1
      ext
      have h_isLt := idx.isLt
      dsimp
      omega

private theorem intermediateSeqSuccEquiv_apply_lt {I : Type*} {n : ℕ} (hn : 1 ≤ n)
    (ks₀ : IntermediateSeq I n) (x : I) (idx : Fin n) (hlt : idx.val < n - 1) :
    intermediateSeqSuccEquiv I hn (ks₀, x) idx = ks₀ ⟨idx.val, hlt⟩ := by
  simp [intermediateSeqSuccEquiv, hlt]

private theorem intermediateSeqSuccEquiv_apply_last {I : Type*} {n : ℕ} (hn : 1 ≤ n)
    (ks₀ : IntermediateSeq I n) (x : I) (idx : Fin n) (_heq : idx.val = n - 1) :
    intermediateSeqSuccEquiv I hn (ks₀, x) idx = x := by
  have hnotlt : ¬ idx.val < n - 1 := by omega
  simp [intermediateSeqSuccEquiv, hnotlt]

private theorem pathVertex_succ_prefix {I : Type*} {n : ℕ} (hn : 1 ≤ n)
    (hn' : 1 ≤ n + 1) (i j x : I) (ks₀ : IntermediateSeq I n) (r : Fin (n + 1)) :
    pathVertex hn' i j (intermediateSeqSuccEquiv I hn (ks₀, x)) r.castSucc =
      pathVertex hn i x ks₀ r := by
  by_cases h0 : r.val = 0
  · simp [pathVertex, h0]
  · by_cases hlast : r.val = n
    · have hnotlast' : r.val ≠ n + 1 := by omega
      have hd1 : pathVertex hn' i j (intermediateSeqSuccEquiv I hn (ks₀, x)) r.castSucc =
          intermediateSeqSuccEquiv I hn (ks₀, x) ⟨r.val - 1, by omega⟩ := by
        dsimp [pathVertex]
        rw [dif_neg h0, dif_neg hnotlast']
      have hd2 : pathVertex hn i x ks₀ r = x := by
        dsimp [pathVertex]
        rw [dif_neg h0, dif_pos hlast]
      rw [hd1, hd2]
      exact intermediateSeqSuccEquiv_apply_last hn ks₀ x ⟨r.val - 1, by omega⟩ (by dsimp; omega)
    · have hnotlast' : r.val ≠ n + 1 := by omega
      have hd1 : pathVertex hn' i j (intermediateSeqSuccEquiv I hn (ks₀, x)) r.castSucc =
          intermediateSeqSuccEquiv I hn (ks₀, x) ⟨r.val - 1, by omega⟩ := by
        dsimp [pathVertex]
        rw [dif_neg h0, dif_neg hnotlast']
      have hd2 : pathVertex hn i x ks₀ r = ks₀ ⟨r.val - 1, by omega⟩ := by
        dsimp [pathVertex]
        rw [dif_neg h0, dif_neg hlast]
      rw [hd1, hd2]
      have hlt : r.val - 1 < n - 1 := by omega
      exact intermediateSeqSuccEquiv_apply_lt hn ks₀ x ⟨r.val - 1, by omega⟩ hlt

/--
OET anchor: oet-e4154c34e95d3c23
有限非空矩阵乘积条目的路径求和展开式（含 `n = 1`）。
-/
theorem channelEntry_nonemptyMatrixProd_eq_sum_pathWeight {I : Type*} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    channelEntry (nonemptyMatrixProd n hn M) i j =
      ∑ ks : IntermediateSeq I n, pathWeight hn M i j ks := by
  induction n generalizing j with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ k ih =>
      cases k with
      | zero =>
          simp [nonemptyMatrixProd, pathWeight]
      | succ m =>
          have hm : 1 ≤ m + 1 := Nat.succ_pos m
          have hm' : 1 ≤ m + 2 := Nat.succ_pos (m + 1)
          rw [nonemptyMatrixProd_succ hm hm', channelEntry_mul]
          have h_expand :
              ∑ x : I, channelEntry (M (Fin.last (m + 1))) x j *
                channelEntry (nonemptyMatrixProd (m + 1) hm (M ∘ Fin.castSucc)) i x =
              ∑ p : IntermediateSeq I (m + 1) × I,
                pathWeight hm' M i j (intermediateSeqSuccEquiv I hm p) := by
            rw [Fintype.sum_prod_type_right]
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [ih hm (M ∘ Fin.castSucc) x, mul_comm, Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro ks₀ _
            dsimp [pathWeight]
            rw [Fin.prod_univ_castSucc (n := m + 1)]
            refine congrArg₂ ((· * ·) : ENNReal → ENNReal → ENNReal) ?_ ?_
            · refine Finset.prod_congr rfl ?_
              intro s _
              dsimp [pathStepEntry]
              have h_start :=
                pathVertex_succ_prefix hm hm' i j x ks₀ s.castSucc
              have h_end :=
                pathVertex_succ_prefix hm hm' i j x ks₀ s.succ
              change _ = channelEntry (M s.castSucc)
                (pathVertex hm' i j (intermediateSeqSuccEquiv I hm (ks₀, x)) s.castSucc.castSucc)
                (pathVertex hm' i j (intermediateSeqSuccEquiv I hm (ks₀, x)) s.castSucc.succ)
              have hs_succ : s.castSucc.succ = s.succ.castSucc := by
                ext
                rfl
              rw [hs_succ, h_start, h_end]
              rfl
            · dsimp [pathStepEntry, channelEntry]
              have h_start :=
                pathVertex_succ_prefix hm hm' i j x ks₀ (Fin.last (m + 1))
              rw [pathVertex_last] at h_start
              rw [h_start, pathVertex_last]
          rw [h_expand]
          exact Equiv.sum_comp (intermediateSeqSuccEquiv I hm)
            (fun ks => pathWeight hm' M i j ks)

/--
OET anchor: oet-e4154c34e95d3c23
**命题 2.6(i)（有限矩阵乘积条目的零值判据，`CH02-P13`）**：
对任意 `n ≥ 1`（含 `n = 1`）与任意 `i, j ∈ I`，
`[M^{(n)} ⋯ M^{(1)}]_{i → j} = 0` 当且仅当每一条指标路径均包含至少一个零因子。
-/
theorem channelEntry_nonemptyMatrixProd_eq_zero_iff {I : Type*} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    channelEntry (nonemptyMatrixProd n hn M) i j = 0 ↔
      ∀ ks : IntermediateSeq I n, HasZeroStep hn M i j ks := by
  rw [channelEntry_nonemptyMatrixProd_eq_sum_pathWeight, Finset.sum_eq_zero_iff]
  constructor
  · intro h ks
    have hprod : pathWeight hn M i j ks = 0 := h ks (Finset.mem_univ ks)
    simpa [pathWeight, HasZeroStep, Finset.prod_eq_zero_iff] using hprod
  · intro h ks _
    simpa [pathWeight, HasZeroStep, Finset.prod_eq_zero_iff] using h ks

/--
OET anchor: oet-e4154c34e95d3c23
`n = 1` 时零值判据路径条件退化为单个矩阵条目 `[M^{(1)}]_{i → j} = 0`（`CH02-P13`）。
-/
theorem all_hasZeroStep_one_iff {I : Type*}
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (∀ ks : IntermediateSeq I 1, HasZeroStep (le_rfl : 1 ≤ 1) M i j ks) ↔
      channelEntry (M 0) i j = 0 := by
  constructor
  · intro h
    rcases h Fin.elim0 with ⟨m, hm⟩
    fin_cases m
    simpa using hm
  · intro h ks
    exact ⟨0, by simpa using h⟩

/--
OET anchor: oet-e4154c34e95d3c23
**命题 2.6(ii)（有限矩阵乘积条目的正值判据，`CH02-P14`）**：
对任意 `n ≥ 1`（含 `n = 1`）与任意 `i, j ∈ I`，
`[M^{(n)} ⋯ M^{(1)}]_{i → j} > 0` 当且仅当存在至少一条全正路径。
-/
theorem channelEntry_nonemptyMatrixProd_pos_iff {I : Type*} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < channelEntry (nonemptyMatrixProd n hn M) i j ↔
      ∃ ks : IntermediateSeq I n, IsPositivePath hn M i j ks := by
  rw [pos_iff_ne_zero, Ne, channelEntry_nonemptyMatrixProd_eq_zero_iff]
  simp [HasZeroStep, IsPositivePath, pos_iff_ne_zero]

/--
OET anchor: oet-e4154c34e95d3c23
带起止端点约束的 `n` 步有限指标路径结构 `(k_0, k_1, ..., k_n)`（`k_0 = i`, `k_n = j`，`CH02-D06`）。
-/
@[ext]
structure IndexPath (I : Type*) (n : ℕ) (i j : I) where
  vertex : Fin (n + 1) → I
  start_eq : vertex 0 = i
  end_eq : vertex (Fin.last n) = j

/-- `n ≥ 1` 时，中间指标序列 `(k_1, ..., k_{n-1})` 与带端点约束的有限指标路径 `IndexPath I n i j` 典范等价（`CH02-D06`）。 -/
def intermediateSeqEquivIndexPath {I : Type*} {n : ℕ} (hn : 1 ≤ n) (i j : I) :
    IntermediateSeq I n ≃ IndexPath I n i j where
  toFun ks :=
    { vertex := pathVertex hn i j ks
      start_eq := pathVertex_zero hn i j ks
      end_eq := pathVertex_last hn i j ks }
  invFun p r := p.vertex ⟨r.val + 1, by omega⟩
  left_inv ks := by
    ext r
    exact pathVertex_intermediate hn i j ks r
  right_inv p := by
    ext r
    by_cases h0 : r.val = 0
    · have hr : r = 0 := by ext; exact h0
      subst hr
      simp [p.start_eq]
    · by_cases hlast : r.val = n
      · have hr : r = Fin.last n := by ext; exact hlast
        subst hr
        simp [p.end_eq]
      · dsimp [pathVertex]
        rw [dif_neg h0, dif_neg hlast]
        congr 1
        ext
        dsimp
        omega

/--
OET anchor: oet-e4154c34e95d3c23
`n = 1` 时正值判据路径条件退化为单个矩阵条目 `[M^{(1)}]_{i → j} > 0`（`CH02-P14`）。
-/
theorem exists_isPositivePath_one_iff {I : Type*}
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (∃ ks : IntermediateSeq I 1, IsPositivePath (le_rfl : 1 ≤ 1) M i j ks) ↔
      0 < channelEntry (M 0) i j := by
  constructor
  · rintro ⟨ks, hks⟩
    simpa using hks 0
  · intro h
    refine ⟨Fin.elim0, fun m => ?_⟩
    fin_cases m
    simpa using h

end LCH02
```

```lean filename=LCH02/OperatorBounds.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import LCH02.MatrixProducts

namespace LCH02

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

/-!
# 第 2 章 算子界 · 有限复合与路径节群（LCH02）

覆盖 `obligations.json` 中与算子 Lipschitz / co-Lipschitz 矩阵界、受限域单调性、
两步与任意有限步链复合及零步边界相关的全部定义与定理义务。
-/

/--
OET anchor: oet-af85899693cc8750
**定义（全域合法 Lipschitz 矩阵谓词，`CH02-D01`）**：
对所有 `x, y ∈ dom ϕ` 与所有 `j ∈ I`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i → j} · d_i(x, y)`。
-/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/--
OET anchor: oet-af85899693cc8750
**定义（全域 Lipschitz 矩阵证书族 `mathscr_L(ϕ)`，`CH02-D01`）**。
-/
def lipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限合法 Lipschitz 矩阵谓词，`CH02-D01`）**：
对子集 `U ⊆ dom ϕ`，在 `U` 上对所有 `x, y ∈ U` 与所有 `j ∈ I` 满足距离放缩上界。
-/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/--
OET anchor: oet-af85899693cc8750
**定义（子集受限 Lipschitz 矩阵证书族 `mathscr_L(ϕ)|_U`，`CH02-D01`）**。
-/
def restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

@[simp]
theorem restrictedLipMatrices_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedLipMatrices d ϕ (dom ϕ) = lipMatrices d ϕ := by
  ext L
  simp [restrictedLipMatrices, IsRestrictedLipMatrix, lipMatrices, IsLipMatrix]

/--
OET anchor: oet-af85899693cc8750
**定义（含非空条件的子集受限 co-Lipschitz 矩阵谓词，`CH02-D02`）**：
按正文约定，凡出现 `mathscr_K(ϕ)|_U` 均包含非空性条件 `U ≠ ∅` 及定义域包含 `U ⊆ dom ϕ`，
且对所有 `x, y ∈ U` 与所有 `j ∈ I` 满足 `d_j(ϕ(x), ϕ(y)) ≥ ∑_{i ∈ I} K_{i → j} · d_i(x, y)`。
-/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/--
OET anchor: oet-af85899693cc8750
**定义（含非空条件的子集受限 co-Lipschitz 矩阵证书族 `mathscr_K(ϕ)|_U`，`CH02-D02`）**。
-/
def restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

theorem IsRestrictedCoLipMatrix.nonempty {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) :
    U.Nonempty :=
  hK.1

theorem IsRestrictedCoLipMatrix.subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) :
    U ⊆ dom ϕ :=
  hK.2.1

/--
OET anchor: oet-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界，指标集等于单点集形式，`CH02-P01`）**：
当 `I = {i}` 时，全域 Lip 矩阵条件等价于标量不等式
`d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} · d_i(x, y)`（`∀ x, y ∈ dom ϕ`）。
-/
theorem lipMatrices_mem_iff_scalar_of_univ_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (i : I) (hi : (Finset.univ : Finset I) = {i}) :
    L ∈ lipMatrices d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    rwa [hi, Finset.sum_singleton] at h
  · intro hscalar x hx y hy j
    have hj : j = i := by
      have hj_mem : j ∈ (Finset.univ : Finset I) := Finset.mem_univ j
      rw [hi, Finset.mem_singleton] at hj_mem
      exact hj_mem
    subst hj
    rw [hi, Finset.sum_singleton]
    exact hscalar x hx y hy

/--
OET anchor: oet-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界，基数 `|I| = 1` 形式，`CH02-P01`）**：
当 `Fintype.card I = 1` 且 `i ∈ I` 时，全域 Lip 矩阵条件退化为单个标量不等式。
-/
theorem lipMatrices_mem_iff_scalar_of_card_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hcard : Fintype.card I = 1) (i : I) :
    L ∈ lipMatrices d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  have hi : (Finset.univ : Finset I) = {i} := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Fintype.card_le_one_iff.mp hcard.le k i
  exact lipMatrices_mem_iff_scalar_of_univ_singleton d ϕ L i hi

/--
OET anchor: oet-c4369c63c86cbacf
单分量受限 Lip 矩阵标量界等价形式（`CH02-P01`）。
-/
theorem restrictedLipMatrices_mem_iff_scalar_of_univ_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ)
    (L : GaugeMatrix I) (i : I) (hi : (Finset.univ : Finset I) = {i}) :
    L ∈ restrictedLipMatrices d ϕ U ↔
      ∀ x ∈ U, ∀ y ∈ U,
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  constructor
  · intro hL x hx y hy
    have h := hL.2 x hx y hy i
    rwa [hi, Finset.sum_singleton] at h
  · intro hscalar
    refine ⟨hU, fun x hx y hy j => ?_⟩
    have hj : j = i := by
      have hj_mem : j ∈ (Finset.univ : Finset I) := Finset.mem_univ j
      rw [hi, Finset.mem_singleton] at hj_mem
      exact hj_mem
    subst hj
    rw [hi, Finset.sum_singleton]
    exact hscalar x hx y hy

/--
OET anchor: oet-4ff5c58d71e1651f
**引理 2.1（受限 Lip 矩阵族的单调性 / 反单调性，`CH02-P02`）**：
若 `U ⊆ V ⊆ dom ϕ`，则 `mathscr_L(ϕ)|_V ⊆ mathscr_L(ϕ)|_U`。
-/
theorem restrictedLipMatrices_anti {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    restrictedLipMatrices d ϕ V ⊆ restrictedLipMatrices d ϕ U := by
  intro L hL
  refine ⟨hUV.trans hV, fun x hx y hy j => ?_⟩
  exact hL.2 x (hUV hx) y (hUV hy) j

/--
OET anchor: oet-4ff5c58d71e1651f
**引理 2.1 特例（全域 Lip 证书可限制到任意定义域子集，`CH02-P03`）**：
对任意 `U ⊆ dom ϕ`，有 `mathscr_L(ϕ) ⊆ mathscr_L(ϕ)|_U`。
-/
theorem lipMatrices_subset_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hU : U ⊆ dom ϕ) :
    lipMatrices d ϕ ⊆ restrictedLipMatrices d ϕ U := by
  rw [← restrictedLipMatrices_dom d ϕ]
  exact restrictedLipMatrices_anti d ϕ hU Set.Subset.rfl

/-- 复合定义域包含关系引理（左因子输入域）：`U₁ ⊆ dom(ϕ₂ ∘ ϕ₁) → U₁ ⊆ dom ϕ₁`。 -/
theorem subset_dom_left_of_subset_dom_comp {X : Type} {bot : X}
    {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    U₁ ⊆ dom ϕ₁ := by
  intro x hx hbot
  have hcomp : ϕ₂.func (ϕ₁.func x) ≠ bot := hU₁ hx
  rw [hbot, ϕ₂.preserves_bot] at hcomp
  exact hcomp rfl

/--
OET anchor: oet-193cebcc1a7f9259
复合定义域包含关系引理（精确中间像域，`CH02-P04`）：
若 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，记 `U₂ = ϕ₁(U₁)`，则 `U₂ ⊆ dom ϕ₂`。
-/
theorem image_subset_dom_of_subset_dom_comp {X : Type} {bot : X}
    {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro y ⟨x, hx, rfl⟩
  exact hU₁ hx

/-- 两步复合定义域的精确充要刻画：`U₁ ⊆ dom(ϕ₂ ∘ ϕ₁) ↔ U₁ ⊆ dom ϕ₁ ∧ ϕ₁(U₁) ⊆ dom ϕ₂`。 -/
theorem subset_dom_comp_iff {X : Type} {bot : X}
    (ϕ₂ ϕ₁ : Operator X bot) (U₁ : Set X) :
    U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁) ↔
      U₁ ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  constructor
  · intro hU₁
    exact ⟨subset_dom_left_of_subset_dom_comp hU₁, image_subset_dom_of_subset_dom_comp hU₁⟩
  · rintro ⟨_, hU₂⟩ x hx
    exact hU₂ ⟨x, hx, rfl⟩

/--
OET anchor: oet-193cebcc1a7f9259
**命题 2.2（Lip 矩阵复合律，`CH02-P04`）**：
设 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，精确中间像集 `U₂ = ϕ₁(U₁)`。
若 `L₁ ∈ mathscr_L(ϕ₁)|_{U₁}` 且 `L₂ ∈ mathscr_L(ϕ₂)|_{U₂}`，
则 `L₂ · L₁ ∈ mathscr_L(ϕ₂ ∘ ϕ₁)|_{U₁}`。
-/
theorem restrictedLipMatrices_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₂ ϕ₁ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁))
    {L₂ L₁ : GaugeMatrix I}
    (hL₁ : L₁ ∈ restrictedLipMatrices d ϕ₁ U₁)
    (hL₂ : L₂ ∈ restrictedLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul L₂ L₁ ∈ restrictedLipMatrices d (operator_compose ϕ₂ ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((operator_compose ϕ₂ ϕ₁).func x) ((operator_compose ϕ₂ ϕ₁).func y)
        = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, channelEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) :=
        hL₂.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ ≤ ∑ k : I, channelEntry L₂ k j * (∑ i : I, channelEntry L₁ i k * d i x y) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (hL₁.2 x hx y hy k) (zero_le _)
    _ = ∑ k : I, ∑ i : I, channelEntry L₂ k j * (channelEntry L₁ i k * d i x y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.mul_sum _ _ _
    _ = ∑ i : I, ∑ k : I, (channelEntry L₂ k j * channelEntry L₁ i k) * d i x y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc]
    _ = ∑ i : I, (∑ k : I, channelEntry L₂ k j * channelEntry L₁ i k) * d i x y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i : I, channelEntry (gaugeMatrixMul L₂ L₁) i j * d i x y := by
        simp [Matrix.mul_apply]

/--
OET anchor: oet-893b1d33535f7245
**引理 2.3（受限 co-Lip 矩阵族的单调性 / 反单调性，`CH02-P05`）**：
若 `∅ ≠ U ⊆ V ⊆ dom ϕ`，则 `mathscr_K(ϕ)|_V ⊆ mathscr_K(ϕ)|_U`。
-/
theorem restrictedCoLipMatrices_anti {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hU_ne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    restrictedCoLipMatrices d ϕ V ⊆ restrictedCoLipMatrices d ϕ U := by
  intro K hK
  refine ⟨hU_ne, hUV.trans hV, fun x hx y hy j => ?_⟩
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/--
OET anchor: oet-893b1d33535f7245
**引理 2.3 特例（全域 co-Lip 证书可限制到任意非空定义域子集，`CH02-P06`）**：
对任意非空子集 `U ⊆ dom ϕ`，有 `mathscr_K(ϕ)|_{dom ϕ} ⊆ mathscr_K(ϕ)|_U`。
-/
theorem globalCoLipMatrices_subset_restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    restrictedCoLipMatrices d ϕ (dom ϕ) ⊆ restrictedCoLipMatrices d ϕ U :=
  restrictedCoLipMatrices_anti d ϕ hU_ne hU Set.Subset.rfl

/--
OET anchor: oet-88784dcbfff0ea66
受限域版本：若 `U` 中存在点对使 `d_j(ϕ(x), ϕ(y)) = 0` 且 `d_i(x, y) > 0`，
则任一受限 co-Lip 矩阵 `K ∈ mathscr_K(ϕ)|_U` 满足 `K_{i → j} = 0`（`CH02-P07`）。
-/
theorem channelEntry_eq_zero_of_restrictedCoLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {i j : I} {K : GaugeMatrix I}
    (h_witness : ∃ x ∈ U, ∃ y ∈ U, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) :
    channelEntry K i j = 0 := by
  rcases h_witness with ⟨x, hx, y, hy, h_out_zero, h_in_pos⟩
  have h_le : ∑ k : I, channelEntry K k j * d k x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    hK.2.2 x hx y hy j
  rw [h_out_zero] at h_le
  have h_term_le : channelEntry K i j * d i x y ≤ ∑ k : I, channelEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k => channelEntry K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have h_mul_zero : channelEntry K i j * d i x y = 0 :=
    le_antisymm (h_term_le.trans h_le) (zero_le _)
  rcases mul_eq_zero.mp h_mul_zero with hK0 | hd0
  · exact hK0
  · exact absurd hd0 (ne_of_gt h_in_pos)

/--
OET anchor: oet-88784dcbfff0ea66
**注（co-Lip 条目为零的充分条件，`CH02-P07`）**：
若存在 `x, y ∈ dom ϕ` 使 `d_j(ϕ(x), ϕ(y)) = 0` 且 `d_i(x, y) > 0`，
则任一全域 co-Lip 矩阵 `K ∈ mathscr_K(ϕ)|_{dom ϕ}` 必满足 `K_{i → j} = 0`。
-/
theorem channelEntry_eq_zero_of_globalCoLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {i j : I} {K : GaugeMatrix I}
    (h_witness : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y)
    (hK : K ∈ restrictedCoLipMatrices d ϕ (dom ϕ)) :
    channelEntry K i j = 0 :=
  channelEntry_eq_zero_of_restrictedCoLip d ϕ h_witness hK

/--
OET anchor: oet-0f256e6f1d38a612
两步 co-Lip 复合中的精确中间像域非空性与定义域包含引理（`CH02-P08`）：
由 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)` 与 `K₁ ∈ mathscr_K(ϕ₁)|_{U₁}`，推出中间像域 `U₂ = ϕ₁(U₁)` 非空且 `U₂ ⊆ dom ϕ₂`。
-/
theorem image_nonempty_and_subset_dom_of_restrictedCoLip {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ₂ ϕ₁ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁))
    {K₁ : GaugeMatrix I} (hK₁ : K₁ ∈ restrictedCoLipMatrices d ϕ₁ U₁) :
    (operator_image ϕ₁ U₁).Nonempty ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ :=
  ⟨hK₁.1.image ϕ₁.func, image_subset_dom_of_subset_dom_comp hU₁⟩

/--
OET anchor: oet-0f256e6f1d38a612
**命题 2.4（co-Lip 矩阵复合律，`CH02-P08`）**：
设 `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`，精确中间像集 `U₂ = ϕ₁(U₁)`。
若 `K₁ ∈ mathscr_K(ϕ₁)|_{U₁}` 且 `K₂ ∈ mathscr_K(ϕ₂)|_{U₂}`，
则 `K₂ · K₁ ∈ mathscr_K(ϕ₂ ∘ ϕ₁)|_{U₁}`。
-/
theorem restrictedCoLipMatrices_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₂ ϕ₁ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (operator_compose ϕ₂ ϕ₁))
    {K₂ K₁ : GaugeMatrix I}
    (hK₁ : K₁ ∈ restrictedCoLipMatrices d ϕ₁ U₁)
    (hK₂ : K₂ ∈ restrictedCoLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul K₂ K₁ ∈ restrictedCoLipMatrices d (operator_compose ϕ₂ ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, channelEntry (gaugeMatrixMul K₂ K₁) i j * d i x y
        = ∑ i : I, (∑ k : I, channelEntry K₂ k j * channelEntry K₁ i k) * d i x y := by
            simp [Matrix.mul_apply]
    _ = ∑ i : I, ∑ k : I, (channelEntry K₂ k j * channelEntry K₁ i k) * d i x y := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, channelEntry K₂ k j * (channelEntry K₁ i k * d i x y) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
            rw [mul_assoc]
    _ = ∑ k : I, channelEntry K₂ k j * (∑ i : I, channelEntry K₁ i k * d i x y) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
    _ ≤ ∑ k : I, channelEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
            refine Finset.sum_le_sum fun k _ => ?_
            exact mul_le_mul_of_nonneg_left (hK₁.2.2 x hx y hy k) (zero_le _)
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
            hK₂.2.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ = d j ((operator_compose ϕ₂ ϕ₁).func x) ((operator_compose ϕ₂ ϕ₁).func y) := rfl

/--
OET anchor: oet-c80171fa685dc795
**定义（按作用次序索引的有限复合算子 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`，`CH02-D05`）**：
`k = 0` 时取恒等算子 `operator_identity`；`k + 1` 时在第 `k` 步前缀复合之后作用 `ϕ_k`。
-/
def finiteComp {X : Type} {bot : X} :
    (k : ℕ) → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => operator_identity
  | k + 1, ϕ => operator_compose (ϕ (Fin.last k)) (finiteComp k (ϕ ∘ Fin.castSucc))

@[simp]
theorem finiteComp_zero {X : Type} {bot : X} (ϕ : Fin 0 → Operator X bot) :
    finiteComp 0 ϕ = operator_identity := rfl

@[simp]
theorem finiteComp_one {X : Type} {bot : X} (ϕ : Fin 1 → Operator X bot) :
    finiteComp 1 ϕ = ϕ 0 := rfl

@[simp]
theorem finiteComp_succ {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) :
    finiteComp (k + 1) ϕ =
      operator_compose (ϕ (Fin.last k)) (finiteComp k (ϕ ∘ Fin.castSucc)) := rfl

/--
OET anchor: oet-c80171fa685dc795
链表示对应定理（`CH02-D05`）：
按正向作用步序 `1, ..., k` 给出的 `finiteComp k ϕ` 与冻结前置模块中按复合外层到内层排列的
`OperatorChain ((List.ofFn ϕ).reverse)` 完全相等。
-/
theorem finiteComp_eq_operatorChain {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) :
    finiteComp k ϕ = OperatorChain ((List.ofFn ϕ).reverse) := by
  induction k with
  | zero =>
      rfl
  | succ m ih =>
      rw [finiteComp_succ, ih, List.ofFn_succ']
      simp [List.concat_eq_append, OperatorChain, operator_compose]
      rfl

theorem finiteComp_eq_reverse_prod {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) :
    finiteComp k ϕ = ((List.ofFn ϕ).reverse).prod := by
  rw [finiteComp_eq_operatorChain, operator_chain_eq_prod]

/-- 反向链表示对应（`CH02-D05`）：任意正向算子列表 `ϕs = [ϕ₁, ..., ϕₖ]` 的逆序 `OperatorChain` 等于 `finiteComp`。 -/
theorem operatorChain_reverse_eq_finiteComp {X : Type} {bot : X}
    (ϕs : List (Operator X bot)) :
    OperatorChain ϕs.reverse = finiteComp ϕs.length ϕs.get := by
  rw [finiteComp_eq_operatorChain, List.ofFn_get]

/--
OET anchor: oet-c80171fa685dc795
**定义（复合链的实际中间像域序列 `U_1, ..., U_{k+1}`，`CH02-D05`）**：
由起始域 `U₁` 出发，递归定义 `U_0 = U₁`、`U_{m+1} = ϕ_m(U_m)`（`m : Fin k`）。
-/
def chainImageDomain {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) : Fin (k + 1) → Set X :=
  Fin.induction U₁ (fun m Um => operator_image (ϕ m) Um)

@[simp]
theorem chainImageDomain_zero {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    chainImageDomain k ϕ U₁ 0 = U₁ := by
  simp [chainImageDomain]

@[simp]
theorem chainImageDomain_succ {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    chainImageDomain k ϕ U₁ m.succ =
      operator_image (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc) := by
  simp [chainImageDomain]

/-- 前缀不变性：扩展第 `k + 1` 步算子不改变前 `k + 1` 个中间像域（`CH02-D05`）。 -/
theorem chainImageDomain_castSucc {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) (U₁ : Set X) (r : Fin (k + 1)) :
    chainImageDomain (k + 1) ϕ U₁ r.castSucc =
      chainImageDomain k (ϕ ∘ Fin.castSucc) U₁ r := by
  refine Fin.inductionOn r ?_ ?_
  · simp
  · intro m ih
    have h_cs : (m.succ : Fin (k + 1)).castSucc = (m.castSucc : Fin (k + 1)).succ := by
      ext
      rfl
    rw [h_cs, chainImageDomain_succ, chainImageDomain_succ, ih]
    rfl

/-- 终点像集刻画：第 `k + 1` 个域 `U_{k+1}` 恰好等于全复合 `c_k` 对 `U₁` 的像集（`CH02-D05`）。 -/
theorem chainImageDomain_last_eq_image_finiteComp {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    chainImageDomain k ϕ U₁ (Fin.last k) = operator_image (finiteComp k ϕ) U₁ := by
  induction k with
  | zero =>
      change U₁ = id '' U₁
      simp
  | succ m ih =>
      have h_last : (Fin.last (m + 1)) = (Fin.last m).succ := by
        ext
        rfl
      rw [h_last, chainImageDomain_succ, chainImageDomain_castSucc, ih]
      simp [operator_image, finiteComp_succ, operator_compose, Set.image_image]

/-- 中间像域非空性传播：若起始域 `U₁` 非空，则链上所有实际中间像域均非空（`CH02-D05`）。 -/
theorem chainImageDomain_nonempty {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) {U₁ : Set X} (hU₁ : U₁.Nonempty) :
    ∀ r : Fin (k + 1), (chainImageDomain k ϕ U₁ r).Nonempty := by
  intro r
  refine Fin.inductionOn r ?_ ?_
  · simpa using hU₁
  · intro m ih
    rw [chainImageDomain_succ]
    exact ih.image (ϕ m).func

/--
OET anchor: oet-c80171fa685dc795
链定义域递推保证引理（`CH02-D05`）：
若 `U₁ ⊆ dom(c_k)`，则对每一步 `m ∈ {1, ..., k}`，实际中间输入域满足 `U_m ⊆ dom(ϕ_m)`。
-/
theorem chainImageDomain_subset_dom {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ)) :
    ∀ m : Fin k, chainImageDomain k ϕ U₁ m.castSucc ⊆ dom (ϕ m) := by
  induction k with
  | zero =>
      intro m
      exact Fin.elim0 m
  | succ n ih =>
      rw [finiteComp_succ, subset_dom_comp_iff] at hU₁
      rcases hU₁ with ⟨h_init, h_last⟩
      intro m
      refine Fin.lastCases ?_ ?_ m
      · rw [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp]
        exact h_last
      · intro s
        have h_cs : s.castSucc.castSucc = (s.castSucc : Fin (n + 1)).castSucc := rfl
        rw [h_cs, chainImageDomain_castSucc]
        exact ih (ϕ ∘ Fin.castSucc) h_init s

/-- 正长度链（`k ≥ 1`）定义域递推充要刻画（`CH02-D05`）：
`U₁ ⊆ dom(c_k)` 当且仅当每一步实际中间输入域满足 `U_m ⊆ dom(ϕ_m)`。 -/
theorem chainImageDomain_subset_dom_iff {X : Type} {bot : X}
    (k : ℕ) (hk : 1 ≤ k) (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    U₁ ⊆ dom (finiteComp k ϕ) ↔
      ∀ m : Fin k, chainImageDomain k ϕ U₁ m.castSucc ⊆ dom (ϕ m) := by
  constructor
  · exact chainImageDomain_subset_dom k ϕ
  · induction k with
    | zero => exact absurd hk (Nat.not_succ_le_zero 0)
    | succ n ih =>
        cases n with
        | zero =>
            intro h
            simpa using h 0
        | succ r =>
            intro h
            rw [finiteComp_succ, subset_dom_comp_iff]
            constructor
            · apply ih (Nat.succ_pos r)
              intro s
              have hs := h s.castSucc
              rwa [chainImageDomain_castSucc] at hs
            · have hlast := h (Fin.last (r + 1))
              rwa [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp] at hlast

/-- 由链起始域条件 `U₁ ⊆ dom(c_k)` 与第 `m` 步逐点不等式构造局部 Lip 证书 `L_m ∈ mathscr_L(ϕ_m)|_{U_m}`（`CH02-P09`）。 -/
theorem step_mem_restrictedLipMatrices_of_chain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : ℕ} {ϕ : Fin k → Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ)) (m : Fin k) (Lm : GaugeMatrix I)
    (h_bound : ∀ x ∈ chainImageDomain k ϕ U₁ m.castSucc,
      ∀ y ∈ chainImageDomain k ϕ U₁ m.castSucc, ∀ j : I,
        d j ((ϕ m).func x) ((ϕ m).func y) ≤ ∑ i : I, channelEntry Lm i j * d i x y) :
    Lm ∈ restrictedLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc) :=
  ⟨chainImageDomain_subset_dom k ϕ hU₁ m, h_bound⟩

/-- 由链起始域非空且 `U₁ ⊆ dom(c_k)` 与第 `m` 步逐点下界不等式构造局部 co-Lip 证书 `K_m ∈ mathscr_K(ϕ_m)|_{U_m}`（`CH02-P10`）。 -/
theorem step_mem_restrictedCoLipMatrices_of_chain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : ℕ} {ϕ : Fin k → Operator X bot} {U₁ : Set X}
    (hU₁_ne : U₁.Nonempty) (hU₁ : U₁ ⊆ dom (finiteComp k ϕ))
    (m : Fin k) (Km : GaugeMatrix I)
    (h_bound : ∀ x ∈ chainImageDomain k ϕ U₁ m.castSucc,
      ∀ y ∈ chainImageDomain k ϕ U₁ m.castSucc, ∀ j : I,
        ∑ i : I, channelEntry Km i j * d i x y ≤ d j ((ϕ m).func x) ((ϕ m).func y)) :
    Km ∈ restrictedCoLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc) :=
  ⟨chainImageDomain_nonempty k ϕ hU₁_ne m.castSucc,
    chainImageDomain_subset_dom k ϕ hU₁ m, h_bound⟩

/--
OET anchor: oet-c80171fa685dc795
**推论 2.5(i)（有限复合的局部 Lip 矩阵界，`CH02-P09`）**：
设 `k ≥ 1`，`c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`，起始子集 `U₁ ⊆ dom(c_k)`，实际中间像域 `U_{m+1} = ϕ_m(U_m)`。
若各单步满足 `L^{(m)} ∈ mathscr_L(ϕ_m)|_{U_m}`，则有序连乘满足
`L^{(k)} · ⋯ · L^{(1)} ∈ mathscr_L(c_k)|_{U₁}`。
-/
theorem finiteComp_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ))
    (L : Fin k → GaugeMatrix I)
    (hL : ∀ m : Fin k,
      L m ∈ restrictedLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc)) :
    nonemptyMatrixProd k hk L ∈ restrictedLipMatrices d (finiteComp k ϕ) U₁ := by
  induction k with
  | zero => exact absurd hk (Nat.not_succ_le_zero 0)
  | succ n ih =>
      cases n with
      | zero =>
          simpa [nonemptyMatrixProd, finiteComp] using hL 0
      | succ r =>
          have hr : 1 ≤ r + 1 := Nat.succ_pos r
          have hr' : 1 ≤ r + 2 := Nat.succ_pos (r + 1)
          rw [nonemptyMatrixProd_succ hr hr', finiteComp_succ]
          have hU_init : U₁ ⊆ dom (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) :=
            subset_dom_left_of_subset_dom_comp hU₁
          have hL_init : ∀ m : Fin (r + 1),
              (L ∘ Fin.castSucc) m ∈
                restrictedLipMatrices d ((ϕ ∘ Fin.castSucc) m)
                  (chainImageDomain (r + 1) (ϕ ∘ Fin.castSucc) U₁ m.castSucc) := by
            intro m
            have hm := hL m.castSucc
            rwa [chainImageDomain_castSucc] at hm
          have h_ih := ih hr (ϕ ∘ Fin.castSucc) hU_init (L ∘ Fin.castSucc) hL_init
          have hL_last := hL (Fin.last (r + 1))
          rw [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp] at hL_last
          exact restrictedLipMatrices_comp d (ϕ (Fin.last (r + 1)))
            (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) hU₁ h_ih hL_last

/-- `OperatorChain` 列表接口下的有限复合局部 Lip 矩阵连乘界（`CH02-P09`）。 -/
theorem operatorChain_reverse_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕs : List (Operator X bot)) (hϕs : 1 ≤ ϕs.length)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (OperatorChain ϕs.reverse))
    (L : Fin ϕs.length → GaugeMatrix I)
    (hL : ∀ m : Fin ϕs.length,
      L m ∈ restrictedLipMatrices d (ϕs.get m)
        (chainImageDomain ϕs.length ϕs.get U₁ m.castSucc)) :
    nonemptyMatrixProd ϕs.length hϕs L ∈
      restrictedLipMatrices d (OperatorChain ϕs.reverse) U₁ := by
  rw [operatorChain_reverse_eq_finiteComp] at hU₁ ⊢
  exact finiteComp_restrictedLipMatrices d ϕs.length hϕs ϕs.get hU₁ L hL

/--
OET anchor: oet-c80171fa685dc795
**推论 2.5(ii)（有限复合的局部 co-Lip 矩阵界，`CH02-P10`）**：
设 `k ≥ 1`，`c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`，起始子集 `U₁ ⊆ dom(c_k)`，实际中间像域 `U_{m+1} = ϕ_m(U_m)`。
若各单步满足 `K^{(m)} ∈ mathscr_K(ϕ_m)|_{U_m}`，则有序连乘满足
`K^{(k)} · ⋯ · K^{(1)} ∈ mathscr_K(c_k)|_{U₁}`。
-/
theorem finiteComp_restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (finiteComp k ϕ))
    (K : Fin k → GaugeMatrix I)
    (hK : ∀ m : Fin k,
      K m ∈ restrictedCoLipMatrices d (ϕ m) (chainImageDomain k ϕ U₁ m.castSucc)) :
    nonemptyMatrixProd k hk K ∈ restrictedCoLipMatrices d (finiteComp k ϕ) U₁ := by
  induction k with
  | zero => exact absurd hk (Nat.not_succ_le_zero 0)
  | succ n ih =>
      cases n with
      | zero =>
          simpa [nonemptyMatrixProd, finiteComp] using hK 0
      | succ r =>
          have hr : 1 ≤ r + 1 := Nat.succ_pos r
          have hr' : 1 ≤ r + 2 := Nat.succ_pos (r + 1)
          rw [nonemptyMatrixProd_succ hr hr', finiteComp_succ]
          have hU_init : U₁ ⊆ dom (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) :=
            subset_dom_left_of_subset_dom_comp hU₁
          have hK_init : ∀ m : Fin (r + 1),
              (K ∘ Fin.castSucc) m ∈
                restrictedCoLipMatrices d ((ϕ ∘ Fin.castSucc) m)
                  (chainImageDomain (r + 1) (ϕ ∘ Fin.castSucc) U₁ m.castSucc) := by
            intro m
            have hm := hK m.castSucc
            rwa [chainImageDomain_castSucc] at hm
          have h_ih := ih hr (ϕ ∘ Fin.castSucc) hU_init (K ∘ Fin.castSucc) hK_init
          have hK_last := hK (Fin.last (r + 1))
          rw [chainImageDomain_castSucc, chainImageDomain_last_eq_image_finiteComp] at hK_last
          exact restrictedCoLipMatrices_comp d (ϕ (Fin.last (r + 1)))
            (finiteComp (r + 1) (ϕ ∘ Fin.castSucc)) hU₁ h_ih hK_last

/-- `OperatorChain` 列表接口下的有限复合局部 co-Lip 矩阵连乘界（`CH02-P10`）。 -/
theorem operatorChain_reverse_restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕs : List (Operator X bot)) (hϕs : 1 ≤ ϕs.length)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (OperatorChain ϕs.reverse))
    (K : Fin ϕs.length → GaugeMatrix I)
    (hK : ∀ m : Fin ϕs.length,
      K m ∈ restrictedCoLipMatrices d (ϕs.get m)
        (chainImageDomain ϕs.length ϕs.get U₁ m.castSucc)) :
    nonemptyMatrixProd ϕs.length hϕs K ∈
      restrictedCoLipMatrices d (OperatorChain ϕs.reverse) U₁ := by
  rw [operatorChain_reverse_eq_finiteComp] at hU₁ ⊢
  exact finiteComp_restrictedCoLipMatrices d ϕs.length hϕs ϕs.get hU₁ K hK

/-- 单位矩阵在分量距离求和下的恒等展开：`∑_{i ∈ I} I_{i → j} · d_i(x, y) = d_j(x, y)`。 -/
theorem sum_identityMatrix_mul_dist {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    ∑ i : I, channelEntry (identityMatrix (I := I)) i j * d i x y = d j x y := by
  simp [identityMatrix, Matrix.one_apply]

/--
OET anchor: oet-11006ddd8c43bfec
**注（恒等算子的全域单位 Lip 矩阵证书，`CH02-P11`）**：
`I ∈ mathscr_L(id_X)`。
-/
theorem identityMatrix_mem_lipMatrices {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    identityMatrix (I := I) ∈ lipMatrices d (operator_identity (X := X) (bot := bot)) := by
  intro x _ y _ j
  rw [sum_identityMatrix_mul_dist]
  rfl

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步恒等算子的受限单位 Lip 矩阵证书，`CH02-P11`）**：
对任意 `U ⊆ dom(id_X)`，`I ∈ mathscr_L(id_X)|_U`。
-/
theorem identityMatrix_mem_restrictedLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    identityMatrix (I := I) ∈
      restrictedLipMatrices d (operator_identity (X := X) (bot := bot)) U :=
  lipMatrices_subset_restrictedLipMatrices d operator_identity hU
    (identityMatrix_mem_lipMatrices d)

/--
OET anchor: oet-11006ddd8c43bfec
零步复合形式（`k = 0`，`CH02-P11`）：
矩阵空复合乘积 `matrixChainProd 0 L = I` 属于零步复合 `finiteComp 0 ϕ = id_X` 在 `U` 上的受限 Lip 证书族。
-/
theorem zeroStep_matrixChainProd_mem_restrictedLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Fin 0 → Operator X bot)
    (L : Fin 0 → GaugeMatrix I) {U : Set X}
    (hU : U ⊆ dom (finiteComp 0 ϕ)) :
    matrixChainProd 0 L ∈ restrictedLipMatrices d (finiteComp 0 ϕ) U :=
  identityMatrix_mem_restrictedLipMatrices d hU

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步恒等算子的受限单位 co-Lip 矩阵证书，`CH02-P12`）**：
对任意非空 `U ⊆ dom(id_X)`，`I ∈ mathscr_K(id_X)|_U`。
-/
theorem identityMatrix_mem_restrictedCoLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    identityMatrix (I := I) ∈
      restrictedCoLipMatrices d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU_ne, hU, fun x _ y _ j => ?_⟩
  rw [sum_identityMatrix_mul_dist]
  rfl

/--
OET anchor: oet-11006ddd8c43bfec
零步复合形式（`k = 0`，`CH02-P12`）：
对任意非空 `U ⊆ dom(c_0)`，矩阵空复合乘积 `matrixChainProd 0 K = I` 属于 `mathscr_K(c_0)|_U`。
-/
theorem zeroStep_matrixChainProd_mem_restrictedCoLipMatrices {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Fin 0 → Operator X bot)
    (K : Fin 0 → GaugeMatrix I) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (finiteComp 0 ϕ)) :
    matrixChainProd 0 K ∈ restrictedCoLipMatrices d (finiteComp 0 ϕ) U :=
  identityMatrix_mem_restrictedCoLipMatrices d hU_ne hU

/--
OET anchor: oet-11006ddd8c43bfec
**注（零步复合的单位矩阵双侧证书封装，`CH02-P11` / `CH02-P12`）**：
对任意非空 `U ⊆ dom(id_X)`，`I ∈ mathscr_L(id_X)|_U ∩ mathscr_K(id_X)|_U`。
-/
theorem identityMatrix_mem_lip_inter_coLip {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    identityMatrix (I := I) ∈
      restrictedLipMatrices d (operator_identity (X := X) (bot := bot)) U ∩
        restrictedCoLipMatrices d (operator_identity (X := X) (bot := bot)) U :=
  ⟨identityMatrix_mem_restrictedLipMatrices d hU,
    identityMatrix_mem_restrictedCoLipMatrices d hU_ne hU⟩

/-- 扩展规范空间语境下，恒等算子的全定义域 `dom(id_X) = X \ {bot}` 非空，故单位矩阵属于全域 co-Lip 族。 -/
theorem identityMatrix_mem_globalCoLipMatrices_of_gaugeSpace {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    identityMatrix (I := I) ∈
      restrictedCoLipMatrices d (operator_identity (X := X) (bot := bot))
        (dom (operator_identity (X := X) (bot := bot))) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  rcases (hd i₀).nonabsorbing with ⟨x₀, hx₀⟩
  exact identityMatrix_mem_restrictedCoLipMatrices d ⟨x₀, hx₀⟩ Set.Subset.rfl

end LCH02
```

```lean filename=Main.lean
import LCH02.MatrixProducts
import LCH02.OperatorBounds

/-!
# Main Entry Module · LCH02（有限复合与路径节群）

导入目标形式化模块 `LCH02.MatrixProducts` 与 `LCH02.OperatorBounds`，
完整覆盖 `obligations.json` 指定的全部 20 项交付义务。
-/
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
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.IsLipMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.lipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.IsRestrictedLipMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedLipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedLipMatrices_dom"
        }
      ],
      "representation": "对象与参数：给定分量扩展伪度量族 d : I → X → X → ENNReal（[Fintype I]）、算子 ϕ : Operator X bot、矩阵 L : GaugeMatrix I 及子集 U : Set X。全域谓词 IsLipMatrix 对 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I 要求 d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y，证书族 lipMatrices d ϕ 表示 ℒ(ϕ)。受限谓词 IsRestrictedLipMatrix 要求定义域约束 U ⊆ dom ϕ 且对 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I 满足同一距离放缩不等式，证书族 restrictedLipMatrices d ϕ U 表示 ℒ(ϕ)|_U，并由 restrictedLipMatrices_dom 证明 ℒ(ϕ)|_{dom ϕ} = ℒ(ϕ)。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.IsRestrictedCoLipMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedCoLipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.IsRestrictedCoLipMatrix.nonempty"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.IsRestrictedCoLipMatrix.subset_dom"
        }
      ],
      "representation": "对象与参数：d : I → X → X → ENNReal（[Fintype I]）、ϕ : Operator X bot、U : Set X、K : GaugeMatrix I。严格遵循正文约定“凡出现 𝒦(ϕ)|_U 均包含非空性条件 U ≠ ∅”，IsRestrictedCoLipMatrix 显式合取 U.Nonempty、U ⊆ dom ϕ 与 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)；restrictedCoLipMatrices d ϕ U 表示下界证书族 𝒦(ϕ)|_U。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.GaugeMatrix"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.channelEntry"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.channelEntry_apply"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.gaugeMatrixMul"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.channelEntry_mul"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.gaugeMatrixMul_assoc"
        }
      ],
      "representation": "对象与约定：GaugeMatrix I := Matrix I I ENNReal 取值于扩展非负实数 ENNReal，第一参数（行指标 j）为输出分量，第二参数（列指标 i）为输入分量。channelEntry M i j := M j i 精确编码正文行列约定 (M)_{ji} = M_{i → j}。gaugeMatrixMul M₂ M₁ := M₂ * M₁ 给出矩阵乘法，并由 channelEntry_mul 证明通道展开公式 (M₂ · M₁)_{i → j} = ∑ k : I, (M₂)_{k → j} * (M₁)_{i → k}。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.identityMatrix"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.channelEntry_identityMatrix"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.matrixChainProd"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.matrixChainProd_zero"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.matrixChainProd_succ"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.matrixChainProd_eq_reverse_prod"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.nonemptyMatrixProd"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.nonemptyMatrixProd_one"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.nonemptyMatrixProd_succ"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.nonemptyMatrixProd_eq_matrixChainProd"
        }
      ],
      "representation": "对象与结论：identityMatrix 定义扩展非负单位矩阵 I（满足 I_{i → j} = if i = j then 1 else 0）。matrixChainProd k M 定义带 k = 0 空乘积边界的有限有序连乘（matrixChainProd 0 M = identityMatrix，对应空复合乘积为单位矩阵）。nonemptyMatrixProd n hn M（1 ≤ n）定义无需 DecidableEq I 的有序非空矩阵连乘 M^{(n)} · ⋯ · M^{(1)}，n = 1 时直接退化为 M 0，并证明其与 matrixChainProd 及逆序列表连乘 ((List.ofFn M).reverse).prod 一致。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.finiteComp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.finiteComp_eq_operatorChain"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.finiteComp_eq_reverse_prod"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.operatorChain_reverse_eq_finiteComp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.chainImageDomain"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.chainImageDomain_zero"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.chainImageDomain_succ"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.chainImageDomain_last_eq_image_finiteComp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.chainImageDomain_nonempty"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.chainImageDomain_subset_dom"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.chainImageDomain_subset_dom_iff"
        }
      ],
      "representation": "对象与对应：finiteComp k ϕ 按正向步序 ϕ : Fin k → Operator X bot 定义有限复合 c_k = ϕ_k ∘ ⋯ ∘ ϕ_1（c_0 = id_X），并由 finiteComp_eq_operatorChain 与 operatorChain_reverse_eq_finiteComp 建立同冻结前置模块 OperatorChain（外层算子在列表首端）的双向精确对应。chainImageDomain k ϕ U₁ : Fin (k + 1) → Set X 递归定义实际中间像域 U_0 = U₁、U_{m+1} = operator_image (ϕ m) U_m，证明终点像域等于 operator_image c_k U₁，且 U₁ ⊆ dom c_k 递推保证每步 U_m ⊆ dom ϕ_m（k ≥ 1 时为充要条件）以及非空性沿链传播。",
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.IntermediateSeq"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.pathVertex"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.pathVertex_zero"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.pathVertex_last"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.pathStepEntry"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.IsPositivePath"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.HasZeroStep"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.IndexPath"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.intermediateSeqEquivIndexPath"
        }
      ],
      "representation": "对象与谓词：对 n ≥ 1，IntermediateSeq I n := Fin (n - 1) → I 表示中间指标序列 (k_1, ..., k_{n-1})（n = 1 时为唯一空序列 Fin 0 → I）；pathVertex hn i j ks 补齐起止指标约定 k_0 = i、k_n = j；同时给出带端点约束的完整路径结构 IndexPath I n i j 及其典范双射 intermediateSeqEquivIndexPath。pathStepEntry 表示第 m 层单步条目 [M^{(m)}]_{k_{m-1} → k_m}；IsPositivePath 为全正路径谓词 ∀ m : Fin n, 0 < pathStepEntry，HasZeroStep 为含零因子路径谓词 ∃ m : Fin n, pathStepEntry = 0。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.lipMatrices_mem_iff_scalar_of_univ_singleton"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.lipMatrices_mem_iff_scalar_of_card_one"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedLipMatrices_mem_iff_scalar_of_univ_singleton"
        }
      ],
      "representation": "前提、量词与结论：分别以 (Finset.univ : Finset I) = {i}（对应 I = {i}）和 Fintype.card I = 1（对应 |I| = 1 且 i : I）刻画单分量情形，证明 L ∈ lipMatrices d ϕ 当且仅当 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y，并给出受限域 U ⊆ dom ϕ 上的对应充要定理。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedLipMatrices_anti"
        }
      ],
      "representation": "前提、量词与结论：固定算子 ϕ : Operator X bot，对任意子集 U, V : Set X，若 hUV : U ⊆ V 且 hV : V ⊆ dom ϕ，则证书族满足反单调包含关系 restrictedLipMatrices d ϕ V ⊆ restrictedLipMatrices d ϕ U（即 ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U）。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.subset_dom_left_of_subset_dom_comp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.image_subset_dom_of_subset_dom_comp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.subset_dom_comp_iff"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedLipMatrices_comp"
        }
      ],
      "representation": "前提、量词与结论：对复合算子 operator_compose ϕ₂ ϕ₁（即 ϕ₂ ∘ ϕ₁）与起始子集 U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)，以 operator_image ϕ₁ U₁ 精确表示中间像域 U₂ = ϕ₁(U₁)，先由 image_subset_dom_of_subset_dom_comp 证明 U₂ ⊆ dom ϕ₂；再由 restrictedLipMatrices_comp 证明：若 L₁ ∈ ℒ(ϕ₁)|_{U₁} 且 L₂ ∈ ℒ(ϕ₂)|_{U₂}，则按复合次序的矩阵乘积 gaugeMatrixMul L₂ L₁ ∈ ℒ(ϕ₂ ∘ ϕ₁)|_{U₁}。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedCoLipMatrices_anti"
        }
      ],
      "representation": "前提、量词与结论：固定算子 ϕ : Operator X bot，对任意子集 U, V : Set X，若 hU_ne : U.Nonempty、hUV : U ⊆ V 且 hV : V ⊆ dom ϕ（对应 ∅ ≠ U ⊆ V ⊆ dom ϕ），则受限 co-Lip 证书族满足反单调包含 restrictedCoLipMatrices d ϕ V ⊆ restrictedCoLipMatrices d ϕ U（即 𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U）。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.channelEntry_eq_zero_of_restrictedCoLip"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.channelEntry_eq_zero_of_globalCoLip"
        }
      ],
      "representation": "前提、量词与结论：对算子 ϕ 与指标 i, j : I，若存在见证点对 ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ 使得 d j (ϕ.func x) (ϕ.func y) = 0 且 0 < d i x y，则对任意全域 co-Lip 证书 K ∈ restrictedCoLipMatrices d ϕ (dom ϕ)（即 𝒦(ϕ)|_{dom ϕ}），必有 channelEntry K i j = 0（即 K_{i → j} = 0）；同时给出任意受限域 U 上的推广形式。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.image_nonempty_and_subset_dom_of_restrictedCoLip"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.restrictedCoLipMatrices_comp"
        }
      ],
      "representation": "前提、量词与结论：对复合算子 operator_compose ϕ₂ ϕ₁ 与 U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)，精确中间像域为 U₂ = operator_image ϕ₁ U₁。image_nonempty_and_subset_dom_of_restrictedCoLip 从 K₁ ∈ 𝒦(ϕ₁)|_{U₁} 内置的 U₁.Nonempty 与复合定义域条件导出 U₂.Nonempty ∧ U₂ ⊆ dom ϕ₂；restrictedCoLipMatrices_comp 证明若 K₁ ∈ 𝒦(ϕ₁)|_{U₁} 且 K₂ ∈ 𝒦(ϕ₂)|_{U₂}，则 gaugeMatrixMul K₂ K₁ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-P04"
      ]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.sum_identityMatrix_mul_dist"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.identityMatrix_mem_lipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.identityMatrix_mem_restrictedLipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.zeroStep_matrixChainProd_mem_restrictedLipMatrices"
        }
      ],
      "representation": "前提、量词与结论：对零步复合 c_0 = finiteComp 0 ϕ = operator_identity（id_X）与空乘积 matrixChainProd 0 L = identityMatrix（I），证明单位矩阵属于全域 Lip 族 lipMatrices d operator_identity，且对任意 U ⊆ dom operator_identity 有 identityMatrix ∈ restrictedLipMatrices d operator_identity U（以及零步链形式 matrixChainProd 0 L ∈ ℒ(c_0)|_U）。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P03"
      ]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.identityMatrix_mem_restrictedCoLipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.zeroStep_matrixChainProd_mem_restrictedCoLipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.identityMatrix_mem_lip_inter_coLip"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.identityMatrix_mem_globalCoLipMatrices_of_gaugeSpace"
        }
      ],
      "representation": "前提、量词与结论：对任意满足 U.Nonempty 且 U ⊆ dom operator_identity 的子集 U，证明单位矩阵满足 identityMatrix ∈ restrictedCoLipMatrices d operator_identity U（零步链形式为 matrixChainProd 0 K ∈ 𝒦(c_0)|_U），并合并封装正文原式 identityMatrix ∈ ℒ(id_X)|_U ∩ 𝒦(id_X)|_U，以及扩展规范空间下全定义域 dom(id_X) 上的全域特例。",
      "dependencies": [
        "CH02-D01",
        "CH02-D02",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P11"
      ]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.channelEntry_nonemptyMatrixProd_pos_iff"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.exists_isPositivePath_one_iff"
        }
      ],
      "representation": "前提、量词与结论：对任意正整数 n ≥ 1（hn : 1 ≤ n，含 n = 1）、扩展非负矩阵族 M : Fin n → GaugeMatrix I（[Fintype I]）及任意指标 i, j : I，证明 0 < channelEntry (nonemptyMatrixProd n hn M) i j 当且仅当 ∃ ks : IntermediateSeq I n, IsPositivePath hn M i j ks（存在至少一条沿路径所有单步矩阵条目均严格正的指标序列）；并由 exists_isPositivePath_one_iff 显式证明 n = 1 时退化为 0 < channelEntry (M 0) i j。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06",
        "CH02-P13"
      ]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.lipMatrices_subset_restrictedLipMatrices"
        }
      ],
      "representation": "前提、量词与结论：固定算子 ϕ : Operator X bot，对任意定义域子集 U ⊆ dom ϕ，证明全域 Lip 证书族可限制到 U：lipMatrices d ϕ ⊆ restrictedLipMatrices d ϕ U（即 ℒ(ϕ) ⊆ ℒ(ϕ)|_U）。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-P02"
      ]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.globalCoLipMatrices_subset_restrictedCoLipMatrices"
        }
      ],
      "representation": "前提、量词与结论：固定算子 ϕ : Operator X bot，对任意满足 U.Nonempty 且 U ⊆ dom ϕ 的非空定义域子集 U，证明全域 co-Lip 证书族可限制到 U：restrictedCoLipMatrices d ϕ (dom ϕ) ⊆ restrictedCoLipMatrices d ϕ U（即 𝒦(ϕ)|_{dom ϕ} ⊆ 𝒦(ϕ)|_U）。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-P05"
      ]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.step_mem_restrictedLipMatrices_of_chain"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.finiteComp_restrictedLipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.operatorChain_reverse_restrictedLipMatrices"
        }
      ],
      "representation": "前提、量词与结论：对任意正长度链 k ≥ 1（hk : 1 ≤ k）、算子序列 ϕ : Fin k → Operator X bot、起始子集 U₁ ⊆ dom(finiteComp k ϕ) 及递归实际中间像域 U_m = chainImageDomain k ϕ U₁ m.castSucc，由逐步局部证书 ∀ m : Fin k, L m ∈ ℒ(ϕ_m)|_{U_m} 经有限归纳建立全链连乘证书 nonemptyMatrixProd k hk L ∈ ℒ(finiteComp k ϕ)|_{U₁}；同时提供从 U₁ ⊆ dom c_k 与单步不等式建立单步证书的构造引理及 OperatorChain 列表形式推论。",
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
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.step_mem_restrictedCoLipMatrices_of_chain"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.finiteComp_restrictedCoLipMatrices"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LCH02.operatorChain_reverse_restrictedCoLipMatrices"
        }
      ],
      "representation": "前提、量词与结论：对任意正长度链 k ≥ 1（hk : 1 ≤ k）、算子序列 ϕ : Fin k → Operator X bot、起始子集 U₁ ⊆ dom(finiteComp k ϕ) 及递归实际中间像域 U_m = chainImageDomain k ϕ U₁ m.castSucc，由逐步局部下界证书 ∀ m : Fin k, K m ∈ 𝒦(ϕ_m)|_{U_m} 经有限归纳建立全链连乘证书 nonemptyMatrixProd k hk K ∈ 𝒦(finiteComp k ϕ)|_{U₁}；同时提供从 U₁.Nonempty ∧ U₁ ⊆ dom c_k 与单步下界建立单步证书的构造引理及 OperatorChain 列表形式推论。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P04",
        "CH02-P08"
      ]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.channelEntry_nonemptyMatrixProd_eq_sum_pathWeight"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.channelEntry_nonemptyMatrixProd_eq_zero_iff"
        },
        {
          "file": "LCH02/MatrixProducts.lean",
          "name": "LCH02.all_hasZeroStep_one_iff"
        }
      ],
      "representation": "前提、量词与结论：对任意正整数 n ≥ 1（hn : 1 ≤ n，含 n = 1）、扩展非负矩阵族 M : Fin n → GaugeMatrix I（[Fintype I]）及任意指标 i, j : I，先由 channelEntry_nonemptyMatrixProd_eq_sum_pathWeight 建立完整的路径乘积求和展开，再由 channelEntry_nonemptyMatrixProd_eq_zero_iff 证明 channelEntry (nonemptyMatrixProd n hn M) i j = 0 当且仅当 ∀ ks : IntermediateSeq I n, HasZeroStep hn M i j ks（每条指标路径至少存在一个层级单步条目为零）；并由 all_hasZeroStep_one_iff 显式证明 n = 1 时退化为 channelEntry (M 0) i j = 0。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06"
      ]
    }
  ]
}
```
