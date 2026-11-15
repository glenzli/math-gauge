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
