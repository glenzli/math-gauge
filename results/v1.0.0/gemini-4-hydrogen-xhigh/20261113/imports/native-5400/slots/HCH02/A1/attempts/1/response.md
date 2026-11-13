{}
已完成第 2 章（[02-operator-bounds.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/source/02-operator-bounds.md)）及 [obligations.json](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/obligations.json) 中全部 40 项义务（`HC02-D01` 至 `HC02-D08`、`HC02-P01` 至 `HC02-P32`）的 Lean 4.29.1 形式化，并与冻结前置模块 [gauge_space.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean) 及 [operator_space.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean) 对接，未修改或覆盖 `formal_oet/` 中的任何文件。

下面按要求以独立命名代码块全文提交全部源码文件与对齐清单。

```lean filename=Ch02Matrices.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# Chapter 2 — Matrices, Ordered Products, Paths, and Sparsity

Formalizes the matrix representation, display-matrix correspondence, multiplication,
identity matrix, ordered finite products, finite index paths, and channel sparsity
predicates for Chapter 2 (`source/02-operator-bounds.md`).
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-- Input-first generalized non-negative matrix over `I`: `M i j` represents $M_{i \to j}$,
i.e. input component `i` to output component `j`. -/
abbrev GaugeMatrix (I : Type) := I → I → ENNReal

/-- Display matrix corresponding to `M : GaugeMatrix I`, where row `j` is the output
index and column `i` is the input index: `(toDisplayMatrix M) j i = M i j`. -/
def toDisplayMatrix {I : Type} (M : GaugeMatrix I) : Matrix I I ENNReal :=
  Matrix.of fun j i => M i j

/-- Recover an input-first matrix from a display matrix `A : Matrix I I ENNReal`. -/
def ofDisplayMatrix {I : Type} (A : Matrix I I ENNReal) : GaugeMatrix I :=
  fun i j => A j i

@[simp]
theorem toDisplayMatrix_apply {I : Type} (M : GaugeMatrix I) (j i : I) :
    toDisplayMatrix M j i = M i j :=
  rfl

@[simp]
theorem ofDisplayMatrix_apply {I : Type} (A : Matrix I I ENNReal) (i j : I) :
    ofDisplayMatrix A i j = A j i :=
  rfl

@[simp]
theorem ofDisplayMatrix_toDisplayMatrix {I : Type} (M : GaugeMatrix I) :
    ofDisplayMatrix (toDisplayMatrix M) = M :=
  rfl

@[simp]
theorem toDisplayMatrix_ofDisplayMatrix {I : Type} (A : Matrix I I ENNReal) :
    toDisplayMatrix (ofDisplayMatrix A) = A := by
  ext j i
  rfl

/-- Composition multiplication of input-first matrices:
$(\mathbf{M}_2 \cdot \mathbf{M}_1)_{i \to j} = \sum_{k \in I} (\mathbf{M}_2)_{k \to j} (\mathbf{M}_1)_{i \to k}$. -/
noncomputable def matMul {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) : GaugeMatrix I :=
  fun i j => ∑ k : I, M₂ k j * M₁ i k

@[simp]
theorem matMul_apply {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) (i j : I) :
    matMul M₂ M₁ i j = ∑ k : I, M₂ k j * M₁ i k :=
  rfl

/-- Correspondence between input-first `matMul` and ordinary display matrix multiplication. -/
theorem toDisplayMatrix_mul {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) :
    toDisplayMatrix (matMul M₂ M₁) = toDisplayMatrix M₂ * toDisplayMatrix M₁ := by
  ext j i
  simp [Matrix.mul_apply, matMul, toDisplayMatrix]

theorem matMul_assoc {I : Type} [Fintype I] (M₃ M₂ M₁ : GaugeMatrix I) :
    matMul (matMul M₃ M₂) M₁ = matMul M₃ (matMul M₂ M₁) := by
  ext i j
  simp only [matMul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  ring

/-- Identity matrix $\mathbf{I}$ in input-first representation ($\delta_{ij}$). -/
def idMatrix {I : Type} [DecidableEq I] : GaugeMatrix I :=
  fun i j => if i = j then 1 else 0

@[simp]
theorem idMatrix_apply_self {I : Type} [DecidableEq I] (i : I) :
    idMatrix i i = 1 := by
  simp [idMatrix]

@[simp]
theorem idMatrix_apply_ne {I : Type} [DecidableEq I] {i j : I} (h : i ≠ j) :
    idMatrix i j = 0 := by
  simp [idMatrix, h]

theorem toDisplayMatrix_id {I : Type} [DecidableEq I] :
    toDisplayMatrix (I := I) idMatrix = (1 : Matrix I I ENNReal) := by
  ext j i
  by_cases h : i = j
  · subst h
    simp [idMatrix]
  · have h' : j ≠ i := Ne.symm h
    simp [idMatrix, h, h']

@[simp]
theorem idMatrix_matMul {I : Type} [Fintype I] [DecidableEq I] (M : GaugeMatrix I) :
    matMul idMatrix M = M := by
  ext i j
  simp only [matMul_apply, idMatrix]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

@[simp]
theorem matMul_idMatrix {I : Type} [Fintype I] [DecidableEq I] (M : GaugeMatrix I) :
    matMul M idMatrix = M := by
  ext i j
  simp only [matMul_apply, idMatrix]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [Ne.symm hki]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Ordered matrix product corresponding to execution sequence `0, 1, ..., k-1`:
`matProd k M` equals $M^{(k)} \cdots M^{(1)}$, with empty product `idMatrix` at `k = 0`. -/
noncomputable def matProd {I : Type} [Fintype I] [DecidableEq I] :
    (k : ℕ) → (Fin k → GaugeMatrix I) → GaugeMatrix I
  | 0, _ => idMatrix
  | k + 1, M => matMul (M (Fin.last k)) (matProd k (fun m => M m.castSucc))

@[simp]
theorem matProd_zero {I : Type} [Fintype I] [DecidableEq I]
    (M : Fin 0 → GaugeMatrix I) :
    matProd 0 M = idMatrix :=
  rfl

@[simp]
theorem matProd_succ {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (M : Fin (k + 1) → GaugeMatrix I) :
    matProd (k + 1) M = matMul (M (Fin.last k)) (matProd k (fun m => M m.castSucc)) :=
  rfl

@[simp]
theorem matProd_one {I : Type} [Fintype I] [DecidableEq I]
    (M : Fin 1 → GaugeMatrix I) :
    matProd 1 M = M 0 := by
  simp [matProd]

theorem matProd_two {I : Type} [Fintype I] [DecidableEq I]
    (M : Fin 2 → GaugeMatrix I) :
    matProd 2 M = matMul (M 1) (M 0) := by
  simp [matProd]

/-- List-based ordered product in execution order `[M₁, ..., Mₖ]`, yielding $M_k \cdots M_1$. -/
noncomputable def matListProd {I : Type} [Fintype I] [DecidableEq I] :
    List (GaugeMatrix I) → GaugeMatrix I
  | [] => idMatrix
  | M :: Ms => matMul (matListProd Ms) M

@[simp]
theorem matListProd_nil {I : Type} [Fintype I] [DecidableEq I] :
    matListProd (I := I) [] = idMatrix :=
  rfl

@[simp]
theorem matListProd_singleton {I : Type} [Fintype I] [DecidableEq I] (M : GaugeMatrix I) :
    matListProd [M] = M := by
  simp [matListProd]

theorem matListProd_append {I : Type} [Fintype I] [DecidableEq I]
    (Ms₁ Ms₂ : List (GaugeMatrix I)) :
    matListProd (Ms₁ ++ Ms₂) = matMul (matListProd Ms₂) (matListProd Ms₁) := by
  induction Ms₁ with
  | nil =>
    rw [List.nil_append, matListProd_nil, matMul_idMatrix]
  | cons M Ms₁ ih =>
    simp only [List.cons_append, matListProd, ih]
    exact matMul_assoc (matListProd Ms₂) (matListProd Ms₁) M

theorem matListProd_ofFn {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (M : Fin k → GaugeMatrix I) :
    matListProd (List.ofFn M) = matProd k M := by
  induction k with
  | zero => simp [matProd]
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, matListProd_append, matListProd_singleton, ih,
      matProd_succ]

/-! ### Finite index paths (HC02-D06) -/

/-- Full vertex sequence $(k_0, k_1, \dots, k_n)$ of a length-`n` path from `k_0 = i` to `k_n = j`
determined by an intermediate index sequence `mid : Fin (n - 1) → I`.
When `n = 1`, `Fin (n - 1) → I` has a unique empty sequence `Fin.elim0`. -/
def pathVertex {I : Type} {n : ℕ} (i j : I) (mid : Fin (n - 1) → I) : Fin (n + 1) → I :=
  fun t =>
    if h0 : t.val = 0 then i
    else if hn : t.val = n then j
    else mid ⟨t.val - 1, by omega⟩

@[simp]
theorem pathVertex_zero {I : Type} {n : ℕ} (i j : I) (mid : Fin (n - 1) → I) :
    pathVertex i j mid 0 = i := by
  simp [pathVertex]

theorem pathVertex_last {I : Type} {n : ℕ} (hn : 1 ≤ n) (i j : I) (mid : Fin (n - 1) → I) :
    pathVertex i j mid (Fin.last n) = j := by
  have hne : n ≠ 0 := by omega
  simp [pathVertex, Fin.last, hne]

theorem pathVertex_snoc_castSucc {I : Type} {n : ℕ} (i k j : I) (mid : Fin n → I)
    (t : Fin (n + 2)) :
    pathVertex (n := n + 2) i j (Fin.snoc mid k) t.castSucc =
      pathVertex (n := n + 1) i k mid t := by
  have ht : t.val < n + 2 := t.isLt
  dsimp [pathVertex, Fin.castSucc]
  by_cases h0 : t.val = 0
  · simp [h0]
  · have hne2 : t.val ≠ n + 2 := by omega
    by_cases h1 : t.val = n + 1
    · have h0' : n + 1 ≠ 0 := by omega
      have hne2' : n + 1 ≠ n + 2 := by omega
      simp only [h1, h0', hne2', ↓reduceDIte]
      have hidx : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
        ext; simp [Fin.last]
      rw [hidx, Fin.snoc_last]
    · simp only [h0, hne2, h1, ↓reduceDIte, Fin.snoc]
      have hsub : t.val - 1 < n := by omega
      simp [hsub]

theorem pathVertex_snoc_last {I : Type} {n : ℕ} (i k j : I) (mid : Fin n → I) :
    pathVertex (n := n + 2) i j (Fin.snoc mid k) (Fin.last (n + 1)).castSucc = k := by
  simpa [pathVertex_last (n := n + 1) (by omega)] using
    pathVertex_snoc_castSucc (n := n) i k j mid (Fin.last (n + 1))

/-- Path weight: product of step matrix entries along the full vertex path. -/
noncomputable def pathWeight {I : Type} {n : ℕ} (M : Fin n → GaugeMatrix I)
    (i j : I) (mid : Fin (n - 1) → I) : ENNReal :=
  ∏ m : Fin n, M m (pathVertex i j mid m.castSucc) (pathVertex i j mid m.succ)

/-- Predicate asserting that every step edge along the path is strictly positive. -/
def PathAllPos {I : Type} {n : ℕ} (M : Fin n → GaugeMatrix I)
    (i j : I) (mid : Fin (n - 1) → I) : Prop :=
  ∀ m : Fin n, 0 < M m (pathVertex i j mid m.castSucc) (pathVertex i j mid m.succ)

/-- Predicate asserting that at least one step edge along the path equals zero. -/
def PathHasZero {I : Type} {n : ℕ} (M : Fin n → GaugeMatrix I)
    (i j : I) (mid : Fin (n - 1) → I) : Prop :=
  ∃ m : Fin n, M m (pathVertex i j mid m.castSucc) (pathVertex i j mid m.succ) = 0

/-- For `n = 1`, there is a unique (empty) intermediate index sequence `Fin (1 - 1) → I`. -/
theorem empty_mid_seq_unique (I : Type) : ∃! _ : Fin (1 - 1) → I, True :=
  ⟨fun x => Fin.elim0 x, trivial, fun _ _ => funext fun x => Fin.elim0 x⟩

theorem pathWeight_one {I : Type} (M : Fin 1 → GaugeMatrix I) (i j : I)
    (mid : Fin 0 → I) :
    pathWeight M i j mid = M 0 i j := by
  have h0 : pathVertex (n := 1) i j mid (0 : Fin 1).castSucc = i :=
    pathVertex_zero (n := 1) i j mid
  have h1 : pathVertex (n := 1) i j mid (0 : Fin 1).succ = j := by
    simpa [Fin.last] using pathVertex_last (n := 1) le_rfl i j mid
  rw [pathWeight, Fin.prod_univ_one, h0, h1]

theorem pathAllPos_one_iff {I : Type} (M : Fin 1 → GaugeMatrix I) (i j : I)
    (mid : Fin 0 → I) :
    PathAllPos M i j mid ↔ 0 < M 0 i j := by
  have h0 : pathVertex (n := 1) i j mid (0 : Fin 1).castSucc = i :=
    pathVertex_zero (n := 1) i j mid
  have h1 : pathVertex (n := 1) i j mid (0 : Fin 1).succ = j := by
    simpa [Fin.last] using pathVertex_last (n := 1) le_rfl i j mid
  rw [PathAllPos, Fin.forall_fin_one, h0, h1]

theorem pathHasZero_one_iff {I : Type} (M : Fin 1 → GaugeMatrix I) (i j : I)
    (mid : Fin 0 → I) :
    PathHasZero M i j mid ↔ M 0 i j = 0 := by
  have h0 : pathVertex (n := 1) i j mid (0 : Fin 1).castSucc = i :=
    pathVertex_zero (n := 1) i j mid
  have h1 : pathVertex (n := 1) i j mid (0 : Fin 1).succ = j := by
    simpa [Fin.last] using pathVertex_last (n := 1) le_rfl i j mid
  rw [PathHasZero, Fin.exists_fin_one, h0, h1]

theorem pathWeight_pos_iff {I : Type} {n : ℕ} (M : Fin n → GaugeMatrix I)
    (i j : I) (mid : Fin (n - 1) → I) :
    0 < pathWeight M i j mid ↔ PathAllPos M i j mid := by
  simp only [pathWeight, PathAllPos, pos_iff_ne_zero, ne_eq, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, not_exists]

theorem pathWeight_eq_zero_iff {I : Type} {n : ℕ} (M : Fin n → GaugeMatrix I)
    (i j : I) (mid : Fin (n - 1) → I) :
    pathWeight M i j mid = 0 ↔ PathHasZero M i j mid := by
  simp only [pathWeight, PathHasZero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

/-- Equivalence splitting an intermediate sequence of length `n + 1` into its prefix of length `n`
and its last element `k : I`. -/
def midSnocEquiv (I : Type) (n : ℕ) : (Fin n → I) × I ≃ (Fin (n + 1) → I) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (fun t => f t.castSucc, f (Fin.last n))
  left_inv p := by
    ext t
    · simp
    · simp
  right_inv f := Fin.snoc_init_self f

theorem pathWeight_snoc {I : Type} {n : ℕ} (M : Fin (n + 2) → GaugeMatrix I)
    (i k j : I) (mid : Fin n → I) :
    pathWeight M i j (Fin.snoc mid k) =
      M (Fin.last (n + 1)) k j * pathWeight (fun m => M m.castSucc) i k mid := by
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc, mul_comm]
  congr 1
  · have h1 : pathVertex (n := n + 2) i j (Fin.snoc mid k) (Fin.last (n + 1)).castSucc = k :=
      pathVertex_snoc_last i k j mid
    have h2 : pathVertex (n := n + 2) i j (Fin.snoc mid k) (Fin.last (n + 1)).succ = j := by
      simpa using pathVertex_last (n := n + 2) (by omega) i j (Fin.snoc mid k)
    rw [h1, h2]
  · refine Finset.prod_congr rfl ?_
    intro m _
    have ha := pathVertex_snoc_castSucc (n := n) i k j mid m.castSucc
    have hb := pathVertex_snoc_castSucc (n := n) i k j mid m.succ
    simpa [Fin.castSucc_succ] using congrArg₂ (M m.castSucc) ha hb

theorem matProd_succ_apply_eq_sum_paths {I : Type} [Fintype I] [DecidableEq I]
    (n' : ℕ) (M : Fin (n' + 1) → GaugeMatrix I) (i j : I) :
    matProd (n' + 1) M i j = ∑ mid : Fin n' → I, pathWeight M i j mid := by
  induction n' generalizing i j with
  | zero =>
    rw [matProd_one]
    have huniq : ∀ mid : Fin 0 → I, pathWeight M i j mid = M 0 i j :=
      fun mid => pathWeight_one M i j mid
    rw [Finset.sum_congr rfl (fun mid _ => huniq mid), Finset.sum_const, Finset.card_univ,
      Fintype.card_unique, one_nsmul]
  | succ n' ih =>
    rw [matProd_succ, matMul_apply]
    have ih_step : ∀ k : I,
        matProd (n' + 1) (fun m => M m.castSucc) i k =
          ∑ mid : Fin n' → I, pathWeight (fun m => M m.castSucc) i k mid :=
      fun k => ih (fun m => M m.castSucc) i k
    simp_rw [ih_step, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h_eq :
        (∑ mid : Fin n' → I, ∑ k : I,
            M (Fin.last (n' + 1)) k j * pathWeight (fun m => M m.castSucc) i k mid) =
          ∑ p : (Fin n' → I) × I,
            M (Fin.last (n' + 1)) p.2 j * pathWeight (fun m => M m.castSucc) i p.2 p.1 := by
      rw [Fintype.sum_prod_type]
    rw [h_eq]
    symm
    refine Fintype.sum_equiv (midSnocEquiv I n').symm _ _ ?_
    intro mid
    let p := (midSnocEquiv I n').symm mid
    have hp : Fin.snoc p.1 p.2 = mid := (midSnocEquiv I n').apply_symm_apply mid
    simpa [p, hp] using pathWeight_snoc M i p.2 j p.1

/-- Every entry of a non-empty ordered matrix product `matProd n M i j` (`n ≥ 1`)
equals the sum of `pathWeight M i j mid` over all intermediate index sequences `mid`. -/
theorem matProd_apply_eq_sum_paths {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    matProd n M i j = ∑ mid : Fin (n - 1) → I, pathWeight M i j mid := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n' => exact matProd_succ_apply_eq_sum_paths n' M i j

/-! ### Component channels and sparsity predicates (HC02-D07) -/

/-- A component channel `(i, j) ∈ I × I` from input component `i` to output component `j`. -/
abbrev Channel (I : Type) := I × I

/-- Single-row sparsity at `(i, j)`: in row `j` (output `j`), all entries with input `k ≠ i` vanish. -/
def RowSparseAt {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- Single-column sparsity at `(i, j)`: in column `i` (input `i`), all entries with output `k ≠ j` vanish. -/
def ColSparseAt {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/-- Diagonal matrix: all off-diagonal entries vanish. -/
def IsDiagMatrix {I : Type} (L : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

theorem isDiagMatrix_iff_rowSparseAt {I : Type} (L : GaugeMatrix I) :
    IsDiagMatrix L ↔ ∀ j : I, RowSparseAt L j j := by
  constructor
  · intro h j k hk
    exact h k j hk
  · intro h i j hij
    exact h j i hij

theorem isDiagMatrix_iff_colSparseAt {I : Type} (L : GaugeMatrix I) :
    IsDiagMatrix L ↔ ∀ i : I, ColSparseAt L i i := by
  constructor
  · intro h i k hk
    exact h i k (Ne.symm hk)
  · intro h i j hij
    exact h i j (Ne.symm hij)

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=Ch02Certificates.lean
import Ch02Matrices

/-!
# Chapter 2 — Lip / co-Lip Certificates, Composition, Perturbation, and Operator Chains

Formalizes obligations `HC02-D01`, `HC02-D02`, `HC02-D04`, `HC02-D05`, and
`HC02-P01` through `HC02-P17` from `source/02-operator-bounds.md`.
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-! ### Operator composition helpers and chain representations (HC02-D04, HC02-D05) -/

/-- Identity operator $\mathrm{id}_{\mathcal{X}} \in \mathcal{X}_{\mathrm{op}}$. -/
def idOperator {X : Type} {bot : X} : Operator X bot :=
  ⟨id, rfl⟩

@[simp]
theorem idOperator_func {X : Type} {bot : X} (x : X) :
    (idOperator (X := X) (bot := bot)).func x = x :=
  rfl

theorem dom_idOperator {X : Type} {bot : X} :
    dom (idOperator (X := X) (bot := bot)) = { x : X | x ≠ bot } :=
  rfl

/-- Composition $\psi \circ \phi$ of two operators in $\mathcal{X}_{\mathrm{op}}$. -/
def opComp {X : Type} {bot : X} (ψ ϕ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ ϕ.func, by simp [ϕ.preserves_bot, ψ.preserves_bot]⟩

@[simp]
theorem opComp_func {X : Type} {bot : X} (ψ ϕ : Operator X bot) (x : X) :
    (opComp ψ ϕ).func x = ψ.func (ϕ.func x) :=
  rfl

@[simp]
theorem opComp_idOperator {X : Type} {bot : X} (ϕ : Operator X bot) :
    opComp ϕ idOperator = ϕ := by
  ext x
  rfl

@[simp]
theorem idOperator_opComp {X : Type} {bot : X} (ϕ : Operator X bot) :
    opComp idOperator ϕ = ϕ := by
  ext x
  rfl

theorem opComp_assoc {X : Type} {bot : X} (χ ψ ϕ : Operator X bot) :
    opComp (opComp χ ψ) ϕ = opComp χ (opComp ψ ϕ) := by
  ext x
  rfl

/-- Common domain $\mathrm{dom}(\phi_1, \phi_2) = \mathrm{dom}(\phi_1) \cap \mathrm{dom}(\phi_2)$. -/
def commonDom₂ {X : Type} {bot : X} (ϕ₁ ϕ₂ : Operator X bot) : Set X :=
  dom ϕ₁ ∩ dom ϕ₂

theorem subset_dom_opComp_iff {X : Type} {bot : X}
    (ψ ϕ : Operator X bot) (U : Set X) :
    U ⊆ dom (opComp ψ ϕ) ↔ U ⊆ dom ϕ ∧ operator_image ϕ U ⊆ dom ψ := by
  constructor
  · intro hU
    refine ⟨?_, ?_⟩
    · intro x hx hbot
      have hx' : (opComp ψ ϕ).func x ≠ bot := hU hx
      simp [opComp, hbot, ψ.preserves_bot] at hx'
    · rintro y ⟨x, hx, rfl⟩
      exact hU hx
  · rintro ⟨_, hψ⟩ x hx
    exact hψ ⟨x, hx, rfl⟩

/-- Ordered finite operator composition $c_k = \phi_k \circ \cdots \circ \phi_1$
for execution sequence `ops : Fin k → Operator X bot`, with $c_0 = \mathrm{id}_{\mathcal{X}}$. -/
def opSeqComp {X : Type} {bot : X} :
    (k : ℕ) → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => idOperator
  | k + 1, ops => opComp (ops (Fin.last k)) (opSeqComp k (fun m => ops m.castSucc))

@[simp]
theorem opSeqComp_zero {X : Type} {bot : X} (ops : Fin 0 → Operator X bot) :
    opSeqComp 0 ops = idOperator :=
  rfl

@[simp]
theorem opSeqComp_succ {X : Type} {bot : X} (k : ℕ) (ops : Fin (k + 1) → Operator X bot) :
    opSeqComp (k + 1) ops = opComp (ops (Fin.last k)) (opSeqComp k (fun m => ops m.castSucc)) :=
  rfl

@[simp]
theorem opSeqComp_one {X : Type} {bot : X} (ops : Fin 1 → Operator X bot) :
    opSeqComp 1 ops = ops 0 := by
  simp [opSeqComp]

theorem opSeqComp_two {X : Type} {bot : X} (ops : Fin 2 → Operator X bot) :
    opSeqComp 2 ops = opComp (ops 1) (ops 0) := by
  simp [opSeqComp]

/-- Correspondence between `opSeqComp` and Chapter 1's `OperatorChain`. -/
theorem opSeqComp_eq_operatorChain {X : Type} {bot : X}
    (k : ℕ) (ops : Fin k → Operator X bot) :
    opSeqComp k ops = OperatorChain (List.ofFn ops).reverse := by
  induction k with
  | zero =>
    ext x
    simp [OperatorChain]
  | succ k ih =>
    rw [opSeqComp_succ, List.ofFn_succ', List.concat_eq_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    ext x
    change (ops (Fin.last k)).func ((opSeqComp k (fun i => ops i.castSucc)).func x) =
      (ops (Fin.last k)).func ((OperatorChain (List.ofFn (fun i => ops i.castSucc)).reverse).func x)
    rw [ih]

/-- Prefix composition $c_m = \phi_m \circ \cdots \circ \phi_1$ for `m ≤ k`. -/
def prefixOpComp {X : Type} {bot : X} {k : ℕ} (ops : Fin k → Operator X bot) :
    (m : ℕ) → m ≤ k → Operator X bot
  | 0, _ => idOperator
  | m + 1, hm => opComp (ops ⟨m, hm⟩) (prefixOpComp ops m (Nat.le_of_succ_le hm))

theorem prefixOpComp_castSucc {X : Type} {bot : X} {k : ℕ}
    (ops : Fin (k + 1) → Operator X bot) (m : ℕ) (hm : m ≤ k) :
    prefixOpComp (fun i : Fin k => ops i.castSucc) m hm =
      prefixOpComp ops m (hm.trans (Nat.le_succ k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [prefixOpComp]
    congr 1
    exact ih (Nat.le_of_succ_le hm)

theorem prefixOpComp_self {X : Type} {bot : X}
    (k : ℕ) (ops : Fin k → Operator X bot) :
    prefixOpComp ops k (le_refl k) = opSeqComp k ops := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prefixOpComp, opSeqComp_succ, ← ih (fun m => ops m.castSucc), prefixOpComp_castSucc]
    rfl

/-- Auxiliary recursive definition of intermediate actual image domains $U_{m+1} = \phi_m(U_m)$. -/
def chainDomainAux {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) : (m : ℕ) → m ≤ k → Set X
  | 0, _ => U₀
  | m + 1, hm => operator_image (ops ⟨m, hm⟩) (chainDomainAux ops U₀ m (Nat.le_of_succ_le hm))

/-- Actual input/image domain sequence $U_0, U_1, \dots, U_k$ indexed by `Fin (k + 1)`,
where `chainDomain ops U₀ 0 = U₀` and `chainDomain ops U₀ m.succ = ops m '' chainDomain ops U₀ m.castSucc`. -/
def chainDomain {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) (m : Fin (k + 1)) : Set X :=
  chainDomainAux ops U₀ m.val (Nat.le_of_lt_succ m.isLt)

@[simp]
theorem chainDomain_zero {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) :
    chainDomain ops U₀ 0 = U₀ :=
  rfl

theorem chainDomain_succ {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) (m : Fin k) :
    chainDomain ops U₀ m.succ = operator_image (ops m) (chainDomain ops U₀ m.castSucc) := by
  rfl

theorem chainDomainAux_castSucc {X : Type} {bot : X} {k : ℕ}
    (ops : Fin (k + 1) → Operator X bot) (U₀ : Set X) (m : ℕ) (hm : m ≤ k) :
    chainDomainAux (fun i : Fin k => ops i.castSucc) U₀ m hm =
      chainDomainAux ops U₀ m (hm.trans (Nat.le_succ k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [chainDomainAux]
    congr 1
    exact ih (Nat.le_of_succ_le hm)

theorem chainDomain_castSucc {X : Type} {bot : X} {k : ℕ}
    (ops : Fin (k + 1) → Operator X bot) (U₀ : Set X) (m : Fin (k + 1)) :
    chainDomain (fun i : Fin k => ops i.castSucc) U₀ m =
      chainDomain ops U₀ m.castSucc :=
  chainDomainAux_castSucc ops U₀ m.val (Nat.le_of_lt_succ m.isLt)

/-- Each successive domain $U_m$ equals the image of $U_0$ under the prefix composite $c_m$. -/
theorem chainDomainAux_eq_image {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) (m : ℕ) (hm : m ≤ k) :
    chainDomainAux ops U₀ m hm = operator_image (prefixOpComp ops m hm) U₀ := by
  induction m with
  | zero =>
    simp [chainDomainAux, prefixOpComp, operator_image, idOperator]
  | succ m ih =>
    simp only [chainDomainAux, prefixOpComp]
    rw [ih (Nat.le_of_succ_le hm)]
    ext y
    simp [operator_image, opComp]

/-- Full composite image equals the final successive image:
$c_k(U_0) = U_k$ (`chainDomain ops U₀ (Fin.last k)`). -/
theorem chainDomain_last_eq_image {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) :
    chainDomain ops U₀ (Fin.last k) = operator_image (opSeqComp k ops) U₀ := by
  have hval : (Fin.last k).val = k := Fin.val_last k
  simpa [chainDomain, hval, prefixOpComp_self] using chainDomainAux_eq_image ops U₀ k (le_refl k)

theorem subset_dom_prefixOpComp_of_le {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X)
    (hdom : U₀ ⊆ dom (opSeqComp k ops)) (m : ℕ) (hm : m ≤ k) :
    U₀ ⊆ dom (prefixOpComp ops m hm) := by
  rw [← prefixOpComp_self k ops] at hdom
  have aux : ∀ n (hn : n ≤ k), U₀ ⊆ dom (prefixOpComp ops n hn) →
      ∀ r (hr : r ≤ n), U₀ ⊆ dom (prefixOpComp ops r (hr.trans hn)) := by
    intro n
    induction n with
    | zero =>
      intro hn h0 r hr
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst hr0
      exact h0
    | succ n ih =>
      intro hn hn_dom r hr
      rcases Nat.lt_or_eq_of_le hr with hlt | heq
      · have hle : r ≤ n := Nat.lt_succ_iff.mp hlt
        have hn' : U₀ ⊆ dom (prefixOpComp ops n (Nat.le_of_succ_le hn)) :=
          (subset_dom_opComp_iff _ _ U₀).mp hn_dom |>.1
        exact ih (Nat.le_of_succ_le hn) hn' r hle
      · subst heq
        exact hn_dom
  exact aux k (le_refl k) hdom m hm

/-- Starting domain inclusion $U_0 \subseteq \mathrm{dom}(c_k)$ implies every intermediate
image domain satisfies $U_m \subseteq \mathrm{dom}(\phi_m)$. -/
theorem chainDomain_subset_dom {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X)
    (hdom : U₀ ⊆ dom (opSeqComp k ops)) (m : Fin k) :
    chainDomain ops U₀ m.castSucc ⊆ dom (ops m) := by
  have hsucc : U₀ ⊆ dom (prefixOpComp ops (m.val + 1) m.isLt) :=
    subset_dom_prefixOpComp_of_le ops U₀ hdom (m.val + 1) m.isLt
  have him : operator_image (prefixOpComp ops m.val (Nat.le_of_succ_le m.isLt)) U₀ ⊆
      dom (ops ⟨m.val, m.isLt⟩) :=
    (subset_dom_opComp_iff (ops ⟨m.val, m.isLt⟩) _ U₀).mp hsucc |>.2
  rw [← chainDomainAux_eq_image] at him
  exact him

/-! ### Lip and co-Lip matrix sets (HC02-D01, HC02-D02) -/

/-- Global Lipschitz matrix condition on $\mathrm{dom}(\phi)$. -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Set $\mathscr{L}(\phi)$ of all legal global Lipschitz matrices for $\phi$. -/
def LipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/-- Restricted Lipschitz matrix condition on $U \subseteq \mathrm{dom}(\phi)$. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Set $\mathscr{L}(\phi)|_U$ of legal restricted Lipschitz matrices for $\phi$ on $U$. -/
def LipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem lipRestricted_dom_eq_lipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    LipRestricted d ϕ (dom ϕ) = LipSet d ϕ := by
  ext L
  simp [LipRestricted, IsRestrictedLipMatrix, LipSet, IsLipMatrix]

/-- Restricted co-Lipschitz matrix condition on nonempty $U \subseteq \mathrm{dom}(\phi)$.
Nonemptiness $U \neq \emptyset$ is part of the definition of $\mathscr{K}(\phi)|_U$. -/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    (∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)

/-- Set $\mathscr{K}(\phi)|_U$ of legal restricted co-Lipschitz matrices for $\phi$ on $U$. -/
def CoLipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

/-- Zero coefficients are always valid in `CoLipRestricted` (when $U \neq \emptyset$ and $U \subseteq \mathrm{dom}(\phi)$). -/
theorem zero_mem_coLipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    (fun _ _ => (0 : ENNReal)) ∈ CoLipRestricted d ϕ U := by
  refine ⟨hU_ne, hU, fun _ _ _ _ _ => ?_⟩
  simp

/-- `⊤` is a legal co-Lip coefficient whenever the corresponding input distance vanishes on $U$. -/
theorem top_entry_mem_coLipRestricted_of_zero_dist {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (i₀ j₀ : I)
    (hzero : ∀ x ∈ U, ∀ y ∈ U, d i₀ x y = 0) :
    (fun i j => if i = i₀ ∧ j = j₀ then (⊤ : ENNReal) else 0) ∈ CoLipRestricted d ϕ U := by
  refine ⟨hU_ne, hU, fun x hx y hy j => ?_⟩
  have hsum : (∑ i : I, (if i = i₀ ∧ j = j₀ then (⊤ : ENNReal) else 0) * d i x y) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    by_cases h : i = i₀ ∧ j = j₀
    · rw [if_pos h, h.1, hzero x hx y hy, mul_zero]
    · rw [if_neg h, zero_mul]
  rw [hsum]
  exact zero_le _

/-- `⊤` is a legal Lip coefficient when input vanishes implies output vanishes. -/
theorem top_mem_lipRestricted_of_zero_preserving {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ)
    (hpres : ∀ x ∈ U, ∀ y ∈ U, (∀ i : I, d i x y = 0) → ∀ j : I, d j (ϕ.func x) (ϕ.func y) = 0) :
    (fun _ _ => (⊤ : ENNReal)) ∈ LipRestricted d ϕ U := by
  refine ⟨hU, fun x hx y hy j => ?_⟩
  by_cases hz : ∀ i : I, d i x y = 0
  · rw [hpres x hx y hy hz j]
    exact zero_le _
  · push Not at hz
    rcases hz with ⟨i₀, hi₀⟩
    have htop : (⊤ : ENNReal) * d i₀ x y = ⊤ := ENNReal.top_mul hi₀
    have hle : (⊤ : ENNReal) * d i₀ x y ≤ ∑ i : I, (⊤ : ENNReal) * d i x y :=
      Finset.single_le_sum (f := fun i => (⊤ : ENNReal) * d i x y)
        (fun _ _ => zero_le _) (Finset.mem_univ i₀)
    rw [htop] at hle
    exact le_top.trans hle

/-! ### Single-component degeneration, domain restriction, entry infima (HC02-P01 to HC02-P04) -/

/-- **HC02-P01**: Single-component degeneration of the Lip matrix condition ($I = \{i\}$). -/
theorem lipSet_singleton_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (hI : ∀ k : I, k = i)
    (L : GaugeMatrix I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  have huniv : (Finset.univ : Finset I) = {i} := by
    ext k
    simp [hI k]
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    rwa [← Finset.sum_singleton (fun k => L k i * d k x y) i, ← huniv]
  · intro h x hx y hy j
    rw [hI j, huniv, Finset.sum_singleton]
    exact h x hx y hy

theorem lipSet_unique_iff {X I : Type} {bot : X} [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d default (ϕ.func x) (ϕ.func y) ≤ L default default * d default x y :=
  lipSet_singleton_iff d ϕ default Unique.eq_default L

/-- **HC02-P02**: Global Lip certificates restrict to any subdomain $U \subseteq \mathrm{dom}(\phi)$. -/
theorem lipSet_subset_lipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) :
    LipSet d ϕ ⊆ LipRestricted d ϕ U := by
  intro L hL
  exact ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/-- **HC02-P03**: Shrinking the evaluation domain enlarges the feasible Lip certificate family. -/
theorem lipRestricted_antitone {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) :
    LipRestricted d ϕ V ⊆ LipRestricted d ϕ U := by
  rintro L ⟨hV, hL⟩
  exact ⟨hUV.trans hV, fun x hx y hy j => hL x (hUV hx) y (hUV hy) j⟩

/-- Entrywise infimum $a_{ij}(U) = \inf \{ M_{i \to j} : M \in \mathscr{L}(\phi)|_U \}$. -/
noncomputable def lipEntryInf {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf { r : ENNReal | ∃ M ∈ LipRestricted d ϕ U, M i j = r }

/-- **HC02-P04**: Entrywise infimum is non-decreasing in $U$ (non-increasing under shrinking $V$ to $U$). -/
theorem lipEntryInf_mono {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (i j : I) :
    lipEntryInf d ϕ U i j ≤ lipEntryInf d ϕ V i j := by
  apply sInf_le_sInf
  rintro r ⟨M, hM, rfl⟩
  exact ⟨M, lipRestricted_antitone d ϕ hUV hM, rfl⟩

/-! ### Two-step composition and co-Lip vanishing criterion (HC02-P05 to HC02-P07) -/

/-- **HC02-P05**: Two-step Lip matrix composition law. -/
theorem lipRestricted_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp ϕ₂ ϕ₁))
    {L₁ L₂ : GaugeMatrix I}
    (hL₁ : L₁ ∈ LipRestricted d ϕ₁ U₁)
    (hL₂ : L₂ ∈ LipRestricted d ϕ₂ (operator_image ϕ₁ U₁)) :
    matMul L₂ L₁ ∈ LipRestricted d (opComp ϕ₂ ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hfx : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hfy : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((opComp ϕ₂ ϕ₁).func x) ((opComp ϕ₂ ϕ₁).func y)
      = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := hL₂.2 (ϕ₁.func x) hfx (ϕ₁.func y) hfy j
    _ ≤ ∑ k : I, L₂ k j * (∑ i : I, L₁ i k * d i x y) := by
      refine Finset.sum_le_sum ?_
      intro k _
      gcongr
      exact hL₁.2 x hx y hy k
    _ = ∑ k : I, ∑ i : I, L₂ k j * (L₁ i k * d i x y) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, (L₂ k j * L₁ i k) * d i x y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [mul_assoc]
    _ = ∑ i : I, matMul L₂ L₁ i j * d i x y := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_mul, matMul_apply]

/-- **HC02-P06**: Pairwise output zero distance with positive input distance forces
global co-Lip entry $K_{i \to j} = 0$. -/
theorem coLip_entry_eq_zero_of_dist_zero {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {K : GaugeMatrix I}
    (hK : K ∈ CoLipRestricted d ϕ (dom ϕ))
    {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ) {i j : I}
    (hout : d j (ϕ.func x) (ϕ.func y) = 0) (hin : 0 < d i x y) :
    K i j = 0 := by
  have hsum : (∑ k : I, K k j * d k x y) ≤ 0 := by
    rw [← hout]
    exact hK.2.2 x hx y hy j
  have hsingle : K i j * d i x y ≤ 0 :=
    (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)).trans hsum
  have hmul : K i j * d i x y = 0 := le_antisymm hsingle (zero_le _)
  rcases mul_eq_zero.mp hmul with h0 | h0
  · exact h0
  · exact absurd h0 (ne_of_gt hin)

/-- **HC02-P07**: Two-step co-Lip matrix composition law (preserving nonemptiness of $U_1$). -/
theorem coLipRestricted_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp ϕ₂ ϕ₁))
    {K₁ K₂ : GaugeMatrix I}
    (hK₁ : K₁ ∈ CoLipRestricted d ϕ₁ U₁)
    (hK₂ : K₂ ∈ CoLipRestricted d ϕ₂ (operator_image ϕ₁ U₁)) :
    matMul K₂ K₁ ∈ CoLipRestricted d (opComp ϕ₂ ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hfx : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hfy : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, matMul K₂ K₁ i j * d i x y
      = ∑ i : I, ∑ k : I, (K₂ k j * K₁ i k) * d i x y := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [matMul_apply, Finset.sum_mul]
    _ = ∑ k : I, K₂ k j * (∑ i : I, K₁ i k * d i x y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [mul_assoc]
    _ ≤ ∑ k : I, K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
        refine Finset.sum_le_sum ?_
        intro k _
        gcongr
        exact hK₁.2.2 x hx y hy k
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
        hK₂.2.2 (ϕ₁.func x) hfx (ϕ₁.func y) hfy j
    _ = d j ((opComp ϕ₂ ϕ₁).func x) ((opComp ϕ₂ ϕ₁).func y) := rfl

/-! ### Two-operator pairwise image distance perturbation bounds (HC02-P08 to HC02-P11) -/

/-- **HC02-P08**: Forward pairwise image distance perturbation bound. -/
theorem perturbation_dist_forward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (_hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
  have hx' : d j (ϕ₂.func x) (ϕ₁.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  have hy' : d j (ϕ₁.func y) (ϕ₂.func y) ≤ δ j := hδ y hy j
  calc
    d j (ϕ₂.func x) (ϕ₂.func y)
      ≤ d j (ϕ₂.func x) (ϕ₁.func x) + d j (ϕ₁.func x) (ϕ₂.func y) := (hd j).triangle _ _ _
    _ ≤ d j (ϕ₂.func x) (ϕ₁.func x) + (d j (ϕ₁.func x) (ϕ₁.func y) + d j (ϕ₁.func y) (ϕ₂.func y)) := by
      gcongr
      exact (hd j).triangle _ _ _
    _ ≤ δ j + (d j (ϕ₁.func x) (ϕ₁.func y) + δ j) := by
      gcongr
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by ring

/-- **HC02-P09**: Backward pairwise image distance perturbation bound (swapping $\phi_1, \phi_2$). -/
theorem perturbation_dist_backward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := by
  have hU' : U ⊆ commonDom₂ ϕ₂ ϕ₁ := by
    simpa [commonDom₂, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ k : I, d k (ϕ₂.func z) (ϕ₁.func z) ≤ δ k := by
    intro z hz k
    rw [(hd k).symm]
    exact hδ z hz k
  exact perturbation_dist_forward d hd ϕ₂ ϕ₁ hU' δ hδ' hx hy j

/-- **HC02-P10**: Additive Lip upper-bound bridge from $\phi_1$ to $\phi_2$. -/
theorem perturbation_lip_bridge {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₁ : GaugeMatrix I} (hL₁ : L₁ ∈ LipRestricted d ϕ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by
  have hfwd := perturbation_dist_forward d hd ϕ₁ ϕ₂ hU δ hδ hx hy j
  have hlip := hL₁.2 x hx y hy j
  calc
    d j (ϕ₂.func x) (ϕ₂.func y)
      ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := hfwd
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + (δ j + δ j) := add_assoc _ _ _
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by rw [two_mul]
    _ ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by gcongr

/-- **HC02-P11**: Additive co-Lip lower-bound bridge from $\phi_1$ to $\phi_2$. -/
theorem perturbation_coLip_bridge {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₁ : GaugeMatrix I} (hK₁ : K₁ ∈ CoLipRestricted d ϕ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i : I, K₁ i j * d i x y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by
  have hbwd := perturbation_dist_backward d hd ϕ₁ ϕ₂ hU δ hδ hx hy j
  have hcolip := hK₁.2.2 x hx y hy j
  calc
    ∑ i : I, K₁ i j * d i x y
      ≤ d j (ϕ₁.func x) (ϕ₁.func y) := hcolip
    _ ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := hbwd
    _ = d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by rw [add_assoc, two_mul]

/-- Swapped Lip bridge from $\phi_2$ to $\phi_1$ (remark after HC02-P11). -/
theorem perturbation_lip_bridge_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₂ : GaugeMatrix I} (hL₂ : L₂ ∈ LipRestricted d ϕ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤ (∑ i : I, L₂ i j * d i x y) + 2 * δ j := by
  have hU' : U ⊆ commonDom₂ ϕ₂ ϕ₁ := by
    simpa [commonDom₂, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ k : I, d k (ϕ₂.func z) (ϕ₁.func z) ≤ δ k := by
    intro z hz k
    rw [(hd k).symm]
    exact hδ z hz k
  exact perturbation_lip_bridge d hd ϕ₂ ϕ₁ hU' δ hδ' hL₂ hx hy j

/-- Swapped co-Lip bridge from $\phi_2$ to $\phi_1$ (remark after HC02-P11). -/
theorem perturbation_coLip_bridge_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₂ : GaugeMatrix I} (hK₂ : K₂ ∈ CoLipRestricted d ϕ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i : I, K₂ i j * d i x y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by
  have hU' : U ⊆ commonDom₂ ϕ₂ ϕ₁ := by
    simpa [commonDom₂, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ k : I, d k (ϕ₂.func z) (ϕ₁.func z) ≤ δ k := by
    intro z hz k
    rw [(hd k).symm]
    exact hδ z hz k
  exact perturbation_coLip_bridge d hd ϕ₂ ϕ₁ hU' δ hδ' hK₂ hx hy j

/-! ### Step-by-step chain structures and finite composition bounds (HC02-D05, HC02-P12 to HC02-P17) -/

/-- Step-by-step Lip certificate chain data on actual successive image domains.
Contains ONLY the step operators, initial domain `U0 ⊆ dom c_k`, step matrices,
and step validity proofs — never the composite product bound itself. -/
structure LipChainData {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  U0 : Set X
  dom_subset : U0 ⊆ dom (opSeqComp k ops)
  mats : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k, mats m ∈ LipRestricted d (ops m) (chainDomain ops U0 m.castSucc)

/-- Prefix of a `LipChainData` of length `k + 1`. -/
def lipChainPrefix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : LipChainData bot d (k + 1)) :
    LipChainData bot d k where
  ops := fun m => chain.ops m.castSucc
  U0 := chain.U0
  dom_subset := (subset_dom_opComp_iff _ _ chain.U0).mp chain.dom_subset |>.1
  mats := fun m => chain.mats m.castSucc
  step_valid := fun m => by
    rw [chainDomain_castSucc]
    exact chain.step_valid m.castSucc

/-- Step-by-step co-Lip certificate chain data on actual successive image domains.
Contains ONLY the step operators, initial domain `U0 ⊆ dom c_k`, step matrices,
and step validity proofs — never the composite product bound itself. -/
structure CoLipChainData {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  U0 : Set X
  dom_subset : U0 ⊆ dom (opSeqComp k ops)
  mats : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k, mats m ∈ CoLipRestricted d (ops m) (chainDomain ops U0 m.castSucc)

/-- Prefix of a `CoLipChainData` of length `k + 1`. -/
def coLipChainPrefix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : CoLipChainData bot d (k + 1)) :
    CoLipChainData bot d k where
  ops := fun m => chain.ops m.castSucc
  U0 := chain.U0
  dom_subset := (subset_dom_opComp_iff _ _ chain.U0).mp chain.dom_subset |>.1
  mats := fun m => chain.mats m.castSucc
  step_valid := fun m => by
    rw [chainDomain_castSucc]
    exact chain.step_valid m.castSucc

/-- Every actual domain `chainDomain chain.ops chain.U0 m` along a non-empty co-Lip chain
(`k ≥ 1`) is nonempty. -/
theorem coLipChain_domains_nonempty {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} (hk : 1 ≤ k) (chain : CoLipChainData bot d k)
    (m : Fin (k + 1)) :
    (chainDomain chain.ops chain.U0 m).Nonempty := by
  have h0 : chain.U0.Nonempty := (chain.step_valid ⟨0, hk⟩).1
  rcases h0 with ⟨x₀, hx₀⟩
  rw [chainDomain, chainDomainAux_eq_image]
  exact ⟨(prefixOpComp chain.ops m.val (Nat.le_of_lt_succ m.isLt)).func x₀, x₀, hx₀, rfl⟩

/-- **HC02-P14 (helper)**: Identity matrix is a legal Lip matrix on any `U ⊆ dom idOperator`. -/
theorem idMatrix_mem_lipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X} (hU : U ⊆ dom (idOperator (X := X) (bot := bot))) :
    idMatrix ∈ LipRestricted d (idOperator (X := X) (bot := bot)) U := by
  refine ⟨hU, fun x _ y _ j => ?_⟩
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [idMatrix_apply_ne hij]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- **HC02-P14**: Zero-step composition ($k = 0$, $c_0 = \mathrm{id}$) admits `idMatrix`
as a legal Lip matrix on any nonempty $U \subseteq \mathrm{dom}(\mathrm{id})$. -/
theorem zero_step_idMatrix_mem_lipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ops : Fin 0 → Operator X bot)
    (mats : Fin 0 → GaugeMatrix I) {U : Set X}
    (_hU_ne : U.Nonempty) (hU : U ⊆ dom (opSeqComp 0 ops)) :
    matProd 0 mats ∈ LipRestricted d (opSeqComp 0 ops) U := by
  simpa [matProd_zero, opSeqComp_zero] using idMatrix_mem_lipRestricted d hU

/-- **HC02-P15**: Zero-step composition ($k = 0$, $c_0 = \mathrm{id}$) admits `idMatrix`
as a legal co-Lip matrix on any nonempty $U \subseteq \mathrm{dom}(\mathrm{id})$. -/
theorem idMatrix_mem_coLipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (idOperator (X := X) (bot := bot))) :
    idMatrix ∈ CoLipRestricted d (idOperator (X := X) (bot := bot)) U := by
  refine ⟨hU_ne, hU, fun x _ y _ j => ?_⟩
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [idMatrix_apply_ne hij]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem zero_step_idMatrix_mem_coLipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ops : Fin 0 → Operator X bot)
    (mats : Fin 0 → GaugeMatrix I) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (opSeqComp 0 ops)) :
    matProd 0 mats ∈ CoLipRestricted d (opSeqComp 0 ops) U := by
  simpa [matProd_zero, opSeqComp_zero] using idMatrix_mem_coLipRestricted d hU_ne hU

/-- **HC02-P12 (all $k$)**: Finite composition local Lip matrix bound for all $k \in \mathbb{N}$. -/
theorem lipChain_prod_mem_all {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ) (chain : LipChainData bot d k),
      matProd k chain.mats ∈ LipRestricted d (opSeqComp k chain.ops) chain.U0
  | 0, chain => idMatrix_mem_lipRestricted d chain.dom_subset
  | k + 1, chain => by
    have hpre := lipChain_prod_mem_all d k (lipChainPrefix chain)
    have hlast := chain.step_valid (Fin.last k)
    have him : chainDomain chain.ops chain.U0 (Fin.last k).castSucc =
        operator_image (opSeqComp k (lipChainPrefix chain).ops) chain.U0 := by
      rw [← chainDomain_castSucc]
      exact chainDomain_last_eq_image (lipChainPrefix chain).ops chain.U0
    rw [him] at hlast
    rw [matProd_succ, opSeqComp_succ]
    exact lipRestricted_comp d _ _ chain.dom_subset hpre hlast

/-- **HC02-P12**: Finite composition local Lip matrix bound for any positive chain length $k \ge 1$. -/
theorem lipChain_prod_mem {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : ℕ} (_hk : 1 ≤ k) (chain : LipChainData bot d k) :
    matProd k chain.mats ∈ LipRestricted d (opSeqComp k chain.ops) chain.U0 :=
  lipChain_prod_mem_all d k chain

/-- **HC02-P13 (helper for `k = k' + 1`)**: Finite composition local co-Lip matrix bound. -/
theorem coLipChain_succ_prod_mem {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    ∀ (k' : ℕ) (chain : CoLipChainData bot d (k' + 1)),
      matProd (k' + 1) chain.mats ∈ CoLipRestricted d (opSeqComp (k' + 1) chain.ops) chain.U0
  | 0, chain => by
    simpa [matProd_one, opSeqComp_one] using chain.step_valid 0
  | k' + 1, chain => by
    have hpre := coLipChain_succ_prod_mem d k' (coLipChainPrefix chain)
    have hlast := chain.step_valid (Fin.last (k' + 1))
    have him : chainDomain chain.ops chain.U0 (Fin.last (k' + 1)).castSucc =
        operator_image (opSeqComp (k' + 1) (coLipChainPrefix chain).ops) chain.U0 := by
      rw [← chainDomain_castSucc]
      exact chainDomain_last_eq_image (coLipChainPrefix chain).ops chain.U0
    rw [him] at hlast
    rw [matProd_succ, opSeqComp_succ]
    exact coLipRestricted_comp d _ _ chain.dom_subset hpre hlast

/-- **HC02-P13**: Finite composition local co-Lip matrix bound for any positive chain length $k \ge 1$. -/
theorem coLipChain_prod_mem {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : ℕ} (hk : 1 ≤ k) (chain : CoLipChainData bot d k) :
    matProd k chain.mats ∈ CoLipRestricted d (opSeqComp k chain.ops) chain.U0 := by
  cases k with
  | zero => exact absurd hk (by omega)
  | succ k' => exact coLipChain_succ_prod_mem d k' chain

/-- Pure matrix entry zero criterion over all finite index paths ($n \ge 1$). -/
theorem matProd_eq_zero_iff_all_paths_hasZero {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    matProd n M i j = 0 ↔ ∀ mid : Fin (n - 1) → I, PathHasZero M i j mid := by
  rw [matProd_apply_eq_sum_paths hn M i j, Finset.sum_eq_zero_iff]
  refine ⟨fun h mid => ?_, fun h mid _ => ?_⟩
  · exact (pathWeight_eq_zero_iff M i j mid).mp (h mid (Finset.mem_univ mid))
  · exact (pathWeight_eq_zero_iff M i j mid).mpr (h mid)

/-- Pure matrix entry positivity criterion over finite index paths ($n \ge 1$). -/
theorem matProd_pos_iff_exists_path_allPos {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < matProd n M i j ↔ ∃ mid : Fin (n - 1) → I, PathAllPos M i j mid := by
  rw [matProd_apply_eq_sum_paths hn M i j, pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff]
  push Not
  constructor
  · rintro ⟨mid, _, hne⟩
    exact ⟨mid, (pathWeight_pos_iff M i j mid).mp (pos_iff_ne_zero.mpr hne)⟩
  · rintro ⟨mid, hpos⟩
    exact ⟨mid, Finset.mem_univ mid, ne_of_gt ((pathWeight_pos_iff M i j mid).mpr hpos)⟩

/-- **HC02-P16**: Along a Lip certificate chain of length $n \ge 1$, the product entry $(i \to j)$
vanishes if and only if every intermediate index path contains at least one zero entry. -/
theorem lipChain_prod_eq_zero_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} {n : ℕ} (hn : 1 ≤ n) (chain : LipChainData bot d n) (i j : I) :
    matProd n chain.mats i j = 0 ↔ ∀ mid : Fin (n - 1) → I, PathHasZero chain.mats i j mid :=
  matProd_eq_zero_iff_all_paths_hasZero hn chain.mats i j

/-- **HC02-P16 ($n = 1$ degeneration)**: At $n = 1$, the zero criterion reduces to $L^{(1)}_{i \to j} = 0$. -/
theorem lipChain_prod_one_eq_zero_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} (chain : LipChainData bot d 1) (i j : I) :
    (∀ mid : Fin 0 → I, PathHasZero chain.mats i j mid) ↔ chain.mats 0 i j = 0 := by
  constructor
  · intro h
    exact (pathHasZero_one_iff chain.mats i j Fin.elim0).mp (h Fin.elim0)
  · intro h mid
    exact (pathHasZero_one_iff chain.mats i j mid).mpr h

/-- **HC02-P17**: Along a co-Lip certificate chain of length $n \ge 1$, the product entry $(i \to j)$
is strictly positive if and only if there exists an intermediate index path with all edges positive. -/
theorem coLipChain_prod_pos_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} {n : ℕ} (hn : 1 ≤ n) (chain : CoLipChainData bot d n) (i j : I) :
    0 < matProd n chain.mats i j ↔ ∃ mid : Fin (n - 1) → I, PathAllPos chain.mats i j mid :=
  matProd_pos_iff_exists_path_allPos hn chain.mats i j

/-- **HC02-P17 ($n = 1$ degeneration)**: At $n = 1$, the unique empty intermediate sequence gives $K^{(1)}_{i \to j} > 0$. -/
theorem coLipChain_prod_one_pos_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} (chain : CoLipChainData bot d 1) (i j : I) :
    (∃ mid : Fin 0 → I, PathAllPos chain.mats i j mid) ↔ 0 < chain.mats 0 i j := by
  constructor
  · rintro ⟨mid, h⟩
    exact (pathAllPos_one_iff chain.mats i j mid).mp h
  · intro h
    exact ⟨Fin.elim0, (pathAllPos_one_iff chain.mats i j Fin.elim0).mpr h⟩

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=Ch02Channels.lean
import Ch02Certificates

/-!
# Chapter 2 — Channel Decoupling, Single-Channel Lip Constants, Bilateral Bounds, and Reflection

Formalizes obligations `HC02-D07` (decoupling predicates), `HC02-D08`, and
`HC02-P18` through `HC02-P32` from `source/02-operator-bounds.md`.
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-! ### Channel decoupling predicates (HC02-D07) -/

/-- Row decoupling of `ϕ` on `U` with respect to output component `j`:
there exists a restricted Lip certificate `L ∈ LipRestricted d ϕ U` whose `j`-th row
has at most one nonzero entry (at some input `i`). -/
def IsRowDecoupledAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ LipRestricted d ϕ U, ∃ i : I, RowSparseAt L i j

/-- Column decoupling of `ϕ` on `U` with respect to input component `i`:
there exists a restricted Lip certificate `L ∈ LipRestricted d ϕ U` whose `i`-th column
has at most one nonzero entry (at some output `j`). -/
def IsColDecoupledAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ LipRestricted d ϕ U, ∃ j : I, ColSparseAt L i j

/-- A certificate `L` yields a fully decoupled system for `ϕ` on `U` when `L` is
a diagonal matrix in `LipRestricted d ϕ U`. -/
def IsFullyDecoupledCert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  L ∈ LipRestricted d ϕ U ∧ IsDiagMatrix L

/-- `ϕ` admits a fully decoupled system certificate on `U`. -/
def IsFullyDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Prop :=
  ∃ L : GaugeMatrix I, IsFullyDecoupledCert d ϕ U L

/-! ### Single-channel feasible scalar set and infimum (HC02-D08, HC02-P18 to HC02-P24) -/

/-- Set $S_{i \to j}(\phi; U)$ of feasible scalar Lipschitz constants $\lambda \in \bar{\mathbb{R}}_+$
along channel `(i, j)` on domain $U \subseteq \mathrm{dom}(\phi)$. -/
def singleChannelFeasible {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { l : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ l * d i x y }

/-- Single-channel Lipschitz constant $\underline{L}_{i \to j}(\phi; U) := \inf S_{i \to j}(\phi; U)$
with `sInf ∅ = ⊤`. -/
noncomputable def singleChannelLip {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (singleChannelFeasible d ϕ U i j)

/-- **HC02-P18**: If there exist $x, y \in U$ with $d_i(x, y) = 0 < d_j(\phi(x), \phi(y))$,
then the feasible scalar set is empty and $\underline{L}_{i \to j}(\phi; U) = +\infty$. -/
theorem singleChannelFeasible_eq_empty_of_zero_pos {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (ϕ.func x) (ϕ.func y)) :
    singleChannelFeasible d ϕ U i j = ∅ := by
  ext l
  simp only [singleChannelFeasible, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hl
  have hle := hl x hx y hy
  rw [hin, mul_zero] at hle
  exact absurd hle (not_le_of_gt hout)

theorem singleChannelLip_eq_top_of_zero_pos {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (ϕ.func x) (ϕ.func y)) :
    singleChannelLip d ϕ U i j = ⊤ := by
  rw [singleChannelLip, singleChannelFeasible_eq_empty_of_zero_pos d ϕ hx hy hin hout, sInf_empty]

/-- **HC02-P20**: The feasible scalar set is upward closed. -/
theorem singleChannelFeasible_upward_closed {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {l₀ l₁ : ENNReal}
    (h0 : l₀ ∈ singleChannelFeasible d ϕ U i j) (hle : l₀ ≤ l₁) :
    l₁ ∈ singleChannelFeasible d ϕ U i j := by
  intro x hx y hy
  calc
    d j (ϕ.func x) (ϕ.func y) ≤ l₀ * d i x y := h0 x hx y hy
    _ ≤ l₁ * d i x y := by gcongr

/-- General form of **HC02-P21**: Every `l > singleChannelLip` (including `l = ⊤`) is feasible. -/
theorem singleChannelLip_lt_mem_feasible {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {l : ENNReal} (hl : singleChannelLip d ϕ U i j < l) :
    l ∈ singleChannelFeasible d ϕ U i j := by
  have hex : ∃ l₀ ∈ singleChannelFeasible d ϕ U i j, l₀ < l := by
    by_contra hno
    push Not at hno
    have hle : l ≤ singleChannelLip d ϕ U i j := le_sInf hno
    exact absurd hl (not_lt_of_ge hle)
  rcases hex with ⟨l₀, hl₀, hlt⟩
  exact singleChannelFeasible_upward_closed d ϕ hl₀ (le_of_lt hlt)

/-- **HC02-P21**: In the positive finite infimum regime $0 < a < +\infty$, every $\lambda > a$
(including $\lambda = +\infty$) belongs to the feasible scalar set. -/
theorem singleChannelLip_gt_mem_feasible_of_pos_lt_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    (_hpos : 0 < singleChannelLip d ϕ U i j) (_hlt : singleChannelLip d ϕ U i j < ⊤)
    {l : ENNReal} (hl : singleChannelLip d ϕ U i j < l) :
    l ∈ singleChannelFeasible d ϕ U i j :=
  singleChannelLip_lt_mem_feasible d ϕ hl

/-- **HC02-P19**: When $0 < \underline{L}_{i \to j}(\phi; U) < +\infty$, the infimum itself
belongs to $S_{i \to j}(\phi; U)$, i.e. the scalar bound holds for $a = \underline{L}_{i \to j}(\phi; U)$. -/
theorem singleChannelLip_mem_feasible_of_pos_lt_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    (hpos : 0 < singleChannelLip d ϕ U i j) (hlt : singleChannelLip d ϕ U i j < ⊤) :
    singleChannelLip d ϕ U i j ∈ singleChannelFeasible d ϕ U i j := by
  set a := singleChannelLip d ϕ U i j
  intro x hx y hy
  by_cases hB0 : d i x y = 0
  · have htop : (⊤ : ENNReal) ∈ singleChannelFeasible d ϕ U i j :=
      singleChannelLip_lt_mem_feasible d ϕ hlt
    have hle := htop x hx y hy
    rw [hB0, mul_zero] at hle
    simpa [hB0] using hle
  · by_cases hBtop : d i x y = ⊤
    · have ha_ne : a ≠ 0 := ne_of_gt hpos
      rw [hBtop, ENNReal.mul_top ha_ne]
      exact le_top
    · have hB_pos : 0 < d i x y := pos_iff_ne_zero.mpr hB0
      by_contra hnot
      have hlt_ab : a * d i x y < d j (ϕ.func x) (ϕ.func y) := lt_of_not_ge hnot
      have ha_div : a < d j (ϕ.func x) (ϕ.func y) / d i x y :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mpr hlt_ab
      obtain ⟨l, hal, hl_div⟩ := exists_between ha_div
      have hl_mem : l ∈ singleChannelFeasible d ϕ U i j :=
        singleChannelLip_lt_mem_feasible d ϕ hal
      have h_upper : d j (ϕ.func x) (ϕ.func y) ≤ l * d i x y := hl_mem x hx y hy
      have h_strict : l * d i x y < d j (ϕ.func x) (ϕ.func y) :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp hl_div
      exact absurd (lt_of_le_of_lt h_upper h_strict) (lt_irrefl _)

/-- **HC02-P22**: When $\underline{L}_{i \to j}(\phi; U) = 0$, every finite positive constant
$0 < \lambda < +\infty$ is a valid single-channel scalar certificate. -/
theorem finite_pos_mem_feasible_of_singleChannelLip_eq_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    (h0 : singleChannelLip d ϕ U i j = 0) {l : ENNReal} (hl_pos : 0 < l) (_hl_lt : l < ⊤) :
    l ∈ singleChannelFeasible d ϕ U i j := by
  apply singleChannelLip_lt_mem_feasible d ϕ
  rw [h0]
  exact hl_pos

/-- **HC02-P24**: $\underline{L}_{i \to j}(\phi; U) < +\infty$ if and only if there exists
a finite constant $\lambda < +\infty$ satisfying the pairwise scalar bound on $U$. -/
theorem singleChannelLip_lt_top_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I} :
    singleChannelLip d ϕ U i j < ⊤ ↔
      ∃ l : ENNReal, l < ⊤ ∧ l ∈ singleChannelFeasible d ϕ U i j := by
  constructor
  · intro hlt
    by_cases h0 : singleChannelLip d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact finite_pos_mem_feasible_of_singleChannelLip_eq_zero d ϕ h0 zero_lt_one ENNReal.one_lt_top
    · have hpos : 0 < singleChannelLip d ϕ U i j := pos_iff_ne_zero.mpr h0
      exact ⟨singleChannelLip d ϕ U i j, hlt,
        singleChannelLip_mem_feasible_of_pos_lt_top d ϕ hpos hlt⟩
  · rintro ⟨l, hlt, hl⟩
    exact lt_of_le_of_lt (sInf_le hl) hlt

/-! ### Counterexample for HC02-P23 and matrix-entry vs single-channel separation for HC02-D08 -/

/-- Discrete `{0, ⊤}` extended pseudo-metric on `Option Bool` with absorbing element `none`. -/
def discreteGauge (_ : Unit) (x y : Option Bool) : ENNReal :=
  if x = y then 0 else ⊤

theorem discreteGauge_extendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric (Option Bool) none (discreteGauge u) := by
  intro u
  refine
    { nonabsorbing := ⟨some false, by simp⟩
      dist_self := fun x => by simp [discreteGauge]
      symm := fun x y => by
        by_cases h : x = y <;> simp [discreteGauge, h, eq_comm]
      triangle := fun x y z => by
        by_cases hxz : x = z
        · subst hxz
          simp [discreteGauge]
        · by_cases hxy : x = y
          · subst hxy
            simp [discreteGauge, hxz]
          · simp [discreteGauge, hxz, hxy]
      isolate_bot := fun x hx => by simp [discreteGauge, hx] }

/-- **HC02-P23**: Counterexample showing $\underline{L}_{i \to j}(\phi; U) = 0$ need not be
achieved by $\lambda = 0$.
Uses a legal extended gauge space `(Option Bool, discreteGauge, none)` over `Unit`,
the identity operator `idOperator`, and nonempty `U = {some false, some true} ⊆ dom idOperator`. -/
theorem zero_singleChannelLip_not_necessarily_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
      singleChannelLip d ϕ U i j = 0 ∧
      0 ∉ singleChannelFeasible d ϕ U i j := by
  let U : Set (Option Bool) := {some false, some true}
  let ϕ : Operator (Option Bool) none := idOperator
  refine ⟨Option Bool, Unit, none, inferInstance, inferInstance,
    discreteGauge, discreteGauge_extendedPseudoMetric, ϕ, U, (), (), ?_, ?_, ?_, ?_⟩
  · exact ⟨some false, by simp [U]⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ϕ, idOperator]
  · have hpos_mem : ∀ l : ENNReal, 0 < l → l ∈ singleChannelFeasible discreteGauge ϕ U () () := by
      intro l hl x _ y _
      by_cases hxy : x = y
      · subst hxy
        simp [discreteGauge, ϕ]
      · simp [discreteGauge, ϕ, hxy, ENNReal.mul_top (ne_of_gt hl)]
    by_contra hne
    have hpos : 0 < singleChannelLip discreteGauge ϕ U () () := pos_iff_ne_zero.mpr hne
    obtain ⟨l, hl0, hla⟩ := exists_between hpos
    have hle : singleChannelLip discreteGauge ϕ U () () ≤ l := sInf_le (hpos_mem l hl0)
    exact absurd hla (not_lt_of_ge hle)
  · intro h0
    have hbad := h0 (some false) (by simp [U]) (some true) (by simp [U])
    simp [discreteGauge, ϕ] at hbad

/-- Auxiliary two-component gauge on `Option Bool` where component `false` collapses non-absorbing
points while component `true` separates them with `⊤`. -/
def twoCompWitnessGauge (b : Bool) (x y : Option Bool) : ENNReal :=
  match b with
  | false =>
    match x, y with
    | none, none => 0
    | none, some _ => ⊤
    | some _, none => ⊤
    | some _, some _ => 0
  | true =>
    if x = y then 0 else ⊤

theorem twoCompWitnessGauge_extendedPseudoMetric :
    ∀ b : Bool, ExtendedPseudoMetric (Option Bool) none (twoCompWitnessGauge b) := by
  intro b
  cases b with
  | false =>
    refine
      { nonabsorbing := ⟨some false, by simp⟩
        dist_self := fun x => by cases x <;> rfl
        symm := fun x y => by cases x <;> cases y <;> rfl
        triangle := fun x y z => by cases x <;> cases y <;> cases z <;> simp [twoCompWitnessGauge]
        isolate_bot := fun x hx => by cases x <;> simp_all [twoCompWitnessGauge] }
  | true =>
    refine
      { nonabsorbing := ⟨some false, by simp⟩
        dist_self := fun x => by simp [twoCompWitnessGauge]
        symm := fun x y => by by_cases h : x = y <;> simp [twoCompWitnessGauge, h, eq_comm]
        triangle := fun x y z => by
          by_cases hxz : x = z
          · subst hxz; simp [twoCompWitnessGauge]
          · by_cases hxy : x = y
            · subst hxy; simp [twoCompWitnessGauge, hxz]
            · simp [twoCompWitnessGauge, hxz, hxy]
        isolate_bot := fun x hx => by simp [twoCompWitnessGauge, hx] }

/-- **HC02-D08 (non-identification witness)**: `singleChannelLip d ϕ U i j` is a genuinely
different object from an arbitrary Lip matrix entry `L i j` (even on the same operator and domain). -/
theorem singleChannelLip_ne_matrix_entry_witness :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) (i j : I),
      U.Nonempty ∧ L ∈ LipRestricted d ϕ U ∧
      L i j ≠ singleChannelLip d ϕ U i j := by
  let U : Set (Option Bool) := {some false, some true}
  let ϕ : Operator (Option Bool) none := idOperator
  have hU : U ⊆ dom ϕ := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ϕ, idOperator]
  refine ⟨Option Bool, Bool, none, inferInstance, inferInstance,
    twoCompWitnessGauge, twoCompWitnessGauge_extendedPseudoMetric,
    ϕ, U, idMatrix, false, true, ⟨some false, by simp [U]⟩,
    idMatrix_mem_lipRestricted twoCompWitnessGauge hU, ?_⟩
  have hL : (idMatrix (I := Bool)) false true = 0 := idMatrix_apply_ne (by decide)
  have hsingle : singleChannelLip twoCompWitnessGauge ϕ U false true = ⊤ := by
    apply singleChannelLip_eq_top_of_zero_pos twoCompWitnessGauge ϕ
      (x := some false) (y := some true) (by simp [U]) (by simp [U])
    · rfl
    · simp [twoCompWitnessGauge, ϕ]
  rw [hL, hsingle]
  exact ENNReal.zero_ne_top

/-! ### Channel decoupling, zero-coefficient removal, bilateral bounds, reflection (HC02-P25 to HC02-P32) -/

/-- **HC02-P25**: A zero entry `L i j = 0` annihilates its term `L i j * d i x y = 0`
(even when `d i x y = ⊤`) and allows removing input `i` from the output-`j` sum. -/
theorem zero_coeff_mul_eq_zero {X I : Type} (d : I → X → X → ENNReal)
    {L : GaugeMatrix I} {i j : I} (h0 : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by
  rw [h0, zero_mul]

theorem sum_erase_of_coeff_zero {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {L : GaugeMatrix I} {i j : I} (h0 : L i j = 0) (x y : X) :
    (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  rw [← Finset.add_sum_erase Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i),
    zero_coeff_mul_eq_zero d h0 x y, zero_add]

theorem lipRestricted_erase_of_coeff_zero {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) {i j : I} (h0 : L i j = 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  rw [← sum_erase_of_coeff_zero d h0 x y]
  exact hL.2 x hx y hy j

/-- **HC02-P26**: Single-row sparsity at arbitrary `(i, j)` (not necessarily `i = j`)
yields the single-input scalar upper bound $d_j(\phi(x), \phi(y)) \le L_{i \to j} d_i(x, y)$. -/
theorem rowSparseAt_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) {i j : I} (hrow : RowSparseAt L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have hsum := hL.2 x hx y hy j
  have hsingle : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [hrow k hki, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rwa [hsingle] at hsum

theorem isRowDecoupledAt_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {j : I}
    (hdec : IsRowDecoupledAt d ϕ U j) :
    ∃ (L : GaugeMatrix I) (i : I), L ∈ LipRestricted d ϕ U ∧
      ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  rcases hdec with ⟨L, hL, i, hrow⟩
  exact ⟨L, i, hL, rowSparseAt_bound d ϕ hL hrow⟩

/-- **HC02-P27**: Single-column sparsity at `(i, j)` forces `L i k * d i x y = 0` for all `k ≠ j`,
so in `L`, input component `i` can contribute at most to output component `j`. -/
theorem colSparseAt_off_zero {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (_hL : L ∈ LipRestricted d ϕ U) {i j : I} (hcol : ColSparseAt L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U, L i k * d i x y = 0 := by
  intro k hkj x _ y _
  rw [hcol k hkj, zero_mul]

theorem colSparseAt_erase_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) {i j : I} (hcol : ColSparseAt L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y := by
  intro k hkj x hx y hy
  exact lipRestricted_erase_of_coeff_zero d ϕ hL (hcol k hkj) hx hy

theorem isColDecoupledAt_erase_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i : I}
    (hdec : IsColDecoupledAt d ϕ U i) :
    ∃ (L : GaugeMatrix I) (j : I), L ∈ LipRestricted d ϕ U ∧
      (∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U, L i k * d i x y = 0) ∧
      (∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y) := by
  rcases hdec with ⟨L, hL, j, hcol⟩
  exact ⟨L, j, hL, colSparseAt_off_zero d ϕ hL hcol, colSparseAt_erase_bound d ϕ hL hcol⟩

/-- **HC02-P28**: A diagonal Lip matrix gives componentwise scalar upper bounds for all components. -/
theorem diag_lip_bounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hdiag : IsDiagMatrix L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact rowSparseAt_bound d ϕ hL ((isDiagMatrix_iff_rowSparseAt L).mp hdiag j)

/-- **HC02-P29**: Bilateral scalar inequality for output component `j` requires only
Lip row sparsity `∀ k ≠ j, L k j = 0` (no sparsity assumed on `K`). -/
theorem diag_row_bilateral_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L K : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hK : K ∈ CoLipRestricted d ϕ U)
    {j : I} (hrow : RowSparseAt L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  constructor
  · exact (Finset.single_le_sum (f := fun k => K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ j)).trans (hK.2.2 x hx y hy j)
  · exact rowSparseAt_bound d ϕ hL hrow x hx y hy

/-- **HC02-P30 (componentwise bilateral bounds)**: If diagonal Lip row sparsity holds
for all `j : I`, bilateral scalar bounds hold simultaneously for all components. -/
theorem all_diag_row_bilateral_bounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L K : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hK : K ∈ CoLipRestricted d ϕ U)
    (hdiag : ∀ j : I, RowSparseAt L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  fun j => diag_row_bilateral_bound d ϕ hL hK (hdiag j)

/-- **HC02-P30 (finite scalar factor branch)**: If additionally `L j j < ⊤` and `K j j < ⊤`
for all `j : I`, the bilateral scalar bounds hold with finite `NNReal` scalar coefficients. -/
theorem all_diag_row_bilateral_bounds_finite {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L K : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hK : K ∈ CoLipRestricted d ϕ U)
    (hdiag : ∀ j : I, RowSparseAt L j j)
    (hLfin : ∀ j : I, L j j < ⊤) (hKfin : ∀ j : I, K j j < ⊤) :
    ∃ (k_fin l_fin : I → NNReal),
      ∀ j : I, (k_fin j : ENNReal) = K j j ∧ (l_fin j : ENNReal) = L j j ∧
        ∀ x ∈ U, ∀ y ∈ U,
          (k_fin j : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ (l_fin j : ENNReal) * d j x y := by
  refine ⟨fun j => (K j j).toNNReal, fun j => (L j j).toNNReal, fun j => ?_⟩
  have hk : ((K j j).toNNReal : ENNReal) = K j j := ENNReal.coe_toNNReal (ne_of_lt (hKfin j))
  have hl : ((L j j).toNNReal : ENNReal) = L j j := ENNReal.coe_toNNReal (ne_of_lt (hLfin j))
  refine ⟨hk, hl, fun x hx y hy => ?_⟩
  rw [hk, hl]
  exact all_diag_row_bilateral_bounds d ϕ hL hK hdiag j x hx y hy

/-- **HC02-P31**: A positive co-Lip entry `0 < K i j` preserves positive distance along
channel `(i, j)`: `0 < d i x y → 0 < d j (ϕ x) (ϕ y)`. -/
theorem coLip_pos_preserves_dist_pos {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {K : GaugeMatrix I} (hK : K ∈ CoLipRestricted d ϕ U)
    {i j : I} (hpos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdist
  have hmul : 0 < K i j * d i x y := ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hdist)
  have hle : K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    (Finset.single_le_sum (f := fun k => K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)
  exact lt_of_lt_of_le hmul hle

/-- **HC02-P32**: Positive diagonal co-Lip entries (`∀ j, 0 < K j j`) reflect
the full-gauge zero-distance equivalence relation `GaugeZeroRelated` ($\sim_{\mathcal{G}}$). -/
theorem coLip_pos_diag_reflects_gaugeZeroRelated {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {K : GaugeMatrix I} (hK : K ∈ CoLipRestricted d ϕ U)
    (hpos : ∀ j : I, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U, GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hdist : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout := coLip_pos_preserves_dist_pos d ϕ hK (hpos j) x hx y hy hdist
  rw [hrel j] at hout
  exact (lt_irrefl 0) hout

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch02Matrices
import Ch02Certificates
import Ch02Channels

/-!
# Main — Complete Formalization of Chapter 2 (`source/02-operator-bounds.md`)

Imports both frozen prerequisite modules from Chapter 1 and all target modules
for Chapter 2 (`Ch02Matrices`, `Ch02Certificates`, `Ch02Channels`).
-/
```

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "HC02-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrix"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipSet"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedLipMatrix"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipRestricted"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipRestricted_dom_eq_lipSet"
        }
      ],
      "representation": "在有限非空指标集 [Fintype I] [Nonempty I]、算子 ϕ : Operator X bot（含 ϕ.preserves_bot）及 ENNReal 伪度量族 d : I → X → X → ENNReal 下，定义全域合法 Lip 矩阵谓词 IsLipMatrix 与证书族 LipSet d ϕ（对应 ℒ(ϕ)），以及受限 Lip 矩阵谓词 IsRestrictedLipMatrix 与证书族 LipRestricted d ϕ U（对应 ℒ(ϕ)|_U，显式包含 U ⊆ dom ϕ 与 ∀ x ∈ U, ∀ y ∈ U, ∀ j, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, L i j * d i x y）；并证明 LipRestricted d ϕ (dom ϕ) = LipSet d ϕ。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedCoLipMatrix"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipRestricted"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_mem_coLipRestricted"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.top_entry_mem_coLipRestricted_of_zero_dist"
        }
      ],
      "representation": "定义 IsRestrictedCoLipMatrix 与 CoLipRestricted d ϕ U（对应 𝒦(ϕ)|_U），显式把 U.Nonempty 与 U ⊆ dom ϕ 写入定义本身，并要求 ∀ x ∈ U, ∀ y ∈ U, ∀ j, ∑ i, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)；矩阵条目与距离均取 ENNReal，zero_mem_coLipRestricted 与 top_entry_mem_coLipRestricted_of_zero_dist 额外确认 0 与 ∞ 均为合法系数。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.GaugeMatrix"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ofDisplayMatrix"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_apply"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul_apply"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_mul"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul_assoc"
        }
      ],
      "representation": "以输入优先类型 GaugeMatrix I := I → I → ENNReal 表示矩阵（M i j 对应 M_{i→j}，输入 i、输出 j）；toDisplayMatrix 将第 j 行第 i 列映射为 M i j，ofDisplayMatrix 互逆；matMul M₂ M₁ i j := ∑ k, M₂ k j * M₁ i k，并通过 toDisplayMatrix_mul 证明其严格对应普通显示矩阵乘法 (toDisplayMatrix M₂) * (toDisplayMatrix M₁)。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.idMatrix"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.toDisplayMatrix_id"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_zero"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_one"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_two"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matListProd"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matListProd_ofFn"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.idOperator"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.opComp"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.opSeqComp"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.opSeqComp_zero"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.opSeqComp_one"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.opSeqComp_eq_operatorChain"
        }
      ],
      "representation": "定义单位矩阵 idMatrix（δ_{ij}，并与显示单位矩阵 1 对应）；matProd k M 按执行顺序 ops 0, …, ops (k-1) 计算反序矩阵乘积 M^{(k)}⋯M^{(1)}，k=0 为 idMatrix（matProd_zero），k=1 为 M 0（matProd_one），并与列表版本 matListProd 等价（matListProd_ofFn）；opSeqComp k ops 实现 c_k = ϕ_k ∘ ⋯ ∘ ϕ_1 且 c_0 = idOperator，并通过 opSeqComp_eq_operatorChain 对齐前置模块的 OperatorChain。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.subset_dom_opComp_iff"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.prefixOpComp"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomainAux"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain_zero"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain_succ"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain_last_eq_image"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.chainDomain_subset_dom"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.LipChainData"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipChainData"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChain_domains_nonempty"
        }
      ],
      "representation": "chainDomain ops U₀ 通过递归 chainDomainAux 实现 U_{m+1} = ϕ_m(U_m)；chainDomain_subset_dom 证明由 U₀ ⊆ dom c_k 推出每步 U_m ⊆ dom ϕ_m；chainDomain_last_eq_image 证明全复合像 operator_image (opSeqComp k ops) U₀ 等于逐次像 chainDomain ops U₀ (Fin.last k)。LipChainData 与 CoLipChainData 仅存储 ops、U0、dom_subset、mats 与各实际输入域上的 step_valid，绝不把最终复合界作为字段。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathVertex"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathVertex_zero"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathVertex_last"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathAllPos"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.PathHasZero"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.empty_mid_seq_unique"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight_one"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathAllPos_one_iff"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathHasZero_one_iff"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight_pos_iff"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight_eq_zero_iff"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_apply_eq_sum_paths"
        }
      ],
      "representation": "对 n ≥ 1，以 mid : Fin (n - 1) → I 参数化全部无正性约束的中间指标序列，pathVertex i j mid 固定起点 k₀ = i、终点 k_n = j；pathWeight 为各层条目连乘；PathAllPos 为所有边 > 0，PathHasZero 为存在边 = 0；empty_mid_seq_unique 与 pathWeight_one/pathAllPos_one_iff/pathHasZero_one_iff 刻画 n = 1 时唯一空中间序列及其退化；matProd_apply_eq_sum_paths 证明乘积条目等于所有路径权重之和。",
      "dependencies": [
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.Channel"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.RowSparseAt"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ColSparseAt"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagMatrix"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.isDiagMatrix_iff_rowSparseAt"
        },
        {
          "file": "Ch02Matrices.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.isDiagMatrix_iff_colSparseAt"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRowDecoupledAt"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsColDecoupledAt"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsFullyDecoupledCert"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsFullyDecoupled"
        }
      ],
      "representation": "定义 Channel I := I × I；RowSparseAt L i j := ∀ k ≠ i, L k j = 0，行解耦 IsRowDecoupledAt d ϕ U j := ∃ L ∈ LipRestricted d ϕ U, ∃ i, RowSparseAt L i j；ColSparseAt L i j := ∀ k ≠ j, L i k = 0，列解耦 IsColDecoupledAt d ϕ U i := ∃ L ∈ LipRestricted d ϕ U, ∃ j, ColSparseAt L i j；对角矩阵 IsDiagMatrix L := ∀ i j, i ≠ j → L i j = 0 与完全解耦体系 IsFullyDecoupledCert / IsFullyDecoupled。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasible"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLip"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLip_ne_matrix_entry_witness"
        }
      ],
      "representation": "定义单通道可行标量集 singleChannelFeasible d ϕ U i j := { l : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ l * d i x y } 及下确界 singleChannelLip d ϕ U i j := sInf (singleChannelFeasible d ϕ U i j)（ENNReal 下 sInf ∅ = ⊤）；并通过 singleChannelLip_ne_matrix_entry_witness 证明其与合法 Lip 矩阵条目 L i j 一般不相等。",
      "dependencies": [
        "HC02-D01",
        "HC02-D04",
        "HC02-P14",
        "HC02-P18"
      ]
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipSet_singleton_iff"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipSet_unique_iff"
        }
      ],
      "representation": "当指标集仅含单元素 i（∀ k : I, k = i 或 Unique I）时，L ∈ LipSet d ϕ 当且仅当对所有 x, y ∈ dom ϕ 成立 d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipSet_subset_lipRestricted"
        }
      ],
      "representation": "对任意子集 U ⊆ dom ϕ，证明 LipSet d ϕ ⊆ LipRestricted d ϕ U（全域合法 Lip 矩阵在任意受限域上仍合法）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipRestricted_antitone"
        }
      ],
      "representation": "当 U ⊆ V（且 LipRestricted d ϕ V 成员已含 V ⊆ dom ϕ）时，证明 LipRestricted d ϕ V ⊆ LipRestricted d ϕ U（评估域缩小扩大证书族）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipEntryInf"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipEntryInf_mono"
        }
      ],
      "representation": "定义逐条目下确界 lipEntryInf d ϕ U i j := sInf { r : ENNReal | ∃ M ∈ LipRestricted d ϕ U, M i j = r }，并由 HC02-P03 与 sInf_le_sInf 证明 U ⊆ V → lipEntryInf d ϕ U i j ≤ lipEntryInf d ϕ V i j。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-P03"
      ]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipRestricted_comp"
        }
      ],
      "representation": "对 U₁ ⊆ dom (opComp ϕ₂ ϕ₁)、实际像域 U₂ = operator_image ϕ₁ U₁、L₁ ∈ LipRestricted d ϕ₁ U₁ 及 L₂ ∈ LipRestricted d ϕ₂ U₂，证明 matMul L₂ L₁ ∈ LipRestricted d (opComp ϕ₂ ϕ₁) U₁。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_entry_eq_zero_of_dist_zero"
        }
      ],
      "representation": "若 K ∈ CoLipRestricted d ϕ (dom ϕ) 且存在 x, y ∈ dom ϕ 使 d j (ϕ.func x) (ϕ.func y) = 0 与 0 < d i x y，则 K i j = 0。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipRestricted_comp"
        }
      ],
      "representation": "对 U₁ ⊆ dom (opComp ϕ₂ ϕ₁)、实际像域 U₂ = operator_image ϕ₁ U₁、K₁ ∈ CoLipRestricted d ϕ₁ U₁ 与 K₂ ∈ CoLipRestricted d ϕ₂ U₂，证明 matMul K₂ K₁ ∈ CoLipRestricted d (opComp ϕ₂ ϕ₁) U₁（其中非空性 U₁.Nonempty 作为 CoLipRestricted 的第一合取项一并成立）。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.commonDom₂"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_dist_forward"
        }
      ],
      "representation": "在扩展伪度量族 hd、U ⊆ commonDom₂ ϕ₁ ϕ₂ (= dom ϕ₁ ∩ dom ϕ₂) 与逐点扰动前提 ∀ z ∈ U, ∀ j, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j 下，对任意 x, y ∈ U 与 j : I 证明 d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_dist_backward"
        }
      ],
      "representation": "在相同前提下交换 ϕ₁ 与 ϕ₂，利用对称性调用 HC02-P08 证明 d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j。",
      "dependencies": [
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_lip_bridge"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_lip_bridge_symm"
        }
      ],
      "representation": "在 HC02-P08 前提下再设 L₁ ∈ LipRestricted d ϕ₁ U，证明 d j (ϕ₂.func x) (ϕ₂.func y) ≤ (∑ i, L₁ i j * d i x y) + 2 * δ j；perturbation_lip_bridge_symm 同步给出交换 ϕ₁, ϕ₂ 的对称桥接结论。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_coLip_bridge"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_coLip_bridge_symm"
        }
      ],
      "representation": "在 HC02-P09 前提下再设 K₁ ∈ CoLipRestricted d ϕ₁ U，证明 ∑ i, K₁ i j * d i x y ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j；perturbation_coLip_bridge_symm 同步给出交换 ϕ₁, ϕ₂ 的对称桥接结论。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-P09"
      ]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChain_prod_mem_all"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChain_prod_mem"
        }
      ],
      "representation": "对 k ≥ 1 与逐步证书链 chain : LipChainData bot d k（其中各 mats m 在实际像域 chainDomain chain.ops chain.U0 m.castSucc 上合法），对链长作归纳由 HC02-P14 与 HC02-P05 证明 matProd k chain.mats ∈ LipRestricted d (opSeqComp k chain.ops) chain.U0。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D04",
        "HC02-D05",
        "HC02-P05",
        "HC02-P14"
      ]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChain_succ_prod_mem"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChain_prod_mem"
        }
      ],
      "representation": "对 k ≥ 1 与逐步 co-Lip 证书链 chain : CoLipChainData bot d k（每步 CoLipRestricted 自动含实际输入域非空性），从 k = 1 起按 HC02-P07 归纳证明 matProd k chain.mats ∈ CoLipRestricted d (opSeqComp k chain.ops) chain.U0。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D04",
        "HC02-D05",
        "HC02-P07"
      ]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.idMatrix_mem_lipRestricted"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_idMatrix_mem_lipRestricted"
        }
      ],
      "representation": "在 k = 0 边界情形（c₀ = idOperator、matProd 0 = idMatrix）及非空 U ⊆ dom idOperator 下，证明 matProd 0 mats ∈ LipRestricted d (opSeqComp 0 ops) U。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.idMatrix_mem_coLipRestricted"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_step_idMatrix_mem_coLipRestricted"
        }
      ],
      "representation": "在同一非空 U ⊆ dom idOperator 上，证明 matProd 0 mats ∈ CoLipRestricted d (opSeqComp 0 ops) U。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_eq_zero_iff_all_paths_hasZero"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChain_prod_eq_zero_iff"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipChain_prod_one_eq_zero_iff"
        }
      ],
      "representation": "在 n ≥ 1 的 LipChainData 上下文与局部证书序列下，证明 matProd n chain.mats i j = 0 当且仅当对所有中间序列 mid : Fin (n - 1) → I 均成立 PathHasZero chain.mats i j mid；并由 lipChain_prod_one_eq_zero_iff 给出 n = 1 时退化为 chain.mats 0 i j = 0。",
      "dependencies": [
        "HC02-D04",
        "HC02-D05",
        "HC02-D06"
      ]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_pos_iff_exists_path_allPos"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChain_prod_pos_iff"
        },
        {
          "file": "Ch02Certificates.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipChain_prod_one_pos_iff"
        }
      ],
      "representation": "在 n ≥ 1 的 CoLipChainData 上下文与局部证书序列下，证明 0 < matProd n chain.mats i j 当且仅当存在中间序列 mid : Fin (n - 1) → I 满足 PathAllPos chain.mats i j mid；并由 coLipChain_prod_one_pos_iff 给出 n = 1 时退化为 0 < chain.mats 0 i j。",
      "dependencies": [
        "HC02-D04",
        "HC02-D05",
        "HC02-D06"
      ]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasible_eq_empty_of_zero_pos"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLip_eq_top_of_zero_pos"
        }
      ],
      "representation": "若存在 x, y ∈ U 使 d i x y = 0 且 0 < d j (ϕ.func x) (ϕ.func y)，则证明 singleChannelFeasible d ϕ U i j = ∅（不存在任何 ENNReal 标量证书）且 singleChannelLip d ϕ U i j = ⊤。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLip_mem_feasible_of_pos_lt_top"
        }
      ],
      "representation": "若 0 < singleChannelLip d ϕ U i j 且 singleChannelLip d ϕ U i j < ⊤，分 d i x y = 0、d i x y = ⊤ 与 0 < d i x y < ⊤ 三类证明 singleChannelLip d ϕ U i j ∈ singleChannelFeasible d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P21"
      ]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelFeasible_upward_closed"
        }
      ],
      "representation": "若 l₀ ∈ singleChannelFeasible d ϕ U i j 且 l₀ ≤ l₁，则 l₁ ∈ singleChannelFeasible d ϕ U i j（标量可行族向上封闭）。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLip_lt_mem_feasible"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLip_gt_mem_feasible_of_pos_lt_top"
        }
      ],
      "representation": "singleChannelLip_lt_mem_feasible 对任意满足 singleChannelLip d ϕ U i j < l（含 l = ⊤）的 l 证明 l ∈ singleChannelFeasible d ϕ U i j；singleChannelLip_gt_mem_feasible_of_pos_lt_top 显式对应 0 < a < ∞ 语境。",
      "dependencies": [
        "HC02-D08",
        "HC02-P20"
      ]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.finite_pos_mem_feasible_of_singleChannelLip_eq_zero"
        }
      ],
      "representation": "当 singleChannelLip d ϕ U i j = 0 时，证明任意满足 0 < l < ⊤ 的 l 均属于 singleChannelFeasible d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P21"
      ]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.discreteGauge"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.discreteGauge_extendedPseudoMetric"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_singleChannelLip_not_necessarily_attained"
        }
      ],
      "representation": "构造合法扩展规范空间 (Option Bool, discreteGauge, none)（discreteGauge_extendedPseudoMetric 验证全部 5 条 ExtendedPseudoMetric 公理）、合法算子 idOperator 及非空合法子集 U = {some false, some true} ⊆ dom idOperator，证明 singleChannelLip = 0 但 0 ∉ singleChannelFeasible。",
      "dependencies": [
        "HC02-D04",
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLip_lt_top_iff"
        }
      ],
      "representation": "证明 singleChannelLip d ϕ U i j < ⊤ 当且仅当存在 l < ⊤ 使 l ∈ singleChannelFeasible d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P19",
        "HC02-P22"
      ]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_coeff_mul_eq_zero"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_erase_of_coeff_zero"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipRestricted_erase_of_coeff_zero"
        }
      ],
      "representation": "当 L i j = 0 时（允许 d i x y = ⊤），由 ENNReal.zero_mul 证明 L i j * d i x y = 0，从而输出 j 的求和可移除输入项 i（∑ k, L k j * d k x y = ∑ k ∈ Finset.univ.erase i, L k j * d k x y），并对 L ∈ LipRestricted d ϕ U 给出删项后的上界。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.rowSparseAt_bound"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.isRowDecoupledAt_bound"
        }
      ],
      "representation": "对任意独立指标 i, j : I（不要求 i = j），若 L ∈ LipRestricted d ϕ U 且 RowSparseAt L i j，则 ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y；isRowDecoupledAt_bound 给出存在型行解耦版本。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D07"
      ]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.colSparseAt_off_zero"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.colSparseAt_erase_bound"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.isColDecoupledAt_erase_bound"
        }
      ],
      "representation": "若 L ∈ LipRestricted d ϕ U 且 ColSparseAt L i j（固定输入 i 列仅输出 j 可能非零），证明对所有 k ≠ j 与 x, y ∈ U 有 L i k * d i x y = 0（colSparseAt_off_zero），且输出 k 的上界求和可删去输入 i（colSparseAt_erase_bound），从而输入 i 在该上界证书中至多向输出 j 贡献；isColDecoupledAt_erase_bound 给出存在型列解耦版本。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D07",
        "HC02-P25"
      ]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.diag_lip_bounds"
        }
      ],
      "representation": "若 L ∈ LipRestricted d ϕ U 且 IsDiagMatrix L（所有非对角项为 0），证明 ∀ j, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.diag_row_bilateral_bound"
        }
      ],
      "representation": "设 L ∈ LipRestricted d ϕ U 与 K ∈ CoLipRestricted d ϕ U，仅假设 RowSparseAt L j j（不对 K 加任何稀疏假设），证明 ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧ d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.all_diag_row_bilateral_bounds"
        },
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.all_diag_row_bilateral_bounds_finite"
        }
      ],
      "representation": "all_diag_row_bilateral_bounds 在 ∀ j, RowSparseAt L j j 条件下给出全部分量的双侧标量界；all_diag_row_bilateral_bounds_finite 在额外假设 ∀ j, L j j < ⊤ 且 K j j < ⊤ 下提取有限非负实标量系数 k_fin, l_fin : I → NNReal 并给出逐分量双侧界。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03",
        "HC02-D07",
        "HC02-P29"
      ]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_pos_preserves_dist_pos"
        }
      ],
      "representation": "若 K ∈ CoLipRestricted d ϕ U 且 0 < K i j，证明 ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y)。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02Channels.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_pos_diag_reflects_gaugeZeroRelated"
        }
      ],
      "representation": "若 K ∈ CoLipRestricted d ϕ U 且 ∀ j : I, 0 < K j j，证明 ∀ x ∈ U, ∀ y ∈ U, GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y（即 ϕ(x) ~_𝒢 ϕ(y) ⇒ x ~_𝒢 y）。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-P31"
      ]
    }
  ]
}
```

### 完成度、严格对齐与验证说明

- **是否已完整完成且严格对齐整章**：**是**。[Ch02Matrices.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/Ch02Matrices.lean)、[Ch02Certificates.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/Ch02Certificates.lean)、[Ch02Channels.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/Ch02Channels.lean)、[Main.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/Main.lean) 与 [alignment.json](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/alignment.json) 已按 [02-operator-bounds.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/source/02-operator-bounds.md) 的量词、定义域（含 $\mathscr{K}(\phi)|_U$ 的非空性与 $U \subseteq \mathrm{dom}(\phi)$）、系数与距离的值域（`ENNReal`）、逐步链字段（`LipChainData`/`CoLipChainData` 不把复合界作为字段）、条件与结论强度严格形式化，并覆盖 [obligations.json](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/obligations.json) 的全部 40 项义务（40 项状态均为 `"complete"`）。
- **本会话最终编译、清单与公理检查实测结果**：
  - 使用 Lean 4.29.1（[LEAN_ENV.sh](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/LEAN_ENV.sh) 环境）依次编译 `Ch02Matrices.lean`、`Ch02Certificates.lean`、`Ch02Channels.lean`、`Main.lean` 均退出码 `0` 无报错。
  - [alignment.json](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/alignment.json) 与 [obligations.json](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/obligations.json) 的 40 个 ID 精确一一匹配，依赖引用与文件声明位置检查全部通过。
  - 对 4 份 Lean 文件按词边界扫描禁用关键字（`sorry`、`admit`、`axiom`、`opaque`、`unsafe`、`native_decide`、`ofReduceBool`、`implemented_by`）均无任何匹配。
  - 对 [alignment.json](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/HCH02/physical-1/session/work/alignment.json) 所列全部 123 个唯一声明执行 `#check` 与 `#print axioms`，Lean 核验证退出码为 `0`（123 条公理报告），观测到的逻辑公理仅限于 `['Classical.choice', 'Quot.sound', 'propext']`。
- **未完成或未确认的范围**：**无**（全部 40 项义务均已完成、对齐并经当前版本终审通过）。
