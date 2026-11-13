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
