/-
  Formalization of matrix-bound foundations for Operator Evolution Theory (OET),
  Volume I, Chapter 2 (finite matrix bounds, ordered products, and index-path criteria).

  Original mathematical theory by Zhe Li (Glen Li / glenzli),
  The Operator Evolution Theory, Volume I, v1.0.0, licensed under CC BY 4.0.
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace LCH02

universe u

section MatrixConventions

/--
**CH02-D03**: Extended nonnegative matrix over index set `I`.
Following the OET convention, output component `j` is the row index and
input component `i` is the column index, so `L_{i -> j}` sits at `(j, i)`.
-/
abbrev GaugeMatrix (I : Type u) : Type u := Matrix I I ENNReal

/--
**CH02-D03**: Entry `M_{i -> j}` from input component `i` to output component `j`,
defined as `M j i` (row = output `j`, column = input `i`).
-/
def matrixEntry {I : Type u} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

@[simp]
theorem matrixEntry_apply {I : Type u} (M : GaugeMatrix I) (i j : I) :
    matrixEntry M i j = M j i :=
  rfl

/-- Construct a `GaugeMatrix` from channel weights `f i j = M_{i -> j}`. -/
def ofChannel {I : Type u} (f : I → I → ENNReal) : GaugeMatrix I :=
  Matrix.of (fun j i => f i j)

@[simp]
theorem matrixEntry_ofChannel {I : Type u} (f : I → I → ENNReal) (i j : I) :
    matrixEntry (ofChannel f) i j = f i j :=
  rfl

/--
**CH02-D03**: Algebraic matrix product in channel-entry form:
`(M₂ * M₁)_{i -> j} = ∑ k, (M₂)_{k -> j} * (M₁)_{i -> k}`.
-/
theorem matrixEntry_mul {I : Type u} [Fintype I] (M₂ M₁ : GaugeMatrix I) (i j : I) :
    matrixEntry (M₂ * M₁) i j = ∑ k : I, matrixEntry M₂ k j * matrixEntry M₁ i k := by
  simp [matrixEntry, Matrix.mul_apply]

/-- Sum-exchange identity for matrix multiplication acting on a nonnegative vector `v`. -/
theorem matrixEntry_mul_sum_eq {I : Type u} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (v : I → ENNReal) (j : I) :
    ∑ i : I, matrixEntry (M₂ * M₁) i j * v i =
      ∑ k : I, matrixEntry M₂ k j * ∑ i : I, matrixEntry M₁ i k * v i := by
  calc
    ∑ i : I, matrixEntry (M₂ * M₁) i j * v i
        = ∑ i : I, (∑ k : I, matrixEntry M₂ k j * matrixEntry M₁ i k) * v i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [matrixEntry_mul]
    _ = ∑ i : I, ∑ k : I, (matrixEntry M₂ k j * matrixEntry M₁ i k) * v i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, (matrixEntry M₂ k j * matrixEntry M₁ i k) * v i :=
            Finset.sum_comm
    _ = ∑ k : I, ∑ i : I, matrixEntry M₂ k j * (matrixEntry M₁ i k * v i) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
            rw [mul_assoc]
    _ = ∑ k : I, matrixEntry M₂ k j * ∑ i : I, matrixEntry M₁ i k * v i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]

end MatrixConventions

section OrderedProducts

noncomputable section

/-- **CH02-D04**: Identity matrix `I` under the input/output convention. -/
def matrixOne {I : Type u} [DecidableEq I] : GaugeMatrix I :=
  (1 : Matrix I I ENNReal)

@[simp]
theorem matrixEntry_one {I : Type u} [DecidableEq I] (i j : I) :
    matrixEntry (matrixOne : GaugeMatrix I) i j = if i = j then 1 else 0 := by
  simp [matrixEntry, matrixOne, Matrix.one_apply, eq_comm]

/--
**CH02-D04**: Ordered nonempty matrix product `M^{(m+1)} * ... * M^{(1)}`
for a sequence indexed by `Fin (m + 1)` in step order (`0` applied first, `m` last).
-/
def matrixPosProd {I : Type u} [Fintype I] :
    {m : ℕ} → (Fin (m + 1) → GaugeMatrix I) → GaugeMatrix I
  | 0, Ms => Ms 0
  | m + 1, Ms => Ms (Fin.last (m + 1)) * matrixPosProd (fun r : Fin (m + 1) => Ms r.castSucc)

@[simp]
theorem matrixPosProd_zero {I : Type u} [Fintype I] (Ms : Fin 1 → GaugeMatrix I) :
    matrixPosProd Ms = Ms 0 :=
  rfl

@[simp]
theorem matrixPosProd_succ {I : Type u} [Fintype I] {m : ℕ}
    (Ms : Fin (m + 2) → GaugeMatrix I) :
    matrixPosProd Ms =
      Ms (Fin.last (m + 1)) * matrixPosProd (fun r : Fin (m + 1) => Ms r.castSucc) :=
  rfl

/--
**CH02-D04**: Ordered nonempty matrix product `M^{(n)} * ... * M^{(1)}`
for any `n ≥ 1` (`hn : 0 < n`).
-/
def matrixNonemptyProd {I : Type u} [Fintype I] {n : ℕ} (hn : 0 < n)
    (Ms : Fin n → GaugeMatrix I) : GaugeMatrix I :=
  match n, hn with
  | 0, hn => absurd hn (Nat.lt_irrefl 0)
  | _ + 1, _ => matrixPosProd Ms

@[simp]
theorem matrixNonemptyProd_one {I : Type u} [Fintype I] (Ms : Fin 1 → GaugeMatrix I) :
    matrixNonemptyProd Nat.one_pos Ms = Ms 0 :=
  rfl

theorem matrixNonemptyProd_succ {I : Type u} [Fintype I] {m : ℕ}
    (Ms : Fin (m + 2) → GaugeMatrix I) :
    matrixNonemptyProd (Nat.succ_pos (m + 1)) Ms =
      Ms (Fin.last (m + 1)) *
        matrixNonemptyProd (Nat.succ_pos m) (fun r : Fin (m + 1) => Ms r.castSucc) :=
  rfl

/--
**CH02-D04**: General ordered matrix product for `n : ℕ` matrices,
defining the empty product (`n = 0`) as the identity matrix `matrixOne`.
-/
def matrixProd {I : Type u} [Fintype I] [DecidableEq I] :
    {n : ℕ} → (Fin n → GaugeMatrix I) → GaugeMatrix I
  | 0, _ => matrixOne
  | _ + 1, Ms => matrixPosProd Ms

@[simp]
theorem matrixProd_zero {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : Fin 0 → GaugeMatrix I) :
    matrixProd Ms = matrixOne :=
  rfl

theorem matrixProd_eq_nonemptyProd {I : Type u} [Fintype I] [DecidableEq I]
    {n : ℕ} (hn : 0 < n) (Ms : Fin n → GaugeMatrix I) :
    matrixProd Ms = matrixNonemptyProd hn Ms := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m => rfl

theorem matrixProd_succ {I : Type u} [Fintype I] [DecidableEq I] {n : ℕ}
    (Ms : Fin (n + 1) → GaugeMatrix I) :
    matrixProd Ms = Ms (Fin.last n) * matrixProd (fun r : Fin n => Ms r.castSucc) := by
  cases n with
  | zero =>
      simp [matrixProd, matrixPosProd, matrixOne]
  | succ m =>
      rfl

theorem matrixPosProd_eq_list_reverse_prod {I : Type u} [Fintype I] [DecidableEq I] :
    {m : ℕ} → (Ms : Fin (m + 1) → GaugeMatrix I) →
      matrixPosProd Ms = (List.ofFn Ms).reverse.prod
  | 0, Ms => by
      simp [matrixPosProd, List.ofFn_succ]
  | m + 1, Ms => by
      have ih := matrixPosProd_eq_list_reverse_prod (fun r : Fin (m + 1) => Ms r.castSucc)
      rw [matrixPosProd_succ, ih]
      conv_rhs => rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
      simp

theorem matrixProd_eq_list_reverse_prod {I : Type u} [Fintype I] [DecidableEq I]
    {n : ℕ} (Ms : Fin n → GaugeMatrix I) :
    matrixProd Ms = (List.ofFn Ms).reverse.prod := by
  cases n with
  | zero => simp [matrixProd, matrixOne]
  | succ m => exact matrixPosProd_eq_list_reverse_prod Ms

end

end OrderedProducts

section IndexPaths

/--
**CH02-D06**: Interior index sequence `(k_1, ..., k_{n-1})` for `n` matrices.
When `n = 1`, `n - 1 = 0`, so `InteriorPath I 1 = (Fin 0 → I)` is uniquely the empty sequence.
-/
abbrev InteriorPath (I : Type u) (n : ℕ) : Type u :=
  Fin (n - 1) → I

/-- Full vertex sequence `(k_0, ..., k_{m+1})` with `k_0 = i` and `k_{m+1} = j`. -/
def pathNodesPos {I : Type u} {m : ℕ} (i j : I) (p : Fin m → I) : Fin (m + 2) → I :=
  Fin.snoc (Fin.cons i p) j

/--
**CH02-D06**: Full index sequence `(k_0, k_1, ..., k_n)` built from endpoints `k_0 = i`,
`k_n = j`, and interior sequence `p : InteriorPath I n` (for `hn : 0 < n`).
-/
def pathNodes {I : Type u} {n : ℕ} (hn : 0 < n) (i j : I)
    (p : InteriorPath I n) : Fin (n + 1) → I :=
  match n, hn, p with
  | 0, hn, _ => absurd hn (Nat.lt_irrefl 0)
  | _ + 1, _, p => pathNodesPos i j p

@[simp]
theorem pathNodesPos_zero {I : Type u} {m : ℕ} (i j : I) (p : Fin m → I) :
    pathNodesPos i j p 0 = i := by
  unfold pathNodesPos
  rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc from rfl, Fin.snoc_castSucc]
  simp

@[simp]
theorem pathNodesPos_last {I : Type u} {m : ℕ} (i j : I) (p : Fin m → I) :
    pathNodesPos i j p (Fin.last (m + 1)) = j := by
  simp [pathNodesPos]

@[simp]
theorem pathNodes_zero {I : Type u} {n : ℕ} (hn : 0 < n) (i j : I)
    (p : InteriorPath I n) :
    pathNodes hn i j p 0 = i := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m => exact pathNodesPos_zero i j p

@[simp]
theorem pathNodes_last {I : Type u} {n : ℕ} (hn : 0 < n) (i j : I)
    (p : InteriorPath I n) :
    pathNodes hn i j p (Fin.last n) = j := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m => exact pathNodesPos_last i j p

/-- For `n = 1`, the interior index sequence is uniquely the empty sequence. -/
instance interiorPath_one_unique {I : Type u} : Unique (InteriorPath I 1) where
  default := fun r => Fin.elim0 r
  uniq _ := funext fun r => Fin.elim0 r

@[simp]
theorem pathNodes_one_zero {I : Type u} (i j : I) (p : InteriorPath I 1) :
    pathNodes Nat.one_pos i j p 0 = i :=
  pathNodes_zero Nat.one_pos i j p

@[simp]
theorem pathNodes_one_one {I : Type u} (i j : I) (p : InteriorPath I 1) :
    pathNodes Nat.one_pos i j p 1 = j :=
  pathNodes_last Nat.one_pos i j p

theorem pathNodesPos_succ_castSucc_eq {I : Type u} {m : ℕ} (i j : I)
    (p : Fin (m + 1) → I) (r : Fin (m + 2)) :
    pathNodesPos i j p r.castSucc =
      pathNodesPos i (p (Fin.last m)) (fun q : Fin m => p q.castSucc) r := by
  unfold pathNodesPos
  rw [Fin.snoc_castSucc]
  induction r using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      simp
  | cast s =>
      rw [Fin.snoc_castSucc]
      induction s using Fin.cases with
      | zero => simp
      | succ t => simp

/--
**CH02-D06**: Step-`r` matrix entry `[M^{(r)}]_{k_{r-1} -> k_r}` along a path `p`.
-/
def pathStepEntry {I : Type u} {n : ℕ} (Ms : Fin n → GaugeMatrix I)
    (hn : 0 < n) (i j : I) (p : InteriorPath I n) (r : Fin n) : ENNReal :=
  matrixEntry (Ms r)
    (pathNodes hn i j p r.castSucc)
    (pathNodes hn i j p r.succ)

/-- **CH02-D06**: All-positive path predicate: every step entry along `p` is strictly positive. -/
def IsPositivePath {I : Type u} {n : ℕ} (Ms : Fin n → GaugeMatrix I)
    (hn : 0 < n) (i j : I) (p : InteriorPath I n) : Prop :=
  ∀ r : Fin n, 0 < pathStepEntry Ms hn i j p r

/-- **CH02-D06**: Zero-factor path predicate: at least one step entry along `p` equals `0`. -/
def HasZeroFactorPath {I : Type u} {n : ℕ} (Ms : Fin n → GaugeMatrix I)
    (hn : 0 < n) (i j : I) (p : InteriorPath I n) : Prop :=
  ∃ r : Fin n, pathStepEntry Ms hn i j p r = 0

theorem not_isPositivePath_iff_hasZeroFactorPath {I : Type u} {n : ℕ}
    (Ms : Fin n → GaugeMatrix I) (hn : 0 < n) (i j : I) (p : InteriorPath I n) :
    ¬ IsPositivePath Ms hn i j p ↔ HasZeroFactorPath Ms hn i j p := by
  simp [IsPositivePath, HasZeroFactorPath, pos_iff_ne_zero]

@[simp]
theorem pathStepEntry_one {I : Type u} (Ms : Fin 1 → GaugeMatrix I)
    (i j : I) (p : InteriorPath I 1) (r : Fin 1) :
    pathStepEntry Ms Nat.one_pos i j p r = matrixEntry (Ms 0) i j := by
  have hr : r = 0 := Fin.eq_zero r
  subst hr
  simp [pathStepEntry]

theorem isPositivePath_one_iff {I : Type u} (Ms : Fin 1 → GaugeMatrix I)
    (i j : I) (p : InteriorPath I 1) :
    IsPositivePath Ms Nat.one_pos i j p ↔ 0 < matrixEntry (Ms 0) i j := by
  simp [IsPositivePath]

theorem hasZeroFactorPath_one_iff {I : Type u} (Ms : Fin 1 → GaugeMatrix I)
    (i j : I) (p : InteriorPath I 1) :
    HasZeroFactorPath Ms Nat.one_pos i j p ↔ matrixEntry (Ms 0) i j = 0 := by
  simp [HasZeroFactorPath]

/-- Explicit endpoint-constrained index path representation, equivalent to `InteriorPath`. -/
@[ext]
structure IndexPath (I : Type u) (n : ℕ) (i j : I) where
  nodes : Fin (n + 1) → I
  start_eq : nodes 0 = i
  end_eq : nodes (Fin.last n) = j

/-- Canonical equivalence between interior sequences `(k_1, ..., k_{n-1})` and endpoint-fixed paths. -/
def interiorPathEquivIndexPath {I : Type u} {n : ℕ} (hn : 0 < n) (i j : I) :
    InteriorPath I n ≃ IndexPath I n i j where
  toFun p :=
    { nodes := pathNodes hn i j p
      start_eq := pathNodes_zero hn i j p
      end_eq := pathNodes_last hn i j p }
  invFun q :=
    match n, hn, q with
    | 0, hn, _ => absurd hn (Nat.lt_irrefl 0)
    | _ + 1, _, q => fun r => q.nodes r.succ.castSucc
  left_inv p := by
    cases n with
    | zero => exact absurd hn (Nat.lt_irrefl 0)
    | succ m =>
        ext r
        change pathNodesPos i j p r.succ.castSucc = p r
        unfold pathNodesPos
        rw [Fin.snoc_castSucc, Fin.cons_succ]
  right_inv q := by
    cases n with
    | zero => exact absurd hn (Nat.lt_irrefl 0)
    | succ m =>
        ext s
        induction s using Fin.lastCases with
        | last =>
            simpa [pathNodes, pathNodesPos] using q.end_eq.symm
        | cast t =>
            change pathNodesPos i j (fun r : Fin m => q.nodes r.succ.castSucc) t.castSucc = q.nodes t.castSucc
            unfold pathNodesPos
            rw [Fin.snoc_castSucc]
            induction t using Fin.cases with
            | zero =>
                simpa using q.start_eq.symm
            | succ u =>
                simp

end IndexPaths

section PathCriteria

private theorem pathNodesPos_step_prefix {I : Type u} {m : ℕ} (i j : I)
    (p : Fin (m + 1) → I) (r : Fin (m + 1)) :
    pathNodesPos i j p r.castSucc.castSucc =
      pathNodesPos i (p (Fin.last m)) (fun q : Fin m => p q.castSucc) r.castSucc ∧
    pathNodesPos i j p r.castSucc.succ =
      pathNodesPos i (p (Fin.last m)) (fun q : Fin m => p q.castSucc) r.succ := by
  constructor
  · exact pathNodesPos_succ_castSucc_eq i j p r.castSucc
  · exact pathNodesPos_succ_castSucc_eq i j p r.succ

private theorem pathNodesPos_step_last {I : Type u} {m : ℕ} (i j : I)
    (p : Fin (m + 1) → I) :
    pathNodesPos i j p (Fin.last (m + 1)).castSucc = p (Fin.last m) ∧
    pathNodesPos i j p (Fin.last (m + 1)).succ = j := by
  constructor
  · unfold pathNodesPos
    rw [Fin.snoc_castSucc, Fin.cons_last]
  · simp [pathNodesPos]

private theorem matrixPosProd_entry_eq_zero_iff {I : Type u} [Fintype I] :
    {m : ℕ} → (Ms : Fin (m + 1) → GaugeMatrix I) → (i j : I) →
      (matrixEntry (matrixPosProd Ms) i j = 0 ↔
        ∀ p : Fin m → I, ∃ r : Fin (m + 1),
          matrixEntry (Ms r)
            (pathNodesPos i j p r.castSucc)
            (pathNodesPos i j p r.succ) = 0)
  | 0, Ms, i, j => by
      simp [matrixPosProd, pathNodesPos, Fin.snoc]
  | m + 1, Ms, i, j => by
      have ih := matrixPosProd_entry_eq_zero_iff (fun r : Fin (m + 1) => Ms r.castSucc)
      rw [matrixPosProd_succ, matrixEntry_mul, Finset.sum_eq_zero_iff]
      simp only [Finset.mem_univ, true_implies, mul_eq_zero]
      constructor
      · intro h p
        rcases h (p (Fin.last m)) with hLast | hPrev
        · refine ⟨Fin.last (m + 1), ?_⟩
          rcases pathNodesPos_step_last i j p with ⟨h1, h2⟩
          rw [h1, h2]
          exact hLast
        · rw [ih i (p (Fin.last m))] at hPrev
          rcases hPrev (fun q : Fin m => p q.castSucc) with ⟨r, hr⟩
          refine ⟨r.castSucc, ?_⟩
          rcases pathNodesPos_step_prefix i j p r with ⟨h1, h2⟩
          rw [h1, h2]
          exact hr
      · intro h k
        by_cases hLast : matrixEntry (Ms (Fin.last (m + 1))) k j = 0
        · exact Or.inl hLast
        · refine Or.inr ((ih i k).2 ?_)
          intro p'
          let p : Fin (m + 1) → I := Fin.snoc p' k
          rcases h p with ⟨r, hr⟩
          induction r using Fin.lastCases with
          | last =>
              exfalso
              have hp_last : p (Fin.last m) = k := by simp [p]
              rcases pathNodesPos_step_last i j p with ⟨h1, h2⟩
              rw [hp_last] at h1
              rw [h1, h2] at hr
              exact hLast hr
          | cast r' =>
              have hp_last : p (Fin.last m) = k := by simp [p]
              have hp_init : (fun q : Fin m => p q.castSucc) = p' := by
                ext q
                simp [p, Fin.snoc_castSucc]
              rcases pathNodesPos_step_prefix i j p r' with ⟨h1, h2⟩
              rw [hp_last, hp_init] at h1 h2
              rw [h1, h2] at hr
              exact ⟨r', hr⟩

/--
**CH02-P13 (Proposition 2.6(i))**: For any `n ≥ 1` and matrices `M^{(1)}, ..., M^{(n)}`,
the `(i -> j)` entry of `M^{(n)} * ... * M^{(1)}` vanishes iff every interior index
sequence `(k_1, ..., k_{n-1})` contains at least one zero factor `[M^{(r)}]_{k_{r-1} -> k_r} = 0`
(with `k_0 = i`, `k_n = j`).
-/
theorem matrixNonemptyProd_entry_eq_zero_iff {I : Type u} [Fintype I]
    {n : ℕ} (hn : 0 < n) (Ms : Fin n → GaugeMatrix I) (i j : I) :
    matrixEntry (matrixNonemptyProd hn Ms) i j = 0 ↔
      ∀ p : InteriorPath I n, HasZeroFactorPath Ms hn i j p := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m =>
      simpa [matrixNonemptyProd, HasZeroFactorPath, pathStepEntry, pathNodes] using
        matrixPosProd_entry_eq_zero_iff Ms i j

/--
**CH02-P13 (n = 1 degeneration)**: When `n = 1`, the interior index sequence is empty,
so the path-zero-factor condition degenerates to `[M^{(1)}]_{i -> j} = 0`.
-/
theorem matrixNonemptyProd_one_entry_eq_zero_iff {I : Type u} [Fintype I]
    (Ms : Fin 1 → GaugeMatrix I) (i j : I) :
    (∀ p : InteriorPath I 1, HasZeroFactorPath Ms Nat.one_pos i j p) ↔
      matrixEntry (Ms 0) i j = 0 := by
  rw [← matrixNonemptyProd_entry_eq_zero_iff Nat.one_pos Ms i j, matrixNonemptyProd_one]

/--
**CH02-P14 (Proposition 2.6(ii))**: For any `n ≥ 1` and matrices `M^{(1)}, ..., M^{(n)}`,
the `(i -> j)` entry of `M^{(n)} * ... * M^{(1)}` is strictly positive iff there exists
at least one interior index sequence `(k_1, ..., k_{n-1})` along which every factor
`[M^{(r)}]_{k_{r-1} -> k_r}` is strictly positive.
-/
theorem matrixNonemptyProd_entry_pos_iff {I : Type u} [Fintype I]
    {n : ℕ} (hn : 0 < n) (Ms : Fin n → GaugeMatrix I) (i j : I) :
    0 < matrixEntry (matrixNonemptyProd hn Ms) i j ↔
      ∃ p : InteriorPath I n, IsPositivePath Ms hn i j p := by
  rw [pos_iff_ne_zero, ne_eq, matrixNonemptyProd_entry_eq_zero_iff hn Ms i j]
  push Not
  simp only [← not_isPositivePath_iff_hasZeroFactorPath, not_not]

/--
**CH02-P14 (n = 1 degeneration)**: When `n = 1`, existence of an all-positive path
degenerates to `0 < [M^{(1)}]_{i -> j}`.
-/
theorem matrixNonemptyProd_one_entry_pos_iff {I : Type u} [Fintype I]
    (Ms : Fin 1 → GaugeMatrix I) (i j : I) :
    (∃ p : InteriorPath I 1, IsPositivePath Ms Nat.one_pos i j p) ↔
      0 < matrixEntry (Ms 0) i j := by
  rw [← matrixNonemptyProd_entry_pos_iff Nat.one_pos Ms i j, matrixNonemptyProd_one]

end PathCriteria

end LCH02
