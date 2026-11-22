/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace LCH02

universe u

/--
Extended nonnegative matrix indexed by a gauge component index set `I`.
Following §2.1 of OET Vol. I, rows index output components `j` and columns index
input components `i`, so the `(j, i)` matrix entry represents `M_{i → j}`.
-/
abbrev GaugeMatrix (I : Type u) := Matrix I I ENNReal

/--
The entry `M_{i → j}` from input component `i` to output component `j`,
stored at row `j` and column `i`: `(M)_{j, i} = M_{i → j}`.
-/
def matrixEntry {I : Type u} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

/-- Construct a `GaugeMatrix` from its `i → j` entry function. -/
def gaugeMatrixOfEntries {I : Type u} (f : I → I → ENNReal) : GaugeMatrix I :=
  Matrix.of fun j i => f i j

@[simp] theorem matrixEntry_ofEntries {I : Type u} (f : I → I → ENNReal) (i j : I) :
    matrixEntry (gaugeMatrixOfEntries f) i j = f i j :=
  rfl

@[ext] theorem gaugeMatrix_ext {I : Type u} {A B : GaugeMatrix I}
    (h : ∀ i j : I, matrixEntry A i j = matrixEntry B i j) : A = B := by
  ext j i
  exact h i j

/--
Multiplication of extended nonnegative gauge matrices.
With rows as outputs and columns as inputs, `(A · B)_{i → j} = ∑ k, A_{k → j} * B_{i → k}`.
-/
noncomputable def gaugeMatrixMul {I : Type u} [Fintype I] (A B : GaugeMatrix I) : GaugeMatrix I :=
  A * B

@[simp] theorem gaugeMatrixMul_eq_mul {I : Type u} [Fintype I] (A B : GaugeMatrix I) :
    gaugeMatrixMul A B = A * B :=
  rfl

theorem matrixEntry_gaugeMatrixMul {I : Type u} [Fintype I]
    (A B : GaugeMatrix I) (i j : I) :
    matrixEntry (gaugeMatrixMul A B) i j =
      ∑ k : I, matrixEntry A k j * matrixEntry B i k := by
  simp [matrixEntry, gaugeMatrixMul, Matrix.mul_apply]

theorem gaugeMatrixMul_assoc {I : Type u} [Fintype I]
    (A B C : GaugeMatrix I) :
    gaugeMatrixMul (gaugeMatrixMul A B) C = gaugeMatrixMul A (gaugeMatrixMul B C) := by
  simp [gaugeMatrixMul, Matrix.mul_assoc]

/-- The identity gauge matrix `I`. -/
def idMatrix {I : Type u} [DecidableEq I] : GaugeMatrix I :=
  (1 : Matrix I I ENNReal)

@[simp] theorem idMatrix_eq_one {I : Type u} [DecidableEq I] :
    (idMatrix : GaugeMatrix I) = 1 :=
  rfl

@[simp] theorem matrixEntry_idMatrix {I : Type u} [DecidableEq I] (i j : I) :
    matrixEntry (idMatrix : GaugeMatrix I) i j = if i = j then 1 else 0 := by
  simp [matrixEntry, idMatrix, Matrix.one_apply, eq_comm]

@[simp] theorem gaugeMatrixMul_idMatrix {I : Type u} [Fintype I] [DecidableEq I]
    (A : GaugeMatrix I) :
    gaugeMatrixMul A idMatrix = A := by
  simp [gaugeMatrixMul, idMatrix]

@[simp] theorem idMatrix_gaugeMatrixMul {I : Type u} [Fintype I] [DecidableEq I]
    (A : GaugeMatrix I) :
    gaugeMatrixMul idMatrix A = A := by
  simp [gaugeMatrixMul, idMatrix]

/--
Ordered nonempty product of `n + 1` matrices `M^(1), ..., M^(n+1)` in composition order:
`M^(n+1) · M^(n) · ... · M^(1)`.
Here `M 0` is the first (innermost) matrix `M^(1)` and `M (Fin.last n)` is the last
(outermost) matrix `M^(n+1)`.
-/
noncomputable def orderedMatrixProdNonempty {I : Type u} [Fintype I] :
    {n : Nat} → (Fin (n + 1) → GaugeMatrix I) → GaugeMatrix I
  | 0, M => M 0
  | _ + 1, M =>
      gaugeMatrixMul (M (Fin.last _)) (orderedMatrixProdNonempty (fun m => M m.castSucc))

@[simp] theorem orderedMatrixProdNonempty_zero {I : Type u} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) :
    orderedMatrixProdNonempty M = M 0 :=
  rfl

theorem orderedMatrixProdNonempty_succ {I : Type u} [Fintype I] {n : Nat}
    (M : Fin (n + 2) → GaugeMatrix I) :
    orderedMatrixProdNonempty M =
      gaugeMatrixMul (M (Fin.last (n + 1))) (orderedMatrixProdNonempty (fun m => M m.castSucc)) :=
  rfl

theorem orderedMatrixProdNonempty_succ_left {I : Type u} [Fintype I] {n : Nat}
    (M : Fin (n + 2) → GaugeMatrix I) :
    orderedMatrixProdNonempty M =
      gaugeMatrixMul (orderedMatrixProdNonempty (fun m => M m.succ)) (M 0) := by
  induction n with
  | zero =>
      simp [orderedMatrixProdNonempty, Fin.last]
  | succ k ih =>
      rw [orderedMatrixProdNonempty_succ]
      have h_init :
          orderedMatrixProdNonempty (fun m : Fin (k + 2) => M m.castSucc) =
            gaugeMatrixMul
              (orderedMatrixProdNonempty (fun m : Fin (k + 1) => M m.succ.castSucc))
              (M 0) :=
        ih (fun m => M m.castSucc)
      rw [h_init, ← gaugeMatrixMul_assoc]
      rfl

/--
Ordered finite product of `n` matrices in composition order `M^(n) · ... · M^(1)`,
with the empty product (`n = 0`) defined as the identity matrix `idMatrix`.
-/
noncomputable def orderedMatrixProd {I : Type u} [Fintype I] [DecidableEq I] :
    {n : Nat} → (Fin n → GaugeMatrix I) → GaugeMatrix I
  | 0, _ => idMatrix
  | _ + 1, M => orderedMatrixProdNonempty M

@[simp] theorem orderedMatrixProd_zero {I : Type u} [Fintype I] [DecidableEq I]
    (M : Fin 0 → GaugeMatrix I) :
    orderedMatrixProd M = idMatrix :=
  rfl

@[simp] theorem orderedMatrixProd_one {I : Type u} [Fintype I] [DecidableEq I]
    (M : Fin 1 → GaugeMatrix I) :
    orderedMatrixProd M = M 0 :=
  rfl

theorem orderedMatrixProd_eq_nonempty {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (M : Fin (n + 1) → GaugeMatrix I) :
    orderedMatrixProd M = orderedMatrixProdNonempty M :=
  rfl

theorem orderedMatrixProd_succ {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (M : Fin (n + 1) → GaugeMatrix I) :
    orderedMatrixProd M =
      gaugeMatrixMul (M (Fin.last n)) (orderedMatrixProd (fun m => M m.castSucc)) := by
  cases n with
  | zero =>
      simp [orderedMatrixProd, orderedMatrixProdNonempty]
  | succ k =>
      rfl

/--
List-based composition-order product for chronological lists `[M^(1), ..., M^(n)]`,
evaluating to `M^(n) · ... · M^(1)` and `idMatrix` on the empty list.
-/
noncomputable def listMatrixProd {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List (GaugeMatrix I)) : GaugeMatrix I :=
  Ms.reverse.prod

@[simp] theorem listMatrixProd_nil {I : Type u} [Fintype I] [DecidableEq I] :
    listMatrixProd ([] : List (GaugeMatrix I)) = idMatrix :=
  rfl

@[simp] theorem listMatrixProd_singleton {I : Type u} [Fintype I] [DecidableEq I]
    (M : GaugeMatrix I) :
    listMatrixProd [M] = M := by
  simp [listMatrixProd]

theorem listMatrixProd_concat {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List (GaugeMatrix I)) (M : GaugeMatrix I) :
    listMatrixProd (Ms ++ [M]) = gaugeMatrixMul M (listMatrixProd Ms) := by
  simp [listMatrixProd, gaugeMatrixMul]

theorem orderedMatrixProd_eq_listMatrixProd {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (M : Fin n → GaugeMatrix I) :
    orderedMatrixProd M = listMatrixProd (List.ofFn M) := by
  induction n with
  | zero =>
      simp [orderedMatrixProd, listMatrixProd]
  | succ k ih =>
      rw [orderedMatrixProd_succ, List.ofFn_succ', List.concat_eq_append, listMatrixProd_concat]
      rw [ih (fun m => M m.castSucc)]

end LCH02
