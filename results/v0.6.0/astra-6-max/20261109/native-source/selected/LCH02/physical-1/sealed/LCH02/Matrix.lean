import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §2.1, https://glenzli.com/books/oet/, CC BY 4.0.
This file is a new formalization of the selected obligations.
-/

open scoped BigOperators Classical Matrix

namespace LCH02

abbrev Mat (I : Type) := Matrix I I ENNReal

/-- The textbook entry i → j is row j, column i. -/
def entry {I : Type} (M : Mat I) (i j : I) : ENNReal := M j i

section Matrices
variable {I : Type} [Fintype I]

theorem entry_mul (A B : Mat I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k := rfl

omit [Fintype I] in
theorem entry_one (i j : I) :
    entry (1 : Mat I) i j = if j = i then 1 else 0 := by
  simp [entry, Matrix.one_apply]

/-- Matrices are listed in execution order: [M₁,...,Mₙ]. -/
noncomputable def matrixProduct : List (Mat I) → Mat I
  | [] => 1
  | M :: Ms => matrixProduct Ms * M

@[simp] theorem matrixProduct_nil : matrixProduct ([] : List (Mat I)) = 1 := rfl

@[simp] theorem matrixProduct_cons (M : Mat I) (Ms : List (Mat I)) :
    matrixProduct (M :: Ms) = matrixProduct Ms * M := rfl

@[simp] theorem matrixProduct_singleton (M : Mat I) :
    matrixProduct [M] = M := by simp [matrixProduct]

theorem matrixProduct_eq_reverse_prod (Ms : List (Mat I)) :
    matrixProduct Ms = Ms.reverse.prod := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih => simp [matrixProduct, ih, List.reverse_cons, List.prod_append]

/-- Multiplication by a matrix preserves pointwise inequalities, including ∞. -/
theorem mulVec_mono (M : Mat I) {v w : I → ENNReal} (h : ∀ i, v i ≤ w i) :
    ∀ j, (M *ᵥ v) j ≤ (M *ᵥ w) j := by
  intro j
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_right (h i) (M j i))

end Matrices

end LCH02
