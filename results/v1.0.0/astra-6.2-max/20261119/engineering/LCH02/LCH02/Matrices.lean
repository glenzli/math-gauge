import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic

namespace LCH02

open scoped BigOperators Classical Matrix

abbrev Bound (I : Type*) := Matrix I I ENNReal

/-- The channel i → j occupies row j, column i. -/
abbrev entry {I : Type*} (A : Bound I) (i j : I) : ENNReal := A j i

variable {I : Type*}

theorem row_sum [Fintype I] (A : Bound I) (v : I → ENNReal) (j : I) :
    (A *ᵥ v) j = ∑ i, entry A i j * v i := rfl

theorem entry_mul [Fintype I] (B A : Bound I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

noncomputable abbrev unitMatrix (I : Type*) : Bound I := 1

theorem entry_one (i j : I) :
    entry (unitMatrix I) i j = if j = i then 1 else 0 :=
  Matrix.one_apply

/-- The family is indexed in time order, with the earliest factor on the right. -/
def orderedProd {M : Type*} [Monoid M] : {n : ℕ} → (Fin n → M) → M
  | 0, _ => 1
  | _ + 1, f => orderedProd (Fin.tail f) * f 0

variable {M : Type*} [Monoid M]

@[simp] theorem orderedProd_empty (f : Fin 0 → M) : orderedProd f = 1 := rfl

theorem orderedProd_succ {n : ℕ} (f : Fin (n + 1) → M) :
    orderedProd f = orderedProd (Fin.tail f) * f 0 := rfl

@[simp] theorem orderedProd_one (f : Fin 1 → M) : orderedProd f = f 0 := one_mul _

theorem orderedProd_eq_reverse_prod {n : ℕ} (f : Fin n → M) :
    orderedProd f = (List.ofFn f).reverse.prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orderedProd_succ, List.ofFn_succ, List.reverse_cons, List.prod_append,
      List.prod_singleton, ih]
    rfl

theorem mulVec_mono [Fintype I] (A : Bound I) {v w : I → ENNReal} (h : v ≤ w) :
    A *ᵥ v ≤ A *ᵥ w :=
  fun _ => Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) _

end LCH02
