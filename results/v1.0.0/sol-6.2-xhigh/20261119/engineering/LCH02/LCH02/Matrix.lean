import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic

namespace LCH02

open scoped BigOperators Classical

abbrev Coefficients (I : Type) := Matrix I I ENNReal

/-- The input index is the column and the output index is the row. -/
def entry {I : Type} (A : Coefficients I) (i j : I) : ENNReal :=
  A j i

theorem entry_mul {I : Type} [Fintype I] (B A : Coefficients I) (i j : I) :
    entry (B * A) i j = ∑ k : I, entry B k j * entry A i k :=
  Matrix.mul_apply

noncomputable def matrixUnit {I : Type} : Coefficients I := 1

theorem entry_unit {I : Type} (i j : I) :
    entry matrixUnit i j = if i = j then 1 else 0 := by
  simp [entry, matrixUnit, Matrix.one_apply, eq_comm]

/-- The list runs from the first applied matrix to the last. -/
noncomputable def matrixProduct {I : Type} [Fintype I]
    (matrices : List (Coefficients I)) : Coefficients I :=
  matrices.reverse.prod

@[simp] theorem matrixProduct_nil {I : Type} [Fintype I] :
    matrixProduct ([] : List (Coefficients I)) = matrixUnit := rfl

theorem matrixProduct_cons {I : Type} [Fintype I]
    (A : Coefficients I) (rest : List (Coefficients I)) :
    matrixProduct (A :: rest) = matrixProduct rest * A := by
  simp [matrixProduct, List.reverse_cons, List.prod_append]

@[simp] theorem matrixProduct_single {I : Type} [Fintype I] (A : Coefficients I) :
    matrixProduct [A] = A := by
  simp [matrixProduct]

/-- A path with `n` intermediate layers chooses one index at each layer. -/
abbrev IndexPath (I : Type) (n : ℕ) := Fin n → I

/-- The endpoints `i` and `j` are external to the intermediate sequence. -/
def pathFactors {I : Type} (A : Coefficients I) :
    (rest : List (Coefficients I)) → I → I → IndexPath I rest.length → List ENNReal
  | [], i, j, _ => [entry A i j]
  | B :: rest, i, j, p =>
      entry A i (p 0) :: pathFactors B rest (p 0) j (Fin.tail p)

theorem pathFactors_length {I : Type} (A : Coefficients I)
    (rest : List (Coefficients I)) (i j : I) (p : IndexPath I rest.length) :
    (pathFactors A rest i j p).length = rest.length + 1 := by
  induction rest generalizing A i with
  | nil => rfl
  | cons B rest ih => simp [pathFactors, ih]

def PositivePath {I : Type} (A : Coefficients I) (rest : List (Coefficients I))
    (i j : I) (p : IndexPath I rest.length) : Prop :=
  ∀ a ∈ pathFactors A rest i j p, 0 < a

def HasZeroFactor {I : Type} (A : Coefficients I) (rest : List (Coefficients I))
    (i j : I) (p : IndexPath I rest.length) : Prop :=
  0 ∈ pathFactors A rest i j p

abbrev singleStepPath_unique {I : Type} : Unique (IndexPath I 0) :=
  ⟨⟨Fin.elim0⟩, fun _ => funext (fun k => Fin.elim0 k)⟩

theorem matrixProduct_pos_iff {I : Type} [Fintype I]
    (A : Coefficients I) (rest : List (Coefficients I)) (i j : I) :
    0 < entry (matrixProduct (A :: rest)) i j ↔
      ∃ p : IndexPath I rest.length, PositivePath A rest i j p := by
  induction rest generalizing A i with
  | nil =>
      simp only [matrixProduct_single, PositivePath, pathFactors, List.mem_singleton]
      constructor
      · intro h
        exact ⟨singleStepPath_unique.default, fun a ha => ha ▸ h⟩
      · rintro ⟨_, h⟩
        exact h _ rfl
  | cons B rest ih =>
      rw [matrixProduct_cons, entry_mul, Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _)]
      simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff, ih B]
      constructor
      · rintro ⟨k, ⟨p, hp⟩, hfirst⟩
        refine ⟨Fin.cons k p, ?_⟩
        simpa [PositivePath, pathFactors, List.forall_mem_cons] using And.intro hfirst hp
      · rintro ⟨p, hp⟩
        have h : 0 < entry A i (p 0) ∧
            PositivePath B rest (p 0) j (Fin.tail p) := by
          simpa [PositivePath, pathFactors, List.forall_mem_cons] using hp
        exact ⟨p 0, ⟨Fin.tail p, h.2⟩, h.1⟩

theorem matrixProduct_zero_iff {I : Type} [Fintype I]
    (A : Coefficients I) (rest : List (Coefficients I)) (i j : I) :
    entry (matrixProduct (A :: rest)) i j = 0 ↔
      ∀ p : IndexPath I rest.length, HasZeroFactor A rest i j p := by
  have hfactor (p : IndexPath I rest.length) :
      ¬ PositivePath A rest i j p ↔ HasZeroFactor A rest i j p := by
    simp [PositivePath, HasZeroFactor, pos_iff_ne_zero]
  rw [← not_ne_iff, ← pos_iff_ne_zero, matrixProduct_pos_iff, not_exists]
  exact forall_congr' hfactor

end LCH02
