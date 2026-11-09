import LCH02.Matrix

open scoped BigOperators Classical Matrix

namespace LCH02

/-- The n internal vertices of a path of n+1 steps; endpoints are separate. -/
abbrev IndexPath (I : Type) (n : ℕ) := Fin n → I

variable {I : Type} [Fintype I]

/-- In execution order, the first edge goes from i to p(0). -/
def AllPositive : (M : Mat I) → (Ms : List (Mat I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => 0 < M j i
  | M, N :: Ns, i, j, p =>
      0 < M (p 0) i ∧ AllPositive N Ns (p 0) j (Fin.tail p)

/-- At least one of the edges of this particular path has zero weight. -/
def HasZero : (M : Mat I) → (Ms : List (Mat I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => M j i = 0
  | M, N :: Ns, i, j, p =>
      M (p 0) i = 0 ∨ HasZero N Ns (p 0) j (Fin.tail p)

omit [Fintype I] in
theorem hasZero_iff_not_allPositive (M : Mat I) (Ms : List (Mat I))
    (i j : I) (p : IndexPath I Ms.length) :
    HasZero M Ms i j p ↔ ¬ AllPositive M Ms i j p := by
  induction Ms generalizing M i with
  | nil => simp [HasZero, AllPositive]
  | cons N Ns ih =>
      simp only [HasZero, AllPositive, ih, not_and_or, not_lt, nonpos_iff_eq_zero]

/-- Every positive-length product, with no finiteness restriction on entries. -/
theorem matrixProduct_pos_iff (M : Mat I) (Ms : List (Mat I)) (i j : I) :
    0 < matrixProduct (M :: Ms) j i ↔
      ∃ p : IndexPath I Ms.length, AllPositive M Ms i j p := by
  induction Ms generalizing M i with
  | nil => simp [AllPositive, IndexPath]
  | cons N Ns ih =>
      rw [matrixProduct_cons, Matrix.mul_apply, Finset.sum_pos_iff]
      simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff]
      constructor
      · rintro ⟨k, hk, hM⟩
        obtain ⟨p, hp⟩ := (ih N k).mp hk
        exact ⟨Fin.cons k p, by simpa [AllPositive] using And.intro hM hp⟩
      · rintro ⟨p, hp⟩
        exact ⟨p 0, (ih N (p 0)).mpr ⟨Fin.tail p, hp.2⟩, hp.1⟩

/-- Zero is equivalent to a zero factor on every internal-index sequence. -/
theorem matrixProduct_zero_iff (M : Mat I) (Ms : List (Mat I)) (i j : I) :
    matrixProduct (M :: Ms) j i = 0 ↔
      ∀ p : IndexPath I Ms.length, HasZero M Ms i j p := by
  simp only [hasZero_iff_not_allPositive, ← not_exists,
    ← matrixProduct_pos_iff, not_lt, nonpos_iff_eq_zero]

omit [Fintype I] in
/-- For one step there is exactly one empty internal-index sequence. -/
theorem one_step_path (M : Mat I) (i j : I) :
    (∃! _p : IndexPath I 0, True) ∧
    (∀ p : IndexPath I 0, AllPositive M [] i j p ↔ 0 < M j i) ∧
    (∀ p : IndexPath I 0, HasZero M [] i j p ↔ M j i = 0) := by
  refine ⟨⟨Fin.elim0, trivial, fun p _ => Subsingleton.elim _ _⟩, ?_, ?_⟩
  · intro p; rfl
  · intro p; rfl

end LCH02
