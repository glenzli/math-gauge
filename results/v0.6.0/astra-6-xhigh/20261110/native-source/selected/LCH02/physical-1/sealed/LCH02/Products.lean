import LCH02.Bounds

noncomputable section

namespace LCH02

open scoped BigOperators

/-- Temporal order: step 0 acts first; the newest factor is on the left. -/
def orderedProduct {α : Type} [Monoid α] (f : ℕ → α) : ℕ → α
  | 0 => 1
  | n + 1 => f n * orderedProduct f n

theorem orderedProduct_eq_reverse_prod {α : Type} [Monoid α] (f : ℕ → α) (n : ℕ) :
    orderedProduct f n = ((List.range n).reverse.map f).prod := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orderedProduct, List.range_succ, List.reverse_append, ih]

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem entry_one (i j : I) :
    entry (1 : Mat I) i j = if i = j then 1 else 0 := by
  simp [entry, Matrix.one_apply, eq_comm]

def matrixProduct (M : ℕ → Mat I) (n : ℕ) : Mat I := orderedProduct M n

@[simp] theorem matrixProduct_zero (M : ℕ → Mat I) : matrixProduct M 0 = 1 := rfl

@[simp] theorem matrixProduct_succ (M : ℕ → Mat I) (n : ℕ) :
    matrixProduct M (n + 1) = M n * matrixProduct M n := rfl

@[simp] theorem matrixProduct_one (M : ℕ → Mat I) : matrixProduct M 1 = M 0 := by
  simp [matrixProduct, orderedProduct]

/-- A length-indexed path with fixed initial and final vertices. -/
inductive IndexPath (I : Type) : ℕ → I → I → Type
  | nil (i : I) : IndexPath I 0 i i
  | snoc {n : ℕ} {i k : I} (p : IndexPath I n i k) (j : I) :
      IndexPath I (n + 1) i j

namespace IndexPath

omit [Fintype I] [DecidableEq I]

def AllPositive (M : ℕ → Mat I) : {n : ℕ} → {i j : I} → IndexPath I n i j → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .snoc (n := n) (k := k) p j =>
      AllPositive M p ∧ 0 < entry (M n) k j

def HasZero (M : ℕ → Mat I) : {n : ℕ} → {i j : I} → IndexPath I n i j → Prop
  | _, _, _, .nil _ => False
  | _, _, _, .snoc (n := n) (k := k) p j =>
      HasZero M p ∨ entry (M n) k j = 0

/-- Vertices in temporal order, including both endpoints. -/
def vertices : {n : ℕ} → {i j : I} → IndexPath I n i j → List I
  | _, _, _, .nil i => [i]
  | _, _, _, .snoc p j => vertices p ++ [j]

theorem vertices_length {n : ℕ} {i j : I} (p : IndexPath I n i j) :
    p.vertices.length = n + 1 := by
  induction p with
  | nil => rfl
  | snoc p j ih => simp [vertices, ih]

/-- The endpoints of edge m, where 0 ≤ m < n. -/
def edge : {n : ℕ} → {i j : I} → IndexPath I n i j → Fin n → I × I
  | _, _, _, .nil _, m => Fin.elim0 m
  | _, _, _, .snoc (k := k) p j, m => Fin.lastCases (k, j) p.edge m

theorem allPositive_iff_edges {n : ℕ} {i j : I} (M : ℕ → Mat I)
    (p : IndexPath I n i j) :
    p.AllPositive M ↔ ∀ m : Fin n, 0 < entry (M m) (p.edge m).1 (p.edge m).2 := by
  induction p with
  | nil => simp [AllPositive]
  | snoc p j ih => simp [AllPositive, edge, Fin.forall_fin_succ', ih]

theorem not_allPositive_iff {n : ℕ} {i j : I} (M : ℕ → Mat I)
    (p : IndexPath I n i j) : ¬ p.AllPositive M ↔ p.HasZero M := by
  induction p with
  | nil => simp [AllPositive, HasZero]
  | snoc p j ih =>
      change (¬ (p.AllPositive M ∧ 0 < _)) ↔ p.HasZero M ∨ _ = 0
      rw [not_and_or, ih]
      simp

theorem hasZero_iff_edges {n : ℕ} {i j : I} (M : ℕ → Mat I)
    (p : IndexPath I n i j) :
    p.HasZero M ↔ ∃ m : Fin n, entry (M m) (p.edge m).1 (p.edge m).2 = 0 := by
  rw [← not_allPositive_iff, allPositive_iff_edges]
  simp

theorem one_step_unique {i j : I} (p : IndexPath I 1 i j) :
    p = IndexPath.snoc (IndexPath.nil i) j := by
  cases p with
  | snoc p j => cases p; rfl

@[simp] theorem single_positive (M : ℕ → Mat I) (i j : I) :
    (IndexPath.snoc (IndexPath.nil i) j).AllPositive M ↔ 0 < entry (M 0) i j := by
  simp [AllPositive]

@[simp] theorem single_zero (M : ℕ → Mat I) (i j : I) :
    (IndexPath.snoc (IndexPath.nil i) j).HasZero M ↔ entry (M 0) i j = 0 := by
  simp [HasZero]

end IndexPath

omit [DecidableEq I] in
theorem mul_entry_pos (B A : Mat I) (i j : I) :
    0 < entry (B * A) i j ↔ ∃ k, 0 < entry A i k ∧ 0 < entry B k j := by
  simp only [entry_mul, Finset.sum_pos_iff, Finset.mem_univ, true_and,
    ENNReal.mul_pos_iff]
  exact exists_congr fun _ => and_comm

theorem matrixProduct_pos_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    0 < entry (matrixProduct M n) i j ↔
      ∃ p : IndexPath I n i j, p.AllPositive M := by
  induction n generalizing i j with
  | zero =>
      constructor
      · intro h
        have hij : i = j := by
          by_contra hne
          simp [entry, Ne.symm hne] at h
        subst j
        exact ⟨.nil i, trivial⟩
      · rintro ⟨p, _⟩
        cases p
        simp [entry]
  | succ n ih =>
      rw [matrixProduct_succ, mul_entry_pos]
      constructor
      · rintro ⟨k, hk, hkj⟩
        obtain ⟨p, hp⟩ := (ih i k).mp hk
        exact ⟨.snoc p j, hp, hkj⟩
      · rintro ⟨p, hp⟩
        cases p with
        | @snoc n i k p j => exact ⟨k, (ih i k).mpr ⟨p, hp.1⟩, hp.2⟩

theorem matrixProduct_zero_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    entry (matrixProduct M n) i j = 0 ↔
      ∀ p : IndexPath I n i j, p.HasZero M := by
  have hzero : entry (matrixProduct M n) i j = 0 ↔
      ¬ 0 < entry (matrixProduct M n) i j := by simp
  rw [hzero, matrixProduct_pos_iff, not_exists]
  exact forall_congr' fun p => p.not_allPositive_iff M

/-- The n = 1 boundary, with no intermediate vertex to choose. -/
theorem one_step_criteria (M : ℕ → Mat I) (i j : I) :
    (0 < entry (M 0) i j ↔ ∃ p : IndexPath I 1 i j, p.AllPositive M) ∧
    (entry (M 0) i j = 0 ↔ ∀ p : IndexPath I 1 i j, p.HasZero M) := by
  constructor
  · simpa using matrixProduct_pos_iff M 1 i j
  · simpa using matrixProduct_zero_iff M 1 i j

end LCH02
