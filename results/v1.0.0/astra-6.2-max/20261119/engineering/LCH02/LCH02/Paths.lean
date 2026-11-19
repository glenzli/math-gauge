import LCH02.Matrices

namespace LCH02

open scoped Classical

variable {I : Type*}

/-- For n+1 edges, the n intermediate vertices are free. The endpoints are separate. -/
abbrev IndexPath (I : Type*) (n : ℕ) := Fin n → I

theorem empty_path_unique (p : IndexPath I 0) : p = Fin.elim0 := Subsingleton.elim _ _

def pathEntry {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) (p : IndexPath I n)
    (m : Fin (n + 1)) : ENNReal :=
  entry (A m) (Fin.cons (α := fun _ => I) i p m) (Fin.snoc (α := fun _ => I) p j m)

def PositivePath {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) (p : IndexPath I n) : Prop :=
  ∀ m, 0 < pathEntry A i j p m

@[simp] theorem pathEntry_one (A : Fin 1 → Bound I) (i j : I) (p : IndexPath I 0)
    (m : Fin 1) : pathEntry A i j p m = entry (A 0) i j := by
  obtain rfl := Subsingleton.elim m 0
  rfl

private theorem positive_cons {n : ℕ} (A : Fin (n + 2) → Bound I) (i j k : I)
    (p : IndexPath I n) :
    PositivePath A i j (Fin.cons k p) ↔
      0 < entry (A 0) i k ∧ PositivePath (Fin.tail A) k j p := by
  unfold PositivePath
  rw [Fin.forall_fin_succ]
  simp only [pathEntry, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ, Fin.tail]

variable [Fintype I]

theorem product_pos_iff {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) :
    0 < entry (orderedProd A) i j ↔ ∃ p : IndexPath I n, PositivePath A i j p := by
  induction n generalizing i with
  | zero => simp [PositivePath, IndexPath]
  | succ n ih =>
    rw [orderedProd_succ, entry_mul, Finset.sum_pos_iff, Fin.exists_fin_succ_pi]
    simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff, ih, positive_cons]
    constructor
    · rintro ⟨k, ⟨p, hp⟩, hk⟩
      exact ⟨k, p, hk, hp⟩
    · rintro ⟨k, p, hk, hp⟩
      exact ⟨k, ⟨p, hp⟩, hk⟩

theorem product_zero_iff {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) :
    entry (orderedProd A) i j = 0 ↔
      ∀ p : IndexPath I n, ∃ m, pathEntry A i j p m = 0 := by
  simpa only [PositivePath, not_exists, not_forall, not_lt, nonpos_iff_eq_zero] using
    not_congr (product_pos_iff A i j)

end LCH02
