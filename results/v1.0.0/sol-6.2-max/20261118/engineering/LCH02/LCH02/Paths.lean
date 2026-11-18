import LCH02.MatrixBounds
import Mathlib.Data.Fin.Tuple.Basic

namespace LCH02

open scoped BigOperators ENNReal

variable {I : Type}

/-- `n` counts the interior vertices, so there are `n + 1` steps. -/
abbrev IndexPath (I : Type) (n : ℕ) := Fin n → I

def pathVertices {n : ℕ} (i j : I) (p : IndexPath I n) : Fin (n + 2) → I :=
  Fin.cons i (Fin.snoc p j)

@[simp] theorem pathVertices_zero {n : ℕ} (i j : I) (p : IndexPath I n) :
    pathVertices i j p 0 = i := by
  simp [pathVertices]

@[simp] theorem pathVertices_last {n : ℕ} (i j : I) (p : IndexPath I n) :
    pathVertices i j p (Fin.last (n + 1)) = j := by
  rw [← Fin.succ_last]
  simp [pathVertices]

@[simp] theorem pathVertices_interior {n : ℕ} (i j : I)
    (p : IndexPath I n) (k : Fin n) :
    pathVertices i j p k.castSucc.succ = p k := by
  simp [pathVertices]

def pathEntry {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I)
    (p : IndexPath I n) (m : Fin (n + 1)) : ℝ≥0∞ :=
  M m (pathVertices i j p m.succ) (pathVertices i j p m.castSucc)

def PositivePath {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I)
    (p : IndexPath I n) : Prop :=
  ∀ m, 0 < pathEntry M i j p m

theorem empty_path_unique (p : IndexPath I 0) : p = Fin.elim0 :=
  funext fun k => k.elim0

theorem pathEntry_one (M : Fin 1 → BoundMatrix I) (i j : I)
    (p : IndexPath I 0) (m : Fin 1) :
    pathEntry M i j p m = M 0 j i := by
  have hm : m = 0 := Subsingleton.elim _ _
  subst m
  change M 0 (pathVertices i j p (Fin.last 1)) (pathVertices i j p 0) = M 0 j i
  rw [pathVertices_last, pathVertices_zero]

private theorem positivePath_cons {n : ℕ} (M : Fin (n + 2) → BoundMatrix I)
    (i k j : I) (p : IndexPath I n) :
    PositivePath M i j (Fin.cons k p) ↔
      0 < M 0 k i ∧ PositivePath (fun m => M m.succ) k j p := by
  rw [PositivePath, Fin.forall_fin_succ]
  simp only [PositivePath, pathEntry, pathVertices, ← Fin.cons_snoc_eq_snoc_cons,
    Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]

variable [Fintype I]

theorem matrixProduct_pos_iff {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    0 < matrixProduct (List.ofFn M) j i ↔ ∃ p : IndexPath I n, PositivePath M i j p := by
  induction n generalizing i with
  | zero =>
    rw [List.ofFn_succ, List.ofFn_zero, matrixProduct_singleton]
    simp only [PositivePath, pathEntry_one]
    exact ⟨fun h => ⟨Fin.elim0, fun _ => h⟩, fun ⟨_, h⟩ => h 0⟩
  | succ n ih =>
    rw [List.ofFn_succ, matrixProduct_cons, matrix_mul_entry,
      Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _), Fin.exists_fin_succ_pi]
    simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff, positivePath_cons, ih]
    constructor
    · rintro ⟨k, ⟨p, hp⟩, hk⟩
      exact ⟨k, p, hk, hp⟩
    · rintro ⟨k, p, hk, hp⟩
      exact ⟨k, ⟨p, hp⟩, hk⟩

theorem matrixProduct_zero_iff {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    matrixProduct (List.ofFn M) j i = 0 ↔
      ∀ p : IndexPath I n, ∃ m : Fin (n + 1), pathEntry M i j p m = 0 := by
  classical
  constructor
  · intro hz p
    by_contra hzero
    have hp : PositivePath M i j p :=
      fun m => pos_of_ne_zero (fun hm => hzero ⟨m, hm⟩)
    exact ((matrixProduct_pos_iff M i j).2 ⟨p, hp⟩).ne' hz
  · intro hpaths
    by_contra hprod
    obtain ⟨p, hp⟩ := (matrixProduct_pos_iff M i j).1 (pos_of_ne_zero hprod)
    obtain ⟨m, hm⟩ := hpaths p
    exact (hp m).ne' hm

end LCH02
