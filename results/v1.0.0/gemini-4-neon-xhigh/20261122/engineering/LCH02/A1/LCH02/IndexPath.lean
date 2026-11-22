/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import LCH02.GaugeMatrix

namespace LCH02

universe u

/--
A finite index path of length `n` from input component `i` to output component `j`:
`nodes 0 = k_0 = i`, intermediate indices `k_1, ..., k_{n-1}`, and `nodes (Fin.last n) = k_n = j`.
-/
@[ext]
structure IndexPath (I : Type u) (n : Nat) (i j : I) where
  nodes : Fin (n + 1) → I
  start_eq : nodes 0 = i
  end_eq : nodes (Fin.last n) = j

/--
The single-step matrix entry `[M^(m)]_{k_{m-1} → k_m}` along step `s` of a path `p`.
-/
def IndexPath.stepEntry {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) (s : Fin n) : ENNReal :=
  matrixEntry (M s) (p.nodes s.castSucc) (p.nodes s.succ)

/--
Construct a length-`(m + 1)` index path from endpoints `i, j` and an intermediate
index sequence `mid : Fin m → I` representing `(k_1, ..., k_m)`.
When `m = 0` (`n = 1`), `mid` is the unique empty sequence and the path is `[i, j]`.
-/
def IndexPath.ofMiddle {I : Type u} {m : Nat} (i j : I) (mid : Fin m → I) :
    IndexPath I (m + 1) i j where
  nodes := Fin.cons i (Fin.snoc mid j)
  start_eq := by simp
  end_eq := by
    have hlast : Fin.last (m + 1) = (Fin.last m).succ := by
      ext
      simp
    rw [hlast, Fin.cons_succ, Fin.snoc_last]

/-- Extract the intermediate index sequence `(k_1, ..., k_m)` of a length-`(m + 1)` path. -/
def IndexPath.middle {I : Type u} {m : Nat} {i j : I}
    (p : IndexPath I (m + 1) i j) : Fin m → I :=
  fun t => p.nodes t.castSucc.succ

/--
Exact bijection between length-`(m + 1)` index paths from `i` to `j`
and intermediate index sequences `(k_1, ..., k_m) : Fin m → I`.
-/
def indexPathEquivMiddle {I : Type u} (m : Nat) (i j : I) :
    IndexPath I (m + 1) i j ≃ (Fin m → I) where
  toFun := IndexPath.middle
  invFun := IndexPath.ofMiddle i j
  left_inv p := by
    ext x
    refine Fin.cases ?_ ?_ x
    · simp [IndexPath.ofMiddle, p.start_eq]
    · intro y
      refine Fin.lastCases ?_ ?_ y
      · have hlast : (Fin.last m).succ = Fin.last (m + 1) := by
          ext
          simp
        simp [IndexPath.ofMiddle, hlast, p.end_eq]
      · intro t
        simp [IndexPath.ofMiddle, IndexPath.middle]
  right_inv mid := by
    funext t
    simp [IndexPath.ofMiddle, IndexPath.middle]

noncomputable instance instFintypeIndexPath {I : Type u} [Fintype I]
    (m : Nat) (i j : I) : Fintype (IndexPath I (m + 1) i j) :=
  Fintype.ofEquiv (Fin m → I) (indexPathEquivMiddle m i j).symm

instance instUniqueIndexPathOne {I : Type u} (i j : I) :
    Unique (IndexPath I 1 i j) where
  default := IndexPath.ofMiddle i j Fin.elim0
  uniq p := by
    apply (indexPathEquivMiddle 0 i j).injective
    funext t
    exact Fin.elim0 t

/-- The product of single-step matrix entries along a path `p`. -/
noncomputable def pathWeight {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) : ENNReal :=
  ∏ s : Fin n, p.stepEntry M s

/-- Predicate stating that every single-step matrix entry along path `p` is strictly positive. -/
def IsPositivePath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) : Prop :=
  ∀ s : Fin n, 0 < p.stepEntry M s

/-- Predicate stating that at least one single-step matrix entry along path `p` is zero. -/
def HasZeroFactorPath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) : Prop :=
  ∃ s : Fin n, p.stepEntry M s = 0

theorem not_isPositivePath_iff_hasZeroFactorPath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    ¬ IsPositivePath M p ↔ HasZeroFactorPath M p := by
  simp [IsPositivePath, HasZeroFactorPath, pos_iff_ne_zero]

theorem not_hasZeroFactorPath_iff_isPositivePath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    ¬ HasZeroFactorPath M p ↔ IsPositivePath M p := by
  rw [← not_isPositivePath_iff_hasZeroFactorPath, not_not]

private theorem finset_prod_eq_zero_iff_ennreal {α : Type*} (s : Finset α) (f : α → ENNReal) :
    (∏ a ∈ s, f a) = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, mul_eq_zero, ih]
      simp

theorem pathWeight_eq_zero_iff {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    pathWeight M p = 0 ↔ HasZeroFactorPath M p := by
  simpa [pathWeight, HasZeroFactorPath] using
    finset_prod_eq_zero_iff_ennreal (Finset.univ : Finset (Fin n)) (fun s => p.stepEntry M s)

theorem pathWeight_pos_iff {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    0 < pathWeight M p ↔ IsPositivePath M p := by
  rw [pos_iff_ne_zero, ne_eq, pathWeight_eq_zero_iff, ← not_isPositivePath_iff_hasZeroFactorPath,
    not_not]

private theorem ofMiddle_snoc_castSucc {I : Type u} {m : Nat}
    (i j k : I) (mid : Fin m → I) (t : Fin (m + 2)) :
    (IndexPath.ofMiddle i j (Fin.snoc mid k)).nodes t.castSucc =
      (IndexPath.ofMiddle i k mid).nodes t := by
  refine Fin.cases ?_ ?_ t
  · simp [IndexPath.ofMiddle]
  · intro y
    have hsucc : y.succ.castSucc = y.castSucc.succ := by
      ext
      simp
    rw [hsucc]
    simp [IndexPath.ofMiddle]

private def middleSnocEquiv {I : Type u} (m : Nat) :
    (I × (Fin m → I)) ≃ (Fin (m + 1) → I) where
  toFun p := Fin.snoc p.2 p.1
  invFun f := (f (Fin.last m), fun t => f t.castSucc)
  left_inv p := by
    rcases p with ⟨k, mid⟩
    ext
    · simp
    · simp
  right_inv f := by
    funext x
    refine Fin.lastCases ?_ ?_ x
    · simp
    · intro t
      simp

/--
Path expansion formula for an ordered nonempty product of `m + 1` extended nonnegative matrices,
summed over all intermediate index sequences `mid : Fin m → I`.
-/
theorem matrixEntry_orderedMatrixProdNonempty_eq_sum_middle {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j =
      ∑ mid : Fin m → I, pathWeight M (IndexPath.ofMiddle i j mid) := by
  induction m generalizing j with
  | zero =>
      simp only [orderedMatrixProdNonempty_zero, Fintype.sum_unique, pathWeight,
        Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one, IndexPath.stepEntry]
      have h0 : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
      have h1 : (0 : Fin 1).succ = Fin.last 1 := rfl
      rw [h0, h1, (IndexPath.ofMiddle i j default).start_eq,
        (IndexPath.ofMiddle i j default).end_eq]
  | succ m ih =>
      rw [orderedMatrixProdNonempty_succ, matrixEntry_gaugeMatrixMul]
      have h_expand :
          (∑ k : I, matrixEntry (M (Fin.last (m + 1))) k j *
              matrixEntry (orderedMatrixProdNonempty (fun s : Fin (m + 1) => M s.castSucc)) i k) =
            ∑ k : I, ∑ mid : Fin m → I,
              matrixEntry (M (Fin.last (m + 1))) k j *
                pathWeight (fun s : Fin (m + 1) => M s.castSucc) (IndexPath.ofMiddle i k mid) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [ih (fun s : Fin (m + 1) => M s.castSucc) k, Finset.mul_sum]
      rw [h_expand, ← Fintype.sum_prod_type']
      refine Fintype.sum_equiv (middleSnocEquiv m) _ _ ?_
      rintro ⟨k, mid⟩
      dsimp [middleSnocEquiv, pathWeight]
      symm
      rw [Fin.prod_univ_castSucc, mul_comm]
      congr 1
      · dsimp [IndexPath.stepEntry]
        have h_prev := ofMiddle_snoc_castSucc i j k mid (Fin.last (m + 1))
        rw [(IndexPath.ofMiddle i k mid).end_eq] at h_prev
        rw [h_prev, (IndexPath.ofMiddle i j (Fin.snoc mid k)).end_eq]
      · refine Finset.prod_congr rfl ?_
        intro s _
        dsimp [IndexPath.stepEntry]
        have h1 := ofMiddle_snoc_castSucc i j k mid s.castSucc
        have h2 := ofMiddle_snoc_castSucc i j k mid s.succ
        have hs : s.castSucc.succ = s.succ.castSucc := by
          ext
          simp
        rw [h1, hs, h2]

/--
Path expansion formula written as a sum over all `p : IndexPath I (m + 1) i j`.
-/
theorem matrixEntry_orderedMatrixProdNonempty_eq_sum_paths {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j =
      ∑ p : IndexPath I (m + 1) i j, pathWeight M p := by
  rw [matrixEntry_orderedMatrixProdNonempty_eq_sum_middle]
  symm
  refine Fintype.sum_equiv (indexPathEquivMiddle m i j) _ _ ?_
  intro p
  have h_inv : IndexPath.ofMiddle i j (indexPathEquivMiddle m i j p) = p :=
    (indexPathEquivMiddle m i j).left_inv p
  rw [h_inv]

/--
**Proposition 2.6 (i) (Zero-value criterion for finite nonempty matrix products)**:
For any `m + 1 ≥ 1` extended nonnegative matrices `M^(1), ..., M^(m+1)` and any `i, j ∈ I`,
`[M^(m+1) · ... · M^(1)]_{i → j} = 0` iff every length-`(m + 1)` index path from `i` to `j`
contains at least one zero factor. Covers `n = 1` (`m = 0`).
-/
theorem orderedMatrixProdNonempty_entry_eq_zero_iff {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j = 0 ↔
      ∀ p : IndexPath I (m + 1) i j, HasZeroFactorPath M p := by
  rw [matrixEntry_orderedMatrixProdNonempty_eq_sum_paths, Finset.sum_eq_zero_iff]
  simp [pathWeight_eq_zero_iff]

/--
Intermediate-sequence formulation of Proposition 2.6 (i), quantifying explicitly over
`(k_1, ..., k_{n-1}) : Fin m → I` with fixed endpoints `k_0 = i`, `k_n = j`.
-/
theorem orderedMatrixProdNonempty_entry_eq_zero_iff_middle {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j = 0 ↔
      ∀ mid : Fin m → I, HasZeroFactorPath M (IndexPath.ofMiddle i j mid) := by
  rw [matrixEntry_orderedMatrixProdNonempty_eq_sum_middle, Finset.sum_eq_zero_iff]
  simp [pathWeight_eq_zero_iff]

/--
Proposition 2.6 (i) stated for `orderedMatrixProd` at any length `n ≥ 1`.
-/
theorem orderedMatrixProd_entry_eq_zero_iff {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProd M) i j = 0 ↔
      ∀ p : IndexPath I n i j, HasZeroFactorPath M p := by
  cases n with
  | zero =>
      omega
  | succ m =>
      exact orderedMatrixProdNonempty_entry_eq_zero_iff M i j

/--
Explicit `n = 1` degeneration of Proposition 2.6 (i): the path condition reduces to
the single matrix entry `[M^(1)]_{i → j} = 0`.
-/
theorem orderedMatrixProdNonempty_entry_eq_zero_iff_one {I : Type u} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (∀ p : IndexPath I 1 i j, HasZeroFactorPath M p) ↔ matrixEntry (M 0) i j = 0 := by
  rw [← orderedMatrixProdNonempty_entry_eq_zero_iff M i j, orderedMatrixProdNonempty_zero]

/--
**Proposition 2.6 (ii) (Positivity criterion for finite nonempty matrix products)**:
For any `m + 1 ≥ 1` extended nonnegative matrices `M^(1), ..., M^(m+1)` and any `i, j ∈ I`,
`[M^(m+1) · ... · M^(1)]_{i → j} > 0` iff there exists at least one length-`(m + 1)` index path
from `i` to `j` whose every single-step matrix entry is strictly positive. Covers `n = 1` (`m = 0`).
-/
theorem orderedMatrixProdNonempty_entry_pos_iff {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    0 < matrixEntry (orderedMatrixProdNonempty M) i j ↔
      ∃ p : IndexPath I (m + 1) i j, IsPositivePath M p := by
  rw [pos_iff_ne_zero, ne_eq, orderedMatrixProdNonempty_entry_eq_zero_iff]
  push Not
  simp [not_hasZeroFactorPath_iff_isPositivePath]

/--
Intermediate-sequence formulation of Proposition 2.6 (ii), quantifying explicitly over
`(k_1, ..., k_{n-1}) : Fin m → I` with fixed endpoints `k_0 = i`, `k_n = j`.
-/
theorem orderedMatrixProdNonempty_entry_pos_iff_middle {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    0 < matrixEntry (orderedMatrixProdNonempty M) i j ↔
      ∃ mid : Fin m → I, IsPositivePath M (IndexPath.ofMiddle i j mid) := by
  rw [pos_iff_ne_zero, ne_eq, orderedMatrixProdNonempty_entry_eq_zero_iff_middle]
  push Not
  simp [not_hasZeroFactorPath_iff_isPositivePath]

/--
Proposition 2.6 (ii) stated for `orderedMatrixProd` at any length `n ≥ 1`.
-/
theorem orderedMatrixProd_entry_pos_iff {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < matrixEntry (orderedMatrixProd M) i j ↔
      ∃ p : IndexPath I n i j, IsPositivePath M p := by
  cases n with
  | zero =>
      omega
  | succ m =>
      exact orderedMatrixProdNonempty_entry_pos_iff M i j

/--
Explicit `n = 1` degeneration of Proposition 2.6 (ii): the path condition reduces to
the single matrix entry `[M^(1)]_{i → j} > 0`.
-/
theorem orderedMatrixProdNonempty_entry_pos_iff_one {I : Type u} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (∃ p : IndexPath I 1 i j, IsPositivePath M p) ↔ 0 < matrixEntry (M 0) i j := by
  rw [← orderedMatrixProdNonempty_entry_pos_iff M i j, orderedMatrixProdNonempty_zero]

end LCH02
