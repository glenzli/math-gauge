import Mathlib
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# Chapter 2: finite extended nonnegative matrices and paths

This file formalizes the matrix-indexing convention used throughout Chapter 2
of the source text, the ordered finite product of such matrices, and the
positive/zero path criteria (Proposition 2.6).

An entry `M i j` always has `i` as the input component (column) and `j` as the
output component (row).  Thus composition `φ₂ ∘ φ₁` uses the product
`matMul L₂ L₁`, whose entry is `∑ k, L₂ k j * L₁ i k`.
-/

namespace OET.Chapter02

open formal_oet.vol_01.ch_01_foundations

universe u

noncomputable section

/-- Extended nonnegative matrices indexed by a finite component set.
`M i j` is the coefficient from input component `i` to output component `j`. -/
abbrev Mat (I : Type) := I → I → ENNReal

/-- The identity matrix with respect to the input/output convention. -/
def matId {I : Type} [DecidableEq I] : Mat I :=
  fun i j => if i = j then 1 else 0

@[simp]
theorem matId_apply {I : Type} [DecidableEq I] (i j : I) :
    matId i j = if i = j then 1 else 0 := rfl

/-- Matrix multiplication in source convention:
`(M₂ · M₁) i j = ∑ k, M₂ k j * M₁ i k`. -/
def matMul {I : Type} [Fintype I] (M₂ M₁ : Mat I) : Mat I :=
  fun i j => ∑ k, M₂ k j * M₁ i k

@[simp]
theorem matMul_apply {I : Type} [Fintype I] (M₂ M₁ : Mat I) (i j : I) :
    matMul M₂ M₁ i j = ∑ k, M₂ k j * M₁ i k := rfl

theorem matMul_matId {I : Type} [Fintype I] [DecidableEq I] (M : Mat I) :
    matMul M matId = M := by
  funext i j
  rw [matMul_apply, Finset.sum_eq_single i]
  · simp [matId]
  · intro k _ hki
    simp [matId, Ne.symm hki]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem matId_matMul {I : Type} [Fintype I] [DecidableEq I] (M : Mat I) :
    matMul matId M = M := by
  funext i j
  rw [matMul_apply, Finset.sum_eq_single j]
  · simp [matId]
  · intro k _ hkj
    simp [matId, hkj]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Associativity of the source-convention matrix product. -/
theorem matMul_assoc {I : Type} [Fintype I] (A B C : Mat I) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  simp only [matMul_apply]
  calc
    (∑ k, (∑ l, A l j * B k l) * C i k)
        = ∑ k, ∑ l, A l j * B k l * C i k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ = ∑ l, ∑ k, A l j * B k l * C i k := Finset.sum_comm
    _ = ∑ l, A l j * ∑ k, B k l * C i k := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- Ordered product of a finite nonempty family of matrices.

The recurrence multiplies the last matrix on the outside and the prefix on the
inside.  Thus for `M : Fin n → Mat I`,
`orderedMatProd M = M (n-1) · ... · M 0`, exactly the product needed for a
chain whose zeroth step acts first.  The empty case is `matId`. -/
def orderedMatProd {I : Type} [Fintype I] [DecidableEq I] :
    {n : ℕ} → (Fin n → Mat I) → Mat I
  | 0, _ => matId
  | n + 1, M => matMul (M (Fin.last n)) (orderedMatProd (fun k => M k.castSucc))

@[simp]
theorem orderedMatProd_zero {I : Type} [Fintype I] [DecidableEq I]
    (M : Fin 0 → Mat I) :
    orderedMatProd M = matId := rfl

theorem orderedMatProd_succ {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (M : Fin (n + 1) → Mat I) :
    orderedMatProd M =
      matMul (M (Fin.last n)) (orderedMatProd (fun k : Fin n => M k.castSucc)) :=
  rfl

/-- The one-step ordered product is the original matrix. -/
theorem orderedMatProd_one {I : Type} [Fintype I] [DecidableEq I]
    (M : Mat I) :
    orderedMatProd (fun _ : Fin 1 => M) = M := by
  rw [orderedMatProd_succ, orderedMatProd_zero, matMul_matId]

/-- A path of length `n` from `i` to `j`, represented by its `n + 1` vertices.
This is the path object used in Proposition 2.6. -/
structure Path (I : Type) (n : ℕ) (i j : I) where
  vertex : Fin (n + 1) → I
  start : vertex 0 = i
  finish : vertex (Fin.last n) = j

namespace Path

/-- Extend a path by one final vertex. -/
def snoc {I : Type} {n : ℕ} {i j : I} (p : Path I n i j) (k : I) :
    Path I (n + 1) i k where
  vertex := Fin.snoc p.vertex k
  start := by
    simpa [Fin.snoc_castSucc] using p.start
  finish := by
    simp

/-- Remove the last vertex of a path. -/
def prePath {I : Type} {n : ℕ} {i j : I} (p : Path I (n + 1) i j) :
    Path I n i (p.vertex (Fin.castSucc (Fin.last n))) where
  vertex m := p.vertex m.castSucc
  start := p.start
  finish := rfl

/-- The penultimate vertex of a positive-length path. -/
def lastVertex {I : Type} {n : ℕ} {i j : I} (p : Path I (n + 1) i j) : I :=
  p.vertex (Fin.castSucc (Fin.last n))

@[simp]
lemma snoc_vertex_castSucc {I : Type} {n : ℕ} {i j : I}
    (p : Path I n i j) (k : I) (m : Fin (n + 1)) :
    (p.snoc k).vertex m.castSucc = p.vertex m := by
  simp [snoc, Fin.snoc_castSucc]

@[simp]
lemma snoc_vertex_last {I : Type} {n : ℕ} {i j : I}
    (p : Path I n i j) (k : I) :
    (p.snoc k).vertex (Fin.last (n + 1)) = k := by
  simp [snoc]

end Path

/-- A path is all-positive when every one of its matrix entries is strictly
positive. -/
def IsPositivePath {I : Type} {n : ℕ} {i j : I}
    (M : Fin n → Mat I) (p : Path I n i j) : Prop :=
  ∀ m : Fin n, 0 < M m (p.vertex m.castSucc) (p.vertex m.succ)

/-- A path has a zero when at least one of its matrix entries is zero. -/
def PathHasZero {I : Type} {n : ℕ} {i j : I}
    (M : Fin n → Mat I) (p : Path I n i j) : Prop :=
  ∃ m : Fin n, M m (p.vertex m.castSucc) (p.vertex m.succ) = 0

lemma snoc_edge_castSucc {I : Type} {n : ℕ} {i j : I}
    (p : Path I n i j) (k : I) (m : Fin n) :
    (p.snoc k).vertex ((m.castSucc).castSucc) = p.vertex m.castSucc ∧
      (p.snoc k).vertex ((m.castSucc).succ) = p.vertex m.succ := by
  constructor
  · exact Path.snoc_vertex_castSucc p k m.castSucc
  · rw [Fin.succ_castSucc, Path.snoc_vertex_castSucc]

lemma positivePath_snoc_iff {I : Type} {n : ℕ} {i k j : I}
    (M : Fin (n + 1) → Mat I) (p : Path I n i k)
    (hlast : 0 < M (Fin.last n) k j) :
    IsPositivePath M (p.snoc j) ↔
      IsPositivePath (fun m : Fin n => M m.castSucc) p := by
  constructor
  · intro h m
    have hm := h m.castSucc
    obtain ⟨h1, h2⟩ := snoc_edge_castSucc p j m
    simpa [IsPositivePath, h1, h2] using hm
  · intro h m
    cases m using Fin.lastCases with
    | last =>
        have hstart : (p.snoc j).vertex ((Fin.last n).castSucc) = k := by
          rw [Path.snoc_vertex_castSucc]
          exact p.finish
        have hend : (p.snoc j).vertex ((Fin.last n).succ) = j := by
          rw [Fin.succ_last, Path.snoc_vertex_last]
        rw [hstart, hend]
        exact hlast
    | cast m =>
        have hm := h m
        obtain ⟨h1, h2⟩ := snoc_edge_castSucc p j m
        simpa [IsPositivePath, h1, h2] using hm

lemma positivePath_prePath {I : Type} {n : ℕ} {i j : I}
    (M : Fin (n + 1) → Mat I) (p : Path I (n + 1) i j)
    (h : IsPositivePath M p) :
    IsPositivePath (fun m : Fin n => M m.castSucc) p.prePath ∧
      0 < M (Fin.last n) p.lastVertex j := by
  constructor
  · intro m
    have hm := h m.castSucc
    have hend : p.vertex ((m.castSucc).succ) = p.vertex (m.succ).castSucc := by
      rw [Fin.succ_castSucc]
    simpa [IsPositivePath, Path.prePath, hend] using hm
  · have hm := h (Fin.last n)
    have hstart : p.vertex ((Fin.last n).castSucc) = p.lastVertex := rfl
    have hend : p.vertex ((Fin.last n).succ) = j := by
      rw [Fin.succ_last]
      exact p.finish
    rw [hstart, hend] at hm
    exact hm

/-- Proposition 2.6(ii), in the stronger all-length form used as a lemma.
The source states it for `n ≥ 1`; the `n = 0` case is the empty product. -/
theorem orderedMatProd_pos_iff_exists_positivePath
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}
    (M : Fin n → Mat I) (i j : I) :
    0 < orderedMatProd M i j ↔
      ∃ p : Path I n i j, IsPositivePath M p := by
  revert M i j
  induction n with
  | zero =>
      intro M i j
      constructor
      · intro h
        by_cases hij : i = j
        · subst j
          refine ⟨⟨fun _ => i, rfl, rfl⟩, ?_⟩
          intro m
          exact Fin.elim0 m
        · have hz : matId (I := I) i j = 0 := by simp [matId, hij]
          rw [orderedMatProd, hz] at h
          exact False.elim ((lt_irrefl (0 : ENNReal)) h)
      · rintro ⟨p, _hp⟩
        have hlast0 : Fin.last (0 : ℕ) = (0 : Fin 1) := rfl
        have hij : i = j := by
          calc
            i = p.vertex 0 := p.start.symm
            _ = p.vertex (Fin.last 0) := by rw [hlast0]
            _ = j := p.finish
        subst j
        simp [orderedMatProd, matId]
  | succ n ih =>
      intro M i j
      change 0 < matMul (M (Fin.last n))
          (orderedMatProd (fun k : Fin n => M k.castSucc)) i j ↔ _
      rw [matMul, Finset.sum_pos_iff_of_nonneg (fun k _ => zero_le _)]
      constructor
      · rintro ⟨k, _, hk⟩
        rw [ENNReal.mul_pos_iff] at hk
        obtain ⟨hlast, hpre⟩ := hk
        obtain ⟨p, hp⟩ :=
          (ih (fun m : Fin n => M m.castSucc) i k).1 hpre
        exact ⟨p.snoc j, (positivePath_snoc_iff M p hlast).2 hp⟩
      · rintro ⟨q, hq⟩
        obtain ⟨hpre, hlast⟩ := positivePath_prePath M q hq
        have hprod : 0 < orderedMatProd
            (fun m : Fin n => M m.castSucc) i q.lastVertex :=
          (ih (fun m : Fin n => M m.castSucc) i q.lastVertex).2
            ⟨q.prePath, hpre⟩
        refine ⟨q.lastVertex, Finset.mem_univ _, ?_⟩
        exact ENNReal.mul_pos (ne_of_gt hlast) (ne_of_gt hprod)

/-- Proposition 2.6(i), in the stronger all-length form used as a lemma. -/
theorem orderedMatProd_eq_zero_iff_forall_pathHasZero
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}
    (M : Fin n → Mat I) (i j : I) :
    orderedMatProd M i j = 0 ↔
      ∀ p : Path I n i j, PathHasZero M p := by
  have hnot : orderedMatProd M i j = 0 ↔
      ¬ 0 < orderedMatProd M i j := by
    constructor
    · intro h
      rw [h]
      exact not_lt.mpr le_rfl
    · intro h
      exact le_antisymm (not_lt.mp h) (zero_le _)
  rw [hnot, orderedMatProd_pos_iff_exists_positivePath]
  constructor
  · intro h p
    by_contra hpz
    apply h
    refine ⟨p, ?_⟩
    intro m
    exact pos_iff_ne_zero.mpr (by
      intro hm
      exact hpz ⟨m, hm⟩)
  · rintro h ⟨p, hp⟩
    obtain ⟨m, hm⟩ := h p
    have hpos := hp m
    rw [hm] at hpos
    exact (lt_irrefl (0 : ENNReal)) hpos

/-- Proposition 2.6(ii) with the source's explicit nonempty-length hypothesis. -/
theorem orderedMatProd_pos_iff_exists_positivePath_of_pos
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ} (_hn : 0 < n)
    (M : Fin n → Mat I) (i j : I) :
    0 < orderedMatProd M i j ↔
      ∃ p : Path I n i j, IsPositivePath M p :=
  orderedMatProd_pos_iff_exists_positivePath M i j

/-- Proposition 2.6(i) with the source's explicit nonempty-length hypothesis. -/
theorem orderedMatProd_eq_zero_iff_forall_pathHasZero_of_pos
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ} (_hn : 0 < n)
    (M : Fin n → Mat I) (i j : I) :
    orderedMatProd M i j = 0 ↔
      ∀ p : Path I n i j, PathHasZero M p :=
  orderedMatProd_eq_zero_iff_forall_pathHasZero M i j

end

end OET.Chapter02
