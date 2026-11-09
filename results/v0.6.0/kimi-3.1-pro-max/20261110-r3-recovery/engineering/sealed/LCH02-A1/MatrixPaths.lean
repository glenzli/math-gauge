import OperatorBounds
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Finite matrix products and component-index paths

An index path stores only its intermediate vertices.  For a list of `n`
matrices it has length `n - 1`; in particular the unique path for one matrix
is empty.  Its factors use the same input/output convention as `channelEntry`.
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators Classical

/-- Adjacent directed edges of a vertex list. -/
def adjacentPairs {I : Type} : List I → List (I × I)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: adjacentPairs (b :: rest)

/-- The full vertex list determined by endpoints and intermediate vertices. -/
def pathVertices {I : Type} (i j : I) (p : List I) : List I := i :: (p ++ [j])

/-- The channel entries along a path, in order of application. -/
def pathFactors {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) :
    List ENNReal :=
  List.zipWith (fun M e => channelEntry M e.1 e.2) Ms
    (adjacentPairs (pathVertices i j p))

/-- Product of all channel entries along a path. -/
noncomputable def pathWeight {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) : ENNReal :=
  (pathFactors Ms i j p).prod

/-- A finite index path has exactly one fewer intermediate vertex than the
number of matrices. -/
def IsIndexPath {I : Type} (Ms : List (ChannelMatrix I)) (p : List I) : Prop :=
  p.length + 1 = Ms.length

/-- A valid path is all-positive when every one-step entry is strictly positive. -/
def IsAllPositivePath {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) : Prop :=
  IsIndexPath Ms p ∧ ∀ a ∈ pathFactors Ms i j p, 0 < a

@[simp] theorem pathWeight_singleton {I : Type} (M : ChannelMatrix I) (i j : I) :
    pathWeight [M] i j [] = channelEntry M i j := by
  simp [pathWeight, pathFactors, pathVertices, adjacentPairs]

@[simp] theorem pathFactors_singleton {I : Type} (M : ChannelMatrix I) (i j : I) :
    pathFactors [M] i j [] = [channelEntry M i j] := by
  simp [pathFactors, pathVertices, adjacentPairs]

/-- Split the first edge from a path through at least two matrices. -/
theorem pathFactors_cons_two {I : Type} (M N : ChannelMatrix I)
    (Ms : List (ChannelMatrix I)) (i j k : I) (p : List I) :
    pathFactors (M :: N :: Ms) i j (k :: p) =
      channelEntry M i k :: pathFactors (N :: Ms) k j p := by
  simp [pathFactors, pathVertices, adjacentPairs]

/-- Multiplicative form of `pathFactors_cons_two`. -/
theorem pathWeight_cons_two {I : Type} (M N : ChannelMatrix I)
    (Ms : List (ChannelMatrix I)) (i j k : I) (p : List I) :
    pathWeight (M :: N :: Ms) i j (k :: p) =
      channelEntry M i k * pathWeight (N :: Ms) k j p := by
  simp [pathWeight, pathFactors_cons_two]

@[simp] theorem isIndexPath_singleton_iff {I : Type} (M : ChannelMatrix I) (p : List I) :
    IsIndexPath [M] p ↔ p = [] := by
  constructor
  · intro h
    apply List.length_eq_zero_iff.mp
    unfold IsIndexPath at h
    simp only [List.length_cons, List.length_nil] at h
    omega
  · rintro rfl
    rfl

@[simp] theorem isIndexPath_cons_two_iff {I : Type} (M N : ChannelMatrix I)
    (Ms : List (ChannelMatrix I)) (k : I) (p : List I) :
    IsIndexPath (M :: N :: Ms) (k :: p) ↔ IsIndexPath (N :: Ms) p := by
  unfold IsIndexPath
  simp only [List.length_cons, List.length_nil]
  omega

/-- In a canonically ordered semiring with no zero divisors, a path product
is positive exactly when all its factors are positive. -/
theorem pathWeight_pos_iff {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) :
    0 < pathWeight Ms i j p ↔ ∀ a ∈ pathFactors Ms i j p, 0 < a := by
  simp only [pathWeight, pos_iff_ne_zero, ne_eq, List.prod_eq_zero_iff]
  constructor
  · intro h a ha hzero
    apply h
    simpa [hzero] using ha
  · intro h hmem
    exact h 0 hmem rfl

/-- Zero-entry criterion for every nonempty ordered matrix product.  The
`n = 1` case is the singleton branch and uses the unique empty path. -/
theorem orderedMatrixProduct_entry_eq_zero_iff {I : Type} [Fintype I]
    (Ms : List (ChannelMatrix I)) (hMs : Ms ≠ []) (i j : I) :
    channelEntry (orderedMatrixProduct Ms) i j = 0 ↔
      ∀ p : List I, IsIndexPath Ms p → pathWeight Ms i j p = 0 := by
  induction Ms generalizing i j with
  | nil => exact (hMs rfl).elim
  | cons M Ms ih =>
      cases Ms with
      | nil =>
          constructor
          · intro h p hp
            have hp' : p = [] := (isIndexPath_singleton_iff M p).mp hp
            subst p
            simpa using h
          · intro h
            have hp : IsIndexPath [M] [] := rfl
            simpa using h [] hp
      | cons N Ms =>
          have ih' := ih (List.cons_ne_nil N Ms)
          rw [orderedMatrixProduct_cons, channelEntry_mul]
          have hsum :
              (∑ k : I, channelEntry (orderedMatrixProduct (N :: Ms)) k j *
                channelEntry M i k) = 0 ↔
              ∀ k : I, channelEntry (orderedMatrixProduct (N :: Ms)) k j *
                channelEntry M i k = 0 := by
            constructor
            · intro h k
              exact (Finset.sum_eq_zero_iff_of_nonneg
                (fun k _ => zero_le (channelEntry (orderedMatrixProduct (N :: Ms)) k j *
                  channelEntry M i k))).mp h k (Finset.mem_univ k)
            · intro h
              exact Finset.sum_eq_zero fun k _ => h k
          rw [hsum]
          constructor
          · intro hterms p hp
            cases p with
            | nil => simp [IsIndexPath] at hp
            | cons k q =>
                have hq : IsIndexPath (N :: Ms) q :=
                  (isIndexPath_cons_two_iff M N Ms k q).mp hp
                rw [pathWeight_cons_two]
                have hterm := hterms k
                by_cases hM : channelEntry M i k = 0
                · rw [hM, zero_mul]
                · have hT : channelEntry (orderedMatrixProduct (N :: Ms)) k j = 0 := by
                    rcases mul_eq_zero.mp hterm with hT | hM0
                    · exact hT
                    · exact (hM hM0).elim
                  have hq0 : pathWeight (N :: Ms) k j q = 0 :=
                    (ih' k j).mp hT q hq
                  simp [hq0]
          · intro hpaths k
            by_cases hM : channelEntry M i k = 0
            · rw [hM, mul_zero]
            · have hT : channelEntry (orderedMatrixProduct (N :: Ms)) k j = 0 := by
                apply (ih' k j).mpr
                intro q hq
                have hfull := hpaths (k :: q)
                  ((isIndexPath_cons_two_iff M N Ms k q).mpr hq)
                rw [pathWeight_cons_two] at hfull
                rcases mul_eq_zero.mp hfull with hM0 | hq0
                · exact (hM hM0).elim
                · exact hq0
              rw [hT, zero_mul]

/-- Zero-entry criterion in the source's explicit form: every valid path
has at least one zero factor. -/
theorem orderedMatrixProduct_entry_eq_zero_iff_exists_zero_factor {I : Type} [Fintype I]
    (Ms : List (ChannelMatrix I)) (hMs : Ms ≠ []) (i j : I) :
    channelEntry (orderedMatrixProduct Ms) i j = 0 ↔
      ∀ p : List I, IsIndexPath Ms p →
        ∃ a ∈ pathFactors Ms i j p, a = 0 := by
  rw [orderedMatrixProduct_entry_eq_zero_iff Ms hMs i j]
  constructor
  · intro h p hp
    have hz : pathWeight Ms i j p = 0 := h p hp
    have hmem : (0 : ENNReal) ∈ pathFactors Ms i j p := by
      rw [← List.prod_eq_zero_iff]
      exact hz
    exact ⟨0, hmem, rfl⟩
  · intro h p hp
    rcases h p hp with ⟨a, ha, ha0⟩
    rw [pathWeight, List.prod_eq_zero_iff]
    simpa [ha0] using ha

/-- Positive-entry criterion: a nonempty ordered product entry is strictly
positive exactly when at least one valid path has all entries positive. -/
theorem orderedMatrixProduct_entry_pos_iff {I : Type} [Fintype I]
    (Ms : List (ChannelMatrix I)) (hMs : Ms ≠ []) (i j : I) :
    0 < channelEntry (orderedMatrixProduct Ms) i j ↔
      ∃ p : List I, IsAllPositivePath Ms i j p := by
  constructor
  · intro hpos
    have hne : channelEntry (orderedMatrixProduct Ms) i j ≠ 0 := ne_of_gt hpos
    have hnot : ¬ (∀ p : List I, IsIndexPath Ms p → pathWeight Ms i j p = 0) := by
      intro hzero
      exact hne ((orderedMatrixProduct_entry_eq_zero_iff Ms hMs i j).mpr hzero)
    push_neg at hnot
    rcases hnot with ⟨p, hp, hw⟩
    refine ⟨p, hp, ?_⟩
    exact (pathWeight_pos_iff Ms i j p).mp (pos_iff_ne_zero.mpr hw)
  · rintro ⟨p, hp, hall⟩
    have hw : 0 < pathWeight Ms i j p := (pathWeight_pos_iff Ms i j p).mpr hall
    apply pos_iff_ne_zero.mpr
    intro hentry
    have hzero := (orderedMatrixProduct_entry_eq_zero_iff Ms hMs i j).mp hentry
    exact (ne_of_gt hw) (hzero p hp)

end formal_oet.vol_01.ch_02_operator_bounds
