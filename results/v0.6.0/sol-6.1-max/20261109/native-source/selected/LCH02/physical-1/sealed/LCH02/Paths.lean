import LCH02.Bounds

namespace LCH02

noncomputable section

open scoped BigOperators

/-- A path with `r` intermediate indices. `r = 0` has exactly one empty path. -/
def IndexPath (I : Type) : ℕ → Type
  | 0 => PUnit
  | r + 1 => I × IndexPath I r

variable {I : Type}

/-- The nonempty chronological matrix list is `M :: Ms`.
Each component of the path chooses the next intermediate index. -/
def AllPositivePath : (M : BoundMatrix I) → (Ms : List (BoundMatrix I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => 0 < M j i
  | M, N :: Ns, i, j, p => 0 < M p.1 i ∧ AllPositivePath N Ns p.1 j p.2

def HasZeroFactor : (M : BoundMatrix I) → (Ms : List (BoundMatrix I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => M j i = 0
  | M, N :: Ns, i, j, p => M p.1 i = 0 ∨ HasZeroFactor N Ns p.1 j p.2

theorem positivePath_iff_no_zero (M : BoundMatrix I) (Ms : List (BoundMatrix I))
    (i j : I) (p : IndexPath I Ms.length) :
    AllPositivePath M Ms i j p ↔ ¬ HasZeroFactor M Ms i j p := by
  induction Ms generalizing M i j with
  | nil => simp [AllPositivePath, HasZeroFactor, pos_iff_ne_zero]
  | cons N Ns ih =>
      rcases p with ⟨k, p⟩
      simp only [AllPositivePath, HasZeroFactor, not_or, pos_iff_ne_zero, ih]

variable [Fintype I] [DecidableEq I]

theorem product_pos_iff_path (M : BoundMatrix I) (Ms : List (BoundMatrix I)) (i j : I) :
    0 < orderedProduct (M :: Ms) j i ↔
      ∃ p : IndexPath I Ms.length, AllPositivePath M Ms i j p := by
  induction Ms generalizing M i j with
  | nil => simp [orderedProduct, IndexPath, AllPositivePath]
  | cons N Ns ih =>
      change (0 < ∑ k, orderedProduct (N :: Ns) j k * M k i) ↔ _
      rw [Finset.sum_pos_iff]
      constructor
      · rintro ⟨k, _, hk⟩
        obtain ⟨htail, hfirst⟩ := ENNReal.mul_pos_iff.mp hk
        obtain ⟨p, hp⟩ := (ih N k j).mp htail
        exact ⟨⟨k, p⟩, hfirst, hp⟩
      · rintro ⟨⟨k, p⟩, hfirst, hp⟩
        exact ⟨k, Finset.mem_univ _, ENNReal.mul_pos_iff.mpr ⟨(ih N k j).mpr ⟨p, hp⟩, hfirst⟩⟩

theorem product_zero_iff_paths (M : BoundMatrix I) (Ms : List (BoundMatrix I)) (i j : I) :
    orderedProduct (M :: Ms) j i = 0 ↔
      ∀ p : IndexPath I Ms.length, HasZeroFactor M Ms i j p := by
  classical
  have hz : orderedProduct (M :: Ms) j i = 0 ↔
      ¬ 0 < orderedProduct (M :: Ms) j i := by
    simp [pos_iff_ne_zero]
  rw [hz, product_pos_iff_path]
  simp only [not_exists, positivePath_iff_no_zero, not_not]

end
end LCH02
