import LCH02.MatrixBounds

namespace LCH02

open scoped BigOperators

noncomputable section

variable {I : Type}

/-- A path has fixed endpoints and one arrow per matrix, in chronological order.
For a singleton matrix list it has no free intermediate vertex. -/
inductive IndexPath : List (BoundMatrix I) → I → I → Type
  | nil (i : I) : IndexPath [] i i
  | cons {M : BoundMatrix I} {Ms : List (BoundMatrix I)} {i k j : I}
      (tail : IndexPath Ms k j) : IndexPath (M :: Ms) i j

def singletonPathEquiv (M : BoundMatrix I) (i j : I) : IndexPath [M] i j ≃ Unit where
  toFun _ := ()
  invFun _ := IndexPath.cons (IndexPath.nil j)
  left_inv p := by
    cases p with
    | cons tail => cases tail; rfl
  right_inv u := by cases u; rfl

def AllPositive : {Ms : List (BoundMatrix I)} → {i j : I} → IndexPath Ms i j → Prop
  | _, _, _, .nil _ => True
  | _, _, _, @IndexPath.cons _ M _ i k _ tail => 0 < M k i ∧ AllPositive tail

def ZeroFactor : {Ms : List (BoundMatrix I)} → {i j : I} → IndexPath Ms i j → Prop
  | _, _, _, .nil _ => False
  | _, _, _, @IndexPath.cons _ M _ i k _ tail => M k i = 0 ∨ ZeroFactor tail

theorem not_allPositive_iff_zeroFactor {Ms : List (BoundMatrix I)} {i j : I}
    (p : IndexPath Ms i j) : ¬ AllPositive p ↔ ZeroFactor p := by
  classical
  induction p with
  | nil => simp [AllPositive, ZeroFactor]
  | cons tail ih =>
      simp only [AllPositive, ZeroFactor, not_and_or, pos_iff_ne_zero, not_not, ih]

theorem matrixProduct_pos_iff [Fintype I] [DecidableEq I]
    (Ms : List (BoundMatrix I)) (i j : I) :
    0 < matrixProduct Ms j i ↔ ∃ p : IndexPath Ms i j, AllPositive p := by
  induction Ms generalizing i j with
  | nil =>
      constructor
      · intro h
        simp only [matrixProduct_nil, Matrix.one_apply] at h
        split_ifs at h with heq
        · subst j
          exact ⟨IndexPath.nil i, trivial⟩
        · exact (lt_irrefl 0 h).elim
      · rintro ⟨p, _⟩
        cases p
        simp
  | cons M Ms ih =>
      rw [matrixProduct_cons, Matrix.mul_apply]
      constructor
      · intro h
        obtain ⟨k, _, hk⟩ := Finset.sum_pos_iff.mp h
        obtain ⟨htail, hentry⟩ := ENNReal.mul_pos_iff.mp hk
        obtain ⟨p, hp⟩ := (ih k j).mp htail
        exact ⟨IndexPath.cons p, hentry, hp⟩
      · rintro ⟨p, hp⟩
        cases p with
        | @cons _ _ _ k _ tail =>
            apply Finset.sum_pos_iff.mpr
            exact ⟨k, Finset.mem_univ k,
              ENNReal.mul_pos_iff.mpr ⟨(ih k j).mpr ⟨tail, hp.2⟩, hp.1⟩⟩

theorem matrixProduct_zero_iff [Fintype I] [DecidableEq I]
    (Ms : List (BoundMatrix I)) (i j : I) :
    matrixProduct Ms j i = 0 ↔ ∀ p : IndexPath Ms i j, ZeroFactor p := by
  constructor
  · intro hz p
    apply (not_allPositive_iff_zeroFactor p).mp
    intro hp
    have hpos := (matrixProduct_pos_iff Ms i j).mpr ⟨p, hp⟩
    simp only [hz, lt_self_iff_false] at hpos
  · intro hz
    by_contra hne
    obtain ⟨p, hp⟩ := (matrixProduct_pos_iff Ms i j).mp (pos_iff_ne_zero.mpr hne)
    exact ((not_allPositive_iff_zeroFactor p).mpr (hz p)) hp

/-- Explicit length-one boundary cases. -/
theorem singleton_path_pos [Fintype I] [DecidableEq I] (M : BoundMatrix I) (i j : I) :
    (∃ p : IndexPath [M] i j, AllPositive p) ↔ 0 < M j i := by
  simpa using (matrixProduct_pos_iff [M] i j).symm

theorem singleton_path_zero [Fintype I] [DecidableEq I] (M : BoundMatrix I) (i j : I) :
    (∀ p : IndexPath [M] i j, ZeroFactor p) ↔ M j i = 0 := by
  simpa using (matrixProduct_zero_iff [M] i j).symm

end
end LCH02
