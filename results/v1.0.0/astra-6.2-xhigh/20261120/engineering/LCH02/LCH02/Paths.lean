import LCH02.Bounds

namespace LCH02

open scoped Classical
noncomputable section

/-- The intermediate indices, starting with the one nearest the output. -/
def Interior (I : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => I × Interior I n

variable {I : Type}

def factors (first : Mat I) (i : I) :
    (later : List (Mat I)) → (j : I) → Interior I later.length → List ENNReal
  | [], j, _ => [entry first i j]
  | A :: t, j, (k, p) => entry A k j :: factors first i t k p

def PositivePath (first : Mat I) (i : I) (later : List (Mat I)) (j : I)
    (p : Interior I later.length) : Prop := ∀ a ∈ factors first i later j p, 0 < a

theorem factors_length (first : Mat I) (i : I) (later : List (Mat I)) (j : I)
    (p : Interior I later.length) : (factors first i later j p).length = later.length + 1 := by
  induction later generalizing j with
  | nil => rfl
  | cons A t ih =>
    obtain ⟨k, p⟩ := p
    exact congrArg Nat.succ (ih k p)

variable [Fintype I]

theorem product_positive_iff (first : Mat I) (later : List (Mat I)) (i j : I) :
    0 < entry (orderedProduct (later ++ [first])) i j ↔
      ∃ p : Interior I later.length, PositivePath first i later j p := by
  induction later generalizing j with
  | nil => simp [orderedProduct, PositivePath, factors, Interior]
  | cons A t ih =>
    rw [List.cons_append, product_cons, entry_mul, Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _)]
    simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff]
    constructor
    · rintro ⟨k, hk, hpre⟩
      obtain ⟨p, hp⟩ := (ih k).mp hpre
      exact ⟨(k, p), List.forall_mem_cons.mpr ⟨hk, hp⟩⟩
    · rintro ⟨⟨k, p⟩, h⟩
      have hparts := List.forall_mem_cons.mp h
      exact ⟨k, hparts.1, (ih k).mpr ⟨p, hparts.2⟩⟩

theorem product_zero_iff (first : Mat I) (later : List (Mat I)) (i j : I) :
    entry (orderedProduct (later ++ [first])) i j = 0 ↔
      ∀ p : Interior I later.length, 0 ∈ factors first i later j p := by
  have nozero (p : Interior I later.length) :
      PositivePath first i later j p ↔ 0 ∉ factors first i later j p := by
    constructor
    · intro h h0
      exact (lt_irrefl 0) (h 0 h0)
    · intro h a ha
      exact pos_iff_ne_zero.mpr (fun e => h (e ▸ ha))
  simpa only [pos_iff_ne_zero, nozero, not_exists, not_not] using
    (not_congr (product_positive_iff first later i j))

end
end LCH02
