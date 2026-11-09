import Chains

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

variable {I X : Type} {bot : X} [Fintype I] [Nonempty I]

/-- All intermediate index sequences, without any support or positivity restriction. -/
def Interior (I : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => I × Interior I n

instance interiorFintype : (n : ℕ) → Fintype (Interior I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := interiorFintype n
    exact inferInstanceAs (Fintype (I × Interior I n))

def interiorEquiv : (n : ℕ) → Interior I n ≃ (Fin n → I)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := by intro p; cases p; rfl
      right_inv := by intro f; funext k; exact Fin.elim0 k }
  | n + 1 =>
    { toFun := fun p => Fin.cases p.1 (interiorEquiv n p.2)
      invFun := fun f => (f 0, (interiorEquiv n).symm (fun k => f k.succ))
      left_inv := by intro p; rcases p with ⟨i, p⟩; simp
      right_inv := by
        intro f
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · rfl
        · simp }

def edges : (A : Mat I) → (As : List (Mat I)) → I → I → Interior I As.length → List ENNReal
  | A, [], i, j, _ => [A i j]
  | A, B :: Bs, i, j, p => A i p.1 :: edges B Bs p.1 j p.2

def weight (A : Mat I) (As : List (Mat I)) (i j : I) (p : Interior I As.length) : ENNReal :=
  (edges A As i j p).prod

def AllPositive (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : Prop := ∀ a ∈ edges A As i j p, 0 < a

def HasZero (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : Prop := 0 ∈ edges A As i j p

theorem edges_length (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : (edges A As i j p).length = As.length + 1 := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simpa [edges] using congrArg Nat.succ (ih B p.1 p.2)

theorem weight_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : weight A As i j p = 0 ↔ HasZero A As i j p := by
  simp [weight, HasZero, List.prod_eq_zero_iff]

theorem weight_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : 0 < weight A As i j p ↔ AllPositive A As i j p := by
  simp [weight, AllPositive, pos_iff_ne_zero, List.prod_eq_zero_iff]
  constructor
  · intro h a ha haz
    exact h (haz ▸ ha)
  · intro h hz
    exact h 0 hz rfl

theorem product_expansion (A : Mat I) (As : List (Mat I)) (i j : I) :
    mprod (A :: As) i j = ∑ p : Interior I As.length, weight A As i j p := by
  induction As generalizing A i with
  | nil => simp [weight, edges, Interior]
  | cons B Bs ih =>
    change (∑ k, mprod (B :: Bs) k j * A i k) =
      ∑ p : I × Interior I Bs.length, A i p.1 * weight B Bs p.1 j p.2
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih B k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    exact mul_comm _ _

theorem product_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    mprod (A :: As) i j = 0 ↔ ∀ p : Interior I As.length, HasZero A As i j p := by
  rw [product_expansion, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, weight_zero_iff]

theorem product_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    0 < mprod (A :: As) i j ↔ ∃ p : Interior I As.length, AllPositive A As i j p := by
  rw [product_expansion, Finset.sum_pos_iff]
  simp only [Finset.mem_univ, true_and, weight_positive_iff]

theorem one_step_paths (A : Mat I) (i j : I) :
    (∀ p : Interior I 0, HasZero A [] i j p) ↔ A i j = 0 := by
  simp [Interior, HasZero, edges, eq_comm]

theorem one_step_positive (A : Mat I) (i j : I) :
    (∃ p : Interior I 0, AllPositive A [] i j p) ↔ 0 < A i j := by
  simp [Interior, AllPositive, edges]

theorem local_path_criteria (d : I → X → X → ENNReal)
    (fs : List (Operator X bot)) (A B : Mat I) (As Bs : List (Mat I)) (U : Set X)
    (_hlenL : fs.length = (A :: As).length) (_hlenK : fs.length = (B :: Bs).length)
    (_hU : U ⊆ dom (chain fs))
    (_hL : OnSteps (fun φ V M => M ∈ Lip d φ V) U (fs.zip (A :: As)))
    (_hK : OnSteps (fun φ V M => M ∈ CoLip d φ V) U (fs.zip (B :: Bs))) (i j : I) :
    (mprod (A :: As) i j = 0 ↔ ∀ p : Interior I As.length, HasZero A As i j p) ∧
    (0 < mprod (B :: Bs) i j ↔ ∃ p : Interior I Bs.length, AllPositive B Bs i j p) :=
  ⟨product_zero_iff A As i j, product_positive_iff B Bs i j⟩

end
end HCH02
