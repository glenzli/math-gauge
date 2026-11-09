import Chains

noncomputable section
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
open formal_oet.vol_01.ch_01_foundations
namespace HCH02
variable {I : Type} [Fintype I]

/- A :: As is in application order. The path contains exactly the
   As.length intermediate indices; its endpoints are the parameters i,j. -/
abbrev Path (I : Type) (n : ℕ) := Fin n → I

def weight (A : Mat I) : (As : List (Mat I)) → I → I → Path I As.length → ENNReal
  | [], i, j, _ => A i j
  | B :: Bs, i, j, p => weight B Bs (p 0) j (fun k => p k.succ) * A i (p 0)

def AllPositive (A : Mat I) : (As : List (Mat I)) → I → I → Path I As.length → Prop
  | [], i, j, _ => 0 < A i j
  | B :: Bs, i, j, p => 0 < A i (p 0) ∧ AllPositive B Bs (p 0) j (fun k => p k.succ)

def HasZero (A : Mat I) : (As : List (Mat I)) → I → I → Path I As.length → Prop
  | [], i, j, _ => A i j = 0
  | B :: Bs, i, j, p => A i (p 0) = 0 ∨ HasZero B Bs (p 0) j (fun k => p k.succ)

def emptyPath : Path I 0 := Fin.elim0

theorem emptyPath_unique (p : Path I 0) : p = emptyPath := by
  funext k
  exact Fin.elim0 k

theorem weight_singleton (A : Mat I) (i j : I) (p : Path I 0) :
    weight A [] i j p = A i j := rfl

theorem weight_zero (A : Mat I) (As : List (Mat I)) (i j : I) (p : Path I As.length) :
    weight A As i j p = 0 ↔ HasZero A As i j p := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simp only [weight, HasZero, mul_eq_zero, ih, or_comm]

theorem weight_positive (A : Mat I) (As : List (Mat I)) (i j : I) (p : Path I As.length) :
    0 < weight A As i j p ↔ AllPositive A As i j p := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simp only [weight, AllPositive, ENNReal.mul_pos_iff, ih, and_comm]

theorem product_expansion (A : Mat I) (As : List (Mat I)) (i j : I) :
    product (A :: As) i j = ∑ p : Path I As.length, weight A As i j p := by
  induction As generalizing A i with
  | nil => simp [weight, Path]
  | cons B Bs ih =>
    change (∑ k, product (B :: Bs) k j * A i k) = _
    simp_rw [ih, Finset.sum_mul]
    rw [← Fintype.sum_prod_type
      (fun q : I × Path I Bs.length => weight B Bs q.1 j q.2 * A i q.1)]
    exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (Bs.length + 1) => I))
      _ _ (fun _ => rfl)

theorem product_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    product (A :: As) i j = 0 ↔ ∀ p : Path I As.length, HasZero A As i j p := by
  rw [product_expansion]
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const, weight_zero]

theorem product_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    0 < product (A :: As) i j ↔ ∃ p : Path I As.length, AllPositive A As i j p := by
  rw [product_expansion]
  simp only [Finset.sum_pos_iff, Finset.mem_univ, true_and, weight_positive]

theorem singleton_criteria (A : Mat I) (i j : I) :
    ((∀ p : Path I 0, HasZero A [] i j p) ↔ A i j = 0) ∧
    ((∃ p : Path I 0, AllPositive A [] i j p) ↔ 0 < A i j) := by
  simp [HasZero, AllPositive, Path]

/- These specializations retain the original actual-domain certificate
   hypotheses. The algebraic lemmas above need no metric assumptions. -/
theorem lip_chain_zero_iff {X : Type} {bot : X} {d : I → X → X → ENNReal}
    (p : Step X I bot) (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run (p :: ps)))
    (hs : AllSteps (fun φ M V => M ∈ Lip d φ V) (p :: ps) U) (i j : I) :
    product (matrices (p :: ps)) ∈ Lip d (run (p :: ps)) U ∧
    (product (matrices (p :: ps)) i j = 0 ↔
      ∀ q : Path I (matrices ps).length, HasZero p.2 (matrices ps) i j q) :=
  ⟨chain_lip (p :: ps) hU hs, product_zero_iff p.2 (matrices ps) i j⟩

theorem colip_chain_positive_iff {X : Type} {bot : X} {d : I → X → X → ENNReal}
    (p : Step X I bot) (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run (p :: ps)))
    (hs : AllSteps (fun φ M V => M ∈ CoLip d φ V) (p :: ps) U) (i j : I) :
    product (matrices (p :: ps)) ∈ CoLip d (run (p :: ps)) U ∧
    (0 < product (matrices (p :: ps)) i j ↔
      ∃ q : Path I (matrices ps).length, AllPositive p.2 (matrices ps) i j q) :=
  ⟨chain_colip (p :: ps) (by simp) hU hs,
    product_positive_iff p.2 (matrices ps) i j⟩

end HCH02
