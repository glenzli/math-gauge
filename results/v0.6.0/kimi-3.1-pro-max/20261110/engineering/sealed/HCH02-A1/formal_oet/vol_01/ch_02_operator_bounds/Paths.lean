import formal_oet.vol_01.ch_02_operator_bounds.Chains

namespace formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

namespace IndexPath

/-- Every path in this representation has positive edge length. -/
theorem length_pos {I : Type} {n : ℕ} {i j : I} (p : IndexPath I n i j) : 0 < n := by
  cases p <;> omega

/-- HC02-D06.  The intermediate list has exactly `n - 1` entries. -/
theorem intermediate_length {I : Type} {n : ℕ} {i j : I} (p : IndexPath I n i j) :
    p.intermediate.length = n - 1 := by
  induction p with
  | single => rfl
  | @snoc n i k p j ih =>
      have hn := length_pos p
      simp only [IndexPath.intermediate, List.length_append, List.length_singleton, ih]
      omega

/-- At length one, the only path is the empty-intermediate-sequence path. -/
theorem eq_single {I : Type} {i j : I} (p : IndexPath I 1 i j) :
    p = IndexPath.single i j := by
  cases p with
  | single => rfl
  | snoc p j => cases p

/-- HC02-D06.  The product weight vanishes exactly when the path has a zero edge. -/
theorem weight_eq_zero_iff {I : Type} (A : ℕ → BoundMatrix I) {n : ℕ} {i j : I}
    (p : IndexPath I n i j) : p.weight A = 0 ↔ p.HasZero A := by
  induction p with
  | single => rfl
  | snoc p j ih => simp [IndexPath.weight, IndexPath.HasZero, ih, mul_eq_zero]

/-- HC02-D06.  The product weight is positive exactly when every edge is positive. -/
theorem weight_pos_iff {I : Type} (A : ℕ → BoundMatrix I) {n : ℕ} {i j : I}
    (p : IndexPath I n i j) : 0 < p.weight A ↔ p.AllPositive A := by
  induction p with
  | single => rfl
  | snoc p j ih => simp [IndexPath.weight, IndexPath.AllPositive, ih, ENNReal.mul_pos_iff]

/-- Having a zero edge is the negation of being an all-positive path. -/
theorem hasZero_iff_not_allPositive {I : Type} (A : ℕ → BoundMatrix I) {n : ℕ} {i j : I}
    (p : IndexPath I n i j) : p.HasZero A ↔ ¬ p.AllPositive A := by
  rw [← weight_eq_zero_iff, ← weight_pos_iff]
  simp [pos_iff_ne_zero]

end IndexPath

/-- A positive ordered-product entry supplies a complete all-positive path. -/
theorem exists_allPositive_path_of_orderedProduct_pos {I : Type} [Fintype I]
    (A : ℕ → BoundMatrix I) (n : ℕ) (i j : I)
    (h : 0 < orderedProduct A (n + 1) i j) :
    ∃ p : IndexPath I (n + 1) i j, p.AllPositive A := by
  induction n generalizing i j with
  | zero =>
      exact ⟨IndexPath.single i j, by simpa using h⟩
  | succ n ih =>
      change 0 < ∑ k : I, A (n + 1) k j * orderedProduct A (n + 1) i k at h
      have hex : ∃ k : I, 0 < A (n + 1) k j * orderedProduct A (n + 1) i k := by
        simpa using (Finset.sum_pos_iff.mp h)
      obtain ⟨k, hk⟩ := hex
      have hparts := ENNReal.mul_pos_iff.mp hk
      obtain ⟨p, hp⟩ := ih i k hparts.2
      exact ⟨IndexPath.snoc p j, hp, hparts.1⟩

/-- Every all-positive path forces the corresponding ordered-product entry
to be positive. -/
theorem orderedProduct_pos_of_allPositive_path {I : Type} [Fintype I]
    (A : ℕ → BoundMatrix I) {n : ℕ} {i j : I}
    (p : IndexPath I n i j) (hp : p.AllPositive A) :
    0 < orderedProduct A n i j := by
  induction p with
  | single i j => simpa using hp
  | @snoc n i k p j ih =>
      change 0 < ∑ l : I, A n l j * orderedProduct A n i l
      apply Finset.sum_pos_iff.mpr
      refine ⟨k, Finset.mem_univ k, ?_⟩
      exact ENNReal.mul_pos_iff.mpr ⟨hp.2, ih hp.1⟩

/-- HC02-P17, algebraic form.  Positivity of an ordered-product entry is
equivalent to existence of one all-positive complete path. -/
theorem orderedProduct_pos_iff {I : Type} [Fintype I]
    (A : ℕ → BoundMatrix I) (n : ℕ) (i j : I) :
    0 < orderedProduct A (n + 1) i j ↔
      ∃ p : IndexPath I (n + 1) i j, p.AllPositive A := by
  constructor
  · exact exists_allPositive_path_of_orderedProduct_pos A n i j
  · rintro ⟨p, hp⟩
    exact orderedProduct_pos_of_allPositive_path A p hp

/-- HC02-P16, algebraic form.  Vanishing is equivalent to every complete
path containing at least one zero edge. -/
theorem orderedProduct_zero_iff {I : Type} [Fintype I]
    (A : ℕ → BoundMatrix I) (n : ℕ) (i j : I) :
    orderedProduct A (n + 1) i j = 0 ↔
      ∀ p : IndexPath I (n + 1) i j, p.HasZero A := by
  constructor
  · intro h p
    apply (IndexPath.hasZero_iff_not_allPositive A p).mpr
    intro hp
    have hpos := (orderedProduct_pos_iff A n i j).mpr ⟨p, hp⟩
    rw [h] at hpos
    exact (lt_irrefl 0) hpos
  · intro h
    by_contra hne
    obtain ⟨p, hp⟩ := (orderedProduct_pos_iff A n i j).mp (pos_iff_ne_zero.mpr hne)
    have hz := h p
    exact (IndexPath.hasZero_iff_not_allPositive A p).mp hz hp

/-- The `n = 1` zero criterion is the unique matrix entry itself. -/
theorem orderedProduct_one_zero_iff {I : Type} [Fintype I]
    (A : ℕ → BoundMatrix I) (i j : I) :
    A 0 i j = 0 ↔ ∀ p : IndexPath I 1 i j, p.HasZero A := by
  simpa using orderedProduct_zero_iff A 0 i j

/-- The `n = 1` positive criterion is the unique matrix entry itself. -/
theorem orderedProduct_one_pos_iff {I : Type} [Fintype I]
    (A : ℕ → BoundMatrix I) (i j : I) :
    0 < A 0 i j ↔ ∃ p : IndexPath I 1 i j, p.AllPositive A := by
  simpa using orderedProduct_pos_iff A 0 i j

/-- HC02-P16.  The zero-entry criterion in the same nonempty Lip-chain
context as the text. -/
theorem lip_chain_product_zero_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (L : ℕ → BoundMatrix I) (n : ℕ)
    (_hdom : U ⊆ dom (operatorChain ϕ (n + 1)))
    (_hvalid : LipChainValid d U ϕ L (n + 1)) (i j : I) :
    orderedProduct L (n + 1) i j = 0 ↔
      ∀ p : IndexPath I (n + 1) i j, p.HasZero L := by
  exact orderedProduct_zero_iff L n i j

/-- HC02-P17.  The positive-entry criterion in the same nonempty co-Lip-chain
context as the text. -/
theorem coLip_chain_product_pos_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (K : ℕ → BoundMatrix I) (n : ℕ)
    (_hdom : U ⊆ dom (operatorChain ϕ (n + 1)))
    (_hvalid : CoLipChainValid d U ϕ K (n + 1)) (i j : I) :
    0 < orderedProduct K (n + 1) i j ↔
      ∃ p : IndexPath I (n + 1) i j, p.AllPositive K := by
  exact orderedProduct_pos_iff K n i j

end formal_oet.vol_01.ch_02_operator_bounds
