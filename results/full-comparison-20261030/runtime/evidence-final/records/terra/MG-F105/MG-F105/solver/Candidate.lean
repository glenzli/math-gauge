import Bridge

open scoped Pointwise
namespace MathGauge.F105
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem dense_coset_cover (A : Finset G) (H : AddSubgroup G) (x : G) (K : ℝ)
    (hB : (cosetSlice A H x).Nonempty)
    (hK : ((A + A).card : ℝ) ≤ K * A.card) :
    ∃ F : Finset G, F ⊆ A ∧
      (F.card : ℝ) ≤ K * A.card / (cosetSlice A H x).card ∧ Covers A H F := by
  have hpos : (0 : ℝ) < (cosetSlice A H x).card := by
    exact_mod_cast Finset.card_pos.mpr hB
  have hsum : ((A + cosetSlice A H x).card : ℝ) ≤ K * A.card := by
    apply le_trans _ hK
    exact_mod_cast Finset.card_le_card (Finset.add_subset_add (Finset.Subset.refl A)
      (slice_subset A H x))
  have hbound : ((A + cosetSlice A H x).card : ℝ) ≤
      (K * A.card / (cosetSlice A H x).card) * (cosetSlice A H x).card := by
    simpa only [div_mul_cancel₀ _ (ne_of_gt hpos)] using hsum
  obtain ⟨F, hFA, hcard, hcov⟩ := Finset.ruzsa_covering_add hB hbound
  exact ⟨F, hFA, hcard, lift_cover A F H x hcov⟩

#print axioms dense_coset_cover
end MathGauge.F105
