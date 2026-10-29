import Candidate
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped Pointwise
namespace MathGauge.F105
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem quotient_eq_iff (H : AddSubgroup G) (a t : G) :
    (QuotientAddGroup.mk a : G ⧸ H) = QuotientAddGroup.mk t ↔ a - t ∈ H := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h; convert H.neg_mem h using 1 <;> abel
  · intro h; convert H.neg_mem h using 1 <;> abel

noncomputable def cosetCount (A : Finset G) (H : AddSubgroup G) : ℕ := by
  classical
  exact (A.image (fun a => (QuotientAddGroup.mk a : G ⧸ H))).card

theorem covers_iff_image (A F : Finset G) (H : AddSubgroup G) (hFA : F ⊆ A) :
    Covers A H F ↔ F.image (fun a => (QuotientAddGroup.mk a : G ⧸ H)) =
      A.image (fun a => (QuotientAddGroup.mk a : G ⧸ H)) := by
  classical
  constructor
  · intro h
    apply Finset.Subset.antisymm (Finset.image_subset_image hFA)
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨t,ht,hat⟩ := h a ha
    exact Finset.mem_image.mpr ⟨t, ht, ((quotient_eq_iff H a t).mpr hat).symm⟩
  · intro h a ha
    have hz : (QuotientAddGroup.mk a : G ⧸ H) ∈ F.image (fun a => (QuotientAddGroup.mk a : G ⧸ H)) := by
      rw [h]; exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    obtain ⟨t,ht,heq⟩ := Finset.mem_image.mp hz
    exact ⟨t,ht,(quotient_eq_iff H a t).mp heq.symm⟩

theorem select_image_representatives {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    ∃ F : Finset α, F ⊆ A ∧ F.image f = A.image f ∧ Set.InjOn f F := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert a A ha ih =>
    obtain ⟨F,hF,himg,hinj⟩ := ih
    by_cases hfa : f a ∈ F.image f
    · refine ⟨F, fun x hx => Finset.mem_insert_of_mem (hF hx), ?_, hinj⟩
      rw [Finset.image_insert, ← himg, Finset.insert_eq_of_mem hfa]
    · refine ⟨insert a F, Finset.insert_subset_insert _ hF, ?_, ?_⟩
      · simp [himg]
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · rfl
          · exact False.elim (hfa (Finset.mem_image.mpr ⟨y,hy,hxy.symm⟩))
        · rcases hy with rfl | hy
          · exact False.elim (hfa (Finset.mem_image.mpr ⟨x,hx,hxy⟩))
          · exact hinj hx hy hxy

theorem cosetCount_le_cover (A F : Finset G) (H : AddSubgroup G)
    (hFA : F ⊆ A) (hc : Covers A H F) : cosetCount A H ≤ F.card := by
  classical
  unfold cosetCount
  rw [← (covers_iff_image A F H hFA).mp hc]
  exact Finset.card_image_le

theorem exists_minimal_cover (A : Finset G) (H : AddSubgroup G) :
    ∃ F : Finset G, F ⊆ A ∧ Covers A H F ∧ F.card = cosetCount A H := by
  classical
  obtain ⟨F,hF,himg,hinj⟩ := select_image_representatives A (fun a => (QuotientAddGroup.mk a : G ⧸ H))
  refine ⟨F,hF,(covers_iff_image A F H hF).mpr himg,?_⟩
  unfold cosetCount
  rw [← himg, Finset.card_image_of_injOn hinj]

theorem cosetCount_bound (A : Finset G) (H : AddSubgroup G) (x : G) (K : ℝ)
    (hB : (cosetSlice A H x).Nonempty)
    (hK : ((A + A).card : ℝ) ≤ K * A.card) :
    (cosetCount A H : ℝ) ≤ K * A.card / (cosetSlice A H x).card := by
  obtain ⟨F,hF,hcard,hcov⟩ := dense_coset_cover A H x K hB hK
  exact le_trans (by exact_mod_cast cosetCount_le_cover A F H hF hcov) hcard

theorem representative_sum_injective (A F : Finset G) (H : AddSubgroup G) (x : G)
    (hrep : ∀ a ∈ F, ∀ t ∈ F, a - t ∈ H → a = t) :
    Set.InjOn (fun p : G × G => p.1 + p.2) (F ×ˢ cosetSlice A H x) := by
  intro p hp q hq heq
  obtain ⟨hpF,hpB⟩ := hp
  obtain ⟨hqF,hqB⟩ := hq
  have hdiff : p.1 - q.1 ∈ H := by
    have h := slice_difference A H x hqB hpB
    have he : p.1 - q.1 = q.2 - p.2 := by
      have : p.1 + p.2 = q.1 + q.2 := heq
      calc
        p.1 - q.1 = (p.1 + p.2) - (q.1 + p.2) := by abel
        _ = (q.1 + q.2) - (q.1 + p.2) := by rw [this]
        _ = q.2 - p.2 := by abel
    rwa [he]
  have hfirst := hrep p.1 hpF q.1 hqF hdiff
  apply Prod.ext hfirst
  change p.1 + p.2 = q.1 + q.2 at heq
  rw [hfirst] at heq
  exact add_left_cancel heq

theorem representative_product_bound (A F : Finset G) (H : AddSubgroup G) (x : G)
    (hFA : F ⊆ A) (hrep : ∀ a ∈ F, ∀ t ∈ F, a - t ∈ H → a = t) :
    F.card * (cosetSlice A H x).card ≤ (A + cosetSlice A H x).card := by
  have hcard : (F + cosetSlice A H x).card = F.card * (cosetSlice A H x).card :=
    Finset.card_add_iff.mpr (representative_sum_injective A F H x hrep)
  rw [← hcard]
  exact Finset.card_le_card (Finset.add_subset_add hFA (Finset.Subset.refl _))

theorem representative_translates_disjoint (A F : Finset G) (H : AddSubgroup G) (x : G)
    (hrep : ∀ a ∈ F, ∀ t ∈ F, a - t ∈ H → a = t) :
    (F : Set G).PairwiseDisjoint (fun t => t +ᵥ cosetSlice A H x) := by
  exact Finset.pairwiseDisjoint_vadd_iff.mpr (representative_sum_injective A F H x hrep)



/-- Maximality is in the finite powerset of A, not an assumed choice certificate. -/
theorem ruzsa_maximal_cover (A B : Finset G) (hB : B.Nonempty) :
    ∃ F : Finset G, F ⊆ A ∧
      (F : Set G).PairwiseDisjoint (fun t => t +ᵥ B) ∧
      (∀ E : Finset G, F ⊆ E → E ⊆ A →
        (E : Set G).PairwiseDisjoint (fun t => t +ᵥ B) → E = F) ∧
      A ⊆ F + (B - B) ∧ F.card * B.card ≤ (A + B).card := by
  classical
  let C := A.powerset.filter (fun (F : Finset G) => (F : Set G).PairwiseDisjoint (fun t => t +ᵥ B))
  obtain ⟨F,hmax⟩ := C.exists_maximal (Finset.filter_nonempty_iff.mpr
    ⟨∅, Finset.empty_mem_powerset A, by simp⟩)
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hmax
  obtain ⟨hFA,hF⟩ := hmax.1
  refine ⟨F,hFA,hF,?_,?_,?_⟩
  · intro E hFE hEA hE
    exact Finset.Subset.antisymm (hmax.2 ⟨hEA,hE⟩ hFE) hFE
  · intro a ha
    by_cases hau : a ∈ F
    · exact Finset.subset_add_left _ hB.zero_mem_sub hau
    by_cases! H : ∀ b ∈ F, Disjoint (a +ᵥ B) (b +ᵥ B)
    · refine (hmax.not_gt ?_ (Finset.ssubset_insert hau)).elim
      rw [Finset.insert_subset_iff, Finset.coe_insert]
      exact ⟨⟨ha,hFA⟩,hF.insert (fun _ hb _ => H _ hb)⟩
    simp_rw [Finset.not_disjoint_iff, ← Finset.neg_vadd_mem_iff] at H
    obtain ⟨b,hb,c,hc₁,hc₂⟩ := H
    exact Finset.mem_add.mpr ⟨b,hb,-b+a,
      Finset.mem_sub.mpr ⟨_,hc₂,_,hc₁,by simp⟩,by simp⟩
  · calc
      F.card * B.card = (F + B).card := (Finset.card_add_iff.mpr
        (Finset.pairwiseDisjoint_vadd_iff.mp hF)).symm
      _ ≤ (A + B).card := Finset.card_le_card (Finset.add_subset_add hFA (Finset.Subset.refl B))

theorem product_cover_allow_empty (A : Finset G) (H : AddSubgroup G) (x : G) (K : ℝ)
    (hK : ((A + A).card : ℝ) ≤ K * A.card) :
    ∃ F : Finset G, F ⊆ A ∧ Covers A H F ∧
      (F.card : ℝ) * (cosetSlice A H x).card ≤ K * A.card := by
  classical
  by_cases hB : (cosetSlice A H x).Nonempty
  · obtain ⟨F,hF,hcard,hcov⟩ := dense_coset_cover A H x K hB hK
    refine ⟨F,hF,hcov,?_⟩
    exact (le_div_iff₀ (by exact_mod_cast Finset.card_pos.mpr hB)).mp hcard
  · have he : cosetSlice A H x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    refine ⟨A, Finset.Subset.refl A, ?_, ?_⟩
    · intro a ha; exact ⟨a,ha,by simp⟩
    · rw [he]; simpa using (le_trans (Nat.cast_nonneg (A+A).card) hK)

def sliceExample : Finset ℤ := {0,1}

theorem slice_example_sum : sliceExample + sliceExample = {0,1,2} := by
  ext z
  simp only [sliceExample, Finset.mem_add, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a,(rfl|rfl),b,(rfl|rfl),rfl⟩ <;> norm_num
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,by simp,0,by simp,by norm_num⟩
    · exact ⟨0,by simp,1,by simp,by norm_num⟩
    · exact ⟨1,by simp,1,by simp,by norm_num⟩

theorem representatives_not_in_slice :
    ((sliceExample + sliceExample).card : ℝ) ≤ (3 / 2 : ℝ) * sliceExample.card ∧
    cosetSlice sliceExample (⊥ : AddSubgroup ℤ) 0 = {0} ∧
    ¬ ∃ F : Finset ℤ, F ⊆ cosetSlice sliceExample ⊥ 0 ∧ Covers sliceExample ⊥ F := by
  have hs : cosetSlice sliceExample (⊥ : AddSubgroup ℤ) 0 = {0} := by
    ext z; simp [cosetSlice, sliceExample]; omega
  refine ⟨?_,hs,?_⟩
  · rw [slice_example_sum]; norm_num [sliceExample]
  · rintro ⟨F,hF,hcov⟩
    obtain ⟨t,ht,hm⟩ := hcov 1 (by simp [sliceExample])
    have ht0 : t = 0 := by simpa [hs] using hF ht
    norm_num [ht0] at hm

theorem zero_denominator_quotient_fails :
    cosetSlice ({0} : Finset ℤ) ⊥ 1 = ∅ ∧
    ((({0} : Finset ℤ) + {0}).card : ℝ) ≤ 1 * ({0} : Finset ℤ).card ∧
    ¬ ∃ F : Finset ℤ, F ⊆ {0} ∧ Covers {0} ⊥ F ∧
      (F.card : ℝ) ≤ 1 * ({0} : Finset ℤ).card / (cosetSlice ({0} : Finset ℤ) ⊥ 1).card := by
  have hs : cosetSlice ({0} : Finset ℤ) ⊥ 1 = ∅ := by
    ext z; simp [cosetSlice]; omega
  refine ⟨hs,by simp,?_⟩
  rintro ⟨F,hF,hcov,hcard⟩
  have hz : F.card = 0 := by simpa [hs] using hcard
  obtain ⟨t,ht,_⟩ := hcov 0 (by simp)
  rw [Finset.card_eq_zero.mp hz] at ht
  simpa using ht

end MathGauge.F105
