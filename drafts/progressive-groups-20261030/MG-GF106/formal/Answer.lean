import Reference
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped Pointwise
namespace MathGauge.F106
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



theorem slice_mono_subgroup (A : Finset G) (H L : AddSubgroup G) (x : G) (hHL : H ≤ L) :
    cosetSlice A H x ⊆ cosetSlice A L x := by
  intro a ha
  obtain ⟨ha,hh⟩ := (mem_cosetSlice A H x a).mp ha
  exact (mem_cosetSlice A L x a).mpr ⟨ha,hHL hh⟩

theorem enlarge_subgroup_reselect (A F : Finset G) (H L : AddSubgroup G) (x : G) (K : ℝ)
    (hHL : H ≤ L) (hFA : F ⊆ A) (hF : Covers A H F)
    (hB : (cosetSlice A H x).Nonempty) (hK : ((A + A).card : ℝ) ≤ K * A.card) :
    ∃ E : Finset G, E ⊆ F ∧ E ⊆ A ∧ Covers A L E ∧
      E.card = cosetCount A L ∧ (E.card : ℝ) ≤ K * A.card / (cosetSlice A L x).card := by
  classical
  have hLF : Covers A L F := by
    intro a ha; obtain ⟨t,ht,hat⟩ := hF a ha; exact ⟨t,ht,hHL hat⟩
  obtain ⟨E,hEF,hE,hcard⟩ := exists_minimal_cover F L
  have hecov : Covers A L E := by
    intro a ha
    obtain ⟨t,ht,hat⟩ := hLF a ha
    obtain ⟨u,hu,htu⟩ := hE t ht
    refine ⟨u,hu,?_⟩
    convert L.add_mem hat htu using 1 <;> abel
  have hc : E.card = cosetCount A L := by
    rw [hcard]
    unfold cosetCount
    rw [(covers_iff_image A F L hFA).mp hLF]
  refine ⟨E,hEF,Finset.Subset.trans hEF hFA,hecov,hc,?_⟩
  rw [hc]
  exact cosetCount_bound A L x K (hB.mono (slice_mono_subgroup A H L x hHL)) hK

theorem cosetCount_bot (A : Finset G) : cosetCount A (⊥ : AddSubgroup G) = A.card := by
  classical
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have : a - b ∈ (⊥ : AddSubgroup G) := (quotient_eq_iff ⊥ a b).mp hab
  exact sub_eq_zero.mp this

def densityExample : Finset ℤ := {0,1,2}

theorem density_example_sum : densityExample + densityExample = {0,1,2,3,4} := by
  ext z
  simp only [densityExample, Finset.mem_add, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, (rfl | rfl | rfl), b, (rfl | rfl | rfl), rfl⟩ <;> norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0,by simp,0,by simp,by norm_num⟩
    · exact ⟨0,by simp,1,by simp,by norm_num⟩
    · exact ⟨0,by simp,2,by simp,by norm_num⟩
    · exact ⟨1,by simp,2,by simp,by norm_num⟩
    · exact ⟨2,by simp,2,by simp,by norm_num⟩

theorem density_factor_counterexample :
    ((densityExample + densityExample).card : ℝ) ≤ (5 / 3 : ℝ) * densityExample.card ∧
    (cosetSlice densityExample (⊥ : AddSubgroup ℤ) 0).Nonempty ∧
    (5 / 3 : ℝ) < cosetCount densityExample (⊥ : AddSubgroup ℤ) := by
  rw [density_example_sum, cosetCount_bot]
  norm_num [densityExample, cosetSlice]
  exact ⟨0, by simp⟩

theorem singleton_slices_bot (A : Finset G) {x : G} (hx : x ∈ A) :
    cosetSlice A (⊥ : AddSubgroup G) x = {x} := by
  ext a
  simp only [mem_cosetSlice, AddSubgroup.mem_bot, sub_eq_zero, Finset.mem_singleton]
  exact ⟨And.right, fun h => ⟨h ▸ hx,h⟩⟩

theorem sum_slice_bounds {ι : Type*} (J : Finset ι) (b : ι → ℝ) (c K a : ℝ)
    (hsum : ∑ j ∈ J, b j = a) (hc : (J.card : ℝ) = c)
    (h : ∀ j ∈ J, c * b j ≤ K * a) : c * a ≤ c * K * a := by
  have hh := Finset.sum_le_sum h
  simpa only [← Finset.mul_sum, hsum, Finset.sum_const, nsmul_eq_mul, hc, mul_assoc, mul_left_comm] using hh

end MathGauge.F106
