import Mathlib
import Core

open scoped Pointwise
open Classical

namespace MathGauge.F106

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- 由子群 `H` 诱导的阿贝尔群 `G` 上的同余等价关系：`x ~ y ↔ x - y ∈ H`。 -/
def cosetSetoid (H : AddSubgroup G) : Setoid G where
  r x y := x - y ∈ H
  iseqv := {
    refl := fun x => by
      rw [sub_self]
      exact H.zero_mem
    symm := fun {x y} h => by
      rw [← neg_sub]
      exact H.neg_mem h
    trans := fun {x y z} h1 h2 => by
      rw [← sub_add_sub_cancel x y z]
      exact H.add_mem h1 h2
  }

/-- 在每个与 `A` 相交的陪集中选取一个属于 `A` 的代表元。若未相交则默认返回 `0`。 -/
noncomputable def rep (A : Finset G) (H : AddSubgroup G) (c : Quot (cosetSetoid H).r) : G :=
  if h : ∃ a ∈ A, Quot.mk (cosetSetoid H).r a = c then
    Classical.choose h
  else 0

/-- 构造的有限覆盖集 `F ⊆ A`：所有相交陪集在 `A` 中代表元的有限集合。 -/
noncomputable def coveringSet (A : Finset G) (H : AddSubgroup G) : Finset G :=
  (A.image (Quot.mk (cosetSetoid H).r)).image (rep A H)

/-- 代表元选取的性质：对于相交陪集 `c`，代表元确实属于 `A` 且其商类就是 `c`。 -/
lemma rep_spec (A : Finset G) (H : AddSubgroup G) {c : Quot (cosetSetoid H).r}
    (hc : c ∈ A.image (Quot.mk (cosetSetoid H).r)) :
    rep A H c ∈ A ∧ Quot.mk (cosetSetoid H).r (rep A H c) = c := by
  have h : ∃ a ∈ A, Quot.mk (cosetSetoid H).r a = c := by
    rcases Finset.mem_image.mp hc with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  have hrep : rep A H c = Classical.choose h := by
    unfold rep
    exact dif_pos h
  rw [hrep]
  exact Classical.choose_spec h

/-- 结论 1：构造的集合满足 `F ⊆ A`。 -/
theorem coveringSet_subset (A : Finset G) (H : AddSubgroup G) :
    coveringSet A H ⊆ A := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨c, hc, rfl⟩
  exact (rep_spec A H hc).1

/-- 结论 2：构造的集合满足覆盖性 `Covers A H F`，即 `∀ a ∈ A, ∃ t ∈ F, a - t ∈ H`。 -/
theorem coveringSet_covers (A : Finset G) (H : AddSubgroup G) :
    Covers A H (coveringSet A H) := by
  intro a ha
  have hc : Quot.mk (cosetSetoid H).r a ∈ A.image (Quot.mk (cosetSetoid H).r) :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hspec := rep_spec A H hc
  refine ⟨rep A H (Quot.mk (cosetSetoid H).r a), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨Quot.mk (cosetSetoid H).r a, hc, rfl⟩
  · have h_eq : Quot.mk (cosetSetoid H).r a = Quot.mk (cosetSetoid H).r (rep A H (Quot.mk (cosetSetoid H).r a)) :=
      hspec.2.symm
    haveI : Setoid G := cosetSetoid H
    exact Quotient.exact h_eq

/-- 性质：`F` 中不同元素属于不同陪集（若差在 `H` 中则必相等）。 -/
lemma coveringSet_sub_mem {A : Finset G} {H : AddSubgroup G} {t₁ t₂ : G}
    (ht₁ : t₁ ∈ coveringSet A H) (ht₂ : t₂ ∈ coveringSet A H)
    (h : t₁ - t₂ ∈ H) : t₁ = t₂ := by
  rcases Finset.mem_image.mp ht₁ with ⟨c₁, hc₁, rfl⟩
  rcases Finset.mem_image.mp ht₂ with ⟨c₂, hc₂, rfl⟩
  have hspec₁ := rep_spec A H hc₁
  have hspec₂ := rep_spec A H hc₂
  have h_sound : Quot.mk (cosetSetoid H).r (rep A H c₁) = Quot.mk (cosetSetoid H).r (rep A H c₂) :=
    Quot.sound h
  rw [hspec₁.2, hspec₂.2] at h_sound
  rw [h_sound]

/-- 结论 3：基数不等式 `|F| ≤ K * |A| / |B|`。 -/
theorem coveringSet_card_le (A : Finset G) (H : AddSubgroup G) (x : G) (K : ℝ)
    (hB : (cosetSlice A H x).Nonempty)
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ((coveringSet A H).card : ℝ) ≤ K * (A.card : ℝ) / ((cosetSlice A H x).card : ℝ) := by
  let F := coveringSet A H
  let B := cosetSlice A H x
  have h_sub : (Finset.product F B).image (fun p : G × G => p.1 + p.2) ⊆ A + A := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have htA : p.1 ∈ A := coveringSet_subset A H hp1
    have hbA : p.2 ∈ A := slice_subset A H x hp2
    exact Finset.add_mem_add htA hbA
  have h_inj : Set.InjOn (fun p : G × G => p.1 + p.2) ↑(Finset.product F B) := by
    intro p1 hp1 p2 hp2 hsum
    rw [Finset.mem_coe, Finset.mem_product] at hp1 hp2
    rcases hp1 with ⟨ht1, hb1⟩
    rcases hp2 with ⟨ht2, hb2⟩
    have hb1H : p1.2 - x ∈ H := (mem_cosetSlice A H x p1.2).mp hb1 |>.2
    have hb2H : p2.2 - x ∈ H := (mem_cosetSlice A H x p2.2).mp hb2 |>.2
    have hdiff : (p2.2 - x) - (p1.2 - x) ∈ H := H.sub_mem hb2H hb1H
    have h_sub_eq : p1.1 - p2.1 = (p2.2 - x) - (p1.2 - x) := by
      calc p1.1 - p2.1 = (p1.1 + p1.2) - p1.2 - p2.1 := by abel
      _ = (p2.1 + p2.2) - p1.2 - p2.1 := by rw [hsum]
      _ = (p2.2 - x) - (p1.2 - x) := by abel
    have ht_sub_H : p1.1 - p2.1 ∈ H := by
      rw [h_sub_eq]
      exact hdiff
    have ht_eq : p1.1 = p2.1 := coveringSet_sub_mem ht1 ht2 ht_sub_H
    have hb_eq : p1.2 = p2.2 := by
      apply add_left_cancel (a := p1.1)
      rw [hsum, ht_eq]
    exact Prod.ext ht_eq hb_eq
  have h_card_image : ((Finset.product F B).image (fun p => p.1 + p.2)).card = (Finset.product F B).card :=
    Finset.card_image_of_injOn h_inj
  have h_card_prod : (Finset.product F B).card = F.card * B.card :=
    Finset.card_product F B
  have h_le_card : ((Finset.product F B).image (fun p => p.1 + p.2)).card ≤ (A + A).card :=
    Finset.card_le_card h_sub
  have h_card_le : F.card * B.card ≤ (A + A).card := by
    rw [← h_card_prod, ← h_card_image]
    exact h_le_card
  have h1 : ((F.card * B.card : ℕ) : ℝ) ≤ ((A + A).card : ℝ) := Nat.cast_le.mpr h_card_le
  rw [Nat.cast_mul] at h1
  have h2 : (F.card : ℝ) * (B.card : ℝ) ≤ K * (A.card : ℝ) := h1.trans hK
  have hB_pos_nat : 0 < B.card := Finset.card_pos.mpr hB
  have hB_pos : 0 < (B.card : ℝ) := Nat.cast_pos.mpr hB_pos_nat
  have hB_ne : (B.card : ℝ) ≠ 0 := ne_of_gt hB_pos
  have hB_inv_nonneg : 0 ≤ (B.card : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hB_pos)
  have h3 : (F.card : ℝ) * (B.card : ℝ) * (B.card : ℝ)⁻¹ ≤ K * (A.card : ℝ) * (B.card : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right h2 hB_inv_nonneg
  rw [mul_assoc, mul_inv_cancel₀ hB_ne, mul_one] at h3
  rw [← div_eq_mul_inv] at h3
  exact h3

/-- 最终主定理（`Finset.Nonempty` 形式前提）：
存在有限子集 `F ⊆ A`，满足覆盖条件 `Covers A H F` 且 `|F| ≤ K * |A| / |B|`。 -/
theorem exists_covering (A : Finset G) (H : AddSubgroup G) (x : G) (K : ℝ)
    (hB : (cosetSlice A H x).Nonempty)
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ∃ F : Finset G, F ⊆ A ∧ ((F.card : ℝ) ≤ K * (A.card : ℝ) / ((cosetSlice A H x).card : ℝ)) ∧ Covers A H F :=
  ⟨coveringSet A H, coveringSet_subset A H, coveringSet_card_le A H x K hB hK, coveringSet_covers A H⟩

/-- 最终主定理（`≠ ∅` 形式前提）：
与上一定理等价，可直接使用 `cosetSlice A H x ≠ ∅` 作为非空前提。 -/
theorem exists_covering_of_ne_empty (A : Finset G) (H : AddSubgroup G) (x : G) (K : ℝ)
    (hB : cosetSlice A H x ≠ ∅)
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ∃ F : Finset G, F ⊆ A ∧ ((F.card : ℝ) ≤ K * (A.card : ℝ) / ((cosetSlice A H x).card : ℝ)) ∧ Covers A H F :=
  exists_covering A H x K (Finset.nonempty_iff_ne_empty.mpr hB) hK

end MathGauge.F106
