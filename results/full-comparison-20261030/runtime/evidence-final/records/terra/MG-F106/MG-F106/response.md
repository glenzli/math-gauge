下面是 `Solution.lean` 的完整候选源码。`exists_coset_representatives` 构造每个陪集的唯一代表；`card_mul_slice_le_card_add` 证明 \(|F||B|\le |A+A|\)；`exists_small_coset_cover` 给出题目要求的实数基数界和覆盖性质。

当前执行工具持续返回 `code-mode host is disabled`，因此我无法实际创建文件或运行 Lean。**源码尚未经过编译验证，不能确认它已经构成可导入的文件。**

`Solution.lean`：

```lean
import Mathlib
import Core

open scoped Pointwise

namespace MathGauge.F106

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Choose an element of a nonempty finite set, with `0` as a fallback. -/
private noncomputable def pickFrom (S : Finset G) : G := by
  classical
  exact if h : S.Nonempty then Classical.choose h else 0

/-- Choose a representative from the slice of `A` containing `a`. -/
private noncomputable def chooseRep
    (A : Finset G) (H : AddSubgroup G) (a : G) : G :=
  pickFrom (cosetSlice A H a)

private theorem chooseRep_mem_slice
    (A : Finset G) (H : AddSubgroup G) {a : G} (ha : a ∈ A) :
    chooseRep A H a ∈ cosetSlice A H a := by
  classical
  have hs : (cosetSlice A H a).Nonempty := by
    refine ⟨a, (mem_cosetSlice A H a a).2 ⟨ha, ?_⟩⟩
    simpa only [sub_self] using H.zero_mem
  simpa only [chooseRep, pickFrom, dif_pos hs] using
    (Classical.choose_spec hs)

/-- Points whose difference lies in `H` define the same slice. -/
private theorem slice_eq_of_sub_mem
    (A : Finset G) (H : AddSubgroup G) {a b : G}
    (hab : a - b ∈ H) :
    cosetSlice A H a = cosetSlice A H b := by
  classical
  have hba : b - a ∈ H := by
    have he : b - a = -(a - b) := by abel
    rw [he]
    exact H.neg_mem hab
  ext z
  simp only [mem_cosetSlice]
  constructor
  · rintro ⟨hzA, hzH⟩
    refine ⟨hzA, ?_⟩
    have he : z - b = (z - a) + (a - b) := by abel
    rw [he]
    exact H.add_mem hzH hab
  · rintro ⟨hzA, hzH⟩
    refine ⟨hzA, ?_⟩
    have he : z - a = (z - b) + (b - a) := by abel
    rw [he]
    exact H.add_mem hzH hba

private theorem chooseRep_eq_of_sub_mem
    (A : Finset G) (H : AddSubgroup G) {a b : G}
    (hab : a - b ∈ H) :
    chooseRep A H a = chooseRep A H b := by
  change pickFrom (cosetSlice A H a) = pickFrom (cosetSlice A H b)
  exact congrArg pickFrom (slice_eq_of_sub_mem A H hab)

/--
There is a subset of `A` containing exactly one representative of each
coset of `H` that intersects `A`.
-/
theorem exists_coset_representatives
    (A : Finset G) (H : AddSubgroup G) :
    ∃ F : Finset G,
      F ⊆ A ∧ Covers A H F ∧
        (∀ t ∈ F, ∀ u ∈ F, t - u ∈ H → t = u) := by
  classical
  let F : Finset G := A.image (chooseRep A H)

  have hFsub : F ⊆ A := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨a, ha, rfl⟩
    exact
      ((mem_cosetSlice A H a (chooseRep A H a)).mp
        (chooseRep_mem_slice A H ha)).1

  have hfix : ∀ t ∈ F, chooseRep A H t = t := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨a, ha, rfl⟩
    apply chooseRep_eq_of_sub_mem A H
    exact
      ((mem_cosetSlice A H a (chooseRep A H a)).mp
        (chooseRep_mem_slice A H ha)).2

  refine ⟨F, hFsub, ?_, ?_⟩
  · intro a ha
    refine ⟨chooseRep A H a, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · have hr : chooseRep A H a - a ∈ H :=
        ((mem_cosetSlice A H a (chooseRep A H a)).mp
          (chooseRep_mem_slice A H ha)).2
      have he : a - chooseRep A H a = -(chooseRep A H a - a) := by
        abel
      rw [he]
      exact H.neg_mem hr
  · intro t ht u hu htu
    calc
      t = chooseRep A H t := (hfix t ht).symm
      _ = chooseRep A H u := chooseRep_eq_of_sub_mem A H htu
      _ = u := hfix u hu

/--
If `F` is a subset of `A` with at most one point in each coset of `H`,
then `F × cosetSlice A H x` injects into `A + A` by addition.
-/
theorem card_mul_slice_le_card_add
    (A : Finset G) (H : AddSubgroup G) (x : G) (F : Finset G)
    (hFsub : F ⊆ A)
    (hFuniq : ∀ t ∈ F, ∀ u ∈ F, t - u ∈ H → t = u) :
    F.card * (cosetSlice A H x).card ≤ (A + A).card := by
  classical
  let B : Finset G := cosetSlice A H x
  let P : Finset (G × G) := F ×ˢ B
  let addPair : G × G → G := fun p => p.1 + p.2

  have hinto : P.image addPair ⊆ A + A := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨⟨t, b⟩, hp, rfl⟩
    have hp' : t ∈ F ∧ b ∈ B := Finset.mem_product.mp hp
    exact Finset.mem_add.mpr
      ⟨t, hFsub hp'.1, b, slice_subset A H x hp'.2, rfl⟩

  have hinj : Set.InjOn addPair (↑P : Set (G × G)) := by
    rintro ⟨t, b⟩ hp ⟨u, c⟩ hq hsum
    have hp' : t ∈ F ∧ b ∈ B := Finset.mem_product.mp hp
    have hq' : u ∈ F ∧ c ∈ B := Finset.mem_product.mp hq
    have hbH : b - x ∈ H :=
      ((mem_cosetSlice A H x b).mp hp'.2).2
    have hcH : c - x ∈ H :=
      ((mem_cosetSlice A H x c).mp hq'.2).2
    have hsum' : t + b = u + c := hsum

    have hcb : c - b ∈ H := by
      have he : c - b = (c - x) - (b - x) := by abel
      rw [he]
      exact H.sub_mem hcH hbH

    have htu : t - u ∈ H := by
      have he : t - u = c - b := by
        calc
          t - u = (t + b) - (u + b) := by abel
          _ = (u + c) - (u + b) := by rw [hsum']
          _ = c - b := by abel
      rw [he]
      exact hcb

    have htu' : t = u := hFuniq t hp'.1 u hq'.1 htu
    have hbc : b = c := by
      have he : u + b = u + c := by
        simpa only [htu'] using hsum'
      exact add_left_cancel he
    exact Prod.ext htu' hbc

  have hcard : (P.image addPair).card = P.card :=
    Finset.card_image_iff.mpr hinj

  calc
    F.card * (cosetSlice A H x).card = P.card := by
      simp [P, B, Finset.card_product]
    _ = (P.image addPair).card := hcard.symm
    _ ≤ (A + A).card := Finset.card_le_card hinto

/--
A nonempty slice and a doubling bound yield a finite cover of `A` by
cosets of `H`, with the stated real-valued cardinality bound.
-/
theorem exists_small_coset_cover
    (A : Finset G) (H : AddSubgroup G) (x : G) (K : ℝ)
    (hB : cosetSlice A H x ≠ ∅)
    (hAA : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ∃ F : Finset G,
      F ⊆ A ∧
        (F.card : ℝ) ≤
          K * (A.card : ℝ) / ((cosetSlice A H x).card : ℝ) ∧
        Covers A H F := by
  classical
  rcases exists_coset_representatives A H with
    ⟨F, hFsub, hcover, hFuniq⟩

  have hnat :
      F.card * (cosetSlice A H x).card ≤ (A + A).card :=
    card_mul_slice_le_card_add A H x F hFsub hFuniq

  have hreal :
      (F.card : ℝ) * ((cosetSlice A H x).card : ℝ) ≤
        ((A + A).card : ℝ) := by
    exact_mod_cast hnat

  have hcardB : 0 < (cosetSlice A H x).card := by
    apply Finset.card_pos.mpr
    exact Finset.nonempty_iff_ne_empty.mpr hB

  have hcardBreal : (0 : ℝ) < ((cosetSlice A H x).card : ℝ) := by
    exact_mod_cast hcardB

  refine ⟨F, hFsub, ?_, hcover⟩
  apply (le_div_iff₀ hcardBreal).2
  exact le_trans hreal hAA

end MathGauge.F106
```