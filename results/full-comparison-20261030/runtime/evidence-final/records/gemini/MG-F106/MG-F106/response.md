本形式化任务的目标是：对于任意阿贝尔群 $G$、有限集 $A\subset G$、子群 $H\le G$、元素 $x\in G$ 与常数 $K\in\mathbb R$，在陪集切片 $B = \{a\in A : a-x\in H\} \ne \varnothing$ 且 $|A+A|\le K|A|$ 的假设下，构造有限子集 $F\subseteq A$，使得：
1. $F$ 覆盖 $A$ 模 $H$：$\forall a\in A, \exists t\in F, a-t\in H$（即 `Covers A H F`）；
2. 基数上界：$|F| \le \frac{K|A|}{|B|}$。

### 数学构造与证明思路

1. **有限集 $F$ 的构造**：
   - 在群 $G$ 上定义同余等价关系：$y_1 \sim y_2 \iff y_1 - y_2 \in H$（即标准陪集等价关系 `cosetSetoid H`）。
   - 考虑商映射 $q : G \to G / H$ 在 $A$ 上的像 $q(A) = A.\mathrm{image}\ q$。
   - 对每个非空相交的商类 $c \in q(A)$，利用经典选择量词（`Classical.choose`）在 $A \cap c$ 中选出一个代表元定义映射 $\mathrm{rep}$。
   - 令 $F = \mathrm{rep}(q(A)) \subseteq A$。由构造即知：
     - $F \subseteq A$；
     - 对任意 $a\in A$，$t = \mathrm{rep}(q(a)) \in F$ 且 $q(t) = q(a)$，即 $a - t \in H$，故 `Covers A H F` 成立；
     - 若 $t_1, t_2 \in F$ 满足 $t_1 - t_2 \in H$，则 $q(t_1) = q(t_2)$，由于代表元由商类唯一确定，必有 $t_1 = t_2$（$F$ 中不同元素分属不同陪集）。

2. **基数不等式 $|F| \cdot |B| \le |A+A|$**：
   - 考虑加法映射 $\Phi : F \times B \to A + A,\ (t, b) \mapsto t + b$。
   - 因 $F\subseteq A, B\subseteq A$，显然其像集包含在 $A+A$ 内。
   - 验证 $\Phi$ 在 $F\times B$ 上是单射：若 $t_1 + b_1 = t_2 + b_2$，则 $t_1 - t_2 = b_2 - b_1$。由于 $b_1, b_2 \in B = \mathrm{cosetSlice}\ A\ H\ x$，有 $b_1 - x \in H$ 且 $b_2 - x \in H$，故 $b_2 - b_1 = (b_2 - x) - (b_1 - x) \in H$。从而 $t_1 - t_2 \in H$。由 $F$ 的互异性知 $t_1 = t_2$，进而 $b_1 = b_2$。
   - 单射保证了 $|F \times B| \le |A+A|$，即 $|F| \cdot |B| \le |A+A| \le K|A|$。
   - 由于 $B \ne \varnothing$，在实数域中 $|B| > 0$，两边同除以 $|B|$ 即得 $|F| \le \frac{K|A|}{|B|}$。

---

### 形式化代码交付 (`Solution.lean`)

```lean
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
```

---

### 各声明覆盖的结论说明

1. [`cosetSetoid`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L13-L27)：
   构造群 $G$ 模子群 $H$ 的等价关系 $x \sim y \iff x - y \in H$，并给出自反、对称与传递性证明。
2. [`rep`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L30-L34) 与 [`coveringSet`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L37-L38)：
   具体构造满足题意的有限子集 $F \subseteq A$。
3. [`rep_spec`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L41-L52)：
   确立代表元选取的关键公理化性质：选取元素属于 $A$ 且落在给定的商类 $c$ 中。
4. [`coveringSet_subset`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L55-L59)：
   覆盖题设条件 $F \subseteq A$。
5. [`coveringSet_covers`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L62-L73)：
   覆盖题设条件 $\forall a \in A\ \exists t \in F:\ a - t \in H$（即 `Covers A H F`）。
6. [`coveringSet_sub_mem`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L76-L86)：
   证明 $F$ 中不同元素落入不同陪集，为单射性证明提供关键引理。
7. [`coveringSet_card_le`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L89-L136)：
   通过乘积集 $F \times B \to A + A$ 的单射性严格证明基数不等式 $|F| \le \frac{K|A|}{|B|}$。
8. [`exists_covering`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L140-L144) 与 [`exists_covering_of_ne_empty`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F106/work/Solution.lean#L148-L152)：
   最终定理，分别对应非空切片的两种表述 `Nonempty` 和 `≠ ∅`，交付了存在满足全部要求的有限子集 $F$ 的完整存在性证明。
