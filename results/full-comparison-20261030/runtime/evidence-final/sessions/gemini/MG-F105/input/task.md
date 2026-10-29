# 陪集切片与有限覆盖

设 $G$ 为任意阿贝尔群，$A\subset G$ 为有限集合，$H\le G$ 为子群，$x\in G$，$K\in\mathbb R$。记
$$B=\{a\in A:a-x\in H\}.$$
假设 $B\ne\varnothing$ 且 $|A+A|\le K|A|$。构造有限集合 $F\subseteq A$，使
$$|F|\le\frac{K|A|}{|B|},\qquad
\forall a\in A\ \exists t\in F:\ a-t\in H.$$
基数在不等式中视为实数。背景定义以附件 `Core.lean` 为准；允许使用 Mathlib 及经典逻辑。

附件 `Core.lean`、`Bridge.lean`、`Candidate.lean` 被提交为这一目标的形式化。审核其声明、定义和依赖是否完整对应目标，给出逐项数学依据，并区分代码有效性与覆盖范围。

Lean 4.29.1，Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6。


File: `Core.lean`
```lean
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

open scoped Pointwise
namespace MathGauge.F105
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def cosetSlice (A : Finset G) (H : AddSubgroup G) (x : G) : Finset G := by
  classical
  exact A.filter (fun a => a - x ∈ H)

def Covers (A : Finset G) (H : AddSubgroup G) (F : Finset G) : Prop :=
  ∀ a ∈ A, ∃ t ∈ F, a - t ∈ H

@[simp] theorem mem_cosetSlice (A : Finset G) (H : AddSubgroup G) (x a : G) :
    a ∈ cosetSlice A H x ↔ a ∈ A ∧ a - x ∈ H := by
  classical
  simp [cosetSlice]

theorem slice_subset (A : Finset G) (H : AddSubgroup G) (x : G) :
    cosetSlice A H x ⊆ A := by
  intro a ha
  exact (mem_cosetSlice A H x a).mp ha |>.1

end MathGauge.F105
```


File: `Bridge.lean`
```lean
import Core

open scoped Pointwise
namespace MathGauge.F105
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem slice_difference (A : Finset G) (H : AddSubgroup G) (x : G)
    {b c : G} (hb : b ∈ cosetSlice A H x) (hc : c ∈ cosetSlice A H x) :
    b - c ∈ H := by
  have h := H.sub_mem ((mem_cosetSlice A H x b).mp hb).2
    ((mem_cosetSlice A H x c).mp hc).2
  convert h using 1 <;> abel

theorem lift_cover (A F : Finset G) (H : AddSubgroup G) (x : G)
    (h : A ⊆ F + (cosetSlice A H x - cosetSlice A H x)) : Covers A H F := by
  intro a ha
  obtain ⟨t, ht, d, hd, htd⟩ := Finset.mem_add.mp (h ha)
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.mem_sub.mp hd
  refine ⟨t, ht, ?_⟩
  have heq : a - t = b - c := by
    rw [← htd, ← hbc]
    abel
  rw [heq]
  exact slice_difference A H x hb hc

end MathGauge.F105
```


File: `Candidate.lean`
```lean
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
```
