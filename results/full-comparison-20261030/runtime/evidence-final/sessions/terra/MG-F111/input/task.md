# 扩展非负值上界与最小系数

设 $X$ 为任意集合，$d,e:X\to[0,+\infty]$。采用扩展非负实数的通常序与算术，特别是 $0\cdot(+\infty)=0$。称有限系数 $c\in[0,+\infty)$ 可行为
\[
\forall x\in X,\qquad e(x)\le c\,d(x).
\]
令
\[
Z:\ \forall x,\ d(x)=0\Rightarrow e(x)=0,\qquad
H:\ \forall x,\ d(x)=+\infty\Rightarrow e(x)=0,
\]
并令
\[
r=\sup\left\{\frac{e(x)}{d(x)}:x\in X,\ 0<d(x)<+\infty\right\},
\]
空集上确界取 $0$。

作者提交附件并声称覆盖以下完整结论：有限可行系数存在当且仅当 $Z$ 且 $r<+\infty$；最小有限可行系数存在当且仅当
\[
Z,\qquad r<+\infty,\qquad r=0\Rightarrow H;
\]
存在时其值为 $r$。此外，单点集合上 $d=+\infty,e=1$ 有有限可行系数但没有最小有限可行系数。

请审核全部附件与这些陈述的对应关系，分别说明前提、量词、边界和实际覆盖范围。给出可定位依据；不要仅凭编译状态或声明名称作结论。

环境：Lean 4.29.1，Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`；附件依次为 `ExtendedBounds.lean`、`CoefficientClassification.lean`、`BoundaryExample.lean`。


File: `ExtendedBounds.lean`
```lean
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

namespace MathGauge.F111

open ENNReal
variable {X : Type*}

def Bound (d e : X → ℝ≥0∞) (c : ℝ≥0∞) : Prop := ∀ x, e x ≤ c * d x

def ZeroCompatible (d e : X → ℝ≥0∞) : Prop := ∀ x, d x = 0 → e x = 0

def TopCompatible (d e : X → ℝ≥0∞) : Prop := ∀ x, d x = ∞ → e x = 0

noncomputable def ratioSup (d e : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ x : {x : X // d x ≠ 0 ∧ d x ≠ ∞}, e x / d x

theorem ratio_le_iff (d e : X → ℝ≥0∞) (c : ℝ≥0∞) :
    ratioSup d e ≤ c ↔ ∀ x, d x ≠ 0 → d x ≠ ∞ → e x ≤ c * d x := by
  constructor
  · intro h x h0 ht
    have hr : e x / d x ≤ c := (le_iSup (fun y : {x : X // d x ≠ 0 ∧ d x ≠ ∞} => e y / d y) ⟨x, h0, ht⟩).trans h
    exact (ENNReal.div_le_iff h0 ht).mp hr
  · intro h
    apply iSup_le
    intro x
    exact (ENNReal.div_le_iff x.property.1 x.property.2).mpr (h x x.property.1 x.property.2)

theorem bound_iff (d e : X → ℝ≥0∞) (c : ℝ≥0∞) :
    Bound d e c ↔ ZeroCompatible d e ∧ ratioSup d e ≤ c ∧ (c = 0 → TopCompatible d e) := by
  constructor
  · intro h
    refine ⟨?_, (ratio_le_iff d e c).mpr (fun x _ _ => h x), ?_⟩
    · intro x hx
      have hx' := h x
      rw [hx, mul_zero] at hx'
      exact le_antisymm hx' bot_le
    · intro hc x hx
      have hx' := h x
      rw [hc, zero_mul] at hx'
      exact le_antisymm hx' bot_le
  · rintro ⟨hz, hr, ht⟩ x
    by_cases h0 : d x = 0
    · rw [h0, hz x h0, mul_zero]
    by_cases htop : d x = ∞
    · by_cases hc : c = 0
      · rw [htop, hc, ht hc x htop, zero_mul]
      · rw [htop, ENNReal.mul_top hc]; exact le_top
    · exact (ratio_le_iff d e c).mp hr x h0 htop

def LeastFinite (d e : X → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  c ≠ ∞ ∧ Bound d e c ∧ ∀ b, b ≠ ∞ → Bound d e b → c ≤ b

end MathGauge.F111
```


File: `CoefficientClassification.lean`
```lean
import ExtendedBounds

namespace MathGauge.F111

open ENNReal
variable {X : Type*}

theorem finite_bound_exists_iff (d e : X → ℝ≥0∞) :
    (∃ c, c ≠ ∞ ∧ Bound d e c) ↔ ZeroCompatible d e ∧ ratioSup d e ≠ ∞ := by
  constructor
  · rintro ⟨c, hc, hb⟩
    obtain ⟨hz, hr, _⟩ := (bound_iff d e c).mp hb
    exact ⟨hz, ne_top_of_le_ne_top hc hr⟩
  · rintro ⟨hz, hr⟩
    refine ⟨ratioSup d e + 1, by simpa using hr, ?_⟩
    apply (bound_iff d e _).mpr
    refine ⟨hz, le_add_right le_rfl, ?_⟩
    intro h0
    have h1 : (1 : ℝ≥0∞) ≤ ratioSup d e + 1 := le_add_left le_rfl
    rw [h0] at h1
    exact False.elim (by simpa using h1)

theorem least_coefficient_eq (d e : X → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : LeastFinite d e c) : c = ratioSup d e := by
  obtain ⟨hcfin, hcb, hmin⟩ := hc
  obtain ⟨hz, hrc, _⟩ := (bound_iff d e c).mp hcb
  apply le_antisymm _ hrc
  by_contra h
  have hlt : ratioSup d e < c := lt_of_not_ge h
  obtain ⟨b, hrb, hbc⟩ := exists_between hlt
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hrb)
  have hbfin : b ≠ ∞ := ne_top_of_le_ne_top hcfin hbc.le
  have hbb : Bound d e b := (bound_iff d e b).mpr ⟨hz, hrb.le, fun h0 => False.elim (hb0 h0)⟩
  exact (not_le_of_gt hbc) (hmin b hbfin hbb)

theorem least_finite_exists_iff (d e : X → ℝ≥0∞) :
    (∃ c, LeastFinite d e c) ↔
    ZeroCompatible d e ∧ ratioSup d e ≠ ∞ ∧ (ratioSup d e = 0 → TopCompatible d e) := by
  constructor
  · rintro ⟨c, hc⟩
    have heq := least_coefficient_eq d e hc
    subst c
    exact ⟨((bound_iff d e _).mp hc.2.1).1, hc.1,
      ((bound_iff d e _).mp hc.2.1).2.2⟩
  · rintro ⟨hz, hr, ht⟩
    refine ⟨ratioSup d e, hr, (bound_iff d e _).mpr ⟨hz, le_rfl, ht⟩, ?_⟩
    intro b hb hbb
    exact ((bound_iff d e b).mp hbb).2.1

#print axioms finite_bound_exists_iff
#print axioms least_finite_exists_iff
#print axioms least_coefficient_eq

end MathGauge.F111
```


File: `BoundaryExample.lean`
```lean
import CoefficientClassification

namespace MathGauge.F111

open ENNReal

def sourceValue (_ : Unit) : ℝ≥0∞ := ∞
def targetValue (_ : Unit) : ℝ≥0∞ := 1

theorem boundary_ratio : ratioSup sourceValue targetValue = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro x
  exact False.elim (x.property.2 rfl)

theorem boundary_feasible : ∃ c, c ≠ ∞ ∧ Bound sourceValue targetValue c := by
  refine ⟨1, by simp, ?_⟩
  intro x
  simp [sourceValue, targetValue]

theorem boundary_not_attained : ¬ ∃ c, LeastFinite sourceValue targetValue c := by
  intro h
  have ht := ((least_finite_exists_iff sourceValue targetValue).mp h).2.2 boundary_ratio
  have := ht () rfl
  simpa [targetValue] using this

#print axioms boundary_feasible
#print axioms boundary_not_attained

end MathGauge.F111
```
