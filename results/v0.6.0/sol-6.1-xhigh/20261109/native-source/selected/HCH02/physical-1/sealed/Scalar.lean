import Bounds

open scoped ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

namespace HCH02

variable {X I : Type} {bot : X}

def Scalars (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : Set ℝ≥0∞ :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ a * d i x y}

noncomputable def scalarInf (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf (Scalars d φ U i j)

variable {d : I → X → X → ℝ≥0∞} {φ : Operator X bot} {U : Set X} {i j : I}

theorem scalars_upward {a b : ℝ≥0∞} (ha : a ∈ Scalars d φ U i j) (hab : a ≤ b) :
    b ∈ Scalars d φ U i j :=
  fun x hx y hy => (ha x hx y hy).trans (mul_le_mul_right' hab _)

theorem above_inf {b : ℝ≥0∞} (hb : scalarInf d φ U i j < b) :
    b ∈ Scalars d φ U i j := by
  obtain ⟨a, ha, hab⟩ := sInf_lt_iff.mp hb
  exact scalars_upward ha hab.le

theorem zero_inf_positive (ha : scalarInf d φ U i j = 0) {b : ℝ≥0∞}
    (hb : 0 < b) (hfin : b < ⊤) : b ∈ Scalars d φ U i j :=
  above_inf (ha ▸ hb)

theorem finite_inf_iff : scalarInf d φ U i j < ⊤ ↔
    ∃ a < ⊤, a ∈ Scalars d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, ht⟩ := sInf_lt_iff.mp h
    exact ⟨a, ht, ha⟩
  · rintro ⟨a, ht, ha⟩
    exact (sInf_le ha).trans_lt ht

theorem positive_finite_attained (hp : 0 < scalarInf d φ U i j)
    (ht : scalarInf d φ U i j < ⊤) :
    scalarInf d φ U i j ∈ Scalars d φ U i j := by
  let S := Scalars d φ U i j
  obtain ⟨a, _, ha⟩ := finite_inf_iff.mp ht
  letI : Nonempty S := ⟨⟨a, ha⟩⟩
  have hi : scalarInf d φ U i j = ⨅ a : S, (a : ℝ≥0∞) := sInf_eq_iInf' S
  intro x hx y hy
  calc
    d j (φ.func x) (φ.func y) ≤ ⨅ a : S, (a : ℝ≥0∞) * d i x y :=
      le_iInf (fun a => a.property x hx y hy)
    _ = scalarInf d φ U i j * d i x y := by
      rw [hi]
      exact (ENNReal.iInf_mul (fun _ hz => (ne_of_gt hp (hi.trans hz)).elim)).symm

theorem zero_input_positive_output {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hz : d i x y = 0) (hp : 0 < d j (φ.func x) (φ.func y)) :
    Scalars d φ U i j = ∅ ∧ scalarInf d φ U i j = ⊤ := by
  have hempty : Scalars d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hz, mul_zero] at h
    exact (not_le_of_gt hp) h
  exact ⟨hempty, by simp [scalarInf, hempty]⟩

end HCH02
