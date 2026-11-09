import Bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

variable {X I : Type} {bot : X}

def ScalarSet (d : I → X → X → ℝ≥0∞) (p : Operator X bot)
    (U : Set X) (i j : I) : Set ℝ≥0∞ :=
  {c | ∀ x ∈ U, ∀ y ∈ U, d j (p.func x) (p.func y) ≤ c * d i x y}

def scalarInf (d : I → X → X → ℝ≥0∞) (p : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf (ScalarSet d p U i j)

variable {d : I → X → X → ℝ≥0∞} {p : Operator X bot}
variable {U : Set X} {i j : I} {c b : ℝ≥0∞}

theorem scalarInf_empty (h : ScalarSet d p U i j = ∅) : scalarInf d p U i j = ⊤ := by
  simp [scalarInf, h]

theorem scalar_upward (hc : c ∈ ScalarSet d p U i j) (h : c ≤ b) :
    b ∈ ScalarSet d p U i j := by
  intro x hx y hy
  exact (hc x hx y hy).trans (mul_le_mul_left h _)

theorem scalar_above (h : scalarInf d p U i j < c) : c ∈ ScalarSet d p U i j := by
  obtain ⟨b, hb, hbc⟩ := sInf_lt_iff.mp h
  exact scalar_upward hb hbc.le

theorem scalar_zero_above (ha : scalarInf d p U i j = 0)
    (hc : 0 < c) (hf : c < ⊤) : c ∈ ScalarSet d p U i j :=
  scalar_above (ha ▸ hc)

theorem scalar_empty_of_zero_input {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (p.func x) (p.func y)) :
    ScalarSet d p U i j = ∅ ∧ scalarInf d p U i j = ⊤ := by
  have hs : ScalarSet d p U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hz := hc x hx y hy
    rw [hin, mul_zero] at hz
    exact (not_le_of_gt hout) hz
  exact ⟨hs, by simp [scalarInf, hs]⟩

theorem scalar_finite_iff : scalarInf d p U i j < ⊤ ↔
    ∃ c, c < ⊤ ∧ c ∈ ScalarSet d p U i j := by
  constructor
  · intro h
    obtain ⟨c, hc, hf⟩ := sInf_lt_iff.mp h
    exact ⟨c, hf, hc⟩
  · rintro ⟨c, hf, hc⟩
    exact (sInf_le hc).trans_lt hf

theorem scalar_attained (ha : 0 < scalarInf d p U i j)
    (hf : scalarInf d p U i j < ⊤) :
    scalarInf d p U i j ∈ ScalarSet d p U i j := by
  obtain ⟨c, _, hc⟩ := scalar_finite_iff.mp hf
  letI : Nonempty (ScalarSet d p U i j) := ⟨⟨c, hc⟩⟩
  have heq : scalarInf d p U i j = ⨅ c : ScalarSet d p U i j, c.val := by
    apply le_antisymm
    · exact le_iInf fun c => sInf_le c.property
    · apply le_sInf
      intro c hc
      exact iInf_le_of_le ⟨c, hc⟩ le_rfl
  intro x hx y hy
  rw [heq, ENNReal.iInf_mul (fun _ hz => ?_)]
  · exact le_iInf fun c => c.property x hx y hy
  · exact ((ne_of_gt ha) (heq.trans hz)).elim

end HCH02
