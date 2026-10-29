import ProjectionExample

noncomputable section
open Set
open scoped ENNReal
namespace MathGauge.ConvexCost
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

theorem epigraph_injective : Function.Injective (epigraph (E := E)) := by
  intro f g h
  have hle (a b : E → ℝ≥0∞) (hab : epigraph a ⊆ epigraph b) : b ≤ a := by
    intro x
    by_cases hx : a x = ⊤
    · simp [hx]
    have hp : (x,(a x).toReal) ∈ epigraph a :=
      ⟨ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hx).ge⟩
    simpa only [ENNReal.ofReal_toReal hx] using (hab hp).2
  exact le_antisymm (hle g f h.symm.subset) (hle f g h.subset)

theorem relaxation_unique {f g : E → ℝ≥0∞} (hf : ConvexCost f)
    (hp : ∃ x, f x ≠ ⊤) (hg : epigraph g = closure (epigraph f)) : g = affineHull f :=
  epigraph_injective (hg.trans (epigraph_affineHull_eq_closure hf hp).symm)

/-- Every nonempty closed vertical section is the claimed real ray; the empty
case corresponds exactly to the value infinity. -/
theorem closed_epigraph_vertical_section {f : E → ℝ≥0∞} (hf : ConvexCost f)
    (hp : ∃ x, f x ≠ ⊤) (x : E) :
    {t : ℝ | (x,t) ∈ closure (epigraph f)} =
      if affineHull f x = ⊤ then ∅ else Ici (affineHull f x).toReal := by
  rw [← epigraph_affineHull_eq_closure hf hp]
  by_cases hx : affineHull f x = ⊤
  · simp [hx,epigraph]
  · rw [if_neg hx]
    ext t
    constructor
    · intro ht
      exact (ENNReal.le_ofReal_iff_toReal_le hx ht.1).mp ht.2
    · intro ht
      have ht0 : 0 ≤ t := ENNReal.toReal_nonneg.trans ht
      exact ⟨ht0, (ENNReal.le_ofReal_iff_toReal_le hx ht0).mpr ht⟩

theorem clipped_minorant_iff (f : E → ℝ≥0∞) (l : E →L[ℝ] ℝ) (b : ℝ) :
    (∀ z, ENNReal.ofReal (l z+b) ≤ f z) ↔
      (∀ z, ((l z+b : ℝ) : EReal) ≤ (f z : EReal)) := by
  constructor
  · intro h z
    have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (h z)
    rw [EReal.coe_ennreal_ofReal] at hh
    exact (EReal.coe_le_coe (le_max_left _ _)).trans hh
  · intro h z
    simpa only [EReal.real_coe_toENNReal, EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal (h z)

def plainAffineHull (f : E → ℝ≥0∞) (x : E) : EReal :=
  ⨆ l : E →L[ℝ] ℝ, ⨆ b : ℝ,
    ⨆ (_ : ∀ z, ((l z+b : ℝ) : EReal) ≤ (f z : EReal)), ((l x+b : ℝ) : EReal)

/-- The ENNReal implementation is exactly the supremum of genuine real affine
minorants, with no additional nonnegativity restriction on the affine functions. -/
theorem plain_affine_sup (f : E → ℝ≥0∞) (x : E) :
    plainAffineHull f x = (affineHull f x : EReal) := by
  have h0 : (0 : EReal) ≤ plainAffineHull f x := by
    have hz : ∀ z, (((0 : E →L[ℝ] ℝ) z + 0 : ℝ) : EReal) ≤ (f z : EReal) := by
      intro z
      simpa using EReal.coe_ennreal_nonneg (f z)
    simpa using (le_iSup_of_le (0 : E →L[ℝ] ℝ)
      (le_iSup_of_le (0 : ℝ) (le_iSup_of_le hz le_rfl)) :
        (((0 : E →L[ℝ] ℝ) x + 0 : ℝ) : EReal) ≤ plainAffineHull f x)
  apply le_antisymm
  · apply iSup_le
    intro l
    apply iSup_le
    intro b
    apply iSup_le
    intro h
    have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (affine_minorant_le_hull l b ((clipped_minorant_iff f l b).mpr h) x)
    rw [EReal.coe_ennreal_ofReal] at hh
    exact (EReal.coe_le_coe (le_max_left _ _)).trans hh
  · have hNN : affineHull f x ≤ (plainAffineHull f x).toENNReal := by
      apply iSup_le
      intro l
      apply iSup_le
      intro b
      apply iSup_le
      intro h
      have hh : ((l x+b : ℝ) : EReal) ≤ plainAffineHull f x :=
        le_iSup_of_le l (le_iSup_of_le b
          (le_iSup_of_le ((clipped_minorant_iff f l b).mp h) le_rfl))
      exact EReal.toENNReal_le_toENNReal hh
    exact (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hNN).trans_eq (EReal.coe_toENNReal h0)

end MathGauge.ConvexCost
