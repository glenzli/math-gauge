import ConvexCostExtras
import Mathlib.Tactic.Ring

noncomputable section
open Set
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace MathGauge.ConvexCost

/-- The closed hyperbola epigraph, expressed without division at zero. -/
def hyperbolaRegion : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 1 ≤ p.1*p.2}

theorem hyperbolaRegion_description (p : ℝ × ℝ) :
    p ∈ hyperbolaRegion ↔ 0 < p.1 ∧ 1 / p.1 ≤ p.2 := by
  constructor
  · rintro ⟨hx,hy,hxy⟩
    have hxp : 0 < p.1 := by
      by_contra h
      have : p.1 = 0 := le_antisymm (not_lt.mp h) hx
      norm_num [this] at hxy
    exact ⟨hxp, (div_le_iff₀ hxp).mpr (by simpa [mul_comm] using hxy)⟩
  · rintro ⟨hx,hy⟩
    exact ⟨hx.le, (one_div_pos.mpr hx).le.trans hy,
      by simpa [mul_comm] using (div_le_iff₀ hx).mp hy⟩

theorem hyperbolaRegion_closed : IsClosed hyperbolaRegion :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_const (continuous_fst.mul continuous_snd)))

theorem hyperbolaRegion_convex : Convex ℝ hyperbolaRegion := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx₁,hx₂,hx⟩
  rcases hy with ⟨hy₁,hy₂,hy⟩
  change 0 ≤ a*x.1+b*y.1 ∧ 0 ≤ a*x.2+b*y.2 ∧
    1 ≤ (a*x.1+b*y.1)*(a*x.2+b*y.2)
  refine ⟨add_nonneg (mul_nonneg ha hx₁) (mul_nonneg hb hy₁),
    add_nonneg (mul_nonneg ha hx₂) (mul_nonneg hb hy₂), ?_⟩
  have hc : 2 ≤ x.1*y.2+y.1*x.2 := by
    have hprod : 1 ≤ (x.1*y.2)*(y.1*x.2) := by nlinarith [mul_le_mul hx hy (by norm_num) (by linarith)]
    have hnon : 0 ≤ x.1*y.2+y.1*x.2 :=
      add_nonneg (mul_nonneg hx₁ hy₂) (mul_nonneg hy₁ hx₂)
    nlinarith [sq_nonneg (x.1*y.2-y.1*x.2)]
  have h₁ := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hx)
  have h₂ := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hy)
  have h₃ := mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr hc)
  nlinarith [sq_nonneg (a+b-1)]

theorem hyperbolaRegion_nonempty : hyperbolaRegion.Nonempty := ⟨(1,1), by norm_num [hyperbolaRegion]⟩

theorem hyperbola_indicator_fixed : affineHull (indicatorCost hyperbolaRegion) =
    indicatorCost hyperbolaRegion := by
  rw [hull_indicator hyperbolaRegion_convex hyperbolaRegion_nonempty,
    hyperbolaRegion_closed.closure_eq]

theorem hyperbola_projection :
    fiberInf Prod.fst (indicatorCost hyperbolaRegion) = indicatorCost (Ioi (0 : ℝ)) := by
  funext x
  by_cases hx : 0 < x
  · have hp : (x,1/x) ∈ hyperbolaRegion :=
      (hyperbolaRegion_description _).mpr ⟨hx,le_rfl⟩
    have hh : fiberInf Prod.fst (indicatorCost hyperbolaRegion) x ≤ 0 :=
      (fiberInf_le Prod.fst (indicatorCost hyperbolaRegion) (x,1/x)).trans (by
        rw [indicatorCost, if_pos hp])
    apply le_antisymm
    · simpa only [indicatorCost, Set.mem_Ioi, if_pos hx] using hh
    · simp [indicatorCost,hx]
  · have hh : fiberInf Prod.fst (indicatorCost hyperbolaRegion) x = ⊤ := by
      apply top_unique
      apply le_iInf
      intro p
      apply le_iInf
      intro hp
      have hn : p ∉ hyperbolaRegion := by
        intro h
        exact hx (hp ▸ (hyperbolaRegion_description p).mp h |>.1)
      simp [indicatorCost,hn]
    simp [hh,indicatorCost,hx]

/-- A closed convex cost has a projection that is not lower semicontinuous;
the relaxation in the projection formula cannot be removed. -/
theorem projected_closed_cost_requires_relaxation :
    affineHull (indicatorCost hyperbolaRegion) = indicatorCost hyperbolaRegion ∧
    fiberInf Prod.fst (indicatorCost hyperbolaRegion) 0 = ⊤ ∧
    affineHull (fiberInf Prod.fst (indicatorCost hyperbolaRegion)) 0 = 0 := by
  refine ⟨hyperbola_indicator_fixed, ?_⟩
  rw [hyperbola_projection, hull_indicator (convex_Ioi 0) nonempty_Ioi, closure_Ioi]
  simp [indicatorCost]

end MathGauge.ConvexCost
