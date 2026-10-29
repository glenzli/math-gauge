import FiniteObservation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Set
open scoped ENNReal

namespace MathGauge.ConvexCost

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Every minorant with a closed real-height epigraph lies below the reconstruction. -/
theorem reconstruct_maximal_ereal_of_isClosed_real_epigraph
    {f : E → ℝ≥0∞} (hf : ConvexCost f) (hp : ∃ x, f x ≠ ⊤)
    (h : E → EReal)
    (hclosed : IsClosed {p : E × ℝ | h p.1 ≤ (p.2 : EReal)})
    (hle : ∀ x, h x ≤ (f x : EReal)) :
    ∀ x, h x ≤ (reconstruct f x : EReal) := by
  have hsub : closure (epigraph f) ⊆ {p : E × ℝ | h p.1 ≤ (p.2 : EReal)} := by
    apply closure_minimal _ hclosed
    intro p hp'
    have he : ((ENNReal.ofReal p.2 : ℝ≥0∞) : EReal) = (p.2 : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hp'.1]
    exact (hle p.1).trans (he ▸ EReal.coe_ennreal_le_coe_ennreal_iff.mpr hp'.2)
  intro x
  rw [reconstruct_eq_affineHull]
  by_cases hx : affineHull f x = ⊤
  · simp [hx]
  have hm : (x, (affineHull f x).toReal) ∈ epigraph (affineHull f) :=
    ⟨ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hx).ge⟩
  rw [epigraph_affineHull_eq_closure hf hp] at hm
  simpa only [Set.mem_setOf_eq, EReal.coe_ennreal_toReal hx] using hsub hm

/-- The existing lower-semicontinuity interface follows from the direct epigraph theorem. -/
theorem reconstruct_maximal_ereal {f : E → ℝ≥0∞} (hf : JensenConvex f)
    (hp : ∃ x, f x ≠ ⊤) (h : E → EReal) (hc : LowerSemicontinuous h)
    (hle : ∀ x, h x ≤ (f x : EReal)) : ∀ x, h x ≤ (reconstruct f x : EReal) := by
  have hclosed : IsClosed {p : E × ℝ | h p.1 ≤ (p.2 : EReal)} :=
    hc.isClosed_epigraph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  exact reconstruct_maximal_ereal_of_isClosed_real_epigraph
    (convexCost_of_jensen hf) hp h hclosed hle

theorem fiberInf_mono {X Y : Type*} (q : X → Y) {f g : X → ℝ≥0∞} (h : f ≤ g) :
    fiberInf q f ≤ fiberInf q g := by
  intro y
  exact iInf_mono fun x => iInf_mono fun _ => h x

/-- The final relaxation in the refined projection identity is retained. -/
theorem relaxed_record_projection {F K : Submodule ℝ (E →L[ℝ] ℝ)} (h : F ≤ K)
    (f : E → ℝ≥0∞) (hp : ∃ x, f x ≠ ⊤) :
    affineHull (fiberInf (restriction h) (affineHull (record K f))) = affineHull (record F f) := by
  let v := fiberInf (restriction h) (affineHull (record K f))
  have hupper : v ≤ record F f := by
    intro y
    rw [record_restriction h]
    exact fiberInf_mono _ (affineHull_le _) y
  have hlower : affineHull (record F f) ≤ v := by
    intro y
    apply le_iInf
    intro z
    apply le_iInf
    intro hz
    rw [← hz]
    exact relaxed_record_mono h f z
  apply le_antisymm (affineHull_mono hupper)
  apply affineHull_maximal
  · obtain ⟨y,hy⟩ := fiberInf_proper (observationMap F) hp
    exact ⟨y, ne_top_of_le_ne_top hy (hupper y)⟩
  · exact affineHull_lowerSemicontinuous _
  · exact affineHull_convex _
  · exact hlower

def indicatorCost {X : Type*} (s : Set X) (x : X) : ℝ≥0∞ := by
  classical
  exact if x ∈ s then 0 else ⊤

theorem epigraph_indicator (s : Set E) : epigraph (indicatorCost s) = s ×ˢ Ici 0 := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epigraph, indicatorCost, hp, and_comm]

theorem indicator_convex {s : Set E} (hs : Convex ℝ s) : ConvexCost (indicatorCost s) := by
  rw [ConvexCost, epigraph_indicator]
  exact hs.prod (convex_Ici 0)

theorem indicator_proper {s : Set E} (hs : s.Nonempty) : ∃ x, indicatorCost s x ≠ ⊤ := by
  obtain ⟨x,hx⟩ := hs
  exact ⟨x, by simp [indicatorCost,hx]⟩

theorem hull_indicator {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty) :
    affineHull (indicatorCost s) = indicatorCost (closure s) := by
  have he := epigraph_affineHull_eq_closure (indicator_convex hs) (indicator_proper hne)
  rw [epigraph_indicator, closure_prod_eq, isClosed_Ici.closure_eq] at he
  funext x
  by_cases hx : x ∈ closure s
  · have hm : (x, (0 : ℝ)) ∈ epigraph (affineHull (indicatorCost s)) := by
      rw [he]
      exact ⟨hx, by simp⟩
    have hz : affineHull (indicatorCost s) x = 0 := le_antisymm (by simpa using hm.2) bot_le
    simp [indicatorCost,hx,hz]
  · have ht : affineHull (indicatorCost s) x = ⊤ := by
      by_contra hn
      have hm : (x, (affineHull (indicatorCost s) x).toReal) ∈ epigraph (affineHull (indicatorCost s)) :=
        ⟨ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hn).ge⟩
      rw [he] at hm
      exact hx hm.1
    simp [indicatorCost,hx,ht]

theorem open_halfline_reconstruction :
    reconstruct (indicatorCost (Ioi (0 : ℝ))) = indicatorCost (Ici 0) := by
  rw [reconstruct_eq_affineHull, hull_indicator (convex_Ioi 0) nonempty_Ioi,
    closure_Ioi]

theorem boundary_not_recovered :
    indicatorCost (Ioi (0 : ℝ)) 0 = ⊤ ∧ reconstruct (indicatorCost (Ioi (0 : ℝ))) 0 = 0 := by
  rw [open_halfline_reconstruction]
  simp [indicatorCost]

def exponentialCost (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp x)

theorem exponential_positive (x : ℝ) : 0 < exponentialCost x :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos x)

theorem exponential_convex : JensenConvex exponentialCost := by
  intro x y a b ha hb hab
  have hh := convexOn_exp.2 (mem_univ x) (mem_univ y) ha hb hab
  change ENNReal.ofReal (Real.exp (a * x + b * y)) ≤ _
  calc
    _ ≤ ENNReal.ofReal (a * Real.exp x + b * Real.exp y) := ENNReal.ofReal_le_ofReal hh
    _ = _ := by rw [ENNReal.ofReal_add (mul_nonneg ha (Real.exp_pos x).le)
      (mul_nonneg hb (Real.exp_pos y).le), ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]; rfl

theorem exponential_continuous : Continuous exponentialCost :=
  ENNReal.continuous_ofReal.comp Real.continuous_exp

theorem exponential_inf_zero : (⨅ x : ℝ, exponentialCost x) = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_forall_gt
  intro b hb
  obtain ⟨t,ht,ht0,htb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
  have htp : 0 < t := ENNReal.ofReal_pos.mp ht0
  exact (iInf_le exponentialCost (Real.log t)).trans_lt (by simpa [exponentialCost,Real.exp_log htp] using htb)

theorem exponential_zero_observation_unattained :
    fiberInf (fun _ : ℝ => (0 : ℝ)) exponentialCost 0 = 0 ∧
    ∀ x, exponentialCost x ≠ fiberInf (fun _ : ℝ => (0 : ℝ)) exponentialCost 0 := by
  have h : fiberInf (fun _ : ℝ => (0 : ℝ)) exponentialCost 0 = 0 := by
    simpa [fiberInf] using exponential_inf_zero
  exact ⟨h, fun x => by rw [h]; exact (exponential_positive x).ne'⟩

end MathGauge.ConvexCost
