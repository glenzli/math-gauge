import CompactRealization
import ObservationBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ENNReal
namespace MathGauge.ConvexCost
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

theorem record_properties (f : E → ℝ≥0∞) (hf : ConvexCost f)
    (hp : ∃ x, f x≠⊤) (F : FiniteObservation E) :
    (∀ y, 0≤record F.1 f y) ∧ ConvexCost (record F.1 f) ∧
      ∃ y, record F.1 f y≠⊤ :=
  ⟨fun _ => bot_le,fiberInf_convex (observationMap F.1).toLinearMap hf,
    fiberInf_proper (observationMap F.1) hp⟩

/-- The task's exact real-height epigraph convention, with all extended-real
competitors, including negative infinity and positive infinity in one function. -/
theorem full_task_recovery (f : E → ℝ≥0∞) (hf : ConvexCost f) (hp : ∃ x, f x≠⊤) :
    IsClosed (epigraph (reconstruct f)) ∧ ConvexCost (reconstruct f) ∧ reconstruct f≤f ∧
      (∃ x, reconstruct f x≠⊤) ∧
      (∀ h : E → EReal,
        IsClosed {p : E × ℝ | h p.1≤(p.2:EReal)} →
        Convex ℝ {p : E × ℝ | h p.1≤(p.2:EReal)} →
        (∀ x, h x≤(f x:EReal)) → ∀ x, h x≤(reconstruct f x:EReal)) := by
  have hs := finite_observation_reconstruction f (jensen_of_convexCost hf) hp
  refine ⟨closed_epigraph hs.1,convexCost_of_jensen hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
  intro h hc _ hh
  exact reconstruct_maximal_ereal_of_isClosed_real_epigraph hf hp h hc hh

theorem reconstruction_exact_iff_closed (f : E → ℝ≥0∞) (hf : ConvexCost f)
    (hp : ∃ x, f x≠⊤) : reconstruct f=f ↔ IsClosed (epigraph f) :=
  (reconstruct_eq_iff_lowerSemicontinuous (jensen_of_convexCost hf) hp).trans
    (lowerSemicontinuous_iff_closed_real_epigraph f)

/-- The intermediate relaxed projection is a genuine nonnegative proper convex
cost, and its closure has exactly the task's projected relaxed value. -/
theorem refined_projection_properties (f : E → ℝ≥0∞) (hp : ∃ x, f x≠⊤)
    (F K : FiniteObservation E) (h : F.1≤K.1) :
    (∀ y, 0≤fiberInf (restriction h) (affineHull (record K.1 f)) y) ∧
    ConvexCost (fiberInf (restriction h) (affineHull (record K.1 f))) ∧
    (∃ y, fiberInf (restriction h) (affineHull (record K.1 f)) y≠⊤) ∧
    affineHull (fiberInf (restriction h) (affineHull (record K.1 f)))=
      affineHull (record F.1 f) := by
  refine ⟨fun _ => bot_le,fiberInf_convex (restriction h).toLinearMap (affineHull_convex _),?_,
    relaxed_record_projection h f hp⟩
  apply fiberInf_proper (restriction h)
  obtain ⟨z,hz⟩ := fiberInf_proper (observationMap K.1) hp
  exact ⟨z,ne_top_of_le_ne_top hz (affineHull_le _ z)⟩

end MathGauge.ConvexCost
