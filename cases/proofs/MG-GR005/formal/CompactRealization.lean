import CompactRecords

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set
open scoped ENNReal
namespace MathGauge.ConvexCost
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- Hahn–Banach supplies the separation used by the actual complete observation family. -/
theorem all_finite_observations_injective {x z : E}
    (h : ∀ F : FiniteObservation E, observationMap F.1 x=observationMap F.1 z) : x=z := by
  by_contra hne
  obtain ⟨l,c,hxc,hzc⟩ := geometric_hahn_banach_point_closed (convex_singleton z)
    isClosed_singleton (by simpa only [mem_singleton_iff] using hne)
  let F : FiniteObservation E := ⟨Submodule.span ℝ {l},inferInstance⟩
  let lf : F.1 := ⟨l,Submodule.mem_span_singleton_self l⟩
  have he : l x=l z := congrArg (fun y : ObservationDual F.1 => y lf) (h F)
  have hh := hzc z (mem_singleton z)
  linarith

/-- Compatible finite records with one common finite cost bound meet inside the
same compact original-space sublevel set. -/
theorem compact_compatible_realization (f : E → ℝ≥0∞) (hf : IsClosed (epigraph f))
    (hk : ∀ c : ℝ, 0≤c → IsCompact {x | f x≤ENNReal.ofReal c})
    (y : ∀ F : FiniteObservation E, ObservationDual F.1)
    (hy : ∀ (F K : FiniteObservation E) (h : F.1≤K.1), restriction h (y K)=y F)
    (c : ℝ) (hc : 0≤c)
    (hcost : ∀ F : FiniteObservation E, record F.1 f (y F)≤ENNReal.ofReal c) :
    ∃! x : E, (∀ F : FiniteObservation E, observationMap F.1 x=y F) ∧ f x≤ENNReal.ofReal c := by
  classical
  letI : Nonempty (FiniteObservation E) := ⟨⟨⊥,inferInstance⟩⟩
  let C (F : FiniteObservation E) : Set E :=
    {x | f x≤ENNReal.ofReal c}∩{x | observationMap F.1 x=y F}
  have hclosed (F : FiniteObservation E) : IsClosed (C F) :=
    ((lowerSemicontinuous_of_closed_real_epigraph hf).isClosed_preimage _).inter
      (isClosed_eq (observationMap F.1).continuous continuous_const)
  have hcompact (F : FiniteObservation E) : IsCompact (C F) :=
    (hk c hc).inter_right (isClosed_eq (observationMap F.1).continuous continuous_const)
  have hnonempty (F : FiniteObservation E) : (C F).Nonempty := by
    obtain ⟨x,hx,hfx⟩ := compact_record_attains f hf hk F (y F)
      (lt_of_le_of_lt (hcost F) ENNReal.ofReal_lt_top)
    refine ⟨x,?_,hx⟩
    change f x≤ENNReal.ofReal c
    rw [hfx]
    exact hcost F
  have hdir : Directed (· ⊇ ·) C := by
    intro F K
    obtain ⟨L,hF,hK⟩ := finite_observations_directed F K
    refine ⟨L,?_,?_⟩
    · intro x hx
      refine ⟨hx.1,?_⟩
      have he := congrArg (restriction hF) hx.2
      simpa only [restriction_observationMap,hy F L hF] using he
    · intro x hx
      refine ⟨hx.1,?_⟩
      have he := congrArg (restriction hK) hx.2
      simpa only [restriction_observationMap,hy K L hK] using he
  obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hdir hnonempty hcompact hclosed
  have hall : ∀ F, x ∈ C F := mem_iInter.mp hx
  refine ⟨x,⟨fun F => (hall F).2,(hall (Classical.choice inferInstance)).1⟩,?_⟩
  intro z hz
  apply all_finite_observations_injective
  intro F
  exact (hz.1 F).trans (hall F).2.symm

end MathGauge.ConvexCost
