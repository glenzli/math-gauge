import RelaxationGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set
open scoped ENNReal
namespace MathGauge.ConvexCost

section RealEpigraph
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem lowerSemicontinuous_of_closed_real_epigraph {f : E → ℝ≥0∞}
    (hf : IsClosed (epigraph f)) : LowerSemicontinuous f := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c=⊤
  · simp [hc]
  have hcl := hf.preimage (continuous_id.prodMk (continuous_const : Continuous (fun _ : E => c.toReal)))
  convert hcl using 1
  ext x
  simp only [mem_preimage,mem_Iic,epigraph,mem_setOf_eq,
    id_eq,ENNReal.ofReal_toReal hc,and_iff_right ENNReal.toReal_nonneg]

theorem lowerSemicontinuous_iff_closed_real_epigraph (f : E → ℝ≥0∞) :
    LowerSemicontinuous f ↔ IsClosed (epigraph f) :=
  ⟨closed_epigraph,lowerSemicontinuous_of_closed_real_epigraph⟩
end RealEpigraph

section CompactFibers
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
variable (q : X → Y) (hq : Continuous q) (f : X → ℝ≥0∞)
variable (hf : LowerSemicontinuous f)
variable (hk : ∀ c : ℝ, 0≤c → IsCompact {x | f x≤ENNReal.ofReal c})

include hq hf hk

/-- A true fiber minimizer is constructed inside one finite compact sublevel set.
No sequential compactness or first countability is used. -/
theorem compact_fiber_attains (y : Y) (hy : fiberInf q f y<⊤) :
    ∃ x, q x=y ∧ f x=fiberInf q f y := by
  obtain ⟨x,hx,hfin⟩ : ∃ x, q x=y ∧ f x<⊤ := by
    simpa only [fiberInf,iInf_lt_iff,exists_prop] using hy
  let K : Set X := {z | f z≤f x}
  have hK : IsCompact K := by
    simpa only [ENNReal.ofReal_toReal hfin.ne] using hk (f x).toReal ENNReal.toReal_nonneg
  let C : Set X := K∩{z | q z=y}
  have hC : IsCompact C := hK.inter_right (isClosed_eq hq continuous_const)
  have hxC : x ∈ C := ⟨by change f x≤f x; exact le_rfl,hx⟩
  obtain ⟨z,hz,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨x,hxC⟩ hC (hf.lowerSemicontinuousOn C)
  refine ⟨z,hz.2,le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro w
    apply le_iInf
    intro hw
    by_cases hwK : f w≤f x
    · exact hmin ⟨hwK,hw⟩
    · exact (hmin hxC).trans (le_of_not_ge hwK)
  · have he := fiberInf_le q f z
    rwa [hz.2] at he

/-- The compact hypothesis gives exact images of finite sublevel sets. -/
theorem compact_fiber_sublevel (c : ℝ) (hc : 0≤c) :
    {y | fiberInf q f y≤ENNReal.ofReal c}=q '' {x | f x≤ENNReal.ofReal c} := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,hfx⟩ := compact_fiber_attains q hq f hf hk y
      (lt_of_le_of_lt hy ENNReal.ofReal_lt_top)
    refine ⟨x,?_,hx⟩
    change f x≤ENNReal.ofReal c
    rw [hfx]
    exact hy
  · rintro ⟨x,hx,rfl⟩
    exact (fiberInf_le q f x).trans hx

theorem compact_fiber_lowerSemicontinuous : LowerSemicontinuous (fiberInf q f) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c=⊤
  · simp [hc]
  have he := compact_fiber_sublevel q hq f hf hk c.toReal ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal hc] at he
  change IsClosed {y | fiberInf q f y≤c}
  rw [he]
  have hK : IsCompact {x | f x≤c} := by
    simpa only [ENNReal.ofReal_toReal hc] using hk c.toReal ENNReal.toReal_nonneg
  exact (hK.image hq).isClosed
end CompactFibers

section ObservedCompact
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem compact_record_attains (f : E → ℝ≥0∞) (hf : IsClosed (epigraph f))
    (hk : ∀ c : ℝ, 0≤c → IsCompact {x | f x≤ENNReal.ofReal c})
    (F : FiniteObservation E) (y : ObservationDual F.1) (hy : record F.1 f y<⊤) :
    ∃ x, observationMap F.1 x=y ∧ f x=record F.1 f y :=
  compact_fiber_attains _ (observationMap F.1).continuous f
    (lowerSemicontinuous_of_closed_real_epigraph hf) hk y hy

theorem compact_record_closed (f : E → ℝ≥0∞) (hf : IsClosed (epigraph f))
    (hk : ∀ c : ℝ, 0≤c → IsCompact {x | f x≤ENNReal.ofReal c})
    (F : FiniteObservation E) : IsClosed (epigraph (record F.1 f)) :=
  closed_epigraph (compact_fiber_lowerSemicontinuous _ (observationMap F.1).continuous f
    (lowerSemicontinuous_of_closed_real_epigraph hf) hk)
end ObservedCompact
end MathGauge.ConvexCost
