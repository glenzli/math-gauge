import CompactRecords

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set
open scoped ENNReal
namespace MathGauge.ConvexCost

abbrev Plane := ℝ × ℝ

def firstFunctional : Plane →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

def secondFunctional : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

def firstSpace : FiniteObservation Plane := ⟨Submodule.span ℝ {firstFunctional},inferInstance⟩

def firstVector : firstSpace.1 := ⟨firstFunctional,Submodule.mem_span_singleton_self _⟩

def firstValue : ObservationDual firstSpace.1 →L[ℝ] ℝ := observationEval firstSpace.1 firstVector

def firstLift : ℝ →L[ℝ] ObservationDual firstSpace.1 :=
  (observationMap firstSpace.1).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)

@[simp] theorem firstValue_lift (t : ℝ) : firstValue (firstLift t)=t := rfl

@[simp] theorem firstValue_observation (p : Plane) : firstValue (observationMap firstSpace.1 p)=p.1 := rfl

theorem firstLift_value (y : ObservationDual firstSpace.1) : firstLift (firstValue y)=y := by
  apply LinearMap.ext
  intro l
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp l.2
  have hl : l=a • firstVector := Subtype.ext ha.symm
  rw [hl,map_smul,map_smul]
  rfl

theorem first_fiber_iff (p : Plane) (y : ObservationDual firstSpace.1) :
    observationMap firstSpace.1 p=y ↔ p.1=firstValue y := by
  constructor
  · intro h; exact congrArg firstValue h
  · intro h
    calc
      _ = firstLift (firstValue (observationMap firstSpace.1 p)) := (firstLift_value _).symm
      _ = firstLift (firstValue y) := congrArg firstLift h
      _ = y := firstLift_value y

theorem first_record_formula (y : ObservationDual firstSpace.1) :
    record firstSpace.1 (indicatorCost hyperbolaRegion) y=indicatorCost (Ioi (0:ℝ)) (firstValue y) := by
  rw [← hyperbola_projection]
  simp only [record,fiberInf,first_fiber_iff]

@[simp] theorem first_record_lift (t : ℝ) :
    record firstSpace.1 (indicatorCost hyperbolaRegion) (firstLift t)=indicatorCost (Ioi (0:ℝ)) t := by
  rw [first_record_formula,firstValue_lift]

theorem hyperbola_cost_closed : IsClosed (epigraph (indicatorCost hyperbolaRegion)) := by
  rw [epigraph_indicator]
  exact hyperbolaRegion_closed.prod isClosed_Ici

/-- The projection failure is witnessed by an actual finite subspace of E-prime. -/
theorem first_record_not_closed :
    ¬ IsClosed (epigraph (record firstSpace.1 (indicatorCost hyperbolaRegion))) := by
  intro h
  have hc := (lowerSemicontinuous_of_closed_real_epigraph h).comp_continuous firstLift.continuous
  have hc' : LowerSemicontinuous (indicatorCost (Ioi (0:ℝ))) := by
    simpa only [Function.comp_def,first_record_lift] using hc
  have he := (reconstruct_eq_iff_lowerSemicontinuous
    (jensen_of_convexCost (indicator_convex (convex_Ioi (0:ℝ))))
    (indicator_proper nonempty_Ioi)).mpr hc'
  have hz := congrArg (fun f : ℝ → ℝ≥0∞ => f 0) he
  rw [open_halfline_reconstruction] at hz
  simpa [indicatorCost] using hz

theorem first_record_boundary :
    record firstSpace.1 (indicatorCost hyperbolaRegion) (firstLift 0)=⊤ ∧
    affineHull (record firstSpace.1 (indicatorCost hyperbolaRegion)) (firstLift 0)=0 := by
  constructor
  · rw [first_record_lift]
    simp [indicatorCost]
  · apply le_antisymm _ bot_le
    have hminor : ∀ t, record firstSpace.1 (indicatorCost hyperbolaRegion) (firstLift t)≤
        indicatorCost (Ioi (0:ℝ)) t := by intro t; rw [first_record_lift]
    have h := affineHull_pullback_le firstLift hminor 0
    rw [hull_indicator (convex_Ioi 0) nonempty_Ioi,closure_Ioi] at h
    simpa only [indicatorCost,mem_Ici,le_refl,if_true] using h

def fullSpace : FiniteObservation Plane := ⟨⊤,inferInstance⟩

def fullFirst : fullSpace.1 := ⟨firstFunctional,by trivial⟩
def fullSecond : fullSpace.1 := ⟨secondFunctional,by trivial⟩

def fullInverse : ObservationDual fullSpace.1 →L[ℝ] Plane :=
  (observationEval fullSpace.1 fullFirst).prod (observationEval fullSpace.1 fullSecond)

theorem plane_dual_decomposition (l : Plane →L[ℝ] ℝ) :
    l=l (1,0) • firstFunctional+l (0,1) • secondFunctional := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p=p.1 • ((1:ℝ),0)+p.2 • ((0:ℝ),1) := by ext <;> simp
  calc
    l p = l (p.1 • ((1:ℝ),0)+p.2 • ((0:ℝ),1)) := congrArg l hp
    _ = p.1*l (1,0)+p.2*l (0,1) := by rw [map_add,map_smul,map_smul]; rfl
    _ = _ := by simp [firstFunctional,secondFunctional,mul_comm]

@[simp] theorem fullInverse_observation (p : Plane) : fullInverse (observationMap fullSpace.1 p)=p := by
  rfl

theorem observation_fullInverse (y : ObservationDual fullSpace.1) : observationMap fullSpace.1 (fullInverse y)=y := by
  apply LinearMap.ext
  intro l
  have hl : l=(l.1 (1,0)) • fullFirst+(l.1 (0,1)) • fullSecond :=
    Subtype.ext (plane_dual_decomposition l.1)
  rw [hl,map_add,map_smul,map_smul,map_add,map_smul,map_smul]
  rfl

theorem full_record_formula (f : Plane → ℝ≥0∞) (y : ObservationDual fullSpace.1) :
    record fullSpace.1 f y=f (fullInverse y) := by
  apply le_antisymm
  · have h := fiberInf_le (observationMap fullSpace.1) f (fullInverse y)
    simpa only [observation_fullInverse] using h
  · apply le_iInf
    intro x
    apply le_iInf
    intro hx
    have he : x=fullInverse y := by
      have ht := congrArg fullInverse hx
      simpa only [fullInverse_observation] using ht
    exact le_of_eq (congrArg f he).symm

theorem full_closed_cost_record_closed (f : Plane → ℝ≥0∞) (hf : IsClosed (epigraph f)) :
    IsClosed (epigraph (record fullSpace.1 f)) := by
  have h := hf.preimage (fullInverse.continuous.comp continuous_fst |>.prodMk continuous_snd)
  convert h using 1
  ext p
  simp only [mem_preimage,epigraph,mem_setOf_eq,full_record_formula,Function.comp_apply]

theorem full_hyperbola_record_fixed :
    affineHull (record fullSpace.1 (indicatorCost hyperbolaRegion))=
      record fullSpace.1 (indicatorCost hyperbolaRegion) := by
  apply le_antisymm (affineHull_le _)
  apply affineHull_maximal
  · exact fiberInf_proper (observationMap fullSpace.1) (indicator_proper hyperbolaRegion_nonempty)
  · exact lowerSemicontinuous_of_closed_real_epigraph
      (full_closed_cost_record_closed _ hyperbola_cost_closed)
  · exact fiberInf_convex (observationMap fullSpace.1).toLinearMap (indicator_convex hyperbolaRegion_convex)
  · exact le_rfl

/-- Actual F subset K=(R²)' in the task, with distinct values infinity and zero at
the same actual observation. Thus the final closure is indispensable. -/
theorem outer_relaxation_indispensable :
    fiberInf (restriction (show firstSpace.1≤fullSpace.1 from le_top))
      (affineHull (record fullSpace.1 (indicatorCost hyperbolaRegion))) (firstLift 0)=⊤ ∧
    affineHull (record firstSpace.1 (indicatorCost hyperbolaRegion)) (firstLift 0)=0 := by
  rw [full_hyperbola_record_fixed,← record_restriction]
  exact first_record_boundary

end MathGauge.ConvexCost
