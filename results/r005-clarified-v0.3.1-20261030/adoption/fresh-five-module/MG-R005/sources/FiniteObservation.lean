import ConvexCost
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.ENNReal.Inv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set
open scoped ENNReal

namespace MathGauge.ConvexCost

section Fiber
variable {X Y Z : Type*}

def fiberInf (q : X → Y) (f : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ⨅ x, ⨅ (_ : q x = y), f x

theorem fiberInf_le (q : X → Y) (f : X → ℝ≥0∞) (x : X) :
    fiberInf q f (q x) ≤ f x := iInf_le_of_le x (iInf_le _ rfl)

theorem fiberInf_empty (q : X → Y) (f : X → ℝ≥0∞) (y : Y)
    (h : ∀ x, q x ≠ y) : fiberInf q f y = ⊤ := by
  simp [fiberInf, h]

theorem fiberInf_comp (q : X → Y) (r : Y → Z) (f : X → ℝ≥0∞) (z : Z) :
    fiberInf (r ∘ q) f z = fiberInf r (fiberInf q f) z := by
  apply le_antisymm
  · apply le_iInf
    intro y
    apply le_iInf
    intro hy
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    exact iInf_le_of_le x <| iInf_le_of_le (by simpa [Function.comp_apply, hx] using hy) le_rfl
  · apply le_iInf
    intro x
    apply le_iInf
    intro hx
    exact iInf_le_of_le (q x) <| iInf_le_of_le hx (fiberInf_le q f x)

theorem fiberInf_proper (q : X → Y) {f : X → ℝ≥0∞} (h : ∃ x, f x ≠ ⊤) :
    ∃ y, fiberInf q f y ≠ ⊤ := by
  obtain ⟨x,hx⟩ := h
  exact ⟨q x, ne_top_of_le_ne_top hx (fiberInf_le q f x)⟩

end Fiber

section FiberConvex
variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

theorem fiberInf_jensen (q : E →ₗ[ℝ] V) {f : E → ℝ≥0∞} (hf : JensenConvex f) :
    JensenConvex (fiberInf q f) := by
  intro y z a b ha hb hab
  by_cases ha0 : a = 0
  · subst a
    have : b = 1 := by linarith
    subst b
    simp
  by_cases hb0 : b = 0
  · subst b
    have : a = 1 := by linarith
    subst a
    simp
  have ha' : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne ha (Ne.symm ha0))).ne'
  have hb' : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hb (Ne.symm hb0))).ne'
  simp only [fiberInf, ENNReal.mul_iInf_of_ne ha' ENNReal.ofReal_ne_top,
    ENNReal.mul_iInf_of_ne hb' ENNReal.ofReal_ne_top]
  apply ENNReal.le_iInf₂_add_iInf₂
  intro x hx w hw
  apply iInf_le_of_le (a • x + b • w)
  apply iInf_le_of_le (by simp [map_add, map_smul, hx, hw])
  exact hf x w a b ha hb hab

theorem fiberInf_convex (q : E →ₗ[ℝ] V) {f : E → ℝ≥0∞} (hf : ConvexCost f) :
    ConvexCost (fiberInf q f) := convexCost_of_jensen (fiberInf_jensen q (jensen_of_convexCost hf))

end FiberConvex

section Pullback
variable {E V : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V]

theorem affineHull_pullback_le (r : E →L[ℝ] V) {g : V → ℝ≥0∞} {f : E → ℝ≥0∞}
    (h : ∀ x, g (r x) ≤ f x) (x : E) : affineHull g (r x) ≤ affineHull f x := by
  apply iSup_le
  intro l
  apply iSup_le
  intro b
  apply iSup_le
  intro hl
  exact affine_minorant_le_hull (l.comp r) b (fun z => (hl (r z)).trans (h z)) x

theorem affineHull_fiber_pullback_le (q : E →L[ℝ] V) (f : E → ℝ≥0∞) (x : E) :
    affineHull (fiberInf q f) (q x) ≤ affineHull f x :=
  affineHull_pullback_le q (fiberInf_le q f) x

end Pullback

section Observations
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The algebraic dual with its topology of pointwise evaluation. In finite dimension
this is the usual Hausdorff finite-dimensional vector-space topology. -/
abbrev ObservationDual (F : Submodule ℝ (E →L[ℝ] ℝ)) :=
  Module.Dual ℝ F

instance observationDualTopology (F : Submodule ℝ (E →L[ℝ] ℝ)) :
    TopologicalSpace (ObservationDual F) :=
  WeakBilin.instTopologicalSpace (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] Module.Dual ℝ F)

instance observationDualTopologicalAddGroup (F : Submodule ℝ (E →L[ℝ] ℝ)) :
    IsTopologicalAddGroup (ObservationDual F) :=
  WeakBilin.instIsTopologicalAddGroup
    (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] Module.Dual ℝ F)

instance observationDualContinuousSMul (F : Submodule ℝ (E →L[ℝ] ℝ)) :
    ContinuousSMul ℝ (ObservationDual F) :=
  inferInstanceAs (ContinuousSMul ℝ
    (WeakBilin (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] Module.Dual ℝ F)))

instance observationDualLocallyConvex (F : Submodule ℝ (E →L[ℝ] ℝ)) :
    LocallyConvexSpace ℝ (ObservationDual F) :=
  inferInstanceAs (LocallyConvexSpace ℝ
    (WeakBilin (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] Module.Dual ℝ F)))

instance observationDualT2 (F : Submodule ℝ (E →L[ℝ] ℝ)) : T2Space (ObservationDual F) :=
  (WeakBilin.isEmbedding (B := (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] Module.Dual ℝ F))
    (fun _ _ h => h)).t2Space

instance observationDualFinite (F : Submodule ℝ (E →L[ℝ] ℝ)) [FiniteDimensional ℝ F] :
    FiniteDimensional ℝ (ObservationDual F) :=
  inferInstanceAs (FiniteDimensional ℝ (Module.Dual ℝ F))

def observationMap (F : Submodule ℝ (E →L[ℝ] ℝ)) : E →L[ℝ] ObservationDual F where
  toFun x :=
    { toFun := fun l => l.1 x
      map_add' := fun l m => by simp
      map_smul' := fun a l => by simp }
  map_add' x y := by ext l; exact map_add l.1 x y
  map_smul' a x := by ext l; exact map_smul l.1 a x
  cont := WeakBilin.continuous_of_continuous_eval _ (fun l => l.1.continuous)

def observationEval (F : Submodule ℝ (E →L[ℝ] ℝ)) (l : F) : ObservationDual F →L[ℝ] ℝ :=
  WeakBilin.eval (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] Module.Dual ℝ F) l

@[simp] theorem observationMap_apply (F : Submodule ℝ (E →L[ℝ] ℝ)) (x : E) (l : F) :
    observationMap F x l = l.1 x := rfl

@[simp] theorem observationEval_apply (F : Submodule ℝ (E →L[ℝ] ℝ)) (l : F)
    (y : ObservationDual F) : observationEval F l y = y l := rfl

def restriction {F K : Submodule ℝ (E →L[ℝ] ℝ)} (h : F ≤ K) :
    ObservationDual K →L[ℝ] ObservationDual F where
  toFun y := y.comp (Submodule.inclusion h)
  map_add' y z := by ext l; rfl
  map_smul' a y := by ext l; rfl
  cont := WeakBilin.continuous_of_continuous_eval _
    (fun l => (observationEval K (Submodule.inclusion h l)).continuous)

@[simp] theorem restriction_observationMap {F K : Submodule ℝ (E →L[ℝ] ℝ)} (h : F ≤ K)
    (x : E) : restriction h (observationMap K x) = observationMap F x := by ext l; rfl

def record (F : Submodule ℝ (E →L[ℝ] ℝ)) (f : E → ℝ≥0∞) : ObservationDual F → ℝ≥0∞ :=
  fiberInf (observationMap F) f

theorem record_restriction {F K : Submodule ℝ (E →L[ℝ] ℝ)} (h : F ≤ K)
    (f : E → ℝ≥0∞) (y : ObservationDual F) :
    record F f y = fiberInf (restriction h) (record K f) y := by
  simp only [record]
  rw [← fiberInf_comp]
  rfl

theorem relaxed_record_mono {F K : Submodule ℝ (E →L[ℝ] ℝ)} (h : F ≤ K)
    (f : E → ℝ≥0∞) (z : ObservationDual K) :
    affineHull (record F f) (restriction h z) ≤ affineHull (record K f) z := by
  apply affineHull_pullback_le
  intro w
  rw [record_restriction h]
  exact fiberInf_le _ _ w

abbrev FiniteObservation (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] :=
  {F : Submodule ℝ (E →L[ℝ] ℝ) // FiniteDimensional ℝ F}

instance finiteObservationFinite (F : FiniteObservation E) : FiniteDimensional ℝ F.1 := F.2

def reconstruct (f : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ⨆ F : FiniteObservation E, affineHull (record F.1 f) (observationMap F.1 x)

/-- Every finite-observation reconstruction equals the global affine hull. -/
theorem reconstruct_eq_affineHull (f : E → ℝ≥0∞) : reconstruct f = affineHull f := by
  funext x
  apply le_antisymm
  · exact iSup_le fun F => affineHull_fiber_pullback_le (observationMap F.1) f x
  · apply iSup_le
    intro l
    apply iSup_le
    intro b
    apply iSup_le
    intro hl
    let F : Submodule ℝ (E →L[ℝ] ℝ) := Submodule.span ℝ {l}
    have hF : FiniteDimensional ℝ F := inferInstance
    let lF : F := ⟨l, Submodule.mem_span_singleton_self l⟩
    have hlocal (y : ObservationDual F) :
        ENNReal.ofReal (observationEval F lF y + b) ≤ record F f y := by
      apply le_iInf
      intro z
      apply le_iInf
      intro hz
      have he : observationEval F lF y = l z := by
        rw [← hz]
        rfl
      rw [he]
      exact hl z
    exact le_iSup_of_le (⟨F,hF⟩ : FiniteObservation E)
      (affine_minorant_le_hull (observationEval F lF) b hlocal (observationMap F x))

theorem finite_observations_directed (F K : FiniteObservation E) :
    ∃ L : FiniteObservation E, F.1 ≤ L.1 ∧ K.1 ≤ L.1 := by
  exact ⟨⟨F.1 ⊔ K.1, inferInstance⟩, le_sup_left, le_sup_right⟩

theorem reconstruct_directed (f : E → ℝ≥0∞) :
    Directed (· ≤ ·) (fun F : FiniteObservation E =>
      fun x => affineHull (record F.1 f) (observationMap F.1 x)) := by
  intro F K
  obtain ⟨L,hF,hK⟩ := finite_observations_directed F K
  refine ⟨L, ?_, ?_⟩
  · intro x
    simpa using relaxed_record_mono hF f (observationMap L.1 x)
  · intro x
    simpa using relaxed_record_mono hK f (observationMap L.1 x)

variable [LocallyConvexSpace ℝ E]

/-- MG-R005 main theorem, with genuine finite-dimensional observation spaces and
all extended values and empty fibers retained. -/
theorem finite_observation_reconstruction (f : E → ℝ≥0∞)
    (hf : JensenConvex f) (hp : ∃ x, f x ≠ ⊤) :
    LowerSemicontinuous (reconstruct f) ∧ JensenConvex (reconstruct f) ∧
    reconstruct f ≤ f ∧ (∃ x, reconstruct f x ≠ ⊤) ∧
    (∀ h : E → ℝ≥0∞, LowerSemicontinuous h → JensenConvex h → h ≤ f → h ≤ reconstruct f) ∧
    (∀ F : FiniteObservation E, JensenConvex (record F.1 f)) := by
  rw [reconstruct_eq_affineHull]
  refine ⟨affineHull_lowerSemicontinuous f, jensen_of_convexCost (affineHull_convex f),
    affineHull_le f, ?_, ?_, ?_⟩
  · obtain ⟨x,hx⟩ := hp
    exact ⟨x, ne_top_of_le_ne_top hx (affineHull_le f x)⟩
  · intro h hc hv hh
    exact affineHull_maximal hp hc (convexCost_of_jensen hv) hh
  · intro F
    exact fiberInf_jensen (observationMap F.1).toLinearMap hf

theorem reconstruct_eq_iff_lowerSemicontinuous {f : E → ℝ≥0∞}
    (hf : JensenConvex f) (hp : ∃ x, f x ≠ ⊤) :
    reconstruct f = f ↔ LowerSemicontinuous f := by
  constructor
  · intro he
    simpa [he] using (finite_observation_reconstruction f hf hp).1
  · intro hc
    rw [reconstruct_eq_affineHull]
    exact le_antisymm (affineHull_le f) (affineHull_maximal hp hc (convexCost_of_jensen hf) le_rfl)

end Observations
end MathGauge.ConvexCost
