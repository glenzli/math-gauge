import ProfiniteReflection
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Function Topology
namespace MathGauge.ObservationTopology
universe u v w

def ClopenTests (X : Type u) [TopologicalSpace X] := {s : Set X // IsClopen s}

def observe (X : Type u) [TopologicalSpace X] (x : X) : ClopenTests X → Bool :=
  fun C => C.val.boolIndicator x

theorem observe_continuous (X : Type u) [TopologicalSpace X] : Continuous (observe X) :=
  continuous_pi (fun C => (continuous_boolIndicator_iff_isClopen C.val).2 C.property)

abbrev ObservationImage (X : Type u) [TopologicalSpace X] := range (observe X)

def observationMap (X : Type u) [TopologicalSpace X] : X → ObservationImage X :=
  Set.rangeFactorization (observe X)

theorem observationMap_continuous (X : Type u) [TopologicalSpace X] :
    Continuous (observationMap X) := (observe_continuous X).rangeFactorization

theorem observationMap_surjective (X : Type u) [TopologicalSpace X] :
    Surjective (observationMap X) := Set.rangeFactorization_surjective

instance observation_compact (X : Type u) [TopologicalSpace X] [CompactSpace X] :
    CompactSpace (ObservationImage X) :=
  isCompact_iff_compactSpace.mp (isCompact_range (observe_continuous X))

theorem observation_profinite (X : Type u) [TopologicalSpace X] [CompactSpace X] :
    CompactSpace (ObservationImage X) ∧ T2Space (ObservationImage X) ∧
      TotallyDisconnectedSpace (ObservationImage X) := ⟨inferInstance,inferInstance,inferInstance⟩

/-- The reverse implication is precisely the compact Hausdorff component /
quasicomponent theorem, used with its real hypotheses. -/
theorem observation_kernel (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x y : X) : observationMap X x=observationMap X y ↔
      ConnectedComponents.mk x=ConnectedComponents.mk y := by
  constructor
  · intro h
    have he : observe X x=observe X y := congrArg Subtype.val h
    apply ConnectedComponents.coe_eq_coe'.2
    rw [connectedComponent_eq_iInter_isClopen]
    apply mem_iInter.2
    intro S
    have hs := congrFun he ⟨S.val,S.property.1⟩
    have hy := S.property.2
    simpa [observe,Set.boolIndicator,hy] using hs
  · intro h
    apply Subtype.ext
    exact (observe_continuous X).image_eq_of_connectedComponent_eq x y
      (ConnectedComponents.coe_eq_coe.1 h)

def componentToObservation (X : Type u) [TopologicalSpace X] :
    ConnectedComponents X → ObservationImage X :=
  (observationMap_continuous X).connectedComponentsLift

theorem componentToObservation_continuous (X : Type u) [TopologicalSpace X] :
    Continuous (componentToObservation X) :=
  (observationMap_continuous X).connectedComponentsLift_continuous

theorem componentToObservation_bijective (X : Type u)
    [TopologicalSpace X] [CompactSpace X] [T2Space X] : Bijective (componentToObservation X) := by
  constructor
  · intro a b he
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y,rfl⟩ := ConnectedComponents.surjective_coe b
    exact (observation_kernel X x y).1 he
  · intro z
    obtain ⟨x,hx⟩ := observationMap_surjective X z
    exact ⟨ConnectedComponents.mk x,hx⟩

def componentObservationHomeomorph (X : Type u)
    [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ConnectedComponents X ≃ₜ ObservationImage X :=
  (Equiv.ofBijective (componentToObservation X) (componentToObservation_bijective X)).toHomeomorphOfContinuousClosed
    (componentToObservation_continuous X) (componentToObservation_continuous X).isClosedMap

theorem observation_fiber (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) : observationMap X ⁻¹' {observationMap X x}=connectedComponent x := by
  ext y
  exact (observation_kernel X y x).trans ConnectedComponents.coe_eq_coe'

/-- The actual image, not merely an abstract quotient, has the required
universal property. Finite discrete targets are a special case. -/
theorem observation_universal (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (Z : Type v) [TopologicalSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z]
    (f : X → Z) (hf : Continuous f) :
    ∃! g : ObservationImage X → Z, Continuous g ∧ g ∘ observationMap X=f := by
  let h := componentObservationHomeomorph X
  let g := hf.connectedComponentsLift ∘ h.symm
  refine ⟨g,⟨hf.connectedComponentsLift_continuous.comp h.symm.continuous,?_⟩,?_⟩
  · funext x
    change hf.connectedComponentsLift (h.symm (h (ConnectedComponents.mk x)))=f x
    rw [h.symm_apply_apply]
    rfl
  · intro g' hg'
    funext z
    obtain ⟨x,rfl⟩ := observationMap_surjective X z
    exact (congrFun hg'.2 x).trans (by
      change f x=hf.connectedComponentsLift (h.symm (h (ConnectedComponents.mk x)))
      rw [h.symm_apply_apply]
      rfl)

theorem component_product {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : connectedComponent (x,y)=connectedComponent x ×ˢ connectedComponent y := by
  apply Subset.antisymm
  · intro z hz
    exact ⟨continuous_fst.mapsTo_connectedComponent (x,y) hz,
      continuous_snd.mapsTo_connectedComponent (x,y) hz⟩
  · exact (isConnected_connectedComponent.prod isConnected_connectedComponent).subset_connectedComponent
      ⟨mem_connectedComponent,mem_connectedComponent⟩

def componentProductMap (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    ConnectedComponents (X × Y) → ConnectedComponents X × ConnectedComponents Y :=
  ((ConnectedComponents.continuous_coe.comp continuous_fst).prodMk
    (ConnectedComponents.continuous_coe.comp continuous_snd)).connectedComponentsLift

theorem componentProductMap_continuous (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] : Continuous (componentProductMap X Y) :=
  ((ConnectedComponents.continuous_coe.comp continuous_fst).prodMk
    (ConnectedComponents.continuous_coe.comp continuous_snd)).connectedComponentsLift_continuous

theorem componentProductMap_bijective (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] : Bijective (componentProductMap X Y) := by
  constructor
  · intro a b he
    obtain ⟨⟨x,y⟩,rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨⟨z,w⟩,rfl⟩ := ConnectedComponents.surjective_coe b
    apply ConnectedComponents.coe_eq_coe'.2
    rw [component_product]
    exact ⟨ConnectedComponents.coe_eq_coe'.1 (congrArg Prod.fst he),
      ConnectedComponents.coe_eq_coe'.1 (congrArg Prod.snd he)⟩
  · rintro ⟨a,b⟩
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y,rfl⟩ := ConnectedComponents.surjective_coe b
    exact ⟨ConnectedComponents.mk (x,y),rfl⟩

def componentProductHomeomorph (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y]
    [T2Space X] [T2Space Y] : ConnectedComponents (X × Y) ≃ₜ
      ConnectedComponents X × ConnectedComponents Y :=
  (Equiv.ofBijective (componentProductMap X Y) (componentProductMap_bijective X Y)).toHomeomorphOfContinuousClosed
    (componentProductMap_continuous X Y) (componentProductMap_continuous X Y).isClosedMap

def observationProductHomeomorph (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y]
    [T2Space X] [T2Space Y] : ObservationImage (X × Y) ≃ₜ ObservationImage X × ObservationImage Y :=
  (componentObservationHomeomorph (X × Y)).symm.trans
    ((componentProductHomeomorph X Y).trans
      ((componentObservationHomeomorph X).prodCongr (componentObservationHomeomorph Y)))

theorem observation_product_natural {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y]
    [T2Space X] [T2Space Y] (x : X) (y : Y) :
    observationProductHomeomorph X Y (observationMap (X × Y) (x,y))=
      (observationMap X x,observationMap Y y) := by
  change ((componentObservationHomeomorph X).prodCongr (componentObservationHomeomorph Y))
    ((componentProductHomeomorph X Y)
      ((componentObservationHomeomorph (X × Y)).symm
        ((componentObservationHomeomorph (X × Y)) (ConnectedComponents.mk (x,y)))))=_
  rw [Homeomorph.symm_apply_apply]
  rfl

def componentMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : ConnectedComponents X → ConnectedComponents Y :=
  (ConnectedComponents.continuous_coe.comp hf).connectedComponentsLift

theorem componentMap_continuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) :
    Continuous (componentMap f hf) :=
  (ConnectedComponents.continuous_coe.comp hf).connectedComponentsLift_continuous

theorem connected_fiber_component_preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hs : Surjective f)
    (hc : ∀ y,IsConnected (f ⁻¹' {y})) (x : X) :
    f ⁻¹' connectedComponent (f x)=connectedComponent x :=
  (hf.isClosedMap.isQuotientMap hf hs).preimage_connectedComponent hc x

theorem connected_fiber_preimage_connected {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hs : Surjective f)
    (hc : ∀ y,IsConnected (f ⁻¹' {y})) (y : Y) :
    IsConnected (f ⁻¹' connectedComponent y) := by
  obtain ⟨x,rfl⟩ := hs y
  rw [connected_fiber_component_preimage f hf hs hc x]
  exact isConnected_connectedComponent

theorem connected_fiber_component_bijective {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hs : Surjective f)
    (hc : ∀ y,IsConnected (f ⁻¹' {y})) : Bijective (componentMap f hf) := by
  constructor
  · intro a b he
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y,rfl⟩ := ConnectedComponents.surjective_coe b
    apply ConnectedComponents.coe_eq_coe'.2
    rw [← connected_fiber_component_preimage f hf hs hc y]
    exact ConnectedComponents.coe_eq_coe'.1 he
  · intro a
    obtain ⟨y,rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨x,rfl⟩ := hs y
    exact ⟨ConnectedComponents.mk x,rfl⟩

def connectedFiberObservationHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y]
    [T2Space X] [T2Space Y] (f : X → Y) (hf : Continuous f) (hs : Surjective f)
    (hc : ∀ y,IsConnected (f ⁻¹' {y})) : ObservationImage X ≃ₜ ObservationImage Y :=
  (componentObservationHomeomorph X).symm.trans
    (((Equiv.ofBijective (componentMap f hf)
      (connected_fiber_component_bijective f hf hs hc)).toHomeomorphOfContinuousClosed
      (componentMap_continuous f hf) (componentMap_continuous f hf).isClosedMap).trans
      (componentObservationHomeomorph Y))

end MathGauge.ObservationTopology
