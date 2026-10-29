import ProductLifting
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousOn

noncomputable section
open Set Filter Function Topology
namespace MathGauge.ProgressiveLifting
open MathGauge.ProductLifting
universe u v w z

theorem discrete_lifts (P : Type u) [TopologicalSpace P] [DiscreteTopology P] :
    Lifts.{u,v,w} P := by
  intro Y Z _ _ _ _ _ _ _ _ q f hq hqs hf
  obtain ⟨s,hs⟩ := hqs.hasRightInverse
  exact ⟨s ∘ f,continuous_of_discreteTopology,funext (fun x => hs (f x))⟩

theorem coproduct_lifts {ι : Type z} (P : ι → Type u) [∀ i,TopologicalSpace (P i)]
    (hP : ∀ i, Lifts.{u,v,w} (P i)) : Lifts.{max z u,v,w} (Σ i, P i) := by
  intro Y Z _ _ _ _ _ _ _ _ q f hq hqs hf
  have hl (i : ι) : ∃ g : P i → Y, Continuous g ∧ q ∘ g = f ∘ Sigma.mk i :=
    hP i Y Z q (f ∘ Sigma.mk i) hq hqs (hf.comp continuous_sigmaMk)
  choose g hg hge using hl
  refine ⟨fun x => g x.1 x.2,continuous_sigma hg,?_⟩
  funext ⟨i,x⟩
  exact congrFun (hge i) x

theorem finite_coproduct_profinite {ι : Type z} [Finite ι] (P : ι → Type u)
    [∀ i,TopologicalSpace (P i)] [∀ i,CompactSpace (P i)] [∀ i,T2Space (P i)]
    [∀ i,TotallyDisconnectedSpace (P i)] :
    CompactSpace (Σ i,P i) ∧ T2Space (Σ i,P i) ∧ TotallyDisconnectedSpace (Σ i,P i) :=
  ⟨inferInstance,inferInstance,inferInstance⟩

theorem retract_lifts {P : Type u} {Q : Type z} [TopologicalSpace P] [TopologicalSpace Q]
    (i : P → Q) (r : Q → P) (hi : Continuous i) (hr : Continuous r)
    (hri : r ∘ i=id) (hQ : Lifts.{z,v,w} Q) : Lifts.{u,v,w} P := by
  intro Y Z _ _ _ _ _ _ _ _ q f hq hqs hf
  obtain ⟨g,hg,hge⟩ := hQ Y Z q (f ∘ r) hq hqs (hf.comp hr)
  refine ⟨g ∘ i,hg.comp hi,?_⟩
  funext x
  exact (congrFun hge (i x)).trans (congrArg f (congrFun hri x))

/-- Continuous gluing along the actual open fibers of a discrete observation. -/
theorem continuous_from_fibers {P : Type u} {A : Type z} {Y : Type v}
    [TopologicalSpace P] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace Y]
    (f : P → A) (hf : Continuous f) (g : P → Y)
    (hg : ∀ a, Continuous (fun x : {x : P // f x=a} => g x.val)) : Continuous g := by
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (s := fun a => {x | f x=a})
  · intro a
    exact continuousOn_iff_continuous_restrict.2 (hg a)
  · intro a
    exact (isOpen_discrete ({a} : Set A)).preimage hf
  · ext x
    simp

theorem product_discrete_lifts (Q : Type u) (A : Type z)
    [TopologicalSpace Q] [TopologicalSpace A] [DiscreteTopology A]
    (hQ : Lifts.{u,v,w} Q) : Lifts.{max u z,v,w} (Q × A) := by
  intro Y Z _ _ _ _ _ _ _ _ q f hq hqs hf
  have hl (a : A) : ∃ g : Q → Y, Continuous g ∧ q ∘ g = (fun x => f (x,a)) :=
    hQ Y Z q (fun x => f (x,a)) hq hqs (hf.comp (continuous_id.prodMk continuous_const))
  choose g hg hge using hl
  refine ⟨fun x => g x.2 x.1,?_,?_⟩
  · apply continuous_from_fibers Prod.snd continuous_snd
    intro a
    have he : (fun x : {x : Q × A // x.2=a} => g x.val.2 x.val.1) =
        (fun x : {x : Q × A // x.2=a} => g a x.val.1) := by
      funext x; rw [x.property]
    rw [he]
    exact (hg a).comp (continuous_fst.comp continuous_subtype_val)
  · funext x
    exact congrFun (hge x.2) x.1

theorem finite_product_profinite (Q : Type u) (A : Type z)
    [TopologicalSpace Q] [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    [TopologicalSpace A] [DiscreteTopology A] [Finite A] :
    CompactSpace (Q × A) ∧ T2Space (Q × A) ∧ TotallyDisconnectedSpace (Q × A) :=
  ⟨inferInstance,inferInstance,inferInstance⟩

theorem ultrafilter_profinite (D : Type u) : CompactSpace (Ultrafilter D) ∧
    T2Space (Ultrafilter D) ∧ TotallyDisconnectedSpace (Ultrafilter D) :=
  ⟨inferInstance,inferInstance,inferInstance⟩

def counit (P : Type u) [TopologicalSpace P] : Ultrafilter P → P := Ultrafilter.extend id

theorem counit_continuous (P : Type u) [TopologicalSpace P] [CompactSpace P] [T2Space P] :
    Continuous (counit P) := continuous_ultrafilter_extend _

theorem counit_surjective (P : Type u) [TopologicalSpace P] [CompactSpace P] [T2Space P] :
    Surjective (counit P) := by
  intro p
  exact ⟨pure p,ultrafilter_extend_pure id p⟩

theorem projective_has_counit_section (P : Type u) [TopologicalSpace P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : Lifts.{u,u,u} P) :
    ∃ i : P → Ultrafilter P, Continuous i ∧ counit P ∘ i=id :=
  hP (Ultrafilter P) P (counit P) id (counit_continuous P) (counit_surjective P) continuous_id

theorem counit_section_projective (P : Type u) [TopologicalSpace P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (h : ∃ i : P → Ultrafilter P, Continuous i ∧ counit P ∘ i=id) : Lifts.{u,v,w} P := by
  obtain ⟨i,hi,hri⟩ := h
  exact retract_lifts i (counit P) hi (counit_continuous P) hri (ultrafilter_lifts P)

theorem projective_iff_counit_retract (P : Type u) [TopologicalSpace P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] :
    Lifts.{u,u,u} P ↔ ∃ i : P → Ultrafilter P, Continuous i ∧ counit P ∘ i=id :=
  ⟨projective_has_counit_section P,counit_section_projective P⟩

/-- Finite range, rather than projectivity of P, suffices. The set-theoretic
choice is made on the finite discrete actual range, so its continuity is proved. -/
theorem finite_range_lift {P : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace P] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    (q : Y → Z) (f : P → Z) (hq : Surjective q) (hf : Continuous f)
    (hfin : (range f).Finite) : ∃ g : P → Y, Continuous g ∧ q ∘ g=f := by
  letI : Finite (range f) := hfin.to_subtype
  let s : range f → Y := fun z => (hq z.val).choose
  have hs : Continuous s := continuous_of_discreteTopology
  let g := s ∘ Set.rangeFactorization f
  refine ⟨g,hs.comp hf.rangeFactorization,?_⟩
  funext x
  exact (hq (f x)).choose_spec

section Fibers
variable {P : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace P] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
variable (q : Y → Z) (f : P → Z)

def LiftSpace := {g : C(P,Y) // ∀ x, q (g x)=f x}
def FiberMaps := ∀ z : range f, C({x : P // f x=z.val},{y : Y // q y=z.val})

def restrictLift (g : LiftSpace q f) : FiberMaps q f := fun z =>
  ⟨fun x => ⟨g.val x.val,(g.property x.val).trans x.property⟩,
    (g.val.continuous.comp continuous_subtype_val).subtype_mk _⟩

def glue (h : FiberMaps q f) (x : P) : Y :=
  (h ⟨f x,⟨x,rfl⟩⟩ ⟨x,rfl⟩).val

theorem glue_restrict (h : FiberMaps q f) (z : range f) (x : {x : P // f x=z.val}) :
    glue q f h x.val = (h z x).val := by
  rcases z with ⟨z,hz⟩
  rcases x with ⟨x,hx⟩
  dsimp at hx ⊢
  subst z
  rfl

theorem range_fiber_open (hf : Continuous f) (hfin : (range f).Finite) (z : range f) :
    IsOpen {x : P | f x=z.val} := by
  letI : Finite (range f) := hfin.to_subtype
  have h := (isOpen_discrete ({z} : Set (range f))).preimage hf.rangeFactorization
  convert h using 1
  ext x
  simp only [mem_setOf_eq,mem_preimage,mem_singleton_iff,Subtype.ext_iff]
  rfl

theorem glue_continuous (hf : Continuous f) (hfin : (range f).Finite) (h : FiberMaps q f) :
    Continuous (glue q f h) := by
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (s := fun z : range f => {x | f x=z.val})
  · intro z
    apply continuousOn_iff_continuous_restrict.2
    have he : (fun x : {x : P // f x=z.val} => glue q f h x.val) =
        (fun x => (h z x).val) := funext (glue_restrict q f h z)
    change Continuous (fun x : {x : P // f x=z.val} => glue q f h x.val)
    rw [he]
    exact continuous_subtype_val.comp (h z).continuous
  · exact range_fiber_open f hf hfin
  · ext x
    simp only [mem_iUnion,mem_setOf_eq,mem_univ,iff_true]
    exact ⟨⟨f x,⟨x,rfl⟩⟩,rfl⟩

def liftFiberEquiv (hf : Continuous f) (hfin : (range f).Finite) :
    LiftSpace q f ≃ FiberMaps q f where
  toFun := restrictLift q f
  invFun h := ⟨⟨glue q f h,glue_continuous q f hf hfin h⟩,fun x =>
    (h ⟨f x,⟨x,rfl⟩⟩ ⟨x,rfl⟩).property⟩
  left_inv g := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    rfl
  right_inv h := by
    funext z
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact glue_restrict q f h z x

end Fibers

/-- A labelled clopen partition allows empty blocks, while every point has
exactly one label. This definition does not assume the desired map exists. -/
def ClopenPartitions (X : Type u) (A : Type v) [TopologicalSpace X] :=
  {B : A → Set X // (∀ a, IsClopen (B a)) ∧ ∀ x, ∃! a, x ∈ B a}

def mapPartition {X : Type u} {A : Type v} [TopologicalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] (g : C(X,A)) : ClopenPartitions X A :=
  ⟨fun a => g ⁻¹' {a},fun a => ⟨isClosed_singleton.preimage g.continuous,
    (isOpen_discrete _).preimage g.continuous⟩,
    fun x => ⟨g x,rfl,fun a ha => ha.symm⟩⟩

def partitionMap {X : Type u} {A : Type v} [TopologicalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] (B : ClopenPartitions X A) : X → A :=
  fun x => (B.property.2 x).exists.choose

theorem partitionMap_fiber {X : Type u} {A : Type v} [TopologicalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] (B : ClopenPartitions X A) (x : X) (a : A) :
    partitionMap B x=a ↔ x ∈ B.val a := by
  have hm := (B.property.2 x).exists.choose_spec
  constructor
  · intro h
    exact h ▸ hm
  · intro h
    exact (B.property.2 x).unique hm h

theorem partitionMap_continuous {X : Type u} {A : Type v} [TopologicalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] (B : ClopenPartitions X A) :
    Continuous (partitionMap B) := by
  apply continuous_def.2
  intro U _
  have he : partitionMap B ⁻¹' U = ⋃ a ∈ U, B.val a := by
    ext x
    simp only [mem_preimage,mem_iUnion]
    constructor
    · intro hx
      exact ⟨partitionMap B x,hx,(partitionMap_fiber B x _).1 rfl⟩
    · rintro ⟨a,ha,hx⟩
      rwa [(partitionMap_fiber B x a).2 hx]
  rw [he]
  exact isOpen_iUnion (fun a => isOpen_iUnion (fun _ => (B.property.1 a).2))

/-- Full inverse classification of continuous maps into a finite discrete
fiber by its labelled clopen partition; the proof also works for arbitrary
discrete labels. Finite Hausdorff fibers supply this topology automatically. -/
def continuousMapPartitionEquiv (X : Type u) (A : Type v) [TopologicalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] : C(X,A) ≃ ClopenPartitions X A where
  toFun := mapPartition
  invFun B := ⟨partitionMap B,partitionMap_continuous B⟩
  left_inv g := by
    apply ContinuousMap.ext
    intro x
    exact (partitionMap_fiber (mapPartition g) x (g x)).2 rfl
  right_inv B := by
    apply Subtype.ext
    funext a
    ext x
    exact partitionMap_fiber B x a

def finiteLiftPartitionEquiv {P : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace P] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space Y] [T2Space Z] (q : Y → Z) (f : P → Z)
    (hf : Continuous f) (hfin : (range f).Finite)
    [∀ z : range f, Finite {y : Y // q y=z.val}] :
    LiftSpace q f ≃ ∀ z : range f,
      ClopenPartitions {x : P // f x=z.val} {y : Y // q y=z.val} :=
  (liftFiberEquiv q f hf hfin).trans (Equiv.piCongrRight (fun z =>
    continuousMapPartitionEquiv {x : P // f x=z.val} {y : Y // q y=z.val}))

end MathGauge.ProgressiveLifting
