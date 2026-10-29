import UltrafilterAlgebras
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Separation.Regular

noncomputable section
open Set Filter Function Topology
namespace MathGauge.UltrafilterAlgebras
universe u v

/-- The canonical algebra on a finite discrete set. -/
def finiteAlgebra (A : Type v) [Finite A] : Algebra A := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact fromTopology

/-- This algebra has exactly the task's finite-fibre rule. -/
theorem finiteAlgebra_limit_iff (A : Type v) [Finite A] (U : Ultrafilter A) (x : A) :
    (finiteAlgebra A).limit U = x ↔ ({x} : Set A) ∈ U := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  change Ultrafilter.extend id U = x ↔ ({x} : Set A) ∈ U
  rw [ultrafilter_extend_eq_iff]
  simp only [Ultrafilter.map_id, nhds_discrete, Filter.le_pure_iff]
  rfl

theorem finiteAlgebra_topology (A : Type v) [Finite A] :
    (finiteAlgebra A).topology = (⊥ : TopologicalSpace A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact topology_roundtrip

/-- Actual connected-component quotient in the constructed topology. -/
abbrev Reflection {X : Type u} (a : Algebra X) := @ConnectedComponents X a.topology

instance reflection_topology {X : Type u} (a : Algebra X) : TopologicalSpace (Reflection a) :=
  @ConnectedComponents.instTopologicalSpace X a.topology

instance reflection_compact {X : Type u} (a : Algebra X) : CompactSpace (Reflection a) :=
  @Quotient.compactSpace X a.topology (@connectedComponentSetoid X a.topology) (constructed_compact a)

instance reflection_t2 {X : Type u} (a : Algebra X) : T2Space (Reflection a) :=
  @ConnectedComponents.t2 X a.topology (constructed_t2 a) (constructed_compact a)

instance reflection_totallyDisconnected {X : Type u} (a : Algebra X) :
    TotallyDisconnectedSpace (Reflection a) :=
  @ConnectedComponents.totallyDisconnectedSpace X a.topology

def project {X : Type u} (a : Algebra X) : X → Reflection a :=
  @ConnectedComponents.mk X a.topology

theorem project_continuous {X : Type u} (a : Algebra X) :
    @Continuous X (Reflection a) a.topology inferInstance (project a) :=
  @ConnectedComponents.continuous_coe X a.topology

theorem project_surjective {X : Type u} (a : Algebra X) : Surjective (project a) := by
  letI := a.topology
  exact ConnectedComponents.surjective_coe

/-- The full universal property, for every profinite target in any universe. -/
theorem reflection_universal {X : Type u} (a : Algebra X) (Z : Type v)
    [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z]
    (f : X → Z) (hf : @Continuous X Z a.topology inferInstance f) :
    ∃! g : Reflection a → Z, Continuous g ∧ g ∘ project a = f := by
  letI := a.topology
  refine ⟨hf.connectedComponentsLift,⟨hf.connectedComponentsLift_continuous,rfl⟩,?_⟩
  intro g hg
  exact hf.connectedComponentsLift_unique g hg.2

/-- Exact fibres, not only a surjective profinite map. -/
theorem project_fibre {X : Type u} (a : Algebra X) (x : X) :
    (project a) ⁻¹' {project a x} = @connectedComponent X a.topology x := by
  letI := a.topology
  exact connectedComponents_preimage_singleton

/-- A finite skeleton of all algebraic finite observations. -/
def FiniteIndistinguishable {X : Type u} (a : Algebra X) (x y : X) : Prop :=
  ∀ (n : ℕ) (f : X → Fin n), Hom a (finiteAlgebra (Fin n)) f → f x = f y

/-- Every finite test in every universe is constant on each constructed fibre. -/
theorem finite_observation_on_fibre {X : Type u} (a : Algebra X) (A : Type v) [Finite A]
    (f : X → A) (hf : Hom a (finiteAlgebra A) f) {x y : X}
    (hxy : project a x = project a y) : f x = f y := by
  letI := a.topology
  letI := (finiteAlgebra A).topology
  letI : T2Space A := constructed_t2 (finiteAlgebra A)
  have hc := (hom_iff_continuous a (finiteAlgebra A) f).mp hf
  exact hc.image_eq_of_connectedComponent_eq x y (ConnectedComponents.coe_eq_coe.mp hxy)


/-- Every finite algebra observation has the required unique continuous factorization. -/
theorem finite_observation_factorization {X : Type u} (a : Algebra X) (A : Type v) [Finite A]
    (f : X → A) (hf : Hom a (finiteAlgebra A) f) :
    letI := (finiteAlgebra A).topology
    ∃! g : Reflection a → A, Continuous g ∧ g ∘ project a = f := by
  letI := (finiteAlgebra A).topology
  letI : CompactSpace A := constructed_compact (finiteAlgebra A)
  letI : T2Space A := constructed_t2 (finiteAlgebra A)
  exact reflection_universal a A f ((hom_iff_continuous a (finiteAlgebra A) f).mp hf)

/-- In a compact Hausdorff space components are exactly finite-observation fibres.
The reverse implication explicitly invokes the component/quasicomponent equality. -/
theorem project_eq_iff_finite {X : Type u} (a : Algebra X) (x y : X) :
    project a x = project a y ↔ FiniteIndistinguishable a x y := by
  letI := a.topology
  letI : CompactSpace X := constructed_compact a
  letI : T2Space X := constructed_t2 a
  constructor
  · intro h n f hf
    exact finite_observation_on_fibre a (Fin n) f hf h
  · intro h
    apply ConnectedComponents.coe_eq_coe'.mpr
    rw [connectedComponent_eq_iInter_isClopen]
    apply mem_iInter.mpr
    intro S
    by_contra hx
    letI := (finiteAlgebra (Fin 2)).topology
    letI : T2Space (Fin 2) := constructed_t2 (finiteAlgebra (Fin 2))
    let g : Bool → Fin 2 := fun b => if b then 1 else 0
    let f : X → Fin 2 := g ∘ S.val.boolIndicator
    have hc : Continuous f :=
      (continuous_of_discreteTopology : Continuous g).comp
        ((continuous_boolIndicator_iff_isClopen S.val).mpr S.property.1)
    have hf : Hom a (finiteAlgebra (Fin 2)) f :=
      (hom_iff_continuous a (finiteAlgebra (Fin 2)) f).mpr hc
    have he := h 2 f hf
    have hy := S.property.2
    simp [f,g,Set.boolIndicator,hx,hy] at he

/-- Faithfulness is an exact algebraic finite-observation condition. -/
theorem project_injective_iff_observations {X : Type u} (a : Algebra X) :
    Injective (project a) ↔ ∀ x y, FiniteIndistinguishable a x y → x = y := by
  constructor
  · intro h x y hxy
    exact h ((project_eq_iff_finite a x y).mpr hxy)
  · intro h x y hxy
    exact h x y ((project_eq_iff_finite a x y).mp hxy)

/-- The same condition is precisely total disconnectedness of the reconstructed topology. -/
theorem project_injective_iff_totallyDisconnected {X : Type u} (a : Algebra X) :
    Injective (project a) ↔ @TotallyDisconnectedSpace X a.topology := by
  letI := a.topology
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  constructor
  · intro h x
    ext y
    constructor
    · intro hy
      exact h (ConnectedComponents.coe_eq_coe'.mpr hy)
    · rintro rfl
      exact mem_connectedComponent
  · intro h x y hxy
    have hm := ConnectedComponents.coe_eq_coe'.mp hxy
    simpa only [h y, mem_singleton_iff] using hm

theorem finite_observations_separate_iff {X : Type u} (a : Algebra X) :
    (∀ x y, FiniteIndistinguishable a x y → x = y) ↔
      @TotallyDisconnectedSpace X a.topology :=
  (project_injective_iff_observations a).symm.trans (project_injective_iff_totallyDisconnected a)

end MathGauge.UltrafilterAlgebras
