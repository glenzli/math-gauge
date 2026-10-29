import CoordinateCWBridge
import CoordinateReindex
import OrderedAcyclicity
import GeneralSuspensionClassification
import TwoConeOpenCover

/-!
The actual MG-P001 coordinate spaces satisfy the local integral chain criterion.
The finite vertex type is reindexed into `Fin (card V)` by a proved homeomorphism,
so the original theorem remains quantified over `V : Type*`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set ContinuousMap TauCeti

namespace MathGauge.PublicProof.Topology.TauBridge

/-- A finite order used only for the orientation of actual simplex chains. -/
@[instance_reducible] def usedVertexLinearOrder {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) : LinearOrder (UsedVertex L) :=
  LinearOrder.lift' (Fintype.equivFin (UsedVertex L)) (Fintype.equivFin _).injective

/-- Nonempty geometric realization supplies an actual vertex of the complex. -/
theorem usedVertex_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) [Nonempty (Realization L)] :
    Nonempty (UsedVertex L) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (Realization L))
  obtain ⟨s, hs, _⟩ := x.2.2
  obtain ⟨v, hv⟩ := (L.isRelLowerSet_faces hs).1
  exact ⟨v, (L.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)⟩

/-- A chain condition on precisely the used vertices of a finite relabeling of `L`.
Its differential is the standard alternating integral simplex boundary and its
augmentation sums the coefficients of vertices. -/
def finiteOrderedAcyclic {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) : Prop :=
  letI := usedVertexLinearOrder (smallComplex L)
  QuasiIso (orderedSimplicialChainComplexAugmentation (usedComplex (smallComplex L)) ℤ)

/-- The actual two-cone space has the reduced singular homology criterion on its base. -/
theorem realizing_contractible_iff_reduced {V : Type} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) [Nonempty (Realization L)] :
    ContractibleSpace (Realization (realizing_complex L)) ↔
      ∀ n : ℕ, IsZero (ReducedIntegralHomology (Realization L) n) := by
  letI : TauCeti.CWType (Realization (realizing_complex L)) :=
    coordinateRealization_cwType (realizing_complex L)
  letI := pole_open_contractible L false
  letI := pole_open_contractible L true
  exact contractible_iff_model_reducedIntegralHomology_isZero
    (isOpen_pole_open L false) (isOpen_pole_open L true) (pole_open_cover L)
    (equatorial_equiv L)

/-- The suspension criterion for every finite vertex type, with no universe restriction
on the input and with the actual coordinate realization as domain. -/
theorem suspension_contractible_iff_finiteOrderedAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) [Nonempty (Realization L)] :
    ContractibleSpace (Susp (Realization L)) ↔ finiteOrderedAcyclic L := by
  let e : Realization L ≃ₜ Realization (smallComplex L) := smallCoordinateHomeomorph L
  letI : Nonempty (Realization (smallComplex L)) :=
    ⟨e (Classical.choice (inferInstance : Nonempty (Realization L)))⟩
  letI := usedVertex_nonempty (smallComplex L)
  letI := usedVertexLinearOrder (smallComplex L)
  rw [(Susp.mapHomeomorph e).contractibleSpace_iff,
    (suspension_realization_homeomorph (smallComplex L)).contractibleSpace_iff,
    realizing_contractible_iff_reduced]
  change (∀ n : ℕ, IsZero (ReducedIntegralHomology (Realization (smallComplex L)) n)) ↔
    QuasiIso (orderedSimplicialChainComplexAugmentation (usedComplex (smallComplex L)) ℤ)
  rw [orderedAugmentation_quasiIso_iff]
  apply forall_congr'
  intro n
  let f := (coordinateTauHomeomorph (smallComplex L)).toHomotopyEquiv
  exact ⟨fun h => h.of_iso (f.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) n).symm,
    fun h => h.of_iso (f.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) n)⟩

/-- The local integral-chain criterion under exactly MG-P001's original geometric
hypotheses. The nonemptiness of the link is derived from the inclusion equivalence. -/
theorem original_contractible_iff_finiteOrderedAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (K B : PreAbstractSimplicialComplex V) (v : V)
    (hBK : B ≤ K) (hv : {v} ∈ B) [ContractibleSpace (Punctured K v)]
    (e : Punctured B v ≃ₕ Realization B) (he : e.toFun = punctured_inclusion_map B v) :
    ContractibleSpace (Realization K) ↔ finiteOrderedAcyclic (vertex_link K v) := by
  obtain ⟨a, ha⟩ := vertex_link_has_vertex K B v hBK hv e he
  letI : Nonempty (Realization (vertex_link K v)) := ⟨vertex _ a ha⟩
  obtain ⟨f⟩ := original_suspension_classification K v B hBK hv e he
  exact f.contractibleSpace_iff.trans
    (suspension_contractible_iff_finiteOrderedAcyclic (vertex_link K v))

end MathGauge.PublicProof.Topology.TauBridge
