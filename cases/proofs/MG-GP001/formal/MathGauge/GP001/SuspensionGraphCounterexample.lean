import MathGauge.GP001.GraphSuspensionFaces
import MathGauge.GP001.GraphNonEquivalence
import MathGauge.GP001.RealizationCone
import MathGauge.GP001.SimplicialHomotopy
import MathGauge.GP001.WedgeHomotopy
import MathGauge.GP001.IsolatedVertex
import CoordinateReindex
import SuspensionRealization

/-! Actual suspension equivalence for the two explicit finite graphs. The
second triangular circle splits off by its vertex link; its two possible
attachment positions retract to the same finite suspended core. -/
namespace MathGauge.GP001
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open Finset Set ContinuousMap MathGauge.PublicProof.Topology unitInterval
open MathGauge.PublicProof.Topology.TauBridge

def graphCoreVertex (b : Bool) : Realization graphCore :=
  vertex _ _ (graph_core_vertex b)

def graphCoreInclusion (b : Bool) : C(Realization graphCore, Realization (graphDeletion b)) :=
  realizationInclusion (graph_core_le b)

def graphCoreRetraction (b : Bool) : C(Realization (graphDeletion b), Realization graphCore) :=
  ((Homeomorph.setCongr (congrArg carrier (graph_core_eq b))) :
    C(Realization (deletion (graphDeletion b) (Sum.inr 4)), Realization graphCore)).comp
    (foldRetraction (graphDeletion b) (Sum.inr 4) (Sum.inr (graphAttachment b))
      (graph_fold_distinct b) (graph_fold_dominates b))

@[simp] theorem graphCoreRetraction_inclusion (b : Bool) (x : Realization graphCore) :
    graphCoreRetraction b (graphCoreInclusion b x) = x := by
  apply Subtype.ext
  have hx : x.1 (Sum.inr 4) = 0 := by
    apply (mem_carrier_deletion_iff.mp (show x.1 ∈ carrier
      (deletion (graphDeletion b) (Sum.inr 4)) from by rw [graph_core_eq]; exact x.2)).2
  exact foldCoordinates_of_zero (Sum.inr 4) (Sum.inr (graphAttachment b)) 1 x.1 hx

def graphCoreHomotopy (b : Bool) : (ContinuousMap.id (Realization (graphDeletion b))).Homotopy
    ((graphCoreInclusion b).comp (graphCoreRetraction b)) :=
  foldHomotopy (graphDeletion b) (Sum.inr 4) (Sum.inr (graphAttachment b))
    (graph_fold_distinct b) (graph_fold_dominates b)

private theorem graphCoreHomotopy_fixes (b : Bool) (t : I) :
    graphCoreHomotopy b (t, graphCoreInclusion b (graphCoreVertex b)) =
      graphCoreInclusion b (graphCoreVertex b) := by
  apply foldHomotopy_fixes
  change (Pi.single (Sum.inr (graphAttachment b)) (1 : ℝ) : GraphVertex → ℝ) (.inr 4) = 0
  simp only [Pi.single_apply, graph_fold_distinct b, ite_false]

def graphLinkNullhomotopy (b : Bool) :
    (link_to_deletion (graphSusp b) (Sum.inr 3)).Homotopy
      (ContinuousMap.const _ (graphCoreInclusion b (graphCoreVertex b))) :=
  inclusionNullhomotopy (vertex_link_le_deletion (graphSusp b) (Sum.inr 3))
    (Sum.inr (graphAttachment b)) ((graph_core_le b) (graph_core_vertex b))
    (graph_link_null_faces b)

/-- Splitting the actual link and folding the remaining dangling edge. -/
def graphSuspensionWedge (b : Bool) :
    Realization (graphSusp b) ≃ₕ
      BaseSuspensionWedge (L := Realization (graphLink b)) (graphCoreVertex b) :=
  (realizationNullLinkWedge (graphSusp b) (Sum.inr 3)
    (graphCoreInclusion b (graphCoreVertex b)) (graphLinkNullhomotopy b)).trans
      (wedgeSDREquiv (graphCoreRetraction b) (graphCoreInclusion b)
        (graphCoreRetraction_inclusion b) (graphCoreVertex b) (graphCoreHomotopy b)
        (graphCoreHomotopy_fixes b))

private theorem graphCoreBase_nonempty : Nonempty (Realization graphCoreBase) :=
  ⟨vertex _ 0 (by decide)⟩

instance graphCore_pathConnected : PathConnectedSpace (Realization graphCore) := by
  letI := graphCoreBase_nonempty
  letI := suspensionPathConnected (Realization graphCoreBase)
  exact pathConnected_of_homotopyEquiv
    (suspension_realization_homeomorph graphCoreBase).toHomotopyEquiv

/-- The links are literally the same four-cycle after permuting two labels. -/
def graphLinksHomeomorph : Realization (graphLink false) ≃ₜ Realization (graphLink true) :=
  (coordinateReindexHomeomorph (graphLink false) graphLinkSwap).trans
    (Homeomorph.setCongr (congrArg carrier graphLinkSwap_faces))

local instance : Nonempty (Realization graphOne) := graphOne_nonempty
local instance : Nonempty (Realization graphTwo) := graphTwo_nonempty

/-- Complete actual homotopy equivalence of the two suspended finite graph realizations. -/
def graphSuspensionsEquiv : Susp (Realization graphOne) ≃ₕ Susp (Realization graphTwo) := by
  let e₁ := (suspension_realization_homeomorph graphOne).toHomotopyEquiv.trans
    (graphSuspensionWedge false)
  let move := (wedgeBasepoint_independent (L := Realization (graphLink true))
    (graphCoreVertex true) (graphCoreVertex false)).some
  let e₂ := ((suspension_realization_homeomorph graphTwo).toHomotopyEquiv.trans
    (graphSuspensionWedge true)).trans
      (move.trans (wedgeLinkHomeomorph (graphCoreVertex false)
        graphLinksHomeomorph.symm).toHomotopyEquiv)
  exact e₁.trans e₂.symm

/-- S6: two concrete nonempty finite complexes have equivalent suspensions
and inequivalent original realizations. No extra premise is required. -/
theorem suspension_does_not_cancel :
    ∃ L₁ L₂ : PreAbstractSimplicialComplex (Fin 6),
      Nonempty (Realization L₁) ∧ Nonempty (Realization L₂) ∧
      Nonempty (Susp (Realization L₁) ≃ₕ Susp (Realization L₂)) ∧
      ¬ Nonempty (Realization L₁ ≃ₕ Realization L₂) :=
  ⟨graphOne, graphTwo, graphOne_nonempty, graphTwo_nonempty,
    ⟨graphSuspensionsEquiv⟩, graph_not_homotopy_equiv⟩

end
end MathGauge.GP001
