import CoordinateCore
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic
import TauCeti.Topology.CWComplex.Classical.CWType

/-!
The finite coordinate realization is the actual weak realization used by TauCeti.
Unused ambient vertices are removed by a proved homeomorphism, never added as faces.
-/

noncomputable section

open Set

namespace MathGauge.PublicProof.Topology.TauBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For an abstract complex with no unused vertices, finite barycentric coordinates
and the TauCeti weak realization have the same usual topology. -/
def abstractCoordinateHomeomorph (K : AbstractSimplicialComplex V) :
    CoordinateRealization K.toPreAbstractSimplicialComplex ≃ₜ
      AbstractSimplicialComplex.Realization K :=
  (Homeomorph.setCongr (Set.ext fun z =>
    (coordinateCarrier_iff_support K.toPreAbstractSimplicialComplex z).trans
      AbstractSimplicialComplex.mem_range_realization_coe_iff.symm)).trans
    (K.realizationHomeomorphRange (Set.toFinite K.faces)).symm

/-- Every finite precomplex has the weak realization of its used-vertex complex.
The theorem includes empty precomplexes, deletions, and links. -/
def coordinateTauHomeomorph (K : PreAbstractSimplicialComplex V) :
    CoordinateRealization K ≃ₜ AbstractSimplicialComplex.Realization (usedComplex K) :=
  (usedCoordinateHomeomorph K).trans (abstractCoordinateHomeomorph (usedComplex K))

/-- The actual finite barycentric realization has CW type. A finite linear ordering is
chosen only to orient the external CW cells; it does not alter the topology. -/
theorem coordinateRealization_cwType (K : PreAbstractSimplicialComplex V) :
    TauCeti.CWType (CoordinateRealization K) := by
  letI : LinearOrder (UsedVertex K) :=
    LinearOrder.lift' (Fintype.equivFin (UsedVertex K)) (Fintype.equivFin _).injective
  letI := AbstractSimplicialComplex.realizationCWComplex (usedComplex K)
  exact (coordinateTauHomeomorph K).cwType

end MathGauge.PublicProof.Topology.TauBridge
