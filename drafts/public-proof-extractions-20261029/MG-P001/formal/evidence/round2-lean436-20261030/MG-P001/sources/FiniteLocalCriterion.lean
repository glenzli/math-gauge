import OriginalCriterion
import FiniteMatrixCriterion

/-!
The bounded local integer-chain criterion for the original MG-P001 problem.
Only the actual link face set is used. The degree bound is the number of used
link vertices; no rationalization and no change of the original hypotheses occur.
-/

noncomputable section

open ContinuousMap TauCeti

namespace MathGauge.PublicProof.Topology

open TauBridge

/-- A finite family of integral augmented boundary tests on the actual used link
vertices, after a proved finite relabeling. -/
def finiteLocalCriterion {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) : Prop :=
  letI := usedVertexLinearOrder (smallComplex L)
  FiniteAugmentedExact (usedComplex (smallComplex L))

theorem finiteLocalCriterion_iff_finiteOrderedAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) [Nonempty (Realization L)] :
    finiteLocalCriterion L ↔ finiteOrderedAcyclic L := by
  let e := smallCoordinateHomeomorph L
  letI : Nonempty (Realization (smallComplex L)) :=
    ⟨e (Classical.choice (inferInstance : Nonempty (Realization L)))⟩
  letI := usedVertex_nonempty (smallComplex L)
  letI := usedVertexLinearOrder (smallComplex L)
  exact finiteAugmentedExact_iff_quasiIso (usedComplex (smallComplex L))

/-- The full original contractibility criterion, with finitely many degrees of
actual integer-chain exactness and no extra homotopical or homological hypotheses. -/
theorem original_contractible_iff_finiteLocalCriterion
    {V : Type*} [Fintype V] [DecidableEq V]
    (K B : PreAbstractSimplicialComplex V) (v : V)
    (hBK : B ≤ K) (hv : {v} ∈ B) [ContractibleSpace (Punctured K v)]
    (e : Punctured B v ≃ₕ Realization B) (he : e.toFun = punctured_inclusion_map B v) :
    ContractibleSpace (Realization K) ↔ finiteLocalCriterion (vertex_link K v) := by
  obtain ⟨a, ha⟩ := vertex_link_has_vertex K B v hBK hv e he
  letI : Nonempty (Realization (vertex_link K v)) := ⟨vertex _ a ha⟩
  exact (original_contractible_iff_finiteOrderedAcyclic K B v hBK hv e he).trans
    (finiteLocalCriterion_iff_finiteOrderedAcyclic (vertex_link K v)).symm

/-- The incident faces alone determine the exact link face set. -/
theorem vertex_link_eq_of_incident_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (K K' : PreAbstractSimplicialComplex V) (v : V)
    (h : ∀ s : Finset V, v ∈ s → (s ∈ K ↔ s ∈ K')) :
    vertex_link K v = vertex_link K' v := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  change (s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K) ↔
    (s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K')
  rw [h (insert v s) (Finset.mem_insert_self v s)]

/-- Changing simplices away from the distinguished vertex cannot change the local test. -/
theorem finiteLocalCriterion_eq_of_incident_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (K K' : PreAbstractSimplicialComplex V) (v : V)
    (h : ∀ s : Finset V, v ∈ s → (s ∈ K ↔ s ∈ K')) :
    finiteLocalCriterion (vertex_link K v) = finiteLocalCriterion (vertex_link K' v) := by
  rw [vertex_link_eq_of_incident_faces K K' v h]

/-- The same local criterion written entirely as finitely many explicit integer
face-incidence matrices, including the all-ones augmentation row. -/
def finiteLocalMatrixCriterion {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) : Prop :=
  letI := usedVertexLinearOrder (smallComplex L)
  FiniteMatrixExact (usedComplex (smallComplex L))

theorem finiteLocalMatrixCriterion_iff {V : Type*} [Fintype V] [DecidableEq V]
    (L : PreAbstractSimplicialComplex V) :
    finiteLocalMatrixCriterion L ↔ finiteLocalCriterion L := by
  letI := usedVertexLinearOrder (smallComplex L)
  exact finiteMatrixExact_iff_augmented (usedComplex (smallComplex L))

/-- MG-P001's complete finite local contractibility criterion. All original
geometric hypotheses are retained; the conclusion uses only finitely many
explicit integer boundary matrices of the actual link. -/
theorem original_contractible_iff_finiteLocalMatrixCriterion
    {V : Type*} [Fintype V] [DecidableEq V]
    (K B : PreAbstractSimplicialComplex V) (v : V)
    (hBK : B ≤ K) (hv : {v} ∈ B) [ContractibleSpace (Punctured K v)]
    (e : Punctured B v ≃ₕ Realization B) (he : e.toFun = punctured_inclusion_map B v) :
    ContractibleSpace (Realization K) ↔ finiteLocalMatrixCriterion (vertex_link K v) :=
  (original_contractible_iff_finiteLocalCriterion K B v hBK hv e he).trans
    (finiteLocalMatrixCriterion_iff (vertex_link K v)).symm

/-- The matrix test depends only on the simplices incident to the distinguished vertex. -/
theorem finiteLocalMatrixCriterion_eq_of_incident_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (K K' : PreAbstractSimplicialComplex V) (v : V)
    (h : ∀ s : Finset V, v ∈ s → (s ∈ K ↔ s ∈ K')) :
    finiteLocalMatrixCriterion (vertex_link K v) =
      finiteLocalMatrixCriterion (vertex_link K' v) := by
  rw [vertex_link_eq_of_incident_faces K K' v h]

end MathGauge.PublicProof.Topology
