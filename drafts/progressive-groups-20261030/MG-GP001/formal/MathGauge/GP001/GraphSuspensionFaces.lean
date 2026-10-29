import MathGauge.GP001.GraphExamples
import SuspensionRealization
import CoordinateReindex

/-! Exact finite incidence checks for the two graph suspensions. Every check
uses kernel-reduced decidability, not an external native certificate. -/
namespace MathGauge.GP001
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open Finset Set ContinuousMap MathGauge.PublicProof.Topology
open MathGauge.PublicProof.Topology.TauBridge

abbrev GraphVertex := Sum Bool (Fin 6)
def graphAttachment (b : Bool) : Fin 6 := if b then 5 else 0
abbrev graphSusp (b : Bool) := realizing_complex (graphAt (graphAttachment b))
abbrev graphDeletion (b : Bool) := deletion (graphSusp b) (Sum.inr 3)
abbrev graphLink (b : Bool) := vertex_link (graphSusp b) (Sum.inr 3)
abbrev graphCoreBase := deletion (deletion graphOne 3) 4
abbrev graphCore := realizing_complex graphCoreBase

instance decidableFaceDeletion {V : Type*} [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) [∀ s, Decidable (s ∈ K)] (v : V) (s : Finset V) :
    Decidable (s ∈ deletion K v) :=
  inferInstanceAs (Decidable (s ∈ K ∧ v ∉ s))

instance decidableFaceRealizing {V : Type*} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) [∀ s, Decidable (s ∈ K)] (s : Finset (Sum Bool V)) :
    Decidable (s ∈ realizing_complex K) := by
  change Decidable ((s.Nonempty ∧ (s.erase (.inl false) = ∅ ∨
      ∃ t : Finset V, t ∈ K ∧ t.image Sum.inr = s.erase (.inl false))) ∨
    (s.Nonempty ∧ (s.erase (.inl true) = ∅ ∨
      ∃ t : Finset V, t ∈ K ∧ t.image Sum.inr = s.erase (.inl true))))
  infer_instance

instance decidableFaceLink {V : Type*} [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) [∀ s, Decidable (s ∈ K)] (v : V) (s : Finset V) :
    Decidable (s ∈ vertex_link K v) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K))

theorem graph_core_le (b : Bool) : graphCore ≤ graphDeletion b := by
  have h : ∀ s : Finset GraphVertex, s ∈ graphCore → s ∈ graphDeletion b := by
    cases b <;> decide
  exact h

theorem graph_fold_dominates (b : Bool) :
    ∀ s ∈ graphDeletion b, Sum.inr 4 ∈ s →
      insert (Sum.inr (graphAttachment b)) s ∈ graphDeletion b := by
  cases b <;> decide

theorem graph_fold_distinct (b : Bool) :
    (Sum.inr 4 : GraphVertex) ≠ Sum.inr (graphAttachment b) := by
  cases b <;> decide

theorem graph_core_eq (b : Bool) :
    deletion (graphDeletion b) (Sum.inr 4) = graphCore := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  exact (show ∀ s : Finset GraphVertex,
    s ∈ deletion (graphDeletion b) (Sum.inr 4) ↔ s ∈ graphCore by cases b <;> decide) s

theorem graph_core_vertex (b : Bool) :
    ({Sum.inr (graphAttachment b)} : Finset GraphVertex) ∈ graphCore := by
  cases b <;> decide

theorem graph_link_vertex (b : Bool) :
    ({Sum.inl false} : Finset GraphVertex) ∈ graphLink b := by
  cases b <;> decide

instance graphLink_nonempty (b : Bool) : Nonempty (Realization (graphLink b)) :=
  ⟨vertex _ _ (graph_link_vertex b)⟩

theorem graph_link_null_faces (b : Bool) :
    ∀ s ∈ graphLink b, insert (Sum.inr (graphAttachment b)) s ∈ graphDeletion b := by
  cases b <;> decide

def graphLinkSwap : GraphVertex ≃ GraphVertex := Equiv.swap (Sum.inr 0) (Sum.inr 5)

theorem graphLinkSwap_faces : reindexComplex (graphLink false) graphLinkSwap = graphLink true := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  exact (show ∀ s : Finset GraphVertex,
    s.image graphLinkSwap.symm ∈ graphLink false ↔ s ∈ graphLink true by decide) s


end
end MathGauge.GP001
