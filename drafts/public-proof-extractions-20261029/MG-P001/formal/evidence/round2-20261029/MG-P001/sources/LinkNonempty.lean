import VertexDeletion
import Mathlib.Topology.Order.IntermediateValue

/-!
The original hypothesis is about the actual inclusion, not merely the
existence of some homotopy equivalence between the two spaces.  This module
uses that inclusion hypothesis to prove the vertex link is nonempty.
-/

noncomputable section

open Finset Set ContinuousMap

namespace MathGauge.PublicProof.Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edge_of_coordinate_between {K : PreAbstractSimplicialComplex V}
    (x : Realization K) (v : V) (hpos : 0 < x.1 v) (hlt : x.1 v < 1) :
    ∃ w, w ≠ v ∧ ({v, w} : Finset V) ∈ K := by
  have hw : ∃ w, w ≠ v ∧ x.1 w ≠ 0 := by
    by_contra! h
    have he : ∑ u, x.1 u = x.1 v :=
      Finset.sum_eq_single v (fun u _ huv => h u huv) (by simp)
    rw [coordinates_sum x] at he
    linarith
  obtain ⟨w, hwv, hw⟩ := hw
  obtain ⟨s, hs, hsupport⟩ := x.2.2
  have hvs : v ∈ s := by
    by_contra hv
    have hz := hsupport v hv
    linarith
  have hws : w ∈ s := by
    by_contra hws
    exact hw (hsupport w hws)
  exact ⟨w, hwv, (K.isRelLowerSet_faces hs).2
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption)
    (insert_nonempty v {w})⟩

/-- The map in the question for the subcomplex `B`. -/
def punctured_inclusion_map (B : PreAbstractSimplicialComplex V) (v : V) :
    C(Punctured B v, Realization B) := ⟨Subtype.val, continuous_subtype_val⟩

/-- Homotopy equivalence of the actual punctured inclusion forces an incident edge. -/
theorem edge_of_punctured_inclusion_equiv (B : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ B) (e : Punctured B v ≃ₕ Realization B)
    (he : e.toFun = punctured_inclusion_map B v) :
    ∃ w, w ≠ v ∧ ({v, w} : Finset V) ∈ B := by
  let p := e.right_inv.some.evalAt (vertex B v hv)
  let f : unitInterval → ℝ := fun t => (p t).1 v
  have hf : Continuous f :=
    (continuous_apply v).comp (continuous_subtype_val.comp p.continuous)
  have hzero : f 0 < 1 := by
    change (p 0).1 v < 1
    rw [p.source]
    change (e.toFun (e.invFun (vertex B v hv))).1 v < 1
    rw [he]
    exact (e.invFun (vertex B v hv)).2
  have hone : f 1 = 1 := by
    change (p 1).1 v = 1
    rw [p.target]
    simp [vertex]
  have hnonneg : 0 ≤ f 0 := coordinate_nonneg (p 0) v
  have hm : (f 0 + 1) / 2 ∈ Icc (f 0) (f 1) := by
    constructor <;> linarith
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 hf hm
  apply edge_of_coordinate_between (p t) v
  · change 0 < f t
    rw [ht]
    linarith
  · change f t < 1
    rw [ht]
    linarith

/-- For every original triple, the link has an actual vertex.  Only the
subcomplex inclusion and the original punctured-inclusion hypothesis are used. -/
theorem vertex_link_has_vertex (K B : PreAbstractSimplicialComplex V) (v : V)
    (hBK : B ≤ K) (hv : {v} ∈ B) (e : Punctured B v ≃ₕ Realization B)
    (he : e.toFun = punctured_inclusion_map B v) :
    ∃ w, ({w} : Finset V) ∈ vertex_link K v := by
  obtain ⟨w, hwv, hw⟩ := edge_of_punctured_inclusion_equiv B v hv e he
  refine ⟨w, singleton_nonempty w, ?_, hBK hw⟩
  simpa using Ne.symm hwv

end MathGauge.PublicProof.Topology
