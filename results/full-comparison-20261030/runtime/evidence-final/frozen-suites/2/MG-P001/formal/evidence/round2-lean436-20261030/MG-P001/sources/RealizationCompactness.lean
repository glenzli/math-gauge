import VertexDeletion

/-! The actual finite barycentric realization is compact and Hausdorff. -/

noncomputable section

open Finset Set

namespace MathGauge.PublicProof.Topology

variable {V : Type*} [Fintype V]

def face_carrier (s : Finset V) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∀ u, u ∉ s → x u = 0}

theorem isClosed_face_carrier (s : Finset V) : IsClosed (face_carrier s) := by
  have h : face_carrier s = stdSimplex ℝ V ∩ ⋂ u : {u : V // u ∉ s},
      {x : V → ℝ | x u.1 = 0} := by
    ext x
    simp [face_carrier]
  rw [h]
  exact (isClosed_stdSimplex ℝ V).inter (isClosed_iInter fun u =>
    isClosed_eq (continuous_apply u.1) continuous_const)

theorem carrier_eq_union_faces (K : PreAbstractSimplicialComplex V) :
    carrier K = ⋃ s : {s : Finset V // s ∈ K}, face_carrier s.1 := by
  ext x
  simp only [carrier, Set.mem_setOf_eq, mem_iUnion, face_carrier]
  constructor
  · rintro ⟨hx, s, hs, hsupport⟩
    exact ⟨⟨s, hs⟩, hx, hsupport⟩
  · rintro ⟨⟨s, hs⟩, hx, hsupport⟩
    exact ⟨hx, s, hs, hsupport⟩

theorem isClosed_carrier (K : PreAbstractSimplicialComplex V) : IsClosed (carrier K) := by
  rw [carrier_eq_union_faces]
  exact isClosed_iUnion_of_finite fun s => isClosed_face_carrier s.1

theorem isCompact_carrier (K : PreAbstractSimplicialComplex V) : IsCompact (carrier K) :=
  (isCompact_stdSimplex ℝ V).of_isClosed_subset (isClosed_carrier K) (fun _ hx => hx.1)

instance compact_realization (K : PreAbstractSimplicialComplex V) : CompactSpace (Realization K) :=
  isCompact_iff_compactSpace.mp (isCompact_carrier K)

end MathGauge.PublicProof.Topology
