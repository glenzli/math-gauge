import CoordinateCore

/-!
Actual reindexing of finite barycentric coordinates along an equivalence.
The explicit equivalence with `Fin (card V)` makes finite realizations small
without restricting the universe of the original vertex type.
-/

noncomputable section

open Finset Set

namespace MathGauge.PublicProof.Topology.TauBridge

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabel the exact face set; no faces are added or removed. -/
def reindexComplex (K : PreAbstractSimplicialComplex V) (e : V ≃ W) :
    PreAbstractSimplicialComplex W where
  faces := {s | s.image e.symm ∈ K}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.image_nonempty.mp (K.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    exact (K.isRelLowerSet_faces hs).2 (Finset.image_mono _ hts) (ht.image _)

/-- The forward coordinate map is the literal permutation of coordinate functions. -/
def reindexCoordinates (K : PreAbstractSimplicialComplex V) (e : V ≃ W)
    (x : CoordinateRealization K) : CoordinateRealization (reindexComplex K e) := by
  refine ⟨fun w => x.1 (e.symm w), ⟨fun w => x.2.1.1 (e.symm w), ?_⟩, ?_⟩
  · exact (e.symm.sum_comp x.1).trans x.2.1.2
  · obtain ⟨s, hs, hx⟩ := x.2.2
    refine ⟨s.image e, ?_, ?_⟩
    · change (s.image e).image e.symm ∈ K
      simpa only [Finset.image_image, Equiv.symm_comp_self, Finset.image_id] using hs
    · intro w hw
      apply hx
      intro hws
      exact hw (Finset.mem_image.mpr ⟨e.symm w, hws, e.apply_symm_apply w⟩)

/-- The inverse coordinate map, with its support in the original face set. -/
def unreindexCoordinates (K : PreAbstractSimplicialComplex V) (e : V ≃ W)
    (x : CoordinateRealization (reindexComplex K e)) : CoordinateRealization K := by
  refine ⟨fun v => x.1 (e v), ⟨fun v => x.2.1.1 (e v), ?_⟩, ?_⟩
  · exact (e.sum_comp x.1).trans x.2.1.2
  · obtain ⟨s, hs, hx⟩ := x.2.2
    refine ⟨s.image e.symm, hs, ?_⟩
    intro v hv
    apply hx
    intro hvs
    exact hv (Finset.mem_image.mpr ⟨e v, hvs, e.symm_apply_apply v⟩)

/-- The usual finite-coordinate topologies agree under vertex reindexing. -/
def coordinateReindexHomeomorph (K : PreAbstractSimplicialComplex V) (e : V ≃ W) :
    CoordinateRealization K ≃ₜ CoordinateRealization (reindexComplex K e) where
  toFun := reindexCoordinates K e
  invFun := unreindexCoordinates K e
  left_inv x := by
    apply Subtype.ext
    funext v
    exact congrArg x.1 (e.symm_apply_apply v)
  right_inv x := by
    apply Subtype.ext
    funext w
    exact congrArg x.1 (e.apply_symm_apply w)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun w => (continuous_apply (e.symm w)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun v => (continuous_apply (e v)).comp continuous_subtype_val

/-- The same finite precomplex on a universe-zero vertex set. -/
def smallComplex (K : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Fin (Fintype.card V)) :=
  reindexComplex K (Fintype.equivFin V)

/-- An actual homeomorphism to the small coordinate model, not a new hypothesis. -/
def smallCoordinateHomeomorph (K : PreAbstractSimplicialComplex V) :
    CoordinateRealization K ≃ₜ CoordinateRealization (smallComplex K) :=
  coordinateReindexHomeomorph K (Fintype.equivFin V)

end MathGauge.PublicProof.Topology.TauBridge
