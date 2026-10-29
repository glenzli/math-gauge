import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Tactic.SplitIfs

/-!
The actual finite barycentric carrier used by MG-P001, and removal of unused ambient vertices.
No singleton is added to the face set. This file is independent of TauCeti.
-/

noncomputable section

open Finset Set

namespace MathGauge.PublicProof.Topology.TauBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Literally the barycentric carrier in MG-P001's `VertexDeletion.lean`. -/
def coordinateCarrier (K : PreAbstractSimplicialComplex V) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∃ s ∈ K, ∀ u, u ∉ s → x u = 0}

abbrev CoordinateRealization (K : PreAbstractSimplicialComplex V) := ↥(coordinateCarrier K)

/-- Restrict the vertex type to the vertices which actually occur. -/
abbrev UsedVertex (K : PreAbstractSimplicialComplex V) := {v : V // ({v} : Finset V) ∈ K}

instance usedVertexFintype (K : PreAbstractSimplicialComplex V) : Fintype (UsedVertex K) :=
  by classical exact Subtype.fintype (fun v => ({v} : Finset V) ∈ K)

/-- The same complex on its used vertices. In particular, deletion and link acquire no
extra isolated vertex from the original ambient vertex type. -/
def usedComplex (K : PreAbstractSimplicialComplex V) : AbstractSimplicialComplex (UsedVertex K) where
  faces := {s | s.image Subtype.val ∈ K}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.image_nonempty.mp (K.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    exact (K.isRelLowerSet_faces hs).2 (Finset.image_mono _ hts) (ht.image _)
  singleton_mem v := by simpa using v.2

theorem coordinate_zero_of_unused (K : PreAbstractSimplicialComplex V)
    (x : CoordinateRealization K) {v : V} (hv : ({v} : Finset V) ∉ K) : x.1 v = 0 := by
  obtain ⟨s, hs, hx⟩ := x.2.2
  apply hx
  intro hvs
  exact hv ((K.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hvs)
    (Finset.singleton_nonempty v))

theorem coordinateCarrier_iff_support (K : PreAbstractSimplicialComplex V) (z : V → ℝ) :
    z ∈ coordinateCarrier K ↔
      (∀ v, 0 ≤ z v) ∧ ∑ v, z v = 1 ∧
        (Finsupp.equivFunOnFinite.symm z).support ∈ K := by
  classical
  constructor
  · rintro ⟨hz, s, hs, hsupport⟩
    refine ⟨hz.1, hz.2, (K.isRelLowerSet_faces hs).2 ?_ ?_⟩
    · intro v hv
      by_contra hvs
      exact (Finsupp.mem_support_iff.mp hv) (hsupport v hvs)
    · apply Finsupp.support_nonempty_iff.mpr
      intro hzero
      have hz0 : z = 0 := by
        funext v
        exact congrArg (fun f : V →₀ ℝ => f v) hzero
      simpa [hz0] using hz.2
  · rintro ⟨hnn, hsum, hs⟩
    refine ⟨⟨hnn, hsum⟩, _, hs, ?_⟩
    intro v hv
    exact Finsupp.notMem_support_iff.mp hv

/-- Restriction of a barycentric point to the used vertex type. -/
def restrictCoordinates (K : PreAbstractSimplicialComplex V) (x : CoordinateRealization K) :
    CoordinateRealization (usedComplex K).toPreAbstractSimplicialComplex := by
  classical
  refine ⟨fun v => x.1 v.1, ⟨fun v => x.2.1.1 v.1, ?_⟩, ?_⟩
  · have h := Fintype.sum_subtype_add_sum_subtype
      (fun v : V => ({v} : Finset V) ∈ K) x.1
    have hzero : ∑ v : {v : V // ({v} : Finset V) ∉ K}, x.1 v.1 = 0 :=
      Finset.sum_eq_zero fun v _ => coordinate_zero_of_unused K x v.2
    rw [hzero, add_zero] at h
    exact h.trans x.2.1.2
  · obtain ⟨s, hs, hx⟩ := x.2.2
    let t : Finset (UsedVertex K) := s.subtype (fun v => ({v} : Finset V) ∈ K)
    have hst : t.image Subtype.val = s := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        (Finset.subtype_map_of_mem (s := s) (p := fun v => ({v} : Finset V) ∈ K)
          (fun v hv => (K.isRelLowerSet_faces hs).2
            (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)))
    refine ⟨t, ?_, ?_⟩
    · change t.image Subtype.val ∈ K
      rwa [hst]
    · intro v hv
      apply hx
      intro hvs
      exact hv (by simpa [t] using hvs)

/-- Extend coordinates by zero outside the actual vertex set. -/
def extendCoordinates (K : PreAbstractSimplicialComplex V)
    (x : CoordinateRealization (usedComplex K).toPreAbstractSimplicialComplex) :
    CoordinateRealization K := by
  classical
  let z : V → ℝ := fun v => if h : ({v} : Finset V) ∈ K then x.1 ⟨v, h⟩ else 0
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · intro v
    dsimp only [z]
    split_ifs with hv
    · exact x.2.1.1 ⟨v, hv⟩
    · exact le_refl _
  · have h := Fintype.sum_subtype_add_sum_subtype
      (fun v : V => ({v} : Finset V) ∈ K) z
    have h₁ : ∑ v : UsedVertex K, z v.1 = 1 := by
      calc
        ∑ v : UsedVertex K, z v.1 = ∑ v : UsedVertex K, x.1 v :=
          Finset.sum_congr rfl fun v _ => dif_pos v.2
        _ = 1 := x.2.1.2
    have h₀ : ∑ v : {v : V // ({v} : Finset V) ∉ K}, z v.1 = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      simp only [z, dif_neg v.2]
    rw [h₁, h₀, add_zero] at h
    exact h.symm
  · obtain ⟨s, hs, hx⟩ := x.2.2
    refine ⟨s.image Subtype.val, hs, ?_⟩
    intro v hv
    dsimp only [z]
    split_ifs with hvK
    · apply hx
      intro hvs
      exact hv (Finset.mem_image.mpr ⟨⟨v, hvK⟩, hvs, rfl⟩)
    · rfl

theorem extend_restrictCoordinates (K : PreAbstractSimplicialComplex V)
    (x : CoordinateRealization K) : extendCoordinates K (restrictCoordinates K x) = x := by
  classical
  apply Subtype.ext
  funext v
  change (if h : ({v} : Finset V) ∈ K then x.1 v else 0) = x.1 v
  split_ifs with hv
  · rfl
  · exact (coordinate_zero_of_unused K x hv).symm

theorem restrict_extendCoordinates (K : PreAbstractSimplicialComplex V)
    (x : CoordinateRealization (usedComplex K).toPreAbstractSimplicialComplex) :
    restrictCoordinates K (extendCoordinates K x) = x := by
  classical
  apply Subtype.ext
  funext v
  change (if h : ({v.1} : Finset V) ∈ K then x.1 ⟨v.1, h⟩ else 0) = x.1 v
  simp [v.2]

/-- Removing unused vertices preserves the actual finite coordinate topology. -/
def usedCoordinateHomeomorph (K : PreAbstractSimplicialComplex V) :
    CoordinateRealization K ≃ₜ
      CoordinateRealization (usedComplex K).toPreAbstractSimplicialComplex where
  toFun := restrictCoordinates K
  invFun := extendCoordinates K
  left_inv := extend_restrictCoordinates K
  right_inv := restrict_extendCoordinates K
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun v => (continuous_apply v.1).comp continuous_subtype_val
  continuous_invFun := by
    classical
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    by_cases hv : ({v} : Finset V) ∈ K
    · simpa only [extendCoordinates, dif_pos hv, Function.comp_def] using
        (continuous_apply (⟨v, hv⟩ : UsedVertex K)).comp continuous_subtype_val
    · simpa only [extendCoordinates, dif_neg hv] using
        (continuous_const : Continuous (fun _ :
          CoordinateRealization (usedComplex K).toPreAbstractSimplicialComplex => (0 : ℝ)))

end MathGauge.PublicProof.Topology.TauBridge
