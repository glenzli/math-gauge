import FiniteCones

/-! Two new vertices for every finite base complex, with the actual original cover hypotheses. -/

noncomputable section

open Finset Set ContinuousMap

namespace MathGauge.PublicProof.Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

def embedded_base (L : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Sum Bool V) := L.map Sum.inr

omit [Fintype V] in
theorem embedded_base_avoids_poles (L : PreAbstractSimplicialComplex V) (b : Bool)
    (s : Finset (Sum Bool V)) (hs : s ∈ embedded_base L) : Sum.inl b ∉ s := by
  rcases hs with ⟨t, ht, rfl⟩
  simp

omit [Fintype V] in
theorem embedded_base_vertex (L : PreAbstractSimplicialComplex V) (a : V) (ha : {a} ∈ L) :
    ({Sum.inr a} : Finset (Sum Bool V)) ∈ embedded_base L := by
  exact ⟨{a}, ha, by simp⟩

def realizing_complex (L : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Sum Bool V) :=
  two_cones (embedded_base L) (Sum.inl false) (Sum.inl true)

def realizing_edge (a : V) : PreAbstractSimplicialComplex (Sum Bool V) :=
  simplex_complex {Sum.inl false, Sum.inr a}

omit [Fintype V] in
theorem realizing_link (L : PreAbstractSimplicialComplex V) :
    vertex_link (realizing_complex L) (Sum.inl false) = embedded_base L :=
  link_two_cones _ _ _ (by simp) (embedded_base_avoids_poles L false)

/-- Every finite base with a chosen actual vertex supplies the original triple's hypotheses.
The separate identification of the whole realization with the suspension remains a later bridge. -/
theorem realizing_original_hypotheses (L : PreAbstractSimplicialComplex V)
    (a : V) (ha : {a} ∈ L) :
    realizing_edge a ≤ realizing_complex L ∧
      ({Sum.inl false} : Finset (Sum Bool V)) ∈ realizing_edge a ∧
      ContractibleSpace (Punctured (realizing_complex L) (Sum.inl false)) ∧
      ∃ e : Punctured (realizing_edge a) (Sum.inl false) ≃ₕ Realization (realizing_edge a),
        e.toFun = punctured_inclusion_map (realizing_edge a) (Sum.inl false) := by
  refine ⟨edge_in_two_cones _ _ _ _ (embedded_base_vertex L a ha), ?_, ?_, ?_⟩
  · exact ⟨singleton_nonempty _, by simp⟩
  · exact punctured_two_cones_contractible _ _ _ (by simp) (embedded_base_avoids_poles L false)
  · exact edge_inclusion_is_homotopy_equivalence _ _ (by simp)

theorem embedded_coordinate_zero (L : PreAbstractSimplicialComplex V)
    (x : Realization (embedded_base L)) (b : Bool) : x.1 (Sum.inl b) = 0 := by
  obtain ⟨s, hs, hsupport⟩ := x.2.2
  exact hsupport _ (embedded_base_avoids_poles L b s hs)

def embed_realization (L : PreAbstractSimplicialComplex V) :
    Realization L → Realization (embedded_base L) := fun x => by
  refine ⟨Sum.elim (fun _ => 0) x.1, ⟨?_, ?_⟩, ?_⟩
  · intro u
    cases u with
    | inl b => exact le_refl 0
    | inr v => exact coordinate_nonneg x v
  · rw [Fintype.sum_sum_type]
    simpa using coordinates_sum x
  · obtain ⟨s, hs, hsupport⟩ := x.2.2
    refine ⟨s.image Sum.inr, ⟨s, hs, rfl⟩, ?_⟩
    intro u hu
    cases u with
    | inl b => rfl
    | inr v =>
      exact hsupport v (fun hv => hu (mem_image.mpr ⟨v, hv, rfl⟩))

def restrict_realization (L : PreAbstractSimplicialComplex V) :
    Realization (embedded_base L) → Realization L := fun x => by
  refine ⟨fun v => x.1 (Sum.inr v), ⟨?_, ?_⟩, ?_⟩
  · intro v; exact coordinate_nonneg x _
  · have h := coordinates_sum x
    rw [Fintype.sum_sum_type] at h
    simpa [embedded_coordinate_zero] using h
  · obtain ⟨s, ⟨t, ht, rfl⟩, hsupport⟩ := x.2.2
    refine ⟨t, ht, ?_⟩
    intro v hv
    exact hsupport _ (by simpa using hv)

/-- Adding the two unused apex coordinates does not change the base's realized space. -/
def embedded_realization_homeomorph (L : PreAbstractSimplicialComplex V) :
    Realization L ≃ₜ Realization (embedded_base L) where
  toFun := embed_realization L
  invFun := restrict_realization L
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    funext u
    cases u with
    | inl b => exact (embedded_coordinate_zero L x b).symm
    | inr v => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    cases u with
    | inl b => exact continuous_const
    | inr v => exact (continuous_apply v).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact (continuous_apply (Sum.inr v)).comp continuous_subtype_val

end MathGauge.PublicProof.Topology
