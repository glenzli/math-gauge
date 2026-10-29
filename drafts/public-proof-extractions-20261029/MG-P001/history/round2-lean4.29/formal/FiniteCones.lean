import VertexDeletion
import LinkNonempty

/-! Actual finite cones and the original hypotheses of the two-cone realizations. -/

noncomputable section

open Finset Set ContinuousMap

namespace MathGauge.PublicProof.Topology

variable {V : Type*} [DecidableEq V]

/-- All nonempty faces of the simplex spanned by a finite set. -/
def simplex_complex (s : Finset V) : PreAbstractSimplicialComplex V where
  faces := {t | t.Nonempty ∧ t ⊆ s}
  isRelLowerSet_faces := fun {_} ht => ⟨ht.1, fun _ htu hu => ⟨hu, htu.trans ht.2⟩⟩

/-- An actual abstract cone: remove the apex from a face to obtain a base face or the empty set. -/
def cone_complex (K : PreAbstractSimplicialComplex V) (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ (s.erase v = ∅ ∨ s.erase v ∈ K)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    by_cases he : t.erase v = ∅
    · exact Or.inl he
    · have hsub : t.erase v ⊆ s.erase v := erase_subset_erase v hts
      rcases hs.2 with hs | hs
      · have hn : (t.erase v).Nonempty := nonempty_iff_ne_empty.mpr he
        obtain ⟨u, hu⟩ := hn
        have hus := hsub hu
        simp [hs] at hus
      · exact Or.inr ((K.isRelLowerSet_faces hs).2 hsub (nonempty_iff_ne_empty.mpr he))

theorem base_le_cone (K : PreAbstractSimplicialComplex V) (v : V) : K ≤ cone_complex K v := by
  intro s hs
  refine ⟨(K.isRelLowerSet_faces hs).1, ?_⟩
  by_cases he : s.erase v = ∅
  · exact Or.inl he
  · exact Or.inr ((K.isRelLowerSet_faces hs).2 (erase_subset v s)
      (nonempty_iff_ne_empty.mpr he))

theorem cone_apex_face (K : PreAbstractSimplicialComplex V) (v : V) :
    ({v} : Finset V) ∈ cone_complex K v := by
  exact ⟨singleton_nonempty v, Or.inl (by simp)⟩

theorem cone_insert_apex {K : PreAbstractSimplicialComplex V} {v : V}
    {s : Finset V} (hs : s ∈ cone_complex K v) : insert v s ∈ cone_complex K v := by
  refine ⟨insert_nonempty v s, ?_⟩
  simpa using hs.2

theorem cone_face_avoids_other {K : PreAbstractSimplicialComplex V} {p q : V}
    (hpq : p ≠ q) (hbase : ∀ s ∈ K, p ∉ s) {s : Finset V}
    (hs : s ∈ cone_complex K q) : p ∉ s := by
  intro hp
  have hpe : p ∈ s.erase q := mem_erase.mpr ⟨hpq, hp⟩
  rcases hs.2 with he | he
  · simp [he] at hpe
  · exact hbase (s.erase q) he hpe

def two_cones (K : PreAbstractSimplicialComplex V) (p q : V) :
    PreAbstractSimplicialComplex V := cone_complex K p ⊔ cone_complex K q

theorem deletion_two_cones (K : PreAbstractSimplicialComplex V) (p q : V)
    (hpq : p ≠ q) (hbase : ∀ s ∈ K, p ∉ s) :
    deletion (two_cones K p q) p = cone_complex K q := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  change ((s ∈ cone_complex K p ∨ s ∈ cone_complex K q) ∧ p ∉ s) ↔
    s ∈ cone_complex K q
  constructor
  · rintro ⟨hs | hs, hp⟩
    · have he : s.erase p = s := erase_eq_of_notMem hp
      rcases hs.2 with h | h
      · exact (hs.1.ne_empty (he.symm.trans h)).elim
      · exact base_le_cone K q (he ▸ h)
    · exact hs
  · intro hs
    exact ⟨Or.inr hs, cone_face_avoids_other hpq hbase hs⟩

theorem link_two_cones (K : PreAbstractSimplicialComplex V) (p q : V)
    (hpq : p ≠ q) (hbase : ∀ s ∈ K, p ∉ s) :
    vertex_link (two_cones K p q) p = K := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  change (s.Nonempty ∧ p ∉ s ∧
    (insert p s ∈ cone_complex K p ∨ insert p s ∈ cone_complex K q)) ↔ s ∈ K
  constructor
  · rintro ⟨hne, hp, hs | hs⟩
    · have he : (insert p s).erase p = s := by simp [hp]
      rcases hs.2 with h | h
      · exact (hne.ne_empty (he.symm.trans h)).elim
      · exact he ▸ h
    · exact (cone_face_avoids_other hpq hbase hs (mem_insert_self p s)).elim
  · intro hs
    exact ⟨(K.isRelLowerSet_faces hs).1, hbase s hs,
      Or.inl (cone_insert_apex (base_le_cone K p hs))⟩

variable [Fintype V]

/-- The straight contraction at an actual cone vertex stays in the actual face complex. -/
def apex_homotopy_point {K : PreAbstractSimplicialComplex V} {v : V}
    (hv : {v} ∈ K) (hcone : ∀ s ∈ K, insert v s ∈ K)
    (t : unitInterval) (x : Realization K) : Realization K := by
  let y : V → ℝ := fun u => (1 - (t : ℝ)) * x.1 u + (t : ℝ) * (vertex K v hv).1 u
  have hy : y ∈ stdSimplex ℝ V := by
    refine ⟨?_, ?_⟩
    · intro u
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (coordinate_nonneg x u))
        (mul_nonneg t.2.1 (coordinate_nonneg (vertex K v hv) u))
    · dsimp [y]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        coordinates_sum x, coordinates_sum (vertex K v hv)]
      ring
  refine ⟨y, hy, ?_⟩
  obtain ⟨s, hs, hsupport⟩ := x.2.2
  refine ⟨insert v s, hcone s hs, ?_⟩
  intro u hu
  have huv : u ≠ v := fun h => hu (h ▸ mem_insert_self v s)
  have hus : u ∉ s := fun h => hu (mem_insert_of_mem h)
  simp [y, hsupport u hus, vertex, Pi.single_eq_of_ne huv]

def apex_homotopy (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ K) (hcone : ∀ s ∈ K, insert v s ∈ K) :
    ContinuousMap.Homotopy (ContinuousMap.id (Realization K))
      (ContinuousMap.const _ (vertex K v hv)) where
  toFun p := apex_homotopy_point hv hcone p.1 p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    change Continuous (fun p : unitInterval × Realization K =>
      (1 - (p.1 : ℝ)) * p.2.1 u + (p.1 : ℝ) * (vertex K v hv).1 u)
    have ht : Continuous (fun p : unitInterval × Realization K => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : unitInterval × Realization K => p.2.1 u) :=
      (continuous_apply u).comp (continuous_subtype_val.comp continuous_snd)
    exact ((continuous_const.sub ht).mul hx).add (ht.mul continuous_const)
  map_zero_left x := by
    apply Subtype.ext
    funext u
    simp [apex_homotopy_point]
  map_one_left x := by
    apply Subtype.ext
    funext u
    simp [apex_homotopy_point]

theorem contractible_of_apex (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ K) (hcone : ∀ s ∈ K, insert v s ∈ K) :
    ContractibleSpace (Realization K) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨vertex K v hv, ⟨apex_homotopy K v hv hcone⟩⟩

theorem cone_contractible (K : PreAbstractSimplicialComplex V) (v : V) :
    ContractibleSpace (Realization (cone_complex K v)) :=
  contractible_of_apex _ v (cone_apex_face K v) (fun _ => cone_insert_apex)

theorem punctured_two_cones_contractible (K : PreAbstractSimplicialComplex V) (p q : V)
    (hpq : p ≠ q) (hbase : ∀ s ∈ K, p ∉ s) :
    ContractibleSpace (Punctured (two_cones K p q) p) := by
  have hdel : ContractibleSpace (Realization (deletion (two_cones K p q) p)) := by
    rw [deletion_two_cones K p q hpq hbase]
    exact cone_contractible K q
  letI := hdel
  exact (punctured_deletion_equiv _ _).contractibleSpace

theorem simplex_contractible (s : Finset V) (a : V) (ha : a ∈ s) :
    ContractibleSpace (Realization (simplex_complex s)) := by
  apply contractible_of_apex _ a
  · exact ⟨singleton_nonempty a, singleton_subset_iff.mpr ha⟩
  · intro t ht
    exact ⟨insert_nonempty a t, insert_subset ha ht.2⟩

omit [Fintype V] in
theorem deletion_simplex (s : Finset V) (v : V) :
    deletion (simplex_complex s) v = simplex_complex (s.erase v) := by
  apply PreAbstractSimplicialComplex.ext
  ext t
  change ((t.Nonempty ∧ t ⊆ s) ∧ v ∉ t) ↔ t.Nonempty ∧ t ⊆ s.erase v
  constructor
  · rintro ⟨⟨hne, hsub⟩, hv⟩
    exact ⟨hne, fun u hu => mem_erase.mpr ⟨fun he => hv (he ▸ hu), hsub hu⟩⟩
  · rintro ⟨hne, hsub⟩
    refine ⟨⟨hne, hsub.trans (erase_subset v s)⟩, ?_⟩
    intro hv
    have h := hsub hv
    simp at h

omit [Fintype V] in
theorem edge_in_two_cones (K : PreAbstractSimplicialComplex V) (p q a : V)
    (ha : {a} ∈ K) : simplex_complex {p, a} ≤ two_cones K p q := by
  have hedge : ({p, a} : Finset V) ∈ cone_complex K p :=
    cone_insert_apex (base_le_cone K p ha)
  intro s hs
  exact Or.inl (((cone_complex K p).isRelLowerSet_faces hedge).2 hs.2 hs.1)

theorem edge_punctured_contractible (p a : V) (ha : a ≠ p) :
    ContractibleSpace (Punctured (simplex_complex {p, a}) p) := by
  have hd : ContractibleSpace (Realization (deletion (simplex_complex {p, a}) p)) := by
    rw [deletion_simplex]
    apply simplex_contractible _ a
    simp [ha]
  letI := hd
  exact (punctured_deletion_equiv _ _).contractibleSpace

private theorem selfmap_homotopic_id {X : Type*} [TopologicalSpace X]
    [ContractibleSpace X] (f : C(X, X)) : f.Homotopic (ContinuousMap.id X) := by
  obtain ⟨x, hx⟩ := id_nullhomotopic X
  exact (show f.Homotopic (ContinuousMap.const X x) from hx.comp (Homotopic.refl f)).trans hx.symm

/-- Every specified continuous map between nonempty contractible spaces is a homotopy equivalence. -/
def equiv_of_contractible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) : X ≃ₕ Y where
  toFun := f
  invFun := ContinuousMap.const Y (Classical.arbitrary X)
  left_inv := selfmap_homotopic_id _
  right_inv := selfmap_homotopic_id _

theorem edge_inclusion_is_homotopy_equivalence (p a : V) (ha : a ≠ p) :
    ∃ e : Punctured (simplex_complex {p, a}) p ≃ₕ Realization (simplex_complex {p, a}),
      e.toFun = punctured_inclusion_map (simplex_complex {p, a}) p := by
  letI := simplex_contractible {p, a} a (by simp)
  letI := edge_punctured_contractible p a ha
  exact ⟨equiv_of_contractible (punctured_inclusion_map _ _), rfl⟩

end MathGauge.PublicProof.Topology
