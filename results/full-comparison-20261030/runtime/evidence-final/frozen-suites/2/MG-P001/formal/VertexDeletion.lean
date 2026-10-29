import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Actual finite abstract complexes and their usual barycentric realization.

The ambient vertex type is finite.  Mathlib's `PreAbstractSimplicialComplex`
records the nonempty faces; adding or removing the empty face has no effect on
the realization below.  A point is a nonnegative real barycentric vector of
total mass one, supported on an actual face of the complex.  The topology is
the subspace topology inherited from the finite product `V → ℝ`.

This module proves vertex deletion and its radial homotopy.  It does not assert
the suspension classification or its integral-homology criterion.
-/

noncomputable section

open Finset Set ContinuousMap

namespace MathGauge.PublicProof.Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The deletion consists of precisely the original faces not containing `v`. -/
def deletion (K : PreAbstractSimplicialComplex V) (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K ∧ v ∉ s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(K.isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts ht
    exact ⟨(K.isRelLowerSet_faces hs.1).2 hts ht, fun hv => hs.2 (hts hv)⟩

/-- The vertex link, expressed using actual finite faces. -/
def vertex_link (K : PreAbstractSimplicialComplex V) (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, fun hv => hs.2.1 (hts hv),
      (K.isRelLowerSet_faces hs.2.2).2 (insert_subset_insert v hts) (insert_nonempty v t)⟩

/-- The closed star is the collection of faces whose union with `v` is a face. -/
def closed_star (K : PreAbstractSimplicialComplex V) (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ insert v s ∈ K}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, (K.isRelLowerSet_faces hs.2).2
      (insert_subset_insert v hts) (insert_nonempty v t)⟩

omit [Fintype V] [DecidableEq V] in
theorem deletion_le (K : PreAbstractSimplicialComplex V) (v : V) : deletion K v ≤ K :=
  fun _ hs => hs.1

omit [Fintype V] in
theorem deletion_union_star (K : PreAbstractSimplicialComplex V) (v : V) :
    deletion K v ⊔ closed_star K v = K := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  change (s ∈ K ∧ v ∉ s) ∨ (s.Nonempty ∧ insert v s ∈ K) ↔ s ∈ K
  constructor
  · rintro (h | h)
    · exact h.1
    · exact (K.isRelLowerSet_faces h.2).2 (subset_insert v s) h.1
  · intro hs
    by_cases hv : v ∈ s
    · exact Or.inr ⟨(K.isRelLowerSet_faces hs).1, by simpa [hv] using hs⟩
    · exact Or.inl ⟨hs, hv⟩

omit [Fintype V] in
theorem deletion_inter_star (K : PreAbstractSimplicialComplex V) (v : V) :
    deletion K v ⊓ closed_star K v = vertex_link K v := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  change (s ∈ K ∧ v ∉ s) ∧ (s.Nonempty ∧ insert v s ∈ K) ↔
    s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h'.1, h.2, h'.2⟩
  · rintro ⟨hne, hv, hs⟩
    exact ⟨⟨(K.isRelLowerSet_faces hs).2 (subset_insert v s) hne, hv⟩, hne, hs⟩

/-- Standard geometric realization as a union of closed standard simplices. -/
def carrier (K : PreAbstractSimplicialComplex V) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∃ s ∈ K, ∀ u, u ∉ s → x u = 0}

abbrev Realization (K : PreAbstractSimplicialComplex V) := ↥(carrier K)

omit [DecidableEq V] in
theorem coordinate_nonneg {K : PreAbstractSimplicialComplex V} (x : Realization K) (u : V) :
    0 ≤ x.1 u := x.2.1.1 u

omit [DecidableEq V] in
theorem coordinate_le_one {K : PreAbstractSimplicialComplex V} (x : Realization K) (u : V) :
    x.1 u ≤ 1 := stdSimplex.le_one ⟨x.1, x.2.1⟩ u

omit [DecidableEq V] in
theorem coordinates_sum {K : PreAbstractSimplicialComplex V} (x : Realization K) :
    ∑ u, x.1 u = 1 := x.2.1.2

/-- The actual vertex point. -/
def vertex (K : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ K) : Realization K :=
  ⟨Pi.single v 1, single_mem_stdSimplex ℝ v, {v}, hv, by
    intro u hu
    have h : u ≠ v := by simpa using hu
    simp [Pi.single_eq_of_ne h]⟩

theorem coordinate_eq_one_iff {K : PreAbstractSimplicialComplex V}
    (x : Realization K) (v : V) (hv : {v} ∈ K) : x.1 v = 1 ↔ x = vertex K v hv := by
  constructor
  · intro h
    apply Subtype.ext
    funext u
    by_cases huv : u = v
    · subst u; simpa [vertex] using h
    · have hsum := coordinates_sum x
      have hle : x.1 u + x.1 v ≤ ∑ w, x.1 w := by
        have hs := Finset.sum_le_sum_of_subset_of_nonneg
          (show ({u, v} : Finset V) ⊆ univ from subset_univ _) (fun w _ _ => coordinate_nonneg x w)
        simpa [huv] using hs
      have hz : x.1 u = 0 := le_antisymm (by linarith) (coordinate_nonneg x u)
      simpa [vertex, Pi.single_eq_of_ne huv] using hz
  · rintro rfl; simp [vertex]

/-- This coordinate domain is exactly the complement of the distinguished vertex. -/
abbrev Punctured (K : PreAbstractSimplicialComplex V) (v : V) :=
  {x : Realization K // x.1 v < 1}

theorem punctured_iff_ne_vertex {K : PreAbstractSimplicialComplex V}
    (x : Realization K) (v : V) (hv : {v} ∈ K) :
    x.1 v < 1 ↔ x ≠ vertex K v hv := by
  rw [lt_iff_le_and_ne, and_iff_right (coordinate_le_one x v)]
  exact not_congr (coordinate_eq_one_iff x v hv)

/-- The coordinate domain is homeomorphic to the literal deleted-point subspace. -/
def punctured_complement_homeomorph (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ K) : Punctured K v ≃ₜ {x : Realization K // x ≠ vertex K v hv} :=
  Homeomorph.setCongr (show {x : Realization K | x.1 v < 1} = {x : Realization K | x ≠ vertex K v hv} from Set.ext (fun x => punctured_iff_ne_vertex x v hv))

omit [DecidableEq V] in
private theorem supported_nonempty {x : V → ℝ} (hsum : ∑ u, x u = 1)
    {s : Finset V} (hs : ∀ u, u ∉ s → x u = 0) : s.Nonempty := by
  by_contra h
  have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : ∑ u, x u = 0 := Finset.sum_eq_zero (fun u _ => hs u (by simp [he]))
  linarith

theorem mem_carrier_deletion_iff {K : PreAbstractSimplicialComplex V} {v : V} {x : V → ℝ} :
    x ∈ carrier (deletion K v) ↔ x ∈ carrier K ∧ x v = 0 := by
  constructor
  · rintro ⟨hx, s, ⟨hs, hv⟩, hsupport⟩
    exact ⟨⟨hx, s, hs, hsupport⟩, hsupport v hv⟩
  · rintro ⟨⟨hx, s, hs, hsupport⟩, hv⟩
    have he : ∀ u, u ∉ s.erase v → x u = 0 := by
      intro u hu
      by_cases huv : u = v
      · simpa [huv] using hv
      · exact hsupport u (fun hus => hu (mem_erase.mpr ⟨huv, hus⟩))
    exact ⟨hx, s.erase v,
      ⟨(K.isRelLowerSet_faces hs).2 (erase_subset v s) (supported_nonempty hx.2 he),
        by simp⟩, he⟩

/-- Normalize every coordinate other than the deleted vertex. -/
def radial_coordinates (v : V) (x : V → ℝ) : V → ℝ :=
  fun u => if u = v then 0 else x u / (1 - x v)

theorem radial_coordinates_mem {K : PreAbstractSimplicialComplex V} {v : V}
    (x : Punctured K v) : radial_coordinates v x.1.1 ∈ carrier (deletion K v) := by
  have hd : 0 < 1 - x.1.1 v := sub_pos.mpr x.2
  have hsum : ∑ u, radial_coordinates v x.1.1 u = 1 := by
    calc
      ∑ u, radial_coordinates v x.1.1 u =
          (∑ u ∈ (univ : Finset V).erase v, x.1.1 u) / (1 - x.1.1 v) := by
        rw [Finset.sum_div]
        rw [← Finset.sum_erase_add _ _ (mem_univ v)]
        simp only [radial_coordinates, if_pos, add_zero]
        apply Finset.sum_congr rfl
        intro u hu
        simp [ne_of_mem_erase hu]
      _ = (1 - x.1.1 v) / (1 - x.1.1 v) := by
        congr 1
        have h := Finset.sum_erase_add (univ : Finset V) (fun u => x.1.1 u) (mem_univ v)
        rw [coordinates_sum x.1] at h
        linarith
      _ = 1 := div_self (ne_of_gt hd)
  obtain ⟨s, hs, hsupport⟩ := x.1.2.2
  have hr : ∀ u, u ∉ s.erase v → radial_coordinates v x.1.1 u = 0 := by
    intro u hu
    by_cases huv : u = v
    · simp [radial_coordinates, huv]
    · have hus : u ∉ s := fun hus => hu (mem_erase.mpr ⟨huv, hus⟩)
      simp [radial_coordinates, huv, hsupport u hus]
  refine ⟨⟨?_, hsum⟩, s.erase v,
    ⟨(K.isRelLowerSet_faces hs).2 (erase_subset v s) (supported_nonempty hsum hr),
      by simp⟩, hr⟩
  intro u
  by_cases huv : u = v
  · simp [radial_coordinates, huv]
  · simp only [radial_coordinates, if_neg huv]
    exact div_nonneg (coordinate_nonneg x.1 u) (le_of_lt hd)

/-- The radial retraction, with its codomain proved to be the actual deletion. -/
def radial (K : PreAbstractSimplicialComplex V) (v : V) :
    Punctured K v → Realization (deletion K v) :=
  fun x => ⟨radial_coordinates v x.1.1, radial_coordinates_mem x⟩

theorem continuous_radial (K : PreAbstractSimplicialComplex V) (v : V) :
    Continuous (radial K v) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  by_cases huv : u = v
  · simpa [radial, radial_coordinates, huv] using
      (continuous_const : Continuous (fun _ : Punctured K v => (0 : ℝ)))
  · simp only [radial_coordinates, if_neg huv]
    exact ((continuous_apply u).comp (continuous_subtype_val.comp continuous_subtype_val)).div
      (continuous_const.sub ((continuous_apply v).comp
        (continuous_subtype_val.comp continuous_subtype_val)))
      (fun x => ne_of_gt (sub_pos.mpr x.2))

/-- The ordinary inclusion of the deletion realization into the punctured one. -/
def deletion_inclusion (K : PreAbstractSimplicialComplex V) (v : V) :
    Realization (deletion K v) → Punctured K v := fun x =>
  ⟨⟨x.1, (mem_carrier_deletion_iff.mp x.2).1⟩,
    by change x.1 v < 1; rw [(mem_carrier_deletion_iff.mp x.2).2]; norm_num⟩

theorem continuous_deletion_inclusion (K : PreAbstractSimplicialComplex V) (v : V) :
    Continuous (deletion_inclusion K v) :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [Fintype V] in
theorem radial_coordinates_of_zero (v : V) (x : V → ℝ) (hv : x v = 0) :
    radial_coordinates v x = x := by
  funext u
  by_cases huv : u = v <;> simp [radial_coordinates, huv, hv]

theorem radial_inclusion (K : PreAbstractSimplicialComplex V) (v : V)
    (x : Realization (deletion K v)) : radial K v (deletion_inclusion K v x) = x := by
  apply Subtype.ext
  exact radial_coordinates_of_zero v x.1 (mem_carrier_deletion_iff.mp x.2).2

def radial_map (K : PreAbstractSimplicialComplex V) (v : V) :
    C(Punctured K v, Realization (deletion K v)) := ⟨radial K v, continuous_radial K v⟩

def deletion_inclusion_map (K : PreAbstractSimplicialComplex V) (v : V) :
    C(Realization (deletion K v), Punctured K v) :=
  ⟨deletion_inclusion K v, continuous_deletion_inclusion K v⟩

/-- The linear homotopy stays in each original simplex and avoids the vertex. -/
def radial_homotopy_point {K : PreAbstractSimplicialComplex V} {v : V}
    (t : unitInterval) (x : Punctured K v) : Punctured K v := by
  let y : V → ℝ := fun u => (1 - (t : ℝ)) * x.1.1 u + (t : ℝ) * radial_coordinates v x.1.1 u
  have hr := radial_coordinates_mem x
  have hy : y ∈ carrier K := by
    obtain ⟨s, hs, hsupport⟩ := x.1.2.2
    refine ⟨⟨?_, ?_⟩, s, hs, ?_⟩
    · intro u
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (coordinate_nonneg x.1 u))
        (mul_nonneg t.2.1 (hr.1.1 u))
    · dsimp [y]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        coordinates_sum x.1, hr.1.2]
      ring
    · intro u hu
      simp [y, hsupport u hu, radial_coordinates]
  refine ⟨⟨y, hy⟩, ?_⟩
  change (1 - (t : ℝ)) * x.1.1 v + (t : ℝ) * radial_coordinates v x.1.1 v < 1
  simp only [radial_coordinates, if_pos, mul_zero, add_zero]
  have hp := coordinate_nonneg x.1 v
  have ht := t.2.1
  have hx := x.2
  nlinarith

theorem continuous_radial_homotopy_point (K : PreAbstractSimplicialComplex V) (v : V) :
    Continuous (fun p : unitInterval × Punctured K v => radial_homotopy_point p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  have ht : Continuous (fun p : unitInterval × Punctured K v => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : unitInterval × Punctured K v => p.2.1.1 u) :=
    (continuous_apply u).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hr : Continuous (fun p : unitInterval × Punctured K v =>
      radial_coordinates v p.2.1.1 u) :=
    (continuous_apply u).comp (continuous_subtype_val.comp
      ((continuous_radial K v).comp continuous_snd))
  exact ((continuous_const.sub ht).mul hx).add (ht.mul hr)

/-- Actual continuous homotopy from the identity to inclusion after radial retraction. -/
def radial_homotopy (K : PreAbstractSimplicialComplex V) (v : V) :
    ContinuousMap.Homotopy (ContinuousMap.id (Punctured K v))
      ((deletion_inclusion_map K v).comp (radial_map K v)) where
  toFun p := radial_homotopy_point p.1 p.2
  continuous_toFun := continuous_radial_homotopy_point K v
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext u
    simp [radial_homotopy_point]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext u
    simp [radial_homotopy_point, radial_map, deletion_inclusion_map,
      deletion_inclusion, radial]

/-- Every point of the deletion is stationary during this homotopy. -/
theorem radial_homotopy_fixes_deletion (K : PreAbstractSimplicialComplex V) (v : V)
    (x : Realization (deletion K v)) (t : unitInterval) :
    radial_homotopy K v (t, deletion_inclusion K v x) = deletion_inclusion K v x := by
  apply Subtype.ext
  apply Subtype.ext
  have hr := radial_coordinates_of_zero v x.1 (mem_carrier_deletion_iff.mp x.2).2
  funext u
  change (1 - (t : ℝ)) * x.1 u + (t : ℝ) * radial_coordinates v x.1 u = x.1 u
  rw [hr]
  ring

/-- The punctured realization is homotopy equivalent to its actual deletion subcomplex. -/
def punctured_deletion_equiv (K : PreAbstractSimplicialComplex V) (v : V) :
    Punctured K v ≃ₕ Realization (deletion K v) where
  toFun := radial_map K v
  invFun := deletion_inclusion_map K v
  left_inv := ⟨(radial_homotopy K v).symm⟩
  right_inv := by
    have h : (radial_map K v).comp (deletion_inclusion_map K v) = ContinuousMap.id _ := by
      apply DFunLike.ext
      intro x
      exact radial_inclusion K v x
    rw [h]

/-- This is the first use of the original contractibility hypothesis. -/
theorem deletion_contractible (K : PreAbstractSimplicialComplex V) (v : V)
    [ContractibleSpace (Punctured K v)] : ContractibleSpace (Realization (deletion K v)) :=
  (punctured_deletion_equiv K v).symm.contractibleSpace

end MathGauge.PublicProof.Topology
