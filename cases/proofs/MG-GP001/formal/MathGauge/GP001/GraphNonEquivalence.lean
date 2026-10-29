import MathGauge.GP001.GraphExamples
import MathGauge.GP001.IsolatedVertex
import CoordinateCWBridge
import MathGauge.GP001.Borrowed.Graph.TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
import MathGauge.GP001.Borrowed.Graph.TauCeti.AlgebraicTopology.Sphere.Contractible
import Mathlib.Analysis.Normed.Module.Connected

/-! The two explicit graphs have different homotopy types.  The distinction is
proved on their actual topological realizations, using the isolated component
of the first graph and the two noncontractible circle components of the second. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Finset Set ContinuousMap unitInterval
open MathGauge.PublicProof.Topology MathGauge.PublicProof.Topology.TauBridge

namespace MathGauge.GP001

private theorem map_to_sum_unit_constant {D X : Type*}
    [TopologicalSpace D] [TopologicalSpace X] [PreconnectedSpace X]
    (f : C(X, D ⊕ Unit)) (x₀ : X) (hx : f x₀ = Sum.inr ()) :
    ∀ x, f x = Sum.inr () := by
  intro x
  have ht := TotallyDisconnectedSpace.eq_of_continuous
    (fun x => Sum.isLeft (f x)) (continuous_isLeft.comp f.continuous) x x₀
  rw [hx] at ht
  cases h : f x with
  | inl d => simp [h] at ht
  | inr u => exact congrArg Sum.inr (Subsingleton.elim u ())

private theorem sum_unit_equiv_forces_contractible_left
    {D X Y : Type*} [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace X] (e : (D ⊕ Unit) ≃ₕ (X ⊕ Y)) (x₀ : X)
    (he : e (Sum.inr ()) = Sum.inl x₀) : ContractibleSpace X := by
  let f : C(X, D ⊕ Unit) := e.invFun.comp ⟨Sum.inl, continuous_inl⟩
  have hbase : f x₀ = Sum.inr () := by
    obtain ⟨H⟩ := e.left_inv
    have ht := TotallyDisconnectedSpace.eq_of_continuous
      (fun t : I => Sum.isLeft (H (t, Sum.inr ())))
      (continuous_isLeft.comp (H.continuous.comp (continuous_id.prodMk continuous_const))) 0 1
    simp only [H.apply_zero, H.apply_one, comp_apply, id_apply, he] at ht
    change Sum.isLeft (f x₀) = false at ht
    cases h : f x₀ with
    | inl d => simp [h] at ht
    | inr u => exact congrArg Sum.inr (Subsingleton.elim u ())
  have hf := map_to_sum_unit_constant f x₀ hbase
  let r : C(X ⊕ Y, X) := ⟨Sum.elim id (fun _ => x₀), continuous_id.sumElim continuous_const⟩
  have hh := (Homotopic.refl r).comp
    (e.right_inv.comp (Homotopic.refl (⟨Sum.inl, continuous_inl⟩ : C(X, X ⊕ Y))))
  have hleft : r.comp ((e.toFun.comp e.invFun).comp
      (⟨Sum.inl, continuous_inl⟩ : C(X, X ⊕ Y))) = ContinuousMap.const X x₀ := by
    ext x
    change r (e (f x)) = x₀
    rw [hf x, he]
    rfl
  have hright : r.comp ((ContinuousMap.id (X ⊕ Y)).comp
      (⟨Sum.inl, continuous_inl⟩ : C(X, X ⊕ Y))) = ContinuousMap.id X := by
    ext x
    rfl
  rw [hleft, hright] at hh
  exact (contractible_iff_id_nullhomotopic X).mpr ⟨x₀, hh.symm⟩

/-- A point component cannot be matched to either of two connected,
noncontractible components by a homotopy equivalence. -/
theorem sum_unit_not_equiv_two_noncontractible
    (D X Y : Type*) [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace X] [PreconnectedSpace Y]
    (hx : ¬ ContractibleSpace X) (hy : ¬ ContractibleSpace Y) :
    ¬ Nonempty ((D ⊕ Unit) ≃ₕ (X ⊕ Y)) := by
  rintro ⟨e⟩
  cases he : e (Sum.inr ()) with
  | inl x => exact hx (sum_unit_equiv_forces_contractible_left e x he)
  | inr y =>
    let e' := e.trans (Homeomorph.sumComm X Y).toHomotopyEquiv
    apply hy (sum_unit_equiv_forces_contractible_left e' y ?_)
    change Sum.swap (e (Sum.inr ())) = Sum.inl y
    rw [he]
    rfl

section CoordinatePolyhedron

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem abstractCoordinateHomeomorph_coordinates
    (K : AbstractSimplicialComplex V)
    (x : CoordinateRealization K.toPreAbstractSimplicialComplex) :
    ((abstractCoordinateHomeomorph K x).1 : V → ℝ) = x.1 := by
  exact K.coe_realizationHomeomorphRange_symm_apply (Set.toFinite K.faces) _

private def coordinatePolyhedronMap (P : PreAbstractSimplicialComplex V) :
    C(Realization P,
      {x : AbstractSimplicialComplex.Realization (⊤ : AbstractSimplicialComplex V) //
        x.1.support ∈ P}) := by
  let topInclusion : C(Realization P,
      CoordinateRealization (⊤ : AbstractSimplicialComplex V).toPreAbstractSimplicialComplex) :=
    ⟨fun x => ⟨x.1, x.2.1, by
      obtain ⟨s, hs, hx⟩ := x.2.2
      exact ⟨s, PreAbstractSimplicialComplex.le_top P hs, hx⟩⟩,
      continuous_subtype_val.subtype_mk _⟩
  let f : C(Realization P,
      AbstractSimplicialComplex.Realization (⊤ : AbstractSimplicialComplex V)) :=
    ⟨fun x => abstractCoordinateHomeomorph _ (topInclusion x),
      (abstractCoordinateHomeomorph _).continuous.comp topInclusion.continuous⟩
  have hf (x : Realization P) : (f x).1.support ∈ P := by
    have he : (f x).1 = Finsupp.equivFunOnFinite.symm x.1 := by
      apply Finsupp.ext
      intro v
      exact congrFun (abstractCoordinateHomeomorph_coordinates _ (topInclusion x)) v
    rw [he]
    exact ((coordinateCarrier_iff_support P x.1).mp x.2).2.2
  exact ⟨fun x => ⟨f x, hf x⟩, f.continuous.subtype_mk _⟩

private theorem coordinatePolyhedronMap_coordinates (P : PreAbstractSimplicialComplex V)
    (x : Realization P) :
    ((coordinatePolyhedronMap P x).1.1 : V → ℝ) = x.1 :=
  abstractCoordinateHomeomorph_coordinates _ _

private theorem coordinatePolyhedronMap_bijective (P : PreAbstractSimplicialComplex V) :
    Function.Bijective (coordinatePolyhedronMap P) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact (coordinatePolyhedronMap_coordinates P x).symm.trans
      ((congrArg (fun z => (z.1.1 : V → ℝ)) h).trans
        (coordinatePolyhedronMap_coordinates P y))
  · intro y
    have hy := TauCeti.mem_standardGeometricComplex_space_iff.mp y.1.2
    have hcoord : (y.1.1 : V → ℝ) ∈ coordinateCarrier P := by
      apply (coordinateCarrier_iff_support P _).mpr
      refine ⟨hy.1, ?_, ?_⟩
      · exact (Finsupp.sum_fintype y.1.1 (fun _ r => r) (fun _ => rfl)).symm.trans hy.2.1
      · simpa using y.2
    let x : Realization P := ⟨y.1.1, hcoord⟩
    refine ⟨x, Subtype.ext (Subtype.ext ?_)⟩
    apply Finsupp.ext
    intro v
    exact congrFun (coordinatePolyhedronMap_coordinates P x) v

/-- Every finite coordinate precomplex is the actual same support-defined
polyhedron in the weak realization of the full ambient simplex. -/
def coordinatePolyhedronHomeomorph (P : PreAbstractSimplicialComplex V) :
    Realization P ≃ₜ
      {x : AbstractSimplicialComplex.Realization (⊤ : AbstractSimplicialComplex V) //
        x.1.support ∈ P} :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (coordinatePolyhedronMap P) (coordinatePolyhedronMap_bijective P))
    (coordinatePolyhedronMap P).continuous

/-- The boundary sphere theorem applies to the old coordinate realization
without adding any unused vertices as faces. -/
theorem coordinate_boundary_sphere (s : Finset V) (hs : s.card = 3) :
    Nonempty (Realization (PreAbstractSimplicialComplex.simplexBoundary s) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  obtain ⟨e⟩ := PreAbstractSimplicialComplex.nonempty_homeomorph_simplexBoundary_sphere
    (n := 1) hs (PreAbstractSimplicialComplex.le_top _)
  exact ⟨(coordinatePolyhedronHomeomorph _).trans e⟩

end CoordinatePolyhedron

section DisjointRealizations

variable {V : Type*} [Fintype V] [DecidableEq V]

private def realizationSupSumMap (P Q : PreAbstractSimplicialComplex V) :
    C(Realization P ⊕ Realization Q, Realization (P ⊔ Q)) := by
  let f : C(Realization P, Realization (P ⊔ Q)) :=
    ⟨fun x => ⟨x.1, x.2.1, by
      obtain ⟨s, hs, hx⟩ := x.2.2
      exact ⟨s, Or.inl hs, hx⟩⟩, continuous_subtype_val.subtype_mk _⟩
  let g : C(Realization Q, Realization (P ⊔ Q)) :=
    ⟨fun x => ⟨x.1, x.2.1, by
      obtain ⟨s, hs, hx⟩ := x.2.2
      exact ⟨s, Or.inr hs, hx⟩⟩, continuous_subtype_val.subtype_mk _⟩
  exact ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩

private theorem disjoint_realization_ne (P Q : PreAbstractSimplicialComplex V)
    (hd : ∀ s ∈ P, ∀ t ∈ Q, Disjoint s t)
    (x : Realization P) (y : Realization Q) : x.1 ≠ y.1 := by
  intro h
  obtain ⟨s, hs, hxs⟩ := x.2.2
  obtain ⟨t, ht, hyt⟩ := y.2.2
  have hz : ∀ v, x.1 v = 0 := by
    intro v
    by_cases hv : v ∈ s
    · rw [h]
      exact hyt v (fun hv' => Finset.disjoint_left.mp (hd s hs t ht) hv hv')
    · exact hxs v hv
  have hone := coordinates_sum x
  simp [hz] at hone

private theorem realizationSupSumMap_bijective (P Q : PreAbstractSimplicialComplex V)
    (hd : ∀ s ∈ P, ∀ t ∈ Q, Disjoint s t) :
    Function.Bijective (realizationSupSumMap P Q) := by
  constructor
  · intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        exact Subtype.ext (congrArg (fun z : Realization (P ⊔ Q) => z.1) he)
      | inr y => exact (disjoint_realization_ne P Q hd x y (congrArg Subtype.val he)).elim
    | inr x =>
      cases y with
      | inl y => exact (disjoint_realization_ne P Q hd y x (congrArg Subtype.val he).symm).elim
      | inr y =>
        apply congrArg Sum.inr
        exact Subtype.ext (congrArg (fun z : Realization (P ⊔ Q) => z.1) he)
  · intro x
    obtain ⟨s, hs | hs, hx⟩ := x.2.2
    · exact ⟨Sum.inl ⟨x.1, x.2.1, s, hs, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x.1, x.2.1, s, hs, hx⟩, rfl⟩

/-- On genuinely disjoint vertex sets, the realization of a union is the
topological disjoint union, by the actual coordinate inclusions. -/
def realizationDisjointSumHomeomorph (P Q : PreAbstractSimplicialComplex V)
    (hd : ∀ s ∈ P, ∀ t ∈ Q, Disjoint s t) :
    (Realization P ⊕ Realization Q) ≃ₜ Realization (P ⊔ Q) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (realizationSupSumMap P Q) (realizationSupSumMap_bijective P Q hd))
    (realizationSupSumMap P Q).continuous

end DisjointRealizations

def firstTriangle : PreAbstractSimplicialComplex (Fin 6) :=
  PreAbstractSimplicialComplex.simplexBoundary {0, 1, 2}

def secondTriangle : PreAbstractSimplicialComplex (Fin 6) :=
  PreAbstractSimplicialComplex.simplexBoundary {3, 4, 5}

instance firstTriangle_decidable (s : Finset (Fin 6)) : Decidable (s ∈ firstTriangle) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ s ⊂ {0, 1, 2}))

instance secondTriangle_decidable (s : Finset (Fin 6)) : Decidable (s ∈ secondTriangle) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ s ⊂ {3, 4, 5}))

theorem graphTwo_eq_triangles : graphTwo = firstTriangle ⊔ secondTriangle := by
  apply SetLike.ext
  exact (by decide : ∀ s : Finset (Fin 6),
    s ∈ graphTwo ↔ s ∈ firstTriangle ∨ s ∈ secondTriangle)

theorem triangle_faces_disjoint :
    ∀ s ∈ firstTriangle, ∀ t ∈ secondTriangle, Disjoint s t := by decide

theorem graphOne_vertex_five : ({5} : Finset (Fin 6)) ∈ graphOne := by decide

instance graphOne_empty_link_five : IsEmpty (Realization (vertex_link graphOne 5)) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨s, hs, _⟩ := x.2.2
  exact (by decide : ∀ s : Finset (Fin 6),
    ¬ (s.Nonempty ∧ (5 : Fin 6) ∉ s ∧ insert 5 s ∈ graphOne)) s hs

/-- The two components really are circle spaces, rather than spaces with only
matching low-degree homology. -/
theorem firstTriangle_sphere :
    Nonempty (Realization firstTriangle ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  coordinate_boundary_sphere {0, 1, 2} (by decide)

theorem secondTriangle_sphere :
    Nonempty (Realization secondTriangle ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  coordinate_boundary_sphere {3, 4, 5} (by decide)

private instance plane_sphere_connected :
    ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  apply (isConnected_iff_connectedSpace).mp
  apply isConnected_sphere
  · rw [← Module.finrank_eq_rank]
    norm_num
  · norm_num

instance firstTriangle_connected : ConnectedSpace (Realization firstTriangle) := by
  obtain ⟨e⟩ := firstTriangle_sphere
  exact e.connectedSpace_iff.mpr inferInstance

instance secondTriangle_connected : ConnectedSpace (Realization secondTriangle) := by
  obtain ⟨e⟩ := secondTriangle_sphere
  exact e.connectedSpace_iff.mpr inferInstance

theorem firstTriangle_not_contractible : ¬ ContractibleSpace (Realization firstTriangle) := by
  intro h
  letI := h
  obtain ⟨e⟩ := firstTriangle_sphere
  exact TauCeti.not_contractibleSpace_sphere e.symm.contractibleSpace

theorem secondTriangle_not_contractible : ¬ ContractibleSpace (Realization secondTriangle) := by
  intro h
  letI := h
  obtain ⟨e⟩ := secondTriangle_sphere
  exact TauCeti.not_contractibleSpace_sphere e.symm.contractibleSpace

def graphTwo_sum_homeomorph :
    (Realization firstTriangle ⊕ Realization secondTriangle) ≃ₜ Realization graphTwo :=
  (realizationDisjointSumHomeomorph _ _ triangle_faces_disjoint).trans
    (Homeomorph.setCongr (congrArg carrier graphTwo_eq_triangles.symm))

/-- S6 negative half: the explicit six-vertex graphs are not homotopy
equivalent. The first has an isolated point component, whereas both components
of the second are proved homeomorphic to the circle and noncontractible. -/
theorem graph_not_homotopy_equiv :
    ¬ Nonempty (Realization graphOne ≃ₕ Realization graphTwo) := by
  rintro ⟨e⟩
  apply sum_unit_not_equiv_two_noncontractible
    (Realization (deletion graphOne 5)) (Realization firstTriangle) (Realization secondTriangle)
    firstTriangle_not_contractible secondTriangle_not_contractible
  exact ⟨(isolatedSumHomeomorph graphOne 5 graphOne_vertex_five).toHomotopyEquiv.trans
    (e.trans graphTwo_sum_homeomorph.symm.toHomotopyEquiv)⟩

end MathGauge.GP001
