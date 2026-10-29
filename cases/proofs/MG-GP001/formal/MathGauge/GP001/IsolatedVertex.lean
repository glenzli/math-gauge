import GeneralSuspensionClassification
import FiniteCones
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homotopy.Path

namespace MathGauge.GP001
noncomputable section
open MathGauge.PublicProof.Topology
open ContinuousMap Set unitInterval

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem coordinate_zero_or_one_of_empty_link (K : PreAbstractSimplicialComplex V)
    (v : V) [IsEmpty (Realization (vertex_link K v))] (x : Realization K) :
    x.1 v = 0 ∨ x.1 v = 1 := by
  by_cases h0 : x.1 v = 0
  · exact Or.inl h0
  by_cases h1 : x.1 v = 1
  · exact Or.inr h1
  have hp : 0 < x.1 v := lt_of_le_of_ne (coordinate_nonneg x v) (Ne.symm h0)
  have hl : x.1 v < 1 := lt_of_le_of_ne (coordinate_le_one x v) h1
  obtain ⟨w, hwv, hw⟩ := edge_of_coordinate_between x v hp hl
  have hwlink : ({w} : Finset V) ∈ vertex_link K v :=
    ⟨Finset.singleton_nonempty _, by simpa using hwv.symm, hw⟩
  exact isEmptyElim (vertex (vertex_link K v) w hwlink)

def isolatedSumMap (K : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ K) :
    C(Realization (deletion K v) ⊕ Unit, Realization K) :=
  ⟨Sum.elim (deletion_to_realization K v) (fun _ => vertex K v hv),
    (deletion_to_realization K v).continuous.sumElim continuous_const⟩

theorem isolatedSumMap_bijective (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ K) [IsEmpty (Realization (vertex_link K v))] :
    Function.Bijective (isolatedSumMap K v hv) := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : Realization K => z.1) hab))
      | inr b =>
        have h0 := (mem_carrier_deletion_iff.mp a.2).2
        have he := congrArg (fun x : Realization K => x.1 v) hab
        change a.1 v = (vertex K v hv).1 v at he
        simp [vertex, h0] at he
    | inr a =>
      cases b with
      | inl b =>
        have h0 := (mem_carrier_deletion_iff.mp b.2).2
        have he := congrArg (fun x : Realization K => x.1 v) hab
        change (vertex K v hv).1 v = b.1 v at he
        simp [vertex, h0] at he
      | inr b => exact congrArg Sum.inr (Subsingleton.elim _ _)
  · intro x
    rcases coordinate_zero_or_one_of_empty_link K v x with h0 | h1
    · exact ⟨Sum.inl ⟨x.1, mem_carrier_deletion_iff.mpr ⟨x.2, h0⟩⟩, rfl⟩
    · exact ⟨Sum.inr (), ((coordinate_eq_one_iff x v hv).mp h1).symm⟩

def isolatedSumHomeomorph (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ K) [IsEmpty (Realization (vertex_link K v))] :
    (Realization (deletion K v) ⊕ Unit) ≃ₜ Realization K :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (isolatedSumMap K v hv) (isolatedSumMap_bijective K v hv))
    (isolatedSumMap K v hv).continuous

/-- A contractible component plus an isolated point has exactly the homotopy
type of the two-point discrete space. -/
def contractibleSumUnitEquiv (D : Type*) [TopologicalSpace D] [ContractibleSpace D] :
    (D ⊕ Unit) ≃ₕ (Unit ⊕ Unit) := by
  let c := (id_nullhomotopic D).choose
  let H := (id_nullhomotopic D).choose_spec.some
  let f : C(D ⊕ Unit, Unit ⊕ Unit) :=
    ⟨Sum.map (fun _ => ()) id, continuous_const.sumMap continuous_id⟩
  let g : C(Unit ⊕ Unit, D ⊕ Unit) :=
    ⟨Sum.map (fun _ => c) id, continuous_const.sumMap continuous_id⟩
  let F : C(I × (D ⊕ Unit), D ⊕ Unit) :=
    ⟨(Sum.elim (fun p : I × D => Sum.inl (H p))
      (fun p : I × Unit => Sum.inr p.2)) ∘ (Homeomorph.prodSumDistrib : I × (D ⊕ Unit) ≃ₜ (I × D) ⊕ (I × Unit)),
      ((continuous_inl.comp H.continuous).sumElim
        (continuous_inr.comp continuous_snd)).comp
          ((Homeomorph.prodSumDistrib : I × (D ⊕ Unit) ≃ₜ (I × D) ⊕ (I × Unit))).continuous⟩
  let HF : (ContinuousMap.id (D ⊕ Unit)).Homotopy (g.comp f) :=
    { toContinuousMap := F
      map_zero_left := by intro x; cases x <;> simp [F, Homeomorph.prodSumDistrib, Homeomorph.sumCongr, H.apply_zero]
      map_one_left := by intro x; cases x <;> simp [F, f, g, c, Homeomorph.prodSumDistrib, Homeomorph.sumCongr, H.apply_one] }
  refine { toFun := f, invFun := g, left_inv := ⟨HF.symm⟩, right_inv := ?_ }
  have he : f.comp g = ContinuousMap.id (Unit ⊕ Unit) := by
    ext x
    cases x <;> rfl
  rw [he]

theorem empty_link_classification (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ K) [IsEmpty (Realization (vertex_link K v))]
    [ContractibleSpace (Punctured K v)] :
    Nonempty (Realization K ≃ₕ (Unit ⊕ Unit)) := by
  letI : ContractibleSpace (Realization (deletion K v)) := deletion_contractible K v
  exact ⟨(isolatedSumHomeomorph K v hv).symm.toHomotopyEquiv.trans
    (contractibleSumUnitEquiv (Realization (deletion K v)))⟩

theorem classification_without_B (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : {v} ∈ K) [ContractibleSpace (Punctured K v)] :
    Nonempty (Realization K ≃ₕ (Unit ⊕ Unit)) ∨
      (Nonempty (Realization (vertex_link K v)) ∧
        Nonempty (Realization K ≃ₕ Susp (Realization (vertex_link K v)))) := by
  cases isEmpty_or_nonempty (Realization (vertex_link K v)) with
  | inl h =>
    letI := h
    exact Or.inl (empty_link_classification K v hv)
  | inr h =>
    letI := h
    letI : ContractibleSpace (Realization (deletion K v)) := deletion_contractible K v
    exact Or.inr ⟨h, general_suspension_classification K v⟩

instance suspensionPathConnected (X : Type*) [TopologicalSpace X] [Nonempty X] :
    PathConnectedSpace (Susp X) := by
  letI : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected (by exact ⟨0, le_rfl, zero_le_one⟩))
  have hj (z : Susp X) : Joined (Susp.south X) z := by
    obtain ⟨⟨t, x⟩, rfl⟩ := Susp.mk_surjective z
    have h := (PathConnectedSpace.joined (0 : I) t).map
      (f := fun s : I => (Susp.mk (s, x) : Susp X))
      (Susp.mk.continuous.comp (continuous_id.prodMk continuous_const))
    simpa only [Susp.mk_zero] using h
  exact ⟨⟨Susp.south X⟩, fun x y => (hj x).symm.trans (hj y)⟩

theorem pathConnected_of_homotopyEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (e : X ≃ₕ Y) : PathConnectedSpace Y := by
  obtain ⟨H⟩ := e.right_inv
  refine ⟨⟨e (Classical.choice (inferInstance : Nonempty X))⟩, fun y z => ?_⟩
  have hy : Joined (e.toFun (e.invFun y)) y := ⟨H.evalAt y⟩
  have hz : Joined (e.toFun (e.invFun z)) z := ⟨H.evalAt z⟩
  exact hy.symm.trans ((PathConnectedSpace.joined (e.invFun y) (e.invFun z)).map
    e.toFun.continuous) |>.trans hz

theorem twoPoints_not_pathConnected : ¬ PathConnectedSpace (Unit ⊕ Unit) := by
  intro h
  letI := h
  haveI : Subsingleton (Unit ⊕ Unit) := subsingleton_of_preconnected_totallyDisconnected
  have he := Subsingleton.elim (Sum.inl () : Unit ⊕ Unit) (Sum.inr ())
  cases he

theorem twoPoints_not_nonempty_suspension (X : Type*) [TopologicalSpace X] [Nonempty X] :
    ¬ Nonempty ((Unit ⊕ Unit) ≃ₕ Susp X) := by
  rintro ⟨e⟩
  exact twoPoints_not_pathConnected (pathConnected_of_homotopyEquiv e.symm)

def twoIsolatedVertices : PreAbstractSimplicialComplex Bool :=
  two_cones ⊥ false true

theorem twoIsolatedVertices_vertex : ({false} : Finset Bool) ∈ twoIsolatedVertices :=
  Or.inl (cone_apex_face ⊥ false)

theorem twoIsolatedVertices_punctured_contractible :
    ContractibleSpace (Punctured twoIsolatedVertices false) :=
  punctured_two_cones_contractible ⊥ false true (by decide) (by intro s hs; exact False.elim hs)

instance twoIsolatedVertices_empty_link :
    IsEmpty (Realization (vertex_link twoIsolatedVertices false)) := by
  have he : vertex_link twoIsolatedVertices false =
      (⊥ : PreAbstractSimplicialComplex Bool) :=
    link_two_cones ⊥ false true (by decide) (by intro s hs; exact False.elim hs)
  rw [he]
  exact ⟨fun x => by obtain ⟨s, hs, _⟩ := x.2.2; exact hs⟩

/-- An actual two-vertex finite simplicial complex supplies the new S⁰ type,
which is excluded by the nonempty suspension conclusion in the original task. -/
theorem counterexample_without_B (X : Type*) [TopologicalSpace X] [Nonempty X] :
    ContractibleSpace (Punctured twoIsolatedVertices false) ∧
      ¬ Nonempty (Realization twoIsolatedVertices ≃ₕ Susp X) := by
  refine ⟨twoIsolatedVertices_punctured_contractible, ?_⟩
  letI := twoIsolatedVertices_punctured_contractible
  obtain ⟨e⟩ := empty_link_classification twoIsolatedVertices false twoIsolatedVertices_vertex
  rintro ⟨h⟩
  exact twoPoints_not_nonempty_suspension X ⟨e.symm.trans h⟩

end
end MathGauge.GP001
