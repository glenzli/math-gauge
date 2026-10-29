import ProfiniteOrbitLocal
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas

noncomputable section
open CategoryTheory Opposite Set
namespace MathGauge.Descent

instance padic_two_infinite : Infinite (ℤ_[2]) :=
  Infinite.of_injective (fun n : ℕ => (n : ℤ_[2])) Nat.cast_injective

theorem padic_two_uncountable : Uncountable (ℤ_[2]) := by
  rw [uncountable_iff_not_countable]
  intro hc
  letI := hc
  obtain ⟨x,y,hy⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun x : ℤ_[2] => ({x} : Set ℤ_[2]))
    (fun x : ℤ_[2] => isClosed_singleton (x := x)) (by ext x; simp)
  have hxy : y = x := mem_singleton_iff.mp (interior_subset hy)
  subst y
  have hi : interior ({x} : Set ℤ_[2]) = {x} :=
    Set.Subset.antisymm interior_subset (singleton_subset_iff.mpr hy)
  have hop : IsOpen ({x} : Set ℤ_[2]) := hi ▸ isOpen_interior
  letI : DiscreteTopology (ℤ_[2]) :=
    (AddAction.IsPretransitive.discreteTopology_iff (ℤ_[2]) x).mpr hop
  haveI : Finite (ℤ_[2]) := finite_of_compact_of_discrete
  exact not_finite (ℤ_[2])

abbrev PadicTwo : Profinite.{0} := Profinite.of (ℤ_[2])

def padic_integer_translation : SpaceAction (Multiplicative ℤ) (ℤ_[2]) where
  act a := Homeomorph.addLeft (a.toAdd : ℤ_[2])
  one x := zero_add x
  mul a b x := by simp [Int.cast_add,add_assoc]

abbrev padic_action : PAction.{1,0,0,0} (Γ := Multiplicative ℤ)
    (prof_probe_sheaf.{0,0} (ℤ_[2])).obj := SpaceAction.probe_action.{0,0,0} padic_integer_translation
abbrev PadicOrbit : ProfSheaf.{0,0} := padic_action.quotient_sheaf ProfSite

theorem padic_orbit_point_nontrivial : Nontrivial (PadicOrbit.obj.obj (op ProfPoint)) := by
  have hns : ¬Function.Surjective (fun n : ℤ => (n : ℤ_[2])) := by
    intro hs
    haveI : Countable (ℤ_[2]) := Function.Surjective.countable hs
    exact ((uncountable_iff_not_countable (ℤ_[2])).mp padic_two_uncountable) inferInstance
  obtain ⟨x,hx⟩ := not_forall.mp hns
  let f : (prof_probe_sheaf.{0,0} (ℤ_[2])).obj.obj (op ProfPoint) := ⟨ContinuousMap.const _ 0⟩
  let g : (prof_probe_sheaf.{0,0} (ℤ_[2])).obj.obj (op ProfPoint) := ⟨ContinuousMap.const _ x⟩
  refine ⟨⟨(padic_action.quotient_projection ProfSite).app _ f,
    (padic_action.quotient_projection ProfSite).app _ g,?_⟩⟩
  intro h
  obtain ⟨a,ha⟩ := (quotient_point_eq_iff padic_action f g).mp h
  have he := congrArg (fun z => z.down PUnit.unit) ha
  change (a.toAdd : ℤ_[2]) + 0 = x at he
  exact hx ⟨a.toAdd,by simpa using he⟩

theorem prof_probe_nat_yoneda {T : Profinite.{0}} {X : Type} [TopologicalSpace X]
    (η : (prof_probe_sheaf.{0,0} T).obj ⟶ (prof_probe_sheaf.{0,0} X).obj)
    (U : Profinite.{0}) (f : C(U,T)) :
    (η.app (op U) ⟨f⟩).down =
      (η.app (op T) ⟨ContinuousMap.id T⟩).down.comp f := by
  let fm : U ⟶ T := CompHausLike.ofHom _ f
  have h := ConcreteCategory.congr_hom (η.naturality fm.op) ⟨ContinuousMap.id T⟩
  exact congrArg ULift.down h

theorem padic_invariant_continuous_constant {X : Type} [TopologicalSpace X] [T2Space X]
    (f : C((ℤ_[2]),X)) (hf : ∀ (n : ℤ) (x : ℤ_[2]), f (n+x) = f x) :
    ∀ x, f x = f 0 := by
  have hclosed : IsClosed {x : ℤ_[2] | f x = f 0} :=
    isClosed_eq f.continuous continuous_const
  have hr : Set.range (fun n : ℤ => (n : ℤ_[2])) ⊆ {x | f x = f 0} := by
    rintro x ⟨n,rfl⟩
    simpa using hf n 0
  have hd : DenseRange (fun n : ℤ => (n : ℤ_[2])) := PadicInt.denseRange_intCast
  intro x
  exact hclosed.closure_subset_iff.mpr hr (hd x)

/-- The dense integer action produces a sheaf quotient with no Hausdorff space realization. -/
theorem padic_quotient_not_hausdorff_probe (X : Type) [TopologicalSpace X] [T2Space X] :
    IsEmpty (PadicOrbit ≅ prof_probe_sheaf.{0,0} X) := by
  constructor
  intro e
  let η := padic_action.quotient_projection ProfSite ≫ e.hom.hom
  let f : C((ℤ_[2]),X) := (η.app (op PadicTwo) ⟨ContinuousMap.id _⟩).down
  have hinv (n : ℤ) : padic_action.act (Multiplicative.ofAdd n) ≫ η = η := by
    dsimp [η]
    rw [← Category.assoc,padic_action.quotient_invariant]
  have hf (n : ℤ) (x : ℤ_[2]) : f (n+x) = f x := by
    let tr : C(PadicTwo,PadicTwo) := ⟨fun x => n+x,continuous_const.add continuous_id⟩
    have hn := congrArg (fun k => (k.app (op PadicTwo) ⟨ContinuousMap.id _⟩).down x) (hinv n)
    have hy := congrArg (fun k : C(PadicTwo,X) => k x) (prof_probe_nat_yoneda η PadicTwo tr)
    exact hy.symm.trans hn
  have hc := padic_invariant_continuous_constant f hf
  have heta : ∀ s : (prof_probe_sheaf.{0,0} (ℤ_[2])).obj.obj (op ProfPoint),
      (η.app (op ProfPoint) s).down PUnit.unit = f 0 := by
    intro s
    have hy := congrArg (fun k : C(ProfPoint,X) => k PUnit.unit)
      (prof_probe_nat_yoneda (T := PadicTwo) (X := X) η ProfPoint s.down)
    exact hy.trans (hc (s.down PUnit.unit))
  have hsub : Subsingleton (PadicOrbit.obj.obj (op ProfPoint)) := by
    constructor
    intro a b
    obtain ⟨s,rfl⟩ := prof_point_locally_surjective.{0,0} (padic_action.quotient_projection ProfSite) a
    obtain ⟨t,rfl⟩ := prof_point_locally_surjective.{0,0} (padic_action.quotient_projection ProfSite) b
    have he : e.hom.hom.app (op ProfPoint)
        ((padic_action.quotient_projection ProfSite).app _ s) =
      e.hom.hom.app (op ProfPoint)
        ((padic_action.quotient_projection ProfSite).app _ t) := by
      apply ULift.ext
      ext z
      have hz : z = PUnit.unit := Subsingleton.elim _ _
      subst z
      exact (heta s).trans (heta t).symm
    have hinj : Function.Injective (e.hom.hom.app (op ProfPoint)) := by
      intro a b hab
      have hi (z) := congrArg (fun k : PadicOrbit ⟶ PadicOrbit => k.hom.app (op ProfPoint) z)
        e.hom_inv_id
      exact (hi a).symm.trans ((congrArg (e.inv.hom.app (op ProfPoint)) hab).trans (hi b))
    exact hinj he
  letI := hsub
  letI := padic_orbit_point_nontrivial
  exact (not_nontrivial (PadicOrbit.obj.obj (op ProfPoint))) inferInstance

end MathGauge.Descent
