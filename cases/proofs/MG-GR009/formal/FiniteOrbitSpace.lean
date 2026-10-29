import ProfiniteOrbitLocal
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Separation.Profinite

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite TopologicalSpace
universe u g w
namespace MathGauge.Descent.FiniteOrbit
variable {Γ : Type g} [Group Γ] [Finite Γ]
variable (T : Profinite.{u}) [MulAction Γ T] [ContinuousConstSMul Γ T]

abbrev Orbit := Quotient (MulAction.orbitRel Γ T)

/-- The actual orbit quotient is Hausdorff and compact. Its clopen basis is
obtained by taking images of clopen neighborhoods under the open quotient map. -/
instance orbitTotallySeparated : TotallySeparatedSpace (Orbit (Γ := Γ) T) := by
  apply totallySeparatedSpace_of_t0_of_basis_clopen
  apply isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.isOpen)
  intro x U hx hU
  obtain ⟨t,rfl⟩ := Quotient.mk_surjective x
  obtain ⟨V,hV,ht,hVU⟩ := compact_exists_isClopen_in_isOpen
    (hU.preimage (continuous_quot_mk : Continuous (Quotient.mk (MulAction.orbitRel Γ T)))) hx
  let q : T → Orbit (Γ := Γ) T := Quotient.mk (MulAction.orbitRel Γ T)
  letI : T2Space (Quot (MulAction.orbitRel Γ T)) :=
    (inferInstance : T2Space (Quotient (MulAction.orbitRel Γ T)))
  refine ⟨q '' V,⟨?_,?_⟩,⟨t,ht,rfl⟩,?_⟩
  · exact (continuous_quot_mk : Continuous q).isClosedMap V hV.isClosed
  · exact isOpenMap_quotient_mk'_mul V hV.isOpen
  · rintro z ⟨t,ht,rfl⟩
    exact hVU ht

def orbitSpace : Profinite.{u} := Profinite.of (Orbit (Γ := Γ) T)

def quotientMap : C(T,orbitSpace (Γ := Γ) T) :=
  ⟨Quotient.mk (MulAction.orbitRel Γ T),continuous_quot_mk⟩

theorem quotientMap_surjective : Function.Surjective (quotientMap (Γ := Γ) T) :=
  Quotient.mk_surjective

theorem quotientMap_eq_iff (x y : T) :
    quotientMap (Γ := Γ) T x=quotientMap T y ↔ ∃ a : Γ, a • x=y := by
  change Quotient.mk (MulAction.orbitRel Γ T) x=Quotient.mk (MulAction.orbitRel Γ T) y ↔ _
  rw [Quotient.eq]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a⁻¹,by rw [← ha]; exact inv_smul_smul a y⟩
  · rintro ⟨a,ha⟩
    exact ⟨a⁻¹,by rw [← ha]; exact inv_smul_smul a x⟩

def spaceAction : SpaceAction Γ T where
  act := Homeomorph.smul
  one := one_smul Γ
  mul := mul_smul

abbrev action : PAction (Γ := Γ) (prof_probe_sheaf.{u,w} T).obj :=
  (spaceAction (Γ := Γ) T).probe_action

def quotientProbe : prof_probe_sheaf.{u,w} T ⟶ prof_probe_sheaf.{u,w} (orbitSpace (Γ := Γ) T) :=
  ⟨(MathGauge.Mapping.lift_nat_equiv _ _) (MathGauge.Mapping.probe_post (quotientMap T))⟩

theorem quotientProbe_invariant : (action (Γ := Γ) T).Invariant (quotientProbe (Γ := Γ) T).hom := by
  intro a
  ext U f x
  change quotientMap (Γ := Γ) T (a • f.down x)=quotientMap T (f.down x)
  exact Quotient.sound ⟨a,rfl⟩

end MathGauge.Descent.FiniteOrbit
