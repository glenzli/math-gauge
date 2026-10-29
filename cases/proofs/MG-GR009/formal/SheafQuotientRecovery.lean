import SheafDescentCriterion

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]

namespace PAction
variable {H : Cᵒᵖ ⥤ Type (max u v w)} (A : PAction (Γ := Γ) H)

/-- A local-orbit quotient criterion; below it is instantiated by the actual pullback projection. -/
theorem quotient_lift_isIso (D : Sheaf J (Type (max u v w))) (r : H ⟶ D.obj)
    (hr : A.Invariant r) (hs : Presheaf.IsLocallySurjective J r)
    (hker : ∀ (U : Cᵒᵖ) (x y : H.obj U), r.app U x = r.app U y →
      A.local_orbit_sieve x y ∈ J U.unop) :
    IsIso (A.quotient_lift J D r hr) := by
  letI := hs
  letI := large_local_surjective_toSheafify.{u,v,w} J A.orbit_presheaf
  letI := large_local_injective_toSheafify.{u,v,w} J A.orbit_presheaf
  let rbar := A.orbit_lift r hr
  let φ := A.quotient_lift J D r hr
  have hfac : J.toSheafify A.orbit_presheaf ≫ φ.hom = rbar :=
    J.toSheafify_sheafifyLift _ D.property
  letI hsur : Presheaf.IsLocallySurjective J rbar := by
    apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (A.orbit_lift_fac r hr)
  letI hinj : Presheaf.IsLocallyInjective J rbar := by
    constructor
    intro U x y hxy
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        change Presheaf.equalizerSieve (F := A.orbit_presheaf)
          (A.orbit_projection.app U x) (A.orbit_projection.app U y) ∈ J U.unop
        rw [← A.local_orbit_sieve_eq]
        exact hker U x y hxy
  letI hc : Presheaf.IsLocallyInjective J (J.toSheafify A.orbit_presheaf ≫ φ.hom) := by
    rw [hfac]
    exact hinj
  letI hc' : Presheaf.IsLocallySurjective J (J.toSheafify A.orbit_presheaf ≫ φ.hom) := by
    rw [hfac]
    exact hsur
  letI hφi : Presheaf.IsLocallyInjective J φ.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J
      (J.toSheafify A.orbit_presheaf) φ.hom
  letI hφs : Presheaf.IsLocallySurjective J φ.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J (J.toSheafify A.orbit_presheaf) φ.hom
  exact (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨hφi,hφs⟩

end PAction

variable {H : Sheaf J (Type (max u v w))} (A : PAction (Γ := Γ) H.obj)
variable (D : Sheaf J (Type (max u v w))) (p : D ⟶ A.quotient_sheaf J)

theorem pullback_snd_invariant :
    (pullback_action A D p).Invariant (fibre_snd (quotient_hom A).hom p.hom) := by
  intro a
  rfl

instance pullback_snd_locally_surjective :
    Presheaf.IsLocallySurjective J (fibre_snd (quotient_hom A).hom p.hom) where
  imageSieve_mem {U} d := by
    have hcov := Presheaf.imageSieve_mem J (A.quotient_projection J) (p.hom.app (op U) d)
    apply J.superset_covering (S := Presheaf.imageSieve (A.quotient_projection J)
      (p.hom.app (op U) d)) _ hcov
    intro V f hf
    obtain ⟨t,ht⟩ := hf
    refine ⟨⟨(t,D.obj.map f.op d), ?_⟩,rfl⟩
    exact ht.trans (nat_restrict p.hom f.op d)

theorem pullback_snd_local_orbits (U : Cᵒᵖ)
    (x y : (fibre_sheaf (quotient_hom A) p).obj.obj U) (hxy : x.val.2 = y.val.2) :
    (pullback_action A D p).local_orbit_sieve x y ∈ J U.unop := by
  have hq : (A.quotient_projection J).app U x.val.1 =
      (A.quotient_projection J).app U y.val.1 :=
    x.property.trans ((congrArg (p.hom.app U) hxy).trans y.property.symm)
  have hcov := (A.quotient_eq_iff_local_orbit J U x.val.1 y.val.1).mp hq
  apply J.superset_covering (S := A.local_orbit_sieve x.val.1 y.val.1) _ hcov
  intro V f hf
  obtain ⟨a,ha⟩ := hf
  refine ⟨a,?_⟩
  apply Subtype.ext
  exact Prod.ext ha (congrArg (D.obj.map f.op) hxy)

/-- The quotient of H×Q D is D, for an arbitrary sheaf D, not only a representable one. -/
def pullback_quotient_to : (pullback_action A D p).quotient_sheaf J ⟶ D :=
  (pullback_action A D p).quotient_lift J D (fibre_snd (quotient_hom A).hom p.hom)
    (pullback_snd_invariant A D p)

instance pullback_quotient_isIso : IsIso (pullback_quotient_to A D p) := by
  exact (pullback_action A D p).quotient_lift_isIso D
    (fibre_snd (quotient_hom A).hom p.hom) (pullback_snd_invariant A D p)
    (pullback_snd_locally_surjective A D p)
    (pullback_snd_local_orbits A D p)

def pullback_quotient_iso : (pullback_action A D p).quotient_sheaf J ≅ D :=
  asIso (pullback_quotient_to A D p)

@[simp] theorem pullback_quotient_fac :
    (pullback_action A D p).quotient_projection J ≫ (pullback_quotient_to A D p).hom =
      fibre_snd (quotient_hom A).hom p.hom :=
  (pullback_action A D p).quotient_lift_fac J D _ _

end MathGauge.Descent
