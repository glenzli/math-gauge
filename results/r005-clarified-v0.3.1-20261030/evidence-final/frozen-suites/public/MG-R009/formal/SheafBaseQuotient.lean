import SheafBaseChange

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]
variable {H : Sheaf J (Type (max u v w))} (A : PAction (Γ := Γ) H.obj)
variable (B D : Sheaf J (Type (max u v w)))
variable (b : B ⟶ A.quotient_sheaf J) (p : D ⟶ A.quotient_sheaf J)

abbrev basechange_right_record :=
  invariant_fibre_record (pullback_action A B b) (fibre_snd_hom (quotient_hom A) b)
    (pullback_snd_invariant A B b) (fibre_sheaf p b) (fibre_snd_hom p b)

abbrev basechange_right_snd :=
  fibre_snd_hom (fibre_snd_hom (quotient_hom A) b) (fibre_snd_hom p b)

instance basechange_right_snd_local_surjective :
    Presheaf.IsLocallySurjective J (basechange_right_snd A B D b p).hom where
  imageSieve_mem {U} d := by
    let r := fibre_snd (quotient_hom A).hom b.hom
    haveI : Presheaf.IsLocallySurjective J r := pullback_snd_locally_surjective A B b
    have hcov := Presheaf.imageSieve_mem J r d.val.2
    apply J.superset_covering (S := Presheaf.imageSieve r d.val.2) _ hcov
    intro V f hf
    obtain ⟨t,ht⟩ := hf
    exact ⟨⟨(t,(fibre_sheaf p b).obj.map f.op d),ht⟩,rfl⟩

theorem basechange_right_kernel (U : Cᵒᵖ)
    (x y : (basechange_right_record A B D b p).sheaf.obj.obj U)
    (hxy : (basechange_right_snd A B D b p).hom.app U x =
      (basechange_right_snd A B D b p).hom.app U y) :
    (basechange_right_record A B D b p).action.local_orbit_sieve x y ∈ J U.unop := by
  have hs : x.val.1.val.2 = y.val.1.val.2 :=
    x.property.trans ((congrArg (fun z => z.val.2) hxy).trans y.property.symm)
  have hcov := pullback_snd_local_orbits A B b U x.val.1 y.val.1 hs
  apply J.superset_covering (S := (pullback_action A B b).local_orbit_sieve x.val.1 y.val.1) _ hcov
  intro V f hf
  obtain ⟨a,ha⟩ := hf
  refine ⟨a,?_⟩
  apply Subtype.ext
  exact Prod.ext ha (congrArg ((fibre_sheaf p b).obj.map f.op) hxy)

def basechange_right_quotient_to :
    (basechange_right_record A B D b p).action.quotient_sheaf J ⟶ fibre_sheaf p b :=
  (basechange_right_record A B D b p).action.quotient_lift J _
    (basechange_right_snd A B D b p).hom (fun _ => rfl)

instance basechange_right_quotient_isIso : IsIso (basechange_right_quotient_to A B D b p) :=
  (basechange_right_record A B D b p).action.quotient_lift_isIso _ _ (fun _ => rfl)
    (basechange_right_snd_local_surjective A B D b p) (basechange_right_kernel A B D b p)

/-- Taking the quotient after arbitrary sheaf base change gives the pulled-back realization. -/
def basechange_realization_quotient_iso :
    (basechange_record A B b (pullback_equivariant A D p)).action.quotient_sheaf J ≅
      fibre_sheaf p b := by
  exact (equivariant_quotientFunctor (pullback_action A B b)).mapIso
    (basechange_realization_iso A B D b p) ≪≫
      @asIso _ _ _ _ (basechange_right_quotient_to A B D b p)
        (basechange_right_quotient_isIso A B D b p)

end MathGauge.Descent
