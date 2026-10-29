import SheafUniverseLocal
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.Condensed.TopComparison
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.GroupTheory.GroupAction.Quotient

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent

variable {C : Type u} [Category.{v} C]
variable {Γ : Type g} [Group Γ]

/-- An actual natural group action, with no descent conclusion included in its fields. -/
structure PAction (H : Cᵒᵖ ⥤ Type (max u v w)) where
  act : Γ → (H ⟶ H)
  one : act 1 = 𝟙 H
  mul : ∀ a b, act (a*b) = act b ≫ act a

namespace PAction
variable {H : Cᵒᵖ ⥤ Type (max u v w)} (A : PAction (Γ := Γ) H)

@[simp] theorem one_apply (U : Cᵒᵖ) (x : H.obj U) : (A.act 1).app U x = x := by rw [A.one]; rfl

@[simp] theorem mul_apply (a b : Γ) (U : Cᵒᵖ) (x : H.obj U) :
    (A.act (a*b)).app U x = (A.act a).app U ((A.act b).app U x) := by rw [A.mul]; rfl

@[simp] theorem inv_apply (a : Γ) (U : Cᵒᵖ) (x : H.obj U) :
    (A.act a⁻¹).app U ((A.act a).app U x) = x := by
  rw [← A.mul_apply, inv_mul_cancel, A.one_apply]

theorem restrict_act {U V : Cᵒᵖ} (f : U ⟶ V) (a : Γ) (x : H.obj U) :
    H.map f ((A.act a).app U x) = (A.act a).app V (H.map f x) :=
  (ConcreteCategory.congr_hom ((A.act a).naturality f) x).symm

def orbit_setoid (U : Cᵒᵖ) : Setoid (H.obj U) where
  r x y := ∃ a : Γ, (A.act a).app U x = y
  iseqv := {
    refl x := ⟨1,A.one_apply U x⟩
    symm := by
      rintro x y ⟨a,rfl⟩
      exact ⟨a⁻¹,A.inv_apply a U x⟩
    trans := by
      rintro x y z ⟨a,rfl⟩ ⟨b,rfl⟩
      exact ⟨b*a,A.mul_apply b a U x⟩ }

abbrev orbit_presheaf : Cᵒᵖ ⥤ Type (max u v w) where
  obj U := Quotient (A.orbit_setoid U)
  map f := Quotient.map (H.map f) (by
    rintro x y ⟨a,ha⟩
    exact ⟨a, (A.restrict_act f a x).symm.trans (congrArg (H.map f) ha)⟩)
  map_id U := by
    funext x
    induction x using Quotient.inductionOn with
    | h x => change Quotient.mk (A.orbit_setoid U) (H.map (𝟙 U) x) = _; simp
  map_comp f g := by
    funext x
    induction x using Quotient.inductionOn with
    | h x => change Quotient.mk (A.orbit_setoid _) (H.map (f ≫ g) x) = _; simp

def orbit_projection : H ⟶ A.orbit_presheaf where
  app U := Quotient.mk (A.orbit_setoid U)
  naturality := by intros; rfl

theorem orbit_projection_surjective (U : Cᵒᵖ) :
    Function.Surjective (A.orbit_projection.app U) := Quotient.mk_surjective

theorem orbit_projection_eq (U : Cᵒᵖ) (x y : H.obj U) :
    A.orbit_projection.app U x = A.orbit_projection.app U y ↔
      ∃ a : Γ, (A.act a).app U x = y := Quotient.eq

theorem orbit_projection_invariant (a : Γ) : A.act a ≫ A.orbit_projection = A.orbit_projection := by
  ext U x
  exact Quotient.sound ⟨a⁻¹,A.inv_apply a U x⟩

def Invariant {Y : Cᵒᵖ ⥤ Type (max u v w)} (b : H ⟶ Y) : Prop :=
  ∀ a : Γ, A.act a ≫ b = b

def orbit_lift {Y : Cᵒᵖ ⥤ Type (max u v w)} (b : H ⟶ Y) (hb : A.Invariant b) :
    A.orbit_presheaf ⟶ Y where
  app U := Quotient.lift (b.app U) (by
    rintro x y ⟨a,rfl⟩
    exact (congrArg (fun η : H ⟶ Y => η.app U x) (hb a)).symm)
  naturality := by
    intro U V f
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact ConcreteCategory.congr_hom (b.naturality f) x

@[simp] theorem orbit_lift_fac {Y : Cᵒᵖ ⥤ Type (max u v w)}
    (b : H ⟶ Y) (hb : A.Invariant b) : A.orbit_projection ≫ A.orbit_lift b hb = b := rfl

theorem orbit_hom_ext {Y : Cᵒᵖ ⥤ Type (max u v w)} (f h : A.orbit_presheaf ⟶ Y)
    (he : A.orbit_projection ≫ f = A.orbit_projection ≫ h) : f = h := by
  ext U q
  obtain ⟨x,rfl⟩ := A.orbit_projection_surjective U q
  exact congrArg (fun η : H ⟶ Y => η.app U x) he

variable (J : GrothendieckTopology C)

/-- The genuine sheafification of the pointwise orbit presheaf. -/
def quotient_sheaf : Sheaf J (Type (max u v w)) :=
  ⟨J.sheafify A.orbit_presheaf, J.sheafify_isSheaf A.orbit_presheaf⟩

def quotient_projection : H ⟶ (A.quotient_sheaf J).obj :=
  A.orbit_projection ≫ J.toSheafify A.orbit_presheaf

theorem quotient_invariant (a : Γ) :
    A.act a ≫ A.quotient_projection J = A.quotient_projection J := by
  rw [quotient_projection, ← Category.assoc, A.orbit_projection_invariant]

instance quotient_locally_surjective : Presheaf.IsLocallySurjective J (A.quotient_projection J) := by
  letI := large_local_surjective_toSheafify.{u,v,w} J A.orbit_presheaf
  letI := Presheaf.isLocallySurjective_of_surjective J A.orbit_projection
    A.orbit_projection_surjective
  exact inferInstanceAs (Presheaf.IsLocallySurjective J
    (A.orbit_projection ≫ J.toSheafify A.orbit_presheaf))

/-- Equality after sheafification is exactly equality of orbit records on a covering sieve. -/
theorem quotient_eq_iff (U : Cᵒᵖ) (x y : H.obj U) :
    (A.quotient_projection J).app U x = (A.quotient_projection J).app U y ↔
      Presheaf.equalizerSieve (F := A.orbit_presheaf)
        (A.orbit_projection.app U x) (A.orbit_projection.app U y)
        ∈ J U.unop := by
  letI := large_local_injective_toSheafify.{u,v,w} J A.orbit_presheaf
  constructor
  · exact Presheaf.equalizerSieve_mem J (J.toSheafify A.orbit_presheaf) _ _
  · intro h
    apply (((isSheaf_iff_isSheaf_of_type J _).mp (A.quotient_sheaf J).property).isSeparated _ h).ext
    intro V f hf
    have hx := ConcreteCategory.congr_hom ((J.toSheafify A.orbit_presheaf).naturality f.op)
      (A.orbit_projection.app U x)
    have hy := ConcreteCategory.congr_hom ((J.toSheafify A.orbit_presheaf).naturality f.op)
      (A.orbit_projection.app U y)
    exact hx.symm.trans ((congrArg ((J.toSheafify A.orbit_presheaf).app (op V)) hf).trans hy)

def local_orbit_sieve {U : Cᵒᵖ} (x y : H.obj U) : Sieve U.unop where
  arrows V f := ∃ a : Γ, (A.act a).app (op V) (H.map f.op x) = H.map f.op y
  downward_closed := by
    rintro V W f ⟨a,ha⟩ g
    refine ⟨a, ?_⟩
    simp only [op_comp, H.map_comp, types_comp_apply]
    rw [← A.restrict_act g.op a, ha]

theorem local_orbit_sieve_eq {U : Cᵒᵖ} (x y : H.obj U) :
    A.local_orbit_sieve x y = Presheaf.equalizerSieve (F := A.orbit_presheaf)
      (A.orbit_projection.app U x) (A.orbit_projection.app U y) := by
  ext V f
  exact (A.orbit_projection_eq _ _ _).symm

theorem quotient_eq_iff_local_orbit (U : Cᵒᵖ) (x y : H.obj U) :
    (A.quotient_projection J).app U x = (A.quotient_projection J).app U y ↔
      A.local_orbit_sieve x y ∈ J U.unop := by
  rw [A.local_orbit_sieve_eq]
  exact A.quotient_eq_iff J U x y

theorem quotient_hom_ext (Y : Sheaf J (Type (max u v w)))
    (f h : (A.quotient_sheaf J).obj ⟶ Y.obj)
    (he : A.quotient_projection J ≫ f = A.quotient_projection J ≫ h) : f = h := by
  apply J.sheafify_hom_ext _ _ Y.property
  apply A.orbit_hom_ext
  simpa only [quotient_projection, Category.assoc] using he

def quotient_lift (Y : Sheaf J (Type (max u v w))) (b : H ⟶ Y.obj) (hb : A.Invariant b) :
    A.quotient_sheaf J ⟶ Y :=
  ⟨J.sheafifyLift (A.orbit_lift b hb) Y.property⟩

@[simp] theorem quotient_lift_fac (Y : Sheaf J (Type (max u v w))) (b : H ⟶ Y.obj)
    (hb : A.Invariant b) : A.quotient_projection J ≫ (A.quotient_lift J Y b hb).hom = b := by
  change (A.orbit_projection ≫ J.toSheafify A.orbit_presheaf) ≫
    J.sheafifyLift (A.orbit_lift b hb) Y.property = b
  rw [Category.assoc, GrothendieckTopology.toSheafify_sheafifyLift]
  exact A.orbit_lift_fac b hb

/-- The invariant quotient universal property, with its concrete composition map. -/
def quotient_universal (Y : Sheaf J (Type (max u v w))) :
    (A.quotient_sheaf J ⟶ Y) ≃ {b : H ⟶ Y.obj // A.Invariant b} where
  toFun f := ⟨A.quotient_projection J ≫ f.hom, fun a => by
    rw [← Category.assoc, A.quotient_invariant]⟩
  invFun b := A.quotient_lift J Y b.val b.property
  left_inv f := by
    apply Sheaf.hom_ext
    apply A.quotient_hom_ext J Y
    exact A.quotient_lift_fac J Y _ _
  right_inv b := Subtype.ext (A.quotient_lift_fac J Y _ _)

theorem quotient_universal_natural {Y Z : Sheaf J (Type (max u v w))}
    (f : A.quotient_sheaf J ⟶ Y) (g : Y ⟶ Z) :
    (A.quotient_universal J Z (f ≫ g)).val =
      (A.quotient_universal J Y f).val ≫ g.hom := by
  exact Category.assoc _ _ _

end PAction
end MathGauge.Descent
