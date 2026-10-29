import SheafDescentMorphisms
import Mathlib.CategoryTheory.Comma.Over.Basic

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]
variable {H : Sheaf J (Type (max u v w))} (A : PAction (Γ := Γ) H.obj)

instance equivariantCategory : Category (EquivariantOver A) where
  Hom := EquivariantOver.Hom
  id := EquivariantOver.Hom.id
  comp := EquivariantOver.Hom.comp
  id_comp f := by apply EquivariantOver.Hom.ext; exact Category.id_comp f.map
  comp_id f := by apply EquivariantOver.Hom.ext; exact Category.comp_id f.map
  assoc f g h := by apply EquivariantOver.Hom.ext; exact Category.assoc f.map g.map h.map

namespace EquivariantOver
variable {A} {E F : EquivariantOver A}

def isoMk (i : E.sheaf ≅ F.sheaf)
    (ho : i.hom ≫ F.projection = E.projection)
    (he : ∀ a : Γ, E.action.act a ≫ i.hom.hom = i.hom.hom ≫ F.action.act a) : E ≅ F where
  hom := ⟨i.hom,ho,he⟩
  inv := ⟨i.inv,by rw [← ho,← Category.assoc,i.inv_hom_id,Category.id_comp],by
    intro a
    ext U y
    have h := congrArg (fun η => η.app U (i.inv.hom.app U y)) (he a)
    have hhi (x : E.sheaf.obj.obj U) : i.inv.hom.app U (i.hom.hom.app U x) = x :=
      congrArg (fun η : E.sheaf ⟶ E.sheaf => η.hom.app U x) i.hom_inv_id
    have hih (y : F.sheaf.obj.obj U) : i.hom.hom.app U (i.inv.hom.app U y) = y :=
      congrArg (fun η : F.sheaf ⟶ F.sheaf => η.hom.app U y) i.inv_hom_id
    change i.hom.hom.app U ((E.action.act a).app U (i.inv.hom.app U y)) =
      (F.action.act a).app U (i.hom.hom.app U (i.inv.hom.app U y)) at h
    have h' := congrArg (i.inv.hom.app U) h
    rw [hhi,hih] at h'
    exact h'.symm⟩
  hom_inv_id := Hom.ext i.hom_inv_id
  inv_hom_id := Hom.ext i.inv_hom_id

end EquivariantOver

abbrev StableEquivariant := ObjectProperty.FullSubcategory
  (fun E : EquivariantOver A => E.StabilizerTrivial)

def realizationFunctor : Over (A.quotient_sheaf J) ⥤ StableEquivariant A where
  obj d := ⟨pullback_equivariant A d.left d.hom,pullback_stabilizer_trivial A d.left d.hom⟩
  map f := ⟨pullback_hom A _ _ ⟨f.left,f.w⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def quotientFunctor : StableEquivariant A ⥤ Over (A.quotient_sheaf J) where
  obj e := Over.mk e.obj.quotient_to_base
  map f := Over.homMk f.hom.quotient_map f.hom.quotient_map_over
  map_id e := by
    apply Over.OverMorphism.ext
    exact EquivariantOver.Hom.quotient_map_id e.obj
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact EquivariantOver.Hom.quotient_map_comp f.hom g.hom

def equivariant_quotientFunctor : EquivariantOver A ⥤ Sheaf J (Type (max u v w)) where
  obj E := E.action.quotient_sheaf J
  map f := f.quotient_map
  map_id E := EquivariantOver.Hom.quotient_map_id E
  map_comp f g := EquivariantOver.Hom.quotient_map_comp f g

instance realizationFunctor_faithful : (realizationFunctor A).Faithful where
  map_injective {d e} f g h := by
    apply Over.OverMorphism.ext
    have hh : pullback_hom A d.hom e.hom ⟨f.left,f.w⟩ =
        pullback_hom A d.hom e.hom ⟨g.left,g.w⟩ := congrArg (fun k => k.hom) h
    exact congrArg Subtype.val ((realization_hom_equiv A d.hom e.hom).injective hh)

instance realizationFunctor_full : (realizationFunctor A).Full where
  map_surjective {d e} f := by
    refine ⟨Over.homMk (descend_pullback_hom A d.hom e.hom f.hom)
      (descend_pullback_over A d.hom e.hom f.hom),?_⟩
    apply ObjectProperty.hom_ext
    exact pullback_descend A d.hom e.hom f.hom

instance realizationFunctor_essSurj : (realizationFunctor A).EssSurj where
  mem_essImage e := by
    refine ⟨Over.mk e.obj.quotient_to_base,?_⟩
    exact ⟨(ObjectProperty.isoMk _
      (EquivariantOver.isoMk (e.obj.comparison_iso e.property) rfl
        e.obj.comparison_equivariant)).symm⟩

instance realizationFunctor_isEquivalence : (realizationFunctor A).IsEquivalence where

/-- The complete descent classification as an actual categorical equivalence. -/
def descent_equivalence : Over (A.quotient_sheaf J) ≌ StableEquivariant A :=
  (realizationFunctor A).asEquivalence

/-- Uniqueness concerns realizations equipped with their chosen identifications. -/
theorem realization_iso_unique (E : StableEquivariant A)
    (d d' : Over (A.quotient_sheaf J))
    (i : E ≅ (realizationFunctor A).obj d)
    (j : E ≅ (realizationFunctor A).obj d') :
    ∃! k : d ≅ d', i ≪≫ (realizationFunctor A).mapIso k = j := by
  let F := realizationFunctor A
  refine ⟨F.preimageIso (i.symm ≪≫ j),?_,?_⟩
  · apply Iso.ext
    change i.hom ≫ F.map (F.preimageIso (i.symm ≪≫ j)).hom = j.hom
    simp
  · intro k hk
    apply Iso.ext
    apply F.map_injective
    apply (cancel_epi i.hom).mp
    have h := congrArg Iso.hom hk
    change i.hom ≫ F.map k.hom = j.hom at h
    simpa using h

end MathGauge.Descent
