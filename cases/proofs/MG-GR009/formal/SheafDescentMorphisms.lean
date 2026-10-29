import SheafQuotientRecovery

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]
variable {H : Sheaf J (Type (max u v w))} {A : PAction (Γ := Γ) H.obj}

namespace EquivariantOver

structure Hom (E F : EquivariantOver A) where
  map : E.sheaf ⟶ F.sheaf
  over : map ≫ F.projection = E.projection
  equivariant : ∀ a : Γ, E.action.act a ≫ map.hom = map.hom ≫ F.action.act a

@[ext] theorem Hom.ext {E F : EquivariantOver A} {f g : Hom E F} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def Hom.id (E : EquivariantOver A) : Hom E E := ⟨𝟙 _,by simp,by intro; simp⟩

def Hom.comp {E F G : EquivariantOver A} (f : Hom E F) (g : Hom F G) : Hom E G where
  map := f.map ≫ g.map
  over := by rw [Category.assoc,g.over,f.over]
  equivariant a := by
    change E.action.act a ≫ (f.map.hom ≫ g.map.hom) =
      (f.map.hom ≫ g.map.hom) ≫ G.action.act a
    rw [← Category.assoc,f.equivariant,Category.assoc,g.equivariant,Category.assoc]

def Hom.quotient_map {E F : EquivariantOver A} (f : Hom E F) :
    E.action.quotient_sheaf J ⟶ F.action.quotient_sheaf J :=
  E.action.quotient_lift J _ (f.map.hom ≫ F.action.quotient_projection J) (fun a => by
    rw [← Category.assoc,f.equivariant,Category.assoc,F.action.quotient_invariant])

@[simp] theorem Hom.quotient_map_fac {E F : EquivariantOver A} (f : Hom E F) :
    E.action.quotient_projection J ≫ f.quotient_map.hom =
      f.map.hom ≫ F.action.quotient_projection J := E.action.quotient_lift_fac J _ _ _

theorem Hom.quotient_map_over {E F : EquivariantOver A} (f : Hom E F) :
    f.quotient_map ≫ F.quotient_to_base = E.quotient_to_base := by
  apply Sheaf.hom_ext
  apply E.action.quotient_hom_ext J (A.quotient_sheaf J)
  change E.action.quotient_projection J ≫ (f.quotient_map.hom ≫ F.quotient_to_base.hom) = _
  rw [← Category.assoc,f.quotient_map_fac,Category.assoc,F.quotient_to_base_fac]
  rw [← Category.assoc]
  have ho : f.map.hom ≫ F.projection.hom = E.projection.hom :=
    congrArg (fun η => η.hom) f.over
  rw [ho]
  exact E.quotient_to_base_fac.symm

theorem Hom.quotient_map_id (E : EquivariantOver A) : (Hom.id E).quotient_map = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply E.action.quotient_hom_ext J (E.action.quotient_sheaf J)
  rw [Hom.quotient_map_fac]
  rfl

theorem Hom.quotient_map_comp {E F G : EquivariantOver A} (f : Hom E F) (g : Hom F G) :
    (f.comp g).quotient_map = f.quotient_map ≫ g.quotient_map := by
  apply Sheaf.hom_ext
  apply E.action.quotient_hom_ext J (G.action.quotient_sheaf J)
  rw [Hom.quotient_map_fac]
  change (f.map.hom ≫ g.map.hom) ≫ G.action.quotient_projection J =
    E.action.quotient_projection J ≫ (f.quotient_map.hom ≫ g.quotient_map.hom)
  calc
    (f.map.hom ≫ g.map.hom) ≫ G.action.quotient_projection J =
      f.map.hom ≫ (g.map.hom ≫ G.action.quotient_projection J) := Category.assoc _ _ _
    _ = f.map.hom ≫ (F.action.quotient_projection J ≫ g.quotient_map.hom) := by
      rw [g.quotient_map_fac]
    _ = (f.map.hom ≫ F.action.quotient_projection J) ≫ g.quotient_map.hom :=
      (Category.assoc _ _ _).symm
    _ = (E.action.quotient_projection J ≫ f.quotient_map.hom) ≫ g.quotient_map.hom := by
      rw [f.quotient_map_fac]
    _ = E.action.quotient_projection J ≫ (f.quotient_map.hom ≫ g.quotient_map.hom) :=
      Category.assoc _ _ _

end EquivariantOver

variable (A)
variable {D D' : Sheaf J (Type (max u v w))}
variable (p : D ⟶ A.quotient_sheaf J) (p' : D' ⟶ A.quotient_sheaf J)

/-- A morphism between realizations, with its required base compatibility. -/
abbrev SliceHom := {f : D ⟶ D' // f ≫ p' = p}

def pullback_hom (f : SliceHom A p p') :
    EquivariantOver.Hom (pullback_equivariant A D p) (pullback_equivariant A D' p') where
  map := ⟨{
    app U x := ⟨(x.val.1,f.val.hom.app U x.val.2), by
      have hf := congrArg (fun η : D ⟶ A.quotient_sheaf J => η.hom.app U x.val.2) f.property
      exact x.property.trans hf.symm⟩
    naturality := by
      intro U V a
      funext x
      apply Subtype.ext
      exact Prod.ext rfl (nat_restrict f.val.hom a x.val.2).symm }⟩
  over := rfl
  equivariant a := rfl

@[simp] theorem pullback_hom_id : pullback_hom A p p ⟨𝟙 D,by simp⟩ =
    EquivariantOver.Hom.id (pullback_equivariant A D p) := rfl

theorem pullback_hom_comp {D'' : Sheaf J (Type (max u v w))}
    (p'' : D'' ⟶ A.quotient_sheaf J) (f : SliceHom A p p') (g : SliceHom A p' p'') :
    pullback_hom A p p'' ⟨f.val ≫ g.val,by rw [Category.assoc,g.property,f.property]⟩ =
      (pullback_hom A p p' f).comp (pullback_hom A p' p'' g) := rfl

def descend_pullback_hom
    (f : EquivariantOver.Hom (pullback_equivariant A D p) (pullback_equivariant A D' p')) :
    D ⟶ D' :=
  (pullback_quotient_iso A D p).inv ≫
    (pullback_action A D p).quotient_lift J D'
      (f.map.hom ≫ fibre_snd (quotient_hom A).hom p'.hom) (fun a => by
        have he := f.equivariant a
        change (pullback_action A D p).act a ≫ f.map.hom =
          f.map.hom ≫ (pullback_action A D' p').act a at he
        ext U x
        exact congrArg (fun z => z.val.2) (congrArg (fun η => η.app U x) he))

theorem descend_pullback_fac
    (f : EquivariantOver.Hom (pullback_equivariant A D p) (pullback_equivariant A D' p')) :
    fibre_snd_hom (quotient_hom A) p ≫ descend_pullback_hom A p p' f =
      f.map ≫ fibre_snd_hom (quotient_hom A) p' := by
  apply Sheaf.hom_ext
  change fibre_snd (quotient_hom A).hom p.hom ≫ _ = _
  rw [← pullback_quotient_fac A D p]
  change ((pullback_action A D p).quotient_projection J ≫
    (pullback_quotient_iso A D p).hom.hom) ≫
    ((pullback_quotient_iso A D p).inv.hom ≫ _) = _
  rw [Category.assoc, ← Category.assoc (pullback_quotient_iso A D p).hom.hom]
  have hid : (pullback_quotient_iso A D p).hom.hom ≫
      (pullback_quotient_iso A D p).inv.hom = 𝟙 _ :=
    congrArg (fun η => η.hom) (pullback_quotient_iso A D p).hom_inv_id
  rw [hid,Category.id_comp]
  exact (pullback_action A D p).quotient_lift_fac J D' _ _

theorem descend_pullback_over
    (f : EquivariantOver.Hom (pullback_equivariant A D p) (pullback_equivariant A D' p')) :
    descend_pullback_hom A p p' f ≫ p' = p := by
  letI : Sheaf.IsLocallySurjective (fibre_snd_hom (quotient_hom A) p) :=
    pullback_snd_locally_surjective A D p
  apply (cancel_epi (fibre_snd_hom (quotient_hom A) p)).mp
  apply Sheaf.hom_ext
  ext U x
  have hf := congrArg (fun η => η.hom.app U x) (descend_pullback_fac A p p' f)
  have ho := congrArg (fun η => η.hom.app U x) f.over
  change (descend_pullback_hom A p p' f).hom.app U x.val.2 =
    (f.map.hom.app U x).val.2 at hf
  change (f.map.hom.app U x).val.1 = x.val.1 at ho
  change p'.hom.app U ((descend_pullback_hom A p p' f).hom.app U x.val.2) =
    p.hom.app U x.val.2
  rw [hf]
  exact (f.map.hom.app U x).property.symm.trans
    ((congrArg ((quotient_hom A).hom.app U) ho).trans x.property)

theorem pullback_descend
    (f : EquivariantOver.Hom (pullback_equivariant A D p) (pullback_equivariant A D' p')) :
    pullback_hom A p p' ⟨descend_pullback_hom A p p' f,descend_pullback_over A p p' f⟩ = f := by
  apply EquivariantOver.Hom.ext
  apply Sheaf.hom_ext
  ext U x
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun η => η.hom.app U x) f.over).symm
  · exact congrArg (fun η => η.hom.app U x) (descend_pullback_fac A p p' f)

theorem descend_pullback (f : SliceHom A p p') :
    descend_pullback_hom A p p' (pullback_hom A p p' f) = f.val := by
  letI : Sheaf.IsLocallySurjective (fibre_snd_hom (quotient_hom A) p) :=
    pullback_snd_locally_surjective A D p
  apply (cancel_epi (fibre_snd_hom (quotient_hom A) p)).mp
  rw [descend_pullback_fac]
  rfl

/-- Full faithfulness on all realization morphisms, with explicit inverse descent. -/
def realization_hom_equiv : SliceHom A p p' ≃
    EquivariantOver.Hom (pullback_equivariant A D p) (pullback_equivariant A D' p') where
  toFun := pullback_hom A p p'
  invFun f := ⟨descend_pullback_hom A p p' f,descend_pullback_over A p p' f⟩
  left_inv f := Subtype.ext (descend_pullback A p p' f)
  right_inv := pullback_descend A p p'

end MathGauge.Descent
