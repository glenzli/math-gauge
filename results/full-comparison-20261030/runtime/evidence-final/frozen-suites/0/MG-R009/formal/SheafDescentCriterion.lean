import SheafFibreProducts

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]
variable {H : Sheaf J (Type (max u v w))} (A : PAction (Γ := Γ) H.obj)

def quotient_hom : H ⟶ A.quotient_sheaf J := ⟨A.quotient_projection J⟩

structure EquivariantOver where
  sheaf : Sheaf J (Type (max u v w))
  projection : sheaf ⟶ H
  action : PAction (Γ := Γ) sheaf.obj
  equivariant : ∀ a : Γ, action.act a ≫ projection.hom = projection.hom ≫ A.act a

namespace EquivariantOver
variable {A} (E : EquivariantOver A)

def StabilizerTrivial : Prop :=
  ∀ (U : Cᵒᵖ) (e : E.sheaf.obj.obj U) (a : Γ),
    (A.act a).app U (E.projection.hom.app U e) = E.projection.hom.app U e →
      (E.action.act a).app U e = e

theorem equivariant_apply (a : Γ) (U : Cᵒᵖ) (e : E.sheaf.obj.obj U) :
    E.projection.hom.app U ((E.action.act a).app U e) =
      (A.act a).app U (E.projection.hom.app U e) :=
  congrArg (fun η => η.app U e) (E.equivariant a)

def quotient_to_base : E.action.quotient_sheaf J ⟶ A.quotient_sheaf J :=
  E.action.quotient_lift J _ (E.projection.hom ≫ A.quotient_projection J) (fun a => by
    rw [← Category.assoc, E.equivariant, Category.assoc, A.quotient_invariant])

theorem quotient_to_base_fac :
    E.action.quotient_projection J ≫ E.quotient_to_base.hom =
      E.projection.hom ≫ A.quotient_projection J :=
  E.action.quotient_lift_fac J _ _ _

def comparison : E.sheaf ⟶ fibre_sheaf (quotient_hom A) E.quotient_to_base :=
  fibre_lift_hom _ _ E.projection (quotient_hom E.action) (by
    apply Sheaf.hom_ext
    exact E.quotient_to_base_fac.symm)

@[simp] theorem comparison_apply (U : Cᵒᵖ) (e : E.sheaf.obj.obj U) :
    (E.comparison.hom.app U e).val =
      (E.projection.hom.app U e,E.action.quotient_projection J |>.app U e) := rfl

theorem comparison_injective (hE : E.StabilizerTrivial) (U : Cᵒᵖ) :
    Function.Injective (E.comparison.hom.app U) := by
  intro e e' he
  have hp : E.projection.hom.app U e = E.projection.hom.app U e' :=
    congrArg (fun x => x.val.1) he
  have hq : (E.action.quotient_projection J).app U e =
      (E.action.quotient_projection J).app U e' := congrArg (fun x => x.val.2) he
  have hcov := (E.action.quotient_eq_iff_local_orbit J U e e').mp hq
  apply (((isSheaf_iff_isSheaf_of_type J _).mp E.sheaf.property).isSeparated _ hcov).ext
  intro V f hf
  obtain ⟨a,ha⟩ := hf
  have hbase : (A.act a).app (op V) (E.projection.hom.app (op V) (E.sheaf.obj.map f.op e)) =
      E.projection.hom.app (op V) (E.sheaf.obj.map f.op e) := by
    rw [← E.equivariant_apply, ha, ← nat_restrict E.projection.hom,
      ← nat_restrict E.projection.hom, hp]
  exact (hE (op V) (E.sheaf.obj.map f.op e) a hbase).symm.trans ha

/-- The canonical comparison is always locally onto; no stabilizer hypothesis is used. -/
instance comparison_locally_surjective : Sheaf.IsLocallySurjective E.comparison where
  imageSieve_mem {U} z := by
    let S := Presheaf.imageSieve (E.action.quotient_projection J) z.val.2
    have hS : S ∈ J U := Presheaf.imageSieve_mem J (E.action.quotient_projection J) z.val.2
    apply J.transitive hS
    intro V f hf
    obtain ⟨e,he⟩ := hf
    change (E.action.quotient_projection J).app (op V) e =
      (E.action.quotient_sheaf J).obj.map f.op z.val.2 at he
    have hb : (A.quotient_projection J).app (op V) (E.projection.hom.app (op V) e) =
        (A.quotient_projection J).app (op V) (H.obj.map f.op z.val.1) := by
      have hfac := congrArg (fun η => η.app (op V) e) E.quotient_to_base_fac
      change E.quotient_to_base.hom.app (op V)
        ((E.action.quotient_projection J).app (op V) e) =
          (A.quotient_projection J).app (op V) (E.projection.hom.app (op V) e) at hfac
      rw [← hfac, he, ← nat_restrict E.quotient_to_base.hom,
        ← nat_restrict (A.quotient_projection J)]
      exact congrArg ((A.quotient_sheaf J).obj.map f.op) z.property.symm
    have hR := (A.quotient_eq_iff_local_orbit J (op V)
      (E.projection.hom.app (op V) e) (H.obj.map f.op z.val.1)).mp hb
    refine J.superset_covering (S := A.local_orbit_sieve
      (E.projection.hom.app (op V) e) (H.obj.map f.op z.val.1)) ?_ hR
    intro W g hg
    obtain ⟨a,ha⟩ := hg
    refine ⟨(E.action.act a).app (op W) (E.sheaf.obj.map g.op e), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change E.projection.hom.app (op W) ((E.action.act a).app (op W)
        (E.sheaf.obj.map g.op e)) = H.obj.map (g ≫ f).op z.val.1
      rw [E.equivariant_apply, ← nat_restrict E.projection.hom, ha]
      simp only [op_comp, H.obj.map_comp, types_comp_apply]
    · change (E.action.quotient_projection J).app (op W)
        ((E.action.act a).app (op W) (E.sheaf.obj.map g.op e)) =
          (E.action.quotient_sheaf J).obj.map (g ≫ f).op z.val.2
      have hinv := congrArg (fun η => η.app (op W) (E.sheaf.obj.map g.op e))
        (E.action.quotient_invariant J a)
      change (E.action.quotient_projection J).app (op W)
        ((E.action.act a).app (op W) (E.sheaf.obj.map g.op e)) =
          (E.action.quotient_projection J).app (op W) (E.sheaf.obj.map g.op e) at hinv
      rw [hinv, ← nat_restrict (E.action.quotient_projection J), he]
      simp only [op_comp, Functor.map_comp, types_comp_apply]

theorem comparison_isIso (hE : E.StabilizerTrivial) : IsIso E.comparison := by
  apply (Sheaf.isLocallyBijective_iff_isIso E.comparison).mp
  constructor
  · exact Presheaf.isLocallyInjective_of_injective J E.comparison.hom (E.comparison_injective hE)
  · infer_instance

def comparison_iso (hE : E.StabilizerTrivial) :
    E.sheaf ≅ fibre_sheaf (quotient_hom A) E.quotient_to_base := by
  letI := E.comparison_isIso hE
  exact asIso E.comparison

end EquivariantOver

variable (D : Sheaf J (Type (max u v w))) (p : D ⟶ A.quotient_sheaf J)

def pullback_action : PAction (Γ := Γ) (fibre_sheaf (quotient_hom A) p).obj where
  act a := {
    app U x := ⟨((A.act a).app U x.val.1,x.val.2), by
      have hi := congrArg (fun η => η.app U x.val.1) (A.quotient_invariant J a)
      exact hi.trans x.property⟩
    naturality := by
      intro U V f
      funext x
      apply Subtype.ext
      exact Prod.ext (A.restrict_act f a x.val.1).symm rfl }
  one := by ext U x; apply Subtype.ext; exact Prod.ext (A.one_apply U x.val.1) rfl
  mul a b := by ext U x; apply Subtype.ext; exact Prod.ext (A.mul_apply a b U x.val.1) rfl

def pullback_equivariant : EquivariantOver A where
  sheaf := fibre_sheaf (quotient_hom A) p
  projection := fibre_fst_hom _ _
  action := pullback_action A D p
  equivariant a := rfl

theorem pullback_stabilizer_trivial : (pullback_equivariant A D p).StabilizerTrivial := by
  intro U e a ha
  apply Subtype.ext
  exact Prod.ext ha rfl

namespace EquivariantOver
variable {A D p} (E : EquivariantOver A)

theorem comparison_equivariant (a : Γ) :
    E.action.act a ≫ E.comparison.hom = E.comparison.hom ≫
      (pullback_action A _ E.quotient_to_base).act a := by
  ext U e
  apply Subtype.ext
  refine Prod.ext (E.equivariant_apply a U e) ?_
  exact congrArg (fun η => η.app U e) (E.action.quotient_invariant J a)

def Realizable : Prop :=
  ∃ (D : Sheaf J (Type (max u v w))) (p : D ⟶ A.quotient_sheaf J)
    (i : E.sheaf ≅ (pullback_equivariant A D p).sheaf),
    i.hom ≫ (pullback_equivariant A D p).projection = E.projection ∧
    ∀ a : Γ, E.action.act a ≫ i.hom.hom = i.hom.hom ≫ (pullback_action A D p).act a

/-- The full testwise stabilizer condition is necessary and sufficient. -/
theorem realizable_iff_stabilizer_trivial : E.Realizable ↔ E.StabilizerTrivial := by
  constructor
  · rintro ⟨D,p,i,hp,hi⟩ U e a ha
    have hinj : Function.Injective (i.hom.hom.app U) := by
      intro x y hxy
      have heq := congrArg (fun z => i.inv.hom.app U z) hxy
      have hiid := congrArg (fun η : E.sheaf ⟶ E.sheaf => η.hom.app U) i.hom_inv_id
      exact (congrFun hiid x).symm.trans (heq.trans (congrFun hiid y))
    apply hinj
    have hφ := congrArg (fun η => η.app U e) (hi a)
    change i.hom.hom.app U ((E.action.act a).app U e) =
      ((pullback_action A D p).act a).app U (i.hom.hom.app U e) at hφ
    rw [hφ]
    apply pullback_stabilizer_trivial A D p U (i.hom.hom.app U e) a
    have hp' := congrArg (fun η : E.sheaf ⟶ H => η.hom.app U e) hp
    change (i.hom.hom.app U e).val.1 = E.projection.hom.app U e at hp'
    change (A.act a).app U (i.hom.hom.app U e).val.1 = (i.hom.hom.app U e).val.1
    rw [hp']
    exact ha
  · intro hE
    refine ⟨E.action.quotient_sheaf J,E.quotient_to_base,E.comparison_iso hE,rfl,?_⟩
    exact E.comparison_equivariant

end EquivariantOver
end MathGauge.Descent
