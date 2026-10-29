import SheafDescentEquivalence

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]

def invariant_fibre_action {M N : Sheaf J (Type (max u v w))}
    (A : PAction (Γ := Γ) M.obj) (r : M ⟶ N) (hr : A.Invariant r.hom)
    (D : Sheaf J (Type (max u v w))) (p : D ⟶ N) :
    PAction (Γ := Γ) (fibre_sheaf r p).obj where
  act a := {
    app U x := ⟨((A.act a).app U x.val.1,x.val.2),
      (congrArg (fun η => η.app U x.val.1) (hr a)).trans x.property⟩
    naturality := by
      intro U V f
      funext x
      apply Subtype.ext
      exact Prod.ext (A.restrict_act f a x.val.1).symm rfl }
  one := by ext U x; apply Subtype.ext; exact Prod.ext (A.one_apply U x.val.1) rfl
  mul a b := by ext U x; apply Subtype.ext; exact Prod.ext (A.mul_apply a b U x.val.1) rfl

def invariant_fibre_record {M N : Sheaf J (Type (max u v w))}
    (A : PAction (Γ := Γ) M.obj) (r : M ⟶ N) (hr : A.Invariant r.hom)
    (D : Sheaf J (Type (max u v w))) (p : D ⟶ N) : EquivariantOver A where
  sheaf := fibre_sheaf r p
  projection := fibre_fst_hom r p
  action := invariant_fibre_action A r hr D p
  equivariant _ := rfl

variable {H : Sheaf J (Type (max u v w))} (A : PAction (Γ := Γ) H.obj)
variable (B D : Sheaf J (Type (max u v w)))
variable (b : B ⟶ A.quotient_sheaf J) (p : D ⟶ A.quotient_sheaf J)

/-- The classification over an arbitrary sheaf base B, via its actual quotient isomorphism. -/
def basechange_equivalence : Over B ≌ StableEquivariant (pullback_action A B b) :=
  (Over.mapIso (pullback_quotient_iso A B b).symm).trans
    (descent_equivalence (pullback_action A B b))

def basechange_record (E : EquivariantOver A) :
    EquivariantOver (pullback_action A B b) where
  sheaf := fibre_sheaf (E.projection ≫ quotient_hom A) b
  projection := ⟨{
    app U x := ⟨(E.projection.hom.app U x.val.1,x.val.2),x.property⟩
    naturality := by
      intro U V f
      funext x
      apply Subtype.ext
      exact Prod.ext (nat_restrict E.projection.hom f x.val.1).symm rfl }⟩
  action := invariant_fibre_action E.action (E.projection ≫ quotient_hom A)
    (fun a => by
      change E.action.act a ≫ (E.projection.hom ≫ A.quotient_projection J) = _
      rw [← Category.assoc,E.equivariant,Category.assoc,A.quotient_invariant]
      rfl) B b
  equivariant a := by
    ext U x
    apply Subtype.ext
    exact Prod.ext (E.equivariant_apply a U x.val.1) rfl

theorem basechange_stabilizer_trivial (E : EquivariantOver A) (hE : E.StabilizerTrivial) :
    (basechange_record A B b E).StabilizerTrivial := by
  intro U x a ha
  apply Subtype.ext
  refine Prod.ext (hE U x.val.1 a ?_) rfl
  exact congrArg (fun z => z.val.1) ha

/-- Coordinate rearrangement for base change of an actual realization. -/
def basechange_fibre_iso :
    fibre_sheaf (fibre_fst_hom (quotient_hom A) p ≫ quotient_hom A) b ≅
      fibre_sheaf (fibre_snd_hom (quotient_hom A) b) (fibre_snd_hom p b) where
  hom := ⟨{
    app U x := ⟨(⟨(x.val.1.val.1,x.val.2),x.property⟩,
      ⟨(x.val.1.val.2,x.val.2),x.val.1.property.symm.trans x.property⟩),rfl⟩
    naturality := by intro U V f; rfl }⟩
  inv := ⟨{
    app U x := ⟨(⟨(x.val.1.val.1,x.val.2.val.1),
      x.val.1.property.trans ((congrArg (b.hom.app U) x.property).trans x.val.2.property.symm)⟩,
        x.val.1.val.2),x.val.1.property⟩
    naturality := by intro U V f; rfl }⟩
  hom_inv_id := by apply Sheaf.hom_ext; ext U x; rfl
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext U x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Prod.ext rfl x.property

@[simp] theorem basechange_fibre_iso_fst (U : Cᵒᵖ)
    (x : (fibre_sheaf (fibre_fst_hom (quotient_hom A) p ≫ quotient_hom A) b).obj.obj U) :
    ((basechange_fibre_iso A B D b p).hom.hom.app U x).val.1.val =
      (x.val.1.val.1,x.val.2) := rfl

@[simp] theorem basechange_fibre_iso_snd (U : Cᵒᵖ)
    (x : (fibre_sheaf (fibre_fst_hom (quotient_hom A) p ≫ quotient_hom A) b).obj.obj U) :
    ((basechange_fibre_iso A B D b p).hom.hom.app U x).val.2.val =
      (x.val.1.val.2,x.val.2) := rfl

/-- The coordinate rearrangement preserves the base projection and every group action. -/
def basechange_realization_iso :
    basechange_record A B b (pullback_equivariant A D p) ≅
      invariant_fibre_record (pullback_action A B b) (fibre_snd_hom (quotient_hom A) b)
        (pullback_snd_invariant A B b) (fibre_sheaf p b) (fibre_snd_hom p b) :=
  EquivariantOver.isoMk (basechange_fibre_iso A B D b p) rfl (fun _ => rfl)

variable {A B D b p}

def fibre_map {M N R M' N' R' : Sheaf J (Type (max u v w))}
    {q : M ⟶ R} {p : N ⟶ R} {q' : M' ⟶ R'} {p' : N' ⟶ R'}
    (f : M ⟶ M') (g : N ⟶ N') (k : R ⟶ R')
    (hf : f ≫ q' = q ≫ k) (hg : g ≫ p' = p ≫ k) :
    fibre_sheaf q p ⟶ fibre_sheaf q' p' := ⟨{
  app U x := ⟨(f.hom.app U x.val.1,g.hom.app U x.val.2),by
    have h1 := congrArg (fun η => η.hom.app U x.val.1) hf
    have h2 := congrArg (fun η => η.hom.app U x.val.2) hg
    exact h1.trans ((congrArg (k.hom.app U) x.property).trans h2.symm)⟩
  naturality := by
    intro U V a
    funext x
    apply Subtype.ext
    exact Prod.ext (nat_restrict f.hom a x.val.1).symm
      (nat_restrict g.hom a x.val.2).symm }⟩

theorem fibre_map_id {M N R : Sheaf J (Type (max u v w))} (q : M ⟶ R) (p : N ⟶ R) :
    fibre_map (q := q) (p := p) (q' := q) (p' := p) (𝟙 M) (𝟙 N) (𝟙 R)
      (by exact (Category.id_comp q).trans (Category.comp_id q).symm)
      (by exact (Category.id_comp p).trans (Category.comp_id p).symm) = 𝟙 _ := rfl

theorem basechange_fibre_natural {B' D' : Sheaf J (Type (max u v w))}
    {b' : B' ⟶ A.quotient_sheaf J} {p' : D' ⟶ A.quotient_sheaf J}
    (f : D ⟶ D') (g : B ⟶ B') (hf : f ≫ p' = p) (hg : g ≫ b' = b) :
    let m := fibre_map (q := quotient_hom A) (p := p) (q' := quotient_hom A) (p' := p')
      (𝟙 H) f (𝟙 _) (by simp) (by simpa using hf)
    let n := fibre_map (q := quotient_hom A) (p := b) (q' := quotient_hom A) (p' := b')
      (𝟙 H) g (𝟙 _) (by simp) (by simpa using hg)
    let d := fibre_map (q := p) (p := b) (q' := p') (p' := b')
      f g (𝟙 _) (by simpa using hf) (by simpa using hg)
    fibre_map m g (𝟙 _) (by apply Sheaf.hom_ext; ext U x; rfl) (by simpa using hg) ≫
      (basechange_fibre_iso A B' D' b' p').hom =
    (basechange_fibre_iso A B D b p).hom ≫
      fibre_map n d g (by rfl) (by rfl) := by
  rfl

end MathGauge.Descent
