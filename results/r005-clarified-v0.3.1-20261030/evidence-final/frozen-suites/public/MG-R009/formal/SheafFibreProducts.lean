import SheafOrbitQuotient

noncomputable section
open CategoryTheory Opposite
universe u v w
namespace MathGauge.Descent

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

theorem nat_restrict {F G : Cᵒᵖ ⥤ Type (max u v w)} (η : F ⟶ G)
    {U V : Cᵒᵖ} (a : U ⟶ V) (x : F.obj U) :
    G.map a (η.app U x) = η.app V (F.map a x) :=
  (ConcreteCategory.congr_hom (η.naturality a) x).symm

abbrev fibre_presheaf {H D Q : Cᵒᵖ ⥤ Type (max u v w)} (q : H ⟶ Q) (p : D ⟶ Q) :
    Cᵒᵖ ⥤ Type (max u v w) where
  obj U := {x : H.obj U × D.obj U // q.app U x.1 = p.app U x.2}
  map f x := ⟨(H.map f x.val.1,D.map f x.val.2), by
    rw [← nat_restrict q, ← nat_restrict p, x.property]⟩
  map_id U := by funext x; apply Subtype.ext; simp
  map_comp f g := by funext x; apply Subtype.ext; simp

def fibre_fst {H D Q : Cᵒᵖ ⥤ Type (max u v w)} (q : H ⟶ Q) (p : D ⟶ Q) :
    fibre_presheaf q p ⟶ H where
  app U x := x.val.1
  naturality := by intros; rfl

def fibre_snd {H D Q : Cᵒᵖ ⥤ Type (max u v w)} (q : H ⟶ Q) (p : D ⟶ Q) :
    fibre_presheaf q p ⟶ D where
  app U x := x.val.2
  naturality := by intros; rfl

theorem fibre_condition {H D Q : Cᵒᵖ ⥤ Type (max u v w)} (q : H ⟶ Q) (p : D ⟶ Q) :
    fibre_fst q p ≫ q = fibre_snd q p ≫ p := by
  ext U x
  exact x.property

def fibre_lift {E H D Q : Cᵒᵖ ⥤ Type (max u v w)} (q : H ⟶ Q) (p : D ⟶ Q)
    (f : E ⟶ H) (g : E ⟶ D) (h : f ≫ q = g ≫ p) : E ⟶ fibre_presheaf q p where
  app U x := ⟨(f.app U x,g.app U x),congrArg (fun η : E ⟶ Q => η.app U x) h⟩
  naturality := by
    intro U V a
    funext x
    apply Subtype.ext
    exact Prod.ext (nat_restrict f a x).symm (nat_restrict g a x).symm

theorem fibre_isSheaf {H D Q : Sheaf J (Type (max u v w))} (q : H ⟶ Q) (p : D ⟶ Q) :
    Presheaf.IsSheaf J (fibre_presheaf q.hom p.hom) := by
  apply (isSheaf_iff_isSheaf_of_type J _).mpr
  intro U S hS x hx
  let HH := ((isSheaf_iff_isSheaf_of_type J H.obj).mp H.property) S hS
  let HD := ((isSheaf_iff_isSheaf_of_type J D.obj).mp D.property) S hS
  let HQ := ((isSheaf_iff_isSheaf_of_type J Q.obj).mp Q.property) S hS
  let xH := x.map (fibre_fst q.hom p.hom)
  let xD := x.map (fibre_snd q.hom p.hom)
  have hxH := hx.map (fibre_fst q.hom p.hom)
  have hxD := hx.map (fibre_snd q.hom p.hom)
  let a := HH.amalgamate xH hxH
  let b := HD.amalgamate xD hxD
  have hab : q.hom.app (op U) a = p.hom.app (op U) b := by
    apply HQ.isSeparatedFor.ext
    intro V f hf
    rw [nat_restrict q.hom, nat_restrict p.hom, HH.valid_glue hxH, HD.valid_glue hxD]
    exact (x f hf).property
  refine ⟨⟨(a,b),hab⟩, ?_, ?_⟩
  · intro V f hf
    apply Subtype.ext
    exact Prod.ext (HH.valid_glue hxH f hf) (HD.valid_glue hxD f hf)
  · intro y hy
    apply Subtype.ext
    apply Prod.ext
    · apply HH.isSeparatedFor.ext
      intro V f hf
      exact (congrArg (fun z => z.val.1) (hy f hf)).trans (HH.valid_glue hxH f hf).symm
    · apply HD.isSeparatedFor.ext
      intro V f hf
      exact (congrArg (fun z => z.val.2) (hy f hf)).trans (HD.valid_glue hxD f hf).symm

/-- The actual sectionwise fibre product is a sheaf, including the empty cover. -/
def fibre_sheaf {H D Q : Sheaf J (Type (max u v w))} (q : H ⟶ Q) (p : D ⟶ Q) :
    Sheaf J (Type (max u v w)) := ⟨fibre_presheaf q.hom p.hom,fibre_isSheaf q p⟩

def fibre_fst_hom {H D Q : Sheaf J (Type (max u v w))} (q : H ⟶ Q) (p : D ⟶ Q) :
    fibre_sheaf q p ⟶ H := ⟨fibre_fst q.hom p.hom⟩

def fibre_snd_hom {H D Q : Sheaf J (Type (max u v w))} (q : H ⟶ Q) (p : D ⟶ Q) :
    fibre_sheaf q p ⟶ D := ⟨fibre_snd q.hom p.hom⟩

def fibre_lift_hom {E H D Q : Sheaf J (Type (max u v w))} (q : H ⟶ Q) (p : D ⟶ Q)
    (f : E ⟶ H) (g : E ⟶ D) (h : f ≫ q = g ≫ p) : E ⟶ fibre_sheaf q p :=
  ⟨fibre_lift q.hom p.hom f.hom g.hom (congrArg (fun η => η.hom) h)⟩

/-- An explicit, unique lifting property verifies this is the categorical fibre product. -/
theorem fibre_universal {E H D Q : Sheaf J (Type (max u v w))} (q : H ⟶ Q) (p : D ⟶ Q)
    (f : E ⟶ H) (g : E ⟶ D) (h : f ≫ q = g ≫ p) :
    ∃! k : E ⟶ fibre_sheaf q p,
      k ≫ fibre_fst_hom q p = f ∧ k ≫ fibre_snd_hom q p = g := by
  refine ⟨fibre_lift_hom q p f g h, ⟨rfl,rfl⟩, ?_⟩
  intro k hk
  apply Sheaf.hom_ext
  ext U x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun η : E ⟶ H => η.hom.app U x) hk.1)
    (congrArg (fun η : E ⟶ D => η.hom.app U x) hk.2)

end MathGauge.Descent
