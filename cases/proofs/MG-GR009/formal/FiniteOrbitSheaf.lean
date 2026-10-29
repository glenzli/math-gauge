import FiniteOrbitSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite TopologicalSpace
universe u g w
namespace MathGauge.Descent.FiniteOrbit
variable {Γ : Type g} [Group Γ] [Finite Γ]
variable (T : Profinite.{u}) [MulAction Γ T] [ContinuousConstSMul Γ T]

def liftingSet (U : Profinite.{u}) (f : C(U,orbitSpace (Γ := Γ) T)) : Set (U×T) :=
  {x | quotientMap T x.2=f x.1}

instance liftingCompact (U : Profinite.{u}) (f : C(U,orbitSpace (Γ := Γ) T)) :
    CompactSpace (liftingSet T U f) := isCompact_iff_compactSpace.mp
  ((isClosed_eq ((quotientMap T).continuous.comp continuous_snd)
    (f.continuous.comp continuous_fst)).isCompact)

def liftingSpace (U : Profinite.{u}) (f : C(U,orbitSpace (Γ := Γ) T)) : Profinite.{u} :=
  Profinite.of (liftingSet T U f)

def liftingProjection (U : Profinite.{u}) (f : C(U,orbitSpace (Γ := Γ) T)) :
    liftingSpace T U f ⟶ U :=
  CompHausLike.ofHom _ ⟨fun x => x.val.1,continuous_fst.comp continuous_subtype_val⟩

theorem liftingProjection_surjective (U : Profinite.{u}) (f : C(U,orbitSpace (Γ := Γ) T)) :
    Function.Surjective (liftingProjection T U f) := by
  intro x
  obtain ⟨t,ht⟩ := quotientMap_surjective (Γ := Γ) T (f x)
  exact ⟨⟨(x,t),ht⟩,rfl⟩

instance quotientProbe_locally_surjective :
    Presheaf.IsLocallySurjective ProfSite (quotientProbe.{u,g,w} (Γ := Γ) T).hom where
  imageSieve_mem {U} f := by
    rw [prof_cover_iff]
    refine ⟨PUnit,inferInstance,fun _ => liftingSpace T U f.down,
      fun _ => liftingProjection T U f.down,?_,?_⟩
    · intro x
      obtain ⟨y,hy⟩ := liftingProjection_surjective T U f.down x
      exact ⟨PUnit.unit,y,hy⟩
    · intro _
      refine ⟨⟨⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩⟩,?_⟩
      apply ULift.ext
      ext x
      exact x.property

def relationSet (U : Profinite.{u}) (f h : C(U,T)) (a : Γ) : Set U :=
  {x | a • f x=h x}

instance relationCompact (U : Profinite.{u}) (f h : C(U,T)) (a : Γ) :
    CompactSpace (relationSet T U f h a) := isCompact_iff_compactSpace.mp
  ((isClosed_eq ((continuous_const_smul a).comp f.continuous) h.continuous).isCompact)

def relationPiece (U : Profinite.{u}) (f h : C(U,T)) (a : Γ) : Profinite.{u} :=
  Profinite.of (relationSet T U f h a)

def relationInclusion (U : Profinite.{u}) (f h : C(U,T)) (a : Γ) :
    relationPiece T U f h a ⟶ U := CompHausLike.ofHom _ ⟨Subtype.val,continuous_subtype_val⟩

/-- Finitely many actual closed graph pieces cover every pair of sections with
the same orbit image. Labels may differ between the covering pieces. -/
theorem quotientProbe_kernel (U : Profinite.{u}ᵒᵖ)
    (f h : (prof_probe_sheaf.{u,w} T).obj.obj U)
    (he : (quotientProbe (Γ := Γ) T).hom.app U f=(quotientProbe T).hom.app U h) :
    (action (Γ := Γ) T).local_orbit_sieve f h ∈ ProfSite U.unop := by
  letI : Fintype Γ := Fintype.ofFinite Γ
  let e := Fintype.equivFin Γ
  rw [prof_cover_iff]
  refine ⟨Fin (Fintype.card Γ),inferInstance,
    fun j => relationPiece T U.unop f.down h.down (e.symm j),
    fun j => relationInclusion T U.unop f.down h.down (e.symm j),?_,?_⟩
  · intro x
    have hx := congrArg (fun z => z.down x) he
    obtain ⟨a,ha⟩ := (quotientMap_eq_iff T (f.down x) (h.down x)).mp hx
    refine ⟨e a,⟨x,?_⟩,rfl⟩
    change e.symm (e a) • f.down x=h.down x
    rw [e.symm_apply_apply]
    exact ha
  · intro j
    refine ⟨e.symm j,?_⟩
    apply ULift.ext
    ext x
    exact x.property

def quotientToProbe : (action (Γ := Γ) T).quotient_sheaf ProfSite ⟶
    prof_probe_sheaf.{u,w} (orbitSpace (Γ := Γ) T) :=
  (action T).quotient_lift ProfSite _ (quotientProbe T).hom (quotientProbe_invariant T)

instance quotientToProbe_isIso : IsIso (quotientToProbe.{u,g,w} (Γ := Γ) T) :=
  (action T).quotient_lift_isIso _ _ (quotientProbe_invariant T)
    (quotientProbe_locally_surjective T) (quotientProbe_kernel T)

/-- The actual represented orbit space is the sheaf quotient, with its original
quotient map, including the empty space and empty covering family. -/
def quotientSheafIso : (action (Γ := Γ) T).quotient_sheaf ProfSite ≅
    prof_probe_sheaf.{u,w} (orbitSpace (Γ := Γ) T) := asIso (quotientToProbe T)

theorem quotientSheafIso_fac :
    (action (Γ := Γ) T).quotient_projection ProfSite ≫
      (quotientSheafIso.{u,g,w} T).hom.hom=(quotientProbe T).hom :=
  (action T).quotient_lift_fac ProfSite _ _ _

end MathGauge.Descent.FiniteOrbit
