import MathGauge.GP003.ActualOpenComparison
import Mathlib.Topology.Sheaves.Functors

/-! Changing an ambient scheme along an actual open immersion preserves the
specified open-neighborhood colimit, naturally in both the presheaf and the
scheme over the ambient. The chart is not substituted for the original
presheaf: its restriction is explicitly the original functor on image opens. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open TopologicalSpace Opposite AlgebraicGeometry

universe u
variable {X Y T : Scheme.{u}} (f : T ⟶ Y) (j : Y ⟶ X) [IsOpenImmersion j]

def ambientRestriction (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    Y.carrier.Presheaf AddCommGrpCat.{u} := j.isOpenEmbedding.functor.op ⋙ F

def ambientRestrictionMap {F G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : F ⟶ G) :
    ambientRestriction j F ⟶ ambientRestriction j G :=
  whiskerLeft j.isOpenEmbedding.functor.op η

def ambientRestrictionSheaf (G : TopCat.Sheaf AddCommGrpCat.{u} X.carrier) :
    TopCat.Sheaf AddCommGrpCat.{u} Y.carrier :=
  ⟨ambientRestriction j G.obj, TopCat.Presheaf.isSheaf_of_isOpenEmbedding j.isOpenEmbedding G.property⟩

def ambientNeighborhoodImage : SchemeNeighborhoods f ⥤ SchemeNeighborhoods (f ≫ j) :=
  (show Monotone (fun U : SchemeNeighborhoods f =>
    (⟨j.isOpenEmbedding.functor.obj U.1, (factors_open_iff_range _ _).mpr (by
      rintro _ ⟨t,rfl⟩
      exact ⟨f t, (factors_open_iff_range f U.1).mp U.2 ⟨t,rfl⟩, rfl⟩)⟩ :
        SchemeNeighborhoods (f ≫ j))) from fun _ _ h => Set.image_mono h).functor

def ambientNeighborhoodPreimage : SchemeNeighborhoods (f ≫ j) ⥤ SchemeNeighborhoods f :=
  (show Monotone (fun V : SchemeNeighborhoods (f ≫ j) =>
    (⟨(Opens.map j.base).obj V.1, (factors_open_iff_range _ _).mpr (by
      rintro _ ⟨t,rfl⟩
      exact (factors_open_iff_range (f ≫ j) V.1).mp V.2 ⟨t,rfl⟩)⟩ :
        SchemeNeighborhoods f)) from fun _ _ h => fun _ hx => h hx).functor

def ambientNeighborhoodAdjunction :
    ambientNeighborhoodImage f j ⊣ ambientNeighborhoodPreimage f j :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun U => homOfLE (show U.1 ≤ _ from fun t ht => ⟨t,ht,rfl⟩)
          naturality := fun _ _ _ => Subsingleton.elim _ _ }
      counit :=
        { app := fun V => homOfLE (show _ ≤ V.1 from fun _ ⟨t,ht,he⟩ => he ▸ ht)
          naturality := fun _ _ _ => Subsingleton.elim _ _ }
      left_triangle := by ext; exact Subsingleton.elim _ _
      right_triangle := by ext; exact Subsingleton.elim _ _ }

instance ambientNeighborhoodImage_final : (ambientNeighborhoodImage f j).op.Final := by
  haveI : (ambientNeighborhoodImage f j).Initial :=
    Functor.initial_of_adjunction (ambientNeighborhoodAdjunction f j)
  infer_instance

/-- Canonical comparison, defined on each section by the same section on the
actual image open in the original ambient scheme. -/
def ambientNeighborhoodIso (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue f (ambientRestriction j F) ≅
      schemeNeighborhoodValue (f ≫ j) F :=
  asIso (colimit.pre ((schemeNeighborhoodInclusion (f ≫ j)).op ⋙ F)
    (ambientNeighborhoodImage f j).op)

@[simp] theorem ambientNeighborhoodIso_representative
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) (U : SchemeNeighborhoods f) :
    colimit.ι ((schemeNeighborhoodInclusion f).op ⋙ ambientRestriction j F) (op U) ≫
        (ambientNeighborhoodIso f j F).hom =
      colimit.ι ((schemeNeighborhoodInclusion (f ≫ j)).op ⋙ F)
        (op ((ambientNeighborhoodImage f j).obj U)) :=
  colimit.ι_pre ((schemeNeighborhoodInclusion (f ≫ j)).op ⋙ F)
    (ambientNeighborhoodImage f j).op (op U)

/-- In particular this applies to the actual sheafification unit, without
replacing it by an arbitrarily chosen isomorphism. -/
theorem ambientNeighborhoodIso_map
    {F G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : F ⟶ G) :
    schemeNeighborhoodMap f (ambientRestrictionMap j η) ≫ (ambientNeighborhoodIso f j G).hom =
      (ambientNeighborhoodIso f j F).hom ≫ schemeNeighborhoodMap (f ≫ j) η := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec
  simp only [← Category.assoc, schemeNeighborhoodMap_representative,
    ambientNeighborhoodIso_representative]
  rw [Category.assoc, ambientNeighborhoodIso_representative]
  rfl

/-- All genuine restriction maps commute with the ambient comparison. -/
theorem ambientNeighborhoodIso_restriction {Z : Scheme.{u}} (g : Z ⟶ Y)
    (k : Z ⟶ T) (hk : k ≫ f = g) (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodRestriction f g k hk (ambientRestriction j F) ≫
        (ambientNeighborhoodIso g j F).hom =
      (ambientNeighborhoodIso f j F).hom ≫
        schemeNeighborhoodRestriction (f ≫ j) (g ≫ j) k (by rw [← Category.assoc,hk]) F := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec
  simp only [← Category.assoc, schemeNeighborhoodRestriction_representative,
    ambientNeighborhoodIso_representative]
  rfl

end
end MathGauge.GP003
