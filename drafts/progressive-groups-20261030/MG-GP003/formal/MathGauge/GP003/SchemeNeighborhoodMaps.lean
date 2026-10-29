import MathGauge.GP003.ActualSemilocalDescent

/-! The original presheaf map and restriction maps on actual neighborhood
presentations of S and its open subschemes. No sheaf property of this extension
is assumed. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
open AlgebraicGeometry MathGauge.PublicProof.Semilocal

universe u
variable {X T Y : Scheme.{u}}

def schemeNeighborhoodMap (f : T ⟶ X) {F G : X.carrier.Presheaf AddCommGrpCat.{u}}
    (η : F ⟶ G) : schemeNeighborhoodValue f F ⟶ schemeNeighborhoodValue f G :=
  colim.map (whiskerLeft (schemeNeighborhoodInclusion f).op η)

@[simp] theorem schemeNeighborhoodMap_representative (f : T ⟶ X)
    {F G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : F ⟶ G) (U : SchemeNeighborhoods f) :
    colimit.ι ((schemeNeighborhoodInclusion f).op ⋙ F) (op U) ≫ schemeNeighborhoodMap f η =
      η.app (op U.1) ≫ colimit.ι ((schemeNeighborhoodInclusion f).op ⋙ G) (op U) :=
  colimit.ι_map (whiskerLeft (schemeNeighborhoodInclusion f).op η) (op U)

/-- Naturality for the actual map over X and the actual original presheaf map. -/
theorem schemeNeighborhoodMap_naturality (f : T ⟶ X) (g : Y ⟶ X)
    (k : Y ⟶ T) (hk : k ≫ f = g) {F G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : F ⟶ G) :
    schemeNeighborhoodMap f η ≫ schemeNeighborhoodRestriction f g k hk G =
      schemeNeighborhoodRestriction f g k hk F ≫ schemeNeighborhoodMap g η := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec
  simp only [← Category.assoc, schemeNeighborhoodMap_representative,
    schemeNeighborhoodRestriction_representative]
  rw [Category.assoc,schemeNeighborhoodRestriction_representative]
  rfl

def schemeOpenToAmbient (f : T ⟶ X) (U : T.Opens) : U.toScheme ⟶ X := U.ι ≫ f

def schemeOpenValue (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u}) (U : T.Opens) :=
  schemeNeighborhoodValue (schemeOpenToAmbient f U) F

def schemeOpenRestriction (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u}) (U : T.Opens) :
    schemeNeighborhoodValue f F ⟶ schemeOpenValue f F U :=
  schemeNeighborhoodRestriction f (schemeOpenToAmbient f U) U.ι rfl F

def schemeOpenRestrictionLE (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u})
    {U V : T.Opens} (hVU : V ≤ U) : schemeOpenValue f F U ⟶ schemeOpenValue f F V :=
  schemeNeighborhoodRestriction (schemeOpenToAmbient f U) (schemeOpenToAmbient f V)
    (T.homOfLE hVU) (by unfold schemeOpenToAmbient; rw [← Category.assoc,T.homOfLE_ι]) F

@[simp] theorem schemeOpenRestriction_comp (f : T ⟶ X)
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) {U V : T.Opens} (hVU : V ≤ U) :
    schemeOpenRestriction f F U ≫ schemeOpenRestrictionLE f F hVU = schemeOpenRestriction f F V := by
  unfold schemeOpenRestriction schemeOpenRestrictionLE
  rw [schemeNeighborhoodRestriction_comp]
  simp only [T.homOfLE_ι]

theorem schemeOpenRestrictionLE_comp (f : T ⟶ X)
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) {U V W : T.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) :
    schemeOpenRestrictionLE f F hVU ≫ schemeOpenRestrictionLE f F hWV =
      schemeOpenRestrictionLE f F (hWV.trans hVU) := by
  unfold schemeOpenRestrictionLE
  rw [schemeNeighborhoodRestriction_comp]
  simp only [T.homOfLE_homOfLE]

/-- The two genuine open restrictions from the actual S value. -/
def schemeTwoOpenRestriction (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (U V : T.Opens) :
    schemeNeighborhoodValue f F →+ (schemeOpenValue f F U × schemeOpenValue f F V) :=
  (schemeOpenRestriction f F U).hom.prod (schemeOpenRestriction f F V).hom

/-- Difference of the genuine restrictions to the actual open intersection. -/
def schemeTwoOpenDifference (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (U V : T.Opens) :
    (schemeOpenValue f F U × schemeOpenValue f F V) →+ schemeOpenValue f F (U ⊓ V) :=
  ((schemeOpenRestrictionLE f F (show U ⊓ V ≤ U from inf_le_left)).hom.comp
    (AddMonoidHom.fst _ _)) -
  ((schemeOpenRestrictionLE f F (show U ⊓ V ≤ V from inf_le_right)).hom.comp
    (AddMonoidHom.snd _ _))

/-- A section on an actual ambient open through which f factors. -/
def sectionToSchemeValue (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (U : X.Opens) (hU : Set.range f ⊆ U) : F.obj (op U) ⟶ schemeNeighborhoodValue f F :=
  colimit.ι ((schemeNeighborhoodInclusion f).op ⋙ F)
    (op ⟨U,(factors_open_iff_range f U).mpr hU⟩)

theorem sectionToSchemeValue_restrict (f : T ⟶ X)
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) {U V : X.Opens}
    (hU : Set.range f ⊆ U) (hV : Set.range f ⊆ V) (hVU : V ≤ U) :
    F.map (homOfLE hVU).op ≫ sectionToSchemeValue f F V hV = sectionToSchemeValue f F U hU := by
  exact colimit.w ((schemeNeighborhoodInclusion f).op ⋙ F)
    (homOfLE (show (⟨V,(factors_open_iff_range f V).mpr hV⟩ : SchemeNeighborhoods f) ≤
      ⟨U,(factors_open_iff_range f U).mpr hU⟩ from hVU)).op

theorem sectionToSchemeValue_map (f : T ⟶ X)
    {F G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : F ⟶ G)
    (U : X.Opens) (hU : Set.range f ⊆ U) :
    sectionToSchemeValue f F U hU ≫ schemeNeighborhoodMap f η =
      η.app (op U) ≫ sectionToSchemeValue f G U hU :=
  schemeNeighborhoodMap_representative f η _

theorem sectionToSchemeValue_restrictTarget (f : T ⟶ X) (g : Y ⟶ X)
    (k : Y ⟶ T) (hk : k ≫ f = g) (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (U : X.Opens) (hU : Set.range f ⊆ U) (hU' : Set.range g ⊆ U) :
    sectionToSchemeValue f F U hU ≫ schemeNeighborhoodRestriction f g k hk F =
      sectionToSchemeValue g F U hU' :=
  schemeNeighborhoodRestriction_representative f g k hk F _


variable {R : Type u} [CommRing R] {sigma : Finset (PrimeSpectrum R)}

/-- The extension of the actual unit on a local scheme is the actual ambient
stalk map, via the proved local-ring/presentation comparison. -/
theorem actualLocalValueIso_naturality (q : PrimeSpectrum (semilocalRing sigma))
    {F G : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}} (η : F ⟶ G) :
    schemeNeighborhoodMap (localToAmbient q) η ≫ (actualLocalValueIso q G).hom =
      (actualLocalValueIso q F).hom ≫ (stalkFunctor (X := TopCat.of (PrimeSpectrum R)) AddCommGrpCat.{u} (ambientPoint q)).map η := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec with
  | _ U =>
    rw [← Category.assoc,schemeNeighborhoodMap_representative,Category.assoc,
      actualLocalValueIso_representative,← Category.assoc,actualLocalValueIso_representative]
    exact (stalkFunctor_map_germ U.1 (ambientPoint q) (actualLocalPoint_mem q U) η).symm

/-- Local bijectivity in the problem's actual neighborhood presentation implies
surjectivity of the actual ambient stalk map used to select representatives. -/
theorem ambient_stalk_surjective_of_actual_local (q : PrimeSpectrum (semilocalRing sigma))
    {F G : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}} (η : F ⟶ G)
    (h : Function.Surjective (schemeNeighborhoodMap (localToAmbient q) η)) :
    Function.Surjective ((stalkFunctor (X := TopCat.of (PrimeSpectrum R)) AddCommGrpCat.{u} (ambientPoint q)).map η) := by
  intro b
  obtain ⟨b',hb'⟩ := (ConcreteCategory.bijective_of_isIso (actualLocalValueIso q G).hom).2 b
  obtain ⟨a,ha⟩ := h b'
  refine ⟨(actualLocalValueIso q F).hom a,?_⟩
  have hh := ConcreteCategory.congr_hom (actualLocalValueIso_naturality q η) a
  change (actualLocalValueIso q G).hom (schemeNeighborhoodMap (localToAmbient q) η a) = _ at hh
  rw [ha,hb'] at hh
  exact hh.symm

end
end MathGauge.GP003
