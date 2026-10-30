import MathGauge.GP003.AffineRestriction

/-! The semilocal equalizer in the original, possibly nonaffine ambient scheme.
An affine presentation is part of the construction of a semilocalization, not
an assumption that the original scheme is affine. The original sheaf, its
actual neighborhood extensions and both actual pullback arrows are retained. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry MathGauge.PublicProof.Semilocal

universe u
variable {R : Type u} [CommRing R] {sigma : Finset (PrimeSpectrum R)}
variable {X : Scheme.{u}} (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]

def generalLocalRestriction (q : PrimeSpectrum (semilocalRing sigma))
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (semilocalToAmbient sigma ≫ j) F ⟶
      schemeNeighborhoodValue (localToAmbient q ≫ j) F :=
  schemeNeighborhoodRestriction (semilocalToAmbient sigma ≫ j) (localToAmbient q ≫ j)
    (localToSemilocal q) (Category.assoc _ _ _).symm F

def generalFiberLeftRestriction (q r : PrimeSpectrum (semilocalRing sigma))
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (localToAmbient q ≫ j) F ⟶
      schemeNeighborhoodValue (localFiberToAmbient q r ≫ j) F :=
  schemeNeighborhoodRestriction (localToAmbient q ≫ j) (localFiberToAmbient q r ≫ j)
    (pullback.fst (localToSemilocal q) (localToSemilocal r))
    (Category.assoc _ _ _).symm F

def generalFiberRightRestriction (q r : PrimeSpectrum (semilocalRing sigma))
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (localToAmbient r ≫ j) F ⟶
      schemeNeighborhoodValue (localFiberToAmbient q r ≫ j) F :=
  schemeNeighborhoodRestriction (localToAmbient r ≫ j) (localFiberToAmbient q r ≫ j)
    (pullback.snd (localToSemilocal q) (localToSemilocal r))
    (by rw [← Category.assoc, fiberRight_over]) F

variable {ι : Type u} (q : ι → PrimeSpectrum (semilocalRing sigma))

def generalRestrictionFamily (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (semilocalToAmbient sigma ≫ j) F →+
      ∀ i, schemeNeighborhoodValue (localToAmbient (q i) ≫ j) F where
  toFun a i := generalLocalRestriction j (q i) F a
  map_zero' := by funext i; exact map_zero _
  map_add' a b := by funext i; exact map_add _ a b

def generalOverlapDifference (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    (∀ i, schemeNeighborhoodValue (localToAmbient (q i) ≫ j) F) →+
      ∀ i k, schemeNeighborhoodValue (localFiberToAmbient (q i) (q k) ≫ j) F where
  toFun a i k := generalFiberLeftRestriction j (q i) (q k) F (a i) -
    generalFiberRightRestriction j (q i) (q k) F (a k)
  map_zero' := by funext i k; simp
  map_add' a b := by funext i k; simp only [Pi.add_apply,map_add]; abel

theorem generalRestrictionFamily_comparison (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (a : schemeNeighborhoodValue (semilocalToAmbient sigma) (ambientRestriction j F)) (i : ι) :
    (ambientNeighborhoodIso (localToAmbient (q i)) j F).hom
        (actualRestrictionFamily q (ambientRestriction j F) a i) =
      generalRestrictionFamily j q F
        ((ambientNeighborhoodIso (semilocalToAmbient sigma) j F).hom a) i :=
  ConcreteCategory.congr_hom (ambientNeighborhoodIso_restriction
    (semilocalToAmbient sigma) j (localToAmbient (q i)) (localToSemilocal (q i)) rfl F) a

theorem generalOverlapDifference_comparison (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (a : ∀ i, schemeNeighborhoodValue (localToAmbient (q i)) (ambientRestriction j F)) (i k : ι) :
    (ambientNeighborhoodIso (localFiberToAmbient (q i) (q k)) j F).hom
        (actualOverlapDifference q (ambientRestriction j F) a i k) =
      generalOverlapDifference j q F
        (fun i => (ambientNeighborhoodIso (localToAmbient (q i)) j F).hom (a i)) i k := by
  have hL := ConcreteCategory.congr_hom (ambientNeighborhoodIso_restriction
    (localToAmbient (q i)) j (localFiberToAmbient (q i) (q k))
    (pullback.fst (localToSemilocal (q i)) (localToSemilocal (q k))) rfl F) (a i)
  have hR := ConcreteCategory.congr_hom (ambientNeighborhoodIso_restriction
    (localToAmbient (q k)) j (localFiberToAmbient (q i) (q k))
    (pullback.snd (localToSemilocal (q i)) (localToSemilocal (q k)))
    (fiberRight_over (q i) (q k)) F) (a k)
  change (ambientNeighborhoodIso (localFiberToAmbient (q i) (q k)) j F).hom
    (fiberLeftRestriction (q i) (q k) (ambientRestriction j F) (a i)) =
    generalFiberLeftRestriction j (q i) (q k) F
      ((ambientNeighborhoodIso (localToAmbient (q i)) j F).hom (a i)) at hL
  change (ambientNeighborhoodIso (localFiberToAmbient (q i) (q k)) j F).hom
    (fiberRightRestriction (q i) (q k) (ambientRestriction j F) (a k)) =
    generalFiberRightRestriction j (q i) (q k) F
      ((ambientNeighborhoodIso (localToAmbient (q k)) j F).hom (a k)) at hR
  change (ambientNeighborhoodIso (localFiberToAmbient (q i) (q k)) j F).hom (_ - _) = _ - _
  rw [map_sub,hL,hR]

/-- S1 for every semilocalization presented in an affine open of an arbitrary
scheme X. In particular X itself need not be affine. The statement is about
the original G on X and its original-X neighborhood colimits, and the actual
fiber products of local schemes. No S_i is assumed open. -/
theorem general_semilocal_descent_exact [Finite ι]
    (hexhaust : ∀ z : PrimeSpectrum (semilocalRing sigma),
      IsClosed ({z} : Set (PrimeSpectrum (semilocalRing sigma))) → z ∈ Set.range q)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X.carrier) :
    Function.Injective (generalRestrictionFamily j q G.obj) ∧
      Function.Exact (generalRestrictionFamily j q G.obj) (generalOverlapDifference j q G.obj) := by
  let E := ambientRestriction j G.obj
  have he := affine_semilocal_descent_exact q hexhaust (ambientRestrictionSheaf j G)
  change Function.Injective (actualRestrictionFamily q E) ∧
    Function.Exact (actualRestrictionFamily q E) (actualOverlapDifference q E) at he
  let e := ambientNeighborhoodIso (semilocalToAmbient sigma) j G.obj
  let eL i := ambientNeighborhoodIso (localToAmbient (q i)) j G.obj
  let eF i k := ambientNeighborhoodIso (localFiberToAmbient (q i) (q k)) j G.obj
  have hglobal := ConcreteCategory.bijective_of_isIso e.hom
  have hlocal i := ConcreteCategory.bijective_of_isIso (eL i).hom
  have hfiber i k := ConcreteCategory.bijective_of_isIso (eF i k).hom
  refine ⟨?_,?_⟩
  · intro a b hab
    obtain ⟨a',rfl⟩ := hglobal.2 a
    obtain ⟨b',rfl⟩ := hglobal.2 b
    congr 1
    apply he.1
    funext i
    apply (hlocal i).1
    exact (generalRestrictionFamily_comparison j q G.obj a' i).trans
      ((congrFun hab i).trans (generalRestrictionFamily_comparison j q G.obj b' i).symm)
  · intro a
    constructor
    · intro ha
      let a' i := (eL i).inv (a i)
      have haa i : (eL i).hom (a' i) = a i := by
        exact ConcreteCategory.congr_hom (eL i).inv_hom_id (a i)
      have hz : actualOverlapDifference q E a' = 0 := by
        funext i k
        apply (hfiber i k).1
        simp only [Pi.zero_apply, map_zero]
        change (ambientNeighborhoodIso (localFiberToAmbient (q i) (q k)) j G.obj).hom
          (actualOverlapDifference q E a' i k) = 0
        rw [generalOverlapDifference_comparison]
        have hfun : (fun i => (ambientNeighborhoodIso (localToAmbient (q i)) j G.obj).hom (a' i)) = a := by
          funext i
          exact haa i
        rw [hfun]
        exact congrFun (congrFun ha i) k
      obtain ⟨b,hb⟩ := (he.2 a').mp hz
      refine ⟨e.hom b,?_⟩
      funext i
      rw [← generalRestrictionFamily_comparison j q G.obj b i]
      change (eL i).hom (actualRestrictionFamily q E b i) = a i
      rw [hb,haa]
    · rintro ⟨b,rfl⟩
      obtain ⟨b',rfl⟩ := hglobal.2 b
      have hc := (he.2 (actualRestrictionFamily q E b')).mpr ⟨b',rfl⟩
      funext i k
      have hfamily : generalRestrictionFamily j q G.obj (e.hom b') =
          (fun i => (eL i).hom (actualRestrictionFamily q E b' i)) := by
        funext i
        exact (generalRestrictionFamily_comparison j q G.obj b' i).symm
      rw [hfamily]
      rw [← generalOverlapDifference_comparison]
      rw [show actualOverlapDifference q E (actualRestrictionFamily q E b') i k = 0 from
        congrFun (congrFun hc i) k,map_zero]
      rfl

omit [IsOpenImmersion j] in
/-- The original-X neighborhood convention uses precisely the finite image
of the selected primes, including primes not closed in X. -/
theorem general_finitePoint_neighborhood_iff (hsigma : sigma.Nonempty) (U : X.Opens) :
    j '' (sigma : Set (PrimeSpectrum R)) ⊆ U ↔
      Set.range (semilocalToAmbient sigma ≫ j) ⊆ U := by
  have h := localization_image_neighborhood_iff sigma hsigma (semilocalRing sigma)
    ((Opens.map j.base).obj U)
  constructor
  · intro hs z hz
    obtain ⟨t,rfl⟩ := hz
    exact h.mp (fun p hp => hs ⟨p,hp,rfl⟩) ⟨t,rfl⟩
  · intro hs z hz
    obtain ⟨p,hp,rfl⟩ := hz
    apply h.mpr (fun z hz => ?_) hp
    obtain ⟨t,rfl⟩ := hz
    exact hs ⟨t,rfl⟩

def generalFinitePointValueIso (hsigma : sigma.Nonempty)
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (semilocalToAmbient sigma ≫ j) F ≅
      neighborhood_value F (j '' (sigma : Set (PrimeSpectrum R))) :=
  schemeNeighborhoodValueIso _ F ≪≫
    sameNeighborhoodIso F (fun U => (general_finitePoint_neighborhood_iff j hsigma U).symm)

def generalFinitePointNeighborhood (hsigma : sigma.Nonempty)
    (U : SchemeNeighborhoods (semilocalToAmbient sigma ≫ j)) :
    SetNeighborhoods (X := X.carrier) (j '' (sigma : Set (PrimeSpectrum R))) :=
  ⟨U.1, (general_finitePoint_neighborhood_iff j hsigma U.1).mpr
    ((factors_open_iff_range _ _).mp U.2)⟩

@[simp] theorem generalFinitePointValueIso_representative (hsigma : sigma.Nonempty)
    (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (U : SchemeNeighborhoods (semilocalToAmbient sigma ≫ j)) :
    colimit.ι ((schemeNeighborhoodInclusion (semilocalToAmbient sigma ≫ j)).op ⋙ F) (op U) ≫
      (generalFinitePointValueIso j hsigma F).hom =
      colimit.ι ((neighborhood_inclusion (X := X.carrier)
        (j '' (sigma : Set (PrimeSpectrum R)))).op ⋙ F)
          (op (generalFinitePointNeighborhood j hsigma U)) := by
  unfold generalFinitePointValueIso
  rw [Iso.trans_hom,← Category.assoc, schemeNeighborhoodValueIso_representative,
    sameNeighborhoodIso_representative]
  rfl

/-- Identification with the finite-point convention preserves the original
natural map, in particular the canonical sheafification unit. -/
theorem generalFinitePointValueIso_map (hsigma : sigma.Nonempty)
    {F G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : F ⟶ G) :
    schemeNeighborhoodMap (semilocalToAmbient sigma ≫ j) η ≫
      (generalFinitePointValueIso j hsigma G).hom =
      (generalFinitePointValueIso j hsigma F).hom ≫
        neighborhood_value_map η (j '' (sigma : Set (PrimeSpectrum R))) := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec
  simp only [← Category.assoc,schemeNeighborhoodMap_representative,
    generalFinitePointValueIso_representative]
  rw [Category.assoc, generalFinitePointValueIso_representative,
    neighborhood_value_map_representative]
  rfl

end
end MathGauge.GP003
