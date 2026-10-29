import MathGauge.GP003.SchemeNeighborhoodValues

/-! Descent on actual affine semilocal schemes, with actual local schemes and
fiber products. All maps arise by restricting the open-scheme presentations. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
open AlgebraicGeometry MathGauge.PublicProof.Semilocal

universe u
variable {R : Type u} [CommRing R] {sigma : Finset (PrimeSpectrum R)}

abbrev ambientPoint (q : PrimeSpectrum (semilocalRing sigma)) : PrimeSpectrum R :=
  PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q

/-- The actual restriction S_i → S on the neighborhood-colimit extension. -/
def localRestriction (q : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (semilocalToAmbient sigma) F ⟶
      schemeNeighborhoodValue (localToAmbient q) F :=
  schemeNeighborhoodRestriction (semilocalToAmbient sigma) (localToAmbient q)
    (localToSemilocal q) rfl F

def fiberLeftRestriction (q r : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (localToAmbient q) F ⟶
      schemeNeighborhoodValue (localFiberToAmbient q r) F :=
  schemeNeighborhoodRestriction (localToAmbient q) (localFiberToAmbient q r)
    (pullback.fst (localToSemilocal q) (localToSemilocal r)) rfl F

theorem fiberRight_over (q r : PrimeSpectrum (semilocalRing sigma)) :
    pullback.snd (localToSemilocal q) (localToSemilocal r) ≫ localToAmbient r =
      localFiberToAmbient q r := by
  unfold localFiberToAmbient localToAmbient
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

def fiberRightRestriction (q r : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (localToAmbient r) F ⟶
      schemeNeighborhoodValue (localFiberToAmbient q r) F :=
  schemeNeighborhoodRestriction (localToAmbient r) (localFiberToAmbient q r)
    (pullback.snd (localToSemilocal q) (localToSemilocal r)) (fiberRight_over q r) F

def actualFiberPairNeighborhood (q r : PrimeSpectrum (semilocalRing sigma))
    (U : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint q))
    (V : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint r)) :
    SchemeNeighborhoods (localFiberToAmbient q r) :=
  ⟨U.1 ⊓ V.1,(factors_open_iff_range _ _).mpr (by
    rw [localFiberToAmbient_range,pairLocalImage_eq]
    intro z hz
    exact ⟨((PrimeSpectrum.le_iff_specializes z _).mp hz.1).mem_open U.1.isOpen U.2,
      ((PrimeSpectrum.le_iff_specializes z _).mp hz.2).mem_open V.1.isOpen V.2⟩)⟩

/-- A pair presentation of the actual scheme fiber product gives exactly the
corresponding representative in the pair-overlap colimit. -/
theorem actualFiberValueIso_pair_representative (q r : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (U : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint q))
    (V : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint r)) :
    colimit.ι ((schemeNeighborhoodInclusion (localFiberToAmbient q r)).op ⋙ F)
      (op (actualFiberPairNeighborhood q r U V)) ≫ (actualFiberValueIso q r F).hom =
      colimit.ι (pairIntersection (ambientPoint q) (ambientPoint r) ⋙ F) (op U,op V) := by
  dsimp only [actualFiberValueIso, Iso.trans_hom]
  rw [← Category.assoc, schemeNeighborhoodValueIso_representative,
    ← Category.assoc, sameNeighborhoodIso_representative]
  change colimit.ι ((neighborhood_inclusion (X := TopCat.of (PrimeSpectrum R))
      (pairLocalImage (ambientPoint q) (ambientPoint r))).op ⋙ F)
      ((pairNeighborhoodToImage (ambientPoint q) (ambientPoint r)).obj (op U,op V)) ≫
        (overlapLocalizationIso (ambientPoint q) (ambientPoint r) F).inv = _
  rw [← overlapLocalizationIso_representative]
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- Compatibility of the first actual pullback restriction with the first
pair-overlap map; proved on all neighborhood representatives. -/
theorem fiberLeftRestriction_overlap (q r : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    fiberLeftRestriction q r F ≫ (actualFiberValueIso q r F).hom =
      (actualLocalValueIso q F).hom ≫ leftOverlapMap F (ambientPoint q) (ambientPoint r) := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec with
  | _ U =>
    let A : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint q) :=
      ⟨U.1,actualLocalPoint_mem q U⟩
    let B : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint r) := ⟨⊤,by trivial⟩
    let W := (schemeNeighborhoodChange (localToAmbient q) (localFiberToAmbient q r)
      (pullback.fst (localToSemilocal q) (localToSemilocal r)) rfl).obj U
    have hle : actualFiberPairNeighborhood q r A B ≤ W :=
      (show A.1 ⊓ B.1 ≤ U.1 from inf_le_left)
    have hw := colimit.w ((schemeNeighborhoodInclusion (localFiberToAmbient q r)).op ⋙ F)
      (homOfLE hle).op
    change F.map (homOfLE inf_le_left : A.1 ⊓ B.1 ⟶ U.1).op ≫
      colimit.ι ((schemeNeighborhoodInclusion (localFiberToAmbient q r)).op ⋙ F)
        (op (actualFiberPairNeighborhood q r A B)) =
          colimit.ι ((schemeNeighborhoodInclusion (localFiberToAmbient q r)).op ⋙ F) (op W) at hw
    rw [← Category.assoc, ← Category.assoc, actualLocalValueIso_representative]
    unfold fiberLeftRestriction
    rw [schemeNeighborhoodRestriction_representative, ← hw, Category.assoc,
      actualFiberValueIso_pair_representative]
    exact (leftOverlapMap_germ F (ambientPoint q) (ambientPoint r) A B).symm

/-- Compatibility of the second actual pullback restriction with the second
pair-overlap map; no symmetry of the two actual projections is assumed. -/
theorem fiberRightRestriction_overlap (q r : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    fiberRightRestriction q r F ≫ (actualFiberValueIso q r F).hom =
      (actualLocalValueIso r F).hom ≫ rightOverlapMap F (ambientPoint q) (ambientPoint r) := by
  apply colimit.hom_ext
  intro V
  cases V using Opposite.rec with
  | _ V =>
    let A : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint q) := ⟨⊤,by trivial⟩
    let B : OpenNhds (X := TopCat.of (PrimeSpectrum R)) (ambientPoint r) :=
      ⟨V.1,actualLocalPoint_mem r V⟩
    let W := (schemeNeighborhoodChange (localToAmbient r) (localFiberToAmbient q r)
      (pullback.snd (localToSemilocal q) (localToSemilocal r)) (fiberRight_over q r)).obj V
    have hle : actualFiberPairNeighborhood q r A B ≤ W :=
      (show A.1 ⊓ B.1 ≤ V.1 from inf_le_right)
    have hw := colimit.w ((schemeNeighborhoodInclusion (localFiberToAmbient q r)).op ⋙ F)
      (homOfLE hle).op
    change F.map (homOfLE inf_le_right : A.1 ⊓ B.1 ⟶ V.1).op ≫
      colimit.ι ((schemeNeighborhoodInclusion (localFiberToAmbient q r)).op ⋙ F)
        (op (actualFiberPairNeighborhood q r A B)) =
          colimit.ι ((schemeNeighborhoodInclusion (localFiberToAmbient q r)).op ⋙ F) (op W) at hw
    rw [← Category.assoc, ← Category.assoc, actualLocalValueIso_representative]
    unfold fiberRightRestriction
    rw [schemeNeighborhoodRestriction_representative, ← hw, Category.assoc,
      actualFiberValueIso_pair_representative]
    exact (rightOverlapMap_germ F (ambientPoint q) (ambientPoint r) A B).symm


variable {ι : Type u} (q : ι → PrimeSpectrum (semilocalRing sigma))
    (hexhaust : ∀ z : PrimeSpectrum (semilocalRing sigma),
      IsClosed ({z} : Set (PrimeSpectrum (semilocalRing sigma))) → z ∈ Set.range q)

def actualGlobalValueIso
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (semilocalToAmbient sigma) F ≅
      neighborhood_value F (Set.range (fun i => ambientPoint (q i))) :=
  schemeNeighborhoodValueIso (semilocalToAmbient sigma) F ≪≫
    sameNeighborhoodIso F (fun U => (closed_point_images_neighborhood_iff sigma q hexhaust U).symm)

@[simp] theorem actualGlobalValueIso_representative
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (U : SchemeNeighborhoods (semilocalToAmbient sigma)) :
    colimit.ι ((schemeNeighborhoodInclusion (semilocalToAmbient sigma)).op ⋙ F) (op U) ≫
      (actualGlobalValueIso q hexhaust F).hom =
        colimit.ι ((neighborhood_inclusion (X := TopCat.of (PrimeSpectrum R))
          (Set.range (fun i => ambientPoint (q i)))).op ⋙ F)
          (op ((sameNeighborhoodOrderIso
            (fun W => (closed_point_images_neighborhood_iff sigma q hexhaust W).symm))
              ((schemeNeighborhoodOrderIso (semilocalToAmbient sigma)) U))) := by
  dsimp only [actualGlobalValueIso, Iso.trans_hom]
  rw [← Category.assoc, schemeNeighborhoodValueIso_representative,
    sameNeighborhoodIso_representative]
  rfl

def actualRestrictionFamily
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (semilocalToAmbient sigma) F →+
      ∀ i, schemeNeighborhoodValue (localToAmbient (q i)) F where
  toFun a i := localRestriction (q i) F a
  map_zero' := by funext i; exact map_zero _
  map_add' a b := by funext i; exact map_add _ a b

def actualOverlapDifference
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    (∀ i, schemeNeighborhoodValue (localToAmbient (q i)) F) →+
      ∀ i j, schemeNeighborhoodValue (localFiberToAmbient (q i) (q j)) F where
  toFun a i j := fiberLeftRestriction (q i) (q j) F (a i) -
    fiberRightRestriction (q i) (q j) F (a j)
  map_zero' := by funext i j; simp
  map_add' a b := by funext i j; simp only [Pi.add_apply,map_add]; abel

/-- The actual global-to-local restriction is the actual germ map under the
canonical presentation comparisons. This checks the arrows, not just objects. -/
theorem actualRestrictionFamily_germ
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (a : schemeNeighborhoodValue (semilocalToAmbient sigma) F) (i : ι) :
    (actualLocalValueIso (q i) F).hom (actualRestrictionFamily q F a i) =
      neighborhoodGermFamily (fun i => ambientPoint (q i)) F
        ((actualGlobalValueIso q hexhaust F).hom a) i := by
  obtain ⟨U,a,rfl⟩ := Concrete.colimit_exists_rep
    ((schemeNeighborhoodInclusion (semilocalToAmbient sigma)).op ⋙ F) a
  cases U using Opposite.rec with
  | _ U =>
    let W := (schemeNeighborhoodChange (semilocalToAmbient sigma) (localToAmbient (q i))
      (localToSemilocal (q i)) rfl).obj U
    have hL := ConcreteCategory.congr_hom
      (schemeNeighborhoodRestriction_representative (semilocalToAmbient sigma)
        (localToAmbient (q i)) (localToSemilocal (q i)) rfl F U) a
    change localRestriction (q i) F
      (colimit.ι ((schemeNeighborhoodInclusion (semilocalToAmbient sigma)).op ⋙ F) (op U) a) =
        colimit.ι ((schemeNeighborhoodInclusion (localToAmbient (q i))).op ⋙ F) (op W) a at hL
    change (actualLocalValueIso (q i) F).hom (localRestriction (q i) F _) = _
    rw [hL]
    have hLI := ConcreteCategory.congr_hom (actualLocalValueIso_representative (q i) F W) a
    change (actualLocalValueIso (q i) F).hom
      (colimit.ι ((schemeNeighborhoodInclusion (localToAmbient (q i))).op ⋙ F) (op W) a) = _ at hLI
    rw [hLI]
    have hG := ConcreteCategory.congr_hom (actualGlobalValueIso_representative q hexhaust F U) a
    change (actualGlobalValueIso q hexhaust F).hom
      (colimit.ι ((schemeNeighborhoodInclusion (semilocalToAmbient sigma)).op ⋙ F) (op U) a) = _ at hG
    rw [hG]
    let Z : SetNeighborhoods (X := TopCat.of (PrimeSpectrum R))
        (Set.range (fun j => ambientPoint (q j))) :=
      (sameNeighborhoodOrderIso (fun W =>
        (closed_point_images_neighborhood_iff sigma q hexhaust W).symm))
          ((schemeNeighborhoodOrderIso (semilocalToAmbient sigma)) U)
    exact (neighborhoodGermFamily_representative (X := TopCat.of (PrimeSpectrum R)) (fun j => ambientPoint (q j)) F Z a i).symm

/-- The actual difference of pullback restrictions is exactly the overlap
difference after the canonical local and fiber-product presentation isomorphisms. -/
theorem actualOverlapDifference_comparison
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (a : ∀ i, schemeNeighborhoodValue (localToAmbient (q i)) F) (i j : ι) :
    (actualFiberValueIso (q i) (q j) F).hom (actualOverlapDifference q F a i j) =
      overlapDifference (fun i => ambientPoint (q i)) F
        (fun i => (actualLocalValueIso (q i) F).hom (a i)) i j := by
  have hL := ConcreteCategory.congr_hom (fiberLeftRestriction_overlap (q i) (q j) F) (a i)
  have hR := ConcreteCategory.congr_hom (fiberRightRestriction_overlap (q i) (q j) F) (a j)
  change (actualFiberValueIso (q i) (q j) F).hom (fiberLeftRestriction (q i) (q j) F (a i)) =
    leftOverlapMap F (ambientPoint (q i)) (ambientPoint (q j))
      ((actualLocalValueIso (q i) F).hom (a i)) at hL
  change (actualFiberValueIso (q i) (q j) F).hom (fiberRightRestriction (q i) (q j) F (a j)) =
    rightOverlapMap F (ambientPoint (q i)) (ambientPoint (q j))
      ((actualLocalValueIso (q j) F).hom (a j)) at hR
  change (actualFiberValueIso (q i) (q j) F).hom (_ - _) = _ - _
  rw [map_sub,hL,hR]

include hexhaust in
/-- Full equalizer for a given affine semilocal presentation. The values are
actual open-scheme neighborhood colimits, S_i are actual local schemes of S,
and S_i ×_S S_j are actual scheme pullbacks. The two arrows are the genuine
pullback restriction maps. No smoothness, perfectness, ambient closedness or
openness of the local schemes is assumed. The finite family exhausts S's closed
points, as required in S1; arbitrary quasi-projective common-affine existence
is a separate geometric obligation, not hidden in this theorem. -/
theorem affine_semilocal_descent_exact [Finite ι]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R))) :
    Function.Injective (actualRestrictionFamily q G.obj) ∧
      Function.Exact (actualRestrictionFamily q G.obj) (actualOverlapDifference q G.obj) := by
  let x : ι → PrimeSpectrum R := fun i => ambientPoint (q i)
  have he := finite_neighborhood_descent_exact (X := TopCat.of (PrimeSpectrum R)) x G
  have hglobal := ConcreteCategory.bijective_of_isIso (actualGlobalValueIso q hexhaust G.obj).hom
  have hlocal i := ConcreteCategory.bijective_of_isIso (actualLocalValueIso (q i) G.obj).hom
  have hfiber i j := ConcreteCategory.bijective_of_isIso (actualFiberValueIso (q i) (q j) G.obj).hom
  refine ⟨?_,?_⟩
  · intro a b hab
    apply hglobal.1
    apply he.1
    funext i
    rw [← actualRestrictionFamily_germ q hexhaust G.obj a i,
      ← actualRestrictionFamily_germ q hexhaust G.obj b i,hab]
  · intro a
    constructor
    · intro ha
      let b : ∀ i, (TopCat.Presheaf.stalk G.obj) (x i) :=
        fun i => (actualLocalValueIso (q i) G.obj).hom (a i)
      have hb : overlapDifference x G.obj b = 0 := by
        funext i j
        simp only [Pi.zero_apply]
        rw [← actualOverlapDifference_comparison q G.obj a i j]
        rw [show actualOverlapDifference q G.obj a i j = 0 from
          congrFun (congrFun ha i) j,map_zero]
      obtain ⟨c,hc⟩ := (he.2 b).mp hb
      obtain ⟨d,hd⟩ := hglobal.2 c
      refine ⟨d,?_⟩
      funext i
      apply (hlocal i).1
      rw [actualRestrictionFamily_germ q hexhaust G.obj d i,hd]
      exact congrFun hc i
    · rintro ⟨d,rfl⟩
      funext i j
      simp only [Pi.zero_apply]
      apply (hfiber i j).1
      rw [map_zero,actualOverlapDifference_comparison]
      have hfamily : (fun i => (actualLocalValueIso (q i) G.obj).hom
          (actualRestrictionFamily q G.obj d i)) =
          neighborhoodGermFamily (X := TopCat.of (PrimeSpectrum R)) x G.obj
            ((actualGlobalValueIso q hexhaust G.obj).hom d) := by
        funext i
        exact actualRestrictionFamily_germ q hexhaust G.obj d i
      rw [hfamily]
      exact congrFun (congrFun (neighborhood_germs_compatible
        (X := TopCat.of (PrimeSpectrum R)) x G.obj
          ((actualGlobalValueIso q hexhaust G.obj).hom d)) i) j


end
end MathGauge.GP003
