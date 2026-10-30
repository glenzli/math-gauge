import MathGauge.GP003.AffineRestriction

/-! The S2 comparison in the original ambient scheme. All hypotheses concern
the original presheaf, original map, and actual neighborhood values. The affine
chart is only a presentation of the given semilocalization. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open MathGauge.PublicProof.Semilocal

universe u
variable {X Y T : Scheme.{u}} (f : T ⟶ Y) (j : Y ⟶ X) [IsOpenImmersion j]

theorem ambientMap_injective_iff
    {H G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : H ⟶ G) :
    Function.Injective (schemeNeighborhoodMap f (ambientRestrictionMap j η)) ↔
      Function.Injective (schemeNeighborhoodMap (f ≫ j) η) := by
  have hH := ConcreteCategory.bijective_of_isIso (ambientNeighborhoodIso f j H).hom
  have hG := ConcreteCategory.bijective_of_isIso (ambientNeighborhoodIso f j G).hom
  have hc a := ConcreteCategory.congr_hom (ambientNeighborhoodIso_map f j η) a
  constructor
  · intro h a b hab
    obtain ⟨a',rfl⟩ := hH.2 a
    obtain ⟨b',rfl⟩ := hH.2 b
    congr 1
    apply h
    apply hG.1
    exact (hc a').trans (hab.trans (hc b').symm)
  · intro h a b hab
    apply hH.1
    apply h
    exact (hc a).symm.trans ((congrArg (ambientNeighborhoodIso f j G).hom hab).trans (hc b))

theorem ambientMap_surjective_iff
    {H G : X.carrier.Presheaf AddCommGrpCat.{u}} (η : H ⟶ G) :
    Function.Surjective (schemeNeighborhoodMap f (ambientRestrictionMap j η)) ↔
      Function.Surjective (schemeNeighborhoodMap (f ≫ j) η) := by
  have hH := ConcreteCategory.bijective_of_isIso (ambientNeighborhoodIso f j H).hom
  have hG := ConcreteCategory.bijective_of_isIso (ambientNeighborhoodIso f j G).hom
  have hc a := ConcreteCategory.congr_hom (ambientNeighborhoodIso_map f j η) a
  constructor
  · intro h b
    obtain ⟨b',rfl⟩ := hG.2 b
    obtain ⟨a,ha⟩ := h b'
    exact ⟨(ambientNeighborhoodIso f j H).hom a,
      (hc a).symm.trans (congrArg (ambientNeighborhoodIso f j G).hom ha)⟩
  · intro h b
    obtain ⟨a,ha⟩ := h ((ambientNeighborhoodIso f j G).hom b)
    obtain ⟨a',rfl⟩ := hH.2 a
    exact ⟨a',hG.1 ((hc a').trans ha)⟩

/-- The same comparison on an actual open subscheme, with the associativity
identification of its structure map made explicit. -/
def ambientOpenValueIso (H : X.carrier.Presheaf AddCommGrpCat.{u}) (U : T.Opens) :
    schemeOpenValue f (ambientRestriction j H) U ≅ schemeOpenValue (f ≫ j) H U := by
  simpa only [schemeOpenValue,schemeOpenToAmbient,Category.assoc] using
    ambientNeighborhoodIso (schemeOpenToAmbient f U) j H

theorem ambientOpenValueIso_restriction
    (H : X.carrier.Presheaf AddCommGrpCat.{u}) (U : T.Opens) :
    schemeOpenRestriction f (ambientRestriction j H) U ≫ (ambientOpenValueIso f j H U).hom =
      (ambientNeighborhoodIso f j H).hom ≫ schemeOpenRestriction (f ≫ j) H U := by
  convert ambientNeighborhoodIso_restriction f j (schemeOpenToAmbient f U) U.ι rfl H using 1 <;>
    simp [ambientOpenValueIso,schemeOpenRestriction,schemeOpenValue,schemeOpenToAmbient,Category.assoc] <;>
    congr 1 <;> simp only [Category.assoc]

theorem ambientOpenValueIso_restrictionLE
    (H : X.carrier.Presheaf AddCommGrpCat.{u}) {U V : T.Opens} (hVU : V ≤ U) :
    schemeOpenRestrictionLE f (ambientRestriction j H) hVU ≫ (ambientOpenValueIso f j H V).hom =
      (ambientOpenValueIso f j H U).hom ≫ schemeOpenRestrictionLE (f ≫ j) H hVU := by
  convert ambientNeighborhoodIso_restriction (schemeOpenToAmbient f U) j
      (schemeOpenToAmbient f V) (T.homOfLE hVU)
      (by unfold schemeOpenToAmbient; rw [← Category.assoc,T.homOfLE_ι]) H using 1 <;>
    simp [ambientOpenValueIso,schemeOpenRestrictionLE,schemeOpenValue,schemeOpenToAmbient,Category.assoc] <;>
    congr 1 <;> simp only [Category.assoc]

/-- Exactness is transported along the actual global, open and overlap
isomorphisms. This does not assert exactness for an unshrunk cover. -/
theorem ambientTwoOpen_exact_iff
    (H : X.carrier.Presheaf AddCommGrpCat.{u}) (U V : T.Opens) :
    Function.Exact (schemeTwoOpenRestriction f (ambientRestriction j H) U V)
      (schemeTwoOpenDifference f (ambientRestriction j H) U V) ↔
    Function.Exact (schemeTwoOpenRestriction (f ≫ j) H U V)
      (schemeTwoOpenDifference (f ≫ j) H U V) := by
  let e := (ambientNeighborhoodIso f j H).hom.hom
  let eU := (ambientOpenValueIso f j H U).hom.hom
  let eV := (ambientOpenValueIso f j H V).hom.hom
  let eI := (ambientOpenValueIso f j H (U ⊓ V)).hom.hom
  let eUV := eU.prodMap eV
  apply AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    _ _ _ _ e eUV eI
  · apply AddMonoidHom.ext
    intro a
    apply Prod.ext
    · exact (ConcreteCategory.congr_hom (ambientOpenValueIso_restriction f j H U) a).symm
    · exact (ConcreteCategory.congr_hom (ambientOpenValueIso_restriction f j H V) a).symm
  · ext a
    change _ - _ = eI (_ - _)
    rw [map_sub]
    congr 1
    · exact (ConcreteCategory.congr_hom (ambientOpenValueIso_restrictionLE f j H
        (show U ⊓ V ≤ U from inf_le_left)) a.1).symm
    · exact (ConcreteCategory.congr_hom (ambientOpenValueIso_restrictionLE f j H
        (show U ⊓ V ≤ V from inf_le_right)) a.2).symm
  · exact (ConcreteCategory.bijective_of_isIso (ambientNeighborhoodIso f j H).hom).2
  · have hU := ConcreteCategory.bijective_of_isIso (ambientOpenValueIso f j H U).hom
    have hV := ConcreteCategory.bijective_of_isIso (ambientOpenValueIso f j H V).hom
    constructor
    · intro a b hab
      exact Prod.ext (hU.1 (congrArg Prod.fst hab)) (hV.1 (congrArg Prod.snd hab))
    · rintro ⟨a,b⟩
      obtain ⟨a',rfl⟩ := hU.2 a
      obtain ⟨b',rfl⟩ := hV.2 b
      exact ⟨(a',b'),rfl⟩
  · exact (ConcreteCategory.bijective_of_isIso (ambientOpenValueIso f j H (U ⊓ V)).hom).1

variable {R : Type u} [CommRing R] {sigma : Finset (PrimeSpectrum R)}

/-- S2 for the original ambient scheme and original map, for every affine
presentation of its semilocalization. Hypotheses are precisely the given global
and overlap injections, local isomorphisms (only their surjectivity is used),
and successful point-preserving shrinking. No sheaf property of H, overlap
surjectivity, or exactness before shrinking is imposed. -/
theorem general_two_closed_comparison
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q r : PrimeSpectrum (semilocalRing sigma)) (hqr : q ≠ r)
    (hqclosed : IsClosed ({q} : Set (PrimeSpectrum (semilocalRing sigma))))
    (hrclosed : IsClosed ({r} : Set (PrimeSpectrum (semilocalRing sigma))))
    (hexhaust : ∀ z : PrimeSpectrum (semilocalRing sigma),
      IsClosed ({z} : Set (PrimeSpectrum (semilocalRing sigma))) → z = q ∨ z = r)
    (H : X.carrier.Presheaf AddCommGrpCat.{u})
    (G : TopCat.Sheaf AddCommGrpCat.{u} X.carrier) (η : H ⟶ G.obj)
    (hglobalmono : Function.Injective (schemeNeighborhoodMap (semilocalToAmbient sigma ≫ j) η))
    (hmono : ∀ U : (finite_point_scheme sigma).Opens,
      Function.Injective (schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma ≫ j) U) η))
    (hqiso : Function.Surjective (schemeNeighborhoodMap (localToAmbient q ≫ j) η))
    (hriso : Function.Surjective (schemeNeighborhoodMap (localToAmbient r ≫ j) η))
    (hrefine : ∀ U₀ V : (finite_point_scheme sigma).Opens,
      Separates ({q} : Set (PrimeSpectrum (semilocalRing sigma))) {r} U₀ V → U₀ ⊔ V = ⊤ →
      ∃ U : (finite_point_scheme sigma).Opens, U ≤ U₀ ∧ U ⊔ V = ⊤ ∧
        Function.Exact (schemeTwoOpenRestriction (semilocalToAmbient sigma ≫ j) H U V)
          (schemeTwoOpenDifference (semilocalToAmbient sigma ≫ j) H U V)) :
    Function.Bijective (schemeNeighborhoodMap (semilocalToAmbient sigma ≫ j) η) := by
  have ha := actual_affine_two_closed_comparison q r hqr hqclosed hrclosed hexhaust
    (ambientRestriction j H) (ambientRestrictionSheaf j G) (ambientRestrictionMap j η)
    ((ambientMap_injective_iff (semilocalToAmbient sigma) j η).mpr hglobalmono)
    (fun U => (ambientMap_injective_iff (schemeOpenToAmbient (semilocalToAmbient sigma) U) j η).mpr
      (by
        have he : schemeOpenToAmbient (semilocalToAmbient sigma) U ≫ j =
            schemeOpenToAmbient (semilocalToAmbient sigma ≫ j) U := by
          unfold schemeOpenToAmbient
          exact Category.assoc _ _ _
        rw [he]
        exact hmono U))
    ((ambientMap_surjective_iff (localToAmbient q) j η).mpr hqiso)
    ((ambientMap_surjective_iff (localToAmbient r) j η).mpr hriso)
    (by
      intro U₀ V hs hcover
      obtain ⟨U,hU,hUV,he⟩ := hrefine U₀ V hs hcover
      exact ⟨U,hU,hUV,(ambientTwoOpen_exact_iff (semilocalToAmbient sigma) j H U V).mpr he⟩)
  exact ⟨hglobalmono,(ambientMap_surjective_iff (semilocalToAmbient sigma) j η).mp ha.2⟩

end
end MathGauge.GP003
