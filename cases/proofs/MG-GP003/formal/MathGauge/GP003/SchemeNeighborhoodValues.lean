import MathGauge.GP003.ActualSemilocalGeometry

/-! Values are presented by actual open-scheme factorizations T → U → X.
Their comparison with image-neighborhood colimits is a theorem, rather than an
identification of a scheme with its point-set image. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry MathGauge.PublicProof.Semilocal

universe u
variable {X T : Scheme.{u}}

def SchemeNeighborhoods (f : T ⟶ X) :=
  {U : X.Opens // ∃ a : T ⟶ U.toScheme, a ≫ U.ι = f}

instance (f : T ⟶ X) : PartialOrder (SchemeNeighborhoods f) :=
  inferInstanceAs (PartialOrder {U : X.Opens // ∃ a : T ⟶ U.toScheme, a ≫ U.ι = f})

theorem factors_open_iff_range (f : T ⟶ X) (U : X.Opens) :
    (∃ a : T ⟶ U.toScheme, a ≫ U.ι = f) ↔ Set.range f ⊆ U := by
  constructor
  · rintro ⟨a,rfl⟩ _ ⟨z,rfl⟩
    exact (a z).2
  · intro h
    have hh : Set.range f ⊆ Set.range U.ι := by simpa only [Scheme.Opens.range_ι] using h
    exact ⟨IsOpenImmersion.lift U.ι f hh,IsOpenImmersion.lift_fac U.ι f hh⟩

/-- All lifts in this indexing category are actual scheme morphisms, uniquely
determined by the structural map. -/
theorem schemeNeighborhood_lift_unique (f : T ⟶ X) (U : SchemeNeighborhoods f)
    (a b : T ⟶ U.1.toScheme) (ha : a ≫ U.1.ι = f) (hb : b ≫ U.1.ι = f) : a = b := by
  apply (cancel_mono U.1.ι).mp
  exact ha.trans hb.symm

def schemeNeighborhoodOrderIso (f : T ⟶ X) :
    SchemeNeighborhoods f ≃o SetNeighborhoods (X := X.carrier) (Set.range f) where
  toFun U := ⟨U.1,(factors_open_iff_range f U.1).mp U.2⟩
  invFun U := ⟨U.1,(factors_open_iff_range f U.1).mpr U.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance schemeNeighborhoodFiltered (f : T ⟶ X) : IsFiltered (SchemeNeighborhoods f)ᵒᵖ :=
  IsFiltered.of_equivalence (schemeNeighborhoodOrderIso f).equivalence.op.symm


def schemeNeighborhoodInclusion (f : T ⟶ X) : SchemeNeighborhoods f ⥤ X.Opens :=
  (show Monotone (fun U : SchemeNeighborhoods f => U.1) from fun _ _ h => h).functor

/-- The value defined by the actual open-neighborhood factorization presentation. -/
def schemeNeighborhoodValue (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} := colimit ((schemeNeighborhoodInclusion f).op ⋙ F)

def schemeNeighborhoodValueIso (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue f F ≅ neighborhood_value F (Set.range f) :=
  asIso (colimit.pre ((neighborhood_inclusion (X := X.carrier) (Set.range f)).op ⋙ F)
    (schemeNeighborhoodOrderIso f).equivalence.functor.op)

@[simp] theorem schemeNeighborhoodValueIso_representative
    (f : T ⟶ X) (F : X.carrier.Presheaf AddCommGrpCat.{u}) (U : SchemeNeighborhoods f) :
    colimit.ι ((schemeNeighborhoodInclusion f).op ⋙ F) (op U) ≫
      (schemeNeighborhoodValueIso f F).hom =
      colimit.ι ((neighborhood_inclusion (X := X.carrier) (Set.range f)).op ⋙ F)
        (op (schemeNeighborhoodOrderIso f U)) :=
  colimit.ι_pre ((neighborhood_inclusion (X := X.carrier) (Set.range f)).op ⋙ F)
    (schemeNeighborhoodOrderIso f).equivalence.functor.op (op U)

/-- Precomposition of genuine neighborhood factorizations by an actual map over X. -/
def schemeNeighborhoodChange {Y : Scheme.{u}} (f : T ⟶ X) (g : Y ⟶ X)
    (k : Y ⟶ T) (hk : k ≫ f = g) : SchemeNeighborhoods f ⥤ SchemeNeighborhoods g :=
  (show Monotone (fun U : SchemeNeighborhoods f =>
    (⟨U.1,by
      obtain ⟨a,ha⟩ := U.2
      exact ⟨k ≫ a, by rw [Category.assoc,ha,hk]⟩⟩ : SchemeNeighborhoods g)) from
    fun _ _ h => h).functor

/-- The actual restriction map on the neighborhood presentation. -/
def schemeNeighborhoodRestriction {Y : Scheme.{u}} (f : T ⟶ X) (g : Y ⟶ X)
    (k : Y ⟶ T) (hk : k ≫ f = g) (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue f F ⟶ schemeNeighborhoodValue g F :=
  colimit.pre ((schemeNeighborhoodInclusion g).op ⋙ F) (schemeNeighborhoodChange f g k hk).op

@[simp] theorem schemeNeighborhoodRestriction_representative {Y : Scheme.{u}}
    (f : T ⟶ X) (g : Y ⟶ X) (k : Y ⟶ T) (hk : k ≫ f = g)
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) (U : SchemeNeighborhoods f) :
    colimit.ι ((schemeNeighborhoodInclusion f).op ⋙ F) (op U) ≫
      schemeNeighborhoodRestriction f g k hk F =
    colimit.ι ((schemeNeighborhoodInclusion g).op ⋙ F)
      (op ((schemeNeighborhoodChange f g k hk).obj U)) :=
  colimit.ι_pre ((schemeNeighborhoodInclusion g).op ⋙ F)
    (schemeNeighborhoodChange f g k hk).op (op U)

/-- A subset of the image determines which actual neighborhood maps occur. -/
theorem schemeNeighborhoodRestriction_comp {Y Z : Scheme.{u}}
    (f : T ⟶ X) (g : Y ⟶ X) (h : Z ⟶ X)
    (k : Y ⟶ T) (hk : k ≫ f = g) (l : Z ⟶ Y) (hl : l ≫ g = h)
    (F : X.carrier.Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodRestriction f g k hk F ≫ schemeNeighborhoodRestriction g h l hl F =
      schemeNeighborhoodRestriction f h (l ≫ k) (by rw [Category.assoc,hk,hl]) F := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec
  simp only [← Category.assoc, schemeNeighborhoodRestriction_representative]
  rfl


variable {R : Type u} [CommRing R]

/-- The problem's finite-point neighborhood convention gives the value of
its actual semilocal scheme through a canonical comparison of presentations. -/
def finitePointSchemeValueIso (sigma : Finset (PrimeSpectrum R)) (hsigma : sigma.Nonempty)
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (semilocalToAmbient sigma) F ≅
      neighborhood_value F (sigma : Set (PrimeSpectrum R)) :=
  schemeNeighborhoodValueIso (semilocalToAmbient sigma) F ≪≫
    (localizationNeighborhoodIso sigma hsigma (semilocalRing sigma) F).symm

theorem actualLocalNeighborhood_iff {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma)) (U : Opens (PrimeSpectrum R)) :
    Set.range (localToAmbient q) ⊆ (U : Set (PrimeSpectrum R)) ↔
      ({PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q} : Set (PrimeSpectrum R)) ⊆ U := by
  rw [localToAmbient_range]
  constructor
  · intro h p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    apply h
    change (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q).asIdeal ≤
      (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q).asIdeal
    exact le_rfl
  · intro h p hp
    exact ((PrimeSpectrum.le_iff_specializes p
      (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q)).mp hp).mem_open U.isOpen
      (h (Set.mem_singleton _))

def actualLocalPoint_mem {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma)) (U : SchemeNeighborhoods (localToAmbient q)) :
    PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q ∈ U.1 :=
  (actualLocalNeighborhood_iff q U.1).mp
    ((factors_open_iff_range (localToAmbient q) U.1).mp U.2) (Set.mem_singleton _)

/-- The actual localization of S at q has the stalk presentation at its
ambient contracted point. No openness of the local scheme is used. -/
def actualLocalValueIso {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (localToAmbient q) F ≅
      F.stalk (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q) :=
  schemeNeighborhoodValueIso (localToAmbient q) F ≪≫
    sameNeighborhoodIso F (actualLocalNeighborhood_iff q) ≪≫ singletonNeighborhoodIso F _

@[simp] theorem actualLocalValueIso_representative {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (U : SchemeNeighborhoods (localToAmbient q)) :
    colimit.ι ((schemeNeighborhoodInclusion (localToAmbient q)).op ⋙ F) (op U) ≫
      (actualLocalValueIso q F).hom =
        F.germ U.1 (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q)
          (actualLocalPoint_mem q U) := by
  dsimp only [actualLocalValueIso, Iso.trans_hom]
  simp only [← Category.assoc, schemeNeighborhoodValueIso_representative,
    sameNeighborhoodIso_representative]
  exact singletonNeighborhoodIso_representative F _ _

/-- The fiber product value is compared through its actual open-scheme
factorizations and the proved cofinal pair-neighborhood presentation. -/
def actualFiberValueIso {sigma : Finset (PrimeSpectrum R)}
    (q r : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    schemeNeighborhoodValue (localFiberToAmbient q r) F ≅
      overlapValue F (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q)
        (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) r) :=
  schemeNeighborhoodValueIso (localFiberToAmbient q r) F ≪≫
    sameNeighborhoodIso F (fun U => by rw [localFiberToAmbient_range]) ≪≫
      (overlapLocalizationIso _ _ F).symm

end
end MathGauge.GP003
