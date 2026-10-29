import MathGauge.GP003.FiniteNeighborhoodDescent
import FinitePrimeLocalization

/-! Actual localization spectra and their neighborhood-colimit values.
The spectrum image is its full set of generalizations, not the finite point set.
The two sets have the same open neighborhoods, which gives the canonical value iso. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
open MathGauge.PublicProof.Semilocal

universe u
variable {X : TopCat.{u}}

/-- The canonical singleton neighborhood value is the actual stalk. -/
def singletonNeighborhoodIso (F : X.Presheaf AddCommGrpCat.{u}) (x : X) :
    neighborhood_value F ({x} : Set X) ≅ F.stalk x :=
  asIso (colimit.pre ((OpenNhds.inclusion x).op ⋙ F)
    (singleton_neighborhood_orderIso x).equivalence.functor.op)

@[simp] theorem singletonNeighborhoodIso_representative
    (F : X.Presheaf AddCommGrpCat.{u}) (x : X) (U : SetNeighborhoods ({x} : Set X)) :
    colimit.ι ((neighborhood_inclusion ({x} : Set X)).op ⋙ F) (op U) ≫
      (singletonNeighborhoodIso F x).hom = F.germ U.1 x (U.2 (Set.mem_singleton x)) := by
  exact colimit.ι_pre ((OpenNhds.inclusion x).op ⋙ F)
    (singleton_neighborhood_orderIso x).equivalence.functor.op (op U)

/-- Equal open-neighborhood conditions identify the actual indexing categories. -/
def sameNeighborhoodOrderIso {s t : Set X}
    (h : ∀ U : Opens X, s ⊆ U ↔ t ⊆ U) : SetNeighborhoods s ≃o SetNeighborhoods t where
  toFun U := ⟨U.1, (h U.1).mp U.2⟩
  invFun U := ⟨U.1, (h U.1).mpr U.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def sameNeighborhoodIso (F : X.Presheaf AddCommGrpCat.{u}) {s t : Set X}
    (h : ∀ U : Opens X, s ⊆ U ↔ t ⊆ U) :
    neighborhood_value F s ≅ neighborhood_value F t :=
  asIso (colimit.pre ((neighborhood_inclusion t).op ⋙ F)
    (sameNeighborhoodOrderIso h).equivalence.functor.op)

@[simp] theorem sameNeighborhoodIso_representative
    (F : X.Presheaf AddCommGrpCat.{u}) {s t : Set X}
    (h : ∀ U : Opens X, s ⊆ U ↔ t ⊆ U) (U : SetNeighborhoods s) :
    colimit.ι ((neighborhood_inclusion s).op ⋙ F) (op U) ≫
      (sameNeighborhoodIso F h).hom =
        colimit.ι ((neighborhood_inclusion t).op ⋙ F)
          (op ((sameNeighborhoodOrderIso h) U)) :=
  colimit.ι_pre ((neighborhood_inclusion t).op ⋙ F)
    (sameNeighborhoodOrderIso h).equivalence.functor.op (op U)

variable {R : Type u} [CommRing R]

/-- Opens contain the actual localized spectrum image exactly when they contain
all selected primes. No selected prime need be ambient closed. -/
theorem localization_image_neighborhood_iff (sigma : Finset (PrimeSpectrum R))
    (hsigma : sigma.Nonempty) (L : Type u) [CommRing L] [Algebra R L]
    [IsLocalization (outside_primes sigma) L] (U : Opens (PrimeSpectrum R)) :
    (sigma : Set (PrimeSpectrum R)) ⊆ U ↔
      Set.range (PrimeSpectrum.comap (algebraMap R L)) ⊆ U := by
  constructor
  · intro h p hp
    obtain ⟨q,hq,hpq⟩ := (localization_spectrum_image_iff sigma hsigma L p).mp hp
    exact ((PrimeSpectrum.le_iff_specializes p q).mp hpq).mem_open U.isOpen (h hq)
  · intro h p hp
    exact h ((localization_spectrum_image_iff sigma hsigma L p).mpr ⟨p,hp,le_rfl⟩)

def localizationNeighborhoodIso (sigma : Finset (PrimeSpectrum R))
    (hsigma : sigma.Nonempty) (L : Type u) [CommRing L] [Algebra R L]
    [IsLocalization (outside_primes sigma) L]
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    neighborhood_value F (sigma : Set (PrimeSpectrum R)) ≅
      neighborhood_value F (Set.range (PrimeSpectrum.comap (algebraMap R L))) :=
  sameNeighborhoodIso F (localization_image_neighborhood_iff sigma hsigma L)

/-- The genuine prime-localization image is the set of all generalizations. -/
theorem prime_localization_image (p : PrimeSpectrum R) :
    Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) =
      {q | q.asIdeal ≤ p.asIdeal} := by
  rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl]
  ext q
  change Disjoint (p.asIdeal.primeCompl : Set R) (q.asIdeal : Set R) ↔ q.asIdeal ≤ p.asIdeal
  rw [Set.disjoint_left]
  constructor
  · intro h a ha
    by_contra hn
    exact h hn ha
  · intro h a hn ha
    exact hn (h ha)

/-- A single actual local scheme has the same ambient open neighborhoods as its point. -/
theorem prime_localization_neighborhood_iff (p : PrimeSpectrum R)
    (U : Opens (PrimeSpectrum R)) :
    ({p} : Set (PrimeSpectrum R)) ⊆ U ↔
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) ⊆ U := by
  rw [prime_localization_image]
  constructor
  · intro h q hq
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hq).mem_open U.isOpen
      (h (Set.mem_singleton p))
  · intro h q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact h (show q.asIdeal ≤ q.asIdeal from le_rfl)

def primeLocalizationValueIso (p : PrimeSpectrum R)
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}) :
    neighborhood_value F
      (Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)))) ≅
        F.stalk p :=
  (sameNeighborhoodIso F (prime_localization_neighborhood_iff p)).symm ≪≫
    singletonNeighborhoodIso F p

end
end MathGauge.GP003
