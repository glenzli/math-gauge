import MathGauge.GP003.PairLocalizationNeighborhoods
import AffineScheme
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! The actual semilocal scheme, its actual local schemes, and their scheme
fiber products. These are not replaced by formal certificates or point sets.
The ambient-neighborhood presentations are connected by explicit algebra and
scheme isomorphisms and by cofinality proved in the preceding modules. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry MathGauge.PublicProof.Semilocal
open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R]

abbrev semilocalRing (sigma : Finset (PrimeSpectrum R)) := finite_prime_localization sigma

def semilocalToAmbient (sigma : Finset (PrimeSpectrum R)) :
    finite_point_scheme sigma ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (semilocalRing sigma)))

def localScheme {sigma : Finset (PrimeSpectrum R)} (q : PrimeSpectrum (semilocalRing sigma)) :
    Scheme := Spec (CommRingCat.of (Localization.AtPrime q.asIdeal))

def localToSemilocal {sigma : Finset (PrimeSpectrum R)} (q : PrimeSpectrum (semilocalRing sigma)) :
    localScheme q ⟶ finite_point_scheme sigma :=
  Spec.map (CommRingCat.ofHom (algebraMap (semilocalRing sigma) (Localization.AtPrime q.asIdeal)))

def localToAmbient {sigma : Finset (PrimeSpectrum R)} (q : PrimeSpectrum (semilocalRing sigma)) :
    localScheme q ⟶ Spec (CommRingCat.of R) := localToSemilocal q ≫ semilocalToAmbient sigma

/-- This actual local ring of S is canonically the localization of the ambient
ring at the contracted prime. The algebra equivalence commutes with the base map. -/
def localRingAmbientEquiv {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma)) :
    Localization.AtPrime (q.asIdeal.comap (algebraMap R (semilocalRing sigma))) ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (outside_primes sigma) q.asIdeal

@[simp] theorem localRingAmbientEquiv_algebraMap {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma)) (r : R) :
    localRingAmbientEquiv q (algebraMap R _ r) = algebraMap R _ r :=
  (localRingAmbientEquiv q).commutes r

theorem localToAmbient_eq_SpecMap {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma)) :
    localToAmbient q = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime q.asIdeal))) := by
  rw [localToAmbient, localToSemilocal, semilocalToAmbient, ← Spec.map_comp]
  congr 1

/-- The actual local scheme's ambient image consists of all generalizations
of the contracted point, even when that point is not ambient closed. -/
theorem localToAmbient_range {sigma : Finset (PrimeSpectrum R)}
    (q : PrimeSpectrum (semilocalRing sigma)) :
    Set.range (localToAmbient q) =
      {p | p.asIdeal ≤ (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q).asIdeal} := by
  rw [localToAmbient_eq_SpecMap]
  change Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime q.asIdeal))) = _
  rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime q.asIdeal)
    (q.asIdeal.comap (algebraMap R (semilocalRing sigma))).primeCompl]
  ext p
  change Disjoint ((q.asIdeal.comap (algebraMap R (semilocalRing sigma))).primeCompl : Set R)
    (p.asIdeal : Set R) ↔ p.asIdeal ≤ _
  rw [Set.disjoint_left]
  constructor
  · intro h a ha
    by_contra hn
    exact h hn ha
  · intro h a hn ha
    exact hn (h ha)

def localFiberProduct {sigma : Finset (PrimeSpectrum R)}
    (q r : PrimeSpectrum (semilocalRing sigma)) : Scheme :=
  pullback (localToSemilocal q) (localToSemilocal r)

def localFiberToAmbient {sigma : Finset (PrimeSpectrum R)}
    (q r : PrimeSpectrum (semilocalRing sigma)) :
    localFiberProduct q r ⟶ Spec (CommRingCat.of R) :=
  pullback.fst (localToSemilocal q) (localToSemilocal r) ≫ localToAmbient q

/-- A structure-preserving scheme isomorphism to the actual tensor product,
not just an equality of underlying point sets. -/
def localFiberTensorIso {sigma : Finset (PrimeSpectrum R)}
    (q r : PrimeSpectrum (semilocalRing sigma)) :
    localFiberProduct q r ≅ Spec (CommRingCat.of
      (Localization.AtPrime q.asIdeal ⊗[semilocalRing sigma] Localization.AtPrime r.asIdeal)) :=
  AlgebraicGeometry.pullbackSpecIso (semilocalRing sigma)
    (Localization.AtPrime q.asIdeal) (Localization.AtPrime r.asIdeal)

/-- The projection of the tensor presentation is the actual first ring map. -/
theorem localFiberTensorIso_fst {sigma : Finset (PrimeSpectrum R)}
    (q r : PrimeSpectrum (semilocalRing sigma)) :
    (localFiberTensorIso q r).inv ≫ pullback.fst (localToSemilocal q) (localToSemilocal r) =
      Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[semilocalRing sigma] Localization.AtPrime r.asIdeal))) :=
  AlgebraicGeometry.pullbackSpecIso_inv_fst' _ _ _

/-- Scheme pullback, followed by the injective localization map, has exactly
the intersection of the two ambient local-spectrum images. -/
theorem localFiberToAmbient_range {sigma : Finset (PrimeSpectrum R)}
    (q r : PrimeSpectrum (semilocalRing sigma)) :
    Set.range (localFiberToAmbient q r) =
      pairLocalImage (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) q)
        (PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) r) := by
  have hi : Function.Injective (semilocalToAmbient sigma) :=
    PrimeSpectrum.localization_comap_injective (semilocalRing sigma) (outside_primes sigma)
  have hh := Scheme.Pullback.range_fst_comp (localToSemilocal q) (localToSemilocal r)
  have hrange : Set.range (localFiberToAmbient q r) =
      Set.range (localToAmbient q) ∩ Set.range (localToAmbient r) := by
    change Set.range ((semilocalToAmbient sigma) ∘
      (pullback.fst (localToSemilocal q) (localToSemilocal r) ≫ localToSemilocal q)) = _
    rw [Set.range_comp, hh, Set.image_inter hi]
    rw [← Set.range_comp, ← Set.range_comp]
    rfl
  rw [hrange, localToAmbient_range, localToAmbient_range, pairLocalImage_eq]
  rfl

/-- Every ambient open containing the images of all closed points of the
actual S contains all of S. This proves the global neighborhood identification. -/
theorem closed_point_images_neighborhood_iff (sigma : Finset (PrimeSpectrum R))
    {ι : Type u} (q : ι → PrimeSpectrum (semilocalRing sigma))
    (hexhaust : ∀ z : PrimeSpectrum (semilocalRing sigma),
      IsClosed ({z} : Set (PrimeSpectrum (semilocalRing sigma))) → z ∈ Set.range q)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Set.range (fun i => semilocalToAmbient sigma (q i)) ⊆ U ↔
      Set.range (semilocalToAmbient sigma) ⊆ U := by
  constructor
  · intro h z hz
    obtain ⟨z,rfl⟩ := hz
    let V : Opens (PrimeSpectrum (semilocalRing sigma)) :=
      (Opens.map (semilocalToAmbient sigma).base).obj U
    have hV : V = ⊤ := open_eq_top_of_contains_closed V (by
      intro w hw
      obtain ⟨i,rfl⟩ := hexhaust w hw
      exact h ⟨i,rfl⟩)
    have hz : z ∈ V := by rw [hV]; trivial
    exact hz
  · intro h z hz
    obtain ⟨i,rfl⟩ := hz
    exact h ⟨q i,rfl⟩

end
end MathGauge.GP003
