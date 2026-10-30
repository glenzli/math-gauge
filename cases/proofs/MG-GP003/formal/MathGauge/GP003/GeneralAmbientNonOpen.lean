import MathGauge.GP003.GeneralAmbient
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Polynomial.Basic

/-! A concrete non-open local scheme in a semilocalization of the smooth
affine plane over Q. This verifies the explicit warning in S1 by an example,
not merely by omitting an openness assumption from the equalizer theorem. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace AlgebraicGeometry
open MathGauge.PublicProof.Semilocal

universe u

theorem local_image_not_open_of_prime_family
    {R : Type u} [CommRing R] (sigma : Finset (PrimeSpectrum R)) (hsigma : sigma.Nonempty)
    (q : PrimeSpectrum (semilocalRing sigma)) {ι : Type*} (p : ι → PrimeSpectrum R)
    (hbelow : ∀ i, ∃ s ∈ sigma, (p i).asIdeal ≤ s.asIdeal)
    (hnotbelow : ∀ i, ¬ (p i).asIdeal ≤ (ambientPoint q).asIdeal)
    (hzero : ∀ a : R, (∀ i, a ∈ (p i).asIdeal) → a = 0) :
    ¬ IsOpen (Set.range (localToSemilocal q)) := by
  intro hopen
  have hemb := PrimeSpectrum.localization_comap_isEmbedding
    (semilocalRing sigma) (outside_primes sigma)
  obtain ⟨U,hU,hpre⟩ := hemb.isInducing.isOpen_iff.mp hopen
  have hq : q ∈ Set.range (localToSemilocal q) := by
    change q ∈ Set.range (PrimeSpectrum.comap (algebraMap (semilocalRing sigma)
      (Localization.AtPrime q.asIdeal)))
    rw [prime_localization_image]
    exact (show q.asIdeal ≤ q.asIdeal from le_rfl)
  have hqp : ambientPoint q ∈ U := by
    have := hq
    rw [← hpre] at this
    exact this
  obtain ⟨B,⟨a,rfl⟩,ha,hBU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU _ hqp
  have haz : a = 0 := hzero a (by
    intro i
    by_contra hn
    obtain ⟨r,hr⟩ := (localization_spectrum_image_iff sigma hsigma
      (semilocalRing sigma) (p i)).mpr (hbelow i)
    have hrU : ambientPoint r ∈ U := by
      change PrimeSpectrum.comap (algebraMap R (semilocalRing sigma)) r ∈ U
      rw [hr]
      exact hBU hn
    have hrimage : r ∈ Set.range (localToSemilocal q) := by
      rw [← hpre]
      exact hrU
    obtain ⟨t,ht⟩ := hrimage
    have himage : p i ∈ Set.range (localToAmbient q) := by
      refine ⟨t,?_⟩
      change semilocalToAmbient sigma (localToSemilocal q t) = _
      rw [ht]
      exact hr
    rw [localToAmbient_range] at himage
    exact hnotbelow i himage)
  exact ha (haz ▸ (ambientPoint q).asIdeal.zero_mem)

namespace NonOpenExample
open Polynomial

abbrev Plane := Polynomial (Polynomial ℚ)

def pointEval (b : ℚ) : Plane →+* ℚ :=
  (Polynomial.evalRingHom b).comp (Polynomial.mapRingHom (Polynomial.evalRingHom 0))

def point (b : ℚ) : PrimeSpectrum Plane :=
  ⟨RingHom.ker (pointEval b), RingHom.ker_isPrime (pointEval b)⟩

def lineEval (a : ℚ) : Plane →+* Polynomial ℚ :=
  Polynomial.evalRingHom (Polynomial.C a * Polynomial.X)

def line (a : ℚ) : PrimeSpectrum Plane :=
  ⟨RingHom.ker (lineEval a), RingHom.ker_isPrime (lineEval a)⟩

theorem pointEval_surjective (b : ℚ) : Function.Surjective (pointEval b) := by
  intro r
  exact ⟨Polynomial.C (Polynomial.C r),by simp [pointEval]⟩

theorem point_maximal (b : ℚ) : (point b).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (pointEval_surjective b)

theorem lineEval_eval_zero (a : ℚ) (f : Plane) :
    Polynomial.eval 0 (lineEval a f) = pointEval 0 f := by
  change Polynomial.eval 0 (Polynomial.eval (Polynomial.C a * Polynomial.X) f) =
    Polynomial.eval 0 (Polynomial.map (Polynomial.evalRingHom 0) f)
  rw [Polynomial.eval_map]
  change (Polynomial.evalRingHom 0) (Polynomial.eval (Polynomial.C a * Polynomial.X) f) = _
  rw [← Polynomial.eval₂_at_apply]
  simp

theorem line_below_origin (a : ℚ) : (line a).asIdeal ≤ (point 0).asIdeal := by
  intro f hf
  change pointEval 0 f = 0
  rw [← lineEval_eval_zero a f]
  change lineEval a f = 0 at hf
  rw [hf,Polynomial.eval_zero]

theorem line_not_below_one (a : ℚ) : ¬ (line a).asIdeal ≤ (point 1).asIdeal := by
  intro h
  have hz : Polynomial.X - Polynomial.C (Polynomial.C a * Polynomial.X) ∈ (line a).asIdeal := by
    change lineEval a _ = 0
    simp [lineEval]
  have hh := h hz
  change pointEval 1 _ = 0 at hh
  simp [pointEval] at hh

theorem lines_detect_zero (f : Plane) (hf : ∀ a : ℚ, f ∈ (line a).asIdeal) : f = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Function.Injective (fun a : ℚ => Polynomial.C a * Polynomial.X) := by
    intro a b hab
    have hh := congrArg (fun p : Polynomial ℚ => p.coeff 1) hab
    simpa using hh
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨a,rfl⟩
  exact hf a

local instance : DecidableEq (PrimeSpectrum Plane) := Classical.decEq _

def selected : Finset (PrimeSpectrum Plane) := {point 0,point 1}

theorem selected_nonempty : selected.Nonempty := by
  exact ⟨point 0,by simp [selected]⟩

theorem exists_point_over_one :
    ∃ q : PrimeSpectrum (semilocalRing selected), ambientPoint q = point 1 :=
  (localization_spectrum_image_iff selected selected_nonempty
    (semilocalRing selected) (point 1)).mpr ⟨point 1,by simp [selected],le_rfl⟩

def closedPoint : PrimeSpectrum (semilocalRing selected) := exists_point_over_one.choose

theorem closedPoint_contract : ambientPoint closedPoint = point 1 :=
  exists_point_over_one.choose_spec

theorem closedPoint_closed :
    IsClosed ({closedPoint} : Set (PrimeSpectrum (semilocalRing selected))) := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  have hm : (Ideal.map (algebraMap Plane (semilocalRing selected)) (point 1).asIdeal).IsMaximal :=
    (maximal_map_selected_iff selected selected_nonempty (semilocalRing selected)
      (point 1) (by simp [selected])).mpr (by
        intro p _ hp
        exact PrimeSpectrum.ext ((point_maximal 1).eq_of_le p.isPrime.ne_top hp))
  have hc : (point 1).asIdeal = Ideal.comap (algebraMap Plane (semilocalRing selected))
      closedPoint.asIdeal := (congrArg PrimeSpectrum.asIdeal closedPoint_contract).symm
  rw [hc,IsLocalization.map_comap (outside_primes selected) (semilocalRing selected)] at hm
  exact hm

/-- A closed point of this genuine finite-point semilocalization whose local
scheme has non-open image. Both selected ambient points are rational points
of the affine plane; no non-noetherian or non-smooth counterexample is used. -/
theorem closedPoint_local_image_not_open :
    ¬ IsOpen (Set.range (localToSemilocal closedPoint)) := by
  apply local_image_not_open_of_prime_family selected selected_nonempty closedPoint line
  · intro a
    exact ⟨point 0,by simp [selected],line_below_origin a⟩
  · intro a
    rw [closedPoint_contract]
    exact line_not_below_one a
  · exact lines_detect_zero

theorem closedPoint_local_not_open_immersion :
    ¬ IsOpenImmersion (localToSemilocal closedPoint) := by
  intro h
  letI := h
  exact closedPoint_local_image_not_open
    (IsOpenImmersion.isOpen_range (localToSemilocal closedPoint))

def affinePlane : Scheme := Spec (CommRingCat.of Plane)

def affinePlaneProjection : affinePlane ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ Plane))

theorem affinePlane_affine : IsAffine affinePlane := by
  dsimp [affinePlane]
  infer_instance

theorem affinePlane_integral : IsIntegral affinePlane := by
  dsimp [affinePlane]
  infer_instance

theorem affinePlane_smooth : Smooth affinePlaneProjection := by
  letI : Algebra.Smooth ℚ (Polynomial ℚ) := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Smooth (Polynomial ℚ) Plane := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Smooth ℚ Plane := Algebra.Smooth.comp ℚ (Polynomial ℚ) Plane
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

end NonOpenExample
end
end MathGauge.GP003
