import MathGauge.GP003.OpenNeighborhoods
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Polynomial.Basic

namespace MathGauge.GP003
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MathGauge.PublicProof.Semilocal

universe u
variable (k : Type u) [Field k]

def affineLine : Scheme := Spec (CommRingCat.of (Polynomial k))

def affineLineProjection : affineLine k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))

theorem affineLine_integral : IsIntegral (affineLine k) := by
  dsimp [affineLine]
  infer_instance

theorem affineLine_affine : IsAffine (affineLine k) := by
  dsimp [affineLine]
  infer_instance

theorem affineLine_smooth : Smooth (affineLineProjection k) := by
  letI : Algebra.Smooth k (Polynomial k) := ⟨inferInstance, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

def origin : affineLine k :=
  PrimeSpectrum.comap (Polynomial.evalRingHom (0 : k)) ⟨⊥, Ideal.isPrime_bot⟩

def puncturedLine : Opens (affineLine k) := PrimeSpectrum.basicOpen Polynomial.X

theorem origin_not_mem_puncturedLine : origin k ∉ puncturedLine k := by
  change ¬ (Polynomial.X ∉ Ideal.comap (Polynomial.evalRingHom (0 : k)) ⊥)
  simp

theorem puncturedLine_nonempty : (puncturedLine k : Set (affineLine k)).Nonempty := by
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  change Polynomial.X ∉ (⊥ : Ideal (Polynomial k))
  simpa using (Polynomial.X_ne_zero : (Polynomial.X : Polynomial k) ≠ 0)

theorem puncturedLine_dense : Dense (puncturedLine k : Set (affineLine k)) := by
  letI := affineLine_integral k
  exact (puncturedLine k).isOpen.dense (puncturedLine_nonempty k)

theorem no_neighborhood_inside_puncturedLine :
    ¬ ∃ U : Opens (affineLine k), ({origin k} : Set (affineLine k)) ⊆ U ∧
      U ≤ puncturedLine k := by
  rintro ⟨U, hs, hU⟩
  exact origin_not_mem_puncturedLine k (hU (hs (Set.mem_singleton _)))

theorem restricted_neighborhoods_empty :
    IsEmpty (RestrictedNeighborhoods (X := (affineLine k).toTopCat)
      ({origin k} : Set (affineLine k)) (puncturedLine k)) :=
  ⟨fun U => no_neighborhood_inside_puncturedLine k ⟨U.1.1, U.1.2, U.2⟩⟩

theorem dense_open_not_final :
    ¬ (restrictedInclusion (X := (affineLine k).toTopCat)
      ({origin k} : Set (affineLine k)) (puncturedLine k)).op.Final := by
  intro h
  letI := h
  let s : Set (affineLine k) := {origin k}
  let U : SetNeighborhoods (X := (affineLine k).toTopCat) s :=
    ⟨⊤, fun _ _ => trivial⟩
  haveI : (restrictedInclusion (X := (affineLine k).toTopCat) s (puncturedLine k)).op.Final := h
  obtain ⟨a⟩ := (h.out (op U)).is_nonempty
  exact (restricted_neighborhoods_empty k).false a.right.unop

end
end MathGauge.GP003
