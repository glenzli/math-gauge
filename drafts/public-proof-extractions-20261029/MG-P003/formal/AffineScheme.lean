import NeighborhoodRefinement
import Mathlib.AlgebraicGeometry.Scheme

/-!
The localization ring is turned into an actual Mathlib scheme, with its actual
structure sheaf. This does not yet construct the smooth/quasi-projective ambient
category, finite correspondences, or its presheaves with transfers.
-/

namespace MathGauge.PublicProof.Semilocal

noncomputable section

open AlgebraicGeometry

variable {R : Type*} [CommRing R]

/-- The actual affine scheme Spec of the task's finite-prime localization. -/
def finite_point_scheme (sigma : Finset (PrimeSpectrum R)) : Scheme :=
  Spec (CommRingCat.of (finite_prime_localization sigma))

/-- The localization scheme has finitely many closed points. -/
theorem finite_point_scheme_finite_closed (sigma : Finset (PrimeSpectrum R))
    (hsigma : sigma.Nonempty) :
    Set.Finite {x : finite_point_scheme sigma |
      IsClosed ({x} : Set (finite_point_scheme sigma))} := by
  exact finite_localization_closed_points sigma hsigma (finite_prime_localization sigma)

/-- The finite closed-point set is nonempty; no ambient closed-point assumption is used. -/
theorem finite_point_scheme_nonempty_closed (sigma : Finset (PrimeSpectrum R))
    (hsigma : sigma.Nonempty) :
    Set.Nonempty {x : finite_point_scheme sigma |
      IsClosed ({x} : Set (finite_point_scheme sigma))} := by
  exact nonempty_localization_closed_points sigma hsigma (finite_prime_localization sigma)

/-- The actual scheme's Zariski opens obey the closed-point cover criterion. -/
theorem finite_point_scheme_open_eq_top (sigma : Finset (PrimeSpectrum R))
    (U : (finite_point_scheme sigma).Opens)
    (hU : ∀ x : finite_point_scheme sigma,
      IsClosed ({x} : Set (finite_point_scheme sigma)) → x ∈ U) : U = ⊤ := by
  exact open_eq_top_of_contains_closed U hU

end

end MathGauge.PublicProof.Semilocal
