import QuadraticConjugates

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace MathGauge.MatrixQuadratics
open MathGauge.QuadraticPotentials MathGauge.QuadraticConjugates
variable {d : ℕ}
abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)

def operator (Q : Matrix (Fin d) (Fin d) ℝ) : V d →L[ℝ] V d := Q.toEuclideanLin.toContinuousLinearMap

@[simp] theorem operator_coordinates (Q : Matrix (Fin d) (Fin d) ℝ) (x : V d) :
    (operator Q x).ofLp=Q.mulVec x.ofLp := rfl

theorem operator_positive (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) :
    (operator Q).IsPositive :=
  (LinearMap.isPositive_toContinuousLinearMap_iff _).mpr (Matrix.isPositive_toEuclideanLin_iff.mpr hQ)

theorem energy_coordinates (Q : Matrix (Fin d) (Fin d) ℝ) (x : V d) :
    inner ℝ (operator Q x) x=x.ofLp ⬝ᵥ Q.mulVec x.ofLp := by
  have h := EuclideanSpace.inner_eq_star_dotProduct (operator Q x) x
  simpa only [star_trivial,operator_coordinates] using h

theorem operator_positive_definite (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) :
    ∀ x : V d,x≠0 → 0 < inner ℝ (operator Q x) x := by
  intro x hx
  rw [energy_coordinates]
  simpa using hQ.dotProduct_mulVec_pos (show x.ofLp≠0 by simpa using hx)

theorem quadratic_coordinates (Q : Matrix (Fin d) (Fin d) ℝ) (b x : V d) :
    quad (operator Q) b x=(x.ofLp ⬝ᵥ Q.mulVec x.ofLp)/2+b.ofLp ⬝ᵥ x.ofLp := by
  rw [quad,energy_coordinates]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

theorem gradient_coordinates (Q : Matrix (Fin d) (Fin d) ℝ) (b x z : V d) :
    grad (operator Q) b x z=(Q.mulVec x.ofLp+b.ofLp) ⬝ᵥ z.ofLp := by
  change inner ℝ (operator Q x+b) z=_
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- The hypotheses for all general operator theorems are obtained from the
original positive-definite matrix, rather than supplied as extra certificates. -/
theorem matrix_data (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) :
    (operator Q).IsPositive ∧ ∀ x : V d,x≠0 → 0 < inner ℝ (operator Q x) x :=
  ⟨operator_positive Q hQ.posSemidef,operator_positive_definite Q hQ⟩

end MathGauge.MatrixQuadratics
