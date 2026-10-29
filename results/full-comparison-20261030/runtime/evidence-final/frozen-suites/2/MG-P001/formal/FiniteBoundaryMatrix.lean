import TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open TauCeti Finsupp

namespace MathGauge.PublicProof.Topology

variable {V : Type} [LinearOrder V] [Fintype V] (K : AbstractSimplicialComplex V)

noncomputable instance finiteCellFintype (n : ℕ) :
    Fintype (AbstractSimplicialComplex.RealizationCell K n) := Fintype.ofFinite _

/-- Actual finite face-indexed integer coordinates of a simplicial chain. -/
def chainCoordinates (n : ℕ) : OrderedSimplicialChain K ℤ n ≃ₗ[ℤ]
    (AbstractSimplicialComplex.RealizationCell K n → ℤ) :=
  Finsupp.linearEquivFunOnFinite ℤ ℤ _

def coordinateBoundary (n : ℕ) :
    (AbstractSimplicialComplex.RealizationCell K (n + 1) → ℤ) →ₗ[ℤ]
      (AbstractSimplicialComplex.RealizationCell K n → ℤ) :=
  (chainCoordinates K n).toLinearMap.comp
    ((OrderedSimplicialChain.boundary (K := K) ℤ n).comp
      (chainCoordinates K (n + 1)).symm.toLinearMap)

/-- The finite integer matrix of the actual alternating simplicial boundary. -/
def boundaryMatrix (n : ℕ) :
    Matrix (AbstractSimplicialComplex.RealizationCell K n)
      (AbstractSimplicialComplex.RealizationCell K (n + 1)) ℤ := by
  classical
  exact LinearMap.toMatrix' (coordinateBoundary K n)

/-- Matrix multiplication agrees with the actual boundary, under proved inverse coordinates. -/
theorem boundaryMatrix_mulVec (n : ℕ)
    (x : AbstractSimplicialComplex.RealizationCell K (n + 1) → ℤ) :
    (boundaryMatrix K n).mulVec x =
      chainCoordinates K n (OrderedSimplicialChain.boundary ℤ n
        ((chainCoordinates K (n + 1)).symm x)) := by
  classical
  exact LinearMap.toMatrix'_mulVec (coordinateBoundary K n) x

/-- Every column is exactly the alternating sum of the codimension-one faces. -/
theorem boundaryMatrix_apply (n : ℕ)
    (r : AbstractSimplicialComplex.RealizationCell K n)
    (c : AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    boundaryMatrix K n r c = OrderedSimplicialChain.boundaryCell ℤ c r := by
  classical
  simp [boundaryMatrix, LinearMap.toMatrix'_apply, coordinateBoundary, chainCoordinates,
    OrderedSimplicialChain.boundaryCell, Finsupp.finsetSum_apply]

/-- The incidence entries are precisely signed ones at deleted faces. -/
theorem boundaryMatrix_face (n : ℕ)
    (c : AbstractSimplicialComplex.RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    boundaryMatrix K n (c.face j) c = (-1 : ℤ) ^ (j : ℕ) := by
  rw [boundaryMatrix_apply, OrderedSimplicialChain.boundaryCell_apply_face]

/-- All other entries are zero; the matrix uses only finite face incidence. -/
theorem boundaryMatrix_zero_of_not_face (n : ℕ)
    (r : AbstractSimplicialComplex.RealizationCell K n)
    (c : AbstractSimplicialComplex.RealizationCell K (n + 1))
    (h : ¬ r.1.1 ⊆ c.1.1) : boundaryMatrix K n r c = 0 := by
  rw [boundaryMatrix_apply]
  exact OrderedSimplicialChain.boundaryCell_apply_eq_zero_of_not_subset ℤ c r h

/-- The augmentation is the finite sum of the coordinates of actual zero-faces. -/
theorem augmentation_coordinates
    (x : AbstractSimplicialComplex.RealizationCell K 0 → ℤ) :
    Finsupp.linearCombination ℤ (fun _ : AbstractSimplicialComplex.RealizationCell K 0 => (1 : ℤ))
      ((chainCoordinates K 0).symm x) = ∑ c, x c := by
  classical
  simpa [chainCoordinates, Fintype.linearCombination_apply] using
    (Finsupp.linearCombination_eq_fintype_linearCombination_apply ℤ
      (fun _ : AbstractSimplicialComplex.RealizationCell K 0 => (1 : ℤ)) x)

theorem boundaryMatrix_mulVec_coordinates (n : ℕ)
    (y : OrderedSimplicialChain K ℤ (n + 1)) :
    (boundaryMatrix K n).mulVec (chainCoordinates K (n + 1) y) =
      chainCoordinates K n (OrderedSimplicialChain.boundary ℤ n y) := by
  rw [boundaryMatrix_mulVec, LinearEquiv.symm_apply_apply]

end MathGauge.PublicProof.Topology
