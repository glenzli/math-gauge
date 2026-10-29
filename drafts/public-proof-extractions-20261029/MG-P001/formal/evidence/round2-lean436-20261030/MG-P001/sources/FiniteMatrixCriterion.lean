import FiniteBoundaryMatrix
import FiniteLocalChains

noncomputable section

open TauCeti Finsupp

namespace MathGauge.PublicProof.Topology

variable {V : Type} [LinearOrder V] [Fintype V] (K : AbstractSimplicialComplex V)

theorem matrix_positive_exact_iff (n : ℕ) :
    (∀ z : AbstractSimplicialComplex.RealizationCell K (n + 1) → ℤ,
      (boundaryMatrix K n).mulVec z = 0 →
        ∃ y : AbstractSimplicialComplex.RealizationCell K (n + 2) → ℤ,
          (boundaryMatrix K (n + 1)).mulVec y = z) ↔
    (∀ z : OrderedSimplicialChain K ℤ (n + 1),
      OrderedSimplicialChain.boundary ℤ n z = 0 →
        ∃ y : OrderedSimplicialChain K ℤ (n + 2),
          OrderedSimplicialChain.boundary ℤ (n + 1) y = z) := by
  constructor
  · intro h z hz
    obtain ⟨y, hy⟩ := h (chainCoordinates K (n + 1) z) (by
      rw [boundaryMatrix_mulVec_coordinates, hz, map_zero])
    refine ⟨(chainCoordinates K (n + 2)).symm y, ?_⟩
    apply (chainCoordinates K (n + 1)).injective
    rwa [boundaryMatrix_mulVec] at hy
  · intro h z hz
    have hc : OrderedSimplicialChain.boundary ℤ n
        ((chainCoordinates K (n + 1)).symm z) = 0 := by
      apply (chainCoordinates K n).injective
      rw [map_zero]
      rwa [boundaryMatrix_mulVec] at hz
    obtain ⟨y, hy⟩ := h ((chainCoordinates K (n + 1)).symm z) hc
    refine ⟨chainCoordinates K (n + 2) y, ?_⟩
    rw [boundaryMatrix_mulVec_coordinates, hy, LinearEquiv.apply_symm_apply]

theorem matrix_augmentation_exact_iff :
    (∀ z : AbstractSimplicialComplex.RealizationCell K 0 → ℤ,
      (∑ c, z c) = 0 →
        ∃ y : AbstractSimplicialComplex.RealizationCell K 1 → ℤ,
          (boundaryMatrix K 0).mulVec y = z) ↔
    (∀ z : OrderedSimplicialChain K ℤ 0,
      integral_augmentation K z = 0 →
        ∃ y : OrderedSimplicialChain K ℤ 1,
          OrderedSimplicialChain.boundary ℤ 0 y = z) := by
  constructor
  · intro h z hz
    have hc : (∑ c, chainCoordinates K 0 z c) = 0 := by
      rw [← augmentation_coordinates K (chainCoordinates K 0 z), LinearEquiv.symm_apply_apply]
      exact hz
    obtain ⟨y, hy⟩ := h (chainCoordinates K 0 z) hc
    refine ⟨(chainCoordinates K 1).symm y, ?_⟩
    apply (chainCoordinates K 0).injective
    rwa [boundaryMatrix_mulVec] at hy
  · intro h z hz
    have hc : integral_augmentation K ((chainCoordinates K 0).symm z) = 0 := by
      exact (augmentation_coordinates K z).trans hz
    obtain ⟨y, hy⟩ := h ((chainCoordinates K 0).symm z) hc
    refine ⟨chainCoordinates K 1 y, ?_⟩
    rw [boundaryMatrix_mulVec_coordinates, hy, LinearEquiv.apply_symm_apply]

/-- A genuinely finite family of integer-matrix exactness tests. The degree-zero
row is the all-ones augmentation. All other matrix entries are proved to be
signed face-incidence entries. The integer coefficient domain retains torsion. -/
def FiniteMatrixExact : Prop :=
  (∀ z : AbstractSimplicialComplex.RealizationCell K 0 → ℤ,
    (∑ c, z c) = 0 →
      ∃ y : AbstractSimplicialComplex.RealizationCell K 1 → ℤ,
        (boundaryMatrix K 0).mulVec y = z) ∧
  ∀ n : Fin (Fintype.card V),
    ∀ z : AbstractSimplicialComplex.RealizationCell K (n.1 + 1) → ℤ,
      (boundaryMatrix K n.1).mulVec z = 0 →
        ∃ y : AbstractSimplicialComplex.RealizationCell K (n.1 + 2) → ℤ,
          (boundaryMatrix K (n.1 + 1)).mulVec y = z

theorem finiteMatrixExact_iff_augmented :
    FiniteMatrixExact K ↔ FiniteAugmentedExact K := by
  unfold FiniteMatrixExact FiniteAugmentedExact
  exact and_congr (matrix_augmentation_exact_iff K)
    (forall_congr' fun n => matrix_positive_exact_iff K n.1)

end MathGauge.PublicProof.Topology
