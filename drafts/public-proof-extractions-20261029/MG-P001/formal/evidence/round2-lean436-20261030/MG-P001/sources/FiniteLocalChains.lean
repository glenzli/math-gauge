import TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic.Linarith

/-!
The local integer criterion is a finite collection of exactness tests on the
actual augmented ordered simplicial chain groups. Degrees above the number of
vertices have no cells, hence no chains. No rationalization or rank-only test
is used, so torsion remains part of the criterion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex TauCeti Finsupp

namespace MathGauge.PublicProof.Topology

variable {V : Type} [LinearOrder V] (K : AbstractSimplicialComplex V)

def integral_augmentation : OrderedSimplicialChain K ℤ 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1 : ℤ))

def AugmentedExact : Prop :=
  (∀ z : OrderedSimplicialChain K ℤ 0, integral_augmentation K z = 0 →
    ∃ y : OrderedSimplicialChain K ℤ 1, OrderedSimplicialChain.boundary ℤ 0 y = z) ∧
  ∀ n : ℕ, ∀ z : OrderedSimplicialChain K ℤ (n + 1),
    OrderedSimplicialChain.boundary ℤ n z = 0 →
    ∃ y : OrderedSimplicialChain K ℤ (n + 2), OrderedSimplicialChain.boundary ℤ (n + 1) y = z

theorem ordered_exactAt_iff (n : ℕ) :
    (orderedSimplicialChainComplex K ℤ).ExactAt (n + 1) ↔
      ∀ z : OrderedSimplicialChain K ℤ (n + 1), OrderedSimplicialChain.boundary ℤ n z = 0 →
        ∃ y : OrderedSimplicialChain K ℤ (n + 2),
          OrderedSimplicialChain.boundary ℤ (n + 1) y = z := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact exact_orderedSimplicialChainComplex_d_iff ℤ _
    (eqToIso (orderedSimplicialChainComplex_X ℤ n)) (g' := OrderedSimplicialChain.boundary ℤ n)
    (by simp)

theorem ordered_augmentation_zero_iff [Nonempty V] :
    QuasiIsoAt (orderedSimplicialChainComplexAugmentation K ℤ) 0 ↔
      ∀ z : OrderedSimplicialChain K ℤ 0, integral_augmentation K z = 0 →
        ∃ y : OrderedSimplicialChain K ℤ 1, OrderedSimplicialChain.boundary ℤ 0 y = z := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ (by simp) rfl rfl]
  have he := exact_orderedSimplicialChainComplex_d_iff (K := K) ℤ
    (g := (orderedSimplicialChainComplexAugmentation K ℤ).f 0)
    (by simp [orderedSimplicialChainComplex_d, ← ModuleCat.ofHom_comp,
      OrderedSimplicialChain.augmentation_comp_boundary]; rfl)
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of ℤ ℤ))
    (g' := integral_augmentation K) (by simp [integral_augmentation])
  constructor
  · intro h
    exact he.mp h.1
  · intro h
    refine ⟨he.mpr h, ?_⟩
    letI : Epi (ModuleCat.ofHom (integral_augmentation K)) := by
      rw [ModuleCat.epi_iff_surjective]
      intro r
      let v : V := Classical.arbitrary V
      exact ⟨Finsupp.single (AbstractSimplicialComplex.RealizationCell.vertex K v) r,
        by simp [integral_augmentation]⟩
    simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂,
      orderedSimplicialChainComplexAugmentation_f_zero]
    change Epi (_ ≫ ModuleCat.ofHom (integral_augmentation K) ≫ _)
    infer_instance

theorem augmentedExact_iff_quasiIso [Nonempty V] :
    AugmentedExact K ↔ QuasiIso (orderedSimplicialChainComplexAugmentation K ℤ) := by
  rw [quasiIso_iff]
  constructor
  · rintro ⟨h₀, h⟩ n
    cases n with
    | zero => exact (ordered_augmentation_zero_iff K).mpr h₀
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact (ordered_exactAt_iff K n).mpr (h n)
  · intro h
    refine ⟨(ordered_augmentation_zero_iff K).mp (h 0), ?_⟩
    intro n
    apply (ordered_exactAt_iff K n).mp
    exact (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj ..)).mp (h (n + 1))

variable [Fintype V]

omit [LinearOrder V] in
theorem no_cells_above_vertex_bound (n : ℕ) (hn : Fintype.card V ≤ n) :
    IsEmpty (AbstractSimplicialComplex.RealizationCell K n) := by
  refine ⟨fun c => ?_⟩
  have hc := Finset.card_le_univ c.1.1
  rw [c.2] at hc
  omega

theorem chains_zero_above_vertex_bound (n : ℕ) (hn : Fintype.card V ≤ n)
    (z : OrderedSimplicialChain K ℤ n) : z = 0 := by
  letI := no_cells_above_vertex_bound K n hn
  exact Subsingleton.elim _ _

/-- A bounded family of actual integer cycles-to-boundaries tests, including the
degree-zero augmentation. Every group has one basis vector for an actual finite face. -/
def FiniteAugmentedExact : Prop :=
  (∀ z : OrderedSimplicialChain K ℤ 0, integral_augmentation K z = 0 →
    ∃ y : OrderedSimplicialChain K ℤ 1, OrderedSimplicialChain.boundary ℤ 0 y = z) ∧
  ∀ n : Fin (Fintype.card V), ∀ z : OrderedSimplicialChain K ℤ (n.1 + 1),
    OrderedSimplicialChain.boundary ℤ n.1 z = 0 →
    ∃ y : OrderedSimplicialChain K ℤ (n.1 + 2), OrderedSimplicialChain.boundary ℤ (n.1 + 1) y = z

theorem finiteAugmentedExact_iff : FiniteAugmentedExact K ↔ AugmentedExact K := by
  constructor
  · rintro ⟨h₀, h⟩
    refine ⟨h₀, ?_⟩
    intro n z hz
    by_cases hn : n < Fintype.card V
    · exact h ⟨n, hn⟩ z hz
    · have hc : Fintype.card V ≤ n + 1 := by omega
      exact ⟨0, by rw [map_zero, chains_zero_above_vertex_bound K (n + 1) hc z]⟩
  · rintro ⟨h₀, h⟩
    exact ⟨h₀, fun n => h n.1⟩

theorem finiteAugmentedExact_iff_quasiIso [Nonempty V] :
    FiniteAugmentedExact K ↔ QuasiIso (orderedSimplicialChainComplexAugmentation K ℤ) :=
  (finiteAugmentedExact_iff K).trans (augmentedExact_iff_quasiIso K)

end MathGauge.PublicProof.Topology
