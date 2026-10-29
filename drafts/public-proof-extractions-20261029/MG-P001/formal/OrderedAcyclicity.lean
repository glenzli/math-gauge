import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedChainComplex
import TauCeti.AlgebraicTopology.Cellular.Augmentation
import TwoOpenContractibility

/-!
Actual ordered integral simplicial chains and their augmentation are compared with
reduced singular homology. The degree-zero augmentation is part of the comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open Set Topology Topology.RelCWComplex TauCeti Finsupp

namespace MathGauge.PublicProof.Topology.TauBridge

section Cellular

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

/-- The degree-zero cellular augmentation detects the ordinary singular augmentation. -/
theorem cellularAugmentation_quasiIsoAt_zero_iff :
    QuasiIsoAt (cellularChainComplexAugmentation C (ModuleCat.of ℤ ℤ)) 0 ↔
      IsIso ((TopCat.of C).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
  rw [quasiIsoAt_iff,
    ShortComplex.quasiIso_iff_isIso_descOpcycles _ (by simp) (by simp) (by simp)]
  simp only [shortComplexFunctor_map_τ₂, cellularChainComplexAugmentation_f_zero]
  change IsIso ((cellularChainComplex C (ModuleCat.of ℤ ℤ)).descOpcycles
      (eqToHom (cellularChainComplex_X C (ModuleCat.of ℤ ℤ) 0) ≫
        cellularAugmentation C (ModuleCat.of ℤ ℤ)) 1 (by simp) (by simp)) ↔ _
  rw [descOpcycles_cellularAugmentation]
  simp only [isIso_comp_left_iff]

/-- The nonempty augmented cellular complex is exact precisely when the actual
reduced integral singular homology vanishes in every degree. -/
theorem cellularAugmentation_quasiIso_iff [Nonempty C] :
    QuasiIso (cellularChainComplexAugmentation C (ModuleCat.of ℤ ℤ)) ↔
      ∀ n : ℕ, IsZero (ReducedIntegralHomology C n) := by
  rw [quasiIso_iff]
  apply forall_congr'
  intro n
  cases n with
  | zero =>
    rw [cellularAugmentation_quasiIsoAt_zero_iff]
    change IsIso ((TopCat.of C).singularHomology₀ε (ModuleCat.of ℤ ℤ)) ↔
      IsZero (kernel ((TopCat.of C).singularHomology₀ε (ModuleCat.of ℤ ℤ)))
    let x : C := Classical.choice (inferInstance : Nonempty C)
    haveI : Epi ((TopCat.of C).singularHomology₀ε (ModuleCat.of ℤ ℤ)) :=
      epi_of_epi_fac (singularHomology₀Section_singularHomology₀ε (ModuleCat.of ℤ ℤ) x)
    constructor
    · intro h
      letI := h
      exact isZero_kernel_of_mono _
    · intro h
      letI := Preadditive.mono_of_isZero_kernel _ h
      exact isIso_of_mono_of_epi _
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
      exactAt_iff_isZero_homology]
    change IsZero ((cellularChainComplex C (ModuleCat.of ℤ ℤ)).homology (n + 1)) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of C))
    exact ⟨fun h => h.of_iso (cellularSingularHomologyIsoOfCWComplex C
      (ModuleCat.of ℤ ℤ) (n + 1)).symm,
      fun h => h.of_iso (cellularSingularHomologyIsoOfCWComplex C
        (ModuleCat.of ℤ ℤ) (n + 1))⟩

/-- Every actual zero-cell basis vector has augmentation one. -/
theorem cellularAugmentation_basis (c : cell C 0) :
    cellularAugmentation C (ModuleCat.of ℤ ℤ) (cellularChainBasis C ℤ 0 c) = 1 := by
  rw [cellularChainBasis_apply]
  exact ConcreteCategory.congr_hom
    (ι_cellularChainGroupIso_inv_comp_cellularAugmentation C (ModuleCat.of ℤ ℤ) c) 1

end Cellular

section Simplicial

variable {V : Type} [LinearOrder V] (K : AbstractSimplicialComplex V)

/-- The cellular-to-ordered chain isomorphism preserves the augmentation: the
degree-zero orientation scale is exactly one. -/
theorem cellularToOrdered_comp_augmentation :
    letI := AbstractSimplicialComplex.realizationCWComplex K
    (cellularChainComplexRealizationIso K ℤ).hom ≫
        orderedSimplicialChainComplexAugmentation K ℤ =
      cellularChainComplexAugmentation (univ : Set (AbstractSimplicialComplex.Realization K))
        (ModuleCat.of ℤ ℤ) := by
  letI := AbstractSimplicialComplex.realizationCWComplex K
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change ((cellularChainComplexRealizationIso K ℤ).hom ≫
      orderedSimplicialChainComplexAugmentation K ℤ).f 0 =
    (cellularChainComplexAugmentation _ (ModuleCat.of ℤ ℤ)).f 0
  rw [HomologicalComplex.comp_f, cellularChainComplexRealizationIso_hom_f,
    orderedSimplicialChainComplexAugmentation_f_zero,
    cellularChainComplexAugmentation_f_zero]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  apply ModuleCat.hom_ext
  apply (cellularChainBasis (univ : Set (AbstractSimplicialComplex.Realization K)) ℤ 0).ext
  intro c
  obtain ⟨d, rfl⟩ := (AbstractSimplicialComplex.realizationCellEquiv K 0).symm.surjective c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
  rw [cellularChainRealizationLinearEquiv_cellularChainBasis,
    realizationChainScale_zero]
  simp only [Units.val_one, linearCombination_single, one_smul,
    HomologicalComplex.singleObjXSelf, Iso.refl_inv, ModuleCat.id_apply]
  exact (cellularAugmentation_basis _ _).symm

/-- The ordered chain augmentation is a quasi-isomorphism exactly when all reduced
integral singular homology of the true realization vanishes. -/
theorem orderedAugmentation_quasiIso_iff [Nonempty V] :
    QuasiIso (orderedSimplicialChainComplexAugmentation K ℤ) ↔
      ∀ n : ℕ, IsZero (ReducedIntegralHomology (AbstractSimplicialComplex.Realization K) n) := by
  letI := AbstractSimplicialComplex.realizationCWComplex K
  letI : Nonempty (AbstractSimplicialComplex.Realization K) :=
    ⟨AbstractSimplicialComplex.vertex K (Classical.choice (inferInstance : Nonempty V))⟩
  rw [← quasiIso_iff_comp_left (cellularChainComplexRealizationIso K ℤ).hom,
    cellularToOrdered_comp_augmentation, cellularAugmentation_quasiIso_iff]
  apply forall_congr'
  intro n
  let e := (Homeomorph.Set.univ (AbstractSimplicialComplex.Realization K)).toHomotopyEquiv
  exact ⟨fun h => h.of_iso (e.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) n).symm,
    fun h => h.of_iso (e.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) n)⟩

end Simplicial

end MathGauge.PublicProof.Topology.TauBridge
