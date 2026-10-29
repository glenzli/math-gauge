import SequentialTower
import CategoryLimits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits TensorProduct Module
open MathGauge.TensorClassification

universe u v
namespace MathGauge.Tower.FreeTower
variable {R : Type} [CommRing R] (T S : FreeTower.{u} R)

/-- The original record functor, with postcomposition on morphisms. -/
def recordFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (T.Record A)
  map f := ModuleCat.ofHom (T.recordMap f.hom)
  map_id A := ModuleCat.hom_ext T.recordMap_id
  map_comp f g := ModuleCat.hom_ext (T.recordMap_comp f.hom g.hom)

def tensorRecordNatIso : tensorFunctor (R := R) T.Invariant ≅ T.recordFunctor :=
  NatIso.ofComponents (fun A => (T.tensorRecordEquiv A).toModuleIso) (fun {A B} f => by
    apply ModuleCat.hom_ext
    exact (T.tensorRecordEquiv_natural A f.hom).symm)

def recordProductMap : T.Record (ℕ → ULift.{u} R) →ₗ[R] (ℕ → T.Record (ULift.{u} R)) :=
  LinearMap.pi fun n => T.recordMap (LinearMap.proj n)

def recordUnitEquiv : T.Record (ULift.{u} R) ≃ₗ[R] T.Invariant :=
  (T.tensorRecordEquiv _).symm.trans (unitEquiv T.Invariant)

theorem recordProduct_tensor (t : T.Invariant ⊗[R] (ℕ → ULift.{u} R)) (j : ℕ) :
    T.recordUnitEquiv (T.recordProductMap (T.tensorRecordEquiv _ t) j) =
      countableProductMap T.Invariant t j := by
  have hn := LinearMap.congr_fun (T.tensorRecordEquiv_natural (ℕ → ULift.{u} R)
    (LinearMap.proj j : (ℕ → ULift.{u} R) →ₗ[R] ULift.{u} R)) t
  change T.recordMap (LinearMap.proj j) (T.tensorRecordEquiv _ t) =
    T.tensorRecordEquiv _ ((LinearMap.lTensor T.Invariant (LinearMap.proj j)) t) at hn
  change unitEquiv T.Invariant ((T.tensorRecordEquiv _).symm
    (T.recordMap (LinearMap.proj j) (T.tensorRecordEquiv _ t))) = _
  rw [hn, LinearEquiv.symm_apply_apply]
  rfl

theorem recordProduct_surjective_iff : Function.Surjective T.recordProductMap ↔
    Function.Surjective (countableProductMap (R := R) T.Invariant) := by
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := h (fun n => T.recordUnitEquiv.symm (y n))
    refine ⟨(T.tensorRecordEquiv _).symm t, funext fun j => ?_⟩
    rw [← T.recordProduct_tensor, LinearEquiv.apply_symm_apply, ht]
    exact T.recordUnitEquiv.apply_symm_apply (y j)
  · intro h y
    obtain ⟨t,ht⟩ := h (fun n => T.recordUnitEquiv (y n))
    refine ⟨T.tensorRecordEquiv _ t, funext fun j => ?_⟩
    apply T.recordUnitEquiv.injective
    rw [T.recordProduct_tensor, ht]

def Representable : Prop := ∃ P : ModuleCat.{u} R,
  Nonempty (T.recordFunctor ≅ homFunctor (R := R) P)

/-- Transport of all group-valued natural transformations, not just additive
transformations chosen from a proposed formula. -/
def recordToTensorNatEquiv :
    (T.recordFunctor ⟶ S.recordFunctor) ≃
      (tensorFunctor (R := R) T.Invariant ⟶ tensorFunctor (R := R) S.Invariant) where
  toFun η := T.tensorRecordNatIso.hom ≫ η ≫ S.tensorRecordNatIso.inv
  invFun η := T.tensorRecordNatIso.inv ≫ η ≫ S.tensorRecordNatIso.hom
  left_inv η := by simp [Category.assoc]
  right_inv η := by simp [Category.assoc]

def recordNatEquiv : (T.recordFunctor ⟶ S.recordFunctor) ≃
    (T.Invariant →ₗ[R] S.Invariant) :=
  (T.recordToTensorNatEquiv S).trans tensorNatEquiv

/-- Ambient-universe enlargement changes neither the range of objects on which
naturality is tested nor the classification. The natural transformation type
already quantifies over every module with carrier in `Type u`; it may be placed
in any larger ambient universe using this explicit equivalence. -/
def recordNatEquivInLargerUniverse :
    ULift.{max u v + 1} (T.recordFunctor ⟶ S.recordFunctor) ≃
      ULift.{max u v + 1} (T.Invariant →ₗ[R] S.Invariant) where
  toFun η := ⟨T.recordNatEquiv S η.down⟩
  invFun f := ⟨(T.recordNatEquiv S).symm f.down⟩
  left_inv η := by cases η; simp
  right_inv f := by cases f; simp

theorem recordNatEquiv_id : T.recordNatEquiv T (𝟙 T.recordFunctor) = LinearMap.id := by
  change tensorNatHom (T.tensorRecordNatIso.hom ≫ 𝟙 _ ≫ T.tensorRecordNatIso.inv) = _
  simp [tensorNatHom_id]

theorem recordNatEquiv_comp (U : FreeTower.{u} R)
    (η : T.recordFunctor ⟶ S.recordFunctor) (ξ : S.recordFunctor ⟶ U.recordFunctor) :
    T.recordNatEquiv U (η ≫ ξ) = (S.recordNatEquiv U ξ).comp (T.recordNatEquiv S η) := by
  change tensorNatHom (T.tensorRecordNatIso.hom ≫ (η ≫ ξ) ≫ U.tensorRecordNatIso.inv) = _
  have h : T.tensorRecordNatIso.hom ≫ (η ≫ ξ) ≫ U.tensorRecordNatIso.inv =
      (T.recordToTensorNatEquiv S η) ≫ (S.recordToTensorNatEquiv U ξ) := by
    simp [recordToTensorNatEquiv, Category.assoc]
  rw [h, tensorNatHom_comp]
  rfl

theorem record_natIso_iff : Nonempty (T.recordFunctor ≅ S.recordFunctor) ↔
    Nonempty (T.Invariant ≃ₗ[R] S.Invariant) := by
  constructor
  · rintro ⟨e⟩
    exact tensor_natIso_iff.mp ⟨T.tensorRecordNatIso.trans (e.trans S.tensorRecordNatIso.symm)⟩
  · intro h
    obtain ⟨e⟩ := tensor_natIso_iff.mpr h
    exact ⟨T.tensorRecordNatIso.symm.trans (e.trans S.tensorRecordNatIso)⟩

variable (T : FreeTower.{u} ℤ)

theorem representable_iff_finite : T.Representable ↔ Module.Finite ℤ T.Invariant := by
  constructor
  · rintro ⟨P,⟨e⟩⟩
    exact finite_of_countableProduct_surjective T.Invariant
      (representable_countableProduct_surjective T.Invariant P (T.tensorRecordNatIso.trans e))
  · intro h
    letI := h
    letI : Module.Free ℤ T.Invariant := Module.free_of_finite_type_torsion_free'
    exact ⟨ModuleCat.of ℤ (Module.Dual ℤ T.Invariant),
      ⟨T.tensorRecordNatIso.symm.trans (finiteDualRepresentation T.Invariant)⟩⟩

theorem product_surjective_iff_finite : Function.Surjective T.recordProductMap ↔
    Module.Finite ℤ T.Invariant := by
  rw [T.recordProduct_surjective_iff]
  constructor
  · exact finite_of_countableProduct_surjective T.Invariant
  · intro h
    letI := h
    letI : Module.Free ℤ T.Invariant := Module.free_of_finite_type_torsion_free'
    exact representable_countableProduct_surjective T.Invariant _ (finiteDualRepresentation T.Invariant)

theorem finite_preserves_all_limits [Module.Finite ℤ T.Invariant]
    {J : Type u} [Category.{u} J] (D : J ⥤ ModuleCat.{u} ℤ) :
    PreservesLimit D T.recordFunctor := by
  letI : Module.Free ℤ T.Invariant := Module.free_of_finite_type_torsion_free'
  letI := representation_preservesLimit T.Invariant (finiteDualRepresentation T.Invariant) D
  exact preservesLimit_of_natIso D T.tensorRecordNatIso

theorem countable_limits_iff_finite : PreservesCountableLimits T.recordFunctor ↔
    Module.Finite ℤ T.Invariant := by
  constructor
  · intro h
    apply finite_of_countableProduct_surjective T.Invariant
    apply categorical_countable_limits_implies_product_surjective
    intro J _ _ _ D
    letI := h J D
    exact preservesLimit_of_natIso D T.tensorRecordNatIso.symm
  · intro h
    letI := h
    intro J _ _ _ D
    exact T.finite_preserves_all_limits D

theorem finite_iff_finite_free : Module.Finite ℤ T.Invariant ↔
    (Module.Finite ℤ T.Invariant ∧ Module.Free ℤ T.Invariant) := by
  constructor
  · intro h
    letI := h
    exact ⟨h, Module.free_of_finite_type_torsion_free'⟩
  · exact And.left

/-- All five conditions of the classification theorem, with the canonical
countable-product comparison and the standard categorical preservation class. -/
theorem classification :
    (T.Representable ↔ Module.Finite ℤ T.Invariant) ∧
    (PreservesCountableLimits T.recordFunctor ↔ Module.Finite ℤ T.Invariant) ∧
    (Function.Surjective T.recordProductMap ↔ Module.Finite ℤ T.Invariant) ∧
    (Module.Finite ℤ T.Invariant ↔
      (Module.Finite ℤ T.Invariant ∧ Module.Free ℤ T.Invariant)) :=
  ⟨T.representable_iff_finite, T.countable_limits_iff_finite,
    T.product_surjective_iff_finite, T.finite_iff_finite_free⟩

def canonicalRepresentation [Module.Finite ℤ T.Invariant] :
    T.recordFunctor ≅ homFunctor (R := ℤ) (Module.Dual ℤ T.Invariant) := by
  letI : Module.Free ℤ T.Invariant := Module.free_of_finite_type_torsion_free'
  exact T.tensorRecordNatIso.symm.trans (finiteDualRepresentation T.Invariant)

theorem all_record_representing_objects [Module.Finite ℤ T.Invariant]
    (P : ModuleCat.{u} ℤ) :
    Nonempty (T.recordFunctor ≅ homFunctor (R := ℤ) P) ↔
      Nonempty (P ≃ₗ[ℤ] Module.Dual ℤ T.Invariant) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨representingObjectEquiv (e.symm.trans T.canonicalRepresentation)⟩
  · rintro ⟨e⟩
    exact ⟨T.canonicalRepresentation.trans (homIsoOfEquiv e.symm)⟩

end MathGauge.Tower.FreeTower
