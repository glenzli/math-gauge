import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Countable.Defs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local ext high] TensorProduct.ext
open TensorProduct CategoryTheory Module

universe u
namespace MathGauge.TensorClassification

variable {R : Type} [CommRing R]

variable (M : Type u) [AddCommGroup M] [Module R M]

def tensorFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (M ⊗[R] A)
  map f := ModuleCat.ofHom (LinearMap.lTensor M f.hom)
  map_id A := by ext x y; rfl
  map_comp f g := by ext x y; rfl

def unitEquiv : M ⊗[R] ULift.{u} R ≃ₗ[R] M :=
  (TensorProduct.congr (LinearEquiv.refl R M) (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R)).trans
    (TensorProduct.rid R M)

@[simp] theorem unitEquiv_tmul (m : M) (k : R) :
    unitEquiv M (m ⊗ₜ[R] (ULift.up k)) = k • m := by simp [unitEquiv]

@[simp] theorem unitEquiv_symm_apply (m : M) :
    (unitEquiv M).symm m = m ⊗ₜ[R] (ULift.up 1) := by
  apply (unitEquiv M).injective
  simp

variable {M} {N : Type u} [AddCommGroup N] [Module R N]

def tensorNat (f : M →ₗ[R] N) : tensorFunctor (R := R) M ⟶ tensorFunctor (R := R) N where
  app A := ModuleCat.ofHom (LinearMap.rTensor A f)
  naturality {A B} h := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

@[simp] theorem tensorNat_tmul (f : M →ₗ[R] N) (A : ModuleCat.{u} R) (m : M) (a : A) :
    (tensorNat f).app A (m ⊗ₜ[R] a) = f m ⊗ₜ[R] a := rfl

def tensorNatHom (η : tensorFunctor (R := R) M ⟶ tensorFunctor (R := R) N) : M →ₗ[R] N :=
  (unitEquiv N).toLinearMap.comp
    ((η.app (ModuleCat.of R (ULift.{u} R))).hom.comp (unitEquiv M).symm.toLinearMap)

theorem nat_at_unit (η : tensorFunctor (R := R) M ⟶ tensorFunctor (R := R) N) (m : M) :
    η.app (ModuleCat.of R (ULift.{u} R)) (m ⊗ₜ[R] ULift.up 1) =
      tensorNatHom η m ⊗ₜ[R] ULift.up 1 := by
  apply (unitEquiv N).injective
  rw [unitEquiv_tmul, one_smul]
  change unitEquiv N (η.app (ModuleCat.of R (ULift.{u} R)) (m ⊗ₜ[R] ULift.up 1)) =
    unitEquiv N (η.app (ModuleCat.of R (ULift.{u} R)) ((unitEquiv M).symm m))
  rw [unitEquiv_symm_apply]

/-- Naturality at the map `1 ↦ a` determines each pure tensor. -/
theorem nat_tmul (η : tensorFunctor (R := R) M ⟶ tensorFunctor (R := R) N) (A : ModuleCat.{u} R)
    (m : M) (a : A) : η.app A (m ⊗ₜ[R] a) = tensorNatHom η m ⊗ₜ[R] a := by
  let f : ULift.{u} R →ₗ[R] A :=
    (LinearMap.toSpanSingleton R A a).comp (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap
  have h := congrArg (fun k => k (m ⊗ₜ[R] ULift.up 1))
    (η.naturality (ModuleCat.ofHom f))
  change η.app A ((LinearMap.lTensor M f) (m ⊗ₜ[R] ULift.up 1)) =
    (LinearMap.lTensor N f) (η.app (ModuleCat.of R (ULift.{u} R)) (m ⊗ₜ[R] ULift.up 1)) at h
  rw [nat_at_unit] at h
  simpa [f] using h

theorem tensorNat_ext {η ξ : tensorFunctor (R := R) M ⟶ tensorFunctor (R := R) N}
    (h : ∀ (A : ModuleCat.{u} R) (m : M) (a : A), η.app A (m ⊗ₜ[R] a) = ξ.app A (m ⊗ₜ[R] a)) :
    η = ξ := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro a
  exact h A m a

def tensorNatEquiv : (tensorFunctor (R := R) M ⟶ tensorFunctor (R := R) N) ≃ (M →ₗ[R] N) where
  toFun := tensorNatHom
  invFun := tensorNat
  left_inv η := by
    apply tensorNat_ext
    intro A m a
    exact (nat_tmul η A m a).symm
  right_inv f := by
    ext m
    change unitEquiv N ((LinearMap.rTensor (ULift.{u} R) f) ((unitEquiv M).symm m)) = f m
    rw [unitEquiv_symm_apply]
    simp

@[simp] theorem tensorNat_id : tensorNat (LinearMap.id : M →ₗ[R] M) = 𝟙 (tensorFunctor (R := R) M) := by
  apply tensorNat_ext
  intro A m a
  rfl

@[simp] theorem tensorNat_comp {P : Type u} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) : tensorNat (g.comp f) = tensorNat f ≫ tensorNat g := by
  apply tensorNat_ext
  intro A m a
  rfl

theorem tensorNatHom_id : tensorNatHom (𝟙 (tensorFunctor (R := R) M)) = LinearMap.id := by
  rw [← tensorNat_id]
  exact tensorNatEquiv.apply_symm_apply _

theorem tensorNatHom_comp {P : Type u} [AddCommGroup P] [Module R P]
    (η : tensorFunctor (R := R) M ⟶ tensorFunctor (R := R) N) (ξ : tensorFunctor (R := R) N ⟶ tensorFunctor (R := R) P) :
    tensorNatHom (η ≫ ξ) = (tensorNatHom ξ).comp (tensorNatHom η) := by
  apply tensorNatEquiv.symm.injective
  change tensorNat (tensorNatHom (η ≫ ξ)) = tensorNat ((tensorNatHom ξ).comp (tensorNatHom η))
  rw [tensorNat_comp]
  exact (tensorNatEquiv.symm_apply_apply (η ≫ ξ)).trans
    (congrArg₂ (fun x y => x ≫ y)
      (tensorNatEquiv.symm_apply_apply η) (tensorNatEquiv.symm_apply_apply ξ)).symm

def tensorIso (e : M ≃ₗ[R] N) : tensorFunctor (R := R) M ≅ tensorFunctor (R := R) N where
  hom := tensorNat e.toLinearMap
  inv := tensorNat e.symm.toLinearMap
  hom_inv_id := by rw [← tensorNat_comp]; simpa using tensorNat_id (M := M)
  inv_hom_id := by rw [← tensorNat_comp]; simpa using tensorNat_id (M := N)

def isoAtUnit (e : tensorFunctor (R := R) M ≅ tensorFunctor (R := R) N) : M ≃ₗ[R] N :=
  (unitEquiv M).symm.trans ((e.app (ModuleCat.of R (ULift.{u} R))).toLinearEquiv.trans (unitEquiv N))

theorem tensor_natIso_iff : Nonempty (tensorFunctor (R := R) M ≅ tensorFunctor (R := R) N) ↔ Nonempty (M ≃ₗ[R] N) :=
  ⟨fun ⟨e⟩ => ⟨isoAtUnit e⟩, fun ⟨e⟩ => ⟨tensorIso e⟩⟩

end MathGauge.TensorClassification
