import TensorRepresentability
import Mathlib.Algebra.Category.ModuleCat.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open TensorProduct CategoryTheory Module

universe u
namespace MathGauge.TensorClassification

variable {R : Type} [CommRing R]

/-- An explicit diagram of modules and all its compatibility equations. Category
diagrams are instantiated below; no conclusion is a field of this structure. -/
structure ModuleDiagram (R : Type) [CommRing R] (J K : Type u) where
  obj : J → ModuleCat.{u} R
  source : K → J
  target : K → J
  map : ∀ k, obj (source k) →ₗ[R] obj (target k)

namespace ModuleDiagram
variable {J K : Type u} (D : ModuleDiagram R J K)

def compatible : Submodule R (∀ j, D.obj j) where
  carrier := {x | ∀ k, D.map k (x (D.source k)) = x (D.target k)}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy k; simpa using congrArg₂ (· + ·) (hx k) (hy k)
  smul_mem' := by intro a x hx k; simpa using congrArg (a • ·) (hx k)

def projection (j : J) : D.compatible →ₗ[R] D.obj j :=
  (LinearMap.proj j).comp D.compatible.subtype

@[simp] theorem projection_apply (j : J) (x : D.compatible) : D.projection j x = x.1 j := rfl

variable (M : Type u) [AddCommGroup M] [Module R M]

def tensor : ModuleDiagram R J K where
  obj j := ModuleCat.of R (M ⊗[R] D.obj j)
  source := D.source
  target := D.target
  map k := LinearMap.lTensor M (D.map k)

def comparison : M ⊗[R] D.compatible →ₗ[R] (D.tensor M).compatible :=
  (LinearMap.pi fun j => LinearMap.lTensor M (D.projection j)).codRestrict _ (by
    intro t k
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m x =>
      change m ⊗ₜ[R] D.map k (x.1 (D.source k)) = m ⊗ₜ[R] x.1 (D.target k)
      rw [x.2 k]
    | add x y hx hy =>
      change (LinearMap.lTensor M (D.map k))
        ((LinearMap.lTensor M (D.projection (D.source k))) (x+y)) =
        (LinearMap.lTensor M (D.projection (D.target k))) (x+y)
      simpa only [map_add] using congrArg₂ (· + ·) hx hy)

@[simp] theorem comparison_apply (t : M ⊗[R] D.compatible) (j : J) :
    (D.comparison M t).1 j = LinearMap.lTensor M (D.projection j) t := rfl

@[simp] theorem comparison_tmul (m : M) (x : D.compatible) (j : J) :
    (D.comparison M (m ⊗ₜ[R] x)).1 j = m ⊗ₜ[R] x.1 j := rfl

variable {P : Type u} [AddCommGroup P] [Module R P]

theorem representation_comparison_bijective
    (e : tensorFunctor (R := R) M ≅ homFunctor (R := R) P) :
    Function.Bijective (D.comparison M) := by
  let L := ModuleCat.of R D.compatible
  have hn (j : J) (t : M ⊗[R] D.compatible) :
      e.hom.app (D.obj j) ((D.comparison M t).1 j) =
        (D.projection j).comp (e.hom.app L t) := by
    exact congrArg (fun k => k t) (e.hom.naturality (ModuleCat.ofHom (D.projection j)))
  constructor
  · intro x y hxy
    apply (e.app L).toLinearEquiv.injective
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    funext j
    have hh := congrArg (fun z : (D.tensor M).compatible =>
      e.hom.app (D.obj j) (z.1 j)) hxy
    dsimp only at hh
    rw [hn, hn] at hh
    exact LinearMap.congr_fun hh p
  · intro y
    let h₀ : P →ₗ[R] (∀ j, D.obj j) :=
      LinearMap.pi fun j => e.hom.app (D.obj j) (y.1 j)
    let h : P →ₗ[R] D.compatible := h₀.codRestrict _ (by
          intro p
          intro k
          have hk := congrArg (fun f => f (y.1 (D.source k)))
            (e.hom.naturality (ModuleCat.ofHom (D.map k)))
          change e.hom.app (D.obj (D.target k))
            ((LinearMap.lTensor M (D.map k)) (y.1 (D.source k))) =
              (D.map k).comp (e.hom.app (D.obj (D.source k)) (y.1 (D.source k))) at hk
          rw [show (LinearMap.lTensor M (D.map k)) (y.1 (D.source k)) =
            y.1 (D.target k) from y.2 k] at hk
          exact (LinearMap.congr_fun hk p).symm)
    let t := (e.app L).toLinearEquiv.symm h
    refine ⟨t, ?_⟩
    apply Subtype.ext
    funext j
    apply (e.app (D.obj j)).toLinearEquiv.injective
    change e.hom.app (D.obj j) ((D.comparison M t).1 j) = e.hom.app (D.obj j) (y.1 j)
    rw [hn]
    change (D.projection j).comp ((e.app L).toLinearEquiv ((e.app L).toLinearEquiv.symm h)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl

end ModuleDiagram

variable (M : Type u) [AddCommGroup M] [Module R M]

def PreservesCountableCompatibleLimits : Prop :=
  ∀ (J K : Type u) [Countable J] [Countable K] (D : ModuleDiagram R J K),
    Function.Bijective (D.comparison M)

theorem representable_preserves_all_compatible_limits {P : Type u} [AddCommGroup P] [Module R P]
    (e : tensorFunctor (R := R) M ≅ homFunctor (R := R) P)
    {J K : Type u} (D : ModuleDiagram R J K) : Function.Bijective (D.comparison M) :=
  D.representation_comparison_bijective M e

theorem countable_limits_implies_product_surjective
    (h : PreservesCountableCompatibleLimits (R := R) M) :
    Function.Surjective (countableProductMap (R := R) M) := by
  let D : ModuleDiagram R (ULift.{u} ℕ) PEmpty.{u+1} :=
    { obj := fun _ => ModuleCat.of R (ULift.{u} R)
      source := PEmpty.elim
      target := PEmpty.elim
      map := PEmpty.elim }
  intro y
  let z : (D.tensor M).compatible :=
    ⟨fun j => (unitEquiv M).symm (y j.down), fun k => PEmpty.elim k⟩
  obtain ⟨t,ht⟩ := (h _ _ D).2 z
  let v : D.compatible →ₗ[R] (ℕ → ULift.{u} R) :=
    { toFun x j := x.1 (ULift.up j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearMap.lTensor M v t, funext fun j => ?_⟩
  change unitEquiv M ((LinearMap.lTensor M (LinearMap.proj j)) ((LinearMap.lTensor M v) t)) = y j
  rw [← LinearMap.lTensor_comp_apply]
  have he : (LinearMap.proj j).comp v = D.projection (ULift.up j) := rfl
  rw [he]
  have hj := congrArg (fun x : (D.tensor M).compatible => x.1 (ULift.up j)) ht
  change LinearMap.lTensor M (D.projection (ULift.up j)) t = (unitEquiv M).symm (y j) at hj
  rw [hj, LinearEquiv.apply_symm_apply]

end MathGauge.TensorClassification
