import TensorNatural
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open TensorProduct CategoryTheory Module

universe u
namespace MathGauge.TensorClassification

variable {R : Type} [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The canonical comparison to the countable product, with universe-lifted scalars. -/
def countableProductMap : M ⊗[R] (ℕ → ULift.{u} R) →ₗ[R] (ℕ → M) :=
  LinearMap.pi fun j => (unitEquiv M).toLinearMap.comp
    (LinearMap.lTensor M (LinearMap.proj j : (ℕ → ULift.{u} R) →ₗ[R] ULift.{u} R))

@[simp] theorem countableProductMap_tmul (m : M) (a : ℕ → ULift.{u} R) (j : ℕ) :
    countableProductMap M (m ⊗ₜ[R] a) j = (a j).down • m := by
  change unitEquiv M (m ⊗ₜ[R] a j) = _
  exact unitEquiv_tmul M m (a j).down

theorem tensor_coordinates_finitely_generated (t : M ⊗[R] (ℕ → ULift.{u} R)) :
    ∃ S : Submodule R M, S.FG ∧ ∀ j, countableProductMap M t j ∈ S := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
  | tmul m a =>
    refine ⟨Submodule.span R {m}, Submodule.fg_span_singleton m, ?_⟩
    intro j
    rw [countableProductMap_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton m))
  | add x y hx hy =>
    obtain ⟨S,hS,hx⟩ := hx
    obtain ⟨T,hT,hy⟩ := hy
    refine ⟨S ⊔ T, hS.sup hT, ?_⟩
    intro j
    simp only [map_add, Pi.add_apply]
    exact Submodule.add_mem _ ((show S ≤ S ⊔ T from le_sup_left) (hx j))
      ((show T ≤ S ⊔ T from le_sup_right) (hy j))

/-- Countability is explicit and is the only enumeration hypothesis in this step. -/
theorem finite_of_countableProduct_surjective [Countable M]
    (h : Function.Surjective (countableProductMap (R := R) M)) : Module.Finite R M := by
  obtain ⟨e,he⟩ := exists_surjective_nat M
  obtain ⟨t,ht⟩ := h e
  obtain ⟨S,hS,hmem⟩ := tensor_coordinates_finitely_generated M t
  have htop : S = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨j,rfl⟩ := he x
    simpa [ht] using hmem j
  exact ⟨htop ▸ hS⟩

variable (P : Type u) [AddCommGroup P] [Module R P]

def homFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (P →ₗ[R] A)
  map f := ModuleCat.ofHom
    { toFun := fun g => f.hom.comp g
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }
  map_id A := by ext; rfl
  map_comp f g := by ext; rfl

/-- Ordinary representability implies surjectivity of the canonical product comparison. -/
theorem representable_countableProduct_surjective
    (e : tensorFunctor (R := R) M ≅ homFunctor (R := R) P) :
    Function.Surjective (countableProductMap (R := R) M) := by
  intro y
  let U := ModuleCat.of R (ULift.{u} R)
  let V := ModuleCat.of R (ℕ → ULift.{u} R)
  let h : P →ₗ[R] (ℕ → ULift.{u} R) :=
    LinearMap.pi fun j => (e.app U).toLinearEquiv ((unitEquiv M).symm (y j))
  let t : M ⊗[R] (ℕ → ULift.{u} R) := (e.app V).toLinearEquiv.symm h
  refine ⟨t, funext fun j => ?_⟩
  change unitEquiv M ((LinearMap.lTensor M (LinearMap.proj j)) t) = y j
  suffices hh : (LinearMap.lTensor M (LinearMap.proj j)) t = (unitEquiv M).symm (y j) by
    rw [hh, LinearEquiv.apply_symm_apply]
  apply (e.app U).toLinearEquiv.injective
  have hn := congrArg (fun k => k t) (e.hom.naturality
    (ModuleCat.ofHom (LinearMap.proj j : (ℕ → ULift.{u} R) →ₗ[R] ULift.{u} R)))
  change e.hom.app U ((LinearMap.lTensor M (LinearMap.proj j)) t) =
    (LinearMap.proj j).comp (e.hom.app V t) at hn
  change e.hom.app U ((LinearMap.lTensor M (LinearMap.proj j)) t) = _
  rw [hn]
  change (LinearMap.proj j).comp ((e.app V).toLinearEquiv ((e.app V).toLinearEquiv.symm h)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable {P}

def finiteDualEquiv [Module.Free R M] [Module.Finite R M] (A : Type u)
    [AddCommGroup A] [Module R A] : M ⊗[R] A ≃ₗ[R] (Module.Dual R M →ₗ[R] A) :=
  (TensorProduct.congr (Module.evalEquiv R M) (LinearEquiv.refl R A)).trans
    (dualTensorHomEquiv R (Module.Dual R M) A)

@[simp] theorem finiteDualEquiv_tmul [Module.Free R M] [Module.Finite R M]
    (A : Type u) [AddCommGroup A] [Module R A] (m : M) (a : A) (ℓ : Module.Dual R M) :
    finiteDualEquiv M A (m ⊗ₜ[R] a) ℓ = ℓ m • a := by simp [finiteDualEquiv]

def finiteDualRepresentation [Module.Free R M] [Module.Finite R M] :
    tensorFunctor (R := R) M ≅ homFunctor (R := R) (Module.Dual R M) :=
  NatIso.ofComponents (fun A => (finiteDualEquiv M A).toModuleIso) (fun {A B} f => by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext m a
    simp only [homFunctor, tensorFunctor]
    ext ℓ
    simp)

variable {M} {Q : Type u} [AddCommGroup Q] [Module R Q]

def homIsoOfEquiv (e : P ≃ₗ[R] Q) : homFunctor (R := R) P ≅ homFunctor (R := R) Q :=
  NatIso.ofComponents
    (fun A => (LinearEquiv.arrowCongr e (LinearEquiv.refl R A)).toModuleIso)
    (fun f => by ext; rfl)

/-- Direct covariant Yoneda argument, retaining the contravariant representing-object direction. -/
def representingObjectEquiv (e : homFunctor (R := R) P ≅ homFunctor (R := R) Q) : P ≃ₗ[R] Q := by
  let f : Q →ₗ[R] P := e.hom.app (ModuleCat.of R P) LinearMap.id
  let g : P →ₗ[R] Q := e.inv.app (ModuleCat.of R Q) LinearMap.id
  have hgf : g.comp f = LinearMap.id := by
    have hn := congrArg (fun k => k (LinearMap.id : P →ₗ[R] P))
      (e.hom.naturality (ModuleCat.ofHom g))
    change e.hom.app (ModuleCat.of R Q) g = g.comp f at hn
    rw [← hn]
    exact congrArg (fun k => k (LinearMap.id : Q →ₗ[R] Q)) (e.inv_hom_id_app (ModuleCat.of R Q))
  have hfg : f.comp g = LinearMap.id := by
    have hn := congrArg (fun k => k (LinearMap.id : Q →ₗ[R] Q))
      (e.inv.naturality (ModuleCat.ofHom f))
    change e.inv.app (ModuleCat.of R P) f = f.comp g at hn
    rw [← hn]
    exact congrArg (fun k => k (LinearMap.id : P →ₗ[R] P)) (e.hom_inv_id_app (ModuleCat.of R P))
  exact LinearEquiv.ofLinear g f hgf hfg

theorem all_representing_objects [Module.Free R M] [Module.Finite R M] :
    Nonempty (tensorFunctor (R := R) M ≅ homFunctor (R := R) P) ↔
    Nonempty (P ≃ₗ[R] Module.Dual R M) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨representingObjectEquiv (e.symm.trans (finiteDualRepresentation M))⟩
  · rintro ⟨e⟩
    exact ⟨(finiteDualRepresentation M).trans (homIsoOfEquiv e.symm)⟩

end MathGauge.TensorClassification
