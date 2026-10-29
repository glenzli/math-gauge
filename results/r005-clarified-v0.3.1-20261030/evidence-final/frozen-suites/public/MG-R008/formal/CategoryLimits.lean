import TensorLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Countable

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Limits TensorProduct

universe u
namespace MathGauge.TensorClassification
variable {R : Type} [CommRing R]
variable {J : Type u} [Category.{u} J]

/-- Instantiation of the compatible-family construction on every arrow of an actual functor. -/
def categoryDiagram (D : J ⥤ ModuleCat.{u} R) :
    ModuleDiagram R J (Σ i j : J, i ⟶ j) where
  obj := D.obj
  source f := f.1
  target f := f.2.1
  map f := (D.map f.2.2).hom

def categoryCone (D : J ⥤ ModuleCat.{u} R) : Cone D where
  pt := ModuleCat.of R (categoryDiagram D).compatible
  π :=
    { app j := ModuleCat.ofHom ((categoryDiagram D).projection j)
      naturality := fun i j f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (x.2 ⟨i,j,f⟩).symm }

def categoryLift (D : J ⥤ ModuleCat.{u} R) (s : Cone D) :
    s.pt →ₗ[R] (categoryDiagram D).compatible :=
  (LinearMap.pi fun j => (s.π.app j).hom).codRestrict _ (by
    intro x ⟨i,j,f⟩
    exact (congrArg (fun h => h x) (s.π.naturality f)).symm)

def categoryConeIsLimit (D : J ⥤ ModuleCat.{u} R) : IsLimit (categoryCone D) where
  lift s := ModuleCat.ofHom (categoryLift D s)
  fac s j := rfl
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext j
    exact congrArg (fun h => h x) (hm j)

variable (M : Type u) [AddCommGroup M] [Module R M]

def tensorCategoryCompatibleEquiv (D : J ⥤ ModuleCat.{u} R) :
    ((categoryDiagram D).tensor M).compatible ≃ₗ[R]
      (categoryDiagram (D ⋙ tensorFunctor (R := R) M)).compatible :=
  LinearEquiv.refl R _

/-- The isomorphism here is built from the canonical comparison, so its legs are the
tensor images of the original limit projections. -/
def categoryTensorConeIsLimit (D : J ⥤ ModuleCat.{u} R)
    (h : Function.Bijective ((categoryDiagram D).comparison M)) :
    IsLimit ((tensorFunctor (R := R) M).mapCone (categoryCone D)) := by
  let e := (LinearEquiv.ofBijective ((categoryDiagram D).comparison M) h).trans
    (tensorCategoryCompatibleEquiv M D)
  refine
    { lift := fun s => ModuleCat.ofHom (e.symm.toLinearMap.comp (categoryLift _ s))
      fac := ?_
      uniq := ?_ }
  · intro s j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun z => z.1 j) (e.apply_symm_apply (categoryLift _ s x))
    exact hh
  · intro s m hm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply e.injective
    change e (m x) = e (e.symm (categoryLift _ s x))
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext j
    exact congrArg (fun h => h x) (hm j)

theorem compatible_comparison_implies_preservesLimit (D : J ⥤ ModuleCat.{u} R)
    (h : Function.Bijective ((categoryDiagram D).comparison M)) :
    PreservesLimit D (tensorFunctor (R := R) M) :=
  preservesLimit_of_preserves_limit_cone (categoryConeIsLimit D)
    (categoryTensorConeIsLimit M D h)

theorem representation_preservesLimit {P : Type u} [AddCommGroup P] [Module R P]
    (e : tensorFunctor (R := R) M ≅ homFunctor (R := R) P)
    (D : J ⥤ ModuleCat.{u} R) : PreservesLimit D (tensorFunctor (R := R) M) :=
  compatible_comparison_implies_preservesLimit M D
    ((categoryDiagram D).representation_comparison_bijective M e)

/-- Countable means countably many objects and countably many arrows. -/
def PreservesCountableLimits (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) : Prop :=
  ∀ (I : Type u) [Category.{u} I] [Countable I]
    [Countable (Σ i j : I, i ⟶ j)] (D : I ⥤ ModuleCat.{u} R), PreservesLimit D F

def discreteScalarDiagram : Discrete (ULift.{u} ℕ) ⥤ ModuleCat.{u} R :=
  Discrete.functor fun _ => ModuleCat.of R (ULift.{u} R)

def scalarProductCone : Cone (discreteScalarDiagram (R := R)) where
  pt := ModuleCat.of R (ℕ → ULift.{u} R)
  π := Discrete.natTrans fun j => ModuleCat.ofHom (LinearMap.proj j.as.down)

def scalarProductConeIsLimit : IsLimit (scalarProductCone.{u} (R := R)) where
  lift s := ModuleCat.ofHom (LinearMap.pi fun n => (s.π.app ⟨ULift.up n⟩).hom)
  fac s j := rfl
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    exact congrArg (fun h => h x) (hm ⟨ULift.up n⟩)

theorem categorical_countable_limits_implies_product_surjective
    (h : PreservesCountableLimits (tensorFunctor (R := R) M)) :
    Function.Surjective (countableProductMap (R := R) M) := by
  letI := h _ (discreteScalarDiagram (R := R))
  let hL := isLimitOfPreserves (tensorFunctor (R := R) M) (scalarProductConeIsLimit.{u} (R := R))
  intro y
  let s : Cone (discreteScalarDiagram (R := R) ⋙ tensorFunctor (R := R) M) :=
    { pt := ModuleCat.of R (ULift.{u} R)
      π := Discrete.natTrans fun j => ModuleCat.ofHom
            ((LinearMap.toSpanSingleton R (M ⊗[R] ULift.{u} R)
              ((unitEquiv M).symm (y j.as.down))).comp ULift.moduleEquiv.toLinearMap) }
  refine ⟨hL.lift s (ULift.up 1), funext fun j => ?_⟩
  have hj := congrArg (fun f => f (ULift.up 1)) (hL.fac s ⟨ULift.up j⟩)
  change (LinearMap.lTensor M (LinearMap.proj j)) (hL.lift s (ULift.up 1)) =
    (1 : R) • (unitEquiv M).symm (y j) at hj
  simp only [one_smul] at hj
  change unitEquiv M ((LinearMap.lTensor M
    (LinearMap.proj j : (ℕ → ULift.{u} R) →ₗ[R] ULift.{u} R))
      (hL.lift s (ULift.up 1))) = y j
  rw [hj, LinearEquiv.apply_symm_apply]

end MathGauge.TensorClassification
