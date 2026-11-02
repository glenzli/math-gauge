import TowerBoundaries

noncomputable section
open Representation Polynomial
namespace MathGauge.TowerBoundaries
universe u
variable {k : Type u} [Field k]
variable {A : Type u} [AddCommGroup A] [Module k A]

/-- Actual short exact rows used in the two split boundary towers. -/
theorem product_row : Function.Injective (LinearMap.inl k A k) ∧
    LinearMap.range (LinearMap.inl k A k)=LinearMap.ker (LinearMap.snd k A k) ∧
    Function.Surjective (LinearMap.snd k A k) := by
  refine ⟨fun a b h => congrArg Prod.fst h, ?_, ?_⟩
  · ext x; constructor
    · rintro ⟨a,rfl⟩; rfl
    · intro hx; exact ⟨x.1,Prod.ext rfl hx.symm⟩
  · intro c; exact ⟨(0,c),rfl⟩

theorem collapse_diagram :
    collapse.comp (LinearMap.inl k k k)=(LinearMap.inl k k k).comp (0 : k →ₗ[k] k) ∧
    (LinearMap.snd k k k).comp collapse=LinearMap.snd k k k := by
  constructor <;> ext x <;> simp [collapse]

def polynomialKernel : k[X] →ₗ[k] k[X] :=
  { toFun := fun p => X*p
    map_add' := by intros; simp [mul_add]
    map_smul' := by intros; simp [mul_smul_comm] }

theorem polynomial_diagram :
    polynomialTransition.comp (LinearMap.inl k k[X] k)=
      (LinearMap.inl k k[X] k).comp polynomialKernel ∧
    (LinearMap.snd k k[X] k).comp polynomialTransition=LinearMap.snd k k[X] k := by
  constructor <;> ext x <;> simp [polynomialTransition,polynomialKernel]

theorem polynomial_row_split :
    (LinearMap.snd k k[X] k).comp (LinearMap.inr k k[X] k)=LinearMap.id := rfl

theorem shear_diagram (v : k) :
    (shear v).toLinearMap.comp (LinearMap.inl k k k)=LinearMap.inl k k k ∧
    (LinearMap.snd k k k).comp (shear v).toLinearMap=LinearMap.snd k k k := by
  constructor <;> ext x <;> simp [shear]

theorem modular_row : Function.Injective modularInclusion ∧
    LinearMap.range modularInclusion.toLinearMap=LinearMap.ker modularQuotient.toLinearMap ∧
    Function.Surjective modularQuotient := product_row

end MathGauge.TowerBoundaries
