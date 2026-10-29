import CompletionFailure
import Mathlib.RingTheory.AdicCompletion.Completeness

noncomputable section
namespace MathGauge.CompletionStructure
open MathGauge.CompletionFailure
open scoped Pointwise
universe u v w z
variable {R : Type u} [CommRing R] (t : R)
variable {M : Type v} {N : Type w} {P : Type z}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

def canonical : M →ₗ[R] completion t M where
  toFun x := ⟨fun n => (powerSub t M n).mkQ x,by intro n m h; rfl⟩
  map_add' x y := by apply Subtype.ext;funext n;exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext;funext n;exact map_smul _ _ _

def eval (n : ℕ) : completion t M →ₗ[R] Level t M n :=
  (LinearMap.proj n).comp (completion t M).subtype

@[simp] theorem eval_canonical (n : ℕ) (x : M) : eval t n (canonical t x)=(powerSub t M n).mkQ x := rfl

@[simp] theorem completed_map_canonical (f : M →ₗ[R] N) (x : M) :
    completionMap t M f (canonical t x)=canonical t (f x) := rfl

theorem completionMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    completionMap t M (g.comp f)=(completionMap t N g).comp (completionMap t M f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change levelMap t M (g.comp f) n (x.val n)=levelMap t N g n (levelMap t M f n (x.val n))
  induction x.val n using Submodule.Quotient.induction_on (powerSub t M n) with
  | H a => rfl

@[simp] theorem completionMap_id : completionMap t M (LinearMap.id : M →ₗ[R] M)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change levelMap t M LinearMap.id n (x.val n)=x.val n
  induction x.val n using Submodule.Quotient.induction_on (powerSub t M n) with
  | H a => rfl

@[simp] theorem completionMap_zero : completionMap t M (0 : M →ₗ[R] N)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change levelMap t M 0 n (x.val n)=0
  induction x.val n using Submodule.Quotient.induction_on (powerSub t M n) with
  | H a => exact (powerSub t N n).mkQ.map_zero

theorem completionMap_add (f g : M →ₗ[R] N) :
    completionMap t M (f+g)=completionMap t M f+completionMap t M g := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change levelMap t M (f+g) n (x.val n)=levelMap t M f n (x.val n)+levelMap t M g n (x.val n)
  induction x.val n using Submodule.Quotient.induction_on (powerSub t M n) with
  | H a => exact (powerSub t N n).mkQ.map_add (f a) (g a)

def completedEquiv (e : M ≃ₗ[R] N) : completion t M ≃ₗ[R] completion t N :=
  { completionMap t M e.toLinearMap with
    invFun := completionMap t N e.symm.toLinearMap
    left_inv := fun x => by
      change ((completionMap t N e.symm.toLinearMap).comp (completionMap t M e.toLinearMap)) x=x
      rw [← completionMap_comp,e.symm_comp,completionMap_id,LinearMap.id_apply]
    right_inv := fun x => by
      change ((completionMap t M e.toLinearMap).comp (completionMap t N e.symm.toLinearMap)) x=x
      rw [← completionMap_comp,e.comp_symm,completionMap_id,LinearMap.id_apply] }

/-- Exact equality of the principal-ideal filtration and the task's t^nM. -/
theorem principal_power (n : ℕ) :
    (Ideal.span {t})^n • (⊤ : Submodule R M)=powerSub t M n := by
  rw [Ideal.span_singleton_pow,Submodule.ideal_span_singleton_smul]
  ext x
  change x∈(t^n) • (⊤ : Submodule R M) ↔ ∃ y,(t^n) • y=x
  simp only [Submodule.mem_smul_pointwise_iff_exists,Submodule.mem_top,true_and]

end MathGauge.CompletionStructure
