import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Countable
import Mathlib.Algebra.Category.ModuleCat.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local ext high] TensorProduct.ext
open TensorProduct Module
open Module.DirectLimit

universe u v
namespace MathGauge.Tower

/-- Only the data in MG-R008: arbitrary adjacent maps between finite free stages. -/
structure FreeTower (R : Type) [CommRing R] where
  stage : ℕ → ModuleCat.{u} R
  step : ∀ n, stage (n+1) →ₗ[R] stage n
  free : ∀ n, Module.Free R (stage n)
  finite : ∀ n, Module.Finite R (stage n)

attribute [instance] FreeTower.free FreeTower.finite

namespace FreeTower

variable {R : Type} [CommRing R]

variable (T : FreeTower.{u} R)

def transition (n m : ℕ) (h : n ≤ m) : T.stage m →ₗ[R] T.stage n :=
  Nat.leRecOn h (fun {k} q => q.comp (T.step k)) LinearMap.id

@[simp] theorem transition_self (n : ℕ) : T.transition n n le_rfl = LinearMap.id :=
  Nat.leRecOn_self _

theorem transition_succ (n m : ℕ) (h : n ≤ m) :
    T.transition n (m+1) (Nat.le_succ_of_le h) = (T.transition n m h).comp (T.step m) :=
  Nat.leRecOn_succ h _

theorem transition_comp (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    (T.transition n m hnm).comp (T.transition m k hmk) = T.transition n k (hnm.trans hmk) := by
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k h ih =>
    rw [transition_succ T m k h, transition_succ T n k (hnm.trans h),
      ← LinearMap.comp_assoc, ih]

variable (A : Type v) [AddCommGroup A] [Module R A]

def homTransition (n m : ℕ) (h : n ≤ m) :
    (T.stage n →ₗ[R] A) →ₗ[R] (T.stage m →ₗ[R] A) where
  toFun f := f.comp (T.transition n m h)
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl

@[simp] theorem homTransition_apply (n m : ℕ) (h : n ≤ m) (f : T.stage n →ₗ[R] A)
    (x : T.stage m) : T.homTransition A n m h f x = f (T.transition n m h x) := rfl

instance homDirectedSystem : DirectedSystem (fun n => T.stage n →ₗ[R] A)
    (fun n m h => T.homTransition A n m h) where
  map_self n f := by ext x; simp [homTransition]
  map_map k m n hnm hmk f := by
    ext x
    simp only [homTransition_apply]
    exact congrArg f (LinearMap.congr_fun (T.transition_comp n m k hnm hmk) x)

abbrev Record := Module.DirectLimit (fun n => T.stage n →ₗ[R] A) (T.homTransition A)
abbrev Invariant := T.Record R

def recordOf (n : ℕ) : (T.stage n →ₗ[R] A) →ₗ[R] T.Record A :=
  Module.DirectLimit.of R ℕ _ (T.homTransition A) n

@[simp] theorem recordOf_transition (n m : ℕ) (h : n ≤ m) (f : T.stage n →ₗ[R] A) :
    T.recordOf A m (T.homTransition A n m h f) = T.recordOf A n f := of_f

theorem record_exists (x : T.Record A) : ∃ n f, T.recordOf A n f = x := exists_of x

/-- Equality is precisely equality at some common later stage, with no injectivity assumption. -/
theorem record_eq_iff (n m : ℕ) (f : T.stage n →ₗ[R] A) (g : T.stage m →ₗ[R] A) :
    T.recordOf A n f = T.recordOf A m g ↔
    ∃ r, ∃ hnr : n ≤ r, ∃ hmr : m ≤ r,
      T.homTransition A n r hnr f = T.homTransition A m r hmr g := by
  constructor
  · intro h
    have he := congrArg (Module.DirectLimit.linearEquiv (fun n => T.stage n →ₗ[R] A)
      (T.homTransition A)) h
    change Module.DirectLimit.linearEquiv _ _
      (of R ℕ (fun i => T.stage i →ₗ[R] A) (T.homTransition A) n f) =
      Module.DirectLimit.linearEquiv _ _
      (of R ℕ (fun i => T.stage i →ₗ[R] A) (T.homTransition A) m g) at he
    rw [linearEquiv_of, linearEquiv_of] at he
    exact Quotient.exact he
  · rintro ⟨r,hnr,hmr,h⟩
    rw [← T.recordOf_transition A n r hnr f, ← T.recordOf_transition A m r hmr g, h]

variable {A} {B : Type*} [AddCommGroup B] [Module R B]

def recordMap (f : A →ₗ[R] B) : T.Record A →ₗ[R] T.Record B :=
  Module.DirectLimit.map
    (fun n =>
      { toFun := fun g => f.comp g
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun a g => by ext x; exact f.map_smul a (g x) })
    (fun n m h => by ext; rfl)

@[simp] theorem recordMap_of (f : A →ₗ[R] B) (n : ℕ) (g : T.stage n →ₗ[R] A) :
    T.recordMap f (T.recordOf A n g) = T.recordOf B n (f.comp g) := map_apply_of _ _ _

@[simp] theorem recordMap_id : T.recordMap (LinearMap.id : A →ₗ[R] A) = LinearMap.id := by
  apply Module.DirectLimit.hom_ext
  intro n
  ext g
  change T.recordMap LinearMap.id (T.recordOf A n g) = T.recordOf A n g
  simp

theorem recordMap_comp {C : Type*} [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    T.recordMap (g.comp f) = (T.recordMap g).comp (T.recordMap f) := by
  apply Module.DirectLimit.hom_ext
  intro n
  ext h
  change T.recordMap (g.comp f) (T.recordOf A n h) =
    T.recordMap g (T.recordMap f (T.recordOf A n h))
  simp [LinearMap.comp_assoc]

variable (A)

def tensorRecordEquiv : T.Invariant ⊗[R] A ≃ₗ[R] T.Record A :=
  (TensorProduct.directLimitLeft (T.homTransition R) A).trans
    (Module.DirectLimit.congr (f' := T.homTransition A) (fun n => dualTensorHomEquiv R (T.stage n) A)
      (fun n m h => by
        ext ℓ a x
        simp [dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, homTransition]))

@[simp] theorem tensorRecordEquiv_of_tmul (n : ℕ) (ℓ : Module.Dual R (T.stage n)) (a : A) :
    T.tensorRecordEquiv A (T.recordOf R n ℓ ⊗ₜ[R] a) =
      T.recordOf A n ((dualTensorHom R (T.stage n) A) (ℓ ⊗ₜ[R] a)) := by
  simp [tensorRecordEquiv, recordOf, congr_apply_of, dualTensorHomEquiv,
    dualTensorHomEquivOfBasis_apply]

theorem tensorRecordEquiv_natural (f : A →ₗ[R] B) :
    (T.recordMap f).comp (T.tensorRecordEquiv A).toLinearMap =
      (T.tensorRecordEquiv B).toLinearMap.comp (LinearMap.lTensor T.Invariant f) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro a
  change T.recordMap f (T.tensorRecordEquiv A (x ⊗ₜ[R] a)) =
    T.tensorRecordEquiv B (x ⊗ₜ[R] f a)
  obtain ⟨n,ℓ,rfl⟩ := T.record_exists R x
  simp only [LinearMap.comp_apply, tensorRecordEquiv_of_tmul, recordMap_of,
    LinearMap.lTensor_tmul]
  congr 1
  ext y
  simp [dualTensorHom_apply]

instance dualCountable [Countable R] (n : ℕ) : Countable (Module.Dual R (T.stage n)) := by
  let b := Module.Free.chooseBasis R (Module.Dual R (T.stage n))
  exact b.repr.injective.countable

instance invariantCountable [Countable R] : Countable T.Invariant := by
  let f : (Σ n, Module.Dual R (T.stage n)) → T.Invariant := fun p => T.recordOf R p.1 p.2
  apply Function.Surjective.countable (f := f)
  intro x
  obtain ⟨n,ℓ,h⟩ := T.record_exists R x
  exact ⟨⟨n,ℓ⟩,h⟩

instance invariantTorsionFree [IsDomain R] : Module.IsTorsionFree R T.Invariant := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro k x hx
  by_cases hk : k = 0
  · exact Or.inl hk
  right
  obtain ⟨n,ℓ,rfl⟩ := T.record_exists R x
  have hz : T.recordOf R n (k • ℓ) = 0 := by simpa using hx
  obtain ⟨m,hnm,hm⟩ := Module.DirectLimit.of.zero_exact hz
  have hzero : T.homTransition R n m hnm ℓ = 0 := by
    have hsmul : k • T.homTransition R n m hnm ℓ = 0 := by simpa using hm
    exact (smul_eq_zero.mp hsmul).resolve_left hk
  rw [← T.recordOf_transition R n m hnm ℓ, hzero, map_zero]

end FreeTower
end MathGauge.Tower
