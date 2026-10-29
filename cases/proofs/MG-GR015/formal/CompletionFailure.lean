import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

noncomputable section
namespace MathGauge.CompletionFailure
universe u v w

section Completion
variable {R : Type u} [CommRing R] (t : R)
variable (M : Type v) [AddCommGroup M] [Module R M]

def powerSub (n : ℕ) : Submodule R M :=
  LinearMap.range ((t^n) • (LinearMap.id : M →ₗ[R] M))

theorem mem_powerSub (n : ℕ) (x : M) : x ∈ powerSub t M n ↔ ∃ y : M, (t^n) • y=x := Iff.rfl

theorem powerSub_anti {n m : ℕ} (h : n ≤ m) : powerSub t M m ≤ powerSub t M n := by
  rintro x ⟨y,rfl⟩
  refine ⟨(t^(m-n)) • y, ?_⟩
  change (t^n) • ((t^(m-n)) • y) = (t^m) • y
  rw [← mul_smul, ← pow_add, Nat.add_sub_of_le h]

abbrev Level (n : ℕ) := M ⧸ powerSub t M n
def reduce {n m : ℕ} (h : n ≤ m) : Level t M m →ₗ[R] Level t M n :=
  Submodule.factor (powerSub_anti t M h)

@[simp] theorem reduce_mk {n m : ℕ} (h : n ≤ m) (x : M) :
    reduce t M h ((powerSub t M m).mkQ x) = (powerSub t M n).mkQ x := rfl

/-- The actual inverse limit of the adic module quotients, with all transition equations. -/
def completion : Submodule R (∀ n, Level t M n) where
  carrier := {x | ∀ n m (h : n ≤ m), reduce t M h (x m)=x n}
  zero_mem' := by simp
  add_mem' := by rintro x y hx hy n m h; simp [hx n m h, hy n m h]
  smul_mem' := by rintro a x hx n m h; simp [hx n m h]

variable {N : Type w} [AddCommGroup N] [Module R N]
def levelMap (f : M →ₗ[R] N) (n : ℕ) : Level t M n →ₗ[R] Level t N n :=
  (powerSub t M n).mapQ (powerSub t N n) f (by
    rintro x ⟨y,rfl⟩
    exact ⟨f y, by simp⟩)

@[simp] theorem levelMap_mk (f : M →ₗ[R] N) (n : ℕ) (x : M) :
    levelMap t M f n ((powerSub t M n).mkQ x) = (powerSub t N n).mkQ (f x) := rfl

theorem reduce_natural (f : M →ₗ[R] N) {n m : ℕ} (h : n ≤ m) (x : Level t M m) :
    reduce t N h (levelMap t M f m x) = levelMap t M f n (reduce t M h x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  rfl

def completionMap (f : M →ₗ[R] N) : completion t M →ₗ[R] completion t N where
  toFun x := ⟨fun n => levelMap t M f n (x.val n), by
    intro n m h
    rw [reduce_natural, x.property n m h]⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    funext n
    exact (levelMap t M f n).map_add _ _
  map_smul' := by
    intro a x
    apply Subtype.ext
    funext n
    exact (levelMap t M f n).map_smul _ _

end Completion

section Counterexample
variable (k : Type u) [Field k]
abbrev P := Polynomial k
abbrev Free := ℕ →₀ P k
open Polynomial

/-- The injective diagonal map e_n ↦ X^n e_n on an actual countable free module. -/
def diagonal : Free k →ₗ[P k] Free k where
  toFun x :=
    { support := x.support
      toFun := fun n => X^n*x n
      mem_support_toFun := by
        intro n
        simp only [Finsupp.mem_support_iff, ne_eq, mul_eq_zero,
          pow_ne_zero _ (X_ne_zero (R := k)), false_or] }
  map_add' := by intro x y; apply Finsupp.ext; intro n; exact mul_add _ _ _
  map_smul' := by
    intro a x
    apply Finsupp.ext
    intro n
    change X^n*(a*x n)=a*(X^n*x n)
    ring

@[simp] theorem diagonal_apply (x : Free k) (n : ℕ) : diagonal k x n = X^n*x n := rfl

theorem diagonal_injective : Function.Injective (diagonal k) := by
  intro x y h
  apply Finsupp.ext
  intro n
  exact mul_left_cancel₀ (pow_ne_zero _ (X_ne_zero (R := k)))
    (congrArg (fun z : Free k => z n) h)

abbrev Cokernel := Free k ⧸ LinearMap.range (diagonal k)
def quotientMap : Free k →ₗ[P k] Cokernel k := (LinearMap.range (diagonal k)).mkQ

theorem quotient_surjective : Function.Surjective (quotientMap k) := Submodule.mkQ_surjective _

theorem row_exact : Function.Exact (diagonal k) (quotientMap k) := by
  intro x
  exact Submodule.Quotient.mk_eq_zero _

def partialSum (m : ℕ) : Free k := ∑ n ∈ Finset.range m, Finsupp.single n (X^n)

theorem partialSum_apply (m n : ℕ) : partialSum k m n = if n<m then X^n else 0 := by
  classical
  simp [partialSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.mem_range]

theorem partialSum_in_range (m : ℕ) : partialSum k m ∈ LinearMap.range (diagonal k) := by
  classical
  refine ⟨∑ n ∈ Finset.range m, Finsupp.single n 1, ?_⟩
  apply Finsupp.ext
  intro n
  simp [partialSum_apply, Finset.sum_apply, Finsupp.single_apply, Finset.mem_range]

theorem partialSum_difference {n m : ℕ} (h : n ≤ m) :
    partialSum k m-partialSum k n ∈ powerSub (X : P k) (Free k) n := by
  classical
  refine ⟨(∑ j ∈ Finset.Ico n m, Finsupp.single j ((X : P k)^(j-n)) : Free k), ?_⟩
  apply Finsupp.ext
  intro j
  change (X : P k)^n*(∑ i ∈ Finset.Ico n m, Finsupp.single i ((X : P k)^(i-n))) j =
    partialSum k m j-partialSum k n j
  have hs : (∑ i ∈ Finset.Ico n m, Finsupp.single i ((X : P k)^(i-n))) j =
      if n≤j ∧ j<m then (X : P k)^(j-n) else 0 := by
    simp [Finset.sum_apply, Finsupp.single_apply, Finset.mem_Ico]
  rw [hs, partialSum_apply, partialSum_apply]
  by_cases hjn : j<n
  · simp [hjn, lt_of_lt_of_le hjn h, Nat.not_le_of_lt hjn]
  · have hnj : n≤j := Nat.le_of_not_gt hjn
    by_cases hjm : j<m
    · simp [hnj, hjm, hjn, ← pow_add, Nat.add_sub_of_le hnj]
    · simp [hjm, hjn]

/-- The compatible record with finite-stage representative Σ_{i<m}X^i e_i. -/
def witness : completion (X : P k) (Free k) :=
  ⟨fun m => (powerSub (X : P k) (Free k) m).mkQ (partialSum k m), by
    intro n m h
    rw [reduce_mk]
    exact (Submodule.Quotient.eq _).2 (partialSum_difference k h)⟩

theorem witness_in_kernel : completionMap (X : P k) (Free k) (quotientMap k) (witness k)=0 := by
  apply Subtype.ext
  funext n
  change (powerSub (X : P k) (Cokernel k) n).mkQ (quotientMap k (partialSum k n)) = 0
  have h : quotientMap k (partialSum k n)=0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (partialSum_in_range k n)
  rw [h, map_zero]

/-- Coefficients of degree below r vanish in X^r times a module vector. -/
theorem low_coefficient_zero {r d : ℕ} (h : d<r) {x : Free k}
    (hx : x ∈ powerSub (X : P k) (Free k) r) (n : ℕ) : (x n).coeff d=0 := by
  obtain ⟨y,rfl⟩ := hx
  change (X^r*y n).coeff d=0
  rw [coeff_X_pow_mul', if_neg (not_le_of_gt h)]

/-- No coherent preimage exists; its first-level representative would have infinite support. -/
theorem witness_not_in_range : witness k ∉ LinearMap.range
    (completionMap (X : P k) (Free k) (diagonal k)) := by
  rintro ⟨a,ha⟩
  obtain ⟨a1,ha1⟩ := (powerSub (X : P k) (Free k) 1).mkQ_surjective (a.val 1)
  have hconst : ∀ n, (a1 n).coeff 0=1 := by
    intro n
    obtain ⟨an,han⟩ := (powerSub (X : P k) (Free k) (n+1)).mkQ_surjective (a.val (n+1))
    have hcompat := a.property 1 (n+1) (by omega)
    rw [← han, ← ha1, reduce_mk] at hcompat
    have heq : an-a1 ∈ powerSub (X : P k) (Free k) 1 := (Submodule.Quotient.eq _).1 hcompat
    have hc := low_coefficient_zero k (by omega : 0<1) heq n
    have hcn : (an n).coeff 0 = (a1 n).coeff 0 := by
      exact sub_eq_zero.mp (by simpa only [Finsupp.sub_apply, coeff_sub] using hc)
    have himg := congrArg (fun z : completion (X : P k) (Free k) => z.val (n+1)) ha
    change levelMap (X : P k) (Free k) (diagonal k) (n+1) (a.val (n+1)) =
      (powerSub (X : P k) (Free k) (n+1)).mkQ (partialSum k (n+1)) at himg
    rw [← han, levelMap_mk] at himg
    have hd := (Submodule.Quotient.eq _).1 himg
    have hc' := low_coefficient_zero k (by omega : n<n+1) hd n
    have hh : (an n).coeff 0=1 := by
      simpa only [Finsupp.sub_apply, diagonal_apply, partialSum_apply, if_pos (by omega : n<n+1),
        coeff_sub, coeff_X_pow_mul', if_pos (le_refl n), Nat.sub_self, coeff_X_pow_self,
        sub_eq_zero] using hc'
    exact hcn.symm.trans hh
  obtain ⟨n,hn⟩ := Infinite.exists_notMem_finset a1.support
  have hz : a1 n = 0 := Finsupp.notMem_support_iff.1 hn
  have h := hconst n
  rw [hz, coeff_zero] at h
  exact zero_ne_one h

theorem completion_not_exact : ¬ Function.Exact
    (completionMap (X : P k) (Free k) (diagonal k))
    (completionMap (X : P k) (Free k) (quotientMap k)) := by
  intro h
  exact witness_not_in_range k ((h (witness k)).1 (witness_in_kernel k))

/-- All hypotheses and the actual failure of the requested middle exactness, assembled. -/
theorem counterexample :
    Nonempty (Module.Basis ℕ (P k) (Free k)) ∧
    Function.Injective (diagonal k) ∧ Function.Surjective (quotientMap k) ∧
    Function.Exact (diagonal k) (quotientMap k) ∧
    ¬ Function.Exact (completionMap (X : P k) (Free k) (diagonal k))
      (completionMap (X : P k) (Free k) (quotientMap k)) :=
  ⟨⟨Finsupp.basisSingleOne⟩, diagonal_injective k, quotient_surjective k,
    row_exact k, completion_not_exact k⟩

end Counterexample
end MathGauge.CompletionFailure
