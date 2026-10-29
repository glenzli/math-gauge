import TowerAndLifts
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
open Polynomial
namespace MathGauge.GR104
open MathGauge.R104
abbrev Base := ℚ[X]
abbrev Dual := TrivSqZeroExt Base Base

def dualAug : Dual →+* Base where
  toFun := TrivSqZeroExt.fst
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def derivativeFun (a : Dual) : Dual := (a.fst, X * a.snd + derivative a.fst)

theorem derivativeFun_zero : derivativeFun 0 = 0 := by
  apply TrivSqZeroExt.ext <;> simp [derivativeFun]
theorem derivativeFun_one : derivativeFun 1 = 1 := by
  apply TrivSqZeroExt.ext <;> simp [derivativeFun]
theorem derivativeFun_add (a b : Dual) : derivativeFun (a+b) = derivativeFun a + derivativeFun b := by
  apply TrivSqZeroExt.ext
  · rfl
  · change X * (a.snd + b.snd) + derivative (a.fst+b.fst) =
      (X*a.snd+derivative a.fst)+(X*b.snd+derivative b.fst)
    rw [derivative_add]
    ring

theorem derivative_polynomial_product (s t m n : Base) :
    X*(s*n + m*t)+derivative (s*t) = s*(X*n+derivative t)+(X*m+derivative s)*t := by
  rw [derivative_mul]
  ring

theorem derivativeFun_mul (a b : Dual) : derivativeFun (a*b) = derivativeFun a * derivativeFun b := by
  apply TrivSqZeroExt.ext
  · simp only [derivativeFun, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mk]
  · simp only [derivativeFun, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_mk,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mk, smul_eq_mul, op_smul_eq_mul]
    exact derivative_polynomial_product a.fst b.fst a.snd b.snd

def derivativeTransition : Dual →+* Dual where
  toFun := derivativeFun
  map_zero' := derivativeFun_zero
  map_one' := derivativeFun_one
  map_add' := derivativeFun_add
  map_mul' := derivativeFun_mul

theorem dualAug_surjective : Function.Surjective dualAug :=
  fun s => ⟨(s, 0), rfl⟩

theorem dualKernel_square_zero (a b : Dual) (ha : dualAug a = 0) (hb : dualAug b = 0) :
    a * b = 0 := by
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  apply TrivSqZeroExt.ext <;>
    simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha, hb]

theorem dualKernel_nil (a : Dual) (ha : dualAug a = 0) : IsNilpotent a :=
  ⟨2, by simpa [pow_two] using dualKernel_square_zero a a ha ha⟩

theorem dualAug_transition (a : Dual) : dualAug (derivativeTransition a) = dualAug a := rfl

theorem dualAug_power (n : ℕ) (a : Dual) :
    dualAug ((derivativeTransition ^ n) a) = dualAug a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change dualAug (derivativeTransition ((derivativeTransition ^ n) a)) = dualAug a
      exact ih

def derivativeSystem : System ℕ (fun _ => Dual) Base where
  transition := fun {i j} _ => derivativeTransition ^ (j - i)
  transition_id i a := by simp
  transition_comp := by
    intro i j k hij hjk a
    change ((derivativeTransition ^ (j-i)) * (derivativeTransition ^ (k-j))) a = _
    rw [← pow_add]
    congr 2
    omega
  augmentation := fun _ => dualAug
  augmentation_surjective := fun _ => dualAug_surjective
  augmentation_transition := fun h a => dualAug_power _ a
  nil_kernel := fun _ => dualKernel_nil

theorem derivativeSystem_adjacent (a : derivativeSystem.Limit) (n : ℕ) :
    derivativeTransition (a.val (n+1)) = a.val n := by
  have h := a.property n (n+1) (by omega)
  simpa [derivativeSystem] using h

theorem polynomial_recurrence_impossible (m : ℕ → Base)
    (h : ∀ n, m n = X * m (n+1) + 1) : False := by
  have hc : ∀ k n, (m n).coeff k = 1 := by
    intro k
    induction k with
    | zero =>
        intro n
        have he := congrArg (fun p : Base => p.coeff 0) (h n)
        simpa using he
    | succ k ih =>
        intro n
        have he := congrArg (fun p : Base => p.coeff (k+1)) (h n)
        simpa [coeff_X_mul, coeff_one, ih] using he
  have hz : (m 0).coeff ((m 0).natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have ho := hc ((m 0).natDegree + 1) 0
  exact zero_ne_one (hz.symm.trans ho)

theorem variable_has_no_coherent_lift :
    ¬ ∃ a : derivativeSystem.Limit, derivativeSystem.limit_augmentation 0 a = X := by
  rintro ⟨a, ha⟩
  have hfst (n : ℕ) : (a.val n).fst = X := by
    have he := derivativeSystem.augmentation_independent
      (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩) n 0 a
    exact he.trans ha
  apply polynomial_recurrence_impossible (fun n => (a.val n).snd)
  intro n
  have he := congrArg TrivSqZeroExt.snd (derivativeSystem_adjacent a n)
  simpa [derivativeTransition, derivativeFun, hfst] using he.symm

theorem derivative_limit_not_surjective :
    ¬ Function.Surjective (derivativeSystem.limit_augmentation 0) :=
  fun h => variable_has_no_coherent_lift (h X)

/-- All hypotheses of S2 hold, hence failure of general element lifting does not
    prevent unique idempotent lifting or finite orthogonal decompositions. -/
theorem derivative_idempotents_still_lift (e : Base) (he : IsIdempotentElem e) :
    ∃! a : derivativeSystem.Limit,
      IsIdempotentElem a ∧ derivativeSystem.limit_augmentation 0 a = e :=
  derivativeSystem.unique_limit_lift
    (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩) 0 e he
end MathGauge.GR104
