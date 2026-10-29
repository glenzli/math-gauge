import TowerFiniteStage
import TowerFiniteLimits
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Module CategoryTheory MathGauge.TensorClassification

namespace MathGauge.Tower.Examples
open FreeTower

@[reducible] def doublingTower : FreeTower ℤ where
  stage _ := ModuleCat.of ℤ ℤ
  step _ := (2 : ℤ) • LinearMap.id
  free _ := inferInstance
  finite _ := inferInstance

theorem int_linear_apply (ℓ : ℤ →ₗ[ℤ] ℤ) (z : ℤ) : ℓ z = z * ℓ 1 := by
  simpa only [smul_eq_mul,mul_one] using ℓ.map_smul z 1

theorem doubling_transition_weighted (n m : ℕ) (h : n ≤ m) (x : ℤ) :
    (2 : ℤ)^n * doublingTower.transition n m h x = (2 : ℤ)^m * x := by
  induction m,h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    rw [doublingTower.transition_succ n m h]
    change (2 : ℤ)^n * doublingTower.transition n m h (2*x) = (2 : ℤ)^(m+1)*x
    have hs := (doublingTower.transition n m h).map_smul (2 : ℤ) x
    simp only [smul_eq_mul] at hs
    rw [hs,pow_succ]
    calc
      _ = 2 * ((2 : ℤ)^n * doublingTower.transition n m h x) := by ring
      _ = 2 * ((2 : ℤ)^m * x) := by rw [ih]
      _ = _ := by ring

def dyadicStageMap (n : ℕ) : Module.Dual ℤ ℤ →ₗ[ℤ] ℚ where
  toFun ℓ := (ℓ 1 : ℚ) / (2 : ℚ)^n
  map_add' f g := by simp [add_div]
  map_smul' z f := by simp [zsmul_eq_mul,mul_div_assoc]

theorem dyadicStageMap_compatible (n m : ℕ) (h : n ≤ m) (ℓ : Module.Dual ℤ ℤ) :
    dyadicStageMap m (doublingTower.homTransition ℤ n m h ℓ) = dyadicStageMap n ℓ := by
  have hw := doubling_transition_weighted n m h 1
  have hi : (2 : ℤ)^n * (doublingTower.homTransition ℤ n m h ℓ) 1 = (2 : ℤ)^m * ℓ 1 := by
    change (2 : ℤ)^n * ℓ (doublingTower.transition n m h 1) = _
    rw [int_linear_apply]
    calc
      _ = ((2 : ℤ)^n * doublingTower.transition n m h 1) * ℓ 1 := by ring
      _ = ((2 : ℤ)^m * 1) * ℓ 1 := by rw [hw]
      _ = _ := by ring
  have hq : (2 : ℚ)^n * ((doublingTower.homTransition ℤ n m h ℓ) 1 : ℚ) =
      (2 : ℚ)^m * (ℓ 1 : ℚ) := by exact_mod_cast hi
  change ((doublingTower.homTransition ℤ n m h ℓ) 1 : ℚ) / (2 : ℚ)^m =
    (ℓ 1 : ℚ) / (2 : ℚ)^n
  field_simp
  simpa only [mul_comm] using hq

def doublingToRat : doublingTower.Invariant →ₗ[ℤ] ℚ :=
  Module.DirectLimit.lift ℤ ℕ _ (doublingTower.homTransition ℤ) dyadicStageMap dyadicStageMap_compatible

@[simp] theorem doublingToRat_of (n : ℕ) (ℓ : Module.Dual ℤ ℤ) :
    doublingToRat (doublingTower.recordOf ℤ n ℓ) = (ℓ 1 : ℚ) / (2 : ℚ)^n :=
  Module.DirectLimit.lift_of _ _ _

theorem dyadicStageMap_injective (n : ℕ) : Function.Injective (dyadicStageMap n) := by
  intro f g h
  have hh := congrArg (fun q : ℚ => q * (2 : ℚ)^n) h
  change (f 1 : ℚ) / (2 : ℚ)^n * (2 : ℚ)^n = (g 1 : ℚ) / (2 : ℚ)^n * (2 : ℚ)^n at hh
  have hn : (2 : ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [div_mul_cancel₀ _ hn] at hh
  have he : f 1 = g 1 := by exact_mod_cast hh
  apply LinearMap.ext
  intro z
  rw [int_linear_apply f z,int_linear_apply g z,he]

theorem doublingToRat_injective : Function.Injective doublingToRat := by
  intro x y h
  obtain ⟨n,f,g,rfl,rfl⟩ := Module.DirectLimit.exists_of₂ x y
  have he : dyadicStageMap n f = dyadicStageMap n g := by
    simpa only [doublingToRat,Module.DirectLimit.lift_of] using h
  rw [dyadicStageMap_injective n he]

/-- The usual additive group ℤ[1/2], realized as the actual dyadic-rational
submodule of ℚ rather than as an abstract localization interface. -/
def dyadicIntegers : Submodule ℤ ℚ where
  carrier := {q | ∃ n : ℕ, ∃ z : ℤ, q = (z : ℚ) / (2 : ℚ)^n}
  zero_mem' := ⟨0,0,by norm_num⟩
  add_mem' := by
    rintro x y ⟨n,z,rfl⟩ ⟨m,w,rfl⟩
    refine ⟨n+m,z*2^m+w*2^n,?_⟩
    push_cast
    rw [pow_add]
    field_simp
  smul_mem' := by
    rintro k x ⟨n,z,rfl⟩
    refine ⟨n,k*z,?_⟩
    simp [zsmul_eq_mul,mul_div_assoc]

theorem doublingToRat_mem (x : doublingTower.Invariant) : doublingToRat x ∈ dyadicIntegers := by
  obtain ⟨n,ℓ,rfl⟩ := doublingTower.record_exists ℤ x
  exact ⟨n,ℓ 1,doublingToRat_of n ℓ⟩

def doublingToDyadic : doublingTower.Invariant →ₗ[ℤ] dyadicIntegers :=
  doublingToRat.codRestrict dyadicIntegers doublingToRat_mem

theorem doublingToDyadic_bijective : Function.Bijective doublingToDyadic := by
  constructor
  · intro x y h
    apply doublingToRat_injective
    exact congrArg Subtype.val h
  · rintro ⟨q,n,z,hq⟩
    refine ⟨doublingTower.recordOf ℤ n (z • LinearMap.id),?_⟩
    apply Subtype.ext
    change doublingToRat (doublingTower.recordOf ℤ n (z • LinearMap.id)) = q
    rw [doublingToRat_of,hq]
    simp

def doublingInvariantEquivDyadic : doublingTower.Invariant ≃ₗ[ℤ] dyadicIntegers :=
  LinearEquiv.ofBijective doublingToDyadic doublingToDyadic_bijective

/-- The next denominator gives an element absent from the image of every fixed
finite stage. This is the bounded-denominator obstruction to finite generation. -/
theorem doubling_stage_not_surjective (n : ℕ) :
    ¬ Function.Surjective (doublingTower.recordOf ℤ n) := by
  intro h
  obtain ⟨ℓ,hℓ⟩ := h (doublingTower.recordOf ℤ (n+1) LinearMap.id)
  have hh := congrArg doublingToRat hℓ
  rw [doublingToRat_of,doublingToRat_of] at hh
  change (ℓ 1 : ℚ) / (2 : ℚ)^n = 1 / (2 : ℚ)^(n+1) at hh
  have hn : (2 : ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_succ] at hh
  have he : (2 : ℚ) * (ℓ 1 : ℚ) = 1 := by
    field_simp at hh
    simpa only [mul_comm] using hh
  have hi : (2 : ℤ) * ℓ 1 = 1 := by exact_mod_cast he
  omega

theorem doubling_invariant_not_finite : ¬ Module.Finite ℤ doublingTower.Invariant := by
  intro h
  obtain ⟨n,hn⟩ := doublingTower.finite_invariant_iff_stage_surjective.mp h
  exact doubling_stage_not_surjective n hn

theorem doubling_not_representable : ¬ doublingTower.Representable :=
  fun h => doubling_invariant_not_finite (doublingTower.representable_iff_finite.mp h)

theorem doubling_not_preserves_countable_limits :
    ¬ PreservesCountableLimits doublingTower.recordFunctor :=
  fun h => doubling_invariant_not_finite (doublingTower.countable_limits_iff_finite.mp h)

theorem dyadicIntegers_not_finitely_generated : ¬ Module.Finite ℤ dyadicIntegers := by
  intro h
  letI := h
  apply doubling_invariant_not_finite
  exact Module.Finite.of_surjective doublingInvariantEquivDyadic.symm.toLinearMap
    doublingInvariantEquivDyadic.symm.surjective

end MathGauge.Tower.Examples
