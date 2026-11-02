import UniformOrbits
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.ZMod.Basic

noncomputable section
open Set Function Polynomial
open MathGauge.R102

namespace MathGauge.GR102

abbrev F₂ := ZMod 2
abbrev ShiftSpace := ℕ →₀ F₂
abbrev CounterSpace := ShiftSpace × F₂

def shift : Module.End F₂ ShiftSpace := Finsupp.lcomapDomain Nat.succ Nat.succ_injective

theorem shift_apply (x : ShiftSpace) (i : ℕ) : shift x i = x (i + 1) := rfl

theorem shift_pow (n : ℕ) (x : ShiftSpace) (i : ℕ) : (shift ^ n) x i = x (i + n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change shift ((shift ^ n) x) i = _
      rw [shift_apply, ih]
      congr 1
      omega

theorem shift_locally_nilpotent (x : ShiftSpace) : ∃ n, (shift ^ n) x = 0 := by
  classical
  refine ⟨x.support.sup id + 1, ?_⟩
  ext i
  rw [shift_pow]
  apply Finsupp.notMem_support_iff.mp
  intro hi
  have hb := Finset.le_sup (f := id) hi
  simp only [id_eq] at hb
  omega

def backward : Module.End F₂ CounterSpace where
  toFun x := (shift x.1, x.2)
  map_add' x y := by ext <;> simp [map_add]
  map_smul' a x := by ext <;> simp [map_smul]

theorem backward_pow (n : ℕ) (x : CounterSpace) :
    (backward ^ n) x = ((shift ^ n) x.1, x.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change backward ((backward ^ n) x) = (shift ((shift ^ n) x.1), x.2)
      rw [ih]
      rfl

theorem backward_finite : PointwiseFiniteOrbit backward := by
  intro x
  obtain ⟨n, hn⟩ := shift_locally_nilpotent x.1
  apply finite_orbit_of_eventual backward x n 1 (by omega)
  apply periodic_of_pow
  have ht : (backward ^ n) x = (0, x.2) := by rw [backward_pow, hn]
  rw [ht, pow_one]
  change (shift 0, x.2) = (0, x.2)
  rw [map_zero]

theorem backward_projection (x : CounterSpace) :
    projection backward backward_finite x = (0, x.2) := by
  apply decomposition_unique (projection_spec backward backward_finite x).1
    (projection_spec backward backward_finite x).2
  · exact ⟨1, by omega, periodic_of_pow (by simp [backward, map_zero])⟩
  · obtain ⟨n, hn⟩ := shift_locally_nilpotent x.1
    refine ⟨n, ?_⟩
    rw [backward_pow]
    simpa using congrArg (fun a : ShiftSpace => (a, (0 : F₂))) hn

def atZero : CounterSpace →ₗ[F₂] F₂ :=
  (Finsupp.lapply 0).comp (LinearMap.fst F₂ ShiftSpace F₂)

/-- All coefficients, not merely all powers, are detected on finite-support basis vectors. -/
theorem polynomial_coefficient (p : F₂[X]) (k : ℕ) :
    atZero (aeval backward p (Finsupp.single k 1, 0)) = p.coeff k := by
  classical
  rw [aeval_endomorphism]
  simp only [Polynomial.sum, Finsupp.sum, map_sum, map_smul]
  simp only [atZero, LinearMap.comp_apply, LinearMap.fst_apply, Finsupp.lapply_apply,
    backward_pow, shift_pow, zero_add, Finsupp.single_apply, smul_eq_mul]
  by_cases hk : k ∈ p.support
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · exact fun h => (h hk).elim
  · rw [Finset.sum_eq_zero]
    · exact (Polynomial.notMem_support_iff.mp hk).symm
    · intro b hb
      have hbk : k ≠ b := fun he => hk (he ▸ hb)
      simp [hbk]

theorem no_polynomial_projection :
    ¬ ∃ p : F₂[X], aeval backward p = projection backward backward_finite := by
  rintro ⟨p, hp⟩
  have hpzero : p = 0 := by
    ext k
    have he := LinearMap.congr_fun hp (Finsupp.single k 1, 0)
    have he' := congrArg atZero he
    rw [polynomial_coefficient, backward_projection] at he'
    simpa [atZero] using he'
  subst p
  have he := LinearMap.congr_fun hp ((0 : ShiftSpace), (1 : F₂))
  rw [backward_projection] at he
  have hc := congrArg Prod.snd he
  norm_num at hc

def twice : Module.End ℚ ℚ := (2 : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)

theorem twice_pow (n : ℕ) (x : ℚ) : (twice ^ n) x = 2 ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change 2 * (twice ^ n) x = _
      rw [ih, pow_succ]
      ring

theorem twice_nil : nilpart twice = ⊥ := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    rw [twice_pow, mul_eq_zero] at hn
    exact hn.resolve_left (pow_ne_zero _ (by norm_num))
  · intro hx
    exact ⟨0, by simpa using hx⟩

theorem twice_periodic : periodicpart twice = ⊥ := by
  ext x
  constructor
  · rintro ⟨p, hp, h⟩
    have he : 2 ^ p * x = x := by simpa [twice_pow] using periodic_pow h
    have hpow : (1 : ℚ) < 2 ^ p := one_lt_pow₀ (by norm_num) (by omega)
    have hx : x = 0 := by
      have hprod : (2 ^ p - 1) * x = 0 := by nlinarith [he]
      exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (ne_of_gt hpow))
    exact hx
  · intro hx
    have : x = 0 := hx
    subst x
    exact (periodicpart twice).zero_mem

theorem finite_orbit_span_twice (x : ℚ) :
    FiniteDimensional ℚ (Submodule.span ℚ (Set.range (fun n : ℕ => (twice ^ n) x))) :=
  inferInstance

theorem twice_not_decomposable :
    ¬ ∀ x : ℚ, ∃ y, y ∈ periodicpart twice ∧ x - y ∈ nilpart twice := by
  intro h
  obtain ⟨y, hy, hn⟩ := h 1
  rw [twice_periodic] at hy
  rw [twice_nil] at hn
  change y = 0 at hy
  change 1 - y = 0 at hn
  norm_num [hy] at hn

end MathGauge.GR102
