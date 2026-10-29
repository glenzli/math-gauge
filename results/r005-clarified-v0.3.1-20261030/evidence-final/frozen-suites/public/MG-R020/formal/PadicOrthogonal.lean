import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace MathGauge.PadicOrthogonal

noncomputable section

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

abbrev R := ℤ_[2]
abbrev M := Matrix (Fin 2) (Fin 2) R

theorem coefficient_dvr : IsDiscreteValuationRing R := inferInstance
theorem coefficient_characteristic_zero : CharZero R := inferInstance
theorem coefficient_complete : IsAdicComplete (IsLocalRing.maximalIdeal R) R := inferInstance

theorem coefficient_maximal_ideal :
    IsLocalRing.maximalIdeal R = Ideal.span {(2 : R)} := PadicInt.maximalIdeal_eq_span_p

theorem five_is_unit : IsUnit (5 : R) := by
  rw [PadicInt.isUnit_iff]
  exact (PadicInt.norm_natCast_eq_one_iff (n := 5)).2 (by norm_num)

noncomputable def fifth : R := ↑(five_is_unit.unit⁻¹)

theorem five_fifth : (5 : R) * fifth = 1 := by
  simp [fifth]

theorem fifth_five : fifth * (5 : R) = 1 := by simpa [mul_comm] using five_fifth

def p : M := !![1, 0; 0, 0]
noncomputable def q : M := !![fifth, 2 * fifth; 2 * fifth, 4 * fifth]
def v : M := !![1, -2; 2, 1]
noncomputable def w : M := !![fifth, 2 * fifth; -(2 * fifth), fifth]

theorem p_symmetric : p.transpose = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem q_symmetric : q.transpose = q := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem p_idempotent : p * p = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, Matrix.mul_apply, Fin.sum_univ_two]

theorem q_idempotent : q * q = q := by
  have h : 5 * fifth ^ 2 = fifth := by linear_combination fifth * five_fifth
  ext i j
  fin_cases i <;> fin_cases j <;> simp [q, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h
  · linear_combination 2 * h
  · linear_combination 2 * h
  · linear_combination 4 * h

theorem v_w : v * w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [v, w, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | (solve | ring) | (solve | linear_combination five_fifth)

theorem w_v : w * v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [v, w, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | (solve | ring) | (solve | linear_combination five_fifth)

noncomputable def v_unit : Mˣ := ⟨v, w, v_w, w_v⟩

theorem q_v : q * v = v * p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p, q, v, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination five_fifth
  · ring
  · linear_combination 2 * five_fifth
  · ring

theorem v_gram : v.transpose * v = 5 • (1 : M) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [v, Matrix.mul_apply, Fin.sum_univ_two]

theorem no_square_mod_eight : ∀ x : ZMod 8, 5 * x ^ 2 ≠ 1 := by decide

theorem squares_mod_eight : ∀ x : ZMod 8, x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by decide

theorem no_normalized_five_square (x : R) : 5 * x ^ 2 ≠ 1 := by
  intro h
  have hh := congrArg (PadicInt.toZModPow (p := 2) 3) h
  have : (5 : ZMod 8) * (PadicInt.toZModPow 3 x) ^ 2 = 1 := by
    simpa only [map_mul, map_pow, map_ofNat, map_one] using hh
  exact no_square_mod_eight _ this

theorem q_fixed_vector (a b : R) (h : fifth * a + 2 * fifth * b = a) : b = 2 * a := by
  have h5 : a + 2 * b = 5 * a := by
    linear_combination 5 * h - a * five_fifth - 2 * b * five_fifth
  have ht : (2 : R) * b = 2 * (2 * a) := by linear_combination h5
  exact (mul_left_cancel₀ (by norm_num : (2 : R) ≠ 0)) ht

theorem no_orthogonal_intertwiner (u : M)
    (hu : u.transpose * u = 1) (hi : q * u = u * p) : False := by
  have hfixed : fifth * u 0 0 + 2 * fifth * u 1 0 = u 0 0 := by
    have h := congrFun (congrFun hi 0) 0
    simpa [p, q, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hb := q_fixed_vector (u 0 0) (u 1 0) hfixed
  have hnorm : u 0 0 * u 0 0 + u 1 0 * u 1 0 = 1 := by
    have h := congrFun (congrFun hu 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  apply no_normalized_five_square (u 0 0)
  rw [hb] at hnorm
  linear_combination hnorm

def IsSymmetricDecomposition {A : Type*} [CommRing A] {d r : ℕ}
    (e : Fin r → Matrix (Fin d) (Fin d) A) : Prop :=
  (∀ i, (e i).transpose = e i) ∧
  (∀ i j, e i * e j = if i = j then e i else 0) ∧
  (∑ i, e i) = 1

def complementary {A : Type*} [CommRing A] {d : ℕ}
    (a : Matrix (Fin d) (Fin d) A) : Fin 2 → Matrix (Fin d) (Fin d) A :=
  ![a, 1 - a]

theorem complementary_valid {A : Type*} [CommRing A] {d : ℕ}
    (a : Matrix (Fin d) (Fin d) A) (hs : a.transpose = a) (ha : a * a = a) :
    IsSymmetricDecomposition (complementary a) := by
  constructor
  · intro i
    fin_cases i <;> simp [complementary, hs]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [complementary, ha, mul_sub, sub_mul]
  · simp [complementary, Fin.sum_univ_two]

theorem v_congr_identity (i j : Fin 2) :
    v i j - (1 : M) i j ∈ IsLocalRing.maximalIdeal R := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  fin_cases i <;> fin_cases j <;> norm_num [v]

structure ComparisonData (A : Type*) [CommRing A] (m : Ideal A) (d r : ℕ) where
  source : Fin r → Matrix (Fin d) (Fin d) A
  target : Fin r → Matrix (Fin d) (Fin d) A
  source_valid : IsSymmetricDecomposition source
  target_valid : IsSymmetricDecomposition target
  comparison : (Matrix (Fin d) (Fin d) A)ˣ
  near_identity : ∀ i j, (comparison : Matrix (Fin d) (Fin d) A) i j -
    (1 : Matrix (Fin d) (Fin d) A) i j ∈ m
  intertwines : ∀ i, (comparison : Matrix (Fin d) (Fin d) A) * source i =
    target i * (comparison : Matrix (Fin d) (Fin d) A)

def HasIsometricComparison {A : Type*} [CommRing A] {m : Ideal A} {d r : ℕ}
    (D : ComparisonData A m d r) : Prop :=
  ∃ u : (Matrix (Fin d) (Fin d) A)ˣ,
    (∀ i j, (u : Matrix (Fin d) (Fin d) A) i j -
      (1 : Matrix (Fin d) (Fin d) A) i j ∈ m) ∧
    (u : Matrix (Fin d) (Fin d) A).transpose * u = 1 ∧
    (∀ i, (u : Matrix (Fin d) (Fin d) A) * D.source i = D.target i * u)

def counterexample : ComparisonData R (IsLocalRing.maximalIdeal R) 2 2 where
  source := complementary p
  target := complementary q
  source_valid := complementary_valid p p_symmetric p_idempotent
  target_valid := complementary_valid q q_symmetric q_idempotent
  comparison := v_unit
  near_identity := v_congr_identity
  intertwines := by
    intro i
    fin_cases i
    · exact q_v.symm
    · simpa [complementary, mul_sub, sub_mul] using congrArg (fun x : M => v - x) q_v.symm

theorem counterexample_has_no_isometric_comparison : ¬ HasIsometricComparison counterexample := by
  rintro ⟨u, _, hu, hi⟩
  apply no_orthogonal_intertwiner (u : M) hu
  exact (hi 0).symm

theorem universal_target_false :
    ¬ (∀ D : ComparisonData R (IsLocalRing.maximalIdeal R) 2 2, HasIsometricComparison D) := by
  intro h
  exact counterexample_has_no_isometric_comparison (h counterexample)

end

end MathGauge.PadicOrthogonal
