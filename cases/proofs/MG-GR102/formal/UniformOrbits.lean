import FiniteOrbitDecomposition
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
open Set Function Polynomial
open MathGauge.R102

namespace MathGauge.GR102
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem finite_orbit_of_eventual (T : Module.End R M) (x : M)
    (n p : ℕ) (hp : 0 < p) (h : IsPeriodicPt T p ((T ^ n) x)) :
    (Set.range (fun k : ℕ => (T ^ k) x)).Finite := by
  apply (Set.finite_range (fun j : Fin (n + p) => (T ^ j.val) x)).subset
  rintro _ ⟨k, rfl⟩
  by_cases hk : k < n
  · exact ⟨⟨k, by omega⟩, rfl⟩
  · refine ⟨⟨n + (k - n) % p, by have := Nat.mod_lt (k - n) hp; omega⟩, ?_⟩
    change (T ^ (n + (k - n) % p)) x = (T ^ k) x
    rw [Nat.add_comm n, pow_add_apply]
    rw [Module.End.pow_apply, h.iterate_mod_apply]
    rw [← Module.End.pow_apply, ← pow_add_apply, Nat.sub_add_cancel (by omega)]

theorem finite_orbits_of_relation (T : Module.End R M) {n p : ℕ} (hp : 0 < p)
    (h : T ^ (n + p) = T ^ n) : PointwiseFiniteOrbit T := by
  intro x
  apply finite_orbit_of_eventual T x n p hp
  apply periodic_of_pow
  rw [← pow_add_apply, Nat.add_comm p, h]

theorem decomposition_iff_finite_orbits (T : Module.End R M) :
    (∀ x, ∃ y, y ∈ periodicpart T ∧ x - y ∈ nilpart T) ↔ PointwiseFiniteOrbit T := by
  constructor
  · intro hd x
    obtain ⟨y, ⟨p, hp, hy⟩, n, hn⟩ := hd x
    have he : (T ^ n) x = (T ^ n) y := by simpa [map_sub, sub_eq_zero] using hn
    apply finite_orbit_of_eventual T x n p hp
    rw [he, Module.End.pow_apply]
    exact hy.apply_iterate n
  · exact decomposition_exists T

theorem finite_powers_relation (T : Module.End R M)
    (h : (Set.range (fun n : ℕ => T ^ n)).Finite) :
    ∃ n p : ℕ, 0 < p ∧ T ^ (n + p) = T ^ n := by
  let S := Set.range (fun n : ℕ => T ^ n)
  letI : Finite S := h.to_subtype
  let f : ℕ → S := fun n => ⟨T ^ n, ⟨n, rfl⟩⟩
  have hi := not_injective_infinite_finite f
  simp only [Injective, not_forall] at hi
  obtain ⟨i, j, he, hij⟩ := hi
  have heq : T ^ i = T ^ j := congrArg Subtype.val he
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j - i, by omega, by rw [Nat.add_sub_of_le (by omega)]; exact heq.symm⟩
  · exact ⟨j, i - j, by omega, by rw [Nat.add_sub_of_le (by omega)]; exact heq⟩

theorem projection_eq_uniform_power (T : Module.End R M) {n p : ℕ} (hp : 0 < p)
    (h : T ^ (n + p) = T ^ n) :
    projection T (finite_orbits_of_relation T hp h) = T ^ (n * p) := by
  apply (projection_characterization T (finite_orbits_of_relation T hp h) _ ?_).symm
  intro x
  have ht : IsPeriodicPt T p ((T ^ n) x) := periodic_of_pow (by
    rw [← pow_add_apply, Nat.add_comm p, h])
  have hnk : n ≤ n * p := by nlinarith
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hnk
  constructor
  · refine ⟨p, hp, ?_⟩
    rw [hs, Nat.add_comm n, pow_add_apply, Module.End.pow_apply]
    exact ht.apply_iterate s
  · refine ⟨n, ?_⟩
    rw [map_sub]
    apply sub_eq_zero.mpr
    calc
      (T ^ n) x = (T ^ (n * p)) ((T ^ n) x) := (periodic_pow (ht.const_mul n)).symm
      _ = (T ^ n) ((T ^ (n * p)) x) := by rw [← pow_add_apply, ← pow_add_apply, Nat.add_comm]

/-- S1: finite M gives a finite endomorphism set, hence one common recurrence. -/
theorem finite_module_uniform [Finite M] (T : Module.End R M) :
    ∃ n p k : ℕ, 0 < p ∧ n ≤ k ∧ T ^ (n + p) = T ^ n ∧
      (T ^ k).comp (T ^ k) = T ^ k ∧
      (T ^ k).ker = nilpart T ∧ (T ^ k).range = periodicpart T ∧
      Nonempty (M ≃ₗ[R] (nilpart T × periodicpart T)) := by
  haveI : Finite (Module.End R M) := Finite.of_injective
    (fun f : Module.End R M => (f : M → M)) DFunLike.coe_injective
  obtain ⟨n, p, hp, hrel⟩ := finite_powers_relation T (Set.toFinite _)
  let hfin := finite_orbits_of_relation T hp hrel
  have he := projection_eq_uniform_power T hp hrel
  refine ⟨n, p, n * p, hp, by nlinarith, hrel, ?_, ?_, ?_, ⟨decomposition_equiv T hfin⟩⟩
  · rw [← he]
    exact projection_idempotent T hfin
  · rw [← he]
    exact projection_kernel T hfin
  · rw [← he]
    exact projection_range T hfin

section FiniteDimensional
variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E] [FiniteDimensional k E]

/-- Finitely many basis vectors suffice to make the whole power family finite. -/
theorem finite_powers_of_pointwise (T : Module.End k E) (h : PointwiseFiniteOrbit T) :
    (Set.range (fun n : ℕ => T ^ n)).Finite := by
  let b := Module.finBasis k E
  let O (i : Fin (Module.finrank k E)) := Set.range (fun n : ℕ => (T ^ n) (b i))
  haveI (i : Fin (Module.finrank k E)) : Finite (O i) := (h (b i)).to_subtype
  let f : Set.range (fun n : ℕ => T ^ n) → ∀ i, O i := fun a i =>
    ⟨a.val (b i), by obtain ⟨n, hn⟩ := a.property; exact ⟨n, LinearMap.congr_fun hn (b i)⟩⟩
  have hi : Injective f := by
    intro a c he
    apply Subtype.ext
    apply b.ext
    intro i
    exact congrArg Subtype.val (congrFun he i)
  haveI : Finite (Set.range (fun n : ℕ => T ^ n)) := Finite.of_injective f hi
  exact Set.toFinite _

theorem relation_iff_minpoly (T : Module.End k E) (n p : ℕ) :
    T ^ (n + p) = T ^ n ↔ minpoly k T ∣ (X : k[X]) ^ n * (X ^ p - 1) := by
  rw [minpoly.dvd_iff]
  simp only [map_mul, map_pow, aeval_X, map_sub, map_one, mul_sub, mul_one,
    ← pow_add, sub_eq_zero]

/-- S6: exact criterion, including dimension zero (whose minpoly is 1). -/
theorem decomposition_minpoly_iff (T : Module.End k E) :
    (∀ x, ∃ y, y ∈ periodicpart T ∧ x - y ∈ nilpart T) ↔
      ∃ n p : ℕ, 0 < p ∧ minpoly k T ∣ (X : k[X]) ^ n * (X ^ p - 1) := by
  rw [decomposition_iff_finite_orbits]
  constructor
  · intro h
    obtain ⟨n,p,hp,hn⟩ := finite_powers_relation T (finite_powers_of_pointwise T h)
    exact ⟨n,p,hp,(relation_iff_minpoly T n p).mp hn⟩
  · rintro ⟨n,p,hp,hdiv⟩
    exact finite_orbits_of_relation T hp ((relation_iff_minpoly T n p).mpr hdiv)

end FiniteDimensional
end MathGauge.GR102
