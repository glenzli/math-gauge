import DyadicEndomorphisms
import Mathlib.Data.Nat.Prime.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open Module
namespace MathGauge.Tower.Dyadic
open Examples

theorem power_mem (k : ℤ) : (2:ℚ)^k ∈ D := by
  cases k with
  | ofNat n => exact ⟨0,2^n,by simp⟩
  | negSucc n => exact ⟨n+1,1,by simp [zpow_negSucc,one_div]⟩

def power (k : ℤ) : D := ⟨(2:ℚ)^k,power_mem k⟩

theorem reciprocal_iff_signed_power (r : D) :
    (∃ s : D, r.1*s.1=1) ↔ ∃ k : ℤ, r.1=(2:ℚ)^k ∨ r.1= -((2:ℚ)^k) := by
  constructor
  · rintro ⟨s,hrs⟩
    obtain ⟨n,z,hz⟩ := r.2
    obtain ⟨m,w,hw⟩ := s.2
    have hq : (z:ℚ)*(w:ℚ)=(2:ℚ)^(n+m) := by
      rw [hz,hw] at hrs
      rw [pow_add]
      field_simp at hrs
      exact hrs
    have hi : z*w=(2:ℤ)^(n+m) := by exact_mod_cast hq
    have hn : z.natAbs*w.natAbs=2^(n+m) := by
      have h := congrArg Int.natAbs hi
      simpa only [Int.natAbs_mul,Int.natAbs_pow] using h
    obtain ⟨j,hj,habs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show z.natAbs∣2^(n+m) from ⟨w.natAbs,hn.symm⟩)
    have hsign : z=(2:ℤ)^j ∨ z= -((2:ℤ)^j) := by
      simpa only [habs,Nat.cast_pow,Nat.cast_ofNat] using Int.natAbs_eq z
    refine ⟨(j:ℤ)-n,?_⟩
    rw [zpow_sub₀ (by norm_num : (2:ℚ)≠0),zpow_natCast,zpow_natCast]
    rcases hsign with hp | hm
    · left
      rw [hz,hp]
      push_cast
      rfl
    · right
      rw [hz,hm]
      push_cast
      ring
  · rintro ⟨k,hp | hm⟩
    · refine ⟨power (-k),?_⟩
      change r.1*(2:ℚ)^(-k)=1
      rw [hp,← zpow_add₀ (by norm_num : (2:ℚ)≠0)]
      simp
    · refine ⟨-(power (-k)),?_⟩
      change r.1*(-((2:ℚ)^(-k)))=1
      rw [hm,neg_mul_neg,← zpow_add₀ (by norm_num : (2:ℚ)≠0)]
      simp

theorem multiply_bijective_iff_signed_power (r : D) :
    Function.Bijective (multiply r) ↔ ∃ k : ℤ, r.1=(2:ℚ)^k ∨ r.1= -((2:ℚ)^k) :=
  (multiply_bijective_iff r).trans (reciprocal_iff_signed_power r)

theorem endomorphism_bijective_iff_signed_power (f : D →ₗ[ℤ] D) :
    Function.Bijective f ↔ ∃ k : ℤ, (f one).1=(2:ℚ)^k ∨ (f one).1= -((2:ℚ)^k) := by
  have he : multiply (f one)=f := endomorphismEquiv.left_inv f
  have hb : Function.Bijective f ↔ Function.Bijective (multiply (f one)) := by rw [he]
  exact hb.trans (multiply_bijective_iff_signed_power (f one))

def automorphism (r : D) (hr : ∃ k : ℤ, r.1=(2:ℚ)^k ∨ r.1= -((2:ℚ)^k)) : D ≃ₗ[ℤ] D :=
  LinearEquiv.ofBijective (multiply r) ((multiply_bijective_iff_signed_power r).mpr hr)

end MathGauge.Tower.Dyadic
