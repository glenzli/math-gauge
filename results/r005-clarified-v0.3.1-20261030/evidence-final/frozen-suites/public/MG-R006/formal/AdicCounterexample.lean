import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
namespace MathGauge.AdicCounterexample

/-- The finite record groups, indexed here by n = 0 for the prose's first row. -/
abbrev C (n : ℕ) := ZMod (2^(n+1))
instance (n : ℕ) : NeZero (2^(n+1)) := ⟨pow_ne_zero _ (by decide)⟩
instance (n : ℕ) : Fintype (C n) := inferInstanceAs (Fintype (ZMod _))

def pi (n : ℕ) : ℤ →+ C n := (Int.castAddHom _)

/-- The actual subgroup 2^(n+1) Z, expressed as the kernel of reduction. -/
def A (n : ℕ) : AddSubgroup ℤ := (pi n).ker

theorem mem_A (n : ℕ) (a : ℤ) : a ∈ A n ↔ (2^(n+1) : ℤ) ∣ a := by
  change (a : C n) = 0 ↔ (2^(n+1) : ℤ) ∣ a
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp

def gamma (n : ℕ) : C (n+1) →+* C n :=
  ZMod.castHom (pow_dvd_pow 2 (by omega : n+1 ≤ (n+1)+1)) (C n)

@[simp] theorem gamma_cast (n : ℕ) (a : ℤ) : gamma n (a : C (n+1)) = (a : C n) := by
  exact map_intCast (gamma n) a

theorem pi_surjective (n : ℕ) : Function.Surjective (pi n) := ZMod.intCast_surjective

theorem gamma_surjective (n : ℕ) : Function.Surjective (gamma n) := by
  intro c
  obtain ⟨a,ha⟩ := ZMod.intCast_surjective c
  exact ⟨(a : C (n+1)), by simpa using ha⟩

def alpha (n : ℕ) : A (n+1) →+ A n where
  toFun a := ⟨a.val, by
    rw [mem_A]
    exact dvd_trans (pow_dvd_pow 2 (by omega : n+1 ≤ (n+1)+1)) ((mem_A (n+1) _).1 a.property)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Each row has actual inclusion as its injective first map and actual reduction as quotient. -/
theorem rows_exact (n : ℕ) :
    Function.Injective (A n).subtype ∧ Function.Surjective (pi n) ∧
      (A n).subtype.range = (pi n).ker := by
  exact ⟨Subtype.val_injective, pi_surjective n, AddSubgroup.range_subtype _⟩

theorem diagram_commutes (n : ℕ) :
    (A n).subtype.comp (alpha n) = (A (n+1)).subtype ∧
    (gamma n).toAddMonoidHom.comp (pi (n+1)) = pi n := by
  constructor
  · rfl
  · apply AddMonoidHom.ext
    intro a
    exact gamma_cast n a

theorem three_unit (n : ℕ) : IsUnit (3 : C n) := by
  apply (ZMod.isUnit_iff_coprime 3 (2^(n+1))).2
  exact (show Nat.Coprime 3 2 by decide).pow_right _

def record (n : ℕ) : C n := (3 : C n)⁻¹

theorem record_equation (n : ℕ) : 3 * record n = (1 : C n) :=
  ZMod.mul_inv_of_unit _ (three_unit n)

theorem record_unique (n : ℕ) {x : C n} (hx : 3*x=1) : x = record n := by
  exact (three_unit n).mul_left_cancel (hx.trans (record_equation n).symm)

theorem record_compatible (n : ℕ) : gamma n (record (n+1)) = record n := by
  apply record_unique
  have h := congrArg (gamma n) (record_equation (n+1))
  simpa only [map_mul, map_one, map_ofNat] using h

theorem divisible_all_two_powers (a : ℤ) (h : ∀ n : ℕ, (2^(n+1) : ℤ) ∣ a) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h a.natAbs)
  have hp : a.natAbs < 2^(a.natAbs+1) := by
    have hh := Nat.lt_two_pow_self (n := a.natAbs+1)
    omega
  simpa using hp

/-- Each individual row and each finite initial segment admits an integer lift. -/
theorem finite_prefix_lift (N : ℕ) : ∃ a : ℤ, ∀ n ≤ N, (a : C n) = record n := by
  obtain ⟨a,ha⟩ := ZMod.intCast_surjective (record N)
  refine ⟨a, ?_⟩
  intro n hn
  apply record_unique
  let r : C N →+* C n := ZMod.castHom (pow_dvd_pow 2 (Nat.add_le_add_right hn 1)) (C n)
  have h := congrArg r (record_equation N)
  rw [← ha] at h
  simpa only [map_mul, map_ofNat, map_intCast, map_one] using h

/-- No compatible choice of row lifts exists, although all given surjectivities and finiteness hold. -/
theorem no_compatible_lift : ¬∃ b : ℕ → ℤ,
    (∀ n, b (n+1)=b n) ∧ (∀ n, (b n : C n)=record n) := by
  rintro ⟨b,hb,hr⟩
  have hconst : ∀ n, b n=b 0 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => exact (hb n).trans ih
  have hd : ∀ n, (2^(n+1) : ℤ) ∣ 3*b 0-1 := by
    intro n
    have h := record_equation n
    rw [← hr n, hconst n] at h
    have hz : ((3*b 0-1 : ℤ) : C n)=0 := by push_cast; exact sub_eq_zero.mpr h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (3*b 0-1) (2^(n+1))).1 hz
    simpa using this
  have he := divisible_all_two_powers (3*b 0-1) hd
  omega

/-- The kernel inverse limit is zero; this does not restore existence of the lifts. -/
theorem kernel_limit_zero (a : ∀ n, A n) (ha : ∀ n, alpha n (a (n+1)) = a n) :
    ∀ n, (a n).val = 0 := by
  have hc : ∀ n, (a n).val = (a 0).val := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => exact (congrArg Subtype.val (ha n)).trans ih
  have hz : (a 0).val = 0 := by
    apply divisible_all_two_powers
    intro n
    rw [← hc n]
    exact (mem_A n _).1 (a n).property
  intro n; exact (hc n).trans hz

end MathGauge.AdicCounterexample
