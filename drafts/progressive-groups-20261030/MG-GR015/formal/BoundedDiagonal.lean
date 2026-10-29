import RestrictedSeries
import AdicBridge
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

noncomputable section
namespace MathGauge.BoundedDiagonal
open MathGauge.CompletionFailure MathGauge.CompletionStructure MathGauge.RestrictedSeries MathGauge.AdicBridge
open Polynomial
universe u
variable (k : Type u) [Field k]

def diagonal (ν : ℕ → ℕ) : F k →ₗ[Polynomial k] F k where
  toFun a := Finsupp.onFinset a.support (fun i => (X : Polynomial k)^(ν i)*a i) (by
    intro i hi
    exact Finsupp.mem_support_iff.mpr (fun hz => hi (by dsimp only; rw [hz,mul_zero])))
  map_add' a b := by
    apply Finsupp.ext
    intro i
    exact mul_add (X^(ν i) : Polynomial k) (a i) (b i)
  map_smul' r a := by
    apply Finsupp.ext
    intro i
    change X^(ν i)*(r*a i)=r*(X^(ν i)*a i)
    ring

@[simp] theorem diagonal_apply (ν : ℕ → ℕ) (a : F k) (i : ℕ) :
    diagonal k ν a i=(X : Polynomial k)^(ν i)*a i := rfl

theorem diagonal_injective (ν : ℕ → ℕ) : Function.Injective (diagonal k ν) := by
  intro a b h
  apply Finsupp.ext
  intro i
  exact mul_left_cancel₀ (pow_ne_zero _ (Polynomial.X_ne_zero : (X : Polynomial k) ≠ 0)) (congrArg (fun x : F k => x i) h)

abbrev Quot (ν : ℕ → ℕ) := F k ⧸ (diagonal k ν).range
def q (ν : ℕ → ℕ) : F k →ₗ[Polynomial k] Quot k ν := (diagonal k ν).range.mkQ

theorem row_exact (ν : ℕ → ℕ) : Function.Exact (diagonal k ν) (q k ν) := by
  intro a
  exact Submodule.Quotient.mk_eq_zero _

theorem q_surjective (ν : ℕ → ℕ) : Function.Surjective (q k ν) := Submodule.mkQ_surjective _

theorem quotient_killed (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M) (c : Quot k ν) :
    (X : Polynomial k)^M • c=0 := by
  obtain ⟨b,rfl⟩ := q_surjective k ν c
  rw [← map_smul]
  apply (row_exact k ν _).mpr
  refine ⟨diagonal k (fun i => M-ν i) b,?_⟩
  apply Finsupp.ext
  intro i
  change X^(ν i)*(X^(M-ν i)*b i)=X^M*b i
  rw [← mul_assoc,← pow_add,Nat.add_sub_of_le (hν i)]

theorem quotient_power_zero (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M) :
    powerSub (X : Polynomial k) (Quot k ν) M=⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro c ⟨b,rfl⟩
  exact quotient_killed k ν M hν b

theorem completed_diagonal_coordinates (ν : ℕ → ℕ)
    (a : completion (X : Polynomial k) (F k)) (i : ℕ) :
    toSeries k (completionMap (X : Polynomial k) (F k) (diagonal k ν) a) i=
      (PowerSeries.X : Series k)^(ν i)*toSeries k a i := by
  apply PowerSeries.ext
  intro d
  obtain ⟨b,hb⟩ := (powerSub (X : Polynomial k) (F k) (d+1)).mkQ_surjective (a.val (d+1))
  have hm : (powerSub (X : Polynomial k) (F k) (d+1)).mkQ (diagonal k ν b)=
      (completionMap (X : Polynomial k) (F k) (diagonal k ν) a).val (d+1) := by
    change _=levelMap (X : Polynomial k) (F k) (diagonal k ν) (d+1) (a.val (d+1))
    rw [← hb,levelMap_mk]
  rw [coeff_series_eq_rep k _ (d+1) _ hm i d (Nat.lt_succ_self d),diagonal_apply,
    Polynomial.coeff_X_pow_mul',PowerSeries.coeff_X_pow_mul']
  split_ifs with hd
  · exact (coeff_series_eq_rep k a (d+1) b hb i (d-ν i) (by omega)).symm
  · rfl

theorem completed_diagonal_injective (ν : ℕ → ℕ) :
    Function.Injective (completionMap (X : Polynomial k) (F k) (diagonal k ν)) := by
  intro a b hab
  apply (seriesEquiv k).injective
  apply Subtype.ext
  funext i
  have h := congrArg (fun x => toSeries k x i) hab
  dsimp only at h
  rw [completed_diagonal_coordinates,completed_diagonal_coordinates] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (PowerSeries.X_ne_zero : (PowerSeries.X : PowerSeries k) ≠ 0)) h

/-- A global bound on the diagonal exponents preserves restricted support
when coordinates are divided; the bound shifts the observation level. -/
theorem divided_family_restricted (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M)
    (b : restricted k) (a : ℕ → Series k)
    (ha : ∀ i,(PowerSeries.X : Series k)^(ν i)*a i=b.val i) : a∈restricted k := by
  intro n
  apply (b.property (n+M)).subset
  intro i hi
  change ¬ (PowerSeries.X : Series k)^(n+M) ∣ b.val i
  intro hb
  apply hi
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro d hd
  have hνi := hν i
  have hzero := PowerSeries.X_pow_dvd_iff.mp hb (d+ν i) (by omega)
  rw [← ha i,PowerSeries.coeff_X_pow_mul] at hzero
  exact hzero

theorem restricted_division (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M)
    (b : restricted k) (hb : ∀ i,(PowerSeries.X : Series k)^(ν i) ∣ b.val i) :
    ∃ a : restricted k,∀ i,(PowerSeries.X : Series k)^(ν i)*a.val i=b.val i := by
  choose a ha using hb
  exact ⟨⟨a,divided_family_restricted k ν M hν b a (fun i => (ha i).symm)⟩,
    fun i => (ha i).symm⟩

theorem kernel_coordinates (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M)
    (b : completion (X : Polynomial k) (F k))
    (hb : completionMap (X : Polynomial k) (F k) (q k ν) b=0) :
    ∀ i,(PowerSeries.X : Series k)^(ν i) ∣ toSeries k b i := by
  obtain ⟨a,ha⟩ := (powerSub (X : Polynomial k) (F k) M).mkQ_surjective (b.val M)
  have hm := congrArg (fun c : completion (X : Polynomial k) (Quot k ν) => c.val M) hb
  change levelMap (X : Polynomial k) (F k) (q k ν) M (b.val M)=0 at hm
  rw [← ha,levelMap_mk] at hm
  have hq : q k ν a=0 := by
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hm
    rw [quotient_power_zero k ν M hν,Submodule.mem_bot] at hmem
    exact hmem
  obtain ⟨x,hx⟩ := (row_exact k ν a).mp hq
  intro i
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro d hd
  rw [coeff_series_eq_rep k b M a ha i d (lt_of_lt_of_le hd (hν i)),← hx,diagonal_apply,
    Polynomial.coeff_X_pow_mul',if_neg (not_le_of_gt hd)]

theorem completed_exact (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M) :
    Function.Exact (completionMap (X : Polynomial k) (F k) (diagonal k ν))
      (completionMap (X : Polynomial k) (F k) (q k ν)) := by
  have hqi : (q k ν).comp (diagonal k ν)=0 := by
    apply LinearMap.ext
    intro a
    exact (row_exact k ν _).mpr ⟨a,rfl⟩
  intro b
  constructor
  · intro hb
    obtain ⟨a,ha⟩ := restricted_division k ν M hν (seriesEquiv k b) (kernel_coordinates k ν M hν b hb)
    refine ⟨fromSeries k a,?_⟩
    apply (seriesEquiv k).injective
    apply Subtype.ext
    funext i
    rw [show (seriesEquiv k (completionMap (X : Polynomial k) (F k) (diagonal k ν)
      (fromSeries k a))).val i=toSeries k (completionMap (X : Polynomial k) (F k)
      (diagonal k ν) (fromSeries k a)) i from rfl,completed_diagonal_coordinates,toSeries_fromSeries]
    exact ha i
  · rintro ⟨a,rfl⟩
    change ((completionMap (X : Polynomial k) (F k) (q k ν)).comp
      (completionMap (X : Polynomial k) (F k) (diagonal k ν))) a=0
    rw [← completionMap_comp,hqi,completionMap_zero,LinearMap.zero_apply]

theorem completed_short_exact (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M) :
    Function.Injective (completionMap (X : Polynomial k) (F k) (diagonal k ν)) ∧
    Function.Surjective (completionMap (X : Polynomial k) (F k) (q k ν)) ∧
    Function.Exact (completionMap (X : Polynomial k) (F k) (diagonal k ν))
      (completionMap (X : Polynomial k) (F k) (q k ν)) :=
  ⟨completed_diagonal_injective k ν,
    completed_map_surjective (X : Polynomial k) (F k) (q k ν) (q_surjective k ν),
    completed_exact k ν M hν⟩

def chosenLift (ν : ℕ → ℕ) (c : completion (X : Polynomial k) (Quot k ν)) :
    completion (X : Polynomial k) (F k) :=
  Classical.choose (completed_map_surjective (X : Polynomial k) (F k) (q k ν) (q_surjective k ν) c)

theorem chosenLift_spec (ν : ℕ → ℕ) (c : completion (X : Polynomial k) (Quot k ν)) :
    completionMap (X : Polynomial k) (F k) (q k ν) (chosenLift k ν c)=c :=
  Classical.choose_spec (completed_map_surjective (X : Polynomial k) (F k) (q k ν) (q_surjective k ν) c)

/-- All lifts in the concrete S2 coordinates; the free parameter is itself
restricted, and its coordinate multiplication is the original diagonal. -/
theorem all_lifts_coordinates (ν : ℕ → ℕ) (M : ℕ) (hν : ∀ i,ν i≤M)
    (c : completion (X : Polynomial k) (Quot k ν)) (b : completion (X : Polynomial k) (F k)) :
    completionMap (X : Polynomial k) (F k) (q k ν) b=c ↔
      ∃! a : restricted k,∀ i,toSeries k b i=toSeries k (chosenLift k ν c) i+
        (PowerSeries.X : Series k)^(ν i)*a.val i := by
  let Q := completionMap (X : Polynomial k) (F k) (q k ν)
  let I := completionMap (X : Polynomial k) (F k) (diagonal k ν)
  have hE := completed_exact k ν M hν
  constructor
  · intro hb
    have hz : Q (b-chosenLift k ν c)=0 := by
      rw [map_sub,hb,chosenLift_spec,sub_self]
    obtain ⟨x,hx⟩ := (hE _).mp hz
    refine ⟨seriesEquiv k x,?_,?_⟩
    · intro i
      have he : b=chosenLift k ν c+I x := by rw [hx];abel
      rw [he,toSeries_add]
      change _=toSeries k (chosenLift k ν c) i+(PowerSeries.X : Series k)^(ν i)*toSeries k x i
      rw [Pi.add_apply,completed_diagonal_coordinates]
    · intro a ha
      apply Subtype.ext
      funext i
      have h1 := ha i
      have hx' : b=chosenLift k ν c+I x := by rw [hx];abel
      rw [hx',toSeries_add,Pi.add_apply,completed_diagonal_coordinates] at h1
      exact mul_left_cancel₀ (pow_ne_zero _ (PowerSeries.X_ne_zero : (PowerSeries.X : PowerSeries k) ≠ 0)) (add_left_cancel h1).symm
  · rintro ⟨a,ha,_⟩
    have hb : b=chosenLift k ν c+I (fromSeries k a) := by
      apply (seriesEquiv k).injective
      apply Subtype.ext
      funext i
      change toSeries k b i=toSeries k (chosenLift k ν c+I (fromSeries k a)) i
      rw [toSeries_add,Pi.add_apply,completed_diagonal_coordinates,toSeries_fromSeries]
      exact ha i
    rw [hb,map_add,chosenLift_spec]
    have hz := (hE _).mpr ⟨fromSeries k a,rfl⟩
    change Q (I (fromSeries k a))=0 at hz
    rw [hz,add_zero]

end MathGauge.BoundedDiagonal
