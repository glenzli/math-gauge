import CompletionStructure
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Div

set_option maxHeartbeats 800000

noncomputable section
namespace MathGauge.RestrictedSeries
open MathGauge.CompletionFailure MathGauge.CompletionStructure
open Polynomial
universe u
variable (k : Type u) [Field k]
abbrev Series := PowerSeries k
abbrev F := ℕ →₀ Polynomial k

/-- Restricted, not unrestricted, product of the genuine power-series rings. -/
def restricted : Submodule (Series k) (ℕ → Series k) where
  carrier := {a | ∀ n : ℕ,{i : ℕ | ¬ (PowerSeries.X : Series k)^n ∣ a i}.Finite}
  zero_mem' := by intro n;simp
  add_mem' := by
    intro a b ha hb n
    apply ((ha n).union (hb n)).subset
    intro i hi
    by_contra hn
    simp only [Set.mem_union,Set.mem_setOf_eq,not_or,not_not] at hn
    exact hi (dvd_add hn.1 hn.2)
  smul_mem' := by
    intro r a ha n
    apply (ha n).subset
    intro i hi
    change ¬ (PowerSeries.X : Series k)^n ∣ a i
    intro hdiv
    exact hi (dvd_mul_of_dvd_right hdiv r)

/-- Coordinate power-series divisibility is exactly vanishing of the first n coefficients. -/
theorem restricted_iff_coeff (a : ℕ → Series k) :
    a∈restricted k ↔ ∀ n : ℕ,{i : ℕ | ∃ d<n,PowerSeries.coeff d (a i)≠0}.Finite := by
  change (∀ n : ℕ,{i : ℕ | ¬ (PowerSeries.X : Series k)^n ∣ a i}.Finite) ↔ _
  simp only [PowerSeries.X_pow_dvd_iff,not_forall,exists_prop]

theorem free_power_iff (n : ℕ) (x : F k) :
    x∈powerSub (X : Polynomial k) (F k) n ↔ ∀ i d,d<n → (x i).coeff d=0 := by
  constructor
  · intro hx i d hd
    exact low_coefficient_zero k hd hx i
  · intro hx
    have hd (i : ℕ) : ∃ p : Polynomial k,(X : Polynomial k)^n*p=x i := by
      obtain ⟨p,hp⟩ := Polynomial.X_pow_dvd_iff.mpr (hx i)
      exact ⟨p,hp.symm⟩
    choose p hp using hd
    let y : F k := Finsupp.onFinset x.support p (by
      intro i hi
      apply Finsupp.mem_support_iff.mpr
      intro hz
      have he : p i=0 := (mul_eq_zero.mp ((hp i).trans hz)).resolve_left (pow_ne_zero _ X_ne_zero)
      exact hi he)
    refine ⟨y,?_⟩
    apply Finsupp.ext
    intro i
    exact hp i

def levelCoeff (n i d : ℕ) (hd : d<n) (x : Level (X : Polynomial k) (F k) n) : k :=
  Quotient.liftOn x (fun a : F k => (a i).coeff d) (by
    intro a b hab
    have hsub : a-b∈powerSub (X : Polynomial k) (F k) n := (Submodule.quotientRel_def _).mp hab
    have hz := low_coefficient_zero k hd hsub i
    exact sub_eq_zero.mp (by simpa only [Finsupp.sub_apply,Polynomial.coeff_sub] using hz))

@[simp] theorem levelCoeff_mk (n i d : ℕ) (hd : d<n) (x : F k) :
    levelCoeff k n i d hd ((powerSub (X : Polynomial k) (F k) n).mkQ x)=(x i).coeff d := rfl

theorem levelCoeff_reduce {n m : ℕ} (h : n≤m) (i d : ℕ) (hd : d<n)
    (x : Level (X : Polynomial k) (F k) m) :
    levelCoeff k n i d hd (reduce (X : Polynomial k) (F k) h x)=
      levelCoeff k m i d (lt_of_lt_of_le hd h) x := by
  obtain ⟨a,rfl⟩ := (powerSub (X : Polynomial k) (F k) m).mkQ_surjective x
  rw [reduce_mk,levelCoeff_mk,levelCoeff_mk]

theorem level_ext (n : ℕ) (x y : Level (X : Polynomial k) (F k) n)
    (h : ∀ i d (hd : d<n),levelCoeff k n i d hd x=levelCoeff k n i d hd y) : x=y := by
  obtain ⟨a,rfl⟩ := (powerSub (X : Polynomial k) (F k) n).mkQ_surjective x
  obtain ⟨b,rfl⟩ := (powerSub (X : Polynomial k) (F k) n).mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  rw [free_power_iff]
  intro i d hd
  simpa only [Finsupp.sub_apply,Polynomial.coeff_sub,sub_eq_zero,levelCoeff_mk] using h i d hd

def coefficients (x : completion (X : Polynomial k) (F k)) (i d : ℕ) : k :=
  levelCoeff k (d+1) i d (Nat.lt_succ_self d) (x.val (d+1))

theorem coefficients_at (x : completion (X : Polynomial k) (F k)) (n i d : ℕ) (hd : d<n) :
    coefficients k x i d=levelCoeff k n i d hd (x.val n) := by
  unfold coefficients
  rw [← x.property (d+1) n hd]
  exact levelCoeff_reduce k hd i d (Nat.lt_succ_self d) (x.val n)

def toSeries (x : completion (X : Polynomial k) (F k)) (i : ℕ) : Series k :=
  PowerSeries.mk (coefficients k x i)

@[simp] theorem coeff_toSeries (x : completion (X : Polynomial k) (F k)) (i d : ℕ) :
    PowerSeries.coeff d (toSeries k x i)=coefficients k x i d := PowerSeries.coeff_mk ..

theorem toSeries_restricted (x : completion (X : Polynomial k) (F k)) : toSeries k x∈restricted k := by
  rw [restricted_iff_coeff]
  intro n
  obtain ⟨a,ha⟩ := (powerSub (X : Polynomial k) (F k) n).mkQ_surjective (x.val n)
  apply a.support.finite_toSet.subset
  rintro i ⟨d,hd,hne⟩
  apply Finsupp.mem_support_iff.mpr
  intro hz
  apply hne
  rw [coeff_toSeries,coefficients_at k x n i d hd,← ha,levelCoeff_mk,hz,Polynomial.coeff_zero]

 theorem trunc_support_finite (a : restricted k) (n : ℕ) :
    (Function.support (fun i => PowerSeries.trunc n (a.val i))).Finite := by
  apply (a.property n).subset
  intro i hi hdiv
  apply hi
  apply Polynomial.ext
  intro d
  rw [PowerSeries.coeff_trunc,Polynomial.coeff_zero]
  split_ifs with hd
  · exact PowerSeries.X_pow_dvd_iff.mp hdiv d hd
  · rfl

 def truncVector (a : restricted k) (n : ℕ) : F k :=
   Finsupp.ofSupportFinite (fun i => PowerSeries.trunc n (a.val i)) (trunc_support_finite k a n)

 @[simp] theorem truncVector_apply (a : restricted k) (n i : ℕ) :
    truncVector k a n i=PowerSeries.trunc n (a.val i) := rfl

 def fromSeries (a : restricted k) : completion (X : Polynomial k) (F k) :=
   ⟨fun n => (powerSub (X : Polynomial k) (F k) n).mkQ (truncVector k a n),by
     intro n m h
     rw [reduce_mk]
     apply level_ext k n
     intro i d hd
     simp only [levelCoeff_mk,truncVector_apply,PowerSeries.coeff_trunc,
       if_pos hd,if_pos (lt_of_lt_of_le hd h)]⟩

 theorem toSeries_fromSeries (a : restricted k) : toSeries k (fromSeries k a)=a.val := by
   funext i
   apply PowerSeries.ext
   intro d
   rw [coeff_toSeries]
   change levelCoeff k (d+1) i d _ ((powerSub (X : Polynomial k) (F k) (d+1)).mkQ
     (truncVector k a (d+1)))=PowerSeries.coeff d (a.val i)
   simp only [levelCoeff_mk,truncVector_apply,PowerSeries.coeff_trunc,if_pos (Nat.lt_succ_self d)]

 theorem fromSeries_toSeries (x : completion (X : Polynomial k) (F k)) :
    fromSeries k ⟨toSeries k x,toSeries_restricted k x⟩=x := by
   apply Subtype.ext
   funext n
   apply level_ext k n
   intro i d hd
   change levelCoeff k n i d hd ((powerSub (X : Polynomial k) (F k) n).mkQ
     (truncVector k ⟨toSeries k x,toSeries_restricted k x⟩ n))=levelCoeff k n i d hd (x.val n)
   simp only [levelCoeff_mk,truncVector_apply,PowerSeries.coeff_trunc,if_pos hd,coeff_toSeries]
   exact coefficients_at k x n i d hd

 def seriesEquiv : completion (X : Polynomial k) (F k) ≃ restricted k where
   toFun x := ⟨toSeries k x,toSeries_restricted k x⟩
   invFun := fromSeries k
   left_inv := fromSeries_toSeries k
   right_inv a := Subtype.ext (toSeries_fromSeries k a)

 theorem levelCoeff_add (n i d : ℕ) (hd : d<n)
    (x y : Level (X : Polynomial k) (F k) n) :
    levelCoeff k n i d hd (x+y)=levelCoeff k n i d hd x+levelCoeff k n i d hd y := by
   obtain ⟨a,rfl⟩ := (powerSub (X : Polynomial k) (F k) n).mkQ_surjective x
   obtain ⟨b,rfl⟩ := (powerSub (X : Polynomial k) (F k) n).mkQ_surjective y
   rw [← map_add,levelCoeff_mk,levelCoeff_mk,levelCoeff_mk,Finsupp.add_apply,Polynomial.coeff_add]

 theorem toSeries_add (x y : completion (X : Polynomial k) (F k)) :
    toSeries k (x+y)=toSeries k x+toSeries k y := by
   funext i
   apply PowerSeries.ext
   intro d
   simp only [Pi.add_apply,map_add,coeff_toSeries,coefficients]
   exact levelCoeff_add k (d+1) i d (Nat.lt_succ_self d) (x.val (d+1)) (y.val (d+1))

 theorem coeff_series_eq_rep (x : completion (X : Polynomial k) (F k)) (n : ℕ) (a : F k)
    (ha : (powerSub (X : Polynomial k) (F k) n).mkQ a=x.val n) (i d : ℕ) (hd : d<n) :
    PowerSeries.coeff d (toSeries k x i)=(a i).coeff d := by
   rw [coeff_toSeries,coefficients_at k x n i d hd,← ha,levelCoeff_mk]

 theorem toSeries_smul (r : Polynomial k) (x : completion (X : Polynomial k) (F k)) :
    toSeries k (r • x)=fun i => (r : Series k)*toSeries k x i := by
   funext i
   apply PowerSeries.ext
   intro d
   obtain ⟨a,ha⟩ := (powerSub (X : Polynomial k) (F k) (d+1)).mkQ_surjective (x.val (d+1))
   have hs : (powerSub (X : Polynomial k) (F k) (d+1)).mkQ (r • a)=(r • x).val (d+1) := by
     rw [map_smul,ha]
     rfl
   rw [coeff_series_eq_rep k (r • x) (d+1) (r • a) hs i d (Nat.lt_succ_self d)]
   change (r*a i).coeff d=_
   rw [Polynomial.coeff_mul,PowerSeries.coeff_mul]
   apply Finset.sum_congr rfl
   rintro ⟨j,l⟩ hjl
   have hl : l<d+1 := by have h := Finset.mem_antidiagonal.mp hjl;omega
   rw [Polynomial.coeff_coe,coeff_series_eq_rep k x (d+1) a ha i l hl]

/-- This is the full R-linear identification; the target already has its
natural module structure over the complete power-series ring. -/
 def seriesLinearEquiv : completion (X : Polynomial k) (F k) ≃ₗ[Polynomial k] restricted k :=
   { seriesEquiv k with
     map_add' := fun x y => Subtype.ext (toSeries_add k x y)
     map_smul' := fun r x => by
       apply Subtype.ext
       exact toSeries_smul k r x }

end MathGauge.RestrictedSeries

