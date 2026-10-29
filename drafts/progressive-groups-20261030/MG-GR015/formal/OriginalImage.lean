import RestrictedSeries

noncomputable section
namespace MathGauge.OriginalImage
open MathGauge.CompletionFailure MathGauge.CompletionStructure MathGauge.RestrictedSeries
open Polynomial
universe u
variable (k : Type u) [Field k]

theorem canonical_injective : Function.Injective (canonical (X : Polynomial k) :
    F k →ₗ[Polynomial k] completion (X : Polynomial k) (F k)) := by
  intro a b hab
  apply Finsupp.ext
  intro i
  apply Polynomial.ext
  intro d
  have h := congrArg (fun x : completion (X : Polynomial k) (F k) => x.val (d+1)) hab
  have hs : a-b∈powerSub (X : Polynomial k) (F k) (d+1) := (Submodule.Quotient.eq _).mp h
  have hz := low_coefficient_zero k (Nat.lt_succ_self d) hs i
  simpa only [Finsupp.sub_apply,Polynomial.coeff_sub,sub_eq_zero] using hz

theorem canonical_series (a : F k) (i : ℕ) :
    toSeries k (canonical (X : Polynomial k) a) i=(a i : Series k) := by
  apply PowerSeries.ext
  intro d
  rw [coeff_toSeries]
  change (a i).coeff d=PowerSeries.coeff d (a i : Series k)
  rw [Polynomial.coeff_coe]

theorem witness_not_original (a : F k) : canonical (X : Polynomial k) a≠witness k := by
  intro ha
  obtain ⟨i,hi⟩ := Infinite.exists_notMem_finset a.support
  have haz : a i=0 := Finsupp.notMem_support_iff.mp hi
  have h := congrArg (fun x : completion (X : Polynomial k) (F k) => x.val (i+1)) ha
  have hs : a-partialSum k (i+1)∈powerSub (X : Polynomial k) (F k) (i+1) :=
    (Submodule.Quotient.eq _).mp h
  have hz := low_coefficient_zero k (Nat.lt_succ_self i) hs i
  simp [Finsupp.sub_apply,haz,partialSum_apply] at hz


theorem original_not_surjective : ¬Function.Surjective (canonical (X : Polynomial k) :
    F k →ₗ[Polynomial k] completion (X : Polynomial k) (F k)) := by
  intro h
  obtain ⟨a,ha⟩ := h (witness k)
  exact witness_not_original k a ha

theorem witness_every_level_original (n : ℕ) :
    (witness k).val n=(powerSub (X : Polynomial k) (F k) n).mkQ (partialSum k n) := rfl

end MathGauge.OriginalImage
