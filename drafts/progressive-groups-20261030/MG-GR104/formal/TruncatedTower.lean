import NilpotentDescent
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
open Polynomial
namespace MathGauge.GR104
open MathGauge.R104
variable (k : Type*) [Field k]

/-- Lean index n is the question's positive index n+1. -/
def truncIdeal (n : ℕ) : Ideal k[X] := Ideal.span {(X : k[X]) ^ (n + 2)}
abbrev Truncation (n : ℕ) := k[X] ⧸ truncIdeal k n

theorem truncIdeal_antitone {i j : ℕ} (h : i ≤ j) : truncIdeal k j ≤ truncIdeal k i := by
  rw [truncIdeal, Ideal.span_singleton_le_iff_mem, truncIdeal, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ (by omega)

def truncTransition {i j : ℕ} (h : i ≤ j) : Truncation k j →+* Truncation k i :=
  Ideal.Quotient.factor (truncIdeal_antitone k h)

theorem truncConstant_vanish (n : ℕ) (f : k[X]) (hf : f ∈ truncIdeal k n) :
    constantCoeff f = 0 := by
  rw [truncIdeal, Ideal.mem_span_singleton] at hf
  obtain ⟨g, rfl⟩ := hf
  simp

def truncAugmentation (n : ℕ) : Truncation k n →+* k :=
  Ideal.Quotient.lift _ constantCoeff (truncConstant_vanish k n)

theorem truncAugmentation_surjective (n : ℕ) : Function.Surjective (truncAugmentation k n) := by
  intro a
  exact ⟨Ideal.Quotient.mk _ (C a), by simp [truncAugmentation]⟩

theorem truncKernel_nil (n : ℕ) (a : Truncation k n) (ha : truncAugmentation k n a = 0) :
    IsNilpotent a := by
  induction a using Quotient.inductionOn' with
  | h f =>
      have hf : f.coeff 0 = 0 := by simpa [truncAugmentation] using ha
      have hd : (X : k[X]) ^ (n + 2) ∣ f ^ (n + 2) := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) _
      refine ⟨n + 2, ?_⟩
      change (Ideal.Quotient.mk (truncIdeal k n) f) ^ (n + 2) = 0
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, truncIdeal, Ideal.mem_span_singleton]
      exact hd

theorem truncTransition_id (i : ℕ) (x : Truncation k i) :
    truncTransition k (le_refl i) x = x := by
  induction x using Quotient.inductionOn' with
  | h f => rfl

theorem truncTransition_comp {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l)
    (x : Truncation k l) :
    truncTransition k hij (truncTransition k hjl x) = truncTransition k (hij.trans hjl) x := by
  exact Ideal.Quotient.factor_comp_apply (truncIdeal_antitone k hjl) (truncIdeal_antitone k hij) x

theorem truncAugmentation_transition {i j : ℕ} (hij : i ≤ j) (x : Truncation k j) :
    truncAugmentation k i (truncTransition k hij x) = truncAugmentation k j x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [truncTransition, Ideal.Quotient.factor_mk, truncAugmentation, Ideal.Quotient.lift_mk]

def truncatedSystem : System ℕ (Truncation k) k where
  transition := fun h => truncTransition k h
  transition_id := truncTransition_id k
  transition_comp := truncTransition_comp k
  augmentation := truncAugmentation k
  augmentation_surjective := truncAugmentation_surjective k
  augmentation_transition := truncAugmentation_transition k
  nil_kernel := truncKernel_nil k

def coherentVariable : (truncatedSystem k).Limit :=
  ⟨fun n => Ideal.Quotient.mk _ X, fun _ _ _ => rfl⟩

theorem coherentVariable_in_kernel (n : ℕ) :
    (truncatedSystem k).limit_augmentation n (coherentVariable k) = 0 := by
  change constantCoeff (X : k[X]) = 0
  simp

theorem coherentVariable_power_ne_zero (N : ℕ) : (coherentVariable k) ^ N ≠ 0 := by
  intro h
  have hn := congrArg ((truncatedSystem k).evaluation N) h
  change (Ideal.Quotient.mk (truncIdeal k N) (X : k[X])) ^ N = 0 at hn
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, truncIdeal, Ideal.mem_span_singleton] at hn
  have hc := (X_pow_dvd_iff.mp hn) N (by omega)
  simpa using hc

theorem limit_kernel_not_nil :
    ¬ ∀ a : (truncatedSystem k).Limit,
      (truncatedSystem k).limit_augmentation 0 a = 0 → IsNilpotent a := by
  intro h
  obtain ⟨N, hN⟩ := h (coherentVariable k) (coherentVariable_in_kernel k 0)
  exact coherentVariable_power_ne_zero k N hN

/-- The same actual system satisfies the hypotheses for unique idempotent lifts. -/
theorem truncated_idempotents_still_lift (e : k) (he : IsIdempotentElem e) :
    ∃! a : (truncatedSystem k).Limit,
      IsIdempotentElem a ∧ (truncatedSystem k).limit_augmentation 0 a = e :=
  (truncatedSystem k).unique_limit_lift
    (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩) 0 e he

end MathGauge.GR104
