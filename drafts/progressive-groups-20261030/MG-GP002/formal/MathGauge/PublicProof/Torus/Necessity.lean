import MathGauge.PublicProof.Torus.GeneralInverse
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
namespace MathGauge.PublicProof.Torus
open scoped BigOperators Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

private lemma weight_one_le (k : PairFrequency) :
    1 ≤ Borrowed.TorusInverse.weight k := by
  dsimp [Borrowed.TorusInverse.weight]
  have h₁ := abs_nonneg (k.1 : ℝ)
  have h₂ := abs_nonneg (k.2 : ℝ)
  linarith

private lemma finite_positive_bound {α : ℝ} (hα : Irrational α)
    (n : ℕ) (s : Finset PairFrequency) :
    ∃ c : ℝ, 0 < c ∧ ∀ k ∈ s, k ≠ 0 →
      c ≤ Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert k s hks ih =>
    obtain ⟨c, hc, hs⟩ := ih
    by_cases hk : k = 0
    · refine ⟨c, hc, ?_⟩
      intro j hj hj0
      rcases Finset.mem_insert.mp hj with h | h
      · exact False.elim (hj0 (h.trans hk))
      · exact hs j h hj0
    · let d := Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k|
      have hd : 0 < d :=
        mul_pos (pow_pos (Borrowed.TorusInverse.weight_pos _) _)
          (abs_pos.mpr (pairDivisor_ne_zero hα k hk))
      refine ⟨min c d, lt_min hc hd, ?_⟩
      intro j hj hj0
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj hj0)

private lemma small_outside_finite {α : ℝ} (hα : Irrational α)
    (hbad : ¬ PolynomialDivisorBound α) (n : ℕ) (c : ℝ) (hc : 0 < c)
    (s : Finset PairFrequency) :
    ∃ k : PairFrequency, k ∉ s ∧ k ≠ 0 ∧
      Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k| < c := by
  obtain ⟨d, hd, hs⟩ := finite_positive_bound hα n s
  have h : ∃ k : PairFrequency, k ≠ 0 ∧
      Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k| < min c d := by
    by_contra hn
    push Not at hn
    exact hbad ⟨n, min c d, lt_min hc hd, hn⟩
  obtain ⟨k, hk, hkc⟩ := h
  refine ⟨k, ?_, hk, hkc.trans_le (min_le_left _ _)⟩
  intro hks
  exact (not_lt_of_ge (hs k hks hk)) (hkc.trans_le (min_le_right _ _))

private def chooseSequence {ι : Type*} [DecidableEq ι]
    (pick : ℕ → Finset ι → ι) (n : ℕ) : ι :=
  pick n ((Finset.range n).attach.image (fun i => chooseSequence pick i.1))
termination_by n
decreasing_by exact Finset.mem_range.mp i.2

private lemma chooseSequence_property {ι : Type*} [DecidableEq ι]
    (P : ℕ → ι → Prop) (pick : ℕ → Finset ι → ι)
    (hpick : ∀ n s, pick n s ∉ s ∧ P n (pick n s)) :
    Function.Injective (chooseSequence pick) ∧ ∀ n, P n (chooseSequence pick n) := by
  have hprop (n : ℕ) : P n (chooseSequence pick n) := by
    rw [chooseSequence]
    exact (hpick _ _).2
  have hne (m n : ℕ) (hlt : m < n) : chooseSequence pick m ≠ chooseSequence pick n := by
    intro he
    have hnot : chooseSequence pick n ∉
        ((Finset.range n).attach.image (fun i => chooseSequence pick i.1)) := by
      nth_rw 1 [chooseSequence]
      exact (hpick n _).1
    apply hnot
    rw [← he]
    exact Finset.mem_image.mpr
      ⟨⟨m, Finset.mem_range.mpr hlt⟩, Finset.mem_attach _ _, rfl⟩
  refine ⟨?_, hprop⟩
  intro m n he
  exact le_antisymm (le_of_not_gt (fun h => hne n m h he.symm))
    (le_of_not_gt (fun h => hne m n h he))

theorem bad_frequency_sequence {α : ℝ} (hα : Irrational α)
    (hbad : ¬ PolynomialDivisorBound α) :
    ∃ q : ℕ → PairFrequency, Function.Injective q ∧
      ∀ n, q n ≠ 0 ∧
        Borrowed.TorusInverse.weight (q n) ^ n *
          ‖((n + 1 : ℕ) : ℂ) * (omega * (pairDivisor α (q n) : ℂ))‖ ≤ (1/2 : ℝ)^n := by
  classical
  have hc (n : ℕ) : 0 < (1/2 : ℝ)^n / (((n : ℝ) + 1) * ‖omega‖) := by
    exact div_pos (pow_pos (by norm_num) _) (mul_pos (by positivity) (norm_pos_iff.mpr omega_ne_zero))
  choose pick hpick using
    (fun (n : ℕ) (s : Finset PairFrequency) =>
      small_outside_finite hα hbad n
        ((1/2 : ℝ)^n / (((n : ℝ) + 1) * ‖omega‖)) (hc n) s)
  let P := fun n k => k ≠ (0 : PairFrequency) ∧
    Borrowed.TorusInverse.weight k ^ n *
      ‖((n + 1 : ℕ) : ℂ) * (omega * (pairDivisor α k : ℂ))‖ ≤ (1/2 : ℝ)^n
  have hP : ∀ n s, pick n s ∉ s ∧ P n (pick n s) := by
    intro n s
    refine ⟨(hpick n s).1, (hpick n s).2.1, ?_⟩
    have h := (lt_div_iff₀ (mul_pos (by positivity : (0:ℝ) < n+1)
      (norm_pos_iff.mpr omega_ne_zero))).mp (hpick n s).2.2
    have hn : ‖((n + 1 : ℕ) : ℂ)‖ = (n : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
    rw [norm_mul, hn, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith
  obtain ⟨hq, hqp⟩ := chooseSequence_property P pick hP
  exact ⟨chooseSequence pick, hq, hqp⟩




/-- A smooth forcing's coefficient sequence with unbounded formal inverse. -/
theorem exists_rapid_bad_inverse {α : ℝ} (hα : Irrational α)
    (hbad : ¬ PolynomialDivisorBound α) :
    ∃ a : PairFrequency → ℂ, Rapid a ∧ a 0 = 0 ∧
      ∀ C : ℝ, ∃ k : PairFrequency, C < ‖generalInverseCoefficients α a k‖ := by
  classical
  obtain ⟨q, hq, hqb⟩ := bad_frequency_sequence hα hbad
  let b : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) * (omega * (pairDivisor α (q n) : ℂ))
  let a : PairFrequency → ℂ := Function.extend q b (fun _ => 0)
  have hval (n : ℕ) : a (q n) = b n := hq.extend_apply b (fun _ => 0) n
  have hout (k : PairFrequency) (hk : k ∉ Set.range q) : a k = 0 :=
    Function.extend_apply' b (fun _ => 0) k hk
  have hrapid : Rapid a := by
    intro p
    have hsum : Summable (fun n => Borrowed.TorusInverse.weight (q n) ^ p * ‖b n‖) := by
      apply (summable_geometric_of_norm_lt_one
        (by norm_num : ‖(1/2 : ℝ)‖ < 1)).of_norm_bounded_eventually_nat
      filter_upwards [Filter.eventually_ge_atTop p] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (pow_nonneg (Borrowed.TorusInverse.weight_pos _).le _) (norm_nonneg _))]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (weight_one_le _) hn) (norm_nonneg _)).trans (hqb n).2
    apply (hq.summable_iff (f := fun k => Borrowed.TorusInverse.weight k ^ p * ‖a k‖) ?_).mp
    · simpa only [Function.comp_def, hval] using hsum
    · intro k hk
      simp [hout k hk]
  have ha0 : a 0 = 0 := by
    apply hout
    rintro ⟨n, hn⟩
    exact (hqb n).1 hn
  have hinv (n : ℕ) : generalInverseCoefficients α a (q n) = ((n + 1 : ℕ) : ℂ) := by
    have hd : omega * (pairDivisor α (q n) : ℂ) ≠ 0 :=
      mul_ne_zero omega_ne_zero (Complex.ofReal_ne_zero.mpr
        (pairDivisor_ne_zero hα (q n) (hqb n).1))
    change (omega * (pairDivisor α (q n) : ℂ))⁻¹ * a (q n) = _
    rw [hval]
    dsimp only [b]
    rw [mul_comm (((n + 1 : ℕ) : ℂ)), ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  refine ⟨a, hrapid, ha0, ?_⟩
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨q n, ?_⟩
  rw [hinv]
  have hnrm : ‖((n + 1 : ℕ) : ℂ)‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  rw [hnrm]
  linarith

end MathGauge.PublicProof.Torus
