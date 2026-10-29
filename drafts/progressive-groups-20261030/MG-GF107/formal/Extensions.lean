import Reference
import Candidate

noncomputable section
namespace MathGauge.F107

/-- A single fixed support bound gives one constant for every input with that support. -/
theorem control_solve_supported {r M : ℕ} {C : ℝ} {f : Seq}
    (hC : 0 ≤ C) (hs : ∀ n, M < n → f n = 0) (h : Control r C f) :
    Control r (((M : ℝ) + 1) * C) (solve f) := by
  intro n
  by_cases hn : n ≤ M
  · calc
      weight n ^ r * |solve f n| = weight n * (weight n ^ r * |f n|) := by
        rw [weighted_identity, pow_succ]; ring
      _ ≤ weight n * C := mul_le_mul_of_nonneg_left (h n) (le_of_lt (weight_pos n))
      _ ≤ ((M : ℝ) + 1) * C := by
        apply mul_le_mul_of_nonneg_right _ hC
        change (n : ℝ) + 1 ≤ (M : ℝ) + 1
        exact_mod_cast Nat.add_le_add_right hn 1
  · have hz := hs n (Nat.lt_of_not_ge hn)
    simp only [solve, hz, mul_zero, abs_zero]
    positivity

theorem spike_rapid (N : ℕ) : Rapid (spike N) := by
  intro r
  refine ⟨weight N ^ r, pow_nonneg (le_of_lt (weight_pos N)) _, ?_⟩
  intro n
  by_cases hn : n = N
  · subst n; simp [spike]
  · simp only [spike, if_neg hn, abs_zero, mul_zero]
    exact pow_nonneg (le_of_lt (weight_pos N)) _

/-- The quantifiers are ∄D ∀f, with Rapid retained in the quantified class. -/
theorem no_uniform_rapid_zero_loss : ¬ ∃ D : ℝ, 0 ≤ D ∧ ∀ f : Seq,
    Rapid f → Control 0 1 f → Control 0 D (solve f) := by
  rintro ⟨D, _, h⟩
  obtain ⟨N, hN⟩ := exists_nat_gt D
  have bound := h (spike N) (spike_rapid N) (spike_control N) N
  simp [solve, spike, weight, abs_of_pos (show (0 : ℝ) < N + 1 by positivity)] at bound
  linarith

theorem rapid_individual_zero_bound {f : Seq} (hf : Rapid f) :
    ∃ D : ℝ, 0 ≤ D ∧ Control 0 D (solve f) := by
  obtain ⟨D, hD, h⟩ := hf 1
  exact ⟨D, hD, control_solve h⟩

theorem candidate_input_exact (r : ℕ) (C : ℝ) (f : Seq) :
    InputControl r C f ↔ Control (r + 2) C f := Iff.rfl

theorem buffered_interface_gap :
    Control 1 1 witness ∧ ¬ InputControl 0 1 witness :=
  ⟨witness_input, witness_extra_fails⟩

end MathGauge.F107
