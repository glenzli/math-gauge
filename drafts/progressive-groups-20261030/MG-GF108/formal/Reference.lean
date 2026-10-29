import Multiplier

noncomputable section
namespace MathGauge.F108

theorem weighted_identity (r n : ℕ) (f : Seq) :
    weight n ^ r * |solve f n| = weight n ^ (r + 1) * |f n| := by
  rw [solve, abs_mul, abs_of_pos (weight_pos n), pow_succ]
  ring

theorem control_solve {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 1) C f) : Control r C (solve f) := by
  intro n
  rw [weighted_identity]
  exact h n

structure CompleteResult (r : ℕ) (C : ℝ) (f : Seq) where
  value : Seq
  solves : transport value = f
  unique : ∀ u, transport u = f → u = value
  estimate : Control r C value

def complete (r : ℕ) (C : ℝ) (f : Seq) (h : Control (r + 1) C f) : CompleteResult r C f where
  value := solve f
  solves := transport_solve f
  unique := fun u hu => solution_unique hu
  estimate := control_solve h

theorem complete_rapid (r : ℕ) (C : ℝ) (f : Seq) (h : Control (r + 1) C f)
    (hf : Rapid f) : Rapid (complete r C f h).value := rapid_solve hf

def witness : Seq := fun n => if n = 1 then (1 / 2 : ℝ) else 0

theorem witness_input : Control 1 1 witness := by
  intro n
  by_cases hn : n = 1
  · subst n; norm_num [weight, witness]
  · simp [witness, hn]

theorem witness_extra_fails : ¬ Control 2 1 witness := by
  intro h
  have := h 1
  norm_num [weight, witness] at this

theorem witness_output : Control 0 1 (solve witness) := by
  exact control_solve witness_input

def spike (N : ℕ) : Seq := fun n => if n = N then 1 else 0

theorem spike_control (N : ℕ) : Control 0 1 (spike N) := by
  intro n
  by_cases hn : n = N <;> simp [spike, hn]

theorem no_uniform_zero_loss : ¬ ∃ C : ℝ, ∀ f : Seq,
    Control 0 1 f → Control 0 C (solve f) := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  have h := hC (spike N) (spike_control N) N
  simp [solve, spike, weight, abs_of_pos (show (0 : ℝ) < N + 1 by positivity)] at h
  linarith

#print axioms complete
#print axioms complete_rapid
#print axioms witness_extra_fails
#print axioms no_uniform_zero_loss
end MathGauge.F108
