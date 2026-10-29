import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace MathGauge.F108

abbrev Seq := ℕ → ℝ

def weight (n : ℕ) : ℝ := n + 1

def Control (r : ℕ) (C : ℝ) (f : Seq) : Prop :=
  ∀ n, weight n ^ r * |f n| ≤ C

def Rapid (f : Seq) : Prop :=
  ∀ r, ∃ C : ℝ, 0 ≤ C ∧ Control r C f

def transport (u : Seq) : Seq := fun n => u n / weight n

def solve (f : Seq) : Seq := fun n => weight n * f n

theorem weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  positivity

theorem weight_one_le (n : ℕ) : 1 ≤ weight n := by
  unfold weight
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem control_down {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 1) C f) : Control r C f := by
  intro n
  have hn : 0 ≤ weight n ^ r * |f n| :=
    mul_nonneg (pow_nonneg (le_of_lt (weight_pos n)) _) (abs_nonneg _)
  calc
    weight n ^ r * |f n| ≤ (weight n ^ r * |f n|) * weight n :=
      le_mul_of_one_le_right hn (weight_one_le n)
    _ = weight n ^ (r + 1) * |f n| := by
      rw [pow_succ]
      ring
    _ ≤ C := h n

end MathGauge.F108
