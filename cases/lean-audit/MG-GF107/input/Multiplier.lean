import Core

noncomputable section
namespace MathGauge.F107
theorem transport_solve (f : Seq) : transport (solve f) = f := by
  funext n
  simp [transport, solve, ne_of_gt (weight_pos n)]

theorem solve_transport (u : Seq) : solve (transport u) = u := by
  funext n
  dsimp [transport, solve]
  field_simp [ne_of_gt (weight_pos n)]

theorem solution_unique {f u : Seq} (h : transport u = f) : u = solve f := by
  rw [← h, solve_transport]

theorem solve_add (f g : Seq) : solve (f + g) = solve f + solve g := by
  funext n
  simp [solve, mul_add]

theorem solve_smul (a : ℝ) (f : Seq) : solve (a • f) = a • solve f := by
  funext n
  simp [solve]
  ring

theorem control_solve_buffered {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 2) C f) : Control r C (solve f) := by
  intro n
  have hd := control_down h n
  calc
    weight n ^ r * |solve f n| = weight n ^ (r + 1) * |f n| := by
      rw [solve, abs_mul, abs_of_pos (weight_pos n), pow_succ]
      ring
    _ ≤ C := hd

theorem rapid_solve {f : Seq} (h : Rapid f) : Rapid (solve f) := by
  intro r
  obtain ⟨C, hC, hb⟩ := h (r + 2)
  exact ⟨C, hC, control_solve_buffered hb⟩

end MathGauge.F107
