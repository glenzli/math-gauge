import Core

noncomputable section
namespace MathGauge.F108
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

/-- 紧确的一阶权控制传递：Control (r + 1) C f 蕴含 Control r C (solve f)。
    此结论为修订后新增证明，原文件仅证明了 Control (r + 2) C f 的带缓冲版本。 -/
theorem control_solve {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 1) C f) : Control r C (solve f) := by
  intro n
  calc
    weight n ^ r * |solve f n| = weight n ^ (r + 1) * |f n| := by
      rw [solve, abs_mul, abs_of_pos (weight_pos n), pow_succ]
      ring
    _ ≤ C := h n

/-- 原文件的带缓冲估计，现作为紧确估计 control_solve 与 control_down 的推论保留。 -/
theorem control_solve_buffered {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 2) C f) : Control r C (solve f) :=
  control_solve (control_down h)

theorem rapid_solve {f : Seq} (h : Rapid f) : Rapid (solve f) := by
  intro r
  obtain ⟨C, hC, hb⟩ := h (r + 1)
  exact ⟨C, hC, control_solve hb⟩

end MathGauge.F108
