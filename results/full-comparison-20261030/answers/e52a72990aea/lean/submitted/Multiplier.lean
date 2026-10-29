import Core

noncomputable section
namespace MathGauge.F108

theorem transport_solve (f : Seq) : transport (solve f) = f := by
  funext n
  dsimp [transport, solve]
  field_simp [ne_of_gt (weight_pos n)] <;> ring

theorem solve_transport (u : Seq) : solve (transport u) = u := by
  funext n
  dsimp [transport, solve]
  field_simp [ne_of_gt (weight_pos n)] <;> ring

theorem solution_unique {f u : Seq} (h : transport u = f) :
    u = solve f := by
  rw [← h, solve_transport]

theorem solve_add (f g : Seq) :
    solve (f + g) = solve f + solve g := by
  funext n
  simp [solve, mul_add]

theorem solve_smul (a : ℝ) (f : Seq) :
    solve (a • f) = a • solve f := by
  funext n
  simp [solve, smul_eq_mul] <;> ring

/-- The inverse of transport, defined on all real sequences. -/
def S : Seq ≃ₗ[ℝ] Seq where
  toFun := solve
  invFun := transport
  left_inv := transport_solve
  right_inv := solve_transport
  map_add' := solve_add
  map_smul' := solve_smul

theorem S_add (f g : Seq) : S (f + g) = S f + S g := by
  change solve (f + g) = solve f + solve g
  exact solve_add f g

theorem S_smul (a : ℝ) (f : Seq) : S (a • f) = a • S f := by
  change solve (a • f) = a • solve f
  exact solve_smul a f

theorem transport_S (f : Seq) : transport (S f) = f := by
  change transport (solve f) = f
  exact transport_solve f

theorem S_transport (u : Seq) : S (transport u) = u := by
  change solve (transport u) = u
  exact solve_transport u

theorem solution_unique_S {f u : Seq} (h : transport u = f) :
    u = S f := by
  change u = solve f
  exact solution_unique h

theorem control_solve {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 1) C f) : Control r C (solve f) := by
  intro n
  calc
    weight n ^ r * |solve f n| =
        weight n ^ (r + 1) * |f n| := by
      simp only [solve, abs_mul, abs_of_pos (weight_pos n), pow_succ]
      ring
    _ ≤ C := h n

/-- The original two-step assumption remains available as a corollary. -/
theorem control_solve_buffered {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 2) C f) : Control r C (solve f) := by
  apply control_solve
  exact control_down h

theorem control_S (r : ℕ) (C : ℝ) (f : Seq)
    (h : Control (r + 1) C f) : Control r C (S f) := by
  change Control r C (solve f)
  exact control_solve h

theorem rapid_solve {f : Seq} (h : Rapid f) : Rapid (solve f) := by
  intro r
  obtain ⟨C, hC, hb⟩ := h (r + 1)
  exact ⟨C, hC, control_solve hb⟩

theorem rapid_S {f : Seq} (h : Rapid f) : Rapid (S f) := by
  change Rapid (solve f)
  exact rapid_solve h

end MathGauge.F108
