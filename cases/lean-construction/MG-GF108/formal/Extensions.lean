import Reference
import Candidate

noncomputable section
namespace MathGauge.F108

def variable_transport (v u : Seq) : Seq := fun n => u n / v n
def variable_solve (v f : Seq) : Seq := fun n => v n * f n
def VariableControl (v : Seq) (r : ℕ) (C : ℝ) (f : Seq) : Prop :=
  ∀ n, v n ^ r * |f n| ≤ C
def VariableRapid (v f : Seq) : Prop :=
  ∀ r, ∃ C : ℝ, 0 ≤ C ∧ VariableControl v r C f

theorem variable_transport_solve (v f : Seq) (hv : ∀ n, 0 < v n) :
    variable_transport v (variable_solve v f) = f := by
  funext n; simp [variable_transport, variable_solve, ne_of_gt (hv n)]

theorem variable_solve_transport (v u : Seq) (hv : ∀ n, 0 < v n) :
    variable_solve v (variable_transport v u) = u := by
  funext n
  dsimp [variable_transport, variable_solve]
  field_simp [ne_of_gt (hv n)]

theorem variable_solution_unique {v f u : Seq} (hv : ∀ n, 0 < v n)
    (h : variable_transport v u = f) : u = variable_solve v f := by
  rw [← h, variable_solve_transport v u hv]

def variable_solve_linear (v : Seq) : Seq →ₗ[ℝ] Seq where
  toFun := variable_solve v
  map_add' f g := by funext n; simp [variable_solve, mul_add]
  map_smul' a f := by funext n; simp [variable_solve]; ring

theorem variable_weighted_identity (v f : Seq) (hv : ∀ n, 0 ≤ v n) (r n : ℕ) :
    v n ^ r * |variable_solve v f n| = v n ^ (r + 1) * |f n| := by
  rw [variable_solve, abs_mul, abs_of_nonneg (hv n), pow_succ]
  ring

theorem variable_control_solve {v f : Seq} (hv : ∀ n, 0 ≤ v n) {r : ℕ} {C : ℝ}
    (h : VariableControl v (r + 1) C f) : VariableControl v r C (variable_solve v f) := by
  intro n; rw [variable_weighted_identity v f hv]; exact h n

theorem variable_rapid_solve {v f : Seq} (hv : ∀ n, 0 ≤ v n)
    (h : VariableRapid v f) : VariableRapid v (variable_solve v f) := by
  intro r
  obtain ⟨C, hC, hc⟩ := h (r + 1)
  exact ⟨C, hC, variable_control_solve hv hc⟩

theorem positive_of_one_le {v : Seq} (hv : ∀ n, 1 ≤ v n) : ∀ n, 0 < v n :=
  fun n => lt_of_lt_of_le zero_lt_one (hv n)

theorem zero_weight_no_solution {v : Seq} {n₀ : ℕ} (hv : v n₀ = 0) :
    ¬ ∃ u : Seq, variable_transport v u = spike n₀ := by
  rintro ⟨u, hu⟩
  have := congrFun hu n₀
  simp [variable_transport, hv, spike] at this

theorem zero_weight_nonunique {v : Seq} {n₀ : ℕ} (hv : v n₀ = 0) :
    variable_transport v (0 : Seq) = 0 ∧
    variable_transport v (spike n₀) = 0 ∧ spike n₀ ≠ 0 := by
  refine ⟨by ext n; simp [variable_transport], ?_, ?_⟩
  · funext n
    by_cases hn : n = n₀
    · subst n; simp [variable_transport, spike, hv]
    · simp [variable_transport, spike, hn]
  · intro h
    have := congrFun h n₀
    simp [spike] at this

theorem zero_weight_not_left_inverse {v : Seq} {n₀ : ℕ} (hv : v n₀ = 0) :
    ¬ Function.LeftInverse (variable_solve v) (variable_transport v) := by
  intro h
  have := congrFun (h (spike n₀)) n₀
  simp [variable_solve, variable_transport, spike, hv] at this

theorem zero_control_eq_zero {r : ℕ} {f : Seq} (h : Control r 0 f) : f = 0 := by
  funext n
  have hp : 0 < weight n ^ r := pow_pos (weight_pos n) _
  have ha : |f n| ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge (h n)) (mul_pos hp (lt_of_not_ge hn))
  exact abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))

theorem zero_control_solve {r : ℕ} {f : Seq} (h : Control r 0 f) :
    Control r 0 (solve f) := by
  rw [zero_control_eq_zero h]
  intro n; simp [solve]

theorem repaired_input_exact (r : ℕ) (C : ℝ) (f : Seq) :
    InputControl r C f ↔ Control (r + 1) C f := Iff.rfl

end MathGauge.F108
