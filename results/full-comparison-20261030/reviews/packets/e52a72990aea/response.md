修订的关键是将输入条件从 `Control (r + 2) C f` 放宽为目标要求的 `Control (r + 1) C f`。下面的 `S : Seq ≃ₗ[ℝ] Seq` 在所有实序列上定义；`transport_S`、`solution_unique_S`、`control_S` 和 `rapid_S` 分别给出所需的逆、唯一性、估计和快速衰减声明。

逐点估计实际上是等式：
\[
w_n^r |(Sf)_n|=w_n^{r+1}|f_n|.
\]
因此 `control_S` 对任意实数 \(C\) 成立。`rapid_solve` 只需取输入的 \(r+1\) 阶控制。原来的较强估计 `control_solve_buffered` 也作为推论保留。

**验证限制：**当前执行工具无法启动，因此未能在指定的 Lean 4.29.1 和 Mathlib 版本下实际编译以下源码。`Core.lean` 的背景定义及其含义保持不变；以下列出三个完整文件。

`Core.lean`

```lean
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
```

`Multiplier.lean`

```lean
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
```

`Candidate.lean`

```lean
import Multiplier

noncomputable section
namespace MathGauge.F108

def InputControl (r : ℕ) (C : ℝ) (f : Seq) : Prop :=
  Control (r + 1) C f

structure Result (r : ℕ) (C : ℝ) (f : Seq) where
  value : Seq
  solves : transport value = f
  unique : ∀ u, transport u = f → u = value
  estimate : Control r C value

def candidate (r : ℕ) (C : ℝ) (f : Seq)
    (h : InputControl r C f) : Result r C f where
  value := S f
  solves := transport_S f
  unique := fun u hu => solution_unique_S hu
  estimate := control_S r C f h

theorem candidate_rapid (r : ℕ) (C : ℝ) (f : Seq)
    (h : InputControl r C f) (hf : Rapid f) :
    Rapid (candidate r C f h).value := by
  change Rapid (S f)
  exact rapid_S hf

#print axioms S
#print axioms transport_S
#print axioms S_transport
#print axioms solution_unique_S
#print axioms control_S
#print axioms rapid_S
#print axioms candidate
#print axioms candidate_rapid

end MathGauge.F108
```