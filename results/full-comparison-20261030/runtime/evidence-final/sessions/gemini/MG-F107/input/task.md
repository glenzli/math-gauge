# 加权序列方程的逆与估计

令 $\mathcal S=\mathbb R^{\mathbb N}$，$w_n=n+1$，并定义
$$ (Tu)_n=u_n/w_n,\qquad
\operatorname{Control}(r,C,f)\iff\forall n\in\mathbb N:\ w_n^r|f_n|\le C.$$
称 $f$ 快速衰减，若对每个 $r\in\mathbb N$，存在非负实数 $C$ 使 $\operatorname{Control}(r,C,f)$。

目标是在全部实序列上构造线性逆 $S$，证明 $T(Sf)=f$，任意 $Tu=f$ 的解均等于 $Sf$，且 $S$ 保持快速衰减。还要求对任意 $r\in\mathbb N$、$C\in\mathbb R$、$f\in\mathcal S$ 有
$$\operatorname{Control}(r+1,C,f)\Longrightarrow\operatorname{Control}(r,C,Sf).$$
背景定义以附件 `Core.lean` 为准；允许使用 Mathlib 及经典逻辑。

附件 `Core.lean`、`Multiplier.lean`、`Candidate.lean` 被提交为这一目标的形式化。审核对外结果及其依赖是否完整对应目标，定位差异并给出数学依据；分别判断代码有效性、已覆盖结论和未覆盖结论。

Lean 4.29.1，Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6。


File: `Core.lean`
```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace MathGauge.F107
abbrev Seq := ℕ → ℝ
def weight (n : ℕ) : ℝ := n + 1
def Control (r : ℕ) (C : ℝ) (f : Seq) : Prop :=
  ∀ n, weight n ^ r * |f n| ≤ C
def Rapid (f : Seq) : Prop := ∀ r, ∃ C : ℝ, 0 ≤ C ∧ Control r C f
def transport (u : Seq) : Seq := fun n => u n / weight n
def solve (f : Seq) : Seq := fun n => weight n * f n

theorem weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity
theorem weight_one_le (n : ℕ) : 1 ≤ weight n := by unfold weight; linarith [Nat.cast_nonneg (α := ℝ) n]

theorem control_down {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 1) C f) : Control r C f := by
  intro n
  have hn : 0 ≤ weight n ^ r * |f n| := mul_nonneg (pow_nonneg (le_of_lt (weight_pos n)) _) (abs_nonneg _)
  calc
    weight n ^ r * |f n| ≤ (weight n ^ r * |f n|) * weight n :=
      le_mul_of_one_le_right hn (weight_one_le n)
    _ = weight n ^ (r + 1) * |f n| := by rw [pow_succ]; ring
    _ ≤ C := h n

end MathGauge.F107
```


File: `Multiplier.lean`
```lean
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
```


File: `Candidate.lean`
```lean
import Multiplier

noncomputable section
namespace MathGauge.F107

def InputControl (r : ℕ) (C : ℝ) (f : Seq) : Prop := Control (r + 2) C f

structure Result (r : ℕ) (C : ℝ) (f : Seq) where
  value : Seq
  solves : transport value = f
  unique : ∀ u, transport u = f → u = value
  estimate : Control r C value

def candidate (r : ℕ) (C : ℝ) (f : Seq) (h : InputControl r C f) : Result r C f where
  value := solve f
  solves := transport_solve f
  unique := fun u hu => solution_unique hu
  estimate := control_solve_buffered h

theorem candidate_rapid (r : ℕ) (C : ℝ) (f : Seq) (h : InputControl r C f)
    (hf : Rapid f) : Rapid (candidate r C f h).value := rapid_solve hf

#print axioms candidate
#print axioms candidate_rapid
end MathGauge.F107
```
