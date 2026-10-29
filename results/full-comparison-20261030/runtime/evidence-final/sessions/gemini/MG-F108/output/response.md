对附件 `Core.lean`、`Multiplier.lean` 与 `Candidate.lean` 进行全面检查与修订。

---

### 原文件问题分析与修订要点

1. **原文件未证明目标所需的一阶控制估计**：
   - 原 `Multiplier.lean` 中仅证明了带有人为缓冲（损失 2 阶权）的引理 `control_solve_buffered`：
     $$\operatorname{Control}(r+2, C, f) \Longrightarrow \operatorname{Control}(r, C, S f)$$
     其证明过程中通过多余的 `have hd := control_down h n` 使得输入条件被不必要地放宽到 $r+2$ 阶。
   - 原 `Candidate.lean` 相应地将输入条件定义为 `InputControl r C f := Control (r + 2) C f`，未能达到题设严格要求的 $\operatorname{Control}(r+1, C, f) \Longrightarrow \operatorname{Control}(r, C, S f)$。
   - **不得将修订后的精细结果误述为原文件已证**：原文件中**并未**包含 $r+1$ 到 $r$ 的紧确控制估计，该结果为本次修订新增证明。

2. **修订策略**：
   - **`Core.lean`**：经检查，背景定义（序列空间 `Seq`、权重 `weight`、控制谓词 `Control`、快速衰减 `Rapid`、算子 `transport` 与 `solve`）及其基本性质（`weight_pos`、`weight_one_le`、`control_down`）形式化严谨正确，完全符合题意，予以保留。
   - **`Multiplier.lean`**：
     - 新增紧确估计定理 `control_solve`，证明对任意 $r, C, f$，$\operatorname{Control}(r+1, C, f) \Longrightarrow \operatorname{Control}(r, C, \operatorname{solve} f)$。
     - 保留 `control_solve_buffered` 作为 `control_solve` 复合 `control_down` 的直接推论，保证向后兼容。
     - 将快速衰减传递定理 `rapid_solve` 升级为使用紧确的 $r+1$ 阶控制与 `control_solve`。
     - 保留并确认逆算子性质（`transport_solve`、`solve_transport`）、解的唯一性（`solution_unique`）及实线性（`solve_add`、`solve_smul`）。
   - **`Candidate.lean`**：
     - 将 `InputControl r C f` 紧缩修正为 `Control (r + 1) C f`。
     - 将 `candidate` 结构体的 `estimate` 字段由原 `control_solve_buffered h` 修订为 `control_solve h`。
     - 保留 `candidate_rapid` 并验证其公理依赖。

---

### 修订后完整源码交付

#### File: `Core.lean`
```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace MathGauge.F108
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

end MathGauge.F108
```

#### File: `Multiplier.lean`
```lean
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
```

#### File: `Candidate.lean`
```lean
import Multiplier

noncomputable section
namespace MathGauge.F108

/-- 输入控制条件：由原文件的 Control (r + 2) C f 修订为目标的紧确条件 Control (r + 1) C f。 -/
def InputControl (r : ℕ) (C : ℝ) (f : Seq) : Prop := Control (r + 1) C f

structure Result (r : ℕ) (C : ℝ) (f : Seq) where
  value : Seq
  solves : transport value = f
  unique : ∀ u, transport u = f → u = value
  estimate : Control r C value

/-- 候选解构造：使用新增的紧确估计 control_solve 替代原有的 control_solve_buffered。 -/
def candidate (r : ℕ) (C : ℝ) (f : Seq) (h : InputControl r C f) : Result r C f where
  value := solve f
  solves := transport_solve f
  unique := fun u hu => solution_unique hu
  estimate := control_solve h

theorem candidate_rapid (r : ℕ) (C : ℝ) (f : Seq) (h : InputControl r C f)
    (hf : Rapid f) : Rapid (candidate r C f h).value := rapid_solve hf

#print axioms candidate
#print axioms candidate_rapid
end MathGauge.F108
```

---

### 最终声明及修订理由说明

1. **`control_solve`（新增定理）**：
   - **声明**：`theorem control_solve {r : ℕ} {C : ℝ} {f : Seq} (h : Control (r + 1) C f) : Control r C (solve f)`。
   - **修订理由**：直接对 $w_n^r |(Sf)_n| = w_n^r \cdot (w_n |f_n|) = w_n^{r+1}|f_n|$ 进行代数展开后，恰好等于输入序列在 $r+1$ 阶的控制项，直接由假设 $h\ n$ 给出 $\le C$。无需且不应调用 `control_down`，精确实现了题设的 $\operatorname{Control}(r+1, C, f) \Longrightarrow \operatorname{Control}(r, C, Sf)$。

2. **`control_solve_buffered`（重构推论）**：
   - **声明**：`theorem control_solve_buffered (h : Control (r + 2) C f) : Control r C (solve f) := control_solve (control_down h)`。
   - **修订理由**：原文件将两步权降解写在计算块中；重构后将其作为紧确结果的推论，保持原有接口不被破坏。

3. **`rapid_solve`（优化假设阶数）**：
   - **声明**：`theorem rapid_solve {f : Seq} (h : Rapid f) : Rapid (solve f)`。
   - **修订理由**：原文件在证明快速衰减时，对于阶数 $r$ 取了输入条件的 $r+2$ 阶；修订后只需取 $r+1$ 阶，并结合紧确的 `control_solve` 证明输出的快速衰减性。

4. **`InputControl` 与 `candidate`（紧缩前置条件）**：
   - **声明**：
     - `def InputControl (r : ℕ) (C : ℝ) (f : Seq) : Prop := Control (r + 1) C f`
     - `def candidate ... estimate := control_solve h`
   - **修订理由**：原文件的 `InputControl` 要求输入满足 $r+2$ 阶控制，无法满足要求在 $\operatorname{Control}(r+1, C, f)$ 假设下得到输出 $r$ 阶控制的目标。修订后前置条件降为 $r+1$ 阶，且打包结构体 `Result` 依然保证了求解性（`solves`）、解的唯一性（`unique`）与对应估计（`estimate`）。
