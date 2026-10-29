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
