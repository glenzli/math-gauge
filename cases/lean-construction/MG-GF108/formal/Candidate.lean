import Reference

noncomputable section
namespace MathGauge.F108

def InputControl (r : ℕ) (C : ℝ) (f : Seq) : Prop := Control (r + 1) C f

structure Result (r : ℕ) (C : ℝ) (f : Seq) where
  value : Seq
  solves : transport value = f
  unique : ∀ u, transport u = f → u = value
  estimate : Control r C value

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
