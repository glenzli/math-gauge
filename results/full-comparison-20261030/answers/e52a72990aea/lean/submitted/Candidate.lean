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
