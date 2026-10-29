import Core

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Matrix
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype V] [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq I]
variable {g : Gauge Y I}

def coeff (s : System Y V E I g) : Matrix (V × I) (V × I) ℝ≥0 := fun vi wj =>
  ∑ e, if s.src e = vi.1 ∧ s.dst e = wj.1 then s.L e vi.2 wj.2 else 0

def extendedCoeff (s : System Y V E I g) : Matrix (V × I) (V × I) ℝ≥0∞ :=
  fun vi wj => s.coeff vi wj

theorem gainAction_matrix (s : System Y V E I g) (u : V × I → ℝ≥0∞) :
    s.gainAction u = s.extendedCoeff *ᵥ u := by
  ext vi
  rw [Matrix.mulVec,dotProduct]
  simp only [extendedCoeff,coeff,ENNReal.coe_finset_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold gainAction
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : s.src e = vi.1
  · simp [hs,Fintype.sum_prod_type,apply_ite,ite_mul,Finset.sum_ite_irrel]
  · simp [hs]

theorem delta_matrix_iterate (s : System Y V E I g) (F G : s.Family) (n : ℕ) :
    s.delta (s.transform^[n] F) (s.transform^[n] G) ≤ s.extendedCoeff ^ n *ᵥ s.delta F G := by
  suffices he : s.gainAction^[n] (s.delta F G) = s.extendedCoeff ^ n *ᵥ s.delta F G by
    simpa [he] using s.delta_iterate F G n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,s.gainAction_matrix,Matrix.mulVec_mulVec,pow_succ']

end MathGauge.RecursiveClosure.System
