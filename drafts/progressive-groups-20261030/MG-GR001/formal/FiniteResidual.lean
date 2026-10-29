import Weighted

noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter Topology
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype V] [Fintype E] [Fintype I]
variable [DecidableEq V] [DecidableEq I] {g : Gauge Y I}

theorem weighted_symm (s : System Y V E I g) (w : V × I → ℝ≥0) (F G : s.Family) :
    s.weighted w F G=s.weighted w G F := by
  simp only [weighted,delta,g.symm]

/-- Cauchy in the actual extended weighted gauge. No point-valued limit or completeness is assumed. -/
def WeightedCauchy (s : System Y V E I g) (w : V × I → ℝ≥0) (F : ℕ → s.Family) : Prop :=
  ∀ ε : ℝ≥0∞, 0<ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, s.weighted w (F m) (F n)<ε

theorem finite_residual_cauchy (s : System Y V E I g) (q : ℝ≥0) (hq : q<1)
    (w : V × I → ℝ≥0)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤ q*s.weighted w F G)
    (H : s.Family) (hfinite : s.weighted w (s.transform H) H ≠ ⊤) :
    s.WeightedCauchy w (fun n => s.transform^[n] H) := by
  have hq' : (q : ℝ≥0∞)<1 := by exact_mod_cast hq
  let R := s.weighted w (s.transform H) H
  have hden : (1-(q : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hq').ne'
  have hcst : R/(1-(q : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top hfinite (ENNReal.inv_ne_top.mpr hden)
  have ht : Tendsto (fun n => R*(q : ℝ≥0∞)^n/(1-(q : ℝ≥0∞))) atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul (a := R/(1-(q : ℝ≥0∞)))
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq') (Or.inr hcst)
    simpa [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  intro ε hε
  obtain ⟨N,hN⟩ := (ht.eventually_lt_const hε).exists_forall_of_atTop
  refine ⟨N,fun m hm n hn => ?_⟩
  rcases le_total n m with hnm|hmn
  · have hh := s.residual_geometric_bound q w hc H n (m-n)
    rw [Nat.add_sub_of_le hnm] at hh
    exact hh.trans_lt (hN n hn)
  · rw [s.weighted_symm]
    have hh := s.residual_geometric_bound q w hc H m (n-m)
    rw [Nat.add_sub_of_le hmn] at hh
    exact hh.trans_lt (hN m hm)

end MathGauge.RecursiveClosure.System
