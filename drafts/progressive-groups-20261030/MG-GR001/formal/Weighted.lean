import Bounds
import Spectral
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Matrix
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype V] [Fintype E] [Fintype I]
variable [DecidableEq V] [DecidableEq I] {g : Gauge Y I}

def weighted (s : System Y V E I g) (w : V × I → ℝ≥0) (F G : s.Family) : ℝ≥0∞ :=
  ⨆ a, s.delta F G a / (w a : ℝ≥0∞)

theorem delta_le_weighted (s : System Y V E I g) (w : V × I → ℝ≥0)
    (hw : ∀ a, 0 < w a) (F G : s.Family) (a : V × I) :
    s.delta F G a ≤ s.weighted w F G * (w a : ℝ≥0∞) := by
  apply (ENNReal.div_le_iff (by exact_mod_cast (hw a).ne') ENNReal.coe_ne_top).1
  exact le_iSup (fun a => s.delta F G a / (w a : ℝ≥0∞)) a

theorem weighted_self (s : System Y V E I g) (w : V × I → ℝ≥0) (F : s.Family) :
    s.weighted w F F = 0 := by simp [weighted,delta,g.self]

theorem weighted_triangle (s : System Y V E I g) (w : V × I → ℝ≥0) (F G H : s.Family) :
    s.weighted w F H ≤ s.weighted w F G + s.weighted w G H := by
  apply iSup_le
  intro a
  have hd : s.delta F H a ≤ s.delta F G a + s.delta G H a := by
    apply iSup_le
    intro x
    exact (g.triangle a.2 _ _ _).trans (add_le_add
      (s.point_le_delta F G a.1 a.2 x) (s.point_le_delta G H a.1 a.2 x))
  calc
    s.delta F H a / (w a : ℝ≥0∞) ≤ (s.delta F G a + s.delta G H a) / (w a : ℝ≥0∞) :=
      by simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_right hd (w a : ℝ≥0∞)⁻¹
    _ = s.delta F G a / (w a : ℝ≥0∞) + s.delta G H a / (w a : ℝ≥0∞) := by simp [div_eq_mul_inv,add_mul]
    _ ≤ s.weighted w F G + s.weighted w G H := add_le_add (le_iSup (fun b => s.delta F G b / (w b : ℝ≥0∞)) a) (le_iSup (fun b => s.delta G H b / (w b : ℝ≥0∞)) a)

theorem weighted_contraction (s : System Y V E I g) (q : ℝ≥0) (w : V × I → ℝ≥0)
    (hw : ∀ a, 0 < w a) (hb : ∀ a, ∑ b, s.coeff a b * w b ≤ q*w a)
    (F G : s.Family) : s.weighted w (s.transform F) (s.transform G) ≤ q * s.weighted w F G := by
  apply iSup_le
  intro a
  apply (ENNReal.div_le_iff (by exact_mod_cast (hw a).ne') ENNReal.coe_ne_top).2
  have hg := s.delta_transform F G a
  rw [s.gainAction_matrix] at hg
  calc
    s.delta (s.transform F) (s.transform G) a ≤ (s.extendedCoeff *ᵥ s.delta F G) a := hg
    _ ≤ ∑ b, (s.coeff a b : ℝ≥0∞) * (s.weighted w F G * (w b : ℝ≥0∞)) :=
      Finset.sum_le_sum fun b _ => mul_le_mul_left' (s.delta_le_weighted w hw F G b) _
    _ = s.weighted w F G * (↑(∑ b, s.coeff a b * w b) : ℝ≥0∞) := by
      simp [ENNReal.coe_finset_sum,Finset.mul_sum,mul_assoc,mul_left_comm]
    _ ≤ s.weighted w F G * (↑(q*w a) : ℝ≥0∞) :=
      mul_le_mul_left' (by exact_mod_cast hb a) _
    _ = (q * s.weighted w F G) * (w a : ℝ≥0∞) := by simp [mul_assoc,mul_left_comm]

theorem spectral_weighted_contraction [Nonempty V] [Nonempty I]
    (s : System Y V E I g) (hs : spectralRadius ℂ (complexMatrix s.coeff) < 1) :
    ∃ q : ℝ≥0, 0 < q ∧ q < 1 ∧ ∃ w : V × I → ℝ≥0,
      (∀ a, 0 < w a) ∧ ∀ F G : s.Family,
        s.weighted w (s.transform F) (s.transform G) ≤ q * s.weighted w F G := by
  obtain ⟨q,hq,hq1,w,hw,hb⟩ := positive_weights_of_spectral s.coeff hs
  exact ⟨q,hq,hq1,w,hw,fun F G => s.weighted_contraction q w hw hb F G⟩

theorem weighted_iterate (s : System Y V E I g) (q : ℝ≥0) (w : V × I → ℝ≥0)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤ q*s.weighted w F G)
    (F G : s.Family) (n : ℕ) :
    s.weighted w (s.transform^[n] F) (s.transform^[n] G) ≤ (q:ℝ≥0∞)^n * s.weighted w F G := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',pow_succ']
    exact (hc _ _).trans (by simpa [mul_assoc] using mul_le_mul_left' ih (q:ℝ≥0∞))

theorem residual_step (s : System Y V E I g) (q : ℝ≥0) (w : V × I → ℝ≥0)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤ q*s.weighted w F G)
    (H : s.Family) (n : ℕ) :
    s.weighted w (s.transform^[n+1] H) (s.transform^[n] H) ≤
      (q:ℝ≥0∞)^n * s.weighted w (s.transform H) H := by
  simpa only [Function.iterate_succ_apply] using s.weighted_iterate q w hc (s.transform H) H n

theorem residual_finite_sum (s : System Y V E I g) (q : ℝ≥0) (w : V × I → ℝ≥0)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤ q*s.weighted w F G)
    (H : s.Family) (n p : ℕ) :
    s.weighted w (s.transform^[n+p] H) (s.transform^[n] H) ≤
      ∑ k ∈ Finset.range p, (q:ℝ≥0∞)^(n+k) * s.weighted w (s.transform H) H := by
  induction p with
  | zero => simp [s.weighted_self]
  | succ p ih =>
    have ht := s.weighted_triangle w (s.transform^[n+p+1] H) (s.transform^[n+p] H) (s.transform^[n] H)
    have he := (add_le_add (s.residual_step q w hc H (n+p)) ih)
    simpa [Finset.sum_range_succ,Nat.add_assoc,add_comm] using ht.trans he

theorem residual_geometric_bound (s : System Y V E I g) (q : ℝ≥0) (w : V × I → ℝ≥0)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤ q*s.weighted w F G)
    (H : s.Family) (n p : ℕ) :
    s.weighted w (s.transform^[n+p] H) (s.transform^[n] H) ≤
      s.weighted w (s.transform H) H * (q:ℝ≥0∞)^n / (1-(q:ℝ≥0∞)) := by
  apply (s.residual_finite_sum q w hc H n p).trans
  calc
    _ ≤ ∑' k : ℕ, (q:ℝ≥0∞)^(n+k) * s.weighted w (s.transform H) H := ENNReal.sum_le_tsum _
    _ = _ := by simp [pow_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_geometric,
      div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

theorem fixed_weighted_zero (s : System Y V E I g) (q : ℝ≥0) (hq : q < 1)
    (w : V × I → ℝ≥0)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤ q*s.weighted w F G)
    (F G : s.Family) (hF : s.transform F = F) (hG : s.transform G = G)
    (hfinite : s.weighted w F G ≠ ⊤) : s.weighted w F G = 0 := by
  have h := hc F G
  rw [hF,hG] at h
  generalize hd : s.weighted w F G = d at h hfinite ⊢
  lift d to ℝ≥0 using hfinite
  have hr : (d:ℝ) ≤ (q:ℝ)*(d:ℝ) := by exact_mod_cast h
  have hq' : (q:ℝ) < 1 := by exact_mod_cast hq
  have hz : (d:ℝ)=0 := by nlinarith [d.2]
  have hd' : d=0 := NNReal.coe_injective hz
  simp [hd']

theorem fixed_pointwise_zero (s : System Y V E I g) (q : ℝ≥0) (hq : q < 1)
    (w : V × I → ℝ≥0) (hw : ∀ a, 0 < w a)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤ q*s.weighted w F G)
    (F G : s.Family) (hF : s.transform F = F) (hG : s.transform G = G)
    (hfinite : s.weighted w F G ≠ ⊤) : ∀ v x i, g.d i (F v x) (G v x) = 0 := by
  have hz := s.fixed_weighted_zero q hq w hc F G hF hG hfinite
  intro v x i
  apply le_antisymm _ bot_le
  have hh := (s.point_le_delta F G v i x).trans (s.delta_le_weighted w hw F G (v,i))
  simpa [hz] using hh

end MathGauge.RecursiveClosure.System
