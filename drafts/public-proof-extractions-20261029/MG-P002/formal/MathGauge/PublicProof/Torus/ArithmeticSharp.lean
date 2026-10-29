import MathGauge.PublicProof.Torus.Arithmetic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace MathGauge.PublicProof.Torus
open Filter
open scoped Topology

lemma weight_le_l1 (k : Frequency) :
    weight k ≤ 1 + |(k 0 : ℝ)| + |(k 1 : ℝ)| := by
  have hw := weight_sq k
  have hp := (weight_pos k).le
  have h0 := abs_nonneg (k 0 : ℝ)
  have h1 := abs_nonneg (k 1 : ℝ)
  apply (sq_le_sq₀ hp (by positivity)).mp
  nlinarith [sq_abs (k 0 : ℝ), sq_abs (k 1 : ℝ), mul_nonneg h0 h1]

/-- Dirichlet provides genuine nonzero lattice frequencies with a bounded size.
The bound is uniform in `n`; no selected frequency is hidden in a hypothesis. -/
theorem dirichlet_frequency (α : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ k : Frequency, k ≠ 0 ∧
      weight k ≤ (2 + |α|) * (n + 1) ∧ |divisor α k| ≤ 1 / (n + 1) := by
  obtain ⟨p, q, hq, hqn, happrox⟩ := Real.exists_int_int_abs_mul_sub_le α hn
  let k : Frequency := ![q, -p]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqnR : (q : ℝ) ≤ n := by exact_mod_cast hqn
  have hnR : (0 : ℝ) ≤ n := by positivity
  have herr : |(q : ℝ) * α - p| ≤ 1 := happrox.trans ((div_le_one (by positivity)).mpr (by linarith))
  have hpb : |(p : ℝ)| ≤ (n : ℝ) * |α| + 1 := by
    calc
      |(p : ℝ)| = |((q : ℝ) * α) - ((q : ℝ) * α - p)| := by ring_nf
      _ ≤ |(q : ℝ) * α| + |(q : ℝ) * α - p| := abs_sub _ _
      _ ≤ (n : ℝ) * |α| + 1 := by
        rw [abs_mul, abs_of_pos hqR]
        exact add_le_add (mul_le_mul_of_nonneg_right hqnR (abs_nonneg _)) herr
  refine ⟨k, ?_, ?_, ?_⟩
  · intro h
    have hz := congrFun h 0
    have : q = 0 := by simpa [k] using hz
    exact (ne_of_gt hq) this
  · calc
      weight k ≤ 1 + |(k 0 : ℝ)| + |(k 1 : ℝ)| := weight_le_l1 k
      _ = 1 + (q : ℝ) + |(p : ℝ)| := by simp [k, abs_of_pos hqR]
      _ ≤ (2 + |α|) * (n + 1) := by nlinarith [abs_nonneg α]
  · simpa [k, divisor, mul_comm, sub_eq_add_neg] using happrox

/-- No nonnegative loss below one can have the required uniform arithmetic bound. -/
theorem one_le_of_divisor_bound {α s : ℝ} (hs : 0 ≤ s) (hb : HasDivisorBound α s) : 1 ≤ s := by
  by_contra h
  have hlt : s < 1 := lt_of_not_ge h
  obtain ⟨c, hc, hbound⟩ := hb
  have hlim : Tendsto (fun n : ℕ => (2 + |α|) ^ s * ((n : ℝ) + 1) ^ (s - 1))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hr := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - s)).comp ht
    have hm := hr.const_mul ((2 + |α|) ^ s)
    simpa only [neg_sub, mul_zero] using hm
  have hev : ∀ᶠ n : ℕ in atTop, c ≤ (2 + |α|) ^ s * ((n : ℝ) + 1) ^ (s - 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    obtain ⟨k, hk, hw, hd⟩ := dirichlet_frequency α (by omega : 0 < n)
    calc
      c ≤ weight k ^ s * |divisor α k| := hbound k hk
      _ ≤ ((2 + |α|) * (n + 1)) ^ s * (1 / (n + 1)) :=
        mul_le_mul (Real.rpow_le_rpow (weight_pos k).le hw hs) hd
          (abs_nonneg _) (by positivity)
      _ = (2 + |α|) ^ s * ((n : ℝ) + 1) ^ (s - 1) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_sub (by positivity), Real.rpow_one]
        ring
  exact (not_le_of_gt hc) (ge_of_tendsto hlim hev)

/-- The arithmetic loss set for the specified quadratic direction includes its endpoint. -/
theorem quadratic_divisor_bound_iff {s : ℝ} (hs : 0 ≤ s) :
    HasDivisorBound quadraticDirection s ↔ 1 ≤ s :=
  ⟨one_le_of_divisor_bound hs, fun h => divisor_bound_mono quadratic_divisor_bound_one h⟩

end MathGauge.PublicProof.Torus
