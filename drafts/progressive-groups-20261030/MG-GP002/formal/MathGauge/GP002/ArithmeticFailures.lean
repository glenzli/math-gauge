import MathGauge.PublicProof.Torus.FullTarget
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.NumberTheory.Transcendental.Liouville.Residual

noncomputable section
namespace MathGauge.GP002

open MathGauge.PublicProof.Torus
open MathGauge.PublicProof.Torus.Borrowed.TorusInverse
open MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData
open Filter
open scoped Topology ContDiff

/-- The requested series starts at n=1, unlike Mathlib's series starting at n=0. -/
def factorialDirection : ℝ := ∑' n : ℕ, 1 / (10 : ℝ) ^ (n + 1).factorial

theorem factorialDirection_eq : factorialDirection = liouvilleNumber 10 - 1/10 := by
  have h := (LiouvilleNumber.summable (by norm_num : (1 : ℝ) < 10)).sum_add_tsum_nat_add 1
  simpa [factorialDirection, liouvilleNumber, Finset.sum_range_one] using
    (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h))

theorem factorialDirection_liouville : Liouville factorialDirection := by
  rw [factorialDirection_eq]
  apply forall_liouvilleWith_iff.mp
  intro p
  convert ((liouville_liouvilleNumber (by norm_num : 2 ≤ (10 : ℕ))).liouvilleWith p).sub_rat (1/10)
    using 1 <;> norm_num

theorem factorialDirection_irrational : Irrational factorialDirection :=
  factorialDirection_liouville.irrational

/-- A Liouville direction has no polynomial lower bound on the actual integer lattice. -/
theorem liouville_no_polynomial_bound {α : ℝ} (hα : Liouville α) :
    ¬ PolynomialDivisorBound α := by
  rintro ⟨n,c,hc,hbound⟩
  let C : ℝ := 3 + |α|
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (C^n / c)
  obtain ⟨b,hb,a,hne,happrox⟩ :=
    ((eventually_gt_atTop (max N 1)).and_frequently (hα.frequently_exists_num (n+2))).exists
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (lt_of_le_of_lt (le_max_right N 1) hb)
  have hb0 : (0 : ℝ) < b := by linarith
  have hNb : (N : ℝ) < b := by exact_mod_cast (lt_of_le_of_lt (le_max_left N 1) hb)
  have herr : |α - a / (b : ℝ)| < 1 := by
    apply happrox.trans_le
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ hb1.le : 1 ≤ (b : ℝ)^(n+2))
  have hap : |(a : ℝ)| ≤ (|α|+1) * b := by
    have ht : |(a : ℝ)/(b : ℝ)| < |α| + 1 := by
      calc
        |(a : ℝ)/(b : ℝ)| = |α - (α-a/(b : ℝ))| := by ring_nf
        _ ≤ |α| + |α-a/(b : ℝ)| := abs_sub _ _
        _ < |α|+1 := by linarith
    rw [abs_div,abs_of_pos hb0] at ht
    exact le_of_lt ((div_lt_iff₀ hb0).mp ht)
  let k : PairFrequency := ((b : ℤ),-a)
  have hk : k ≠ 0 := by
    intro he
    have hz : (b : ℤ) = 0 := congrArg Prod.fst he
    have : b = 0 := Int.natCast_eq_zero.mp hz
    subst b; norm_num at hb1
  have hw : Borrowed.TorusInverse.weight k ≤ C*b := by
    simp only [Borrowed.TorusInverse.weight,k,Int.cast_natCast,Int.cast_neg,abs_neg,
      abs_of_pos hb0]
    dsimp [C]
    nlinarith [abs_nonneg α]
  have hd : |pairDivisor α k| < (b : ℝ) / (b : ℝ)^(n+2) := by
    have he : pairDivisor α k = (b : ℝ) * (α-a/(b : ℝ)) := by
      simp only [pairDivisor,k,Int.cast_natCast,Int.cast_neg]
      field_simp
      ring
    rw [he,abs_mul,abs_of_pos hb0]
    simpa only [mul_one_div] using mul_lt_mul_of_pos_left happrox hb0
  have hsmall : Borrowed.TorusInverse.weight k ^ n * |pairDivisor α k| < C^n / (b : ℝ) := by
    calc
      _ ≤ (C*b)^n * |pairDivisor α k| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Borrowed.TorusInverse.weight_pos k).le hw n)
          (abs_nonneg _)
      _ < (C*b)^n * ((b : ℝ)/(b : ℝ)^(n+2)) :=
        mul_lt_mul_of_pos_left hd (pow_pos (mul_pos hC hb0) n)
      _ = C^n / (b : ℝ) := by rw [mul_pow,pow_add]; field_simp
  have hcb : C^n/(b : ℝ) < c := by
    apply (div_lt_iff₀ hb0).mpr
    have ht := (div_lt_iff₀ hc).mp (hN.trans hNb)
    nlinarith
  exact (not_lt_of_ge (hbound k hk)) (hsmall.trans hcb)

/-- One fixed actual smooth forcing, not a frequency depending on a proposed estimate. -/
theorem factorialDirection_unsolvable :
    ∃ F : C(Torus2,ℂ), Smooth F ∧ MeanZero F ∧
      ¬ ∃ u : C(Torus2,ℂ), Smooth u ∧ MeanZero u ∧
        ∀ y, transport factorialDirection u y = F y := by
  obtain ⟨f,hf,hp,hf0,hno⟩ := exists_smooth_unsolvable factorialDirection_irrational
    (liouville_no_polynomial_bound factorialDirection_liouville)
  refine ⟨ofCover f hf hp,ofCover_smooth f hf hp,?_,?_⟩
  · rw [native_meanZero_iff_cover,coverOf_ofCover]; exact hf0
  · rintro ⟨u,hu,hum,hsol⟩
    apply hno
    refine ⟨coverOf u,(smooth_iff_coverOf u).mp hu,coverOf_periodic u,
      (native_meanZero_iff_cover u).mp hum,?_⟩
    funext x
    rw [← transport_native_cover u hu factorialDirection x,hsol,
      ← coverOf_apply,coverOf_ofCover]

end MathGauge.GP002
