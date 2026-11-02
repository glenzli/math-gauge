import Core

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Matrix Filter Topology
namespace MathGauge.RecursiveClosure

/-- Gelfand's formula, used with the actual finite matrix rather than an assumed
contraction norm on the space of operator families. -/
theorem spectral_powers_decay {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (hA : spectralRadius ℂ A < 1) :
    Tendsto (fun n : ℕ => (↑‖A^n‖₊ : ℝ≥0∞)) atTop (𝓝 0) := by
  obtain ⟨q,hq,hq1⟩ := exists_between hA
  have hr : ∀ᶠ n : ℕ in atTop, (↑‖A^n‖₊ : ℝ≥0∞) ^ (1/(n:ℝ)) < q :=
    (tendsto_order.1 (spectrum.gelfand_formula A)).2 q hq
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_atTop.2 ⟨1,by omega⟩
  have hb : ∀ᶠ n : ℕ in atTop, (↑‖A^n‖₊ : ℝ≥0∞) ≤ q^n :=
    (hr.and hn).mono fun n hh => by
      have hp : (0:ℝ) < n := by exact_mod_cast hh.2
      have hc : (1/(n:ℝ))*(n:ℝ)=1 := by field_simp
      have hh' := ENNReal.rpow_lt_rpow hh.1 hp
      have he : ((↑‖A^n‖₊ : ℝ≥0∞)^(1/(n:ℝ)))^(n:ℝ) = (↑‖A^n‖₊ : ℝ≥0∞) := by
        rw [← ENNReal.rpow_mul,hc,ENNReal.rpow_one]
      rw [he,ENNReal.rpow_natCast] at hh'
      exact hh'.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1)
    (Eventually.of_forall fun _ => zero_le _) hb

def complexMatrix {J : Type} (A : Matrix J J ℝ≥0) : Matrix J J ℂ := fun i j => A i j

theorem complexMatrix_pow {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℝ≥0) (n : ℕ) : complexMatrix (A^n) = complexMatrix A ^ n := by
  induction n with
  | zero => ext i j; by_cases h : i=j <;> simp [complexMatrix,h]
  | succ n ih =>
    rw [pow_succ,pow_succ,← ih]
    ext i j
    simp [complexMatrix,Matrix.mul_apply]

theorem row_le_complex_norm {J : Type} [Fintype J] (A : Matrix J J ℝ≥0) (i : J) :
    ∑ j, A i j ≤ ‖complexMatrix A‖₊ := by
  rw [Matrix.linfty_opNNNorm_def]
  have h : ∑ j, A i j = ∑ j, ‖complexMatrix A i j‖₊ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [complexMatrix,Complex.nnnorm_real,Real.nnnorm_of_nonneg (A i j).2]
  rw [h]
  exact Finset.le_sup (f := fun i => ∑ j, ‖complexMatrix A i j‖₊) (Finset.mem_univ i)

theorem power_sum_identity {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℝ≥0) (N : ℕ) :
    A * (∑ k ∈ Finset.range N, A^k) + 1 = (∑ k ∈ Finset.range N, A^k) + A^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,mul_add,pow_succ']
    calc
      _ = (A * (∑ k ∈ Finset.range N, A^k) + 1) + A*A^N := by simp only [add_assoc,add_comm,add_left_comm]
      _ = _ := by rw [ih]

/-- Construct positive weights by a finite power sum. This is an alternative
proof of the weight existence used in the prose, with no assumed certificate. -/
theorem positive_weights_of_spectral {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (A : Matrix J J ℝ≥0) (hA : spectralRadius ℂ (complexMatrix A) < 1) :
    ∃ q : ℝ≥0, 0 < q ∧ q < 1 ∧ ∃ w : J → ℝ≥0,
      (∀ i, 0 < w i) ∧ ∀ i, ∑ j, A i j * w j ≤ q*w i := by
  have hd := spectral_powers_decay (complexMatrix A) hA
  have he : ∀ᶠ n : ℕ in atTop, (↑‖complexMatrix A ^ n‖₊ : ℝ≥0∞) < 1 :=
    (tendsto_order.1 hd).2 1 (by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  let K := N+1
  have hK : (↑‖complexMatrix A ^ K‖₊ : ℝ≥0∞) < 1 := hN K (by dsimp [K]; omega)
  have hK' : ‖complexMatrix A ^ K‖₊ < 1 := by exact_mod_cast hK
  let S := ∑ k ∈ Finset.range K, A^k
  let w : J → ℝ≥0 := fun i => ∑ j, S i j
  have hw : ∀ i, 1 ≤ w i := by
    intro i
    have hdiag : 1 ≤ S i i := by
      have hh := Finset.single_le_sum (f := fun k => (A^k) i i) (fun k _ => zero_le _)
        (show 0 ∈ Finset.range K by simp [K])
      simpa [S,Matrix.sum_apply] using hh
    exact hdiag.trans (Finset.single_le_sum (fun j _ => zero_le (S i j)) (Finset.mem_univ i))
  have hp : ∀ i, 0 < w i := fun i => lt_of_lt_of_le zero_lt_one (hw i)
  have ht : ∀ i, (A *ᵥ w) i < w i := by
    intro i
    have hid := congrArg (fun B : Matrix J J ℝ≥0 => ∑ j, B i j) (power_sum_identity A K)
    have hsum : ∑ j, (A*S) i j = (A *ᵥ w) i := by
      simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct,w,Finset.mul_sum]
      rw [Finset.sum_comm]
    have hh : (A *ᵥ w) i + 1 = w i + ∑ j, (A^K) i j := by
      change (∑ j, (A*S+1) i j) = ∑ j, (S+A^K) i j at hid
      simpa [Matrix.add_apply,Finset.sum_add_distrib,Matrix.one_apply,hsum,w] using hid
    have hb : ∑ j, (A^K) i j < 1 :=
      lt_of_le_of_lt (row_le_complex_norm (A^K) i) (by simpa [complexMatrix_pow] using hK')
    have hc : (A *ᵥ w) i + 1 < w i + 1 := by
      rw [hh]
      simpa only [add_comm] using add_lt_add_left hb (w i)
    exact lt_of_add_lt_add_right hc

  let r : ℝ≥0 := Finset.univ.sup fun i => (A *ᵥ w) i / w i
  have hr : r < 1 := by
    apply (Finset.sup_lt_iff (by norm_num)).2
    intro i hi
    exact (div_lt_one (hp i)).2 (ht i)
  let q : ℝ≥0 := (r+1)/2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; exact (div_lt_iff₀ (by norm_num)).2 (by nlinarith)
  have hrq : r ≤ q := by dsimp [q]; exact (le_div_iff₀ (by norm_num)).2 (by nlinarith)
  refine ⟨q,hq,hq1,w,hp,?_⟩
  intro i
  have hi : (A *ᵥ w) i / w i ≤ q :=
    (Finset.le_sup (f := fun i => (A *ᵥ w) i / w i) (Finset.mem_univ i)).trans hrq
  exact (div_le_iff₀ (hp i)).1 hi

end MathGauge.RecursiveClosure
