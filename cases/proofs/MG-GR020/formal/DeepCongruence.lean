import RealAndOdd
import ParameterGroup

noncomputable section
namespace MathGauge.GR020
open MathGauge.PadicOrthogonal
local notation "Z₂" => ℤ_[2]
variable {d r : ℕ}

theorem numeral_mul_entry (n : ℕ) (A : Mat Z₂ d) (i j : Fin d) :
    ((n : Mat Z₂ d)*A) i j=(n : Z₂)*A i j := by
  simp only [← nsmul_eq_mul]
  rfl

theorem eight_matrix_cancel {A B : Mat Z₂ d} (h : (8 : Mat Z₂ d)*A=8*B) : A=B := by
  ext i j
  have hh := congrFun (congrFun h i) j
  change (((8 : ℕ) : Mat Z₂ d)*A) i j=(((8 : ℕ) : Mat Z₂ d)*B) i j at hh
  rw [numeral_mul_entry,numeral_mul_entry] at hh
  exact mul_left_cancel₀ (by norm_num : (8 : Z₂) ≠ 0) hh

/-- S5: actual entrywise divisibility by 8 constructs the correction T.
Its Catalan iteration converges 2-adically; this is an integral alternative
to the binomial series, with no hidden inverse of 2. -/
theorem eight_congruence_normalization (V : (Mat Z₂ d)ˣ) (E F : Fin r → Mat Z₂ d)
    (hE : ∀ i, (E i).transpose=E i) (hF : ∀ i, (F i).transpose=F i)
    (hi : ∀ i, (V : Mat Z₂ d)*E i=F i*V)
    (h8 : Near (Ideal.span {(8 : Z₂)}) (V : Mat Z₂ d) 1) :
    ∃ U : (Mat Z₂ d)ˣ, Near (IsLocalRing.maximalIdeal Z₂) (U : Mat Z₂ d) 1 ∧
      (U : Mat Z₂ d).transpose*U=1 ∧ ∀ i, (U : Mat Z₂ d)*E i=F i*U := by
  have hw : ∀ i j, ∃ w : Z₂, (V : Mat Z₂ d) i j-(1 : Mat Z₂ d) i j=8*w := by
    intro i j
    obtain ⟨w,hw⟩ := Ideal.mem_span_singleton.mp (h8 i j)
    exact ⟨w,hw⟩
  choose w hw using hw
  let W : Mat Z₂ d := w
  have hW := hw
  have hVform : (V : Mat Z₂ d)=1+8*W := by
    ext i j
    change (V : Mat Z₂ d) i j=(1 : Mat Z₂ d) i j+(((8 : ℕ) : Mat Z₂ d)*W) i j
    rw [numeral_mul_entry]
    linear_combination hW i j
  let B : Mat Z₂ d := W.transpose+W+8*(W.transpose*W)
  have hGram : (V : Mat Z₂ d).transpose*V=1+8*B := by
    rw [hVform]
    simp only [Matrix.transpose_add,Matrix.transpose_one,Matrix.transpose_mul,Matrix.transpose_ofNat]
    dsimp [B]
    noncomm_ring
  have hBsym : B.transpose=B := by
    dsimp [B]
    simp only [Matrix.transpose_add,Matrix.transpose_transpose,Matrix.transpose_mul,Matrix.transpose_ofNat]
    noncomm_ring
  have hBcomm : ∀ i, Commute B (E i) := by
    intro i
    have hc := (gram_commutes (hE i) (hF i) (hi i)).eq
    rw [hGram] at hc
    apply eight_matrix_cancel
    calc
      (8 : Mat Z₂ d)*(B*E i) = (1+8*B)*E i-E i := by noncomm_ring
      _ = E i*(1+8*B)-E i := by rw [hc]
      _ = 8*(E i*B) := by noncomm_ring
  let T : Mat Z₂ d := -(2*B)
  have hT : Near (IsLocalRing.maximalIdeal Z₂) T 0 := by
    intro i j
    rw [PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton]
    refine ⟨-B i j,?_⟩
    change -(2*B) i j-0=2*(-B i j)
    change -((((2 : ℕ) : Mat Z₂ d)*B) i j)-0=2*(-B i j)
    rw [numeral_mul_entry]
    ring
  have hTs : T.transpose=T := by
    dsimp [T]
    simp only [Matrix.transpose_neg,Matrix.transpose_mul,Matrix.transpose_ofNat,hBsym]
    noncomm_ring
  have hTc : ∀ i, Commute T (E i) := by
    intro i
    exact ((Commute.ofNat_left 2 (E i)).mul_left (hBcomm i)).neg_left
  have hGT : (V : Mat Z₂ d).transpose*V=1-4*T := by
    rw [hGram]
    dsimp [T]
    noncomm_ring
  have hVnear : Near (IsLocalRing.maximalIdeal Z₂) (V : Mat Z₂ d) 1 := by
    intro i j
    rw [PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton,hW i j]
    exact ⟨4*W i j,by ring⟩
  exact normalize_adic (IsLocalRing.maximalIdeal Z₂) V E F hi T hT hTs hTc hGT hVnear

end MathGauge.GR020
