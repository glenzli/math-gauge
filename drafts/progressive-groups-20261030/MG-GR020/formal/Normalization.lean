import MatrixAdic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

noncomputable section
namespace MathGauge.GR020
variable {R : Type*} [CommRing R] {d r : ℕ}

theorem gram_commutes {V E F : Mat R d} (hE : E.transpose=E)
    (hF : F.transpose=F) (hi : V*E=F*V) : Commute (V.transpose*V) E := by
  have ht := congrArg Matrix.transpose hi
  simp only [Matrix.transpose_mul,hE,hF] at ht
  change V.transpose*V*E=E*(V.transpose*V)
  calc
    _ = V.transpose*(F*V) := by rw [mul_assoc,hi]
    _ = (E*V.transpose)*V := by rw [← mul_assoc,← ht]
    _ = _ := mul_assoc _ _ _

theorem near_unit_inv (I : Ideal R) (u : (Mat R d)ˣ) (h : Near I (u : Mat R d) 1) :
    Near I (↑u⁻¹ : Mat R d) 1 := by
  rw [near_iff_reduce] at *
  have hh := congrArg (reduce I) u.mul_inv
  simp only [map_mul,map_one,h,one_mul] at hh
  simpa only [map_one] using hh

/-- Algebraic normalization by an actually constructed symmetric square root. -/
theorem normalize_root (V : (Mat R d)ˣ) (E F : Fin r → Mat R d)
    (hi : ∀ i, (V : Mat R d)*E i=F i*V)
    (D : Mat R d) (hD : D*D=(V : Mat R d).transpose*V)
    (hs : D.transpose=D) (hc : ∀ i, Commute D (E i)) :
    ∃ U : (Mat R d)ˣ, (U : Mat R d).transpose*U=1 ∧
      (∀ i, (U : Mat R d)*E i=F i*U) ∧ (↑U⁻¹ : Mat R d)*V=D ∧
      (∀ I : Ideal R, Near I (V : Mat R d) 1 → Near I D 1 → Near I (U : Mat R d) 1) := by
  have hunit : IsUnit D := by
    apply isUnit_mul_self_iff.mp
    rw [hD]
    exact ((Matrix.isUnit_transpose _).mpr V.isUnit).mul V.isUnit
  let D' : (Mat R d)ˣ := hunit.unit
  have hval : (D' : Mat R d)=D := hunit.unit_spec
  let U := V*D'⁻¹
  have hdunit : (D' : Mat R d).transpose*(D' : Mat R d)=(V : Mat R d).transpose*V := by
    rw [hval,hs,hD]
  refine ⟨U,?_,?_,?_,?_⟩
  · change ((V : Mat R d)*(↑D'⁻¹ : Mat R d)).transpose*
      ((V : Mat R d)*(↑D'⁻¹ : Mat R d))=1
    rw [Matrix.transpose_mul]
    calc
      _ = (↑D'⁻¹ : Mat R d).transpose*((V : Mat R d).transpose*V)*(↑D'⁻¹ : Mat R d) := by noncomm_ring
      _ = (↑D'⁻¹ : Mat R d).transpose*((D' : Mat R d).transpose*D')*(↑D'⁻¹ : Mat R d) := by rw [hdunit]
      _ = ((D' : Mat R d)*(↑D'⁻¹ : Mat R d)).transpose*((D' : Mat R d)*(↑D'⁻¹ : Mat R d)) := by rw [Matrix.transpose_mul]; noncomm_ring
      _ = 1 := by simp
  · intro i
    have hdcomm : Commute (D' : Mat R d) (E i) := hval ▸ hc i
    change (V : Mat R d)*(↑D'⁻¹ : Mat R d)*E i=F i*((V : Mat R d)*(↑D'⁻¹ : Mat R d))
    rw [mul_assoc,hdcomm.units_inv_left.eq,← mul_assoc,hi,mul_assoc]
  · change (↑(V*D'⁻¹)⁻¹ : Mat R d)*V=D
    simp [hval]
  · intro I hV hDnear
    change Near I ((V : Mat R d)*(↑D'⁻¹ : Mat R d)) 1
    have hh := hV.mul (near_unit_inv I D' (hval ▸ hDnear))
    simpa only [one_mul] using hh

theorem normalize_adic (I : Ideal R) [IsAdicComplete I R]
    (V : (Mat R d)ˣ) (E F : Fin r → Mat R d)
    (hi : ∀ i, (V : Mat R d)*E i=F i*V)
    (T : Mat R d) (hT : Near I T 0) (hs : T.transpose=T)
    (hc : ∀ i, Commute T (E i)) (hG : (V : Mat R d).transpose*V=1-4*T)
    (hV : Near I (V : Mat R d) 1) :
    ∃ U : (Mat R d)ˣ, Near I (U : Mat R d) 1 ∧
      (U : Mat R d).transpose*U=1 ∧ ∀ i, (U : Mat R d)*E i=F i*U := by
  obtain ⟨D,hD,hsD,hnD,hcD⟩ := adic_square_root I T hT hs
  obtain ⟨U,hu,hiU,_,hn⟩ := normalize_root V E F hi D (hD.trans hG.symm) hsD
    (fun i => hcD (E i) (hc i))
  exact ⟨U,hn I hV hnD,hu,hiU⟩

end MathGauge.GR020
