import Normalization

noncomputable section
namespace MathGauge.GR020
open scoped MatrixOrder
variable {d r : ℕ}

/-- S1: polar normalization of the supplied real intertwiner, with its
positive definite residual and all intertwining equations. -/
theorem real_normalization (V : (Mat ℝ d)ˣ) (E F : Fin r → Mat ℝ d)
    (hE : ∀ i, (E i).transpose=E i) (hF : ∀ i, (F i).transpose=F i)
    (hi : ∀ i, (V : Mat ℝ d)*E i=F i*V) :
    ∃ U : (Mat ℝ d)ˣ, (U : Mat ℝ d).transpose*U=1 ∧
      (∀ i, (U : Mat ℝ d)*E i=F i*U) ∧
      ((↑U⁻¹ : Mat ℝ d)*V).PosDef := by
  let G : Mat ℝ d := (V : Mat ℝ d).transpose*V
  have hG : G.PosDef := by
    simpa [G,Matrix.conjTranspose] using Matrix.PosDef.conjTranspose_mul_self
      (V : Mat ℝ d) (Matrix.mulVec_injective_iff_isUnit.mpr V.isUnit)
  let D := CFC.sqrt G
  have hDpos : D.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hG.isStrictlyPositive.sqrt
  have hs : D.transpose=D := by
    simpa [Matrix.IsHermitian,Matrix.conjTranspose] using hDpos.isHermitian
  have hc : ∀ i, Commute D (E i) := by
    intro i
    exact (gram_commutes (hE i) (hF i) (hi i)).cfcₙ_nnreal NNReal.sqrt
  obtain ⟨U,hu,hiU,hd,_⟩ := normalize_root V E F hi D
    (CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg) hs hc
  exact ⟨U,hu,hiU,hd ▸ hDpos⟩

variable {R : Type*} [CommRing R]

/-- S2, in fact over any complete commutative adic ring where 2 is a unit.
Symmetry supplies the centralizing property of the actual Gram matrix. -/
theorem two_invertible_normalization (I : Ideal R) [IsAdicComplete I R]
    (htwo : IsUnit (2 : R)) (V : (Mat R d)ˣ) (E F : Fin r → Mat R d)
    (hE : ∀ i, (E i).transpose=E i) (hF : ∀ i, (F i).transpose=F i)
    (hi : ∀ i, (V : Mat R d)*E i=F i*V) (hV : Near I (V : Mat R d) 1) :
    ∃ U : (Mat R d)ˣ, Near I (U : Mat R d) 1 ∧
      (U : Mat R d).transpose*U=1 ∧ ∀ i, (U : Mat R d)*E i=F i*U := by
  let a : R := (↑htwo.unit⁻¹ : R)*(↑htwo.unit⁻¹ : R)
  have ha : (4 : R)*a=1 := by
    have hb : (2 : R)*(↑htwo.unit⁻¹ : R)=1 := by simp
    dsimp [a]
    linear_combination (2*(↑htwo.unit⁻¹ : R)+1)*hb
  let S : Mat R d := algebraMap R (Mat R d) a
  have hS : 4*S=1 := by
    simpa only [map_mul,map_ofNat,map_one] using congrArg (algebraMap R (Mat R d)) ha
  let G : Mat R d := (V : Mat R d).transpose*V
  let T : Mat R d := S*(1-G)
  have hGnear : Near I G 1 := by
    simpa only [Matrix.transpose_one,one_mul] using hV.transpose.mul hV
  have hT : Near I T 0 := by
    have hh := (Near.refl I S).mul ((Near.refl I (1 : Mat R d)).sub hGnear)
    simpa only [sub_self,mul_zero] using hh
  have hGs : G.transpose=G := by simp [G]
  have hSs : S.transpose=S := by simp [S,Algebra.algebraMap_eq_smul_one]
  have hcS (A : Mat R d) : Commute S A := Algebra.commute_algebraMap_left a A
  have hTs : T.transpose=T := by
    dsimp [T]
    rw [Matrix.transpose_mul,Matrix.transpose_sub,Matrix.transpose_one,hGs,hSs]
    exact (hcS (1-G)).eq.symm
  have hTc : ∀ i, Commute T (E i) := by
    intro i
    exact (hcS (E i)).mul_left ((Commute.one_left _).sub_left
      (gram_commutes (hE i) (hF i) (hi i)))
  have hGram : G=1-4*T := by
    dsimp only [T]
    rw [← mul_assoc,hS,one_mul]
    noncomm_ring
  exact normalize_adic I V E F hi T hT hTs hTc hGram hV

end MathGauge.GR020
