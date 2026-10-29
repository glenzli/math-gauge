import Normalization

noncomputable section
namespace MathGauge.GR020
variable {R : Type*} [CommRing R] {d r : ℕ}

def Orthogonal (U : (Mat R d)ˣ) : Prop := (U : Mat R d).transpose*U=1

theorem orthogonal_mul {U W : (Mat R d)ˣ} (hU : Orthogonal U) (hW : Orthogonal W) :
    Orthogonal (U*W) := by
  change ((U : Mat R d)*(W : Mat R d)).transpose*((U : Mat R d)*(W : Mat R d))=1
  rw [Matrix.transpose_mul]
  calc
    _ = (W : Mat R d).transpose*((U : Mat R d).transpose*U)*W := by noncomm_ring
    _ = 1 := by rw [hU,mul_one]; exact hW

theorem orthogonal_inv {U : (Mat R d)ˣ} (hU : Orthogonal U) : Orthogonal U⁻¹ := by
  have he : (U : Mat R d).transpose=(↑U⁻¹ : Mat R d) := by
    have hh := congrArg (fun A : Mat R d => A*(↑U⁻¹ : Mat R d)) hU
    simpa [mul_assoc] using hh
  change (↑U⁻¹ : Mat R d).transpose*(↑U⁻¹ : Mat R d)=1
  rw [← he,Matrix.transpose_transpose]
  rw [he]
  exact U.mul_inv

/-- All three restrictions form one actual subgroup of the matrix units. -/
def freedomGroup (I : Ideal R) (E : Fin r → Mat R d) : Subgroup (Mat R d)ˣ where
  carrier := {H | Orthogonal H ∧ Near I (H : Mat R d) 1 ∧ ∀ i, Commute (H : Mat R d) (E i)}
  one_mem' := by
    refine ⟨?_,Near.refl _ _,fun i => Commute.one_left _⟩
    simp [Orthogonal]
  mul_mem' := by
    rintro U W ⟨hu,hn,hc⟩ ⟨hw,hm,hd⟩
    refine ⟨orthogonal_mul hu hw,?_,fun i => (hc i).mul_left (hd i)⟩
    simpa only [Units.val_mul,one_mul] using hn.mul hm
  inv_mem' := by
    rintro U ⟨hu,hn,hc⟩
    exact ⟨orthogonal_inv hu,near_unit_inv I U hn,fun i => (hc i).units_inv_left⟩

def Comparison (I : Ideal R) (E F : Fin r → Mat R d) (U : (Mat R d)ˣ) : Prop :=
  Orthogonal U ∧ Near I (U : Mat R d) 1 ∧ ∀ i, (U : Mat R d)*E i=F i*U

theorem comparison_times_freedom {I : Ideal R} {E F : Fin r → Mat R d}
    {U H : (Mat R d)ˣ} (hu : Comparison I E F U) (hh : H ∈ freedomGroup I E) :
    Comparison I E F (U*H) := by
  refine ⟨orthogonal_mul hu.1 hh.1,?_,?_⟩
  · simpa only [Units.val_mul,one_mul] using hu.2.1.mul hh.2.1
  · intro i
    change (U : Mat R d)*(H : Mat R d)*E i=F i*((U : Mat R d)*(H : Mat R d))
    rw [mul_assoc,(hh.2.2 i).eq,← mul_assoc,hu.2.2 i,mul_assoc]

theorem difference_in_freedom {I : Ideal R} {E F : Fin r → Mat R d}
    {U₀ U : (Mat R d)ˣ} (h₀ : Comparison I E F U₀) (hu : Comparison I E F U) :
    U₀⁻¹*U ∈ freedomGroup I E := by
  refine ⟨orthogonal_mul (orthogonal_inv h₀.1) hu.1,?_,?_⟩
  · simpa only [Units.val_mul,one_mul] using (near_unit_inv I U₀ h₀.2.1).mul hu.2.1
  · intro i
    have hi : (↑U₀⁻¹ : Mat R d)*F i=E i*(↑U₀⁻¹ : Mat R d) := by
      have hh := congrArg (fun A : Mat R d => (↑U₀⁻¹ : Mat R d)*A*(↑U₀⁻¹ : Mat R d)) (h₀.2.2 i)
      simpa [mul_assoc] using hh.symm
    change (↑U₀⁻¹ : Mat R d)*(U : Mat R d)*E i=E i*((↑U₀⁻¹ : Mat R d)*(U : Mat R d))
    rw [mul_assoc,hu.2.2 i,← mul_assoc,hi,mul_assoc]

/-- S3: a bijection with the actual orthogonal near-identity centralizer;
its inverse is H ↦ U₀H, so every comparison and its unique parameter occur. -/
def comparisonEquiv (I : Ideal R) (E F : Fin r → Mat R d)
    (U₀ : (Mat R d)ˣ) (h₀ : Comparison I E F U₀) :
    {U : (Mat R d)ˣ // Comparison I E F U} ≃ freedomGroup I E where
  toFun U := ⟨U₀⁻¹*U.val,difference_in_freedom h₀ U.property⟩
  invFun H := ⟨U₀*H.val,comparison_times_freedom h₀ H.property⟩
  left_inv U := by apply Subtype.ext; simp [mul_assoc]
  right_inv H := by apply Subtype.ext; simp [mul_assoc]

end MathGauge.GR020
