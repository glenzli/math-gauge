import TowerDoublingExample

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Module CategoryTheory MathGauge.TensorClassification
namespace MathGauge.Tower.Dyadic
open FreeTower Examples

abbrev D := dyadicIntegers

def one : D := ⟨1,0,1,by norm_num⟩

def multiply (r : D) : D →ₗ[ℤ] D where
  toFun x := ⟨r.1*x.1,by
    obtain ⟨n,z,hz⟩ := r.2
    obtain ⟨m,w,hw⟩ := x.2
    refine ⟨n+m,z*w,?_⟩
    rw [hz,hw,pow_add]
    push_cast
    ring⟩
  map_add' x y := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' k x := by apply Subtype.ext; simp [zsmul_eq_mul,mul_left_comm]

@[simp] theorem multiply_value (r x : D) : (multiply r x).1=r.1*x.1 := rfl

/-- Division by all powers of two is actual rational division. Linearity over the
integers alone forces every endomorphism to be multiplication by its value at one. -/
theorem endomorphism_value (f : D →ₗ[ℤ] D) (x : D) : (f x).1=(f one).1*x.1 := by
  obtain ⟨n,z,hz⟩ := x.2
  have hn : (2:ℚ)^n≠0 := pow_ne_zero _ (by norm_num)
  have hx : (2^n:ℤ) • x=z • one := by
    apply Subtype.ext
    change ((2^n:ℤ):ℚ)*x.1=(z:ℚ)*1
    push_cast
    rw [hz]
    field_simp
  have hf := congrArg f hx
  rw [map_smul,map_smul] at hf
  have he : (2:ℚ)^n*(f x).1=(z:ℚ)*(f one).1 := by
    simpa only [Submodule.coe_smul,zsmul_eq_mul,Int.cast_pow,Int.cast_ofNat] using congrArg Subtype.val hf
  apply mul_left_cancel₀ hn
  rw [he,hz]
  field_simp

def endomorphismEquiv : (D →ₗ[ℤ] D) ≃ D where
  toFun f := f one
  invFun := multiply
  left_inv f := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (endomorphism_value f x).symm
  right_inv r := by apply Subtype.ext; simp [multiply,one]

theorem endomorphism_coefficient_add (f g : D →ₗ[ℤ] D) :
    endomorphismEquiv (f+g)=endomorphismEquiv f+endomorphismEquiv g := rfl

theorem endomorphism_coefficient_comp (f g : D →ₗ[ℤ] D) :
    (endomorphismEquiv (f.comp g)).1=(endomorphismEquiv f).1*(endomorphismEquiv g).1 :=
  endomorphism_value f (g one)

theorem endomorphism_coefficient_id : endomorphismEquiv LinearMap.id=one := rfl

theorem multiply_bijective_iff (r : D) :
    Function.Bijective (multiply r) ↔ ∃ s : D, r.1*s.1=1 := by
  constructor
  · intro h
    obtain ⟨s,hs⟩ := h.2 one
    exact ⟨s,congrArg Subtype.val hs⟩
  · rintro ⟨s,hrs⟩
    have hr : r.1≠0 := by intro hz; rw [hz,zero_mul] at hrs; norm_num at hrs
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ hr (congrArg Subtype.val hxy)
    · intro y
      refine ⟨multiply s y,?_⟩
      apply Subtype.ext
      change r.1*(s.1*y.1)=y.1
      rw [← mul_assoc,hrs,one_mul]

/-- The concrete forbidden target is represented at stage j by the identity,
which has the rational value 2^(-j) under the proved invariant isomorphism. -/
def reciprocalRecord (j : ℕ) : doublingTower.Record ℤ := doublingTower.recordOf ℤ j LinearMap.id

def integerProductComparison : doublingTower.Record (ℕ → ℤ) →ₗ[ℤ] (ℕ → doublingTower.Record ℤ) :=
  LinearMap.pi fun j => doublingTower.recordMap (LinearMap.proj j)

@[simp] theorem reciprocalRecord_value (j : ℕ) : doublingToRat (reciprocalRecord j)=1/(2:ℚ)^j := by
  rw [reciprocalRecord,doublingToRat_of]
  rfl

theorem reciprocalRecord_not_in_product_image :
    ¬ ∃ x, integerProductComparison x=reciprocalRecord := by
  rintro ⟨x,hx⟩
  obtain ⟨n,f,rfl⟩ := doublingTower.record_exists (ℕ → ℤ) x
  have he := congrArg (fun y : ℕ → doublingTower.Record ℤ => doublingToRat (y (n+1))) hx
  change doublingToRat (doublingTower.recordMap (LinearMap.proj (n+1))
    (doublingTower.recordOf (ℕ → ℤ) n f))=doublingToRat (reciprocalRecord (n+1)) at he
  rw [doublingTower.recordMap_of,doublingToRat_of,reciprocalRecord_value] at he
  change (f 1 (n+1):ℚ)/(2:ℚ)^n=1/(2:ℚ)^(n+1) at he
  rw [pow_succ] at he
  have hh : (2:ℚ)*(f 1 (n+1):ℚ)=1 := by
    field_simp at he
    simpa only [mul_comm] using he
  have hi : (2:ℤ)*f 1 (n+1)=1 := by exact_mod_cast hh
  omega

end MathGauge.Tower.Dyadic
