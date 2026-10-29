import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MathGauge.Descent.FiniteFibres
universe g u v
variable {Γ : Type g} [Group Γ]
section Balanced
variable (K : Subgroup Γ) (Y : Type v) [MulAction K Y]

/-- The actual balanced-product relation (g h^{-1},h y) ~ (g,y). -/
def balanced : Setoid (Γ×Y) where
  r p q := ∃ h : K, q=(p.1*(h:Γ)⁻¹,h • p.2)
  iseqv := {
    refl p := ⟨1,by simp⟩
    symm := by
      rintro p q ⟨h,rfl⟩
      exact ⟨h⁻¹,by simp [mul_assoc]⟩
    trans := by
      rintro p q r ⟨h,rfl⟩ ⟨j,rfl⟩
      exact ⟨j*h,by simp [mul_smul,mul_assoc]⟩ }

def Induced := Quotient (balanced K Y)

def inducedMk (g : Γ) (y : Y) : Induced K Y := Quotient.mk _ (g,y)

instance inducedFinite [Finite Γ] [Finite Y] : Finite (Induced K Y) :=
  inferInstanceAs (Finite (Quotient (balanced K Y)))

instance inducedAction : MulAction Γ (Induced K Y) where
  smul a := Quotient.map (fun p : Γ×Y => (a*p.1,p.2)) (by
    rintro p q ⟨h,rfl⟩
    exact ⟨h,by simp [mul_assoc]⟩)
  one_smul x := by
    induction x using Quotient.inductionOn with
    | h p => change Quotient.mk _ (1*p.1,p.2)=Quotient.mk _ p; simp
  mul_smul a b x := by
    induction x using Quotient.inductionOn with
    | h p => change Quotient.mk _ ((a*b)*p.1,p.2)=Quotient.mk _ (a*(b*p.1),p.2); rw [mul_assoc]

@[simp] theorem induced_smul_mk (a g : Γ) (y : Y) :
    a • inducedMk K Y g y=inducedMk K Y (a*g) y := rfl

theorem induced_balance (g : Γ) (h : K) (y : Y) :
    inducedMk K Y (g*(h:Γ)⁻¹) (h • y)=inducedMk K Y g y := by
  change Quotient.mk (balanced K Y) (g*(h:Γ)⁻¹,h • y)=Quotient.mk (balanced K Y) (g,y)
  apply Eq.symm
  apply Quotient.sound
  exact ⟨h,rfl⟩

end Balanced

variable {T : Type u} [MulAction Γ T] (Y : Type v) (t : T)
variable [MulAction (MulAction.stabilizer Γ t) Y]

def inducedProjection : Induced (MulAction.stabilizer Γ t) Y → T :=
  Quotient.lift (fun p : Γ×Y => p.1 • t) (by
    rintro p q ⟨h,rfl⟩
    change p.1 • t=(p.1*(h:Γ)⁻¹) • t
    rw [mul_smul]
    have hh : (h:Γ)⁻¹ • t=t := (h⁻¹).property
    rw [hh])

@[simp] theorem inducedProjection_mk (g : Γ) (y : Y) :
    inducedProjection Y t (inducedMk (MulAction.stabilizer Γ t) Y g y)=g • t := rfl

theorem inducedProjection_equivariant (a : Γ)
    (x : Induced (MulAction.stabilizer Γ t) Y) :
    inducedProjection Y t (a • x)=a • inducedProjection Y t x := by
  induction x using Quotient.inductionOn with
  | h p => exact mul_smul _ _ _

def canonicalFibre (y : Y) : {x : Induced (MulAction.stabilizer Γ t) Y // inducedProjection Y t x=t} :=
  ⟨inducedMk _ Y (1:Γ) y,one_smul _ _⟩

theorem canonicalFibre_bijective : Function.Bijective (canonicalFibre (Γ := Γ) Y t) := by
  constructor
  · intro x y hxy
    obtain ⟨h,hh⟩ := Quotient.exact (congrArg Subtype.val hxy)
    have hfst : (1:Γ)=(h:Γ)⁻¹ := by simpa using congrArg Prod.fst hh
    have he : h=1 := Subtype.ext (inv_eq_one.mp hfst.symm)
    have hs := congrArg Prod.snd hh
    simpa only [he,one_smul] using hs.symm
  · rintro ⟨x,hx⟩
    induction x using Quotient.inductionOn with
    | h p =>
      change p.1 • t=t at hx
      let h : MulAction.stabilizer Γ t := ⟨p.1,hx⟩
      refine ⟨h • p.2,?_⟩
      apply Subtype.ext
      apply (Quotient.sound (s := balanced (MulAction.stabilizer Γ t) Y) ?_).symm
      exact ⟨h,by simp [h]⟩

def canonicalFibreEquiv : Y ≃ {x : Induced (MulAction.stabilizer Γ t) Y // inducedProjection Y t x=t} :=
  Equiv.ofBijective (canonicalFibre (Γ := Γ) Y t) (canonicalFibre_bijective (Γ := Γ) Y t)

end MathGauge.Descent.FiniteFibres
