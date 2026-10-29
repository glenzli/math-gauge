import InducedFibre

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MathGauge.Descent.FiniteFibres
universe g u v w
variable {Γ : Type g} [Group Γ] {T : Type u} [MulAction Γ T]
variable {X : Type v} [MulAction Γ X] (π : X →ₑ[(id : Γ → Γ)] T)

/-- The actual fibre, including the empty fibre. -/
def Fibre (t : T) := {x : X // π x=t}
instance fibreAction (t : T) : MulAction (MulAction.stabilizer Γ t) (Fibre π t) where
  smul a x := ⟨(a:Γ) • x.val,by rw [π.map_smul,x.property]; exact a.property⟩
  one_smul x := Subtype.ext (one_smul Γ x.val)
  mul_smul a b x := Subtype.ext (mul_smul (a:Γ) (b:Γ) x.val)
@[simp] theorem fibre_smul_val (t : T) (a : MulAction.stabilizer Γ t) (x : Fibre π t) :
    (a • x).val=(a:Γ) • x.val := rfl

abbrev OrbitIndex := Quotient (MulAction.orbitRel Γ T)
def orbitIndex (t : T) : OrbitIndex (Γ := Γ) (T := T) := Quotient.mk _ t
def representative (o : OrbitIndex (Γ := Γ) (T := T)) : T := o.out
@[simp] theorem orbit_representative (o : OrbitIndex (Γ := Γ) (T := T)) :
    orbitIndex (Γ := Γ) (representative (Γ := Γ) o)=o := Quotient.out_eq o
@[simp] theorem orbit_smul (a : Γ) (t : T) : orbitIndex (Γ := Γ) (a • t)=orbitIndex (Γ := Γ) t :=
  Quotient.sound ⟨a,rfl⟩

theorem exists_transport (t : T) : ∃ a : Γ, a • representative (Γ := Γ) (orbitIndex (Γ := Γ) t)=t := by
  have h : (MulAction.orbitRel Γ T) t (representative (Γ := Γ) (orbitIndex (Γ := Γ) t)) :=
    Quotient.exact (orbit_representative (orbitIndex (Γ := Γ) t)).symm
  exact h

def transport (t : T) : Γ := Classical.choose (exists_transport (Γ := Γ) t)
theorem transport_spec (t : T) : transport (Γ := Γ) t • representative (Γ := Γ) (orbitIndex (Γ := Γ) t)=t :=
  Classical.choose_spec (exists_transport (Γ := Γ) t)

def normalise (x : X) : Fibre π (representative (Γ := Γ) (orbitIndex (Γ := Γ) (π x))) :=
  ⟨(transport (Γ := Γ) (π x))⁻¹ • x,by
    rw [π.map_smul]
    calc
      _ = (transport (Γ := Γ) (π x))⁻¹ • (transport (Γ := Γ) (π x) • representative (orbitIndex (Γ := Γ) (π x))) :=
        congrArg ((transport (Γ := Γ) (π x))⁻¹ • ·) (transport_spec (Γ := Γ) (π x)).symm
      _ = _ := inv_smul_smul _ _⟩
@[simp] theorem transport_normalise (x : X) :
    transport (Γ := Γ) (π x) • (normalise π x).val=x := smul_inv_smul _ _

/-- Evaluation of the genuine balanced product into the original Γ-set. -/
def inducedEvaluation (t : T) : Induced (MulAction.stabilizer Γ t) (Fibre π t) → X :=
  Quotient.lift (fun p : Γ×Fibre π t => p.1 • p.2.val) (by
    rintro p q ⟨h,rfl⟩
    change p.1 • p.2.val=(p.1*(h:Γ)⁻¹) • ((h:Γ) • p.2.val)
    simp [mul_smul])
@[simp] theorem inducedEvaluation_mk (t : T) (a : Γ) (x : Fibre π t) :
    inducedEvaluation π t (inducedMk _ _ a x)=a • x.val := rfl

theorem inducedEvaluation_projection (t : T)
    (x : Induced (MulAction.stabilizer Γ t) (Fibre π t)) :
    π (inducedEvaluation π t x)=inducedProjection (Fibre π t) t x := by
  induction x using Quotient.inductionOn with
  | h p => exact (π.map_smul p.1 p.2.val).trans (congrArg (p.1 • ·) p.2.property)

theorem inducedEvaluation_equivariant (t : T) (a : Γ)
    (x : Induced (MulAction.stabilizer Γ t) (Fibre π t)) :
    inducedEvaluation π t (a • x)=a • inducedEvaluation π t x := by
  induction x using Quotient.inductionOn with
  | h p => exact mul_smul _ _ _

theorem inducedEvaluation_injective (t : T) : Function.Injective (inducedEvaluation π t) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      intro he
      change p.1 • p.2.val=q.1 • q.2.val at he
      have ht : p.1 • t=q.1 • t := by
        have hh := congrArg π he
        simpa only [π.map_smul,p.2.property,q.2.property] using hh
      let a : MulAction.stabilizer Γ t := ⟨q.1⁻¹*p.1,by
        change (q.1⁻¹*p.1) • t=t
        rw [mul_smul,ht,inv_smul_smul]⟩
      apply Quotient.sound
      refine ⟨a,?_⟩
      apply Prod.ext
      · change q.1=p.1*(q.1⁻¹*p.1)⁻¹
        simp [mul_assoc]
      · apply Subtype.ext
        change q.2.val=(q.1⁻¹*p.1) • p.2.val
        rw [mul_smul,he,inv_smul_smul]

/-- Disjoint union of the actual induced fibres over all base orbits. -/
def Reconstructed := (o : OrbitIndex (Γ := Γ) (T := T)) ×
  Induced (MulAction.stabilizer Γ (representative (Γ := Γ) o)) (Fibre π (representative (Γ := Γ) o))

instance reconstructedAction : MulAction Γ (Reconstructed π) where
  smul a x := ⟨x.1,a • x.2⟩
  one_smul x := by
    rcases x with ⟨o,x⟩
    change (⟨o,(1:Γ) • x⟩ : Reconstructed π)=⟨o,x⟩
    rw [one_smul]
  mul_smul a b x := by
    rcases x with ⟨o,x⟩
    change (⟨o,(a*b) • x⟩ : Reconstructed π)=⟨o,a • (b • x)⟩
    rw [mul_smul]

def reconstructEvaluation (x : Reconstructed π) : X := inducedEvaluation π _ x.2

theorem reconstructEvaluation_equivariant (a : Γ) (x : Reconstructed π) :
    reconstructEvaluation π (a • x)=a • reconstructEvaluation π x :=
  inducedEvaluation_equivariant π _ a x.2

theorem reconstructEvaluation_orbit (x : Reconstructed π) :
    orbitIndex (Γ := Γ) (π (reconstructEvaluation π x))=x.1 := by
  rcases x with ⟨o,x⟩
  induction x using Quotient.inductionOn with
  | h p =>
    change orbitIndex (Γ := Γ) (π (p.1 • p.2.val))=o
    rw [π.map_smul,p.2.property,orbit_smul,orbit_representative]

theorem reconstructEvaluation_bijective : Function.Bijective (reconstructEvaluation π) := by
  constructor
  · rintro ⟨o,x⟩ ⟨p,y⟩ h
    have hop : o=p := (reconstructEvaluation_orbit π ⟨o,x⟩).symm.trans
      ((congrArg (fun x => orbitIndex (Γ := Γ) (π x)) h).trans (reconstructEvaluation_orbit π ⟨p,y⟩))
    subst p
    have hxy : x=y := inducedEvaluation_injective π _ h
    subst y
    rfl
  · intro x
    refine ⟨⟨orbitIndex (Γ := Γ) (π x),inducedMk _ _ (transport (Γ := Γ) (π x)) (normalise π x)⟩,?_⟩
    exact transport_normalise π x

def reconstructionEquiv : Reconstructed π ≃ X :=
  Equiv.ofBijective (reconstructEvaluation π) (reconstructEvaluation_bijective π)

instance reconstructedFinite [Finite X] : Finite (Reconstructed π) :=
  Finite.of_injective _ (reconstructEvaluation_bijective π).injective

end MathGauge.Descent.FiniteFibres
