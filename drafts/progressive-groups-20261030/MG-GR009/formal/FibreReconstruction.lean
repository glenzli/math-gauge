import OrbitFibres

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MathGauge.Descent.FiniteFibres
universe g u v
variable {Γ : Type g} [Group Γ] {T : Type u} [MulAction Γ T]
variable (Y : OrbitIndex (Γ := Γ) (T := T) → Type v)
variable [∀ o, MulAction (MulAction.stabilizer Γ (representative o)) (Y o)]

/-- The inverse construction on an arbitrary family of stabilizer sets. -/
def FamilyObject := (o : OrbitIndex (Γ := Γ) (T := T)) ×
  Induced (MulAction.stabilizer Γ (representative o)) (Y o)

instance familyAction : MulAction Γ (FamilyObject Y) where
  smul a x := ⟨x.1,a • x.2⟩
  one_smul x := by
    rcases x with ⟨o,x⟩
    change (⟨o,(1:Γ) • x⟩ : FamilyObject Y)=⟨o,x⟩
    rw [one_smul]
  mul_smul a b x := by
    rcases x with ⟨o,x⟩
    change (⟨o,(a*b) • x⟩ : FamilyObject Y)=⟨o,a • (b • x)⟩
    rw [mul_smul]

instance familyFinite [Finite Γ] [Finite T] [∀ o, Finite (Y o)] : Finite (FamilyObject Y) :=
  inferInstanceAs (Finite ((o : OrbitIndex (Γ := Γ) (T := T)) ×
    Induced (MulAction.stabilizer Γ (representative o)) (Y o)))

def familyProjection : FamilyObject Y →ₑ[(id : Γ → Γ)] T where
  toFun x := inducedProjection (Y x.1) (representative x.1) x.2
  map_smul' a x := inducedProjection_equivariant _ _ a x.2

theorem familyProjection_orbit (x : FamilyObject Y) :
    orbitIndex (Γ := Γ) (familyProjection Y x)=x.1 := by
  rcases x with ⟨o,x⟩
  induction x using Quotient.inductionOn with
  | h p =>
    change orbitIndex (Γ := Γ) (p.1 • representative o)=o
    rw [orbit_smul,orbit_representative]

def familyFibre (o : OrbitIndex (Γ := Γ) (T := T)) (y : Y o) :
    Fibre (familyProjection Y) (representative o) :=
  ⟨⟨o,inducedMk _ _ (1:Γ) y⟩,one_smul _ _⟩

theorem familyFibre_bijective (o : OrbitIndex (Γ := Γ) (T := T)) :
    Function.Bijective (familyFibre Y o) := by
  constructor
  · intro x y h
    have hh : inducedMk _ _ (1:Γ) x=inducedMk _ _ (1:Γ) y :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
    apply (canonicalFibre_bijective (Γ := Γ) (Y o) (representative o)).injective
    exact Subtype.ext hh
  · rintro ⟨⟨p,x⟩,hx⟩
    have hpo : p=o := (familyProjection_orbit Y ⟨p,x⟩).symm.trans
      ((congrArg (orbitIndex (Γ := Γ)) hx).trans (orbit_representative o))
    subst p
    obtain ⟨y,hy⟩ := (canonicalFibre_bijective (Γ := Γ) (Y o) (representative o)).surjective ⟨x,hx⟩
    refine ⟨y,Subtype.ext ?_⟩
    exact congrArg (fun z => (⟨o,z⟩ : FamilyObject Y)) (congrArg Subtype.val hy)

theorem familyFibre_equivariant (o : OrbitIndex (Γ := Γ) (T := T))
    (h : MulAction.stabilizer Γ (representative o)) (y : Y o) :
    familyFibre Y o (h • y)=h • familyFibre Y o y := by
  apply Subtype.ext
  change (⟨o,inducedMk _ _ (1:Γ) (h • y)⟩ : FamilyObject Y)=⟨o,(h:Γ) • inducedMk _ _ (1:Γ) y⟩
  rw [induced_smul_mk,mul_one]
  have he := induced_balance (MulAction.stabilizer Γ (representative o)) (Y o) (h:Γ) h y
  simpa only [mul_inv_cancel] using congrArg (fun z => (⟨o,z⟩ : FamilyObject Y)) he

/-- Restricting the inverse construction recovers each supplied stabilizer set equivariantly. -/
def familyFibreEquiv (o : OrbitIndex (Γ := Γ) (T := T)) :
    Y o ≃ Fibre (familyProjection Y) (representative o) :=
  Equiv.ofBijective (familyFibre Y o) (familyFibre_bijective Y o)

end MathGauge.Descent.FiniteFibres
