import OrbitFibres

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MathGauge.Descent.FiniteFibres
universe g u v w z
variable {Γ : Type g} [Group Γ] {T : Type u} [MulAction Γ T]
variable {X : Type v} [MulAction Γ X] {Y : Type w} [MulAction Γ Y]
variable (π : X →ₑ[(id : Γ → Γ)] T) (ρ : Y →ₑ[(id : Γ → Γ)] T)

/-- Actual equivariant maps over the given base. -/
structure HomOver where
  hom : X →ₑ[(id : Γ → Γ)] Y
  over_base : ∀ x, ρ (hom x)=π x

@[ext] theorem HomOver.ext {f g : HomOver π ρ} (h : ∀ x, f.hom x=g.hom x) : f=g := by
  cases f with | mk f hf =>
    cases g with | mk g hg =>
      have hfg : f=g := MulActionHom.ext h
      subst g
      rfl

abbrev FibreMaps := ∀ o : OrbitIndex (Γ := Γ) (T := T),
  Fibre π (representative o) →ₑ[(id : MulAction.stabilizer Γ (representative o) → MulAction.stabilizer Γ (representative o))] Fibre ρ (representative o)

def restrictHom (f : HomOver π ρ) : FibreMaps π ρ := fun o => {
  toFun := fun x => ⟨f.hom x.val,(f.over_base x.val).trans x.property⟩
  map_smul' := fun a x => Subtype.ext (f.hom.map_smul (a:Γ) x.val) }

/-- A fibre map extends along the genuine balanced-product quotient. -/
def extensionEvaluation (f : FibreMaps π ρ) (x : Reconstructed π) : Y :=
  Quotient.lift (fun p : Γ×Fibre π (representative x.1) => p.1 • (f x.1 p.2).val) (by
    rintro p q ⟨h,rfl⟩
    change p.1 • (f x.1 p.2).val=(p.1*(h:Γ)⁻¹) • (f x.1 (h • p.2)).val
    rw [(f x.1).map_smul]
    simp [mul_smul]) x.2

def extendFunction (f : FibreMaps π ρ) (x : X) : Y :=
  extensionEvaluation π ρ f ((reconstructionEquiv π).symm x)

theorem extendFunction_evaluation (f : FibreMaps π ρ) (x : Reconstructed π) :
    extendFunction π ρ f (reconstructEvaluation π x)=extensionEvaluation π ρ f x := by
  change extensionEvaluation π ρ f ((reconstructionEquiv π).symm ((reconstructionEquiv π) x))=_
  rw [Equiv.symm_apply_apply]

theorem extendFunction_mk (f : FibreMaps π ρ) (o : OrbitIndex (Γ := Γ) (T := T))
    (a : Γ) (x : Fibre π (representative o)) :
    extendFunction π ρ f (a • x.val)=a • (f o x).val :=
  extendFunction_evaluation π ρ f ⟨o,inducedMk _ _ a x⟩

def extendHom (f : FibreMaps π ρ) : HomOver π ρ where
  hom := {
    toFun := extendFunction π ρ f
    map_smul' := by
      intro a x
      obtain ⟨⟨o,x⟩,rfl⟩ := (reconstructEvaluation_bijective π).surjective x
      induction x using Quotient.inductionOn with
      | h p =>
        change extendFunction π ρ f (a • (p.1 • p.2.val))=a • extendFunction π ρ f (p.1 • p.2.val)
        rw [← mul_smul,extendFunction_mk,extendFunction_mk,mul_smul] }
  over_base := by
    intro x
    obtain ⟨⟨o,x⟩,rfl⟩ := (reconstructEvaluation_bijective π).surjective x
    induction x using Quotient.inductionOn with
    | h p =>
      change ρ (extendFunction π ρ f (p.1 • p.2.val))=π (p.1 • p.2.val)
      rw [extendFunction_mk,ρ.map_smul,π.map_smul,(f o p.2).property,p.2.property]

@[simp] theorem extendHom_on_fibre (f : FibreMaps π ρ)
    (o : OrbitIndex (Γ := Γ) (T := T)) (x : Fibre π (representative o)) :
    (extendHom π ρ f).hom x.val=(f o x).val := by
  have h := extendFunction_mk π ρ f o 1 x
  simpa only [one_smul] using h

@[simp] theorem restrict_extend (f : FibreMaps π ρ) : restrictHom π ρ (extendHom π ρ f)=f := by
  funext o
  apply MulActionHom.ext
  intro x
  apply Subtype.ext
  exact extendHom_on_fibre π ρ f o x

@[simp] theorem extend_restrict (f : HomOver π ρ) : extendHom π ρ (restrictHom π ρ f)=f := by
  apply HomOver.ext
  intro x
  obtain ⟨⟨o,x⟩,rfl⟩ := (reconstructEvaluation_bijective π).surjective x
  induction x using Quotient.inductionOn with
  | h p =>
    change extendFunction π ρ (restrictHom π ρ f) (p.1 • p.2.val)=f.hom (p.1 • p.2.val)
    rw [extendFunction_mk,f.hom.map_smul]
    rfl

/-- The full morphism classification, with no omission of empty fibres. -/
def fibreHomEquiv : HomOver π ρ ≃ FibreMaps π ρ where
  toFun := restrictHom π ρ
  invFun := extendHom π ρ
  left_inv := extend_restrict π ρ
  right_inv := restrict_extend π ρ

def identity : HomOver π π := ⟨MulActionHom.id Γ,fun _ => rfl⟩

def composition {Z : Type z} [MulAction Γ Z] (σ : Z →ₑ[(id : Γ → Γ)] T)
    (g : HomOver ρ σ) (f : HomOver π ρ) : HomOver π σ :=
  ⟨g.hom.comp f.hom,fun x => (g.over_base (f.hom x)).trans (f.over_base x)⟩

theorem restrict_identity : restrictHom π π (identity π)=fun _ => MulActionHom.id _ := rfl

theorem restrict_composition {Z : Type z} [MulAction Γ Z] (σ : Z →ₑ[(id : Γ → Γ)] T)
    (g : HomOver ρ σ) (f : HomOver π ρ) :
    restrictHom π σ (composition π ρ σ g f)=fun o => (restrictHom ρ σ g o).comp (restrictHom π ρ f o) := rfl

end MathGauge.Descent.FiniteFibres
