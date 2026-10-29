import FibreMorphisms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace MathGauge.Descent.FiniteFibres
universe g u v
variable {Γ : Type g} [Group Γ] {T : Type u} [MulAction Γ T]
variable {X : Type v} [MulAction Γ X] (π : X →ₑ[(id : Γ → Γ)] T)

def FibreTrivial : Prop := ∀ (o : OrbitIndex (Γ := Γ) (T := T))
  (a : MulAction.stabilizer Γ (representative o)) (x : Fibre π (representative o)), a • x=x

def PointTrivial : Prop := ∀ (a : Γ) (x : X), a • π x=π x → a • x=x

theorem pointTrivial_iff_fibreTrivial : PointTrivial π ↔ FibreTrivial π := by
  constructor
  · intro h o a x
    apply Subtype.ext
    apply h (a:Γ) x.val
    rw [x.property]
    exact a.property
  · intro h a x ha
    obtain ⟨⟨o,x⟩,rfl⟩ := (reconstructEvaluation_bijective π).surjective x
    induction x using Quotient.inductionOn with
    | h p =>
      change a • (p.1 • p.2.val)=p.1 • p.2.val
      change a • π (p.1 • p.2.val)=π (p.1 • p.2.val) at ha
      have ht : a • (p.1 • representative o)=p.1 • representative o := by
        simpa only [π.map_smul,p.2.property] using ha
      let b : MulAction.stabilizer Γ (representative o) := ⟨p.1⁻¹*a*p.1,by
        rw [MulAction.mem_stabilizer_iff,mul_smul,mul_smul,ht,inv_smul_smul]⟩
      have hb : (p.1⁻¹*a*p.1) • p.2.val=p.2.val := congrArg Subtype.val (h o b p.2)
      calc
        _ = p.1 • ((p.1⁻¹*a*p.1) • p.2.val) := by simp [mul_smul]
        _ = _ := congrArg (p.1 • ·) hb

/-- Actual equivariant permutations over T, with composition as multiplication. -/
def AutOver : Subgroup (Equiv.Perm X) where
  carrier := {e | (∀ x, π (e x)=π x) ∧ ∀ (a : Γ) x, e (a • x)=a • e x}
  one_mem' := ⟨fun _ => rfl,fun _ _ => rfl⟩
  mul_mem' := by
    rintro e f ⟨he,heq⟩ ⟨hf,hfq⟩
    exact ⟨fun x => (he (f x)).trans (hf x),fun a x => by
      change e (f (a • x))=a • e (f x)
      rw [hfq,heq]⟩
  inv_mem' := by
    rintro e ⟨he,heq⟩
    constructor
    · intro x
      simpa using (he (e.symm x)).symm
    · intro a x
      apply e.injective
      change e (e.symm (a • x))=e (a • e.symm x)
      rw [heq]
      simp

def automorphismHom (e : AutOver π) : HomOver π π :=
  ⟨⟨e.val, e.property.2⟩,e.property.1⟩

def restrictAut (e : AutOver π) (o : OrbitIndex (Γ := Γ) (T := T)) :
    Equiv.Perm (Fibre π (representative o)) where
  toFun := restrictHom π π (automorphismHom π e) o
  invFun := restrictHom π π (automorphismHom π e⁻¹) o
  left_inv x := Subtype.ext (e.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.val.apply_symm_apply x.val)

theorem restrictAut_injective : Function.Injective (restrictAut π) := by
  intro e f h
  have hh : automorphismHom π e=automorphismHom π f := by
    apply (fibreHomEquiv π π).injective
    funext o
    apply MulActionHom.ext
    intro x
    exact congrArg (fun k => k o x) h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrArg (fun k : HomOver π π => k.hom x) hh

@[simp] theorem restrictAut_mul (e f : AutOver π) :
    restrictAut π (e*f)=restrictAut π e * restrictAut π f := by
  funext o
  apply Equiv.ext
  intro x
  rfl

/-- With trivial stabilizers every fibre permutation is automatically equivariant. -/
def permutationFibreMaps (h : FibreTrivial π)
    (e : ∀ o : OrbitIndex (Γ := Γ) (T := T), Equiv.Perm (Fibre π (representative o))) :
    FibreMaps π π := fun o => {
  toFun := e o
  map_smul' := fun a x => by
    change e o (a • x)=a • e o x
    rw [h o a x,h o a (e o x)] }

theorem permutation_extensions_inverse (h : FibreTrivial π)
    (e : ∀ o : OrbitIndex (Γ := Γ) (T := T), Equiv.Perm (Fibre π (representative o))) :
    composition π π π (extendHom π π (permutationFibreMaps π h (fun o => (e o).symm)))
      (extendHom π π (permutationFibreMaps π h e))=identity π := by
  apply (fibreHomEquiv π π).injective
  change restrictHom π π _=restrictHom π π _
  rw [restrict_composition,restrict_identity,restrict_extend,restrict_extend]
  funext o
  apply MulActionHom.ext
  intro x
  exact (e o).symm_apply_apply x

def extendAut (h : FibreTrivial π)
    (e : ∀ o : OrbitIndex (Γ := Γ) (T := T), Equiv.Perm (Fibre π (representative o))) : AutOver π :=
  ⟨{
    toFun := (extendHom π π (permutationFibreMaps π h e)).hom
    invFun := (extendHom π π (permutationFibreMaps π h (fun o => (e o).symm))).hom
    left_inv := fun x => congrArg (fun f : HomOver π π => f.hom x) (permutation_extensions_inverse π h e)
    right_inv := fun x => by
      have hh := permutation_extensions_inverse π h (fun o => (e o).symm)
      exact congrArg (fun f : HomOver π π => f.hom x) hh },
    (extendHom π π (permutationFibreMaps π h e)).over_base,
    (extendHom π π (permutationFibreMaps π h e)).hom.map_smul⟩

@[simp] theorem restrict_extendAut (h : FibreTrivial π)
    (e : ∀ o : OrbitIndex (Γ := Γ) (T := T), Equiv.Perm (Fibre π (representative o))) :
    restrictAut π (extendAut π h e)=e := by
  funext o
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact extendHom_on_fibre π π (permutationFibreMaps π h e) o x

/-- The asserted group computation, not merely a bijection of underlying sets. -/
def automorphismGroupEquiv (h : FibreTrivial π) :
    AutOver π ≃* (∀ o : OrbitIndex (Γ := Γ) (T := T), Equiv.Perm (Fibre π (representative o))) where
  toFun := restrictAut π
  invFun := extendAut π h
  left_inv e := restrictAut_injective π (restrict_extendAut π h (restrictAut π e))
  right_inv := restrict_extendAut π h
  map_mul' := restrictAut_mul π

end MathGauge.Descent.FiniteFibres
