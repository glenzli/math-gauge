import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Tactic

noncomputable section
open Representation
namespace MathGauge.SectionTransport
universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {A B C D E F : Type w}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable [AddCommGroup E] [AddCommGroup F]
variable [Module k A] [Module k B] [Module k C] [Module k D] [Module k E] [Module k F]
variable {ρA : Representation k G A} {ρB : Representation k G B}
variable {ρC : Representation k G C} {ρD : Representation k G D}
variable {ρE : Representation k G E} {ρF : Representation k G F}

def homEquiv (a : Representation.Equiv ρA ρC) (b : Representation.Equiv ρB ρD) :
    ρA.IntertwiningMap ρB ≃ₗ[k] ρC.IntertwiningMap ρD where
  toFun f := b.toIntertwiningMap.comp (f.comp a.symm.toIntertwiningMap)
  invFun f := b.symm.toIntertwiningMap.comp (f.comp a.toIntertwiningMap)
  left_inv f := by apply IntertwiningMap.ext; apply LinearMap.ext; intro x; simp
  right_inv f := by apply IntertwiningMap.ext; apply LinearMap.ext; intro x; simp
  map_add' := by intro f g; apply IntertwiningMap.ext; apply LinearMap.ext; intro x; simp
  map_smul' := by intro r f; apply IntertwiningMap.ext; apply LinearMap.ext; intro x; simp

@[simp] theorem homEquiv_apply (a : Representation.Equiv ρA ρC)
    (b : Representation.Equiv ρB ρD) (f : ρA.IntertwiningMap ρB) (x : C) :
    homEquiv a b f x=b (f (a.symm x)) := rfl

theorem transport_identity (f : ρA.IntertwiningMap ρB) :
    homEquiv (Representation.Equiv.refl ρA) (Representation.Equiv.refl ρB) f=f := rfl

theorem transport_composition (a : Representation.Equiv ρA ρC)
    (b : Representation.Equiv ρB ρD) (c : Representation.Equiv ρC ρE)
    (d : Representation.Equiv ρD ρF) (f : ρA.IntertwiningMap ρB) :
    homEquiv c d (homEquiv a b f)=homEquiv (a.trans c) (b.trans d) f := rfl

theorem transport_section (a : Representation.Equiv ρA ρC)
    (b : Representation.Equiv ρB ρD) (q : ρB.IntertwiningMap ρA)
    (q' : ρD.IntertwiningMap ρC)
    (hq : q'.comp b.toIntertwiningMap=a.toIntertwiningMap.comp q)
    (s : ρA.IntertwiningMap ρB) (hs : q.comp s=IntertwiningMap.id ρA) :
    q'.comp (homEquiv a b s)=IntertwiningMap.id ρC := by
  apply IntertwiningMap.ext; apply LinearMap.ext; intro x
  change q' (b (s (a.symm x)))=x
  have hh := congrArg (fun f : ρB.IntertwiningMap ρC => f (s (a.symm x))) hq
  change q' (b (s (a.symm x)))=a (q (s (a.symm x))) at hh
  rw [hh]
  have hh' := congrArg (fun f : ρA.IntertwiningMap ρA => f (a.symm x)) hs
  change q (s (a.symm x))=a.symm x at hh'
  rw [hh']; exact a.apply_symm_apply x

section Tower
variable {V V' : ℕ → Type w}
variable [∀ n, AddCommGroup (V n)] [∀ n, AddCommGroup (V' n)]
variable [∀ n, Module k (V n)] [∀ n, Module k (V' n)]
variable (ρ : ∀ n, Representation k G (V n)) (ρ' : ∀ n, Representation k G (V' n))
variable (b : ∀ n, (ρ (n+1)).IntertwiningMap (ρ n))
variable (b' : ∀ n, (ρ' (n+1)).IntertwiningMap (ρ' n))
variable (e : ∀ n, Representation.Equiv (ρ n) (ρ' n))
variable (a : Representation.Equiv ρA ρC)

/-- The stated b_n s_n d^{-1} formula preserves every transition equation. -/
theorem transport_coherent
    (hb : ∀ n, (b' n).comp (e (n+1)).toIntertwiningMap=(e n).toIntertwiningMap.comp (b n))
    (s : ∀ n, ρA.IntertwiningMap (ρ n))
    (hs : ∀ n, (b n).comp (s (n+1))=s n) :
    ∀ n, (b' n).comp (homEquiv a (e (n+1)) (s (n+1)))=homEquiv a (e n) (s n) := by
  intro n; apply IntertwiningMap.ext; apply LinearMap.ext; intro x
  change b' n (e (n+1) (s (n+1) (a.symm x)))=e n (s n (a.symm x))
  have hh := congrArg (fun f : (ρ (n+1)).IntertwiningMap (ρ' n) => f (s (n+1) (a.symm x))) (hb n)
  change b' n (e (n+1) (s (n+1) (a.symm x)))=e n (b n (s (n+1) (a.symm x))) at hh
  rw [hh]
  exact congrArg (e n) (congrArg (fun f : ρA.IntertwiningMap (ρ n) => f (a.symm x)) (hs n))

/-- Inverse diagram isomorphisms satisfy the inverse transition equations. -/
theorem inverse_diagram
    (hb : ∀ n, (b' n).comp (e (n+1)).toIntertwiningMap=(e n).toIntertwiningMap.comp (b n)) :
    ∀ n, (b n).comp (e (n+1)).symm.toIntertwiningMap=(e n).symm.toIntertwiningMap.comp (b' n) := by
  intro n; apply IntertwiningMap.ext; apply LinearMap.ext; intro x
  apply (e n).toLinearEquiv.injective
  change e n (b n ((e (n+1)).symm x))=e n ((e n).symm (b' n x))
  rw [(e n).apply_symm_apply]
  have hh := congrArg (fun f : (ρ (n+1)).IntertwiningMap (ρ' n) => f ((e (n+1)).symm x)) (hb n)
  simpa using hh.symm

/-- The transformation of the whole family of maps is a linear equivalence, before imposing section equations. -/
def familyEquiv : (∀ n, ρA.IntertwiningMap (ρ n)) ≃ₗ[k] (∀ n, ρC.IntertwiningMap (ρ' n)) :=
  LinearEquiv.piCongrRight (fun n => homEquiv a (e n))

end Tower
end MathGauge.SectionTransport
