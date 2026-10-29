import SplitRepresentation
import CoherentTransport

noncomputable section
open Representation
namespace MathGauge.SplitRepresentation
universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {A B C A' B' C' : Type w}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module k A] [Module k B] [Module k C]
variable [Module k A'] [Module k B'] [Module k C']
variable {ρA : Representation k G A} {ρB : Representation k G B} {ρC : Representation k G C}
variable {ρA' : Representation k G A'} {ρB' : Representation k G B'} {ρC' : Representation k G C'}

/-- Every decomposition with the specified inclusion is determined by its section. -/
theorem decomposition_classified (i : ρA.IntertwiningMap ρB) (q : ρB.IntertwiningMap ρC)
    (e : Representation.Equiv (ρA.prod ρC) ρB)
    (he : ∀ a, e (a,0)=i a) (hq : ∀ a c, q (e (a,c))=c) :
    ∃ s : ρC.IntertwiningMap ρB,
      q.comp s=IntertwiningMap.id ρC ∧ e.toIntertwiningMap=splitMap i s := by
  let j : ρC.IntertwiningMap (ρA.prod ρC) :=
    { toLinearMap := LinearMap.inr k A C
      isIntertwining' := by intro g; ext c <;> simp }
  let s := e.toIntertwiningMap.comp j
  refine ⟨s, ?_, ?_⟩
  · apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    exact hq 0 c
  · apply IntertwiningMap.ext; apply LinearMap.ext; rintro ⟨a,c⟩
    change e (a,c)=i a+e (0,c)
    have hp : (a,c)=(a,0)+(0,c) := by ext <;> simp
    rw [hp,map_add,he]

/-- A zero quotient has only the zero section. -/
theorem section_zero_quotient [Subsingleton C] (s : ρC.IntertwiningMap ρB) : s=0 := by
  apply IntertwiningMap.ext; apply LinearMap.ext; intro c
  rw [Subsingleton.elim c 0]; exact map_zero s

/-- A zero kernel makes the section unique; existence is still separately supplied. -/
theorem section_zero_kernel [Subsingleton A]
    (i : ρA.IntertwiningMap ρB) (q : ρB.IntertwiningMap ρC)
    (hi : Function.Injective i) (hex : LinearMap.range i.toLinearMap=LinearMap.ker q.toLinearMap)
    (s t : ρC.IntertwiningMap ρB)
    (hs : q.comp s=IntertwiningMap.id ρC) (ht : q.comp t=IntertwiningMap.id ρC) : t=s := by
  obtain ⟨u,hu,_⟩ := (sections_classified i q hi hex s t hs).mp ht
  rw [hu]
  have hz : i.comp u=0 := by
    apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    change i (u c)=0
    rw [Subsingleton.elim (u c) 0]; exact map_zero i
  rw [hz,add_zero]

/-- The transport of section differences is exactly transport of the kernel map. -/
theorem transport_translation
    (i : ρA.IntertwiningMap ρB) (i' : ρA'.IntertwiningMap ρB')
    (a : Representation.Equiv ρA ρA') (b : Representation.Equiv ρB ρB')
    (d : Representation.Equiv ρC ρC')
    (h : b.toIntertwiningMap.comp i=i'.comp a.toIntertwiningMap)
    (s : ρC.IntertwiningMap ρB) (t : ρC.IntertwiningMap ρA) :
    MathGauge.SectionTransport.homEquiv d b (s+i.comp t)=
      MathGauge.SectionTransport.homEquiv d b s+
      i'.comp (MathGauge.SectionTransport.homEquiv d a t) := by
  apply IntertwiningMap.ext; apply LinearMap.ext; intro c
  change b (s (d.symm c)+i (t (d.symm c)))=b (s (d.symm c))+i' (a (t (d.symm c)))
  rw [map_add]
  congr 1
  exact congrArg (fun f : ρA.IntertwiningMap ρB' => f (t (d.symm c))) h

end MathGauge.SplitRepresentation
