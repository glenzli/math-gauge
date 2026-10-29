import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Tactic

noncomputable section
open Representation
namespace MathGauge.SplitRepresentation
universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {A B C D : Type w} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable [Module k A] [Module k B] [Module k C] [Module k D]
variable {ρA : Representation k G A} {ρB : Representation k G B}
variable {ρC : Representation k G C} {ρD : Representation k G D}
variable (i : ρA.IntertwiningMap ρB) (q : ρB.IntertwiningMap ρC)
variable (hi : Function.Injective i) (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)

include hex in
theorem qi (a : A) : q (i a)=0 := by
  have h : i a ∈ LinearMap.ker q.toLinearMap := by rw [← hex]; exact ⟨a,rfl⟩
  exact h

include hi hex

/-- Actual equivariant linear factorization through the injective kernel map. -/
theorem kernel_factor (f : ρD.IntertwiningMap ρB) (hf : q.comp f=0) :
    ∃! u : ρD.IntertwiningMap ρA, i.comp u=f := by
  have hh : ∀ d, ∃ a, i a=f d := by
    intro d
    have hd : f d ∈ LinearMap.ker q.toLinearMap := congrArg (fun t : ρD.IntertwiningMap ρC => t d) hf
    rw [← hex] at hd
    exact hd
  choose u hu using hh
  let ul : D →ₗ[k] A :=
    { toFun := u
      map_add' := by intro x y; apply hi; simp only [map_add, hu]
      map_smul' := by intro a x; apply hi; simp only [map_smul, hu, RingHom.id_apply] }
  let ue : ρD.IntertwiningMap ρA :=
    { toLinearMap := ul
      isIntertwining' := by
        intro g; apply LinearMap.ext; intro d
        apply hi
        change i (u (ρD g d))=i (ρA g (u d))
        rw [hu, IntertwiningMap.isIntertwining ρA ρB i, hu,
          IntertwiningMap.isIntertwining ρD ρB f] }
  refine ⟨ue, ?_, ?_⟩
  · apply IntertwiningMap.ext; apply LinearMap.ext; exact hu
  · intro v hv
    apply IntertwiningMap.ext; apply LinearMap.ext; intro d
    apply hi
    exact (congrArg (fun t => t d) hv).trans (hu d).symm

/-- Every equivariant section differs uniquely by an equivariant kernel map. -/
theorem sections_classified (s t : ρC.IntertwiningMap ρB)
    (hs : q.comp s=IntertwiningMap.id ρC) :
    q.comp t=IntertwiningMap.id ρC ↔
      ∃! u : ρC.IntertwiningMap ρA, t=s+i.comp u := by
  constructor
  · intro ht
    have hf : q.comp (t-s)=0 := by
      apply IntertwiningMap.ext; apply LinearMap.ext; intro c
      change q (t c-s c)=0
      rw [map_sub]
      have hh := congrArg (fun f => f c) ht
      have hh' := congrArg (fun f => f c) hs
      change q (t c)=c at hh
      change q (s c)=c at hh'
      rw [hh,hh',sub_self]
    obtain ⟨u,hu,huq⟩ := kernel_factor i q hi hex (t-s) hf
    refine ⟨u, ?_, ?_⟩
    · apply IntertwiningMap.ext; apply LinearMap.ext; intro c
      have h := congrArg (fun f => f c) hu
      change i (u c)=t c-s c at h
      change t c=s c+i (u c)
      rw [h]; abel
    · intro v hv
      apply huq v
      apply IntertwiningMap.ext; apply LinearMap.ext; intro c
      have h := congrArg (fun f => f c) hv
      change t c=s c+i (v c) at h
      change i (v c)=t c-s c
      rw [h]; abel
  · rintro ⟨u,hu,_⟩
    rw [hu]
    apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    change q (s c+i (u c))=c
    rw [map_add,qi i q hex,add_zero]
    exact congrArg (fun f => f c) hs

/-- The stated direct-sum map, with the given inclusion and the selected section. -/
def splitMap (s : ρC.IntertwiningMap ρB) : (ρA.prod ρC).IntertwiningMap ρB where
  toLinearMap := i.toLinearMap.coprod s.toLinearMap
  isIntertwining' := by
    intro g; apply LinearMap.ext; rintro ⟨a,c⟩
    change i (ρA g a)+s (ρC g c)=ρB g (i a+s c)
    rw [map_add,IntertwiningMap.isIntertwining ρA ρB i,
      IntertwiningMap.isIntertwining ρC ρB s]

theorem split_bijective (s : ρC.IntertwiningMap ρB) (hs : q.comp s=IntertwiningMap.id ρC) :
    Function.Bijective (splitMap i s) := by
  have hs' : ∀ c, q (s c)=c := fun c => congrArg (fun f => f c) hs
  constructor
  · rintro ⟨a,c⟩ ⟨a',c'⟩ h
    change i a+s c=i a'+s c' at h
    have hc : c=c' := by
      have hh := congrArg q h
      simpa only [map_add,qi i q hex,zero_add,hs'] using hh
    subst c'
    have ha : a=a' := hi (add_right_cancel h)
    subst a'; rfl
  · intro b
    have hz : b-s (q b) ∈ LinearMap.ker q.toLinearMap := by
      change q (b-s (q b))=0
      rw [map_sub,hs',sub_self]
    rw [← hex] at hz
    obtain ⟨a,ha⟩ := hz
    refine ⟨(a,q b), ?_⟩
    change i a+s (q b)=b
    change i a=b-s (q b) at ha
    rw [ha]; abel

/-- The equivalence is constructed from the original maps, not supplied as an assumption. -/
def splitEquiv (s : ρC.IntertwiningMap ρB) (hs : q.comp s=IntertwiningMap.id ρC) :
    Representation.Equiv (ρA.prod ρC) ρB :=
  (splitMap i s).ofBijective (split_bijective i q hi hex s hs)

@[simp] theorem split_inclusion (s : ρC.IntertwiningMap ρB) (hs : q.comp s=IntertwiningMap.id ρC)
    (a : A) : splitEquiv i q hi hex s hs (a,0)=i a := by
  change i a+s 0=i a; simp

@[simp] theorem split_projection (s : ρC.IntertwiningMap ρB) (hs : q.comp s=IntertwiningMap.id ρC)
    (a : A) (c : C) : q (splitEquiv i q hi hex s hs (a,c))=c := by
  change q (i a+s c)=c
  rw [map_add,qi i q hex,zero_add]
  exact congrArg (fun f => f c) hs

end MathGauge.SplitRepresentation
