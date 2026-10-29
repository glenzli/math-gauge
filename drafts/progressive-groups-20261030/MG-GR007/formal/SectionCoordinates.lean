import AffineTower
import TowerSplit
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace MathGauge.GR007.SectionCoordinates
universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {A B C : Type w} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module k A] [Module k B] [Module k C]
variable {ρA : Representation k G A} {ρB : Representation k G B} {σ : Representation k G C}

def Sections (q : ρB.IntertwiningMap σ) :=
  {s : σ.IntertwiningMap ρB // q.comp s=IntertwiningMap.id σ}

variable (i : ρA.IntertwiningMap ρB) (q : ρB.IntertwiningMap σ)
variable (hi : Function.Injective i)
variable (hex : LinearMap.range i.toLinearMap=LinearMap.ker q.toLinearMap)
variable (s : Sections q)

def shift (u : σ.IntertwiningMap ρA) : Sections q :=
  ⟨s.val+i.comp u, by
    apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    change q (s.val c+i (u c))=c
    rw [map_add,MathGauge.SplitRepresentation.qi i q hex,add_zero]
    exact congrArg (fun f => f c) s.property⟩

include hi in
theorem shift_bijective : Function.Bijective (shift i q hex s) := by
  constructor
  · intro u v huv
    have hh := congrArg Subtype.val huv
    have he : i.comp u=i.comp v := add_left_cancel hh
    apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    exact hi (congrArg (fun f => f c) he)
  · intro t
    obtain ⟨u,hu,_⟩ :=
      (MathGauge.SplitRepresentation.sections_classified i q hi hex s.val t.val s.property).mp t.property
    exact ⟨u,Subtype.ext hu.symm⟩

/-- This is the actual section torsor, with direction Hom_G(C,A). -/
def coordinates : (σ.IntertwiningMap ρA) ≃ Sections q :=
  Equiv.ofBijective (shift i q hex s) (shift_bijective i q hi hex s)

@[simp] theorem coordinates_val (u : σ.IntertwiningMap ρA) :
    (coordinates i q hi hex s u).val=s.val+i.comp u := rfl

/-- Transport of the standard torsor, followed below by the formula for its
actual action in the ambient Hom_G(C,B). -/
@[reducible] def torsorOfEquiv {W X : Type*} [AddCommGroup W] (e : W ≃ X) : AddTorsor W X where
  vadd u x := e (u+e.symm x)
  vsub x y := e.symm x-e.symm y
  zero_vadd x := by change e (0+e.symm x)=x; simp
  add_vadd u v x := by change e (u+v+e.symm x)=e (u+e.symm (e (v+e.symm x))); simp [add_assoc]
  nonempty := ⟨e 0⟩
  vsub_vadd' x y := by change e (e.symm x-e.symm y+e.symm y)=x; simp
  vadd_vsub' u x := by change e.symm (e (u+e.symm x))-e.symm x=u; simp

@[reducible] def sectionTorsor : AddTorsor (σ.IntertwiningMap ρA) (Sections q) :=
  torsorOfEquiv (coordinates i q hi hex s)

theorem torsor_action (u : σ.IntertwiningMap ρA) (t : Sections q) :
    letI := sectionTorsor i q hi hex s
    (u +ᵥ t : Sections q).val=t.val+i.comp u := by
  change (coordinates i q hi hex s (u+(coordinates i q hi hex s).symm t)).val=_
  rw [coordinates_val,IntertwiningMap.add_comp]
  have ht := congrArg Subtype.val ((coordinates i q hi hex s).apply_symm_apply t)
  rw [coordinates_val] at ht
  rw [← ht]
  abel

/-- The coordinate chart preserves binary affine combinations over k. -/
theorem coordinates_affine (a : k) (u v : σ.IntertwiningMap ρA) :
    (coordinates i q hi hex s (a • u+(1-a) • v)).val=
      a • (coordinates i q hi hex s u).val+(1-a) • (coordinates i q hi hex s v).val := by
  apply IntertwiningMap.ext; apply LinearMap.ext; intro c
  change s.val c+i (a • u c+(1-a) • v c)=
    a • (s.val c+i (u c))+(1-a) • (s.val c+i (v c))
  simp only [map_add,map_smul,smul_add,sub_smul,one_smul]
  simp only [map_sub,map_smul]
  abel

/-- The actual torsor operation, including in characteristic two. -/
theorem coordinates_ternary (u v w : σ.IntertwiningMap ρA) :
    (coordinates i q hi hex s (u-v+w)).val=
      (coordinates i q hi hex s u).val-(coordinates i q hi hex s v).val+
        (coordinates i q hi hex s w).val := by
  apply IntertwiningMap.ext; apply LinearMap.ext; intro c
  change s.val c+i (u c-v c+w c)=
    (s.val c+i (u c))-(s.val c+i (v c))+(s.val c+i (w c))
  simp only [map_add,map_sub]
  abel

section Tower
variable {An Bn : ℕ → Type w} [∀ n, AddCommGroup (An n)] [∀ n, AddCommGroup (Bn n)]
variable [∀ n, Module k (An n)] [∀ n, Module k (Bn n)]
variable (ρAn : ∀ n, Representation k G (An n)) (ρBn : ∀ n, Representation k G (Bn n))
variable (σn : Representation k G C)
variable (a : ∀ n, (ρAn (n+1)).IntertwiningMap (ρAn n))
variable (b : ∀ n, (ρBn (n+1)).IntertwiningMap (ρBn n))
variable (inc : ∀ n, (ρAn n).IntertwiningMap (ρBn n))
variable (quot : ∀ n, (ρBn n).IntertwiningMap σn)
variable (hb : ∀ n, (b n).comp (inc (n+1))=(inc n).comp (a n))
variable (hq : ∀ n, (quot n).comp (b n)=quot (n+1))
variable (hin : ∀ n, Function.Injective (inc n))
variable (he : ∀ n, LinearMap.range (inc n).toLinearMap=LinearMap.ker (quot n).toLinearMap)
variable (base : ∀ n, Sections (quot n))

def transition (n : ℕ) (s : Sections (quot (n+1))) : Sections (quot n) :=
  ⟨(b n).comp s.val,by
    change ((quot n).comp (b n)).comp s.val=_
    rw [hq,s.property]⟩

def linearTransition (n : ℕ) : (σn.IntertwiningMap (ρAn (n+1))) →ₗ[k]
    (σn.IntertwiningMap (ρAn n)) := IntertwiningMap.llcomp _ _ _ (a n)

def displacement (n : ℕ) : σn.IntertwiningMap (ρAn n) :=
  (coordinates (inc n) (quot n) (hin n) (he n) (base n)).symm
    (transition ρBn σn b quot hq n (base (n+1)))

include hb in
theorem transition_coordinates (n : ℕ) (u : σn.IntertwiningMap (ρAn (n+1))) :
    transition ρBn σn b quot hq n
      (coordinates (inc (n+1)) (quot (n+1)) (hin (n+1)) (he (n+1)) (base (n+1)) u)=
    coordinates (inc n) (quot n) (hin n) (he n) (base n)
      (linearTransition ρAn σn a n u+displacement ρAn ρBn σn b inc quot hq hin he base n) := by
  apply Subtype.ext
  have hd := congrArg Subtype.val
    ((coordinates (inc n) (quot n) (hin n) (he n) (base n)).apply_symm_apply
      (transition ρBn σn b quot hq n (base (n+1))))
  change (base n).val+(inc n).comp (displacement ρAn ρBn σn b inc quot hq hin he base n)=
    (b n).comp (base (n+1)).val at hd
  change (b n).comp ((base (n+1)).val+(inc (n+1)).comp u)=
    (base n).val+(inc n).comp ((a n).comp u+_)
  rw [IntertwiningMap.add_comp,IntertwiningMap.add_comp,← hd]
  have hcomp : (b n).comp ((inc (n+1)).comp u)=(inc n).comp ((a n).comp u) := by
    change ((b n).comp (inc (n+1))).comp u=((inc n).comp (a n)).comp u
    rw [hb]
  rw [hcomp]
  abel

include a inc hb hq hin he base in
/-- Finite dimension is imposed only on the actual section direction spaces. -/
theorem coherent_sections_of_finite_parameters
    [∀ n, FiniteDimensional k (σn.IntertwiningMap (ρAn n))] :
    ∃ s : ∀ n, σn.IntertwiningMap (ρBn n),
      (∀ n, (quot n).comp (s n)=IntertwiningMap.id σn) ∧
      (∀ n, (b n).comp (s (n+1))=s n) := by
  obtain ⟨u,hu⟩ := AffineTower.coherent
    (W := fun n => σn.IntertwiningMap (ρAn n))
    (linearTransition ρAn σn a) (displacement ρAn ρBn σn b inc quot hq hin he base)
  refine ⟨fun n => (coordinates (inc n) (quot n) (hin n) (he n) (base n) (u n)).val,
    fun n => (coordinates (inc n) (quot n) (hin n) (he n) (base n) (u n)).property,?_⟩
  intro n
  have ht := transition_coordinates ρAn ρBn σn a b inc quot hb hq hin he base n (u (n+1))
  have hn := hu n
  change linearTransition ρAn σn a n (u (n+1))+_=u n at hn
  rw [hn] at ht
  exact congrArg Subtype.val ht

end Tower
end MathGauge.GR007.SectionCoordinates
