import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
open Representation Polynomial
namespace MathGauge.TowerBoundaries
universe u
variable {k : Type u} [Field k]

/-- The non-surjective transition from the split finite-dimensional example. -/
def collapse : k × k →ₗ[k] k × k where
  toFun x := (0,x.2)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

def elementarySection (t : k) : k →ₗ[k] k × k where
  toFun c := (t*c,c)
  map_add' := by intros; ext <;> simp [mul_add]
  map_smul' := by intros; ext <;> simp; ring

theorem collapse_not_surjective : ¬Function.Surjective (collapse : k × k →ₗ[k] k × k) := by
  intro h
  obtain ⟨x,hx⟩ := h (1,0)
  have h := congrArg Prod.fst hx
  change (0:k)=1 at h
  exact zero_ne_one h

theorem collapse_section (t : k) : collapse.comp (elementarySection t)=elementarySection 0 := by
  apply LinearMap.ext; intro c
  change (0,c)=(0*c,c)
  simp

theorem elementary_section_quotient (t : k) :
    (LinearMap.snd k k k).comp (elementarySection t)=LinearMap.id := rfl

/-- The shear automorphisms of the identity tower translate section parameters. -/
def shear (v : k) : (k × k) ≃ₗ[k] (k × k) where
  toFun x := (x.1+v*x.2,x.2)
  invFun x := (x.1-v*x.2,x.2)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp
  map_add' := by intros; ext <;> simp [mul_add]; ring
  map_smul' := by intros; ext <;> simp [mul_add]; ring

theorem shear_section (v t : k) : (shear v).toLinearMap.comp (elementarySection t)=elementarySection (t+v) := by
  ext c <;> simp [shear,elementarySection] <;> ring

theorem no_shear_fixed_section (s : k →ₗ[k] k × k)
    (hs : (LinearMap.snd k k k).comp s=LinearMap.id) :
    ¬(shear (1:k)).toLinearMap.comp s=s := by
  intro h
  have hq := congrArg (fun f : k →ₗ[k] k => f 1) hs
  change (s 1).2=1 at hq
  have hh := congrArg (fun f : k →ₗ[k] k × k => (f 1).1) h
  change (s 1).1+1*(s 1).2=(s 1).1 at hh
  rw [hq,one_mul] at hh
  have hbad : (1:k)=0 := (add_eq_left).mp hh
  exact one_ne_zero hbad

/-- The actual infinite-dimensional polynomial transition from the reference. -/
def polynomialTransition : k[X] × k →ₗ[k] k[X] × k where
  toFun x := (X*x.1+C x.2,x.2)
  map_add' := by intros; ext <;> simp [mul_add] <;> abel
  map_smul' := by intro r x; ext <;> simp [smul_add,smul_mul_assoc,mul_smul_comm]

/-- An infinite coherent lift would force every coefficient of one polynomial to be one. -/
theorem no_polynomial_recurrence : ¬∃ a : ℕ → k[X], ∀ n, a n=X*a (n+1)+1 := by
  rintro ⟨a,ha⟩
  have hc : ∀ m n, (a n).coeff m=1 := by
    intro m; induction m with
    | zero => intro n; rw [ha n]; simp
    | succ m ih => intro n; rw [ha n]; simpa [Polynomial.coeff_one, Nat.succ_ne_zero] using ih (n+1)
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p := a 0) (by omega : (a 0).natDegree < (a 0).natDegree+1)
  have ho := hc ((a 0).natDegree+1) 0
  exact zero_ne_one (hz.symm.trans ho)

theorem no_coherent_polynomial_sections : ¬∃ s : ℕ → (k →ₗ[k] k[X] × k),
    (∀ n, (LinearMap.snd k k[X] k).comp (s n)=LinearMap.id) ∧
    (∀ n, polynomialTransition.comp (s (n+1))=s n) := by
  rintro ⟨s,hs,hb⟩
  apply no_polynomial_recurrence (k := k)
  refine ⟨fun n => (s n 1).1, fun n => ?_⟩
  have hh := congrArg (fun f : k →ₗ[k] k[X] × k => (f 1).1) (hb n)
  have hq := congrArg (fun f : k →ₗ[k] k => f 1) (hs (n+1))
  change (s (n+1) 1).2=1 at hq
  change X*(s (n+1) 1).1+C ((s (n+1) 1).2)=(s n 1).1 at hh
  simpa only [hq,Polynomial.map_one] using hh.symm

abbrev F := ZMod 2
abbrev GroupTwo := Multiplicative F

/-- A genuine two-element-group representation in characteristic two. -/
def modularRep : Representation F GroupTwo (F × F) where
  toFun g :=
    { toFun x := (x.1+(Multiplicative.toAdd g)*x.2,x.2)
      map_add' := by intros; ext <;> simp [mul_add]; ring
      map_smul' := by intros; ext <;> simp [mul_add]; ring }
  map_one' := by ext <;> simp
  map_mul' := by intro g h; ext <;> simp [add_mul] <;> ring

def modularQuotient : modularRep.IntertwiningMap (Representation.trivial F GroupTwo F) where
  toLinearMap := LinearMap.snd F F F
  isIntertwining' _ := rfl

def modularInclusion : (Representation.trivial F GroupTwo F).IntertwiningMap modularRep where
  toLinearMap := LinearMap.inl F F F
  isIntertwining' := by
    intro g; apply LinearMap.ext; intro c
    change (c,0)=(c+(Multiplicative.toAdd g)*0,0)
    simp

/-- Local equivariant splitting really is needed: averaging fails in modular characteristic. -/
theorem no_modular_section : ¬∃ s : (Representation.trivial F GroupTwo F).IntertwiningMap modularRep,
    modularQuotient.comp s=IntertwiningMap.id _ := by
  rintro ⟨s,hs⟩
  have hq := congrArg (fun f : (Representation.trivial F GroupTwo F).IntertwiningMap _ => f 1) hs
  change (s 1).2=1 at hq
  have hh := IntertwiningMap.isIntertwining _ _ s (Multiplicative.ofAdd (1:F)) 1
  have hfst := congrArg Prod.fst hh
  change (s 1).1=(s 1).1+(1:F)*(s 1).2 at hfst
  rw [hq,one_mul] at hfst
  have hbad : (1:F)=0 := add_left_cancel (show (s 1).1+1=(s 1).1+0 by simpa using hfst.symm)
  exact one_ne_zero hbad

end MathGauge.TowerBoundaries
