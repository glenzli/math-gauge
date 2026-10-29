import SectionTail
import BoundaryData

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Polynomial
namespace MathGauge.GR007.TrivialTowers
open MathGauge.TowerBoundaries SectionCoordinates
universe u
variable {k : Type u} [Field k]

def trivial (V : Type u) [AddCommGroup V] [Module k V] : Representation k Unit V :=
  Representation.trivial k Unit V

def equivariant {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f : V →ₗ[k] W) : (trivial (k := k) V).IntertwiningMap (trivial (k := k) W) where
  toLinearMap := f
  isIntertwining' _ := by ext x; rfl

def inclusion : (trivial (k := k) k[X]).IntertwiningMap (trivial (k := k) (k[X]×k)) :=
  equivariant (LinearMap.inl k k[X] k)
def quotient : (trivial (k := k) (k[X]×k)).IntertwiningMap (trivial (k := k) k) :=
  equivariant (LinearMap.snd k k[X] k)
def alpha : (trivial (k := k) k[X]).IntertwiningMap (trivial (k := k) k[X]) := equivariant polynomialKernel
def beta : (trivial (k := k) (k[X]×k)).IntertwiningMap (trivial (k := k) (k[X]×k)) := equivariant polynomialTransition

theorem polynomial_exact_row : Function.Injective (inclusion (k := k)) ∧
    LinearMap.range (inclusion (k := k)).toLinearMap=LinearMap.ker (quotient (k := k)).toLinearMap ∧
    Function.Surjective (quotient (k := k)) := product_row

theorem polynomial_commutes :
    (beta (k := k)).comp inclusion=inclusion.comp alpha ∧ (quotient (k := k)).comp beta=quotient := by
  constructor
  · apply IntertwiningMap.ext; exact polynomial_diagram.1
  · apply IntertwiningMap.ext; exact polynomial_diagram.2

def baseSection : Sections (quotient (k := k)) :=
  ⟨equivariant (LinearMap.inr k k[X] k),by apply IntertwiningMap.ext; rfl⟩

def nextSection (n : ℕ) (s : Sections (quotient (k := k))) : Sections (quotient (k := k)) :=
  ⟨beta.comp s.val,by
    change (quotient.comp beta).comp s.val=_
    rw [polynomial_commutes.2,s.property]⟩

theorem polynomial_no_global_sections :
    ¬∃ s : ℕ → (trivial (k := k) k).IntertwiningMap (trivial (k := k) (k[X]×k)),
      (∀ n,quotient.comp (s n)=IntertwiningMap.id _) ∧
      (∀ n,beta.comp (s (n+1))=s n) := by
  rintro ⟨s,hs,hb⟩
  apply no_coherent_polynomial_sections (k := k)
  exact ⟨fun n => (s n).toLinearMap,
    fun n => congrArg IntertwiningMap.toLinearMap (hs n),
    fun n => congrArg IntertwiningMap.toLinearMap (hb n)⟩

theorem polynomial_all_finite_prefixes (N : ℕ) :
    ∃ s : Fin (N+1) → (trivial (k := k) k).IntertwiningMap (trivial (k := k) (k[X]×k)),
      (∀ n,quotient.comp (s n)=IntertwiningMap.id _) ∧
      (∀ n : Fin N,beta.comp (s ⟨n+1,by omega⟩)=s ⟨n,by omega⟩) := by
  obtain ⟨x,hx,_⟩ := EventualTower.finite_prefix (X := fun _ => Sections (quotient (k := k)))
    nextSection N baseSection
  exact ⟨fun n => (x n).val,fun n => (x n).property,
    fun n => congrArg Subtype.val (hx n)⟩

def shearEquiv (v : k) : Representation.Equiv (trivial (k := k) (k×k)) (trivial (k := k) (k×k)) :=
  (equivariant (shear v).toLinearMap).ofBijective (shear v).bijective

def shearInclusion : (trivial (k := k) k).IntertwiningMap (trivial (k := k) (k×k)) :=
  equivariant (LinearMap.inl k k k)
def shearQuotient : (trivial (k := k) (k×k)).IntertwiningMap (trivial (k := k) k) :=
  equivariant (LinearMap.snd k k k)

theorem shear_exact_row : Function.Injective (shearInclusion (k := k)) ∧
    LinearMap.range (shearInclusion (k := k)).toLinearMap=LinearMap.ker (shearQuotient (k := k)).toLinearMap ∧
    Function.Surjective (shearQuotient (k := k)) := product_row

theorem shear_tower_isomorphism (v : k) :
    (shearEquiv v).toIntertwiningMap.comp shearInclusion=shearInclusion ∧
    shearQuotient.comp (shearEquiv v).toIntertwiningMap=shearQuotient ∧
    (IntertwiningMap.id (trivial (k := k) (k×k))).comp (shearEquiv v).toIntertwiningMap=
      (shearEquiv v).toIntertwiningMap.comp (IntertwiningMap.id (trivial (k := k) (k×k))) := by
  refine ⟨?_,?_,rfl⟩
  · apply IntertwiningMap.ext; exact shear_diagram v |>.1
  · apply IntertwiningMap.ext; exact shear_diagram v |>.2

theorem shear_finite_data : Finite Unit ∧ FiniteDimensional k k ∧ FiniteDimensional k (k×k) :=
  ⟨inferInstance,inferInstance,inferInstance⟩

/-- Every actual compatible family in the constant split identity tower is
moved by a legal automorphism of that whole tower. -/
theorem no_natural_preferred_family
    (s : ℕ → (trivial (k := k) k).IntertwiningMap (trivial (k := k) (k×k)))
    (hs : ∀ n,shearQuotient.comp (s n)=IntertwiningMap.id _) :
    ¬∀ n,(shearEquiv (1 : k)).toIntertwiningMap.comp (s n)=s n := by
  intro h
  exact no_shear_fixed_section (s 0).toLinearMap
    (congrArg IntertwiningMap.toLinearMap (hs 0))
    (congrArg IntertwiningMap.toLinearMap (h 0))

/-- The identity tower really has compatible sections. -/
theorem shear_family_exists :
    ∃ s : ℕ → (trivial (k := k) k).IntertwiningMap (trivial (k := k) (k×k)),
      (∀ n,shearQuotient.comp (s n)=IntertwiningMap.id _) ∧
      (∀ n,(IntertwiningMap.id (trivial (k := k) (k×k))).comp (s (n+1))=s n) :=
  ⟨fun _ => equivariant (LinearMap.inr k k k),fun _ => rfl,fun _ => rfl⟩

end MathGauge.GR007.TrivialTowers
