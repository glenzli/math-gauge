import Mathlib.Algebra.Exact
import Mathlib.Tactic

/-!
The final abelian-group argument from reference.md, explicitly as an auxiliary
lemma. It has no scheme, finite-correspondence or sheafification claim.
-/

namespace MathGauge.PublicProof.Semilocal

variable {A B C A' B' C' : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']

/-- In a commuting diagram of left-exact rows, a bijection in the middle and
an injection on the right yield a bijection on the left. The bottom row only
needs to be a complex with an injective first arrow; right surjectivity is unused. -/
theorem comparison_bijective
    (r : A →+ B) (d : B →+ C) (r' : A' →+ B') (d' : B' →+ C')
    (α : A →+ A') (β : B →+ B') (γ : C →+ C')
    (comm_left : r'.comp α = β.comp r) (comm_right : d'.comp β = γ.comp d)
    (hrow : Function.Exact r d) (hcomplex : d'.comp r' = 0)
    (hr : Function.Injective r) (hr' : Function.Injective r')
    (hβ : Function.Bijective β) (hγ : Function.Injective γ) :
    Function.Bijective α := by
  have left (x : A) : r' (α x) = β (r x) := DFunLike.congr_fun comm_left x
  have right (x : B) : d' (β x) = γ (d x) := DFunLike.congr_fun comm_right x
  constructor
  · intro a b hab
    apply hr
    apply hβ.1
    rw [← left, ← left, hab]
  · intro a'
    obtain ⟨b, hb⟩ := hβ.2 (r' a')
    have hdb : d b = 0 := by
      apply hγ
      rw [map_zero, ← right, hb]
      exact DFunLike.congr_fun hcomplex a'
    obtain ⟨a, ha⟩ := (hrow b).mp hdb
    refine ⟨a, hr' ?_⟩
    rw [left, ha, hb]

end MathGauge.PublicProof.Semilocal
