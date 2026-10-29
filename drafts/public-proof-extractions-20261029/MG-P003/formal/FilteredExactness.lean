import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Exact
import Mathlib.Tactic

/-!
Elementwise facts for Mathlib's genuine quotient direct limit of abelian groups.
In particular, exactness need only hold at arbitrarily fine stages. The input
systems are not asserted to come from presheaves with transfers.
-/

namespace MathGauge.PublicProof.Semilocal

noncomputable section

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A B C : ι → Type*}
variable [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
variable (f : ∀ i j, i ≤ j → A i →+ A j)
variable (g : ∀ i j, i ≤ j → B i →+ B j)
variable (h : ∀ i j, i ≤ j → C i →+ C j)
variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]
variable [DirectedSystem C (h · · ·)]

/-- The homomorphism induced by a natural family on the quotient direct limits. -/
def direct_limit_map (φ : ∀ i, A i →+ B i)
    (hφ : ∀ i j hij x, g i j hij (φ i x) = φ j (f i j hij x)) :
    DirectLimit A f →+ DirectLimit B g where
  toFun := DirectLimit.map f g (fun i => φ i) hφ
  map_zero' := by
    let i : ι := Classical.arbitrary ι
    rw [DirectLimit.zero_def (f := f) i, DirectLimit.map_def,
      map_zero, ← DirectLimit.zero_def]
  map_add' := by
    intro x y
    induction x, y using DirectLimit.induction₂ f with
    | ih i x y =>
      simp only [DirectLimit.add_def, DirectLimit.map_def, map_add]

@[simp]
theorem direct_limit_map_mk (φ : ∀ i, A i →+ B i)
    (hφ : ∀ i j hij x, g i j hij (φ i x) = φ j (f i j hij x)) (i : ι) (x : A i) :
    direct_limit_map f g φ hφ (⟦⟨i, x⟩⟧ : DirectLimit A f) =
      (⟦⟨i, φ i x⟩⟧ : DirectLimit B g) := rfl

/-- Filtered direct limits preserve componentwise injectivity. -/
theorem direct_limit_map_injective (φ : ∀ i, A i →+ B i)
    (hφ : ∀ i j hij x, g i j hij (φ i x) = φ j (f i j hij x))
    (hmono : ∀ i, Function.Injective (φ i)) :
    Function.Injective (direct_limit_map f g φ hφ) := by
  intro x y
  induction x, y using DirectLimit.induction₂ f with
  | ih i x y =>
    intro heq
    change (⟦⟨i, φ i x⟩⟧ : DirectLimit B g) = ⟦⟨i, φ i y⟩⟧ at heq
    obtain ⟨j, hij, hij', hxy⟩ := Quotient.eq.mp heq
    apply Quotient.sound
    refine ⟨j, hij, hij', hmono j ?_⟩
    simpa only [hφ] using hxy

/-- Componentwise surjectivity also survives the quotient direct limit. -/
theorem direct_limit_map_surjective (φ : ∀ i, A i →+ B i)
    (hφ : ∀ i j hij x, g i j hij (φ i x) = φ j (f i j hij x))
    (hepi : ∀ i, Function.Surjective (φ i)) :
    Function.Surjective (direct_limit_map f g φ hφ) := by
  intro y
  induction y using DirectLimit.induction g with
  | ih i y =>
    obtain ⟨x, rfl⟩ := hepi i y
    exact ⟨⟦⟨i, x⟩⟧, rfl⟩

/-- Exact stages are allowed to be a cofinal subset of the directed system.
No coherent choice of successful refinements is required. -/
theorem direct_limit_exact_of_cofinal_exact
    (φ : ∀ i, A i →+ B i) (ψ : ∀ i, B i →+ C i)
    (hφ : ∀ i j hij x, g i j hij (φ i x) = φ j (f i j hij x))
    (hψ : ∀ i j hij x, h i j hij (ψ i x) = ψ j (g i j hij x))
    (hexact : ∀ i, ∃ j, ∃ _hij : i ≤ j, Function.Exact (φ j) (ψ j)) :
    Function.Exact (direct_limit_map f g φ hφ) (direct_limit_map g h ψ hψ) := by
  intro y
  induction y using DirectLimit.induction g with
  | ih i y =>
    constructor
    · intro hy
      change (⟦⟨i, ψ i y⟩⟧ : DirectLimit C h) = 0 at hy
      obtain ⟨j, hij, hzero⟩ := (DirectLimit.exists_eq_zero (f := h) ⟨i, ψ i y⟩).mp hy
      obtain ⟨k, hjk, hk⟩ := hexact j
      have hzero' : ψ k (g j k hjk (g i j hij y)) = 0 := by
        rw [← hψ, ← hψ, hzero, map_zero]
      obtain ⟨x, hx⟩ := (hk _).mp hzero'
      refine ⟨⟦⟨k, x⟩⟧, ?_⟩
      rw [direct_limit_map_mk, hx]
      rw [DirectedSystem.map_map' g]
      exact (DirectLimit.eq_of_le (f := g) ⟨i, y⟩ k (hij.trans hjk)).symm
    · rintro ⟨x, hx⟩
      rw [← hx]
      induction x using DirectLimit.induction f with
      | ih l x =>
        change (⟦⟨l, ψ l (φ l x)⟩⟧ : DirectLimit C h) = 0
        obtain ⟨k, hlk, hk⟩ := hexact l
        apply (DirectLimit.exists_eq_zero (f := h) ⟨l, ψ l (φ l x)⟩).mpr
        refine ⟨k, hlk, ?_⟩
        rw [hψ, hφ]
        exact hk.apply_apply_eq_zero _

end

end MathGauge.PublicProof.Semilocal
