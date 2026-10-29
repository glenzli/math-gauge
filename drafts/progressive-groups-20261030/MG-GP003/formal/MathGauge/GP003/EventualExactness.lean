import FilteredExactness

/-! S6: the quantifier is per class, not a uniform exact stage. These results
use the genuine quotient direct limit; no target exactness is assumed. -/

namespace MathGauge.GP003
open MathGauge.PublicProof.Semilocal
noncomputable section

section General
variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A B C : ι → Type*}
variable [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
variable (f : ∀ i j, i ≤ j → A i →+ A j)
variable (g : ∀ i j, i ≤ j → B i →+ B j)
variable (h : ∀ i j, i ≤ j → C i →+ C j)
variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]
variable [DirectedSystem C (h · · ·)]

theorem direct_limit_exact_of_classes_eventually_zero
    (φ : ∀ i, A i →+ B i) (ψ : ∀ i, B i →+ C i)
    (hφ : ∀ i j hij x, g i j hij (φ i x) = φ j (f i j hij x))
    (hψ : ∀ i j hij x, h i j hij (ψ i x) = ψ j (g i j hij x))
    (hcomplex : ∀ i x, ψ i (φ i x) = 0)
    (hkill : ∀ i y, ψ i y = 0 → ∃ j, ∃ hij : i ≤ j,
      ∃ x, φ j x = g i j hij y) :
    Function.Exact (direct_limit_map f g φ hφ) (direct_limit_map g h ψ hψ) := by
  intro y
  induction y using DirectLimit.induction g with
  | ih i y =>
    constructor
    · intro hy
      change (⟦⟨i, ψ i y⟩⟧ : DirectLimit C h) = 0 at hy
      obtain ⟨j, hij, hz⟩ := (DirectLimit.exists_eq_zero (f := h) ⟨i, ψ i y⟩).mp hy
      have hz' : ψ j (g i j hij y) = 0 := by rw [← hψ, hz]
      obtain ⟨k, hjk, x, hx⟩ := hkill j (g i j hij y) hz'
      refine ⟨⟦⟨k, x⟩⟧, ?_⟩
      rw [direct_limit_map_mk, hx, DirectedSystem.map_map' g]
      exact (DirectLimit.eq_of_le (f := g) ⟨i, y⟩ k (hij.trans hjk)).symm
    · rintro ⟨x, hx⟩
      rw [← hx]
      induction x using DirectLimit.induction f with
      | ih j x =>
        rw [direct_limit_map_mk, direct_limit_map_mk, hcomplex,
          ← DirectLimit.zero_def]

theorem direct_limit_bijective_of_two_homology_groups_eventually_zero
    (φ : ∀ i, A i →+ B i)
    (hφ : ∀ i j hij x, g i j hij (φ i x) = φ j (f i j hij x))
    (hker : ∀ i x, φ i x = 0 → ∃ j, ∃ hij : i ≤ j, f i j hij x = 0)
    (hcoker : ∀ i y, ∃ j, ∃ hij : i ≤ j, ∃ x, φ j x = g i j hij y) :
    Function.Bijective (direct_limit_map f g φ hφ) := by
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    induction x using DirectLimit.induction f with
    | ih i x =>
      change (⟦⟨i, φ i x⟩⟧ : DirectLimit B g) = 0 at hx
      obtain ⟨j, hij, hz⟩ := (DirectLimit.exists_eq_zero (f := g) ⟨i, φ i x⟩).mp hx
      have hz' : φ j (f i j hij x) = 0 := by rw [← hφ, hz]
      obtain ⟨k, hjk, hk⟩ := hker j (f i j hij x) hz'
      apply (DirectLimit.exists_eq_zero (f := f) ⟨i, x⟩).mpr
      refine ⟨k, hij.trans hjk, ?_⟩
      rw [← DirectedSystem.map_map' f hij hjk]
      exact hk
  · intro y
    induction y using DirectLimit.induction g with
    | ih i y =>
      obtain ⟨j, hij, x, hx⟩ := hcoker i y
      refine ⟨⟦⟨j, x⟩⟧, ?_⟩
      rw [direct_limit_map_mk, hx]
      exact (DirectLimit.eq_of_le (f := g) ⟨i, y⟩ j hij).symm

end General

/-- The injective transition from stage i to j is multiplication by 2^(j-i). -/
def doublingTransition (i j : ℕ) (_hij : i ≤ j) : ℤ →+ ℤ where
  toFun x := (2 : ℤ) ^ (j - i) * x
  map_zero' := mul_zero _
  map_add' := mul_add _

instance doublingDirectedSystem :
    DirectedSystem (fun _ : ℕ => ℤ) (doublingTransition · · ·) where
  map_self i x := by simp [doublingTransition]
  map_map i j k hij hjk x := by
    dsimp [doublingTransition]
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega

def doubleInteger : ℤ →+ ℤ where
  toFun x := 2 * x
  map_zero' := mul_zero _
  map_add' := mul_add _

theorem doubleInteger_injective : Function.Injective doubleInteger := by
  intro x y hxy
  change 2 * x = 2 * y at hxy
  omega

theorem doubleInteger_not_surjective : ¬ Function.Surjective doubleInteger := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  change 2 * x = 1 at hx
  omega

theorem doubling_chainMap (i j : ℕ) (hij : i ≤ j) (x : ℤ) :
    doublingTransition i j hij (doubleInteger x) =
      doubleInteger (doublingTransition i j hij x) := by
  dsimp [doublingTransition, doubleInteger]
  ring

abbrev DoublingLimit := DirectLimit (fun _ : ℕ => ℤ) doublingTransition

def doubleLimit : DoublingLimit →+ DoublingLimit :=
  direct_limit_map doublingTransition doublingTransition
    (fun _ => doubleInteger) doubling_chainMap

theorem doubleLimit_bijective : Function.Bijective doubleLimit := by
  apply direct_limit_bijective_of_two_homology_groups_eventually_zero
  · intro i x hx
    have hx0 : x = 0 := doubleInteger_injective (by simpa using hx)
    exact ⟨i, le_rfl, by simp [hx0]⟩
  · intro i y
    refine ⟨i + 1, Nat.le_succ i, y, ?_⟩
    simp [doublingTransition, doubleInteger]

/-- Every term of the two-term complex is ℤ, the differential is ×2, and
the transition maps are injective chain maps. The colimit differential is an
isomorphism, while no stage differential is surjective, even eventually. -/
theorem exact_limit_not_eventual_exact_stage :
    Function.Bijective doubleLimit ∧
    (∀ i j (hij : i ≤ j), Function.Injective (doublingTransition i j hij)) ∧
    ¬ (∃ n : ℕ, ∀ i ≥ n, Function.Surjective (fun x : ℤ => doubleInteger x)) := by
  refine ⟨doubleLimit_bijective, ?_, ?_⟩
  · intro i j hij x y hxy
    change (2 : ℤ) ^ (j - i) * x = 2 ^ (j - i) * y at hxy
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hxy
  · rintro ⟨n, hn⟩
    exact doubleInteger_not_surjective (hn n le_rfl)

end
end MathGauge.GP003
