import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §2.1, https://glenzli.com/books/oet/, CC BY 4.0.
ORCID: https://orcid.org/0009-0006-6536-3453.
This file is a new Lean formalization of the selected obligations.
-/

namespace LCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

variable {X I : Type} {bot : X} [Fintype I]

/-- The arrow i → j is stored in row j, column i. -/
def channel (M : BoundMatrix I) (i j : I) : ENNReal := M j i

theorem channel_mul (B A : BoundMatrix I) (i j : I) :
    channel (B * A) i j = ∑ k, channel B k j * channel A i k := rfl

/-- Chronological input order: [M₁,...,Mₙ] has product Mₙ ⋯ M₁. -/
def matrixProduct [DecidableEq I] (Ms : List (BoundMatrix I)) : BoundMatrix I := Ms.reverse.prod

@[simp] theorem matrixProduct_nil [DecidableEq I] :
    matrixProduct ([] : List (BoundMatrix I)) = 1 := rfl

@[simp] theorem matrixProduct_cons [DecidableEq I] (M : BoundMatrix I)
    (Ms : List (BoundMatrix I)) :
    matrixProduct (M :: Ms) = matrixProduct Ms * M := by
  simp [matrixProduct, List.reverse_cons, List.prod_append]

@[simp] theorem matrixProduct_singleton [DecidableEq I] (M : BoundMatrix I) :
    matrixProduct [M] = M := by simp

def LipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

def lipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) := {L | LipOn d φ U L}

def lipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (BoundMatrix I) := lipMatricesOn d φ (dom φ)

def CoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K j i * d i x y) ≤ d j (φ.func x) (φ.func y)

def coLipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) := {K | CoLipOn d φ U K}

theorem lip_single_component [Unique I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (L : BoundMatrix I) (i : I) :
    LipOn d φ U L ↔ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hs (f : I → ENNReal) : ∑ k, f k = f i := by
    simpa only [Subsingleton.elim (default : I) i] using Fintype.sum_unique f
  constructor
  · rintro ⟨hU, hL⟩
    exact ⟨hU, fun x hx y hy => by simpa only [hs] using hL x hx y hy i⟩
  · rintro ⟨hU, hL⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy j
    simpa only [hs, Subsingleton.elim j i] using hL x hx y hy

theorem global_lip_single_component [Unique I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : BoundMatrix I) (i : I) :
    L ∈ lipMatrices d φ ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  change LipOn d φ (dom φ) L ↔ _
  simpa using lip_single_component d φ (dom φ) L i

theorem lip_antitone (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) :
    lipMatricesOn d φ V ⊆ lipMatricesOn d φ U := by
  rintro L ⟨hV, hL⟩
  exact ⟨hUV.trans hV, fun x hx y hy j => hL x (hUV hx) y (hUV hy) j⟩

theorem lip_restrict (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U : Set X} (hU : U ⊆ dom φ) :
    lipMatrices d φ ⊆ lipMatricesOn d φ U := lip_antitone d φ hU

theorem coLip_antitone (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U V : Set X} (hU : U.Nonempty) (hUV : U ⊆ V) :
    coLipMatricesOn d φ V ⊆ coLipMatricesOn d φ U := by
  rintro K ⟨_, hV, hK⟩
  exact ⟨hU, hUV.trans hV, fun x hx y hy j => hK x (hUV hx) y (hUV hy) j⟩

theorem coLip_restrict (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U : Set X} (hU : U.Nonempty) (hdom : U ⊆ dom φ) :
    coLipMatricesOn d φ (dom φ) ⊆ coLipMatricesOn d φ U :=
  coLip_antitone d φ hU hdom

theorem composition_domains (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) :
    U ⊆ dom φ₁ ∧ operator_image φ₁ U ⊆ dom φ₂ := by
  constructor
  · intro x hx heq
    apply hU hx
    change φ₂.func (φ₁.func x) = bot
    rw [heq, φ₂.preserves_bot]
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

theorem matrix_action_mul (B A : BoundMatrix I) (v : I → ENNReal) (j : I) :
    (∑ i, (B * A) j i * v i) = ∑ k, B j k * (∑ i, A k i * v i) := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lip_comp (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    {U : Set X} {L₁ L₂ : BoundMatrix I} (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : LipOn d φ₁ U L₁) (h₂ : LipOn d φ₂ (operator_image φ₁ U) L₂) :
    LipOn d (φ₂ * φ₁) U (L₂ * L₁) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) ≤ _
  calc
    _ ≤ ∑ k, L₂ j k * d k (φ₁.func x) (φ₁.func y) :=
      h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, L₂ j k * (∑ i, L₁ k i * d i x y) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2 x hx y hy k) _
    _ = _ := (matrix_action_mul L₂ L₁ (fun i => d i x y) j).symm

theorem coLip_comp (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    {U : Set X} {K₁ K₂ : BoundMatrix I} (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : CoLipOn d φ₁ U K₁) (h₂ : CoLipOn d φ₂ (operator_image φ₁ U) K₂) :
    CoLipOn d (φ₂ * φ₁) U (K₂ * K₁) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  change _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y))
  calc
    _ = ∑ k, K₂ j k * (∑ i, K₁ k i * d i x y) :=
      matrix_action_mul K₂ K₁ (fun i => d i x y) j
    _ ≤ ∑ k, K₂ j k * d k (φ₁.func x) (φ₁.func y) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2.2 x hx y hy k) _
    _ ≤ _ := h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem coLip_entry_zero (d : I → X → X → ENNReal) (φ : Operator X bot)
    {K : BoundMatrix I} (hK : CoLipOn d φ (dom φ) K)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K j i = 0 := by
  have hterm : K j i * d i x y ≤ 0 := calc
    _ ≤ ∑ k, K j k * d k x y := Finset.single_le_sum (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
    _ = 0 := hout
  exact (mul_eq_zero.mp (le_antisymm hterm (zero_le _))).resolve_right (ne_of_gt hin)

theorem identity_lip [DecidableEq I] (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (1 : Operator X bot)) : LipOn d (1 : Operator X bot) U 1 := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i, (1 : BoundMatrix I) j i * d i x y
  simp [Matrix.one_apply]

theorem identity_coLip [DecidableEq I] (d : I → X → X → ENNReal) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X bot)) :
    CoLipOn d (1 : Operator X bot) U 1 := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, (1 : BoundMatrix I) j i * d i x y) ≤ d j x y
  simp [Matrix.one_apply]

end
end LCH02
