import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-!
Formalization of the selected statements of OET, Volume I, Chapter 2.
Source: Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
https://glenzli.com/books/oet/, DOI 10.5281/zenodo.21457931, CC BY 4.0.
The mathematical content is from that source; this Lean formalization is new.
-/

namespace LCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

section Matrices

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Input `i`, output `j` is the entry in row `j`, column `i`. -/
def channel (M : BoundMatrix I) (i j : I) : ENNReal := M j i

omit [DecidableEq I] in
theorem channel_mul (M₂ M₁ : BoundMatrix I) (i j : I) :
    channel (M₂ * M₁) i j = ∑ k, channel M₂ k j * channel M₁ i k := rfl

/-- The list is in chronological order: the first matrix acts first. -/
def orderedProduct : List (BoundMatrix I) → BoundMatrix I
  | [] => 1
  | M :: Ms => orderedProduct Ms * M

theorem orderedProduct_eq_reverse_prod (Ms : List (BoundMatrix I)) :
    orderedProduct Ms = Ms.reverse.prod := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih => simp [orderedProduct, List.reverse_cons, ih]

@[simp] theorem orderedProduct_nil : orderedProduct ([] : List (BoundMatrix I)) = 1 := rfl

@[simp] theorem orderedProduct_singleton (M : BoundMatrix I) :
    orderedProduct [M] = M := by simp [orderedProduct]

omit [DecidableEq I] in
theorem matrix_action_mul (B A : BoundMatrix I) (v : I → ENNReal) (j : I) :
    (∑ k, B j k * ∑ i, A k i * v i) = ∑ i, (B * A) j i * v i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Matrices

section Bounds

variable {X I : Type} {bot : X} [Fintype I]
variable (d : I → X → X → ENNReal)

/-- Membership includes the stipulated restriction to the operator domain. -/
def IsRestrictedLip (φ : Operator X bot) (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

def IsLip (φ : Operator X bot) (L : BoundMatrix I) : Prop :=
  IsRestrictedLip d φ (dom φ) L

def lipFamily (φ : Operator X bot) : Set (BoundMatrix I) := {L | IsLip d φ L}

def restrictedLipFamily (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {L | IsRestrictedLip d φ U L}

/-- Nonemptiness is part of the predicate, not an implicit convention. -/
def IsRestrictedCoLip (φ : Operator X bot) (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K j i * d i x y) ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipFamily (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {K | IsRestrictedCoLip d φ U K}

theorem singleton_lip_iff [Unique I] (φ : Operator X bot) (L : BoundMatrix I) (j : I) :
    IsLip d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · intro h x hx y hy
    simpa [Finset.univ_unique, ← Unique.eq_default j] using h.2 x hx y hy j
  · intro h
    refine ⟨fun _ hx => hx, ?_⟩
    intro x hx y hy k
    have hk : k = j := Subsingleton.elim _ _
    subst k
    simpa [Finset.univ_unique, ← Unique.eq_default j] using h x hx y hy

theorem restrictedLipFamily_antitone (φ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) : restrictedLipFamily d φ V ⊆ restrictedLipFamily d φ U := by
  intro L hL
  exact ⟨fun _ hx => hL.1 (hUV hx), fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

theorem lipFamily_restrict (φ : Operator X bot) {U : Set X} (hU : U ⊆ dom φ) :
    lipFamily d φ ⊆ restrictedLipFamily d φ U :=
  restrictedLipFamily_antitone d φ hU

theorem restrictedCoLipFamily_antitone (φ : Operator X bot) {U V : Set X}
    (hne : U.Nonempty) (hUV : U ⊆ V) :
    restrictedCoLipFamily d φ V ⊆ restrictedCoLipFamily d φ U := by
  intro K hK
  exact ⟨hne, fun _ hx => hK.2.1 (hUV hx), fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

theorem coLipFamily_restrict (φ : Operator X bot) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    restrictedCoLipFamily d φ (dom φ) ⊆ restrictedCoLipFamily d φ U :=
  restrictedCoLipFamily_antitone d φ hne hU

theorem coLip_entry_eq_zero (φ : Operator X bot) (K : BoundMatrix I)
    (hK : IsRestrictedCoLip d φ (dom φ) K)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K j i = 0 := by
  have hterm : K j i * d i x y ≤ 0 := calc
    K j i * d i x y ≤ ∑ k, K j k * d k x y :=
      Finset.single_le_sum (f := fun k => K j k * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
    _ = 0 := hout
  have hz : K j i * d i x y = 0 := le_antisymm hterm (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

/-- The exact intermediate image lies in the second operator's domain. -/
theorem image_subset_dom_of_comp (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) : φ₁.func '' U ⊆ dom φ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU hx

theorem subset_dom_first_of_comp (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) : U ⊆ dom φ₁ := by
  intro x hx heq
  apply hU hx
  change φ₂.func (φ₁.func x) = bot
  rw [heq, φ₂.preserves_bot]

variable [DecidableEq I]

omit [DecidableEq I] in
theorem lip_comp (φ₁ φ₂ : Operator X bot) (U : Set X) (L₁ L₂ : BoundMatrix I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : IsRestrictedLip d φ₁ U L₁)
    (h₂ : IsRestrictedLip d φ₂ (φ₁.func '' U) L₂) :
    IsRestrictedLip d (φ₂ * φ₁) U (L₂ * L₁) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y)
        ≤ ∑ k, L₂ j k * d k (φ₁.func x) (φ₁.func y) :=
      h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, L₂ j k * ∑ i, L₁ k i * d i x y :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2 x hx y hy k) _
    _ = ∑ i, (L₂ * L₁) j i * d i x y := matrix_action_mul L₂ L₁ (fun i => d i x y) j

omit [DecidableEq I] in
theorem coLip_comp (φ₁ φ₂ : Operator X bot) (U : Set X) (K₁ K₂ : BoundMatrix I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : IsRestrictedCoLip d φ₁ U K₁)
    (h₂ : IsRestrictedCoLip d φ₂ (φ₁.func '' U) K₂) :
    IsRestrictedCoLip d (φ₂ * φ₁) U (K₂ * K₁) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  calc
    (∑ i, (K₂ * K₁) j i * d i x y)
        = ∑ k, K₂ j k * ∑ i, K₁ k i * d i x y :=
      (matrix_action_mul K₂ K₁ (fun i => d i x y) j).symm
    _ ≤ ∑ k, K₂ j k * d k (φ₁.func x) (φ₁.func y) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2.2 x hx y hy k) _
    _ ≤ d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y) :=
      h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem identity_lip (U : Set X) (hU : U ⊆ dom (1 : Operator X bot)) :
    IsRestrictedLip d (1 : Operator X bot) U (1 : BoundMatrix I) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i, (1 : BoundMatrix I) j i * d i x y
  simp [Matrix.one_apply]

theorem identity_coLip (U : Set X) (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsRestrictedCoLip d (1 : Operator X bot) U (1 : BoundMatrix I) := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, (1 : BoundMatrix I) j i * d i x y) ≤ d j x y
  simp [Matrix.one_apply]

end Bounds
end
end LCH02
