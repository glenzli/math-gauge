import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §2.1, CC BY 4.0. https://glenzli.com/books/oet/
This file is a new formalization of the selected statements.
-/

noncomputable section

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-- Output index first, input index second. -/
abbrev Mat (I : Type) := Matrix I I ENNReal

def entry {I : Type} (A : Mat I) (i j : I) : ENNReal := A j i

variable {X I : Type} {bot : X} [Fintype I]

theorem entry_mul (B A : Mat I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k := rfl

def applyMatrix (A : Mat I) (v : I → ENNReal) (j : I) : ENNReal :=
  ∑ i, A j i * v i

theorem applyMatrix_mul (B A : Mat I) (v : I → ENNReal) (j : I) :
    applyMatrix (B * A) v j = applyMatrix B (applyMatrix A v) j := by
  simp only [applyMatrix, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

@[simp] theorem applyMatrix_one [DecidableEq I] (v : I → ENNReal) (j : I) :
    applyMatrix (1 : Mat I) v j = v j := by
  simp [applyMatrix, Matrix.one_apply, ite_mul]

theorem applyMatrix_mono (A : Mat I) {v w : I → ENNReal}
    (h : ∀ i, v i ≤ w i) (j : I) : applyMatrix A v j ≤ applyMatrix A w j := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) (A j i)

/-- The restricted domain condition is part of the predicate. -/
def LipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ applyMatrix L (fun i => d i x y) j

def Lip (d : I → X → X → ENNReal) (φ : Operator X bot) (L : Mat I) : Prop :=
  LipOn d φ (dom φ) L

def lipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {L | LipOn d φ U L}

def lipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {L | Lip d φ L}

/-- Nonemptiness is required whenever a co-Lip certificate is asserted. -/
def CoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    applyMatrix K (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)

def coLipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {K | CoLipOn d φ U K}

variable {d : I → X → X → ENNReal}
    {φ φ₁ φ₂ : Operator X bot} {U V : Set X} {A B : Mat I}

theorem lip_singleton [Unique I] (L : Mat I) :
    Lip d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d (default : I) (φ.func x) (φ.func y) ≤
        L default default * d default x y := by
  constructor
  · intro h x hx y hy
    simpa [applyMatrix] using h.2 x hx y hy default
  · intro h
    refine ⟨fun _ hx => hx, ?_⟩
    intro x hx y hy j
    have hj : j = default := Subsingleton.elim _ _
    subst j
    simpa [applyMatrix] using h x hx y hy

theorem lipOn_mono (hUV : U ⊆ V) (h : LipOn d φ V A) : LipOn d φ U A :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem lipFamilyOn_antitone (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    lipFamilyOn d φ V ⊆ lipFamilyOn d φ U :=
  fun _ h => lipOn_mono hUV h

theorem lip_restrict (hU : U ⊆ dom φ) : lipFamily d φ ⊆ lipFamilyOn d φ U :=
  fun _ h => lipOn_mono hU h

theorem coLipOn_mono (hne : U.Nonempty) (hUV : U ⊆ V)
    (h : CoLipOn d φ V A) : CoLipOn d φ U A :=
  ⟨hne, hUV.trans h.2.1, fun x hx y hy j => h.2.2 x (hUV hx) y (hUV hy) j⟩

theorem coLipFamilyOn_antitone (hne : U.Nonempty) (hUV : U ⊆ V)
    (_hV : V ⊆ dom φ) : coLipFamilyOn d φ V ⊆ coLipFamilyOn d φ U :=
  fun _ h => coLipOn_mono hne hUV h

theorem coLip_restrict (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipFamilyOn d φ (dom φ) ⊆ coLipFamilyOn d φ U :=
  fun _ h => coLipOn_mono hne hU h

theorem composition_domains (hU : U ⊆ dom (φ₂ * φ₁)) :
    U ⊆ dom φ₁ ∧ φ₁.func '' U ⊆ dom φ₂ := by
  constructor
  · intro x hx hbot
    apply hU hx
    change φ₂.func (φ₁.func x) = bot
    rw [hbot, φ₂.preserves_bot]
  · rintro z ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_comp (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : LipOn d φ₁ U A) (h₂ : LipOn d φ₂ (φ₁.func '' U) B) :
    LipOn d (φ₂ * φ₁) U (B * A) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) ≤ _
  rw [applyMatrix_mul]
  exact (h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j).trans
    (applyMatrix_mono B (fun k => h₁.2 x hx y hy k) j)

theorem coLip_comp (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : CoLipOn d φ₁ U A) (h₂ : CoLipOn d φ₂ (φ₁.func '' U) B) :
    CoLipOn d (φ₂ * φ₁) U (B * A) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  change _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y))
  rw [applyMatrix_mul]
  exact (applyMatrix_mono B (fun k => h₁.2.2 x hx y hy k) j).trans
    (h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)

theorem coLip_entry_zero (h : CoLipOn d φ (dom φ) A)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    entry A i j = 0 := by
  have hle : A j i * d i x y ≤ 0 := calc
    A j i * d i x y ≤ applyMatrix A (fun k => d k x y) j :=
      Finset.single_le_sum (f := fun k => A j k * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := h.2.2 x hx y hy j
    _ = 0 := hout
  exact (mul_eq_zero.mp (le_antisymm hle (zero_le _))).resolve_right (ne_of_gt hin)

theorem identity_lip [DecidableEq I] (hU : U ⊆ dom (1 : Operator X bot)) :
    LipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ applyMatrix (1 : Mat I) (fun i => d i x y) j
  rw [applyMatrix_one]

theorem identity_coLip [DecidableEq I] (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    CoLipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change applyMatrix (1 : Mat I) (fun i => d i x y) j ≤ d j x y
  rw [applyMatrix_one]

end LCH02
