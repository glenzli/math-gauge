import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Source: Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §§2.1–2.2, v1.0.0, DOI 10.5281/zenodo.21457931.
ORCID: https://orcid.org/0009-0006-6536-3453
Official work: https://glenzli.com/books/oet/
Source repository: https://gitlab.com/glenzli/oet-public
License: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/
This is a new Lean formalization of the supplied mathematical text.
The supplied foundation modules are imported without modification.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-- Rows are outputs and columns are inputs; entries may be infinite. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- `entry M i j` denotes the textbook coefficient `M_{i → j}`. -/
def entry {I : Type} (M : ChannelMatrix I) (i j : I) : ENNReal := M j i

/-- `M₂` acts after `M₁`, using ordinary matrix multiplication. -/
noncomputable def matrix_comp {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) : ChannelMatrix I := M₂ * M₁

theorem matrix_comp_entry {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) (i j : I) :
    entry (matrix_comp M₂ M₁) i j =
      ∑ k : I, entry M₂ k j * entry M₁ i k := by
  rfl

/-- A component channel is the ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

/-- Output row `j` has no input contribution except possibly input `i`. -/
def SingleInputRow {I : Type} (M : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → entry M k j = 0

/-- All off-diagonal input/output coefficients vanish. -/
def Diagonal {I : Type} (M : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → entry M i j = 0

theorem diagonal_singleInputRow {I : Type} {M : ChannelMatrix I}
    (hM : Diagonal M) (j : I) : SingleInputRow M j j := by
  intro k hk
  exact hM k j hk

section Certificates

variable {X I : Type} [Fintype I] {bot : X}

/-- The restricted Lip predicate includes the required domain inclusion. -/
def IsRestrictedLip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i : I, entry L i j * d i x y

/-- The full Lip predicate evaluates every pair in the operator domain. -/
def IsLip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  IsRestrictedLip d φ (dom φ) L

def lipCertificates (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (ChannelMatrix I) := {L | IsLip d φ L}

def restrictedLipCertificates (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {L | IsRestrictedLip d φ U L}

/-- Nonemptiness is part of every restricted co-Lip certificate. -/
def IsRestrictedCoLip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, entry K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipCertificates (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {K | IsRestrictedCoLip d φ U K}

end Certificates

end LCH01
