import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I,
§§2.1–2.2, https://glenzli.com/books/oet/, DOI 10.5281/zenodo.21457931.
Author ORCID: https://orcid.org/0009-0006-6536-3453.
Source: https://github.com/glenzli/oet-public, commit
539b40cec73184d98e06d54fbd10e4b4698bd6e7.
License: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
This file is a new Lean formalization of the selected definitions.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-- Matrices have output components as rows and input components as columns. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- `entry A i j` is the source's coefficient `A_{i → j}`, namely `A j i`. -/
def entry {I : Type} (A : ChannelMatrix I) (i j : I) : ENNReal := A j i

/-- The later step is the left factor in ordinary matrix multiplication. -/
noncomputable def matrixComp {I : Type} [Fintype I]
    (B A : ChannelMatrix I) : ChannelMatrix I :=
  B * A

@[simp] theorem entry_matrixComp {I : Type} [Fintype I]
    (B A : ChannelMatrix I) (i j : I) :
    entry (matrixComp B A) i j = ∑ k : I, entry B k j * entry A i k := by
  simp only [entry, matrixComp, Matrix.mul_apply]

/-- The restricted Lip condition includes the specified domain inclusion. -/
def IsRestrictedLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i : I, entry L i j * d i x y

/-- The full-domain Lip condition is the restricted condition on `dom φ`. -/
def IsLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (L : ChannelMatrix I) : Prop :=
  IsRestrictedLip d φ (dom φ) L

def restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) :=
  {L | IsRestrictedLip d φ U L}

def lipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (ChannelMatrix I) :=
  {L | IsLip d φ L}

/-- Restricted co-Lip matrices require a nonempty input set. -/
def IsRestrictedCoLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, entry K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) :=
  {K | IsRestrictedCoLip d φ U K}

/-- A component channel is the ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

def channel (I : Type) (i j : I) : ComponentChannel I := (i, j)

/-- Only input `i` may have a nonzero coefficient in output row `j`. -/
def SingleInputRow {I : Type} (A : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → entry A k j = 0

/-- A diagonal matrix has zero entries on all off-diagonal channels. -/
def IsDiagonal {I : Type} (A : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → entry A i j = 0

theorem diagonal_singleInputRow {I : Type} {A : ChannelMatrix I}
    (hA : IsDiagonal A) (j : I) : SingleInputRow A j j := by
  intro k hkj
  exact hA k j hkj

end LCH01
