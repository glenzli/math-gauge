import Mathlib.Data.Matrix.Mul
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
Formalization of the eight LCH01 obligations from Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, Volume I, v1.0.0, Chapter 2.
Author ORCID: https://orcid.org/0009-0006-6536-3453
Source DOI: https://doi.org/10.5281/zenodo.21457931
Official work: https://glenzli.com/books/oet/
Current source repository: https://gitlab.com/glenzli/oet-public
Source snapshot: https://github.com/glenzli/oet-public
at commit 539b40cec73184d98e06d54fbd10e4b4698bd6e7.
License: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/
The Lean declarations in LCH01 are a new formalization of the cited text.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- CH02-D03: rows are output indices; columns are input indices. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- The source's `M_{i → j}` is the usual matrix entry `M j i`. -/
def entry (M : ChannelMatrix I) (i j : I) : ENNReal := M j i

/-- Standard matrix multiplication in the source's input/output notation. -/
theorem entry_mul [Fintype I] (M₂ M₁ : ChannelMatrix I) (i j : I) :
    entry (M₂ * M₁) i j = ∑ k : I, entry M₂ k j * entry M₁ i k := by
  rfl

/-- The finite weighted sum for one output row. -/
noncomputable def rowSum [Fintype I] (M : ChannelMatrix I) (j : I) (v : I → ENNReal) :
    ENNReal := ∑ i : I, entry M i j * v i

/-- CH02-D01: a restricted Lip matrix includes its domain condition. -/
def IsRestrictedLipMatrix [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ rowSum L j (fun i => d i x y)

/-- A global Lip matrix is a restricted one on the full operator domain. -/
def IsLipMatrix [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : ChannelMatrix I) : Prop :=
  IsRestrictedLipMatrix d φ (dom φ) L

/-- The global definition has precisely the source's pointwise quantifiers. -/
theorem isLipMatrix_iff [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : ChannelMatrix I) :
    IsLipMatrix d φ L ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
        d j (φ.func x) (φ.func y) ≤ rowSum L j (fun i => d i x y) := by
  simp [IsLipMatrix, IsRestrictedLipMatrix]

/-- The source's `𝓛(φ)`. -/
def lipMatrices [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) : Set (ChannelMatrix I) :=
  {L | IsLipMatrix d φ L}

/-- The source's `𝓛(φ)|_U`. -/
def restrictedLipMatrices [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {L | IsRestrictedLipMatrix d φ U L}

/-- CH02-D02: nonemptiness is part of the co-Lip predicate. -/
def IsRestrictedCoLipMatrix [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      rowSum K j (fun i => d i x y) ≤ d j (φ.func x) (φ.func y)

/-- The source's `𝓚(φ)|_U`, with nonemptiness required of every member. -/
def restrictedCoLipMatrices [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {K | IsRestrictedCoLipMatrix d φ U K}

/-- CH02-D07: a component channel is an ordered (input, output) pair. -/
abbrev ComponentChannel (I : Type) := I × I

/-- Only input `i` may contribute to output row `j`; its entry may also be zero. -/
def SingleInputRow (M : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → entry M k j = 0

/-- A diagonal matrix has no off-diagonal input contributions. -/
def IsDiagonal (M : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → entry M i j = 0

theorem isDiagonal_iff_singleInputRows (M : ChannelMatrix I) :
    IsDiagonal M ↔ ∀ j : I, SingleInputRow M j j := by
  constructor
  · intro h j k hkj
    exact h k j hkj
  · intro h i j hij
    exact h j i hij

end LCH01
