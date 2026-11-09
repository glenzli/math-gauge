import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Formalization of the selected definitions in Chapter 2 of
Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I.
Source: https://glenzli.com/books/oet/ ; CC BY 4.0.
This file is a new Lean formalization, not an author-supplied implementation.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-- The background gauge axioms, using the frozen prerequisite definition. -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X bot (d i)

/-- Rows are output components; columns are input components. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- The textbook entry `M_{i → j}` is the ordinary matrix entry `M j i`. -/
def entry {I : Type} (M : ChannelMatrix I) (i j : I) : ENNReal := M j i

/-- The second step acts after the first step. -/
noncomputable def matrixComp {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) : ChannelMatrix I := M₂ * M₁

theorem entry_matrixComp {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) (i j : I) :
    entry (matrixComp M₂ M₁) i j =
      ∑ k, entry M₂ k j * entry M₁ i k := by
  exact Matrix.mul_apply

/-- A component channel is an ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

def channelCoefficient {I : Type}
    (M : ChannelMatrix I) (c : ComponentChannel I) : ENNReal :=
  entry M c.1 c.2

/-- Output row `j` may use only input `i`; that entry may itself be zero. -/
def RowSupported {I : Type} (M : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k, k ≠ i → entry M k j = 0

/-- Each output row uses only the input with the same index. -/
def IsDiagonal {I : Type} (M : ChannelMatrix I) : Prop :=
  ∀ j, RowSupported M j j

section Bounds

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

/-- Restricted Lip legality includes the specified domain containment. -/
def LipOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      G.d j (φ.func x) (φ.func y) ≤ ∑ i, entry L i j * G.d i x y

def Lip (G : Gauge X I bot) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  LipOn G φ (dom φ) L

def lipMatricesOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  {L | LipOn G φ U L}

def lipMatrices (G : Gauge X I bot) (φ : Operator X bot) :
    Set (ChannelMatrix I) :=
  {L | Lip G φ L}

/-- Nonemptiness is part of co-Lip legality, including for the full domain. -/
def CoLipOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      (∑ i, entry K i j * G.d i x y) ≤ G.d j (φ.func x) (φ.func y)

def coLipMatricesOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  {K | CoLipOn G φ U K}

/-- The scalar inequality associated with one input/output channel. -/
def ChannelLipOn (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (i j : I) (l : ENNReal) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U,
      G.d j (φ.func x) (φ.func y) ≤ l * G.d i x y

end Bounds

end LCH01
