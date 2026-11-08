# LCH01 formalization

All eight selected obligations are complete. The entrypoint is `Main.lean`; it imports the complete target module `Channels.lean` and prints the proof axiom dependencies. Both files were checked with the supplied Lean 4.29.1 environment and pinned Mathlib. The printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

Attribution: Zhe Li (Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution Theory*, Volume I, v1.0.0, https://glenzli.com/books/oet/, DOI https://doi.org/10.5281/zenodo.21457931. Original mathematical content is licensed under CC BY 4.0 (https://creativecommons.org/licenses/by/4.0/). The Lean code below is a new formalization of the selected statements, not the author's implementation. The supplied frozen prerequisites are imported unchanged.

Representation: `Gauge` bundles only the original component distances and frozen extended-pseudometric assumptions. `entry M i j = M j i` implements the input/output convention. Restricted legality explicitly includes domain containment, and co-Lip legality also includes nonemptiness. No separation assumption or matrix extremum is introduced. Pure matrix definitions also make sense without a nonempty index set; the mathematical theorem context retains the chapter's finite nonempty setting.

Build in the supplied workspace, first compiling the unchanged `gauge_space.lean` and `operator_space.lean` to their corresponding `.olean` files using `./lean-local -o`, then run `./lean-local -o Channels.olean Channels.lean` and `./lean-local -o Main.olean Main.lean`. The harmless unused-section-variable warnings record that several algebraic facts do not need nonemptiness.

```lean filename=Channels.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-!
Formalization of the selected channel statements in Chapter 2 of
Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I.
Source: https://doi.org/10.5281/zenodo.21457931, CC BY 4.0.
This file is a new formalization, not the author's Lean implementation.
-/
noncomputable section

namespace LCH01

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-- A finite nonempty family is imposed by the section's instances below.
Each component retains all frozen extended-pseudometric axioms. -/
structure Gauge (X I : Type) (bot : X) where
  dist : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X bot (dist i)

/-- Ordinary matrix layout: output index first, input index second. -/
abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

/-- The entry denoted `M_{i → j}` in the chapter. -/
def entry {I : Type} (M : BoundMatrix I) (i j : I) : ENNReal := M j i

/-- A component channel is an ordered (input, output) pair. -/
abbrev Channel (I : Type) := I × I

def channel {I : Type} (i j : I) : Channel I := (i, j)

/-- All entries of output row `j` other than input `i` vanish.
The surviving entry is allowed to be zero too. -/
def SingleInputRow {I : Type} (M : BoundMatrix I) (i j : I) : Prop :=
  ∀ k, k ≠ i → entry M k j = 0

/-- Every output row retains only its same-component input. -/
def Diagonal {I : Type} (M : BoundMatrix I) : Prop :=
  ∀ j, SingleInputRow M j j

section Finite
variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

/-- Algebraic matrix multiplication, with the later bound on the left. -/
def boundMul (M₂ M₁ : BoundMatrix I) : BoundMatrix I := M₂ * M₁

theorem boundMul_entry (M₂ M₁ : BoundMatrix I) (i j : I) :
    entry (boundMul M₂ M₁) i j =
      ∑ k : I, entry M₂ k j * entry M₁ i k := rfl

/-- The finite sum bounding output component `j`. -/
def bound (G : Gauge X I bot) (M : BoundMatrix I) (x y : X) (j : I) : ENNReal :=
  ∑ i : I, entry M i j * G.dist i x y

/-- Legal restricted Lip matrix: domain admissibility and all point pairs. -/
def RestrictedLip (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    G.dist j (φ.func x) (φ.func y) ≤ bound G L x y j

/-- Global Lip condition is the restricted condition on the whole domain. -/
def Lip (G : Gauge X I bot) (φ : Operator X bot) (L : BoundMatrix I) : Prop :=
  RestrictedLip G φ (dom φ) L

def lipFamily (G : Gauge X I bot) (φ : Operator X bot) : Set (BoundMatrix I) :=
  {L | Lip G φ L}

def restrictedLipFamily (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) := {L | RestrictedLip G φ U L}

theorem lip_iff (G : Gauge X I bot) (φ : Operator X bot) (L : BoundMatrix I) :
    Lip G φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j,
      G.dist j (φ.func x) (φ.func y) ≤ bound G L x y j := by
  exact and_iff_right (Set.Subset.refl _)

/-- Nonemptiness is part of legality, not an optional theorem assumption. -/
def RestrictedCoLip (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    bound G K x y j ≤ G.dist j (φ.func x) (φ.func y)

def restrictedCoLipFamily (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) := {K | RestrictedCoLip G φ U K}

theorem coLip_nonempty (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) (hK : K ∈ restrictedCoLipFamily G φ U) :
    U.Nonempty := hK.1

/-- The sum in a single-input output row is precisely its surviving term. -/
theorem singleInput_bound (G : Gauge X I bot) (L : BoundMatrix I)
    (i j : I) (hrow : SingleInputRow L i j) (x y : X) :
    bound G L x y j = entry L i j * G.dist i x y := by
  classical
  unfold bound
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · simp

/-- CH02-P19: sparse row gives a scalar upper estimate on every pair in U. -/
theorem singleInput_lip (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) (hL : L ∈ restrictedLipFamily G φ U)
    (i j : I) (hrow : SingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      G.dist j (φ.func x) (φ.func y) ≤ entry L i j * G.dist i x y := by
  intro x hx y hy
  simpa only [singleInput_bound G L i j hrow x y] using hL.2 x hx y hy j

/-- CH02-P19, diagonal specialization, for every output component. -/
theorem diagonal_lip (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) (hL : L ∈ restrictedLipFamily G φ U)
    (hdiag : Diagonal L) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U,
      G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y := by
  intro j
  exact singleInput_lip G φ U L hL j j (hdiag j)

/-- A single nonnegative summand lies below a legal co-Lip output distance. -/
theorem coLip_term_le (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) (hK : K ∈ restrictedCoLipFamily G φ U)
    (i j : I) (x : X) (hx : x ∈ U) (y : X) (hy : y ∈ U) :
    entry K i j * G.dist i x y ≤ G.dist j (φ.func x) (φ.func y) := by
  have hterm : entry K i j * G.dist i x y ≤ bound G K x y j := by
    unfold bound
    exact Finset.single_le_sum (fun k _ => zero_le (entry K k j * G.dist k x y)) (Finset.mem_univ i)
  exact hterm.trans (hK.2.2 x hx y hy j)

/-- CH02-P20: a strictly positive co-Lip channel preserves positive distance. -/
theorem positive_channel (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) (hK : K ∈ restrictedCoLipFamily G φ U)
    (i j : I) (hpos : 0 < entry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < G.dist i x y →
      0 < G.dist j (φ.func x) (φ.func y) := by
  intro x hx y hy hxy
  exact lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hxy.ne') (coLip_term_le G φ U K hK i j x hx y hy)

/-- CH02-P21: reflect the family zero-distance relation, not point equality. -/
theorem reflect_gaugeZero (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) (hK : K ∈ restrictedCoLipFamily G φ U)
    (hdiag : ∀ j, 0 < entry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated G.dist (φ.func x) (φ.func y) → GaugeZeroRelated G.dist x y := by
  intro x hx y hy hzero j
  by_contra hn
  have hp : 0 < G.dist j x y := bot_lt_iff_ne_bot.mpr hn
  have hout := positive_channel G φ U K hK j j (hdiag j) x hx y hy hp
  rw [hzero j] at hout
  exact (lt_irrefl 0) hout

/-- CH02-P25: Exercise 2.2, without requiring any sparsity of K. -/
theorem scalar_two_sided (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L K : BoundMatrix I)
    (hL : L ∈ restrictedLipFamily G φ U) (hK : K ∈ restrictedCoLipFamily G φ U)
    (j : I) (hrow : SingleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
      G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y := by
  intro x hx y hy
  exact ⟨coLip_term_le G φ U K hK j j x hx y hy,
    singleInput_lip G φ U L hL j j hrow x hx y hy⟩

end Finite
end LCH01
```

```lean filename=Main.lean
import Channels

#print axioms LCH01.boundMul_entry
#print axioms LCH01.lip_iff
#print axioms LCH01.coLip_nonempty
#print axioms LCH01.singleInput_bound
#print axioms LCH01.singleInput_lip
#print axioms LCH01.diagonal_lip
#print axioms LCH01.coLip_term_le
#print axioms LCH01.positive_channel
#print axioms LCH01.reflect_gaugeZero
#print axioms LCH01.scalar_two_sided
```

```json filename=alignment.json
{
  "case_id": "LCH01",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.RestrictedLip"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.Lip"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.lipFamily"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.restrictedLipFamily"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.lip_iff"
        }
      ],
      "representation": {
        "objects": "G.dist is the original gauge family; φ is the frozen Operator X bot. Matrices have ENNReal entries, including infinity.",
        "parameters": "X and I are types, bot is distinguished, G.metric supplies the frozen extended-pseudometric assumptions. Fintype I provides the finite sum; theorem context retains Nonempty I.",
        "quantifiers": "RestrictedLip includes U ⊆ dom φ and the inequality for every x ∈ U, y ∈ U, j ∈ I. No nonemptiness is imposed on a Lip domain.",
        "conclusion": "Lip evaluates RestrictedLip on dom φ. lip_iff shows exactly the full-domain inequality; the two families are sets defined by these predicates, without extremal matrices."
      },
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.RestrictedCoLip"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.restrictedCoLipFamily"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.coLip_nonempty"
        }
      ],
      "representation": {
        "objects": "The co-Lip family is the set of matrices K satisfying RestrictedCoLip.",
        "parameters": "The same G, φ, U and extended nonnegative matrices as for Lip.",
        "quantifiers": "Legality is the conjunction U.Nonempty, U ⊆ dom φ, and the lower inequality for all x ∈ U, y ∈ U and all output indices j.",
        "conclusion": "The sum is bounded above by the output distance. Nonemptiness is mandatory, even when the pointwise inequality would be vacuous. coLip_nonempty extracts it from family membership."
      },
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.BoundMatrix"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.entry"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.boundMul"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.boundMul_entry"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.bound"
        }
      ],
      "representation": {
        "objects": "BoundMatrix I is Mathlib Matrix I I ENNReal.",
        "parameters": "entry M i j = M j i: the first matrix coordinate is output (row), the second input (column).",
        "quantifiers": "boundMul_entry holds for every pair of matrices and every i,j in the finite index type.",
        "conclusion": "boundMul M₂ M₁ is ordinary M₂ * M₁, with entry ∑ k, entry M₂ k j * entry M₁ i k. bound is ∑ i, entry M i j * G.dist i x y. ENNReal arithmetic has zero times infinity equal to zero."
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.Channel"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.channel"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.SingleInputRow"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.Diagonal"
        }
      ],
      "representation": {
        "objects": "Channel I is the ordered pair type I × I; channel i j is the input-output pair (i,j).",
        "parameters": "SingleInputRow M i j concerns output row j and the sole possibly nonzero input i.",
        "quantifiers": "It requires entry M k j = 0 for all k ≠ i. Diagonal requires this with i=j for every j.",
        "conclusion": "These definitions impose no unnecessary positivity on the surviving entry. They match the single-input and diagonal cases in section 2.2."
      },
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.singleInput_bound"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.singleInput_lip"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.diagonal_lip"
        }
      ],
      "representation": {
        "objects": "A selected restricted Lip certificate L and a single-input output row.",
        "parameters": "The legal domain and all original gauge assumptions are retained.",
        "quantifiers": "For all x,y ∈ U and for the chosen i,j; diagonal_lip universally quantifies j as well.",
        "conclusion": "singleInput_bound proves exact equality of the finite sum to L_{i→j} d_i(x,y). singleInput_lip gives the scalar upper bound; diagonal_lip specializes it simultaneously to each same-component channel."
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D07"
      ]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.coLip_term_le"
        },
        {
          "file": "Channels.lean",
          "name": "LCH01.positive_channel"
        }
      ],
      "representation": {
        "objects": "K is a member of the nonempty-domain restricted co-Lip family.",
        "parameters": "The selected channel (i,j) has 0 < entry K i j; infinite positive entries remain allowed.",
        "quantifiers": "For every x,y ∈ U, positive input distance implies positive output distance.",
        "conclusion": "coLip_term_le bounds the single channel term by the output distance. positive_channel uses positivity of the ENNReal product, with no finiteness assumption."
      },
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.reflect_gaugeZero"
        }
      ],
      "representation": {
        "objects": "The frozen GaugeZeroRelated relation, defined by all component distances being zero.",
        "parameters": "A legal restricted co-Lip K with positive diagonal entries for every j.",
        "quantifiers": "For all x,y ∈ U, GaugeZeroRelated G.dist (φ.func x) (φ.func y) implies GaugeZeroRelated G.dist x y.",
        "conclusion": "The conclusion is precisely reflection of family zero distance. No separation or point-equality conclusion is assumed or asserted."
      },
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-P20"
      ]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {
          "file": "Channels.lean",
          "name": "LCH01.scalar_two_sided"
        }
      ],
      "representation": {
        "objects": "Restricted Lip L and co-Lip K certificates for the same operator and same U.",
        "parameters": "Only output row j of L is required to vanish off the diagonal. There is no sparsity condition on K.",
        "quantifiers": "For every x,y ∈ U. Nonemptiness follows from co-Lip membership.",
        "conclusion": "The conjunction K_{j→j} d_j(x,y) ≤ d_j(φ(x),φ(y)) and d_j(φ(x),φ(y)) ≤ L_{j→j} d_j(x,y) is the requested scalar two-sided bound."
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D02",
        "CH02-D03",
        "CH02-D07",
        "CH02-P19"
      ]
    }
  ]
}
```
