import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

namespace formal_oet.ch_02_operator_bounds

/-- A matrix of extended nonnegative entries indexed by the gauge components.

Following the book, the first index is the input component and the second index is the
output component.  Thus `L i j` is the entry denoted `L_{i → j}` in the source; in
displayed matrix form it lies in output-row `j` and input-column `i`. -/
abbrev GaugeMatrix (I : Type) := I → I → ENNReal

/-- The entry `L_{i → j}`: input component `i` and output component `j`. -/
def matrixEntry {I : Type} (L : GaugeMatrix I) (i j : I) : ENNReal :=
  L i j

/-- The output row `j`: all input-to-output coefficients whose output component is `j`. -/
def outputRow {I : Type} (L : GaugeMatrix I) (j : I) : I → ENNReal :=
  fun i => L i j

/-- The input column `i`: all coefficients leaving input component `i`. -/
def inputColumn {I : Type} (L : GaugeMatrix I) (i : I) : I → ENNReal :=
  fun j => L i j

/-- CH02-D03. Matrix multiplication in the source's row/column convention.

If `M₂` maps intermediate components to final components and `M₁` maps initial
components to intermediate components, then `matrixMul M₂ M₁` is the matrix of the
composite map.  Its `(i,j)` entry is
`∑ k, M₂ k j * M₁ i k`, exactly `(M₂ · M₁)_{i → j}` from the text. -/
noncomputable def matrixMul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) : GaugeMatrix I :=
  fun i j => ∑ k, M₂ k j * M₁ i k

@[simp] theorem matrixMul_apply {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    matrixMul M₂ M₁ i j = ∑ k, M₂ k j * M₁ i k := rfl

/-- The `(i,j)` entry of the composite matrix, read with input index `i` and output
index `j`. -/
theorem matrixEntry_matrixMul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    matrixEntry (matrixMul M₂ M₁) i j = ∑ k, M₂ k j * M₁ i k := rfl

@[simp] theorem matrixEntry_apply {I : Type} (L : GaugeMatrix I) (i j : I) :
    matrixEntry L i j = L i j := rfl

@[simp] theorem outputRow_apply {I : Type} (L : GaugeMatrix I) (j i : I) :
    outputRow L j i = L i j := rfl

@[simp] theorem inputColumn_apply {I : Type} (L : GaugeMatrix I) (i j : I) :
    inputColumn L i j = L i j := rfl

section FiniteNonemptyIndex

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I]
variable (d : I → X → X → ENNReal)

/-- CH02-D01. The pointwise Lip inequality on a restricted domain `U`.  This is the inequality
part of the definition; `IsLipMatrixOn` additionally records that `U` lies in `dom ϕ`. -/
def LipBoundOn (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, L i j * d i x y

/-- A legal restricted Lipschitz matrix for `ϕ` on `U`.

The source defines restricted Lip matrices for `U ⊆ dom(ϕ)`; that domain condition is
kept explicitly rather than hidden in a certificate field for the inequality. -/
def IsLipMatrixOn (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧ LipBoundOn d ϕ U L

/-- A legal global Lipschitz matrix for `ϕ`, on the whole domain `dom(ϕ)`. -/
def IsLipMatrix (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  IsLipMatrixOn d ϕ (dom ϕ) L

/-- The certificate family `𝓛(ϕ)|_U` of legal restricted Lip matrices. -/
def lipMatricesOn (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  {L | IsLipMatrixOn d ϕ U L}

/-- The global certificate family `𝓛(ϕ)`. -/
def lipMatrices (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  {L | IsLipMatrix d ϕ L}

/-- The pointwise co-Lip inequality on a restricted domain `U`. -/
def CoLipBoundOn (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- CH02-D02. A legal restricted co-Lipschitz matrix for `ϕ` on `U`.

This retains all three source conditions: `U` is nonempty, `U ⊆ dom(ϕ)`, and the
co-Lip lower bound holds pointwise. -/
def IsCoLipMatrixOn (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ CoLipBoundOn d ϕ U K

/-- The certificate family `𝓚(ϕ)|_U` of legal restricted co-Lip matrices. -/
def coLipMatricesOn (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  {K | IsCoLipMatrixOn d ϕ U K}

/-- A legal global co-Lip matrix, using `dom(ϕ)` as the restricted domain.  In
accordance with the source, this family is empty when `dom(ϕ)` is empty. -/
def IsCoLipMatrix (ϕ : Operator X bot) (K : GaugeMatrix I) : Prop :=
  IsCoLipMatrixOn d ϕ (dom ϕ) K

/-- The global co-Lip certificate family `𝓚(ϕ)`. -/
def coLipMatrices (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  {K | IsCoLipMatrix d ϕ K}


/-- An ordered pair `(i,j)` is the component channel from input component `i` to
output component `j` in §2.2. -/
abbrev ComponentChannel (I : Type) := I × I

/-- The input component of a component channel. -/
def channelInput {I : Type} (c : ComponentChannel I) : I := c.1

/-- The output component of a component channel. -/
def channelOutput {I : Type} (c : ComponentChannel I) : I := c.2

/-- CH02-D07. The `j`-th output row has no nonzero input entry except possibly `i`.  This is the
single-input-channel row hypothesis used in §2.2. -/
def SingleInputRow (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- The same single-input condition, stated for an ordered component channel. -/
abbrev SingleInputChannel (L : GaugeMatrix I) (c : ComponentChannel I) : Prop :=
  SingleInputRow L c.1 c.2

/-- A diagonally supported matrix: all off-diagonal entries vanish. -/
def IsDiagonalMatrix (L : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

end FiniteNonemptyIndex

end formal_oet.ch_02_operator_bounds
