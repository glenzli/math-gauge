import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# Matrix Bounds and Indexing Conventions (LCH01)

This module formalizes the foundational matrix indexing conventions, matrix multiplication,
global/restricted Lipschitz matrix predicates and certificate families, and restricted
co-Lipschitz matrix predicates and certificate families with nonemptiness condition.

Attribution: Mathematical framework and definitions are based on Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution Theory*, Volume I
(https://glenzli.com/books/oet/), Chapter 2 (§ 2.1), licensed under CC BY 4.0.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-!
## CH02-D03: Input/Output Matrix Indexing Convention and Multiplication

Following OET § 2.1 (`oet-af85899693cc8750`):
- Entries take values in `ENNReal` (`[0, +∞]`), where `0 * ⊤ = 0` holds by `ENNReal` arithmetic.
- Output component `j : I` is the row index and input component `i : I` is the column index,
  so the channel entry `M_{i → j}` sits at row `j`, column `i`, i.e., `(M)_{j, i} = M_{i → j}`.
- Under this convention, standard matrix multiplication satisfies
  `(M₂ · M₁)_{i → j} = ∑ k, (M₂)_{k → j} * (M₁)_{i → k}`.
-/

/-- Extended nonnegative matrix indexed by gauge index type `I`, with output component as row
    index and input component as column index (`M j i = M_{i → j}`). -/
abbrev BoundMatrix (I : Type) : Type := Matrix I I ENNReal

/-- Read the channel entry `M_{i → j}` (input component `i` to output component `j`),
    located at row `j` and column `i` of `M`. -/
def channelEntry {I : Type} (M : BoundMatrix I) (i j : I) : ENNReal :=
  M j i

/-- Construct a `BoundMatrix I` from an input-to-output entry function `f i j = M_{i → j}`
    using the output-as-row, input-as-column convention. -/
def ofChannelEntries {I : Type} (f : I → I → ENNReal) : BoundMatrix I :=
  fun j i => f i j

@[simp] theorem channelEntry_def {I : Type} (M : BoundMatrix I) (i j : I) :
    channelEntry M i j = M j i := rfl

@[simp] theorem channelEntry_ofChannelEntries {I : Type} (f : I → I → ENNReal) (i j : I) :
    channelEntry (ofChannelEntries f) i j = f i j := rfl

@[simp] theorem ofChannelEntries_channelEntry {I : Type} (M : BoundMatrix I) :
    ofChannelEntries (channelEntry M) = M := rfl

/-- Two bound matrices are equal iff all their input-to-output channel entries agree. -/
theorem boundMatrix_ext_channelEntry {I : Type} {M N : BoundMatrix I}
    (h : ∀ i j : I, channelEntry M i j = channelEntry N i j) : M = N := by
  ext j i
  exact h i j

/-- Matrix multiplication of extended nonnegative bound matrices, matching
    `(M₂ · M₁)_{i → j} = ∑ k, (M₂)_{k → j} * (M₁)_{i → k}`. -/
noncomputable def boundMatrixMul {I : Type} [Fintype I] (M₂ M₁ : BoundMatrix I) : BoundMatrix I :=
  M₂ * M₁

/-- Channel-entry expansion of `boundMatrixMul`:
    `(M₂ · M₁)_{i → j} = ∑ k : I, (M₂)_{k → j} * (M₁)_{i → k}`. -/
@[simp] theorem channelEntry_boundMatrixMul {I : Type} [Fintype I]
    (M₂ M₁ : BoundMatrix I) (i j : I) :
    channelEntry (boundMatrixMul M₂ M₁) i j =
      ∑ k : I, channelEntry M₂ k j * channelEntry M₁ i k := by
  simp [boundMatrixMul, channelEntry, Matrix.mul_apply]

/-- Associativity of bound matrix multiplication. -/
theorem boundMatrixMul_assoc {I : Type} [Fintype I]
    (M₃ M₂ M₁ : BoundMatrix I) :
    boundMatrixMul (boundMatrixMul M₃ M₂) M₁ =
      boundMatrixMul M₃ (boundMatrixMul M₂ M₁) := by
  exact Matrix.mul_assoc M₃ M₂ M₁

/-- Identity bound matrix `I`. -/
noncomputable def boundMatrixOne {I : Type} [DecidableEq I] : BoundMatrix I :=
  (1 : Matrix I I ENNReal)

/-- Channel-entry formula for the identity bound matrix. -/
@[simp] theorem channelEntry_boundMatrixOne {I : Type} [DecidableEq I] (i j : I) :
    channelEntry (boundMatrixOne (I := I)) i j = if i = j then 1 else 0 := by
  simp [boundMatrixOne, channelEntry, Matrix.one_apply, eq_comm]

/-- Left identity law for bound matrix multiplication. -/
@[simp] theorem boundMatrixOne_mul {I : Type} [Fintype I] [DecidableEq I] (M : BoundMatrix I) :
    boundMatrixMul boundMatrixOne M = M := by
  exact Matrix.one_mul M

/-- Right identity law for bound matrix multiplication. -/
@[simp] theorem boundMatrixMul_one {I : Type} [Fintype I] [DecidableEq I] (M : BoundMatrix I) :
    boundMatrixMul M boundMatrixOne = M := by
  exact Matrix.mul_one M

/-- Compatibility of the output-as-row, input-as-column convention with matrix-vector product:
    `(M *ᵥ v) j = ∑ i, M_{i → j} * v i`. -/
theorem boundMatrix_mulVec_apply {I : Type} [Fintype I]
    (M : BoundMatrix I) (v : I → ENNReal) (j : I) :
    M.mulVec v j = ∑ i : I, channelEntry M i j * v i := by
  simp [Matrix.mulVec, dotProduct, channelEntry]

/-!
## CH02-D01: Global and Restricted Lipschitz Matrix Predicates and Certificate Families

Following OET § 2.1 (`oet-af85899693cc8750`):
- A global Lipschitz matrix `L ∈ 𝓛(ϕ)` satisfies
  `d_j(ϕ(x), ϕ(y)) ≤ ∑ i, L_{i → j} * d_i(x, y)` for all `x, y ∈ dom(ϕ)` and `j ∈ I`.
- A subset-restricted Lipschitz matrix `L ∈ 𝓛(ϕ)|_U` requires `U ⊆ dom(ϕ)` and the same
  inequality for all `x, y ∈ U` and `j ∈ I`.
-/

/-- Predicate asserting that `L` is a valid global Lipschitz matrix for `ϕ` on `dom ϕ`. -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : BoundMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/-- The global Lipschitz matrix certificate family `𝓛(ϕ)`. -/
def lipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (BoundMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/-- Predicate asserting that `L` is a valid Lipschitz matrix for `ϕ` restricted to `U ⊆ dom ϕ`. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/-- The subset-restricted Lipschitz matrix certificate family `𝓛(ϕ)|_U`. -/
def restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

@[simp] theorem mem_lipMatrices_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : BoundMatrix I) :
    L ∈ lipMatrices d ϕ ↔ IsLipMatrix d ϕ L := Iff.rfl

@[simp] theorem mem_restrictedLipMatrices_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I) :
    L ∈ restrictedLipMatrices d ϕ U ↔ IsRestrictedLipMatrix d ϕ U L := Iff.rfl

theorem IsRestrictedLipMatrix.subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {L : BoundMatrix I}
    (hL : IsRestrictedLipMatrix d ϕ U L) : U ⊆ dom ϕ :=
  hL.1

theorem IsRestrictedLipMatrix.bound {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {L : BoundMatrix I}
    (hL : IsRestrictedLipMatrix d ϕ U L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y :=
  hL.2 x hx y hy j

/-- Global Lipschitz matrices coincide with Lipschitz matrices restricted to `dom ϕ`. -/
theorem isLipMatrix_iff_isRestrictedLipMatrix_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : BoundMatrix I) :
    IsLipMatrix d ϕ L ↔ IsRestrictedLipMatrix d ϕ (dom ϕ) L := by
  exact ⟨fun h => ⟨Set.Subset.rfl, h⟩, fun h => h.2⟩

/-- Equality of certificate families `𝓛(ϕ) = 𝓛(ϕ)|_{dom(ϕ)}`. -/
theorem lipMatrices_eq_restrictedLipMatrices_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    lipMatrices d ϕ = restrictedLipMatrices d ϕ (dom ϕ) := by
  ext L
  exact isLipMatrix_iff_isRestrictedLipMatrix_dom d ϕ L

/-!
## CH02-D02: Restricted co-Lipschitz Matrix Predicate and Certificate Family (with Nonemptiness)

Following OET § 2.1 (`oet-af85899693cc8750`):
- A restricted co-Lipschitz matrix `K ∈ 𝓚(ϕ)|_U` requires `U.Nonempty` (`U ≠ ∅`),
  `U ⊆ dom(ϕ)`, and `∑ i, K_{i → j} * d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))` for all `x, y ∈ U` and `j ∈ I`.
- Whenever `𝓚(ϕ)|_U` appears, the nonemptiness condition `U ≠ ∅` is included.
-/

/-- Predicate asserting that `K` is a valid restricted co-Lipschitz matrix for `ϕ` on `U`,
    explicitly carrying the nonemptiness condition `U.Nonempty` and `U ⊆ dom ϕ`. -/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- The subset-restricted co-Lipschitz matrix certificate family `𝓚(ϕ)|_U`. -/
def restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

@[simp] theorem mem_restrictedCoLipMatrices_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : BoundMatrix I) :
    K ∈ restrictedCoLipMatrices d ϕ U ↔ IsRestrictedCoLipMatrix d ϕ U K := Iff.rfl

/-- Equivalent formulation of `IsRestrictedCoLipMatrix` using `U ≠ ∅`. -/
theorem isRestrictedCoLipMatrix_iff_ne_empty {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : BoundMatrix I) :
    IsRestrictedCoLipMatrix d ϕ U K ↔
      U ≠ ∅ ∧ U ⊆ dom ϕ ∧
      ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
        ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  simp [IsRestrictedCoLipMatrix, Set.nonempty_iff_ne_empty]

theorem IsRestrictedCoLipMatrix.nonempty {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : BoundMatrix I}
    (hK : IsRestrictedCoLipMatrix d ϕ U K) : U.Nonempty :=
  hK.1

theorem IsRestrictedCoLipMatrix.ne_empty {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : BoundMatrix I}
    (hK : IsRestrictedCoLipMatrix d ϕ U K) : U ≠ ∅ :=
  hK.1.ne_empty

theorem IsRestrictedCoLipMatrix.subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : BoundMatrix I}
    (hK : IsRestrictedCoLipMatrix d ϕ U K) : U ⊆ dom ϕ :=
  hK.2.1

theorem IsRestrictedCoLipMatrix.bound {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : BoundMatrix I}
    (hK : IsRestrictedCoLipMatrix d ϕ U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i : I, channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) :=
  hK.2.2 x hx y hy j

/-- On the empty set, the restricted co-Lipschitz certificate family is empty due to the
    nonemptiness requirement. -/
@[simp] theorem restrictedCoLipMatrices_empty {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedCoLipMatrices d ϕ ∅ = ∅ := by
  ext K
  simp [restrictedCoLipMatrices, IsRestrictedCoLipMatrix]

/-- Single-channel lower bound extracted from a restricted co-Lipschitz certificate:
    for any `K ∈ 𝓚(ϕ)|_U`, `i, j : I`, and `x, y ∈ U`,
    `K_{i → j} * d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))`. -/
theorem colip_single_channel_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) (i j : I)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  have hsum : ∑ k : I, channelEntry K k j * d k x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    hK.bound hx hy j
  have hsingle :
      channelEntry K i j * d i x y ≤ ∑ k : I, channelEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k : I => channelEntry K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  exact le_trans hsingle hsum

end LCH01
