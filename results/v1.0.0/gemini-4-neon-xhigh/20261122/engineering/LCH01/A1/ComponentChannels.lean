import MatrixBounds

/-!
# Component Channels, Single-Input Simplification, and Scalar Two-Sided Bounds (LCH01)

This module formalizes OET Chapter 2, § 2.2 (Component Channels, single-input row sparsity,
diagonal special case, Proposition 2.8) and § 2.3 Exercise 2.2 (scalar two-sided bound on a
diagonal input row).

Attribution: Mathematical framework, definitions, and propositions are based on Zhe Li
(Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution
Theory*, Volume I (https://glenzli.com/books/oet/), Chapter 2 (§ 2.2–§ 2.3), licensed under
CC BY 4.0.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-!
## CH02-D07: Component Channels, Single-Input Row Sparsity, and Diagonal Matrices

Following OET § 2.2 (`oet-7fa97eb6e24d5527`):
- A component channel `(i, j)` is an ordered pair from input component `d_i` to output
  component `d_j`.
- Single-input row sparsity on channel `(i, j)` means row `j` vanishes outside column `i`,
  i.e., `∀ k ≠ i, M_{k → j} = 0`.
- A bound matrix `M` is diagonal iff every off-diagonal channel entry vanishes, equivalently
  every row `j` satisfies single-input row sparsity on the same-component channel `(j, j)`.
-/

/-- A component channel `(i, j)` from input gauge component `d_i` to output gauge component `d_j`. -/
abbrev ComponentChannel (I : Type) : Type := I × I

/-- Input component index of a component channel. -/
def ComponentChannel.input {I : Type} (c : ComponentChannel I) : I := c.1

/-- Output component index of a component channel. -/
def ComponentChannel.output {I : Type} (c : ComponentChannel I) : I := c.2

/-- The same-component (diagonal) channel `(i, i)`. -/
def ComponentChannel.diag {I : Type} (i : I) : ComponentChannel I := (i, i)

/-- Matrix coefficient `M_{c.input → c.output}` associated with component channel `c`. -/
def channelCoeff {I : Type} (M : BoundMatrix I) (c : ComponentChannel I) : ENNReal :=
  channelEntry M c.input c.output

@[simp] theorem ComponentChannel.input_mk {I : Type} (i j : I) :
    ComponentChannel.input (i, j) = i := rfl

@[simp] theorem ComponentChannel.output_mk {I : Type} (i j : I) :
    ComponentChannel.output (i, j) = j := rfl

@[simp] theorem ComponentChannel.input_diag {I : Type} (i : I) :
    (ComponentChannel.diag i).input = i := rfl

@[simp] theorem ComponentChannel.output_diag {I : Type} (i : I) :
    (ComponentChannel.diag i).output = i := rfl

@[simp] theorem channelCoeff_mk {I : Type} (M : BoundMatrix I) (i j : I) :
    channelCoeff M (i, j) = channelEntry M i j := rfl

/-- Single-input row sparsity: row `j` (output component `j`) of `M` vanishes on every
    input component `k ≠ i`, leaving only `M_{i → j}`. -/
def IsSingleInputRow {I : Type} (M : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → channelEntry M k j = 0

/-- Channel-pair form of single-input row sparsity for `c = (i, j)`. -/
def IsSingleInputChannel {I : Type} (M : BoundMatrix I) (c : ComponentChannel I) : Prop :=
  IsSingleInputRow M c.input c.output

/-- Diagonal bound matrix: all off-diagonal channel entries `M_{k → j}` (`k ≠ j`) vanish. -/
def IsDiagonalBoundMatrix {I : Type} (M : BoundMatrix I) : Prop :=
  ∀ k j : I, k ≠ j → channelEntry M k j = 0

/-- A bound matrix is diagonal iff every row `j` is single-input on the diagonal channel `(j, j)`. -/
theorem isDiagonalBoundMatrix_iff_forall_singleInputRow {I : Type} (M : BoundMatrix I) :
    IsDiagonalBoundMatrix M ↔ ∀ j : I, IsSingleInputRow M j j := by
  constructor
  · intro h j k hk
    exact h k j hk
  · intro h k j hk
    exact h j k hk

/-- Every same-component channel `(i, i)` of a diagonal bound matrix satisfies single-input
    row sparsity. -/
theorem IsDiagonalBoundMatrix.singleInputRow {I : Type} {M : BoundMatrix I}
    (hdiag : IsDiagonalBoundMatrix M) (i : I) :
    IsSingleInputRow M i i :=
  (isDiagonalBoundMatrix_iff_forall_singleInputRow M).mp hdiag i

/-- Channel-pair form of `IsDiagonalBoundMatrix.singleInputRow`. -/
theorem IsDiagonalBoundMatrix.singleInputChannel_diag {I : Type} {M : BoundMatrix I}
    (hdiag : IsDiagonalBoundMatrix M) (i : I) :
    IsSingleInputChannel M (ComponentChannel.diag i) :=
  hdiag.singleInputRow i

/-!
## CH02-P19: Single-Input Row Simplification (Including the Diagonal Special Case)

Following OET § 2.2 (`oet-7fa97eb6e24d5527`):
- A zero channel entry `L_{i → j} = 0` drops out of the upper-bound sum.
- If row `j` of `L ∈ 𝓛(ϕ)|_U` vanishes outside `L_{i → j}`, then for all `x, y ∈ U`,
  `d_j(ϕ(x), ϕ(y)) ≤ ∑ k, L_{k → j} * d_k(x, y) = L_{i → j} * d_i(x, y)`.
- If `L` is diagonal, this simplification holds for every same-component channel `(i, i)`.
-/

/-- Exact row-sum reduction under single-input row sparsity:
    `∑ k, L_{k → j} * v k = L_{i → j} * v i`. -/
theorem sum_singleInputRow {I : Type} [Fintype I]
    (L : BoundMatrix I) (i j : I) (v : I → ENNReal)
    (hrow : IsSingleInputRow L i j) :
    ∑ k : I, channelEntry L k j * v k = channelEntry L i j * v i := by
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- A zero channel entry `L_{i → j} = 0` does not contribute to the Lipschitz upper bound
    for output component `j` (even when `d_i(x, y) = ⊤`, since `0 * ⊤ = 0`). -/
theorem lip_zero_channel_omit {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : BoundMatrix I) (i j : I)
    (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hzero : channelEntry L i j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤
        ∑ k ∈ Finset.univ.erase i, channelEntry L k j * d k x y := by
  intro x hx y hy
  have hbound := hL.bound hx hy j
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun k : I => channelEntry L k j * d k x y) (Finset.mem_univ i)
  dsimp only at hsplit
  rw [hzero, zero_mul, zero_add] at hsplit
  rw [hsplit]
  exact hbound

/-- Single-input row Lipschitz simplification:
    if `L ∈ 𝓛(ϕ)|_U` and row `j` vanishes outside `L_{i → j}`, then for all `x, y ∈ U`,
    `d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} * d_i(x, y)`. -/
theorem lip_singleInputRow_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : BoundMatrix I) (i j : I)
    (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hrow : IsSingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L i j * d i x y := by
  intro x hx y hy
  calc
    d j (ϕ.func x) (ϕ.func y)
      ≤ ∑ k : I, channelEntry L k j * d k x y := hL.bound hx hy j
    _ = channelEntry L i j * d i x y := sum_singleInputRow L i j (fun k => d k x y) hrow

/-- Channel-pair form of `lip_singleInputRow_bound`. -/
theorem lip_singleInputChannel_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : BoundMatrix I) (c : ComponentChannel I)
    (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hch : IsSingleInputChannel L c) :
    ∀ x ∈ U, ∀ y ∈ U,
      d c.output (ϕ.func x) (ϕ.func y) ≤ channelCoeff L c * d c.input x y :=
  lip_singleInputRow_bound d ϕ U L c.input c.output hL hch

/-- Exact row-sum reduction for every row of a diagonal bound matrix:
    `∑ k, L_{k → i} * v k = L_{i → i} * v i`. -/
theorem sum_diagonalRow {I : Type} [Fintype I]
    (L : BoundMatrix I) (v : I → ENNReal)
    (hdiag : IsDiagonalBoundMatrix L) (i : I) :
    ∑ k : I, channelEntry L k i * v k = channelEntry L i i * v i :=
  sum_singleInputRow L i i v (hdiag.singleInputRow i)

/-- Diagonal special case of single-input row simplification:
    if `L ∈ 𝓛(ϕ)|_U` is diagonal, then for every same-component channel `(i, i)` and all
    `x, y ∈ U`, `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} * d_i(x, y)`. -/
theorem lip_diagonal_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : BoundMatrix I)
    (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hdiag : IsDiagonalBoundMatrix L) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  intro i
  exact lip_singleInputRow_bound d ϕ U L i i hL (hdiag.singleInputRow i)

/-!
## CH02-P20: Proposition 2.8(i) — Positive co-Lip Channel Preserves Positive Distance

Following OET Proposition 2.8(i) (`oet-f82672ec0dd48f28`):
If `K ∈ 𝓚(ϕ)|_U` and `K_{i → j} > 0`, then for all `x, y ∈ U`,
`d_i(x, y) > 0 → d_j(ϕ(x), ϕ(y)) > 0`.
-/

/-- Proposition 2.8(i): a strictly positive co-Lip channel `K_{i → j} > 0` preserves
    strictly positive distance from component `i` to component `j` on `U`. -/
theorem colip_pos_channel_preserves_pos_dist {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) (i j : I)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hK_pos : 0 < channelEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hd_pos
  have hmul_pos : 0 < channelEntry K i j * d i x y :=
    ENNReal.mul_pos (ne_of_gt hK_pos) (ne_of_gt hd_pos)
  exact lt_of_lt_of_le hmul_pos (colip_single_channel_le d ϕ U K i j hK x hx y hy)

/-- Channel-pair form of Proposition 2.8(i). -/
theorem colip_pos_componentChannel_preserves_pos_dist {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) (c : ComponentChannel I)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hK_pos : 0 < channelCoeff K c) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d c.input x y → 0 < d c.output (ϕ.func x) (ϕ.func y) :=
  colip_pos_channel_preserves_pos_dist d ϕ U K c.input c.output hK hK_pos

/-!
## CH02-P21: Proposition 2.8(ii) — All-Diagonal Positive co-Lip Reflects Gauge Zero-Relation

Following OET Proposition 2.8(ii) (`oet-f82672ec0dd48f28`):
If `K ∈ 𝓚(ϕ)|_U` and `K_{j → j} > 0` for all `j ∈ I`, then for all `x, y ∈ U`,
`ϕ(x) ∼_G ϕ(y) → x ∼_G y`.
Per the textbook convention, gauge separation is not assumed, so the conclusion is
`GaugeZeroRelated d x y` rather than `x = y`.
-/

/-- Proposition 2.8(ii): if `K ∈ 𝓚(ϕ)|_U` has strictly positive diagonal entries
    `K_{j → j} > 0` for every `j : I`, then `ϕ` reflects the family zero-distance relation
    `GaugeZeroRelated d` on `U` (without strengthening to point equality). -/
theorem colip_pos_diag_reflects_gauge_zero_related {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hK_diag : ∀ j : I, 0 < channelEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hphi_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    colip_pos_channel_preserves_pos_dist d ϕ U K j j hK (hK_diag j) x hx y hy hpos
  exact (ne_of_gt hphi_pos) (hrel j)

/-- Counterexample showing that Proposition 2.8(ii) cannot be strengthened to point equality
    `x = y` in a general (non-separating) extended gauge space. -/
theorem colip_pos_diag_not_implies_eq_without_separation :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal)
      (_ : ∀ i : I, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (K : BoundMatrix I) (x y : X),
      IsNonSeparating d ∧
      K ∈ restrictedCoLipMatrices d ϕ U ∧
      (∀ j : I, 0 < channelEntry K j j) ∧
      x ∈ U ∧ y ∈ U ∧
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) ∧
      GaugeZeroRelated d x y ∧
      x ≠ y := by
  let d0 : Option Bool → Option Bool → ENNReal := fun a b =>
    match a, b with
    | none, none => 0
    | some _, some _ => 0
    | some _, none => ⊤
    | none, some _ => ⊤
  let d : Unit → Option Bool → Option Bool → ENNReal := fun _ => d0
  have hd : ∀ i : Unit, ExtendedPseudoMetric (Option Bool) none (d i) := by
    intro _
    refine
      { nonabsorbing := ⟨some false, by simp⟩
        dist_self := by
          intro a
          cases a <;> rfl
        symm := by
          intro a b
          cases a <;> cases b <;> rfl
        triangle := by
          intro a b c
          cases a <;> cases b <;> cases c <;> simp [d, d0]
        isolate_bot := by
          intro a ha
          cases a with
          | none => exact False.elim (ha rfl)
          | some _ => rfl }
  let ϕ : Operator (Option Bool) none := operator_identity
  let U : Set (Option Bool) := {some false, some true}
  let K : BoundMatrix Unit := fun _ _ => 1
  refine ⟨Option Bool, Unit, none, inferInstance, inferInstance, d, hd, ϕ, U, K,
    some false, some true, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hsep
    have heq : (some false : Option Bool) = some true := hsep (some false) (some true) (fun _ => rfl)
    cases heq
  · refine ⟨⟨some false, by simp [U]⟩, ?_, ?_⟩
    · intro z hz
      rcases hz with rfl | rfl <;> simp [dom, ϕ, operator_identity]
    · intro a ha b hb j
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp [d, d0, ϕ, operator_identity, K, channelEntry]
  · intro j
    simp [K, channelEntry]
  · simp [U]
  · simp [U]
  · intro _
    rfl
  · intro _
    rfl
  · simp

/-!
## CH02-P25: Exercise 2.2 — Scalar Two-Sided Bound on a Diagonal Input Row

Following OET Exercise 2.2 (`oet-6a98a58b5bc95360`):
Let `ϕ ∈ X_op`, `U ⊆ dom(ϕ)`, `j ∈ I`, `L ∈ 𝓛(ϕ)|_U`, and `K ∈ 𝓚(ϕ)|_U`.
If row `j` of `L` retains only the diagonal input term (`L_{k → j} = 0` for all `k ≠ j`),
then for all `x, y ∈ U`,
`K_{j → j} * d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} * d_j(x, y)`.
-/

/-- Exercise 2.2: scalar two-sided inequality on output component `j` when `L ∈ 𝓛(ϕ)|_U`
    has only the diagonal input term in row `j` (`IsSingleInputRow L j j`) and
    `K ∈ 𝓚(ϕ)|_U`. Note that `L ∈ 𝓛(ϕ)|_U` already carries `U ⊆ dom ϕ` and
    `K ∈ 𝓚(ϕ)|_U` carries `U.Nonempty ∧ U ⊆ dom ϕ`. -/
theorem scalar_two_sided_diag_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (j : I) (L K : BoundMatrix I)
    (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hrow : IsSingleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · exact colip_single_channel_le d ϕ U K j j hK x hx y hy
  · exact lip_singleInputRow_bound d ϕ U L j j hL hrow x hx y hy

end LCH01
