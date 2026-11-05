import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Lean reformulation of selected material from Zhe Li (also known as Glen Li /
glenzli), ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution
Theory*, Volume I, Chapter 2, https://glenzli.com/books/oet/ . Licensed under
CC BY 4.0, https://creativecommons.org/licenses/by/4.0/ .
-/

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

namespace LCH01

variable {X I : Type} {bot : X} [Fintype I]

/-- Matrices use output components as rows and input components as columns. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- A component channel is an ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

/-- The coefficient of a channel `(i,j)` is the matrix entry at row `j`, column `i`. -/
def channelCoefficient (M : ChannelMatrix I) (c : ComponentChannel I) : ENNReal :=
  M c.2 c.1

omit [Fintype I] in
@[simp] theorem channelCoefficient_pair (M : ChannelMatrix I) (i j : I) :
    channelCoefficient M (i, j) = M j i := rfl

/-- The composition product has the later matrix on the left. -/
noncomputable def channelProduct (M₂ M₁ : ChannelMatrix I) : ChannelMatrix I := M₂ * M₁

theorem channelProduct_entry (M₂ M₁ : ChannelMatrix I) (i j : I) :
    channelCoefficient (channelProduct M₂ M₁) (i, j) =
      ∑ k : I, channelCoefficient M₂ (k, j) * channelCoefficient M₁ (i, k) := by
  exact Matrix.mul_apply

/-- An unrestricted Lip matrix has the defining inequality on the whole domain. -/
def IsLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L j i * d i x y

/-- Restricted Lip certificates require the restriction to lie in the domain. -/
def IsRestrictedLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L j i * d i x y

def lipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (ChannelMatrix I) :=
  { L | IsLipMatrix d φ L }

def restrictedLipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  { L | IsRestrictedLipMatrix d φ U L }

theorem lipMatrix_iff_restricted_domain (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : ChannelMatrix I) :
    IsLipMatrix d φ L ↔ IsRestrictedLipMatrix d φ (dom φ) L := by
  constructor
  · intro h
    exact ⟨Set.Subset.rfl, h⟩
  · intro h
    exact h.2

/-- Restricted co-Lip certificates additionally require a nonempty restriction. -/
def IsRestrictedCoLipMatrix (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, K j i * d i x y ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (ChannelMatrix I) :=
  { K | IsRestrictedCoLipMatrix d φ U K }

/-- Only the coefficient on channel `(i,j)` may be nonzero in output row `j`. -/
def IsSingleInputRow (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L j k = 0

/-- Each output row of a diagonal matrix is supported on its diagonal input. -/
def IsDiagonal (L : ChannelMatrix I) : Prop :=
  ∀ j : I, IsSingleInputRow L j j

omit [Fintype I] in
theorem zero_channel_term (L : ChannelMatrix I) (i j : I)
    (d : I → X → X → ENNReal) (x y : X)
    (hzero : channelCoefficient L (i, j) = 0) :
    L j i * d i x y = 0 := by
  simpa using congrArg (fun a : ENNReal => a * d i x y) hzero

open scoped Classical in
/-- A zero channel can be omitted from the corresponding Lip row bound. -/
theorem zero_channel_lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsRestrictedLipMatrix d φ U L)
    (hzero : channelCoefficient L (i, j) = 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤
      ∑ k ∈ Finset.univ.erase i, L j k * d k x y := by
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, L j k * d k x y :=
      hL.2 x hx y hy j
    _ = ∑ k ∈ Finset.univ.erase i, L j k * d k x y := by
      symm
      exact Finset.sum_erase Finset.univ (zero_channel_term L i j d x y hzero)

/-- Exact simplification of a single-input row, including infinite values. -/
theorem singleInputRow_sum (d : I → X → X → ENNReal)
    (L : ChannelMatrix I) (i j : I) (hrow : IsSingleInputRow L i j) (x y : X) :
    (∑ k : I, L j k * d k x y) = L j i * d i x y := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- A single-input row gives the stated scalar Lip bound on that channel. -/
theorem singleInputRow_lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsRestrictedLipMatrix d φ U L) (hrow : IsSingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j i * d i x y := by
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, L j k * d k x y :=
      hL.2 x hx y hy j
    _ = L j i * d i x y := singleInputRow_sum d L i j hrow x y

/-- The diagonal case holds simultaneously for every component. -/
theorem diagonal_lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I)
    (hL : IsRestrictedLipMatrix d φ U L) (hdiag : IsDiagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  singleInputRow_lip d φ U L j j hL (hdiag j) hx hy

/-- A single nonnegative channel term is bounded by the full output-row sum. -/
theorem channel_term_le_sum (d : I → X → X → ENNReal)
    (K : ChannelMatrix I) (i j : I) (x y : X) :
    K j i * d i x y ≤ ∑ k : I, K j k * d k x y := by
  classical
  exact Finset.single_le_sum (f := fun k : I => K j k * d k x y)
    (fun k _ => zero_le (K j k * d k x y)) (Finset.mem_univ i)

/-- Positive co-Lip channels preserve positive input-component distance. -/
theorem positive_coLip_channel (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I) (i j : I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hpos : 0 < K j i)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hd : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hprod : 0 < K j i * d i x y :=
    ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hd)
  exact lt_of_lt_of_le hprod
    (le_trans (channel_term_le_sum d K i j x y) (hK.2.2 x hx y hy j))

/-- Strictly positive diagonal co-Lip entries reflect family-zero distance. -/
theorem positive_diagonal_coLip_reflects_zero
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hdiag : ∀ j : I, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have houtpos := positive_coLip_channel d φ U K j j hK (hdiag j) hx hy hpos
  exact (ne_of_gt houtpos) (hout j)

/-- Exercise 2.2: the diagonal channel gives a scalar two-sided estimate. -/
theorem scalar_two_sided_bounds (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (L K : ChannelMatrix I) (j : I)
    (hL : IsRestrictedLipMatrix d φ U L)
    (hK : IsRestrictedCoLipMatrix d φ U K)
    (hrow : IsSingleInputRow L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · exact le_trans (channel_term_le_sum d K j j x y) (hK.2.2 x hx y hy j)
  · exact singleInputRow_lip d φ U L j j hL hrow hx hy

/-!
The preceding algebraic results do not need the pseudometric axioms or a
nonempty index set. The following specializations explicitly retain the
ambient extended-gauge-space assumptions of the source.
-/
namespace Textbook

/-- The single-row Lip display in the finite nonempty gauge setting. -/
theorem singleInputRow [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (L : ChannelMatrix I) (i j : I)
    (hL : IsRestrictedLipMatrix d φ U L) (hrow : IsSingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ (∑ k : I, L j k * d k x y) ∧
      (∑ k : I, L j k * d k x y) = L j i * d i x y :=
  ⟨hL.2 x hx y hy j, singleInputRow_sum d L i j hrow x y⟩

/-- For a diagonal Lip matrix the single-row bound holds in each component. -/
theorem diagonal [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (L : ChannelMatrix I)
    (hL : IsRestrictedLipMatrix d φ U L) (hdiag : IsDiagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  diagonal_lip d φ U L hL hdiag hx hy j

theorem positiveChannel [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I) (i j : I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hpos : 0 < K j i)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hdist : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  positive_coLip_channel d φ U K i j hK hpos hx hy hdist

theorem reflectsFamilyZero [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (K : ChannelMatrix I)
    (hK : IsRestrictedCoLipMatrix d φ U K) (hdiag : ∀ j : I, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y :=
  positive_diagonal_coLip_reflects_zero d φ U K hK hdiag hx hy hout

theorem scalarTwoSided [Nonempty I] (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (L K : ChannelMatrix I) (j : I)
    (hL : IsRestrictedLipMatrix d φ U L)
    (hK : IsRestrictedCoLipMatrix d φ U K)
    (hrow : IsSingleInputRow L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  scalar_two_sided_bounds d φ U L K j hL hK hrow hx hy

end Textbook

end LCH01
