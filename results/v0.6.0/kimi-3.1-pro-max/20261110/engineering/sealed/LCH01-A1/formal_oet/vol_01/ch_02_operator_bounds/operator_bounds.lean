import Mathlib.Data.Matrix.Mul
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-- An extended nonnegative bound matrix.  The first index is the output
component (the row), and the second index is the input component (the column).
Thus `L j i` represents the source entry `L_{i → j}`. -/
abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

/-- Matrix multiplication in output-row/input-column coordinates. -/
theorem boundMatrix_mul_channel_apply {I : Type} [Fintype I]
    (M N : BoundMatrix I) (i j : I) :
    (M * N) j i = ∑ k, M j k * N k i := by
  rw [Matrix.mul_apply]

/-- `L` is a Lipschitz certificate for `φ` restricted to `U`.
The domain condition is part of restricted-certificate validity. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

/-- `L` is a global Lipschitz certificate: the restricted predicate on
`dom φ`. -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : BoundMatrix I) : Prop :=
  IsRestrictedLipMatrix d φ (dom φ) L

/-- The family of all global Lipschitz certificates for `φ`. -/
def lipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (BoundMatrix I) :=
  {L | IsLipMatrix d φ L}

/-- The family of all Lipschitz certificates for `φ` restricted to `U`. -/
def restrictedLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) :=
  {L | IsRestrictedLipMatrix d φ U L}

/-- The global predicate expands to exactly the displayed family of
Lipschitz inequalities on `dom φ`. -/
theorem isLipMatrix_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (L : BoundMatrix I) :
    IsLipMatrix d φ L ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j,
        d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y := by
  simp [IsLipMatrix, IsRestrictedLipMatrix]

/-- A co-Lipschitz certificate on `U`.  Both `U ⊆ dom φ` and the source's
standing nonemptiness requirement `U ≠ ∅` are included in validity. -/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      ∑ i, K j i * d i x y ≤ d j (φ.func x) (φ.func y)

/-- The family of all co-Lipschitz certificates for `φ` restricted to `U`;
membership includes the requirement that `U` be nonempty. -/
def restrictedCoLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) :=
  {K | IsRestrictedCoLipMatrix d φ U K}

/-- A component channel, viewed as an ordered pair with separately named
input and output components. -/
structure ComponentChannel (I : Type) where
  input : I
  output : I

/-- The matrix coefficient attached to a component channel. -/
def channelEntry {I : Type} (L : BoundMatrix I) (c : ComponentChannel I) : ENNReal :=
  L c.output c.input

/-- In output row `j`, only input column `i` is allowed to be nonzero. -/
def SingleInputRow {I : Type} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k, k ≠ i → L j k = 0

/-- A bound matrix is diagonal when every off-diagonal channel entry is zero. -/
def IsDiagonalBoundMatrix {I : Type} (L : BoundMatrix I) : Prop :=
  ∀ i j, i ≠ j → L j i = 0

/-- Every diagonal output row has only its same-component input term. -/
theorem diagonal_singleInputRow {I : Type} (L : BoundMatrix I)
    (hL : IsDiagonalBoundMatrix L) (i : I) :
    SingleInputRow L i i := by
  intro k hki
  exact hL k i hki

/-- With only one potentially nonzero input term in an output row, the whole
weighted sum simplifies to that term. -/
theorem weighted_row_eq_single_input {I : Type} [Fintype I]
    (L : BoundMatrix I) (v : I → ENNReal) (i j : I)
    (hrow : SingleInputRow L i j) :
    ∑ k, L j k * v k = L j i * v i := by
  classical
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · simp

/-- Proposition: a single-input output row reduces the restricted Lipschitz
inequality to the corresponding scalar upper bound. -/
theorem lip_bound_of_singleInputRow {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I)
    (hL : L ∈ restrictedLipCertificates d φ U)
    {i j : I} (hrow : SingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j i * d i x y := by
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k, L j k * d k x y := hL.2 x hx y hy j
    _ = L j i * d i x y := weighted_row_eq_single_input L (fun k => d k x y) i j hrow

/-- Diagonal special case: every same-component channel has the scalar
Lipschitz upper bound. -/
theorem lip_bound_of_diagonal {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I)
    (hL : L ∈ restrictedLipCertificates d φ U)
    (hdiag : IsDiagonalBoundMatrix L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i : I) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  exact lip_bound_of_singleInputRow d φ U L hL
    (diagonal_singleInputRow L hdiag i) hx hy

/-- One input term is already bounded above by the output distance whenever
`K` is a restricted co-Lipschitz certificate. -/
theorem coLip_single_input_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I)
    (hK : K ∈ restrictedCoLipCertificates d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K j i * d i x y ≤ d j (φ.func x) (φ.func y) := by
  calc
    K j i * d i x y ≤ ∑ k, K j k * d k x y := by
      exact Finset.single_le_sum (fun k _ => zero_le (K j k * d k x y))
        (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

/-- Proposition 2.8(i): a strictly positive co-Lipschitz channel carries
strictly positive input distance to strictly positive output distance. -/
theorem positive_output_dist_of_positive_coLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I)
    (hK : K ∈ restrictedCoLipCertificates d φ U)
    {i j : I} (hKij : 0 < K j i)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hd : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hterm : 0 < K j i * d i x y :=
    ENNReal.mul_pos (ne_of_gt hKij) (ne_of_gt hd)
  exact lt_of_lt_of_le hterm (coLip_single_input_le d φ U K hK hx hy i j)

/-- Proposition 2.8(ii): if every diagonal co-Lipschitz entry is strictly
positive, then `φ` reflects the family's zero-distance relation on `U`.
The conclusion is `GaugeZeroRelated`, not point equality. -/
theorem reflects_gaugeZeroRelated_of_positive_diagonal_coLip
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I)
    (hK : K ∈ restrictedCoLipCertificates d φ U)
    (hdiag : ∀ j, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hd : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have himage : 0 < d j (φ.func x) (φ.func y) :=
    positive_output_dist_of_positive_coLip d φ U K hK (hdiag j) hx hy hd
  rw [hzero j] at himage
  exact lt_irrefl 0 himage

/-- Exercise 2.2: with only the diagonal input term in the Lipschitz row,
the output distance has the stated scalar two-sided bound. -/
theorem scalar_two_sided_bound_of_diagonal_input_row
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L K : BoundMatrix I)
    (hL : L ∈ restrictedLipCertificates d φ U)
    (hK : K ∈ restrictedCoLipCertificates d φ U)
    {j : I} (hrow : ∀ k, k ≠ j → L j k = 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · exact coLip_single_input_le d φ U K hK hx hy j j
  · exact lip_bound_of_singleInputRow d φ U L hL hrow hx hy

end formal_oet.vol_01.ch_02_operator_bounds
