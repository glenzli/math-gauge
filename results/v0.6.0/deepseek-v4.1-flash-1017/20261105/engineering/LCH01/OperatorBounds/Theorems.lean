import OperatorBounds.Basic

set_option linter.unusedSectionVars false

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

namespace formal_oet.ch_02_operator_bounds

section FiniteNonemptyIndex

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I]
variable {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
variable {L K : GaugeMatrix I}

/-- CH02-P19: a Lip row with only the input term `i` possibly nonzero reduces to a
single scalar channel `i → j`.  The hypothesis is stated exactly as in §2.2:
all entries `L_{k→j}` with `k ≠ i` vanish. -/
theorem lip_single_input_row
    (hL : IsLipMatrixOn d ϕ U L)
    {i j : I} (hrow : SingleInputRow L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  calc
    d j (ϕ.func x) (ϕ.func y)
        ≤ ∑ k, L k j * d k x y := (IsLipMatrixOn.bound hL) x hx y hy j
    _ = L i j * d i x y := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro k _ hki
        rw [hrow k hki, zero_mul]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))

/-- CH02-P19, diagonal special case: if an off-diagonally supported matrix is used,
each same-component channel `j → j` gives the scalar Lip bound
`d_j(ϕx,ϕy) ≤ L_{j→j} d_j(x,y)`. -/
theorem lip_diagonal_same_component
    (hL : IsLipMatrixOn d ϕ U L)
    (hdiag : IsDiagonalMatrix L)
    {j : I} {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  lip_single_input_row hL (diagonal_row_vanishes hdiag) hx hy

/-- CH02-P20: a strictly positive co-Lip entry `K_{i→j}` preserves strict positivity
of distances: a positive input `d_i`-distance implies a positive output `d_j`-distance. -/
theorem coLip_pos_preserves_pos
    (hK : IsCoLipMatrixOn d ϕ U K)
    {i j : I} (hKij : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hdij : 0 < d i x y) :
    0 < d j (ϕ.func x) (ϕ.func y) := by
  have hterm : 0 < K i j * d i x y :=
    ENNReal.mul_pos (ne_of_gt hKij) (ne_of_gt hdij)
  have hterm_le_sum : K i j * d i x y ≤ ∑ k, K k j * d k x y := by
    exact Finset.single_le_sum (fun k _ => (zero_le (K k j * d k x y) : 0 ≤ K k j * d k x y))
      (Finset.mem_univ i)
  have hsum : 0 < ∑ k, K k j * d k x y := lt_of_lt_of_le hterm hterm_le_sum
  exact lt_of_lt_of_le hsum ((IsCoLipMatrixOn.bound hK) x hx y hy j)

/-- CH02-P21: if all diagonal co-Lip entries are strictly positive on `U`, then `ϕ`
reflects the all-component zero-distance relation.  The conclusion is deliberately
only `x ∼_G y`, not point equality `x = y`; no separation of the ambient gauge family
is assumed. -/
theorem coLip_diagonal_reflects_zero_related
    (hK : IsCoLipMatrixOn d ϕ U K)
    (hdiag : ∀ j : I, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hphi : GaugeZeroRelated d (ϕ.func x) (ϕ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have houtpos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    coLip_pos_preserves_pos hK (hdiag j) hx hy hpos
  have houtzero : d j (ϕ.func x) (ϕ.func y) = 0 := hphi j
  rw [houtzero] at houtpos
  exact (lt_irrefl (0 : ENNReal)) houtpos

/-- CH02-P25 (Exercise 2.2): under a row with only the diagonal input term, the
co-Lip and Lip certificates give the scalar two-sided bound
`K_{j→j} d_j(x,y) ≤ d_j(ϕx,ϕy) ≤ L_{j→j} d_j(x,y)`. -/
theorem scalar_two_sided_bound
    (hL : IsLipMatrixOn d ϕ U L)
    (hK : IsCoLipMatrixOn d ϕ U K)
    {j : I} (hrow : SingleInputRow L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  constructor
  · have hterm_le_sum : K j j * d j x y ≤ ∑ i, K i j * d i x y := by
      exact Finset.single_le_sum (fun i _ => (zero_le (K i j * d i x y) : 0 ≤ K i j * d i x y)) (Finset.mem_univ j)
    exact le_trans hterm_le_sum ((IsCoLipMatrixOn.bound hK) x hx y hy j)
  · exact lip_single_input_row hL hrow hx hy

end FiniteNonemptyIndex

end formal_oet.ch_02_operator_bounds
