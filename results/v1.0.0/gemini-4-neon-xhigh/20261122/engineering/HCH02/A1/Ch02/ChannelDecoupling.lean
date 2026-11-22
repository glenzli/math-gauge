import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch02.MatrixCore
import Ch02.MatrixBounds

/-!
# Chapter 2 Component Channels, Decoupling, Single-Channel Constants, and Distinguishability

Formalizes Section 2.2 (`#h-7fa97eb6e24d5527`) of `source/02-operator-bounds.md`:
- Component channels, row/column sparsity and decoupling, diagonal certificates (`HC02-D07`).
- Single-channel feasible scalar family and optimal constant (`HC02-D08`) with all
  boundary/attainment properties and explicit counterexample (`HC02-P18`–`HC02-P24`).
- Zero-entry removal, row/column/diagonal simplification (`HC02-P25`–`HC02-P28`).
- Two-sided diagonal scalar bounds and finite-coefficient branch (`HC02-P29`, `HC02-P30`).
- Positive co-Lip channel distinguishability preservation and diagonal reflection of
  the gauge zero-distance relation (`HC02-P31`, `HC02-P32`).
-/

namespace OetCh02

open formal_oet.vol_01.ch_01_foundations

/-! ### 1. Component Channels, Row/Column Sparsity, and Diagonal Structure (HC02-D07) -/

/-- A component channel `(i, j) ∈ I × I` from input component `d_i` to output component `d_j`. -/
abbrev Channel (I : Type) : Type := I × I

/-- Channel isolation in an upper-bound certificate `L`: `L_{i → j} = 0`. -/
def ChannelIsolated {I : Type} (L : GaugeMatrix I) (c : Channel I) : Prop :=
  L c.1 c.2 = 0

/-- Positive lower-bound transmission in a co-Lip certificate `K`: `K_{i → j} > 0`. -/
def ChannelPosLowerBound {I : Type} (K : GaugeMatrix I) (c : Channel I) : Prop :=
  0 < K c.1 c.2

/-- Single-row sparsity `Row(L, i, j)`: in row `j` (fixed output `j`), every input entry
`k ≠ i` vanishes (`∀ k ≠ i, L_{k → j} = 0`). -/
def RowSparse {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- Matrix-level row decoupling at output `j`: row `j` has at most one nonzero entry. -/
def MatrixRowDecoupled {I : Type} (L : GaugeMatrix I) (j : I) : Prop :=
  ∃ i : I, RowSparse L i j

/-- Operator-level row decoupling (`HC02-D07`, line 313): `ϕ` is row-decoupled on `U`
at output component `d_j` if there exists `L ∈ ℒ(ϕ)|_U` whose `j`-th row has at most
one nonzero entry. -/
def IsRowDecoupled {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, MatrixRowDecoupled L j

/-- Single-column sparsity `Col(L, i, j)`: in column `i` (fixed input `i`), every output
entry `k ≠ j` vanishes (`∀ k ≠ j, L_{i → k} = 0`). -/
def ColSparse {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/-- Matrix-level column decoupling at input `i`: column `i` has at most one nonzero entry. -/
def MatrixColDecoupled {I : Type} (L : GaugeMatrix I) (i : I) : Prop :=
  ∃ j : I, ColSparse L i j

/-- Operator-level column decoupling (`HC02-D07`, line 315): `ϕ` is column-decoupled on `U`
at input component `d_i` if there exists `L ∈ ℒ(ϕ)|_U` whose `i`-th column has at most
one nonzero entry. -/
def IsColDecoupled {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, MatrixColDecoupled L i

/-- Diagonal gauge matrix: all off-diagonal entries vanish (`∀ i ≠ j, L_{i → j} = 0`). -/
def IsDiagonalMatrix {I : Type} (L : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- Completely decoupled upper-bound system (`HC02-D07`, line 317):
a legal restricted Lip certificate `L ∈ ℒ(ϕ)|_U` that is diagonal. -/
def IsCompletelyDecoupled {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  L ∈ RestrictedLipSet d ϕ U ∧ IsDiagonalMatrix L

theorem isDiagonalMatrix_iff_forall_rowSparse {I : Type} (L : GaugeMatrix I) :
    IsDiagonalMatrix L ↔ ∀ j : I, RowSparse L j j := by
  constructor
  · intro h j k hkj
    exact h k j hkj
  · intro h i j hij
    exact h j i hij

theorem isDiagonalMatrix_iff_forall_colSparse {I : Type} (L : GaugeMatrix I) :
    IsDiagonalMatrix L ↔ ∀ i : I, ColSparse L i i := by
  constructor
  · intro h i k hki
    exact h i k hki.symm
  · intro h i j hij
    exact h i j hij.symm

/-! ### 2. Single-Channel Feasible Scalar Family and Infimum (HC02-D08, HC02-P18–P24) -/

/-- Feasible scalar Lipschitz constant family `S_{i → j}(ϕ; U)` for channel `(i, j)` on `U`:
`{ λ ∈ ENNReal | ∀ x, y ∈ U, d_j(ϕ(x), ϕ(y)) ≤ λ * d_i(x, y) }` (`HC02-D08`). -/
def SingleChannelLipFeasible {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { lam : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y }

/-- Single-channel Lipschitz constant `L̲_{i → j}(ϕ; U) := inf S_{i → j}(ϕ; U)` (`HC02-D08`).
By `ENNReal` `sInf`, an empty feasible set automatically yields `⊤` (`+∞`).
This is defined independently of any matrix certificate entry `L_{i → j}`. -/
noncomputable def singleChannelLipConst {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (SingleChannelLipFeasible d ϕ U i j)

theorem singleChannelLipConst_eq_top_of_empty {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hempty : SingleChannelLipFeasible d ϕ U i j = ∅) :
    singleChannelLipConst d ϕ U i j = ⊤ := by
  simp [singleChannelLipConst, hempty]

/--
`HC02-P18`: If there exist `x, y ∈ U` with `d_i(x, y) = 0` and `d_j(ϕ(x), ϕ(y)) > 0`,
then no `λ ∈ ENNReal` (including `∞`) satisfies the single-channel bound, so
`S_{i → j} = ∅` and `L̲_{i → j}(ϕ; U) = +∞`.
-/
theorem singleChannelLipFeasible_eq_empty_of_zero_pos {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_in : d i x y = 0) (h_out : 0 < d j (ϕ.func x) (ϕ.func y)) :
    SingleChannelLipFeasible d ϕ U i j = ∅ ∧
      singleChannelLipConst d ϕ U i j = ⊤ := by
  have hempty : SingleChannelLipFeasible d ϕ U i j = ∅ := by
    ext lam
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hlam
    have hle := hlam x hx y hy
    rw [h_in, mul_zero] at hle
    exact not_lt_of_ge hle h_out
  exact ⟨hempty, singleChannelLipConst_eq_top_of_empty d ϕ U i j hempty⟩

/--
`HC02-P20`: The feasible scalar set `S_{i → j}` is upward closed:
if `λ₀ ∈ S` and `λ₀ ≤ λ₁`, then `λ₁ ∈ S`.
-/
theorem singleChannelLipFeasible_upward_closed {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {lam0 lam1 : ENNReal}
    (h0 : lam0 ∈ SingleChannelLipFeasible d ϕ U i j) (hle : lam0 ≤ lam1) :
    lam1 ∈ SingleChannelLipFeasible d ϕ U i j := by
  intro x hx y hy
  exact le_trans (h0 x hx y hy) (mul_le_mul_left hle (d i x y))

/-- General lemma: any `λ > L̲_{i → j}(ϕ; U)` (allowing `λ = +∞`) belongs to `S_{i → j}`. -/
theorem mem_singleChannelLipFeasible_of_const_lt {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {lam : ENNReal} (hlt : singleChannelLipConst d ϕ U i j < lam) :
    lam ∈ SingleChannelLipFeasible d ϕ U i j := by
  have hnotle : ¬ lam ≤ sInf (SingleChannelLipFeasible d ϕ U i j) := not_le_of_gt hlt
  have hex : ∃ lam0 ∈ SingleChannelLipFeasible d ϕ U i j, ¬ lam ≤ lam0 := by
    by_contra hall
    push Not at hall
    exact hnotle (le_sInf hall)
  rcases hex with ⟨lam0, hlam0, hnot⟩
  exact singleChannelLipFeasible_upward_closed d ϕ U i j hlam0 (le_of_lt (lt_of_not_ge hnot))

/--
`HC02-P21`: In the positive finite infimum context `0 < a < ∞`, every `λ > a`
(including `λ = ∞`) belongs to `S`.
-/
theorem mem_singleChannelLipFeasible_of_gt_pos_finite {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (_hpos : 0 < singleChannelLipConst d ϕ U i j)
    (_hfin : singleChannelLipConst d ϕ U i j < ⊤)
    {lam : ENNReal} (hlt : singleChannelLipConst d ϕ U i j < lam) :
    lam ∈ SingleChannelLipFeasible d ϕ U i j :=
  mem_singleChannelLipFeasible_of_const_lt d ϕ U i j hlt

/--
`HC02-P19` (lines 279–297): When `0 < a < ∞` where `a = L̲_{i → j}(ϕ; U)`,
the infimum is attained: `a ∈ S_{i → j}`, i.e., `d_j(ϕ(x), ϕ(y)) ≤ a * d_i(x, y)`
holds for all `x, y ∈ U`.
-/
theorem singleChannelLipConst_mem_of_pos_lt_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hpos : 0 < singleChannelLipConst d ϕ U i j)
    (hfin : singleChannelLipConst d ϕ U i j < ⊤) :
    singleChannelLipConst d ϕ U i j ∈ SingleChannelLipFeasible d ϕ U i j := by
  set a := singleChannelLipConst d ϕ U i j
  intro x hx y hy
  set A := d j (ϕ.func x) (ϕ.func y)
  set B := d i x y
  by_cases hB0 : B = 0
  · have htop_mem : (⊤ : ENNReal) ∈ SingleChannelLipFeasible d ϕ U i j :=
      mem_singleChannelLipFeasible_of_gt_pos_finite d ϕ U i j hpos hfin hfin
    have hA0 : A ≤ (⊤ : ENNReal) * B := htop_mem x hx y hy
    rw [hB0, mul_zero] at hA0 ⊢
    exact hA0
  · by_cases hBtop : B = ⊤
    · rw [hBtop, ENNReal.mul_top hpos.ne']
      exact le_top
    · by_contra hnotle
      have hlt : a * B < A := lt_of_not_ge hnotle
      have ha_lt_div : a < A / B :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mpr hlt
      obtain ⟨lam, ha_lt_lam, hlam_lt_div⟩ := exists_between ha_lt_div
      have hlam_mem : lam ∈ SingleChannelLipFeasible d ϕ U i j :=
        mem_singleChannelLipFeasible_of_gt_pos_finite d ϕ U i j hpos hfin ha_lt_lam
      have hA_le : A ≤ lam * B := hlam_mem x hx y hy
      have hlamB_lt : lam * B < A :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp hlam_lt_div
      exact not_lt_of_ge hA_le hlamB_lt

/--
`HC02-P22` (Remark `#h-57de7918859a9de2`, lines 299–305):
When `L̲_{i → j}(ϕ; U) = 0`, every finite positive `λ` (`0 < λ < ∞`) is a valid
single-channel scalar certificate (`λ ∈ S_{i → j}`).
-/
theorem mem_singleChannelLipFeasible_of_const_eq_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hzero : singleChannelLipConst d ϕ U i j = 0)
    {lam : ENNReal} (hpos : 0 < lam) (_hfin : lam < ⊤) :
    lam ∈ SingleChannelLipFeasible d ϕ U i j := by
  apply mem_singleChannelLipFeasible_of_const_lt d ϕ U i j
  rw [hzero]
  exact hpos

/--
`HC02-P24` (Remark `#h-57de7918859a9de2`, lines 299–309):
Whether or not the infimum is attained, `L̲_{i → j}(ϕ; U) < ∞` holds iff there exists
a finite constant `λ < ∞` satisfying the single-channel bound on all `x, y ∈ U`.
-/
theorem singleChannelLipConst_lt_top_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) :
    singleChannelLipConst d ϕ U i j < ⊤ ↔
      ∃ lam : ENNReal, lam < ⊤ ∧ lam ∈ SingleChannelLipFeasible d ϕ U i j := by
  constructor
  · intro hfin
    by_cases h0 : singleChannelLipConst d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact mem_singleChannelLipFeasible_of_const_eq_zero d ϕ U i j h0 zero_lt_one ENNReal.one_lt_top
    · have hpos : 0 < singleChannelLipConst d ϕ U i j := pos_iff_ne_zero.mpr h0
      exact ⟨singleChannelLipConst d ϕ U i j, hfin,
        singleChannelLipConst_mem_of_pos_lt_top d ϕ U i j hpos hfin⟩
  · rintro ⟨lam, hlam_fin, hlam_mem⟩
    exact lt_of_le_of_lt (sInf_le hlam_mem) hlam_fin

/-! ### 3. Counterexample: Zero Single-Channel Infimum Not Attained by `0` (HC02-P23) -/

/-- Explicit two-component extended pseudometric family on `Option Bool` (with absorbing
element `bot = none`):
- `d false` assigns `0` on the diagonal and `⊤` between distinct points;
- `d true` assigns `0` on the diagonal, `⊤` to `none`, and `1` between distinct non-`bot` points. -/
def zeroInfCounterexampleDist : Bool → Option Bool → Option Bool → ENNReal
  | false, x, y => if x = y then 0 else ⊤
  | true, x, y => if x = y then 0 else if x = none ∨ y = none then ⊤ else 1

theorem zeroInfCounterexample_extendedPseudoMetric :
    ∀ i : Bool, ExtendedPseudoMetric (Option Bool) none (zeroInfCounterexampleDist i) := by
  intro i
  cases i with
  | false =>
      refine
        { nonabsorbing := ⟨some false, Option.some_ne_none false⟩
          dist_self := fun x => by simp [zeroInfCounterexampleDist]
          symm := fun x y => by
            by_cases h : x = y
            · subst h; simp [zeroInfCounterexampleDist]
            · have h' : y ≠ x := Ne.symm h
              simp [zeroInfCounterexampleDist, h, h']
          triangle := fun x y z => by
            by_cases hxz : x = z
            · subst hxz; simp [zeroInfCounterexampleDist]
            · by_cases hxy : x = y
              · subst hxy; simp [zeroInfCounterexampleDist, hxz]
              · simp [zeroInfCounterexampleDist, hxz, hxy]
          isolate_bot := fun x hx => by simp [zeroInfCounterexampleDist, hx] }
  | true =>
      refine
        { nonabsorbing := ⟨some false, Option.some_ne_none false⟩
          dist_self := fun x => by simp [zeroInfCounterexampleDist]
          symm := fun x y => by
            cases x <;> cases y <;> simp [zeroInfCounterexampleDist]
            · rename_i a b
              by_cases h : a = b
              · subst h; simp
              · have h' : b ≠ a := Ne.symm h
                simp [h, h']
          triangle := fun x y z => by
            cases x with
            | none =>
                cases y with
                | none =>
                    cases z <;> simp [zeroInfCounterexampleDist]
                | some b =>
                    cases z <;> simp [zeroInfCounterexampleDist]
            | some a =>
                cases y with
                | none =>
                    cases z <;> simp [zeroInfCounterexampleDist]
                | some b =>
                    cases z with
                    | none => simp [zeroInfCounterexampleDist]
                    | some c =>
                        cases a <;> cases b <;> cases c <;>
                          simp [zeroInfCounterexampleDist]
          isolate_bot := fun x hx => by
            cases x with
            | none => exact absurd rfl hx
            | some a => simp [zeroInfCounterexampleDist] }

/-- Nonempty valid domain `U = {some false, some true} ⊆ dom(id)`. -/
def zeroInfCounterexampleU : Set (Option Bool) :=
  {some false, some true}

theorem zeroInfCounterexampleU_nonempty : zeroInfCounterexampleU.Nonempty :=
  ⟨some false, by simp [zeroInfCounterexampleU]⟩

theorem zeroInfCounterexampleU_subset_dom :
    zeroInfCounterexampleU ⊆ dom (idOp (bot := (none : Option Bool))) := by
  intro x hx
  rcases hx with rfl | rfl <;> simp [dom, idOp]

/-- Every positive `λ` belongs to `S_{false → true}(id; U)`, so the infimum is `0`. -/
theorem zeroInfCounterexample_const_eq_zero :
    singleChannelLipConst zeroInfCounterexampleDist (idOp (bot := (none : Option Bool)))
      zeroInfCounterexampleU false true = 0 := by
  have hpos_mem : ∀ lam : ENNReal, 0 < lam →
      lam ∈ SingleChannelLipFeasible zeroInfCounterexampleDist
        (idOp (bot := (none : Option Bool))) zeroInfCounterexampleU false true := by
    intro lam hlam x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [zeroInfCounterexampleDist, ENNReal.mul_top hlam.ne']
  have hle_pos : ∀ lam : ENNReal, 0 < lam →
      singleChannelLipConst zeroInfCounterexampleDist (idOp (bot := (none : Option Bool)))
        zeroInfCounterexampleU false true ≤ lam :=
    fun lam hlam => sInf_le (hpos_mem lam hlam)
  by_contra hne
  set a := singleChannelLipConst zeroInfCounterexampleDist (idOp (bot := (none : Option Bool)))
    zeroInfCounterexampleU false true
  have ha_pos : 0 < a := pos_iff_ne_zero.mpr hne
  obtain ⟨lam, h0_lt_lam, hlam_lt_a⟩ := exists_between ha_pos
  exact not_lt_of_ge (hle_pos lam h0_lt_lam) hlam_lt_a

/-- Yet `λ = 0` is NOT feasible because `d_false(x, y) = ∞`, `0 * ∞ = 0`, while `d_true(x, y) = 1`. -/
theorem zeroInfCounterexample_zero_not_mem :
    (0 : ENNReal) ∉ SingleChannelLipFeasible zeroInfCounterexampleDist
      (idOp (bot := (none : Option Bool))) zeroInfCounterexampleU false true := by
  intro h0
  have hle := h0 (some false) (by simp [zeroInfCounterexampleU])
    (some true) (by simp [zeroInfCounterexampleU])
  simp [zeroInfCounterexampleDist] at hle

/--
`HC02-P23`: Explicit counterexample proving that in a legal extended gauge space with
a legal operator `ϕ` and nonempty valid `U ⊆ dom(ϕ)`, one can have `L̲_{i → j}(ϕ; U) = 0`
while `0 ∉ S_{i → j}(ϕ; U)`.
-/
theorem exists_zero_singleChannelLipConst_not_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i : I, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
      singleChannelLipConst d ϕ U i j = 0 ∧
      (0 : ENNReal) ∉ SingleChannelLipFeasible d ϕ U i j :=
  ⟨Option Bool, Bool, none, inferInstance, inferInstance,
    zeroInfCounterexampleDist, zeroInfCounterexample_extendedPseudoMetric,
    idOp, zeroInfCounterexampleU, false, true,
    zeroInfCounterexampleU_nonempty, zeroInfCounterexampleU_subset_dom,
    zeroInfCounterexample_const_eq_zero, zeroInfCounterexample_zero_not_mem⟩

/-- Remark `#h-57de7918859a9de2` (`HC02-D08` separation note): the single-channel constant
`L̲_{i → j}(ϕ; U)` is genuinely distinct from a Lip matrix entry `[L]_{i → j}`:
in a legal extended gauge space, there exists `L ∈ ℒ(ϕ)|_U` with `L_{i → j} = 0`
while `L̲_{i → j}(ϕ; U) = +∞`. -/
theorem exists_singleChannelLipConst_ne_lipMatrix_entry :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i : I, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) (i j : I),
      L ∈ RestrictedLipSet d ϕ U ∧
      L i j = 0 ∧
      singleChannelLipConst d ϕ U i j = ⊤ ∧
      singleChannelLipConst d ϕ U i j ≠ L i j := by
  let d : Bool → Option Bool → Option Bool → ENNReal
    | false, x, y => if x = y then 0 else if x = none ∨ y = none then ⊤ else 0
    | true, x, y => if x = y then 0 else if x = none ∨ y = none then ⊤ else 1
  have hd : ∀ i : Bool, ExtendedPseudoMetric (Option Bool) none (d i) := by
    intro i
    cases i with
    | false =>
        refine
          { nonabsorbing := ⟨some false, Option.some_ne_none false⟩
            dist_self := fun x => by simp [d]
            symm := fun x y => by cases x <;> cases y <;> simp [d]
            triangle := fun x y z => by
              cases x with
              | none => cases y <;> cases z <;> simp [d]
              | some a =>
                  cases y with
                  | none => cases z <;> simp [d]
                  | some b =>
                      cases z with
                      | none => simp [d]
                      | some c => cases a <;> cases b <;> cases c <;> simp [d]
            isolate_bot := fun x hx => by
              cases x with
              | none => exact absurd rfl hx
              | some a => simp [d] }
    | true =>
        exact zeroInfCounterexample_extendedPseudoMetric true
  have hL : idMatrix ∈ RestrictedLipSet d (idOp (bot := (none : Option Bool)))
      zeroInfCounterexampleU := by
    refine ⟨zeroInfCounterexampleU_subset_dom, ?_⟩
    intro x _ y _ j
    rw [Finset.sum_eq_single j]
    · simp [idOp]
    · intro k _ hkj
      rw [idMatrix_apply_ne hkj, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have htop : singleChannelLipConst d (idOp (bot := (none : Option Bool)))
      zeroInfCounterexampleU false true = ⊤ := by
    have hpair := singleChannelLipFeasible_eq_empty_of_zero_pos d (idOp (bot := none))
      zeroInfCounterexampleU false true
      (x := some false) (y := some true)
      (by simp [zeroInfCounterexampleU]) (by simp [zeroInfCounterexampleU])
      (by simp [d]) (by simp [d])
    exact hpair.2
  have h0 : idMatrix false true = 0 := idMatrix_apply_ne (by decide)
  refine ⟨Option Bool, Bool, none, inferInstance, inferInstance, d, hd,
    idOp, zeroInfCounterexampleU, idMatrix, false, true, hL, h0, htop, ?_⟩
  rw [htop, h0]
  exact ENNReal.top_ne_zero

/-! ### 4. Zero-Entry Removal and Row/Column/Diagonal Simplifications (HC02-P25–P28) -/

/--
`HC02-P25` (part 1): If `L_{i → j} = 0`, then `L_{i → j} * d_i(x, y) = 0`
even when `d_i(x, y) = +∞` (by `0 * ∞ = 0` in `ENNReal`).
-/
theorem zero_entry_term_eq_zero {X I : Type}
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) {i j : I}
    (h0 : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by
  rw [h0, zero_mul]

/--
`HC02-P25` (part 2, `DecidableEq`-free form):
If `L_{i → j} = 0`, any finset `s : Finset I` containing all `r ≠ i` (for instance `I \ {i}`)
gives the exact same output-`j` sum, removing input `i` even when `d_i(x, y) = +∞`.
-/
theorem sum_eq_sum_of_zero_entry {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) {i j : I}
    (h0 : L i j = 0) (s : Finset I) (hs : ∀ r : I, r ≠ i → r ∈ s) (x y : X) :
    (∑ k : I, L k j * d k x y) = ∑ k ∈ s, L k j * d k x y := by
  symm
  refine Finset.sum_subset (Finset.subset_univ s) ?_
  intro k _ hks
  have hki : k = i := by
    by_contra hne
    exact hks (hs k hne)
  subst hki
  exact zero_entry_term_eq_zero d L h0 x y

/--
`HC02-P25` (part 2, `Finset.erase` form):
If `L_{i → j} = 0`, the `i`-th input term can be erased from the output-`j` sum.
-/
theorem sum_erase_of_zero_entry {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) {i j : I}
    (h0 : L i j = 0) (x y : X) :
    (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y :=
  sum_eq_sum_of_zero_entry d L h0 (Finset.univ.erase i) (fun r hr => by simp [hr]) x y

/--
`HC02-P25` (certificate inequality form, `DecidableEq`-free):
If `L ∈ ℒ(ϕ)|_U` and `L_{i → j} = 0`, input `d_i` can be omitted from the `d_j` upper bound.
-/
theorem restrictedLip_of_zero_entry_compl {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (h0 : L i j = 0) (s : Finset I) (hs : ∀ r : I, r ≠ i → r ∈ s) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ s, L k j * d k x y := by
  intro x hx y hy
  rw [← sum_eq_sum_of_zero_entry d L h0 s hs x y]
  exact hL.2 x hx y hy j

/--
`HC02-P25` (certificate inequality form with `Finset.univ.erase`):
If `L ∈ ℒ(ϕ)|_U` and `L_{i → j} = 0`, input `d_i` does not participate in the `d_j` upper bound.
-/
theorem restrictedLip_erase_of_zero_entry {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (h0 : L i j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y :=
  restrictedLip_of_zero_entry_compl d ϕ U hL h0 (Finset.univ.erase i) (fun r hr => by simp [hr])

/--
`HC02-P26` (line 313): If `L ∈ ℒ(ϕ)|_U` and row `j` is supported at a single input `i`
(`∀ k ≠ i, L_{k → j} = 0`, where `i` need not equal `j`), then
`d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} * d_i(x, y)` for all `x, y ∈ U`.
-/
theorem restrictedLip_of_rowSparse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hrow : RowSparse L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [hrow k hki, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hsum]
  exact hL.2 x hx y hy j

/-- Corollary of `HC02-P26`: a row-sparse entry `L_{i → j}` is a feasible single-channel scalar
constant, so `L̲_{i → j}(ϕ; U) ≤ L_{i → j}`. -/
theorem rowSparse_entry_mem_singleChannel {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hrow : RowSparse L i j) :
    L i j ∈ SingleChannelLipFeasible d ϕ U i j ∧
      singleChannelLipConst d ϕ U i j ≤ L i j := by
  have hmem : L i j ∈ SingleChannelLipFeasible d ϕ U i j :=
    restrictedLip_of_rowSparse d ϕ U hL hrow
  exact ⟨hmem, sInf_le hmem⟩

/-- Operator-level consequence of row decoupling (`HC02-P26`): if `ϕ` is row-decoupled
at output `j`, some certificate `L ∈ ℒ(ϕ)|_U` and input `i` yield the scalar bound
`d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} * d_i(x, y)`. -/
theorem isRowDecoupled_scalar_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I)
    (hdec : IsRowDecoupled d ϕ U j) :
    ∃ L ∈ RestrictedLipSet d ϕ U, ∃ i : I,
      RowSparse L i j ∧
      ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  rcases hdec with ⟨L, hL, i, hrow⟩
  exact ⟨L, hL, i, hrow, restrictedLip_of_rowSparse d ϕ U hL hrow⟩

/--
`HC02-P27` (line 315): If `L ∈ ℒ(ϕ)|_U` has column `i` supported at most at output `j`
(`∀ k ≠ j, L_{i → k} = 0`), then for every `k ≠ j` and all `x, y ∈ U`,
`L_{i → k} * d_i(x, y) = 0`, and input `d_i` contributes nothing to the output-`k` bound
(i.e. every `s : Finset I` covering `I \ {i}` already bounds `d_k(ϕ(x), ϕ(y))`).
-/
theorem colSparse_zero_contribution {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hcol : ColSparse L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      L i k * d i x y = 0 ∧
      ∀ s : Finset I, (∀ r : I, r ≠ i → r ∈ s) →
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ r ∈ s, L r k * d r x y := by
  intro k hkj x hx y hy
  have h0 : L i k = 0 := hcol k hkj
  refine ⟨zero_entry_term_eq_zero d L h0 x y, ?_⟩
  intro s hs
  exact restrictedLip_of_zero_entry_compl d ϕ U hL h0 s hs x hx y hy

/-- `Finset.erase` variant of `HC02-P27`. -/
theorem colSparse_erase_bound {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hcol : ColSparse L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      L i k * d i x y = 0 ∧
      d k (ϕ.func x) (ϕ.func y) ≤ ∑ r ∈ Finset.univ.erase i, L r k * d r x y := by
  intro k hkj x hx y hy
  have h0 : L i k = 0 := hcol k hkj
  exact ⟨zero_entry_term_eq_zero d L h0 x y,
    restrictedLip_erase_of_zero_entry d ϕ U hL h0 x hx y hy⟩

/--
`HC02-P28` (lines 317–319): If `L ∈ ℒ(ϕ)|_U` is diagonal (`∀ i ≠ j, L_{i → j} = 0`),
then every component `j ∈ I` satisfies the scalar upper bound
`d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} * d_j(x, y)` for all `x, y ∈ U`.
-/
theorem restrictedLip_of_diagonal {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    (hdiag : IsDiagonalMatrix L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact restrictedLip_of_rowSparse d ϕ U hL ((isDiagonalMatrix_iff_forall_rowSparse L).mp hdiag j)

/-! ### 5. Two-Sided Diagonal Scalar Bounds and Finite Branch (HC02-P29, HC02-P30) -/

/--
OET anchor: h-6a98a58b5bc95360 (`HC02-P29`)
**Lemma (Two-sided scalar bound from a diagonal-only Lip row)**:
Given `L ∈ ℒ(ϕ)|_U` and `K ∈ 𝒦(ϕ)|_U`, assuming ONLY that row `j` of `L` is supported
on the diagonal (`∀ k ≠ j, L_{k → j} = 0`), every `x, y ∈ U` satisfies
`K_{j → j} * d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} * d_j(x, y)`.
-/
theorem diagonal_two_sided_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U)
    (hK : K ∈ CoLipSet d ϕ U)
    (j : I) (hrow : RowSparse L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, restrictedLip_of_rowSparse d ϕ U hL hrow x hx y hy⟩
  calc
    K j j * d j x y
        ≤ ∑ k : I, K k j * d k x y :=
          Finset.single_le_sum (f := fun k => K k j * d k x y)
            (fun _ _ => zero_le _) (Finset.mem_univ j)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
`HC02-P30` (part 1, line 338): If the diagonal-row condition on `L` holds for all `j ∈ I`,
then the two-sided scalar inequality holds simultaneously for every component `j ∈ I`.
-/
theorem componentwise_two_sided_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U)
    (hK : K ∈ CoLipSet d ϕ U)
    (hrow_all : ∀ j : I, RowSparse L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  fun j => diagonal_two_sided_bound d ϕ U hL hK j (hrow_all j)

/--
`HC02-P30` (part 2, finite-coefficient branch, line 338):
If in addition `L_{j → j} < ∞` and `K_{j → j} < ∞` for all `j ∈ I`, then the componentwise
two-sided bounds have finite nonnegative real (`NNReal`) scaling coefficients `k, l`.
-/
theorem componentwise_finite_two_sided_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U)
    (hK : K ∈ CoLipSet d ϕ U)
    (hrow_all : ∀ j : I, RowSparse L j j)
    (hL_fin : ∀ j : I, L j j < ⊤)
    (hK_fin : ∀ j : I, K j j < ⊤) :
    ∀ j : I, ∃ k l : NNReal,
      (k : ENNReal) = K j j ∧ (l : ENNReal) = L j j ∧
      ∀ x ∈ U, ∀ y ∈ U,
        (k : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ (l : ENNReal) * d j x y := by
  intro j
  refine ⟨(K j j).toNNReal, (L j j).toNNReal,
    ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne, ?_⟩
  rw [ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne]
  exact componentwise_two_sided_bound d ϕ U hL hK hrow_all j

/-! ### 6. Positive co-Lip Distinguishability Preservation & Zero-Distance Reflection (HC02-P31, P32) -/

/--
OET anchor: h-f82672ec0dd48f28 (i) (`HC02-P31`)
**Proposition (Distinguishability preservation along positive co-Lip channels)**:
If `K ∈ 𝒦(ϕ)|_U` and `K_{i → j} > 0`, then for all `x, y ∈ U`,
`d_i(x, y) > 0 → d_j(ϕ(x), ϕ(y)) > 0`.
-/
theorem coLip_preserves_distinguishability {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ U)
    {i j : I} (hpos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdpos
  have hmul_pos : 0 < K i j * d i x y := ENNReal.mul_pos hpos.ne' hdpos.ne'
  have hle : K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
    calc
      K i j * d i x y
          ≤ ∑ k : I, K k j * d k x y :=
            Finset.single_le_sum (f := fun k => K k j * d k x y)
              (fun _ _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
  exact lt_of_lt_of_le hmul_pos hle

/--
OET anchor: h-f82672ec0dd48f28 (ii) (`HC02-P32`)
**Proposition (Reflection of gauge zero-distance relation from positive diagonal co-Lip)**:
If `K ∈ 𝒦(ϕ)|_U` and `K_{j → j} > 0` for all `j ∈ I`, then for all `x, y ∈ U`,
`ϕ(x) ∼_G ϕ(y) → x ∼_G y`.
-/
theorem coLip_reflects_gaugeZeroRelated {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ U)
    (hdiag_pos : ∀ j : I, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout : 0 < d j (ϕ.func x) (ϕ.func y) :=
    coLip_preserves_distinguishability d ϕ U hK (hdiag_pos j) x hx y hy hpos
  rw [hrel j] at hout
  exact lt_irrefl 0 hout

end OetCh02
