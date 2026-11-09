以下为完整 Lean 源码与对齐文件。项目已在 Lean 4.29.1、指定 mathlib 下通过 `lake build` 与 `lean Main.lean` 检查。

```lean filename=OperatorBounds/Defs.lean
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
```

```lean filename=OperatorBounds/Basic.lean
import OperatorBounds.Defs

set_option linter.unusedSectionVars false

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

namespace formal_oet.ch_02_operator_bounds

section FiniteNonemptyIndex

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I]
variable {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}

/-- A diagonal matrix row reduces to its diagonal entry.  This is the direct
off-diagonal-zero specialization used for same-component channels. -/
theorem diagonal_row_vanishes {L : GaugeMatrix I} {j : I}
    (hdiag : IsDiagonalMatrix L) :
    SingleInputRow L j j := by
  intro k hk
  exact hdiag k j hk

/-- Explicit accessor for the domain condition of a restricted Lip matrix. -/
theorem IsLipMatrixOn.subset_dom {L : GaugeMatrix I} (hL : IsLipMatrixOn d ϕ U L) :
    U ⊆ dom ϕ := hL.1

/-- Explicit accessor for the pointwise Lip inequality of a restricted Lip matrix. -/
theorem IsLipMatrixOn.bound {L : GaugeMatrix I} (hL : IsLipMatrixOn d ϕ U L) :
    LipBoundOn d ϕ U L := hL.2

/-- Explicit accessor for nonemptiness of the domain of a restricted co-Lip matrix. -/
theorem IsCoLipMatrixOn.nonempty {K : GaugeMatrix I} (hK : IsCoLipMatrixOn d ϕ U K) :
    U.Nonempty := hK.1

/-- Explicit accessor for the domain condition of a restricted co-Lip matrix. -/
theorem IsCoLipMatrixOn.subset_dom {K : GaugeMatrix I} (hK : IsCoLipMatrixOn d ϕ U K) :
    U ⊆ dom ϕ := hK.2.1

/-- Explicit accessor for the pointwise co-Lip inequality of a restricted co-Lip
matrix. -/
theorem IsCoLipMatrixOn.bound {K : GaugeMatrix I} (hK : IsCoLipMatrixOn d ϕ U K) :
    CoLipBoundOn d ϕ U K := hK.2.2

/-- Membership in a restricted Lip certificate family is exactly the restricted
Lip predicate. -/
@[simp] theorem mem_lipMatricesOn_iff {L : GaugeMatrix I} :
    L ∈ lipMatricesOn d ϕ U ↔ IsLipMatrixOn d ϕ U L := Iff.rfl

/-- Membership in the global Lip certificate family is exactly the global Lip
predicate. -/
@[simp] theorem mem_lipMatrices_iff {L : GaugeMatrix I} :
    L ∈ lipMatrices d ϕ ↔ IsLipMatrix d ϕ L := Iff.rfl

/-- Membership in a restricted co-Lip certificate family is exactly the restricted
co-Lip predicate, including nonemptiness of `U` and `U ⊆ dom(ϕ)`. -/
@[simp] theorem mem_coLipMatricesOn_iff {K : GaugeMatrix I} :
    K ∈ coLipMatricesOn d ϕ U ↔ IsCoLipMatrixOn d ϕ U K := Iff.rfl

/-- Membership in the global co-Lip certificate family is exactly the global co-Lip
predicate. -/
@[simp] theorem mem_coLipMatrices_iff {K : GaugeMatrix I} :
    K ∈ coLipMatrices d ϕ ↔ IsCoLipMatrix d ϕ K := Iff.rfl

end FiniteNonemptyIndex

end formal_oet.ch_02_operator_bounds
```

```lean filename=OperatorBounds/Theorems.lean
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
```

```lean filename=Main.lean
/-
  LCH01: selected obligations from Chapter 2 of The Operator Evolution Theory.

  The frozen Chapter 1 foundations are imported through `OperatorBounds.Basic`;
  the three local modules below contain the selected definitions and theorems.
-/
import OperatorBounds.Defs
import OperatorBounds.Basic
import OperatorBounds.Theorems

namespace formal_oet.ch_02_operator_bounds

end formal_oet.ch_02_operator_bounds
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
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.LipBoundOn"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.IsLipMatrixOn"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.IsLipMatrix"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.lipMatricesOn"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.lipMatrices"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.IsLipMatrixOn.subset_dom"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.IsLipMatrixOn.bound"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.mem_lipMatricesOn_iff"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.mem_lipMatrices_iff"}
      ],
      "representation": {
        "objects": "X 上的算子 ϕ : Operator X bot，指标集 I 上的矩阵 L : I → I → ENNReal，以及受限域 U : Set X；目标空间即冻结模块中的 Operator 与 ENNReal。",
        "parameters": "[Fintype I] [Nonempty I]、分量伪度量族 d : I → X → X → ENNReal、ϕ、U、L。矩阵条目 L i j 表示原文 L_{i→j}。",
        "quantifiers": "LipBoundOn 为 ∀ x ∈ U, ∀ y ∈ U, ∀ j, d j (ϕ x) (ϕ y) ≤ ∑ i, L i j * d i x y；IsLipMatrixOn 另外显式保留原文的 U ⊆ dom ϕ；全域名 U=dom ϕ 由 IsLipMatrix 表示。",
        "conclusion": "得到受限合法 Lip 矩阵谓词 IsLipMatrixOn 及其证书族 lipMatricesOn，以及全域名谓词 IsLipMatrix 和证书族 lipMatrices；成员关系与谓词严格等价。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.CoLipBoundOn"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.IsCoLipMatrixOn"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.coLipMatricesOn"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.IsCoLipMatrix"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.coLipMatrices"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.IsCoLipMatrixOn.nonempty"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.IsCoLipMatrixOn.subset_dom"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.IsCoLipMatrixOn.bound"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.mem_coLipMatricesOn_iff"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.mem_coLipMatrices_iff"}
      ],
      "representation": {
        "objects": "算子 ϕ : Operator X bot、矩阵 K : I → I → ENNReal 与受限域 U : Set X；K i j 对应 K_{i→j}。",
        "parameters": "[Fintype I] [Nonempty I]、d、ϕ、U、K。原文要求 U 非空且 U ⊆ dom ϕ，这两项均在谓词中显式保留。",
        "quantifiers": "CoLipBoundOn 为 ∀ x ∈ U, ∀ y ∈ U, ∀ j, ∑ i, K i j * d i x y ≤ d j (ϕ x) (ϕ y)；IsCoLipMatrixOn 为 U.Nonempty ∧ U ⊆ dom ϕ ∧ CoLipBoundOn。",
        "conclusion": "得到含非空条件的受限合法 co-Lip 谓词 IsCoLipMatrixOn 及其证书族 coLipMatricesOn；全域名使用 dom ϕ，并因非空条件在 dom ϕ 为空时证书族为空。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.GaugeMatrix"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.matrixEntry"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.outputRow"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.inputColumn"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.matrixMul"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.matrixMul_apply"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.matrixEntry_matrixMul"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.matrixEntry_apply"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.outputRow_apply"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.inputColumn_apply"}
      ],
      "representation": {
        "objects": "指标集 I 上的扩展非负矩阵 GaugeMatrix I := I → I → ENNReal。约定第一个指标 i 是输入分量、第二个指标 j 是输出分量；因此 L i j 是原文的 L_{i→j}，位于输出行 j、输入列 i。",
        "parameters": "I 为有限指标集；matrixMul 需要 [Fintype I]；条目取值 ENNReal，包含 +∞。",
        "quantifiers": "矩阵乘法定义为 matrixMul M₂ M₁ i j = ∑ k, M₂ k j * M₁ i k；其复合参数顺序与原文 M₂ · M₁ 的前后顺序一致。",
        "conclusion": "matrixMul_apply 与 matrixEntry_matrixMul 给出矩阵乘积的指标公式；outputRow/inputColumn 固定原文的行列含义；没有偷偷采用相反的矩阵指标约定。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.ComponentChannel"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.channelInput"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.channelOutput"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.SingleInputRow"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.SingleInputChannel"},
        {"file": "OperatorBounds/Defs.lean", "name": "formal_oet.ch_02_operator_bounds.IsDiagonalMatrix"},
        {"file": "OperatorBounds/Basic.lean", "name": "formal_oet.ch_02_operator_bounds.diagonal_row_vanishes"}
      ],
      "representation": {
        "objects": "分量通道用有序对 ComponentChannel I := I × I 表示，(i,j) 的输入分量为 channelInput，输出分量为 channelOutput；矩阵 L 的同一行与对角支撑性质分别由 SingleInputRow/SingleInputChannel 与 IsDiagonalMatrix 表示。",
        "parameters": "L : GaugeMatrix I；输入输出指标 i j : I；指标集仍为有限非空 I。",
        "quantifiers": "SingleInputRow L i j 定义为 ∀ k, k ≠ i → L k j = 0，即第 j 行除可能出现的 L_{i→j} 外全部为零；IsDiagonalMatrix L 定义为 ∀ i j, i ≠ j → L i j = 0。",
        "conclusion": "刻画原文的分量通道、单输入通道行稀疏性与对角特例；diagonal_row_vanishes 把对角矩阵的每个同分量通道化为相应的 SingleInputRow。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds/Theorems.lean", "name": "formal_oet.ch_02_operator_bounds.lip_single_input_row"},
        {"file": "OperatorBounds/Theorems.lean", "name": "formal_oet.ch_02_operator_bounds.lip_diagonal_same_component"}
      ],
      "representation": {
        "objects": "受限合法 Lip 矩阵 L、算子 ϕ : Operator X bot、受限域 U 与点 x,y : X。",
        "parameters": "[Fintype I] [Nonempty I]、d、ϕ、U、L，以及输出指标 j 与唯一输入指标 i。",
        "quantifiers": "前提为 hL : IsLipMatrixOn d ϕ U L（含 U ⊆ dom ϕ 及逐点 Lip 不等式）、hrow : ∀ k, k ≠ i → L k j = 0、x ∈ U、y ∈ U。结论为 d j (ϕ x) (ϕ y) ≤ L i j * d i x y。对角特例接受 IsDiagonalMatrix L，并对每个 j 得到 d j (ϕ x) (ϕ y) ≤ L j j * d j x y。",
        "conclusion": "证明在单一输入项行中整行求和化为唯一标量项，并单独给出对角线同分量通道的化简约化，完全对应 §2.2 的例外情形。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds/Theorems.lean", "name": "formal_oet.ch_02_operator_bounds.coLip_pos_preserves_pos"}
      ],
      "representation": {
        "objects": "合法受限 co-Lip 矩阵 K、算子 ϕ、受限域 U 与点 x,y : X。",
        "parameters": "[Fintype I] [Nonempty I]、d、ϕ、U、K、输入指标 i、输出指标 j。",
        "quantifiers": "前提为 hK : IsCoLipMatrixOn d ϕ U K（显含 U 非空、U ⊆ dom ϕ 与逐点 co-Lip 下界）、0 < K i j、x ∈ U、y ∈ U、0 < d i x y。",
        "conclusion": "得到 0 < d j (ϕ x) (ϕ y)，即正 co-Lip 通道 i→j 保持严格正距离；证明用非负有限和的单项下界与 co-Lip 不等式。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds/Theorems.lean", "name": "formal_oet.ch_02_operator_bounds.coLip_diagonal_reflects_zero_related"}
      ],
      "representation": {
        "objects": "合法受限 co-Lip 矩阵 K、算子 ϕ、受限域 U 与点 x,y : X；族零距关系使用冻结模块的 GaugeZeroRelated。",
        "parameters": "[Fintype I] [Nonempty I]、d、ϕ、U、K；对角正性前提 ∀ j, 0 < K j j。",
        "quantifiers": "前提为 hK : IsCoLipMatrixOn d ϕ U K、hdiag : ∀ j, 0 < K j j、x ∈ U、y ∈ U，以及 GaugeZeroRelated d (ϕ.func x) (ϕ.func y)。结论是 GaugeZeroRelated d x y。",
        "conclusion": "对每个 j，由 P20 的严格正性保持与输出零距矛盾，推出 d j x y = 0；最终只断言 x∼_G y，未加强为 x = y。这正是原文“不预设族分离性”的强度。"
      },
      "dependencies": ["CH02-D02", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds/Theorems.lean", "name": "formal_oet.ch_02_operator_bounds.scalar_two_sided_bound"}
      ],
      "representation": {
        "objects": "同一算子 ϕ 的合法 Lip 矩阵 L 与合法受限 co-Lip 矩阵 K，受限域 U，点 x,y : X，以及输出指标 j。",
        "parameters": "[Fintype I] [Nonempty I]、d、ϕ、U、L、K、j；行稀疏前提 SingleInputRow L j j 即 ∀ k, k ≠ j → L k j = 0。",
        "quantifiers": "前提为 hL : IsLipMatrixOn d ϕ U L、hK : IsCoLipMatrixOn d ϕ U K、hrow : SingleInputRow L j j、x ∈ U、y ∈ U。结论为合取 K j j * d j x y ≤ d j (ϕ x) (ϕ y) ∧ d j (ϕ x) (ϕ y) ≤ L j j * d j x y。",
        "conclusion": "下界由 co-Lip 的单项项 K_{j→j} d_j 小于等于全行和得到；上界调用 P19 的单输入项行化简；因此精确给出习题 2.2 的标量双侧界。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```