以下形式化基于 Zhe Li（Glen Li）的 *The Operator Evolution Theory* 选段，原作品采用 CC BY 4.0 许可。全部 8 项义务均已完成，并通过 `lake build`、`lake env lean Main.lean` 及公理依赖审计。

```lean filename=formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean
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
```

```lean filename=Main.lean
import formal_oet.vol_01.ch_02_operator_bounds.operator_bounds
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedLipMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lipCertificates"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedLipCertificates"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.isLipMatrix_iff"
        }
      ],
      "representation": {
        "objects": "BoundMatrix I 是 I×I 的 ENNReal 矩阵，L j i 对应原文 L_{i→j}。lipCertificates 和 restrictedLipCertificates 分别表示全域证书族与 U 上的受限证书族。",
        "parameters": "X、bot、d、φ、U、L 分别对应底空间、吸收元、分量伪度量族、算子、限制域和候选 Lip 矩阵；[Fintype I] 表示有限指标集。全域谓词取 U=dom φ。",
        "quantifiers": "受限谓词包含 U⊆dom φ，并逐一量化 x∈U、y∈U、j∈I；右端为 ∑ i, L j i * d i x y。isLipMatrix_iff 给出全域谓词在 dom φ 上的逐项展开。",
        "conclusion": "完整表示原文全域/受限 Lip 不等式及其合法矩阵集合，未预设任何极值证书或额外分离性。"
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedCoLipMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.restrictedCoLipCertificates"
        }
      ],
      "representation": {
        "objects": "K j i 对应 K_{i→j}；restrictedCoLipCertificates d φ U 是原文 K(φ)|_U 的集合表示。",
        "parameters": "d、φ、U、K 与原文相同；U.Nonempty 显式表示 U≠∅，并同时保留 U⊆dom φ。",
        "quantifiers": "对所有 x∈U、y∈U、j∈I，要求 ∑ i, K j i * d i x y ≤ d j (φ.func x) (φ.func y)。",
        "conclusion": "证书族成员关系包含原文特别强调的非空性条件以及完整的受限 co-Lip 下界不等式。"
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.BoundMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.boundMatrix_mul_channel_apply"
        }
      ],
      "representation": {
        "objects": "采用 mathlib 的 Matrix I I ENNReal；第一个索引是输出分量/行，第二个索引是输入分量/列，因此 L j i=L_{i→j}。",
        "parameters": "M、N 是两个同指标矩阵，i 是输入指标，j 是输出指标；矩阵条目和乘法均在 ENNReal 中解释。",
        "quantifiers": "定理对任意 M、N、i、j 给出逐条目公式。",
        "conclusion": "(M*N) j i = ∑ k, M j k * N k i，正是原文 [(M·N)]_{i→j}=∑k M_{k→j}N_{i→k}，并采用标准 Matrix.mul。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.ComponentChannel"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.channelEntry"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.SingleInputRow"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagonalBoundMatrix"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.diagonal_singleInputRow"
        }
      ],
      "representation": {
        "objects": "ComponentChannel 以 input、output 两个字段表示有序通道 (i,j)；channelEntry L c=L c.output c.input。SingleInputRow L i j 表示第 j 行除输入 i 外均为零，IsDiagonalBoundMatrix 表示所有非对角通道条目为零。",
        "parameters": "L 为界矩阵，i、j 分别为输入与输出分量；对角情形取二者相同。",
        "quantifiers": "单行稀疏量化为 ∀ k, k≠i → L j k=0；对角条件量化为 ∀ i j, i≠j → L j i=0。",
        "conclusion": "diagonal_singleInputRow 证明每个对角行都是对角同分量通道的单输入行，为原文对角特例提供直接对应。"
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.weighted_row_eq_single_input"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_bound_of_singleInputRow"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_bound_of_diagonal"
        }
      ],
      "representation": {
        "objects": "hrow 是 SingleInputRow L i j；hL 是 L 属于 U 上的合法 Lip 证书族。",
        "parameters": "x、y 是 U 中任意两点；v 在辅助等式中表示任意 ENNReal 输入权值，并在主定理中取 v k=d k x y。",
        "quantifiers": "主定理以 hx、hy 的柯里化形式表达 ∀x,y∈U；对角定理进一步对每个输出分量 i 给出结论。",
        "conclusion": "先证 ∑k,L j k*v k=L j i*v i，再得 d j(φx,φy)≤L j i*d i(x,y)；对角特例为 d i(φx,φy)≤L i i*d i(x,y)。"
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_single_input_le"
        },
        {
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.positive_output_dist_of_positive_coLip"
        }
      ],
      "representation": {
        "objects": "K 是 U 上的合法受限 co-Lip 证书，K j i 对应通道 i→j 的条目。",
        "parameters": "hKij:0<K j i，hx:x∈U，hy:y∈U，hd:0<d i x y；未增加距离有限性假设，允许 ENNReal 的 ∞ 条目。",
        "quantifiers": "对任意合法 K、通道 i,j 和 U 中任意 x,y 成立。",
        "conclusion": "辅助引理给出 K j i*d i(x,y)≤d j(φx,φy)，主定理得到 0<d j(φx,φy)，即正 co-Lip 通道保持正距离。"
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.reflects_gaugeZeroRelated_of_positive_diagonal_coLip"
        }
      ],
      "representation": {
        "objects": "GaugeZeroRelated 直接复用冻结模块中的族零距关系；hdiag:∀j,0<K j j 表示全部同分量 co-Lip 通道严格为正。",
        "parameters": "K、φ、U 与 CH02-P20 相同，x、y 为 U 中点；hzero 是 φ(x) 与 φ(y) 的全分量零距假设。",
        "quantifiers": "结论展开为 ∀j,d j x y=0；证明固定任意 j，并由 CH02-P20 排除 d j x y>0。",
        "conclusion": "由 GaugeZeroRelated d (φx) (φy) 推出 GaugeZeroRelated d x y。结论没有加强为 x=y，也不需要族分离性。"
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
          "file": "formal_oet/vol_01/ch_02_operator_bounds/operator_bounds.lean",
          "name": "formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound_of_diagonal_input_row"
        }
      ],
      "representation": {
        "objects": "L、K 分别是 U 上的 Lip 与 co-Lip 证书；hrow:∀k,k≠j→L j k=0 是习题只保留对角输入项的条件。",
        "parameters": "d、φ、U、j 与习题一致，x、y 通过 hx、hy 量化于 U；没有加入额外的有限性或分离性前提。",
        "quantifiers": "对任意合法证书、满足行稀疏条件的输出分量 j 以及任意 x,y∈U 成立。",
        "conclusion": "以合取同时给出 K j j*d j(x,y)≤d j(φx,φy) 和 d j(φx,φy)≤L j j*d j(x,y)，完整对应习题 2.2 的标量双侧界。"
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D02",
        "CH02-D03",
        "CH02-D07",
        "CH02-P19",
        "CH02-P20"
      ]
    }
  ]
}
```