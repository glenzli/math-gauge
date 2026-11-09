8 项义务均已完成，并通过指定 Lean/mathlib 环境的内核检查。公理依赖仅含 `propext`、`Classical.choice`、`Quot.sound`。以下是全部新增项目文件，与附件中保持原样的 `formal_oet/` 配合使用。

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```toml filename=lakefile.toml
name = "lch01"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "formal_oet"

[[lean_lib]]
name = "LCH01"

[[lean_lib]]
name = "Main"
```

```lean filename=LCH01/MatrixChannels.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Source: Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §§2.1–2.2, v1.0.0, DOI 10.5281/zenodo.21457931.
ORCID: https://orcid.org/0009-0006-6536-3453
Official work: https://glenzli.com/books/oet/
Source repository: https://gitlab.com/glenzli/oet-public
License: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/
This is a new Lean formalization of the supplied mathematical text.
The supplied foundation modules are imported without modification.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-- Rows are outputs and columns are inputs; entries may be infinite. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- `entry M i j` denotes the textbook coefficient `M_{i → j}`. -/
def entry {I : Type} (M : ChannelMatrix I) (i j : I) : ENNReal := M j i

/-- `M₂` acts after `M₁`, using ordinary matrix multiplication. -/
noncomputable def matrix_comp {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) : ChannelMatrix I := M₂ * M₁

theorem matrix_comp_entry {I : Type} [Fintype I]
    (M₂ M₁ : ChannelMatrix I) (i j : I) :
    entry (matrix_comp M₂ M₁) i j =
      ∑ k : I, entry M₂ k j * entry M₁ i k := by
  rfl

/-- A component channel is the ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

/-- Output row `j` has no input contribution except possibly input `i`. -/
def SingleInputRow {I : Type} (M : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → entry M k j = 0

/-- All off-diagonal input/output coefficients vanish. -/
def Diagonal {I : Type} (M : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → entry M i j = 0

theorem diagonal_singleInputRow {I : Type} {M : ChannelMatrix I}
    (hM : Diagonal M) (j : I) : SingleInputRow M j j := by
  intro k hk
  exact hM k j hk

section Certificates

variable {X I : Type} [Fintype I] {bot : X}

/-- The restricted Lip predicate includes the required domain inclusion. -/
def IsRestrictedLip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i : I, entry L i j * d i x y

/-- The full Lip predicate evaluates every pair in the operator domain. -/
def IsLip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : ChannelMatrix I) : Prop :=
  IsRestrictedLip d φ (dom φ) L

def lipCertificates (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (ChannelMatrix I) := {L | IsLip d φ L}

def restrictedLipCertificates (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {L | IsRestrictedLip d φ U L}

/-- Nonemptiness is part of every restricted co-Lip certificate. -/
def IsRestrictedCoLip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, entry K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipCertificates (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : Set (ChannelMatrix I) :=
  {K | IsRestrictedCoLip d φ U K}

end Certificates

end LCH01
```

```lean filename=LCH01/ChannelBounds.lean
import LCH01.MatrixChannels

/-!
Formalization of the selected channel results in Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, Volume I, §2.2 and Exercise 2.2.
See MatrixChannels.lean for source attribution and the CC BY 4.0 license.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} [Fintype I] {bot : X}

/-- The sum in a row with a single possible input reduces to that term. -/
theorem single_input_row_sum (M : ChannelMatrix I) (v : I → ENNReal)
    (i j : I) (hrow : SingleInputRow M i j) :
    (∑ k : I, entry M k j * v k) = entry M i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [hrow k hk, zero_mul]
  · simp

/-- Each nonnegative summand is bounded by the co-Lip output distance. -/
theorem colip_entry_le {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {K : ChannelMatrix I} (hK : IsRestrictedCoLip d φ U K)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    entry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  calc
    entry K i j * d i x y ≤ ∑ k : I, entry K k j * d k x y :=
      Finset.single_le_sum (f := fun k : I => entry K k j * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

section GaugeSpace

variable (d : I → X → X → ENNReal)

/-- CH02-P19: a sparse output row gives a scalar upper bound. -/
theorem lip_single_input [Nonempty I]
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : IsRestrictedLip d φ U L)
    {i j : I} (hrow : SingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L i j * d i x y := by
  intro x hx y hy
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, entry L k j * d k x y :=
      hL.2 x hx y hy j
    _ = entry L i j * d i x y :=
      single_input_row_sum L (fun k => d k x y) i j hrow

/-- CH02-P19, diagonal special case, simultaneously for every output. -/
theorem lip_diagonal [Nonempty I]
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L : ChannelMatrix I} (hL : IsRestrictedLip d φ U L)
    (hdiag : Diagonal L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro j
  exact lip_single_input d hd hL (diagonal_singleInputRow hdiag j)

/-- CH02-P20: a positive co-Lip channel preserves positive distance. -/
theorem positive_colip_channel [Nonempty I]
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : IsRestrictedCoLip d φ U K)
    {i j : I} (hpos : 0 < entry K i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d i x y → 0 < d j (φ.func x) (φ.func y) := by
  intro x hx y hy hxy
  exact lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hxy.ne')
    (colip_entry_le hK hx hy i j)

/-- CH02-P21: positive diagonal entries reflect the family zero relation. -/
theorem colip_reflects_gauge_zero [Nonempty I]
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {K : ChannelMatrix I} (hK : IsRestrictedCoLip d φ U K)
    (hdiag : ∀ j : I, 0 < entry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout := positive_colip_channel d hd hK (hdiag j) x hx y hy hpos
  rw [hzero j] at hout
  exact (lt_irrefl (0 : ENNReal)) hout

/-- CH02-P25 (Exercise 2.2): the diagonal scalar two-sided bound. -/
theorem scalar_two_sided [Nonempty I]
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X}
    {L K : ChannelMatrix I}
    (hL : IsRestrictedLip d φ U L) (hK : IsRestrictedCoLip d φ U K)
    (j : I) (hrow : SingleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro x hx y hy
  exact ⟨colip_entry_le hK hx hy j j,
    lip_single_input d hd hL hrow x hx y hy⟩

end GaugeSpace

end LCH01
```

```lean filename=Main.lean
import LCH01.MatrixChannels
import LCH01.ChannelBounds
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
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.IsRestrictedLip"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.IsLip"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.lipCertificates"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.restrictedLipCertificates"}
      ],
      "representation": {
        "objects": "沿用冻结的 Operator X bot、dom 与 ENNReal；d i 表示分量伪度量。",
        "parameters": "φ、U、L、有限指标类型 I；谓词可对任意 d 定义，目标命题显式保留 Nonempty I 及 hd : ∀ i, ExtendedPseudoMetric X bot (d i)。",
        "quantifiers": "受限谓词包含 U ⊆ dom φ，并量化所有 x∈U、y∈U、j∈I；全域谓词取 U=dom φ。",
        "conclusion": "上界为 d j (φ.func x) (φ.func y) ≤ ∑ i, entry L i j * d i x y；两个 Set 分别收集所有合法全域和受限矩阵，不选择极值矩阵。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.IsRestrictedCoLip"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.restrictedCoLipCertificates"},
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.colip_entry_le"}
      ],
      "representation": {
        "objects": "K 是 ENNReal 矩阵；restrictedCoLipCertificates 是全部合法受限 co-Lip 矩阵的集合。",
        "parameters": "d、φ、U、K 与有限 I；U.Nonempty 和 U ⊆ dom φ 均直接包含在合法性谓词中。",
        "quantifiers": "对每个 x∈U、y∈U、输出 j，要求下界；辅助引理还任取输入 i。",
        "conclusion": "∑ i, entry K i j * d i x y ≤ d j (φ.func x) (φ.func y)；辅助引理证明其中每一项也不超过输出距离。空域没有合法 co-Lip 证书。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.ChannelMatrix"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.entry"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.matrix_comp"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.matrix_comp_entry"}
      ],
      "representation": {
        "objects": "ChannelMatrix I = Matrix I I ENNReal，采用通常的行列矩阵。",
        "parameters": "entry M i j = M j i，故 i 是输入列、j 是输出行；I 在乘法中有限。",
        "quantifiers": "matrix_comp_entry 对所有 M₂、M₁、i、j 成立。",
        "conclusion": "matrix_comp M₂ M₁ = M₂ * M₁，且其 i→j 条目等于 ∑ k, entry M₂ k j * entry M₁ i k；允许无限条目并使用 ENNReal 的 0*∞=0 算术。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.ComponentChannel"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.SingleInputRow"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.Diagonal"},
        {"file": "LCH01/MatrixChannels.lean", "name": "LCH01.diagonal_singleInputRow"}
      ],
      "representation": {
        "objects": "ComponentChannel I = I×I，依次记录输入 i 和输出 j。",
        "parameters": "SingleInputRow M i j 描述第 j 输出行只可能保留第 i 输入项；Diagonal M 描述全矩阵对角性。",
        "quantifiers": "单行稀疏要求所有 k≠i 的 entry M k j 为零；对角性要求所有 i≠j 的 entry M i j 为零。",
        "conclusion": "对角矩阵在每个 j 上满足 SingleInputRow M j j；保留项允许为零。对应的距离化简由 CH02-P19 完成。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.single_input_row_sum"},
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.lip_single_input"},
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.lip_diagonal"}
      ],
      "representation": {
        "objects": "给定合法受限 Lip 矩阵 L，使用 SingleInputRow 或 Diagonal 表示原文零条目条件。",
        "parameters": "目标定理显式保留有限非空 I、全部规范公理 hd、φ、U、L；U ⊆ dom φ 来自 hL。",
        "quantifiers": "单行结论对任意输入 i、输出 j、x∈U、y∈U 成立；对角结论对所有 j 同时成立。",
        "conclusion": "先证明 ∑ k, entry L k j * v k = entry L i j * v i，再得到 d j (φ x) (φ y) ≤ entry L i j * d i x y；对角时 i=j。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.positive_colip_channel"}
      ],
      "representation": {
        "objects": "φ 在 U 上具有合法 co-Lip 矩阵 K；距离与系数均取 ENNReal。",
        "parameters": "显式保留有限非空 I 与 hd；hK 包含 U 非空、U ⊆ dom φ 及全部下界；另要求 0 < entry K i j。",
        "quantifiers": "任取输入 i、输出 j、x∈U、y∈U。",
        "conclusion": "0 < d i x y 蕴含 0 < d j (φ.func x) (φ.func y)，包括正系数或输入距离为 ∞ 的情形。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.colip_reflects_gauge_zero"}
      ],
      "representation": {
        "objects": "直接沿用冻结前置模块的 GaugeZeroRelated d，即所有分量距离同时为零。",
        "parameters": "有限非空 I、hd、合法受限 co-Lip 矩阵 K，且 ∀ j, 0 < entry K j j；不要求 K 的非对角项为零，也不要求规范族分离。",
        "quantifiers": "对每个 x∈U、y∈U，从所有输出分量距离为零推出所有输入分量距离为零。",
        "conclusion": "GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y；结论没有加强为 x=y。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.scalar_two_sided"}
      ],
      "representation": {
        "objects": "同一个 φ、U 上的合法 Lip 矩阵 L 与合法 co-Lip 矩阵 K。",
        "parameters": "有限非空 I、hd 与指定输出 j；SingleInputRow L j j 正是 ∀ k≠j, L_{k→j}=0；U 的非空性来自 co-Lip 合法性。",
        "quantifiers": "对所有 x∈U、y∈U，同时给出上下界。",
        "conclusion": "用合取表示标量双侧不等式：entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) 且 d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y；不对 K 的其他条目施加稀疏条件。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19"]
    }
  ]
}
```