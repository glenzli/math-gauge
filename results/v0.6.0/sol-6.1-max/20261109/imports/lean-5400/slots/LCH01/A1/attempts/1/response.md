全部 8 项已完成，并通过指定 Lean 4.29.1、mathlib 提交的离线 Lake 构建。公理审计仅包含 `propext`、`Classical.choice`、`Quot.sound`。以下为全部新增文件，与冻结的 `formal_oet/` 附件同置。

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
name = "Main"
roots = ["Main"]

[[lean_lib]]
name = "LCH01"

[[lean_lib]]
name = "formal_oet"
```

```json filename=lake-manifest.json
{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {"url": "https://github.com/leanprover-community/mathlib4.git", "type": "git", "subDir": null, "scope": "", "rev": "5e932f97dd25535344f80f9dd8da3aab83df0fe6", "name": "mathlib", "manifestFile": "lake-manifest.json", "inputRev": "5e932f97dd25535344f80f9dd8da3aab83df0fe6", "inherited": false, "configFile": "lakefile.lean"},
    {"url": "https://github.com/leanprover-community/plausible", "type": "git", "subDir": null, "scope": "leanprover-community", "rev": "83e90935a17ca19ebe4b7893c7f7066e266f50d3", "name": "plausible", "manifestFile": "lake-manifest.json", "inputRev": "main", "inherited": true, "configFile": "lakefile.toml"},
    {"url": "https://github.com/leanprover-community/LeanSearchClient", "type": "git", "subDir": null, "scope": "leanprover-community", "rev": "c5d5b8fe6e5158def25cd28eb94e4141ad97c843", "name": "LeanSearchClient", "manifestFile": "lake-manifest.json", "inputRev": "main", "inherited": true, "configFile": "lakefile.toml"},
    {"url": "https://github.com/leanprover-community/import-graph", "type": "git", "subDir": null, "scope": "leanprover-community", "rev": "48d5698bc464786347c1b0d859b18f938420f060", "name": "importGraph", "manifestFile": "lake-manifest.json", "inputRev": "main", "inherited": true, "configFile": "lakefile.toml"},
    {"url": "https://github.com/leanprover-community/ProofWidgets4", "type": "git", "subDir": null, "scope": "leanprover-community", "rev": "4dd0959c44d1af0462bd604d0f87c5781307d709", "name": "proofwidgets", "manifestFile": "lake-manifest.json", "inputRev": "v0.0.95+lean-v4.29.1", "inherited": true, "configFile": "lakefile.lean"},
    {"url": "https://github.com/leanprover-community/aesop", "type": "git", "subDir": null, "scope": "leanprover-community", "rev": "7152850e7b216a0d409701617721b6e469d34bf6", "name": "aesop", "manifestFile": "lake-manifest.json", "inputRev": "master", "inherited": true, "configFile": "lakefile.toml"},
    {"url": "https://github.com/leanprover-community/quote4", "type": "git", "subDir": null, "scope": "leanprover-community", "rev": "707efb56d0696634e9e965523a1bbe9ac6ce141d", "name": "Qq", "manifestFile": "lake-manifest.json", "inputRev": "master", "inherited": true, "configFile": "lakefile.toml"},
    {"url": "https://github.com/leanprover-community/batteries", "type": "git", "subDir": null, "scope": "leanprover-community", "rev": "756e3321fd3b02a85ffda19fef789916223e578c", "name": "batteries", "manifestFile": "lake-manifest.json", "inputRev": "main", "inherited": true, "configFile": "lakefile.toml"},
    {"url": "https://github.com/leanprover/lean4-cli", "type": "git", "subDir": null, "scope": "leanprover", "rev": "7802da01beb530bf051ab657443f9cd9bc3e1a29", "name": "Cli", "manifestFile": "lake-manifest.json", "inputRev": "v4.29.0", "inherited": true, "configFile": "lakefile.toml"}
  ],
  "name": "lch01",
  "lakeDir": ".lake"
}
```

```lean filename=LCH01/MatrixInterfaces.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-!
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I,
§§2.1–2.2, https://glenzli.com/books/oet/, DOI 10.5281/zenodo.21457931.
Author ORCID: https://orcid.org/0009-0006-6536-3453.
Source: https://github.com/glenzli/oet-public, commit
539b40cec73184d98e06d54fbd10e4b4698bd6e7.
License: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
This file is a new Lean formalization of the selected definitions.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-- Matrices have output components as rows and input components as columns. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- `entry A i j` is the source's coefficient `A_{i → j}`, namely `A j i`. -/
def entry {I : Type} (A : ChannelMatrix I) (i j : I) : ENNReal := A j i

/-- The later step is the left factor in ordinary matrix multiplication. -/
noncomputable def matrixComp {I : Type} [Fintype I]
    (B A : ChannelMatrix I) : ChannelMatrix I :=
  B * A

@[simp] theorem entry_matrixComp {I : Type} [Fintype I]
    (B A : ChannelMatrix I) (i j : I) :
    entry (matrixComp B A) i j = ∑ k : I, entry B k j * entry A i k := by
  simp only [entry, matrixComp, Matrix.mul_apply]

/-- The restricted Lip condition includes the specified domain inclusion. -/
def IsRestrictedLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i : I, entry L i j * d i x y

/-- The full-domain Lip condition is the restricted condition on `dom φ`. -/
def IsLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (L : ChannelMatrix I) : Prop :=
  IsRestrictedLip d φ (dom φ) L

def restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) :=
  {L | IsRestrictedLip d φ U L}

def lipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (ChannelMatrix I) :=
  {L | IsLip d φ L}

/-- Restricted co-Lip matrices require a nonempty input set. -/
def IsRestrictedCoLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, entry K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) :=
  {K | IsRestrictedCoLip d φ U K}

/-- A component channel is the ordered pair (input, output). -/
abbrev ComponentChannel (I : Type) := I × I

def channel (I : Type) (i j : I) : ComponentChannel I := (i, j)

/-- Only input `i` may have a nonzero coefficient in output row `j`. -/
def SingleInputRow {I : Type} (A : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → entry A k j = 0

/-- A diagonal matrix has zero entries on all off-diagonal channels. -/
def IsDiagonal {I : Type} (A : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → entry A i j = 0

theorem diagonal_singleInputRow {I : Type} {A : ChannelMatrix I}
    (hA : IsDiagonal A) (j : I) : SingleInputRow A j j := by
  intro k hkj
  exact hA k j hkj

end LCH01
```

```lean filename=LCH01/ChannelBounds.lean
import LCH01.MatrixInterfaces

/-!
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I,
§2.2 and Exercise 2.2, https://glenzli.com/books/oet/,
author ORCID https://orcid.org/0009-0006-6536-3453,
DOI 10.5281/zenodo.21457931. License: CC BY 4.0,
https://creativecommons.org/licenses/by/4.0/.
This file supplies new Lean proofs of the selected statements.
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-- Algebraic row reduction, valid also for infinite ENNReal coefficients. -/
theorem singleInputRow_sum {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) {L : ChannelMatrix I} {i j : I}
    (hrow : SingleInputRow L i j) (x y : X) :
    (∑ k : I, entry L k j * d k x y) = entry L i j * d i x y := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- CH02-P19: a row supported on one input gives the scalar Lip bound. -/
theorem single_input_lip_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {L : ChannelMatrix I} {i j : I}
    (hL : L ∈ restrictedLipMatrices d φ U) (hrow : SingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L i j * d i x y := by
  intro x hx y hy
  calc
    d j (φ.func x) (φ.func y) ≤ ∑ k : I, entry L k j * d k x y :=
      hL.2 x hx y hy j
    _ = entry L i j * d i x y := singleInputRow_sum d hrow x y

/-- CH02-P19, diagonal special case, simultaneously for every output. -/
theorem diagonal_lip_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {L : ChannelMatrix I}
    (hL : L ∈ restrictedLipMatrices d φ U) (hdiag : IsDiagonal L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro j
  exact single_input_lip_bound d hd hL (diagonal_singleInputRow hdiag j)

/-- Each input-channel term is below the full co-Lip sum and the output. -/
theorem coLip_channel_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    {φ : Operator X bot} {U : Set X} {K : ChannelMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    (i j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    entry K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  classical
  calc
    entry K i j * d i x y ≤ ∑ k : I, entry K k j * d k x y :=
      Finset.single_le_sum (fun k _ => zero_le (entry K k j * d k x y))
        (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

/-- CH02-P20: a positive co-Lip channel preserves positive distance. -/
theorem positive_coLip_channel {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {K : ChannelMatrix I} {i j : I}
    (hK : K ∈ restrictedCoLipMatrices d φ U) (hpos : 0 < entry K i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d i x y → 0 < d j (φ.func x) (φ.func y) := by
  intro x hx y hy hxy
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpos, hxy⟩)
    (coLip_channel_le d hK i j hx hy)

/-- CH02-P21: positive diagonal entries reflect the family zero relation. -/
theorem positive_diagonal_reflects_gauge_zero {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {K : ChannelMatrix I}
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    (hdiag : ∀ j : I, 0 < entry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  apply le_antisymm _ (zero_le _)
  by_contra hn
  have hin : 0 < d j x y := lt_of_not_ge hn
  have hout := positive_coLip_channel d hd hK (hdiag j) x hx y hy hin
  rw [hzero j] at hout
  exact (lt_irrefl (0 : ENNReal)) hout

/-- CH02-P25 (Exercise 2.2): only the chosen output row must be sparse. -/
theorem scalar_two_sided_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {φ : Operator X bot} {U : Set X} {L K : ChannelMatrix I} {j : I}
    (hL : L ∈ restrictedLipMatrices d φ U)
    (hK : K ∈ restrictedCoLipMatrices d φ U)
    (hrow : SingleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ entry L j j * d j x y := by
  intro x hx y hy
  exact ⟨coLip_channel_le d hK j j hx hy,
    single_input_lip_bound d hd hL hrow x hx y hy⟩

end LCH01
```

```lean filename=Main.lean
import LCH01.MatrixInterfaces
import LCH01.ChannelBounds

#print axioms LCH01.entry_matrixComp
#print axioms LCH01.diagonal_singleInputRow
#print axioms LCH01.singleInputRow_sum
#print axioms LCH01.single_input_lip_bound
#print axioms LCH01.diagonal_lip_bound
#print axioms LCH01.coLip_channel_le
#print axioms LCH01.positive_coLip_channel
#print axioms LCH01.positive_diagonal_reflects_gauge_zero
#print axioms LCH01.scalar_two_sided_bound
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
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.IsRestrictedLip"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.IsLip"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.restrictedLipMatrices"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.lipMatrices"}
      ],
      "representation": {
        "objects": "X、bot、Operator、dom 使用冻结前置模块；d : I → X → X → ENNReal 为分量距离族，矩阵元素属于 ENNReal，允许正无穷。",
        "parameters": "Fintype I 表示有限指标族；定义可用于任意距离族，目标定理另显式保留 Nonempty I 和各分量 ExtendedPseudoMetric 的背景条件。",
        "quantifiers": "IsRestrictedLip 是 U ⊆ dom φ 与对所有 x∈U、y∈U、j∈I 的 Lip 不等式之合取；IsLip 取 U=dom φ。",
        "conclusion": "两种矩阵族分别定义为满足对应谓词的矩阵集合；求和项为 entry L i j * d i x y，与正文的上界逐项相同。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.IsRestrictedCoLip"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.restrictedCoLipMatrices"}
      ],
      "representation": {
        "objects": "K 为 ENNReal 矩阵；受限 co-Lip 族是满足 IsRestrictedCoLip 的矩阵集合。",
        "parameters": "U.Nonempty 与 U ⊆ dom φ 均为谓词的显式合取分量，因此族成员本身包含正文规定的非空性和定义域条件。",
        "quantifiers": "对所有 x∈U、y∈U 和输出 j，要求所有输入项的有限和不超过输出距离。",
        "conclusion": "下界为 ∑ i, entry K i j * d i x y ≤ d j (φ.func x) (φ.func y)，无有限系数或严格正系数的额外限制。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.ChannelMatrix"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.entry"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.matrixComp"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.entry_matrixComp"}
      ],
      "representation": {
        "objects": "ChannelMatrix I = Matrix I I ENNReal；普通矩阵的第一指标是输出行，第二指标是输入列。",
        "parameters": "entry A i j 定义为 A j i，对应正文 A_{i→j}。matrixComp B A 定义为普通矩阵积 B*A，后一步 B 位于左侧。",
        "quantifiers": "乘积条目定理对任意有限 I、任意 A、B 和任意输入 i、输出 j 成立。",
        "conclusion": "entry (matrixComp B A) i j = ∑ k, entry B k j * entry A i k，完整给出正文的输入/输出乘法约定。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D07",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.ComponentChannel"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.channel"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.SingleInputRow"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.IsDiagonal"},
        {"file": "LCH01/MatrixInterfaces.lean", "name": "LCH01.diagonal_singleInputRow"}
      ],
      "representation": {
        "objects": "ComponentChannel I = I×I，channel I i j = (i,j)，第一坐标为输入，第二坐标为输出。",
        "parameters": "SingleInputRow A i j 要求输出行 j 的所有 k≠i 输入条目为零；保留的条目 A_{i→j} 也允许为零。",
        "quantifiers": "IsDiagonal A 要求所有 i≠j 的通道系数为零。",
        "conclusion": "diagonal_singleInputRow 证明对角矩阵在每个输出 j 上满足 SingleInputRow A j j；对应的距离界由 CH02-P19 交付。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P19",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.singleInputRow_sum"},
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.single_input_lip_bound"},
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.diagonal_lip_bound"}
      ],
      "representation": {
        "objects": "φ 为冻结定义的保吸收元算子；L 是 φ 在 U 上的合法受限 Lip 矩阵。",
        "parameters": "主定理保留有限非空指标族、每个分量的 ExtendedPseudoMetric 条件及 SingleInputRow L i j；U ⊆ dom φ 来自矩阵族成员。",
        "quantifiers": "singleInputRow_sum 对任意点对给出整行求和等式；主定理对所有 x,y∈U 成立，对角特例进一步对所有 j 成立。",
        "conclusion": "输出距离 ≤ 整行求和 = entry L i j * d i x y；对角矩阵给出每个同分量通道的标量 Lip 上界，允许零及无穷系数。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D07"]
    },
    {
      "id": "CH02-P20",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.coLip_channel_le"},
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.positive_coLip_channel"}
      ],
      "representation": {
        "objects": "K 是 φ 在非空 U 上的合法受限 co-Lip 矩阵，i、j 分别是输入和输出。",
        "parameters": "保留规范空间背景条件；唯一通道附加条件为 0 < entry K i j，允许该系数等于正无穷。",
        "quantifiers": "对所有 x,y∈U，输入距离 0 < d i x y 蕴含输出距离严格为正。",
        "conclusion": "辅助引理证明单项 ≤ 整行和 ≤ 输出距离；ENNReal.mul_pos_iff 保证正系数乘正输入距离严格为正，从而得到正文结论。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P21",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.positive_diagonal_reflects_gauge_zero"}
      ],
      "representation": {
        "objects": "直接使用冻结前置定义 GaugeZeroRelated d x y，即对所有分量 j 有 d j x y = 0。",
        "parameters": "K 为 U 上的合法受限 co-Lip 矩阵；要求所有对角条目严格正，不要求非对角条目为零，也不假设规范族分离。",
        "quantifiers": "对所有 x,y∈U，若所有输出分量距离为零，则所有输入分量距离为零。",
        "conclusion": "结论恰为 GaugeZeroRelated d x y；逐分量使用 CH02-P20 排除正输入距离，不推出 x=y。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P20"]
    },
    {
      "id": "CH02-P25",
      "status": "complete",
      "declarations": [
        {"file": "LCH01/ChannelBounds.lean", "name": "LCH01.scalar_two_sided_bound"}
      ],
      "representation": {
        "objects": "φ、U、j 及同一限制域 U 上的合法 Lip 矩阵 L、合法 co-Lip 矩阵 K 与习题一致。",
        "parameters": "SingleInputRow L j j 正是对所有 k≠j 有 L_{k→j}=0；仅限制所选输出行，不要求 L 或 K 整体对角，也不要求 K_{j→j} 为正。",
        "quantifiers": "保留有限非空规范族与各分量扩展伪度量条件；对所有 x,y∈U 同时给出左右两个不等式。",
        "conclusion": "Lean 中用合取表示链式不等式：entry K j j * d j x y ≤ d j (φ.func x) (φ.func y) 且输出距离 ≤ entry L j j * d j x y。下界使用 CH02-P20 所列辅助引理 coLip_channel_le，上界使用 CH02-P19。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D07", "CH02-P19", "CH02-P20"]
    }
  ]
}
```