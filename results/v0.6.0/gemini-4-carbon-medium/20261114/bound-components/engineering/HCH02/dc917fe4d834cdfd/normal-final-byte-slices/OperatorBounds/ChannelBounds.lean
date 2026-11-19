import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic
import OperatorBounds.MatrixBounds

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-!
# 第2章 算子界 — §2.2 分量解耦与通道分辨保持 (`#h-7fa97eb6e24d5527`)

本模块形式化第2章第二节的全部定义、反例与命题证明义务（`HC02-D07`、`HC02-D08`，
`HC02-P18` 至 `HC02-P32`）。
-/

/-! ## HC02-D07: 分量通道、单行/单列稀疏、行/列解耦与对角体系 -/

/--
**分量通道** (`HC02-D07`)：
序对 `(i, j) : I × I` 表示从输入分量伪度量 $d_i$ 到输出分量伪度量 $d_j$ 的一个分量通道。
-/
abbrev Channel (I : Type) : Type := I × I

/--
**单行稀疏谓词** $\mathrm{Row}(\mathbf{L}, i, j)$ (`HC02-D07`)：
固定输出指标（第 $j$ 行），除输入位置 $i$ 外其余条目全为 $0$（$\forall k \neq i,\, L_{k \to j} = 0$）。
-/
def IsRowSparseAt {I : Type} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/--
**矩阵第 $j$ 行至多一项非零** (`HC02-D07`)：$\exists i \in I,\, \mathrm{Row}(\mathbf{L}, i, j)$。
-/
def IsRowDecoupledMatrix {I : Type} (L : BoundMatrix I) (j : I) : Prop :=
  ∃ i : I, IsRowSparseAt L i j

/--
**单列稀疏谓词** $\mathrm{Col}(\mathbf{L}, i, j)$ (`HC02-D07`)：
固定输入指标（第 $i$ 列），除输出位置 $j$ 外其余条目全为 $0$（$\forall k \neq j,\, L_{i \to k} = 0$）。
-/
def IsColSparseAt {I : Type} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/--
**矩阵第 $i$ 列至多一项非零** (`HC02-D07`)：$\exists j \in I,\, \mathrm{Col}(\mathbf{L}, i, j)$。
-/
def IsColDecoupledMatrix {I : Type} (L : BoundMatrix I) (i : I) : Prop :=
  ∃ j : I, IsColSparseAt L i j

/--
**对角矩阵谓词** (`HC02-D07`)：所有非对角条目均为 $0$（$\forall i \neq j,\, L_{i \to j} = 0$）。
-/
def IsDiagonalBound {I : Type} (L : BoundMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

theorem forall_isRowSparseAt_diag_iff_isDiagonalBound {I : Type} (L : BoundMatrix I) :
    (∀ j : I, IsRowSparseAt L j j) ↔ IsDiagonalBound L := by
  constructor
  · intro h i j hij
    exact h j i hij
  · intro h j i hij
    exact h i j hij

section DecouplingDefinitions

set_option linter.unusedFintypeInType false

/--
**定义（关于输出分量 $d_j$ 的行解耦）** (`HC02-D07`)：
存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 及 $i \in I$，使得 $\forall k \neq i,\, L_{k \to j} = 0$。
-/
def IsRowDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, ∃ i : I, IsRowSparseAt L i j

/--
**定义（关于输入分量 $d_i$ 的列解耦）** (`HC02-D07`)：
存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 及 $j \in I$，使得 $\forall k \neq j,\, L_{i \to k} = 0$。
-/
def IsColDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, ∃ j : I, IsColSparseAt L i j

/--
**定义（完全解耦体系证书）** (`HC02-D07`)：
上界证书 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 为对角矩阵。
-/
def IsCompletelyDecoupledCert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I) : Prop :=
  L ∈ RestrictedLipSet d ϕ U ∧ IsDiagonalBound L

end DecouplingDefinitions

/-! ## HC02-D08 & HC02-P18 至 HC02-P24: 单通道 Lip 常数及其性质与反例 -/

section SingleChannelConstants

set_option linter.unusedFintypeInType false

/--
**定义（单通道可行标量族 $\mathcal{S}_{i \to j}(\phi; U)$）** (`HC02-D08`)：
对 $U \subseteq \mathrm{dom}(\phi)$，收集所有满足单分量点对放缩不等式
$d_j(\phi(x), \phi(y)) \le \lambda \cdot d_i(x, y)$（$\forall x, y \in U$）的常数 $\lambda \in \bar{\mathbb{R}}_+$。
-/
def ChannelFeasibleScalars {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { lam : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y }

/--
**定义（单通道 Lip 常数 $\underline{L}_{i \to j}(\phi; U)$）** (`HC02-D08`)：
定义为可行标量族 $\mathcal{S}_{i \to j}(\phi; U)$ 的下确界 `sInf`（空集下确界为 $\top = +\infty$），
不与任何多分量 Lip 矩阵的条目相混淆。
-/
noncomputable def channelLipConst {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (ChannelFeasibleScalars d ϕ U i j)

/-- 当可行标量集合为空时，按约定 $\inf \emptyset = +\infty$ (`HC02-D08`)。 -/
theorem channelLipConst_of_empty {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hempty : ChannelFeasibleScalars d ϕ U i j = ∅) :
    channelLipConst d ϕ U i j = ⊤ := by
  simp [channelLipConst, hempty]

/--
**标量可行族向上封闭** (`HC02-P20`)：
若 $\lambda_0 \in \mathcal{S}_{i \to j}(\phi; U)$ 且 $\lambda_1 \ge \lambda_0$，
则 $\lambda_1 \in \mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem channelFeasibleScalars_upward_closed {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {lam₀ lam₁ : ENNReal}
    (h₀ : lam₀ ∈ ChannelFeasibleScalars d ϕ U i j) (hle : lam₀ ≤ lam₁) :
    lam₁ ∈ ChannelFeasibleScalars d ϕ U i j := by
  intro x hx y hy
  exact le_trans (h₀ x hx y hy) (mul_le_mul_left hle (d i x y))

/--
**零输入距而正输出距使可行标量族为空且单通道常数为 $+\infty$** (`HC02-P18`)：
若存在 $x, y \in U$ 使 $d_i(x, y) = 0$ 且 $d_j(\phi(x), \phi(y)) > 0$，
则不存在任何 $\lambda \in \bar{\mathbb{R}}_+$（含 $+\infty$）满足标量界，
故 $\mathcal{S}_{i \to j}(\phi; U) = \emptyset$ 且 $\underline{L}_{i \to j}(\phi; U) = +\infty$。
-/
theorem channelFeasibleScalars_empty_of_zero_input_pos_output
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hdi : d i x y = 0) (hdj : 0 < d j (ϕ.func x) (ϕ.func y)) :
    ChannelFeasibleScalars d ϕ U i j = ∅ ∧ channelLipConst d ϕ U i j = ⊤ := by
  have hempty : ChannelFeasibleScalars d ϕ U i j = ∅ := by
    ext lam
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hlam
    have hle := hlam x hx y hy
    rw [hdi, mul_zero] at hle
    exact (not_le_of_gt hdj) hle
  exact ⟨hempty, channelLipConst_of_empty d ϕ U i j hempty⟩

/--
**正有限下确界以上的每个常数均可行** (`HC02-P21`)：
记 $a = \underline{L}_{i \to j}(\phi; U)$。当 $0 < a < +\infty$ 时，
任意 $\lambda > a$（允许 $\lambda = +\infty$）均属于 $\mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem mem_channelFeasibleScalars_of_gt_inf
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (_hpos : 0 < channelLipConst d ϕ U i j)
    (_hfin : channelLipConst d ϕ U i j < ⊤)
    {lam : ENNReal} (hgt : channelLipConst d ϕ U i j < lam) :
    lam ∈ ChannelFeasibleScalars d ϕ U i j := by
  rcases sInf_lt_iff.mp hgt with ⟨lam₀, hlam₀_mem, hlam₀_lt⟩
  exact channelFeasibleScalars_upward_closed d ϕ hU hlam₀_mem (le_of_lt hlam₀_lt)

/--
**正有限最优单通道下确界可被取到** (`HC02-P19`)：
当 $0 < \underline{L}_{i \to j}(\phi; U) < +\infty$ 时，
$\underline{L}_{i \to j}(\phi; U) \in \mathcal{S}_{i \to j}(\phi; U)$，即对任意 $x, y \in U$ 成立
$d_j(\phi(x), \phi(y)) \le \underline{L}_{i \to j}(\phi; U) \cdot d_i(x, y)$。
-/
theorem channelLipConst_mem_of_pos_of_lt_top
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (hpos : 0 < channelLipConst d ϕ U i j)
    (hfin : channelLipConst d ϕ U i j < ⊤) :
    channelLipConst d ϕ U i j ∈ ChannelFeasibleScalars d ϕ U i j ∧
      ∀ x ∈ U, ∀ y ∈ U,
        d j (ϕ.func x) (ϕ.func y) ≤ channelLipConst d ϕ U i j * d i x y := by
  have hmem : channelLipConst d ϕ U i j ∈ ChannelFeasibleScalars d ϕ U i j := by
    set a := channelLipConst d ϕ U i j
    have ha_gt : a < a + 1 := ENNReal.lt_add_right hfin.ne one_ne_zero
    have ha1_mem : a + 1 ∈ ChannelFeasibleScalars d ϕ U i j :=
      mem_channelFeasibleScalars_of_gt_inf d ϕ hU hpos hfin ha_gt
    intro x hx y hy
    set A := d j (ϕ.func x) (ϕ.func y)
    set B := d i x y
    by_cases hB0 : B = 0
    · -- B = 0 情形
      have hA_le : A ≤ 0 := by
        have h := ha1_mem x hx y hy
        simpa [A, B, hB0] using h
      rw [hB0, mul_zero]
      exact hA_le
    · by_cases hBtop : B = ⊤
      · -- B = +∞ 情形：由 a > 0 知 a * ⊤ = ⊤
        rw [hBtop, ENNReal.mul_top hpos.ne']
        exact le_top
      · -- 0 < B < +∞ 情形
        have ha1_lt_top : a + 1 < ⊤ := ENNReal.add_lt_top.mpr ⟨hfin, ENNReal.one_lt_top⟩
        have hA_lt_top : A < ⊤ :=
          lt_of_le_of_lt (ha1_mem x hx y hy) (ENNReal.mul_lt_top ha1_lt_top (lt_top_iff_ne_top.mpr hBtop))
        have hA_ne_top : A ≠ ⊤ := hA_lt_top.ne
        have ha_ne_top : a ≠ ⊤ := hfin.ne
        -- 化为有限非负实数 NNReal 验证反证法
        set a' : NNReal := a.toNNReal
        set b' : NNReal := B.toNNReal
        set A' : NNReal := A.toNNReal
        have ha_coe : (a' : ENNReal) = a := ENNReal.coe_toNNReal ha_ne_top
        have hB_coe : (b' : ENNReal) = B := ENNReal.coe_toNNReal hBtop
        have hA_coe : (A' : ENNReal) = A := ENNReal.coe_toNNReal hA_ne_top
        have hb'_pos : 0 < b' := by
          rw [← ENNReal.coe_pos, hB_coe]
          exact pos_iff_ne_zero.mpr hB0
        rw [← hA_coe, ← ha_coe, ← hB_coe, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
        by_contra hnot
        have hlt : a' * b' < A' := lt_of_not_ge hnot
        have ha'_lt_div : a' < A' / b' := (lt_div_iff₀ hb'_pos).mpr hlt
        rcases exists_between ha'_lt_div with ⟨c, hac, hcdiv⟩
        have hcb : c * b' < A' := (lt_div_iff₀ hb'_pos).mp hcdiv
        have hlam_gt : a < (c : ENNReal) := by
          rw [← ha_coe, ENNReal.coe_lt_coe]
          exact hac
        have hc_mem : (c : ENNReal) ∈ ChannelFeasibleScalars d ϕ U i j :=
          mem_channelFeasibleScalars_of_gt_inf d ϕ hU hpos hfin hlam_gt
        have hA_le_cb : A ≤ (c : ENNReal) * B := hc_mem x hx y hy
        rw [← hA_coe, ← hB_coe, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at hA_le_cb
        exact (not_le_of_gt hcb) hA_le_cb
  exact ⟨hmem, hmem⟩

/--
OET anchor: h-57de7918859a9de2 (零下确界正有限常数分支)
**注（零下确界给出所有有限正常数界）** (`HC02-P22`)：
当 $\underline{L}_{i \to j}(\phi; U) = 0$ 时，任意满足 $0 < \lambda < +\infty$ 的常数 $\lambda$
均属于 $\mathcal{S}_{i \to j}(\phi; U)$。
-/
theorem mem_channelFeasibleScalars_of_inf_eq_zero
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (hzero : channelLipConst d ϕ U i j = 0)
    {lam : ENNReal} (hpos : 0 < lam) (_hfin : lam < ⊤) :
    lam ∈ ChannelFeasibleScalars d ϕ U i j := by
  have hgt : channelLipConst d ϕ U i j < lam := by
    rwa [hzero]
  rcases sInf_lt_iff.mp hgt with ⟨lam₀, hlam₀_mem, hlam₀_lt⟩
  exact channelFeasibleScalars_upward_closed d ϕ hU hlam₀_mem (le_of_lt hlam₀_lt)

/--
OET anchor: h-57de7918859a9de2 (有限性等价判据)
**注（单通道下确界有限当且仅当存在有限可行常数）** (`HC02-P24`)：
$\underline{L}_{i \to j}(\phi; U) < +\infty$ 当且仅当存在有限常数 $\lambda < +\infty$，
使对所有 $x, y \in U$ 有 $d_j(\phi(x), \phi(y)) \le \lambda \cdot d_i(x, y)$。
-/
theorem channelLipConst_lt_top_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) (i j : I) :
    channelLipConst d ϕ U i j < ⊤ ↔
      ∃ lam : ENNReal, lam < ⊤ ∧
        ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y := by
  constructor
  · intro hfin
    by_cases hzero : channelLipConst d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact mem_channelFeasibleScalars_of_inf_eq_zero d ϕ hU hzero zero_lt_one ENNReal.one_lt_top
    · refine ⟨channelLipConst d ϕ U i j, hfin, ?_⟩
      exact (channelLipConst_mem_of_pos_of_lt_top d ϕ hU
        (pos_iff_ne_zero.mpr hzero) hfin).1
  · rintro ⟨lam, hlam_lt, hlam_mem⟩
    exact lt_of_le_of_lt (sInf_le hlam_mem) hlam_lt

end SingleChannelConstants

/-! ### HC02-P23: 零下确界未必由 $0$ 实现的显式反例构造 -/

namespace ZeroInfCounterexample

/-- 反例底层空间的四个点：`0` 为吸收元，`1, 2, 3` 为非吸收点。 -/
abbrev CX : Type := Fin 4

/-- 反例底层吸收元 $\bot = 0$。 -/
def cbot : CX := 0

/-- 反例单分量伪度量族（指标集 `Unit`）：仅 `{2, 3}` 之间距离为 `1`，其余异点距离全为 `⊤`。 -/
def cd (_ : Unit) (x y : CX) : ENNReal :=
  if x = y then 0
  else if (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) then 1
  else ⊤

instance instExtendedPseudoMetricCounterexample (u : Unit) :
    ExtendedPseudoMetric CX cbot (cd u) where
  nonabsorbing := ⟨1, by decide⟩
  dist_self x := by simp [cd]
  symm x y := by
    fin_cases x <;> fin_cases y <;> rfl
  triangle x y z := by
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [cd]
  isolate_bot x hx := by
    fin_cases x
    · exact False.elim (hx rfl)
    · rfl
    · rfl
    · rfl

/-- 反例算子 $\phi$：保吸收元 `0 ↦ 0`，并把距离为 `⊤` 的点对 `(1, 2)` 映到距离为 `1` 的点对 `(2, 3)`。 -/
def cphi : Operator CX cbot where
  func x :=
    match x with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 2
    | ⟨2, _⟩ => 3
    | ⟨3, _⟩ => 3
  preserves_bot := rfl

/-- 反例非空评估域 $U = \{1, 2\} \subseteq \mathrm{dom}(\phi)$。 -/
def cU : Set CX := {1, 2}

theorem cU_nonempty : cU.Nonempty := ⟨1, by simp [cU]⟩

theorem cU_subset_dom : cU ⊆ dom cphi := by
  intro x hx
  rcases hx with rfl | rfl
  · change cphi.func 1 ≠ cbot
    decide
  · change cphi.func 2 ≠ cbot
    decide

theorem pos_mem_cFeasible {lam : ENNReal} (hpos : 0 < lam) :
    lam ∈ ChannelFeasibleScalars cd cphi cU () () := by
  intro x hx y hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp [cphi, cd]
  · have htop : cd () 1 2 = ⊤ := rfl
    have hout : cd () (cphi.func 1) (cphi.func 2) = 1 := rfl
    rw [htop, hout, ENNReal.mul_top hpos.ne']
    exact le_top
  · have htop : cd () 2 1 = ⊤ := rfl
    have hout : cd () (cphi.func 2) (cphi.func 1) = 1 := rfl
    rw [htop, hout, ENNReal.mul_top hpos.ne']
    exact le_top
  · simp [cphi, cd]

theorem cChannelLipConst_eq_zero :
    channelLipConst cd cphi cU () () = 0 := by
  apply le_antisymm _ (zero_le _)
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  exact sInf_le (pos_mem_cFeasible hc)

theorem zero_not_mem_cFeasible :
    (0 : ENNReal) ∉ ChannelFeasibleScalars cd cphi cU () () := by
  intro h0
  have hle := h0 1 (by simp [cU]) 2 (by simp [cU])
  have htop : cd () 1 2 = ⊤ := rfl
  have hout : cd () (cphi.func 1) (cphi.func 2) = 1 := rfl
  rw [htop, hout, zero_mul] at hle
  exact (not_le_of_gt zero_lt_one) hle

end ZeroInfCounterexample

/--
OET anchor: h-57de7918859a9de2 (零下确界不可达反例)
**反例（零下确界未必由 $\lambda = 0$ 实现）** (`HC02-P23`)：
存在合法扩展规范空间、合法算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 及非空子集 $U \subseteq \mathrm{dom}(\phi)$，
使得 $\underline{L}_{i \to j}(\phi; U) = 0$，但 $\lambda = 0 \notin \mathcal{S}_{i \to j}(\phi; U)$
（即 $0$ 不满足相应单通道标量上界）。
-/
theorem exists_zero_channelLipConst_not_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ k : I, ExtendedPseudoMetric X bot (d k))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
      channelLipConst d ϕ U i j = 0 ∧
      (0 : ENNReal) ∉ ChannelFeasibleScalars d ϕ U i j := by
  refine ⟨ZeroInfCounterexample.CX, Unit, ZeroInfCounterexample.cbot,
    inferInstance, inferInstance, ZeroInfCounterexample.cd,
    ZeroInfCounterexample.instExtendedPseudoMetricCounterexample,
    ZeroInfCounterexample.cphi, ZeroInfCounterexample.cU, (), (),
    ZeroInfCounterexample.cU_nonempty, ZeroInfCounterexample.cU_subset_dom,
    ZeroInfCounterexample.cChannelLipConst_eq_zero,
    ZeroInfCounterexample.zero_not_mem_cFeasible⟩

/-! ## HC02-P25 至 HC02-P32: 通道隔离、行列解耦、标量双侧界与可分辨保持 -/

section ChannelAndDistinguishability

set_option linter.unusedFintypeInType false

/--
**零系数移除该上界证书中的输入求和项** (`HC02-P25`)：
当 $L_{i \to j} = 0$ 时，无论 $d_i(x, y)$ 取何值（包括 $d_i(x, y) = +\infty$），
恒有 $L_{i \to j} \cdot d_i(x, y) = 0$，故输出 $d_j$ 的上界求和可直接删去 $i$-项。
-/
theorem zero_entry_removes_channel_term {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I} {i j : I}
    (hzero : L i j = 0) :
    open Classical in
    (∀ x y : X, L i j * d i x y = 0) ∧
      (∀ x y : X, (∑ k : I, L k j * d k x y) =
        ∑ k ∈ Finset.univ.erase i, L k j * d k x y) ∧
      (L ∈ RestrictedLipSet d ϕ U →
        ∀ x ∈ U, ∀ y ∈ U,
          d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y) := by
  classical
  have hterm : ∀ x y : X, L i j * d i x y = 0 := by
    intro x y
    rw [hzero, zero_mul]
  have hsum : ∀ x y : X, (∑ k : I, L k j * d k x y) =
      ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
    intro x y
    rw [← Finset.add_sum_erase Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i),
      hterm x y, zero_add]
  refine ⟨hterm, hsum, ?_⟩
  intro hL x hx y hy
  rw [← hsum x y]
  exact hL.2 x hx y hy j

/--
**任意唯一输入位置的单行化简** (`HC02-P26`)：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 且第 $j$ 行除输入 $i$ 外全为 $0$（$i$ 不必等于 $j$），
则对所有 $x, y \in U$，$d_j(\phi(x), \phi(y)) \le L_{i \to j} \cdot d_i(x, y)$。
-/
theorem restrictedLip_of_isRowSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) {i j : I} (hrow : IsRowSparseAt L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [hrow k hki, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [← hsum]
  exact hL.2 x hx y hy j

/--
**任意单列支撑的证书贡献范围** (`HC02-P27`)：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 的第 $i$ 列仅输出 $j$ 可能非零（`IsColSparseAt L i j`），
则对任意异于 $j$ 的输出分量 $k \neq j$，输入项 $L_{i \to k} d_i(x, y) = 0$，
且 $d_k(\phi(x), \phi(y))$ 的该证书上界不依赖输入分量 $d_i$。
-/
theorem restrictedLip_of_isColSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) {i j : I} (hcol : IsColSparseAt L i j) :
    open Classical in
    ∀ k : I, k ≠ j →
      (∀ x y : X, L i k * d i x y = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U,
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y) := by
  classical
  intro k hkj
  have hk_zero := zero_entry_removes_channel_term d ϕ (U := U) (L := L) (i := i) (j := k) (hcol k hkj)
  exact ⟨hk_zero.1, hk_zero.2.2 hL⟩

/--
**完全解耦（对角 Lip 矩阵）给出所有分量的独立标量放缩上界** (`HC02-P28`)：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 为对角矩阵，则对所有 $j \in I$ 与 $x, y \in U$，
$d_j(\phi(x), \phi(y)) \le L_{j \to j} \cdot d_j(x, y)$。
-/
theorem restrictedLip_of_isDiagonalBound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hdiag : IsDiagonalBound L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact restrictedLip_of_isRowSparseAt d ϕ hL (fun k hkj => hdiag k j hkj)

/--
OET anchor: h-6a98a58b5bc95360
**引理（对角输入项的标量双侧界）** (`HC02-P29`)：
给定 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 与 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$，
仅要求 $\mathbf{L}$ 在第 $j$ 行满足 $L_{k \to j} = 0$（$\forall k \neq j$，不对 $\mathbf{K}$ 施加稀疏假设），
即可对任意 $x, y \in U$ 得到
$K_{j \to j} \cdot d_j(x, y) \le d_j(\phi(x), \phi(y)) \le L_{j \to j} \cdot d_j(x, y)$。
-/
theorem diagonal_row_scalar_two_sided_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L K : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hK : K ∈ RestrictedCoLipSet d ϕ U)
    {j : I} (hrow : IsRowSparseAt L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, restrictedLip_of_isRowSparseAt d ϕ hL hrow x hx y hy⟩
  calc
    K j j * d j x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ j)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
**逐分量标量双侧界（全分量对角输入行条件）** (`HC02-P30`)：
若对所有 $j \in I$ 均满足 $L_{k \to j} = 0$（$\forall k \neq j$），则全部分量的标量双侧界同时成立。
-/
theorem componentwise_scalar_two_sided_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L K : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hK : K ∈ RestrictedCoLipSet d ϕ U)
    (hrows : ∀ j : I, IsRowSparseAt L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact diagonal_row_scalar_two_sided_bound d ϕ hL hK (hrows j)

/--
**有限标量双侧放缩界（含有限对角系数分支）** (`HC02-P30`)：
若进一步要求对所有 $j \in I$ 有 $L_{j \to j}, K_{j \to j} < +\infty$，
则存在有限非负实数标量族 $\kappa, \ell : I \to \mathbb{R}_{\ge 0}$，给出逐分量的有限标量双侧放缩界。
-/
theorem componentwise_finite_scalar_two_sided_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L K : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) (hK : K ∈ RestrictedCoLipSet d ϕ U)
    (hrows : ∀ j : I, IsRowSparseAt L j j)
    (hL_fin : ∀ j : I, L j j < ⊤) (hK_fin : ∀ j : I, K j j < ⊤) :
    ∃ (κ ℓ : I → NNReal),
      (∀ j : I, (κ j : ENNReal) = K j j ∧ (ℓ j : ENNReal) = L j j) ∧
      ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
        (κ j : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ (ℓ j : ENNReal) * d j x y := by
  refine ⟨fun j => (K j j).toNNReal, fun j => (L j j).toNNReal, ?_, ?_⟩
  · intro j
    exact ⟨ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne⟩
  · intro j x hx y hy
    rw [ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne]
    exact componentwise_scalar_two_sided_bound d ϕ hL hK hrows j x hx y hy

/--
**单行化简证书与单通道 Lip 常数的比较关系** (`HC02-D08`, `HC02-P26`)：
仅当 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 在第 $j$ 行关于输入 $i$ 单行稀疏时，
其条目 $L_{i \to j}$ 才构成单通道可行常数并满足 $\underline{L}_{i \to j}(\phi; U) \le L_{i \to j}$。
-/
theorem channelLipConst_le_of_isRowSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {L : BoundMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U) {i j : I} (hrow : IsRowSparseAt L i j) :
    channelLipConst d ϕ U i j ≤ L i j :=
  sInf_le (restrictedLip_of_isRowSparseAt d ϕ hL hrow)

/--
**正 co-Lip 条目给出的单通道正下界传递** (`HC02-P31`，对应正文 311 行)：
若 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且 $K_{i \to j} > 0$，则该证书给出从输入分量 $d_i$
到输出分量 $d_j$ 的正系数下界 $K_{i \to j} \cdot d_i(x, y) \le d_j(\phi(x), \phi(y))$。
-/
theorem pos_coLip_channel_lower_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {K : BoundMatrix I}
    (hK : K ∈ RestrictedCoLipSet d ϕ U) {i j : I} (hKij : 0 < K i j) :
    0 < K i j ∧ ∀ x ∈ U, ∀ y ∈ U, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  refine ⟨hKij, fun x hx y hy => ?_⟩
  calc
    K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
OET anchor: h-f82672ec0dd48f28 (i)
**命题（正 co-Lip 通道的可分辨保持）** (`HC02-P31`)：
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若 $K_{i \to j} > 0$，则对任意 $x, y \in U$，
$d_i(x, y) > 0 \implies d_j(\phi(x), \phi(y)) > 0$。
-/
theorem pos_coLip_preserves_distinguishability {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {K : BoundMatrix I}
    (hK : K ∈ RestrictedCoLipSet d ϕ U) {i j : I} (hKij : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdi
  have hprod_pos : 0 < K i j * d i x y :=
    ENNReal.mul_pos hKij.ne' hdi.ne'
  have hle := (pos_coLip_channel_lower_bound d ϕ hK hKij).2 x hx y hy
  exact lt_of_lt_of_le hprod_pos hle

/--
OET anchor: h-f82672ec0dd48f28 (ii)
**命题（正对角 co-Lip 反射族零距关系）** (`HC02-P32`)：
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若对所有 $j \in I$ 均有 $K_{j \to j} > 0$，
则对任意 $x, y \in U$，$\phi(x) \sim_{\mathcal{G}} \phi(y) \implies x \sim_{\mathcal{G}} y$。
-/
theorem coLip_reflects_gaugeZeroRelated {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (ϕ : Operator X bot) {U : Set X} {K : BoundMatrix I}
    (hK : K ∈ RestrictedCoLipSet d ϕ U) (hdiag_pos : ∀ j : I, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_coLip_preserves_distinguishability d ϕ hK (hdiag_pos j) x hx y hy hpos
  exact hout_pos.ne' (hrel j)

end ChannelAndDistinguishability

end formal_oet.vol_01.ch_02_operator_bounds
