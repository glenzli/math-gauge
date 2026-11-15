import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.matrix_bounds

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

noncomputable section

/-!
## 单通道可行标量族与单通道 Lip 常数 (HC02-D08, HC02-P18 .. HC02-P24)
-/

/-- 分量通道类型：从输入分量 $i \in I$ 到输出分量 $j \in I$ 的有序对 $(i, j) \in I \times I$ (HC02-D07)。 -/
abbrev ComponentChannel (I : Type) : Type := I × I

/--
算子 $\phi$ 在作用域 $U \subseteq \mathrm{dom}(\phi)$ 上关于通道 $(i, j)$ 的单通道可行标量族：
$\mathcal{S}_{i \to j}(\phi; U) := \{\lambda \in \bar{\mathbb{R}}_+ \mid \forall x, y \in U,\; d_j(\phi(x), \phi(y)) \le \lambda \cdot d_i(x, y)\}$ (HC02-D08)。
-/
def SingleChannelFeasibleSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (i j : I) : Set ENNReal :=
  { r : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ r * d i x y }

/--
算子 $\phi$ 在作用域 $U \subseteq \mathrm{dom}(\phi)$ 上关于通道 $(i, j)$ 的单通道 Lip 常数：
$\underline{L}_{i \to j}(\phi; U) := \inf \mathcal{S}_{i \to j}(\phi; U)$，空集下确界按 `ENNReal` 约定为 `⊤` ($+\infty$) (HC02-D08)。
-/
def singleChannelLipConst {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (i j : I) : ENNReal :=
  sInf (SingleChannelFeasibleSet d ϕ U i j)

@[simp]
theorem sInf_empty_ennreal : sInf (∅ : Set ENNReal) = ⊤ :=
  sInf_empty

/--
当存在 $x, y \in U$ 使 $d_i(x, y) = 0 < d_j(\phi(x), \phi(y))$ 时，
不存在任何可行标量常数，可行集合为空且 $\underline{L}_{i \to j}(\phi; U) = +\infty$ (HC02-P18)。
-/
theorem singleChannel_empty_and_top_of_zero_input_pos_output
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_in : d i x y = 0) (h_out : 0 < d j (ϕ.func x) (ϕ.func y)) :
    (∀ r : ENNReal, r ∉ SingleChannelFeasibleSet d ϕ U i j) ∧
      SingleChannelFeasibleSet d ϕ U i j = ∅ ∧
      singleChannelLipConst d ϕ U i j = ⊤ := by
  have h_no : ∀ r : ENNReal, r ∉ SingleChannelFeasibleSet d ϕ U i j := by
    intro r hr
    have hle := hr x hx y hy
    rw [h_in, mul_zero] at hle
    exact (not_lt_of_ge hle) h_out
  have h_empty : SingleChannelFeasibleSet d ϕ U i j = ∅ := by
    ext r
    exact ⟨fun hr => False.elim (h_no r hr), False.elim⟩
  refine ⟨h_no, h_empty, ?_⟩
  simp [singleChannelLipConst, h_empty]

/-- 单通道可行标量族向上封闭：$\lambda_0 \in \mathcal{S}$ 且 $\lambda_1 \ge \lambda_0$ 时 $\lambda_1 \in \mathcal{S}$ (HC02-P20)。 -/
theorem singleChannelFeasibleSet_upward_closed
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (_hU : U ⊆ dom ϕ) {i j : I}
    {r0 r1 : ENNReal}
    (hr0 : r0 ∈ SingleChannelFeasibleSet d ϕ U i j) (hle : r0 ≤ r1) :
    r1 ∈ SingleChannelFeasibleSet d ϕ U i j := by
  intro x hx y hy
  exact le_trans (hr0 x hx y hy) (mul_le_mul_of_nonneg_right hle (zero_le _))

/-- 在 $0 < a < +\infty$ 语境下，任意严格大于 $a = \underline{L}_{i \to j}(\phi; U)$ 的常数（含 $+\infty$）均属于可行族 (HC02-P21)。 -/
theorem singleChannelFeasibleSet_of_gt_const
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (_ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (_ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤)
    {r : ENNReal} (hr : singleChannelLipConst d ϕ U i j < r) :
    r ∈ SingleChannelFeasibleSet d ϕ U i j := by
  unfold singleChannelLipConst at hr
  rcases sInf_lt_iff.mp hr with ⟨r0, hr0, hr0_lt⟩
  exact singleChannelFeasibleSet_upward_closed d ϕ hU hr0 hr0_lt.le

/--
当 $0 < \underline{L}_{i \to j}(\phi; U) < +\infty$ 时，单通道下确界本身可被取到，
即 $\underline{L}_{i \to j}(\phi; U) \in \mathcal{S}_{i \to j}(\phi; U)$ (HC02-P19)。
-/
theorem singleChannelLipConst_mem_of_pos_lt_top
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤) :
    singleChannelLipConst d ϕ U i j ∈ SingleChannelFeasibleSet d ϕ U i j := by
  set a := singleChannelLipConst d ϕ U i j
  intro x hx y hy
  set A := d j (ϕ.func x) (ϕ.func y)
  set B := d i x y
  by_cases hB0 : B = 0
  · have h_top_mem : (⊤ : ENNReal) ∈ SingleChannelFeasibleSet d ϕ U i j :=
      singleChannelFeasibleSet_of_gt_const d ϕ hU ha_pos ha_lt_top ha_lt_top
    have hA0 : A ≤ (⊤ : ENNReal) * B := h_top_mem x hx y hy
    rw [hB0, mul_zero] at hA0
    exact le_trans hA0 (zero_le _)
  · by_cases hBtop : B = ⊤
    · rw [hBtop, ENNReal.mul_top ha_pos.ne']
      exact le_top
    · have ha1_gt : a < a + 1 := ENNReal.lt_add_right ha_lt_top.ne one_ne_zero
      have ha1_mem : a + 1 ∈ SingleChannelFeasibleSet d ϕ U i j :=
        singleChannelFeasibleSet_of_gt_const d ϕ hU ha_pos ha_lt_top ha1_gt
      have hA_le : A ≤ (a + 1) * B := ha1_mem x hx y hy
      have ha1_ne_top : a + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha_lt_top.ne, ENNReal.one_ne_top⟩
      have hA_ne_top : A ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ha1_ne_top hBtop) hA_le
      have haB_ne_top : a * B ≠ ⊤ := ENNReal.mul_ne_top ha_lt_top.ne hBtop
      rw [← ENNReal.toReal_le_toReal hA_ne_top haB_ne_top, ENNReal.toReal_mul]
      by_contra h_not_le
      push Not at h_not_le
      have hB_real_pos : 0 < B.toReal := ENNReal.toReal_pos hB0 hBtop
      set ε : ℝ := (A.toReal - a.toReal * B.toReal) / (2 * B.toReal)
      have hε_pos : 0 < ε := div_pos (sub_pos.mpr h_not_le) (by linarith)
      have hof_pos : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε_pos
      have hr_gt : a < a + ENNReal.ofReal ε :=
        ENNReal.lt_add_right ha_lt_top.ne hof_pos.ne'
      have hr_mem : a + ENNReal.ofReal ε ∈ SingleChannelFeasibleSet d ϕ U i j :=
        singleChannelFeasibleSet_of_gt_const d ϕ hU ha_pos ha_lt_top hr_gt
      have hr_bound : A ≤ (a + ENNReal.ofReal ε) * B := hr_mem x hx y hy
      have hr_ne_top : a + ENNReal.ofReal ε ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ha_lt_top.ne, ENNReal.ofReal_ne_top⟩
      have hrB_ne_top : (a + ENNReal.ofReal ε) * B ≠ ⊤ :=
        ENNReal.mul_ne_top hr_ne_top hBtop
      have h_real_le : A.toReal ≤ ((a + ENNReal.ofReal ε) * B).toReal :=
        (ENNReal.toReal_le_toReal hA_ne_top hrB_ne_top).mpr hr_bound
      rw [ENNReal.toReal_mul, ENNReal.toReal_add ha_lt_top.ne ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε_pos.le, add_mul] at h_real_le
      have hεB : ε * B.toReal = (A.toReal - a.toReal * B.toReal) / 2 := by
        dsimp [ε]
        field_simp [hB_real_pos.ne']
      linarith

/-- 正有限单通道下确界取到时的显式逐点对标量上界形式 (HC02-P19)。 -/
theorem singleChannelLipConst_bound_of_pos_lt_top
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (ha_pos : 0 < singleChannelLipConst d ϕ U i j)
    (ha_lt_top : singleChannelLipConst d ϕ U i j < ⊤) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ singleChannelLipConst d ϕ U i j * d i x y :=
  singleChannelLipConst_mem_of_pos_lt_top d ϕ hU ha_pos ha_lt_top

/--
OET anchor: h-57de7918859a9de2
**注（零下确界给出所有有限正常数界）** (HC02-P22)
当 $\underline{L}_{i \to j}(\phi; U) = 0$ 时，任意 $0 < \lambda < +\infty$ 均属于单通道可行族。
-/
theorem singleChannelFeasibleSet_of_const_eq_zero
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) {i j : I}
    (ha0 : singleChannelLipConst d ϕ U i j = 0)
    {r : ENNReal} (hr_pos : 0 < r) (_hr_lt_top : r < ⊤) :
    r ∈ SingleChannelFeasibleSet d ϕ U i j := by
  have hlt : sInf (SingleChannelFeasibleSet d ϕ U i j) < r := by
    unfold singleChannelLipConst at ha0
    rwa [ha0]
  rcases sInf_lt_iff.mp hlt with ⟨r0, hr0, hr0_lt⟩
  exact singleChannelFeasibleSet_upward_closed d ϕ hU hr0 hr0_lt.le

/--
用于证明零单通道下确界未必在 $\lambda = 0$ 处取到的五点载体空间 (HC02-P23)。
-/
inductive ZeroInfCounterX : Type
  | bot
  | x0
  | x1
  | y0
  | y1
  deriving DecidableEq

/-- 五点反例空间上的扩展伪度量：`y0` 与 `y1` 距离为 `1`，其余相异点对距离均为 `⊤`。 -/
def zeroInfCounterDist (_ : Unit) (p q : ZeroInfCounterX) : ENNReal :=
  match p, q with
  | .bot, .bot => 0
  | .x0, .x0 => 0
  | .x1, .x1 => 0
  | .y0, .y0 => 0
  | .y1, .y1 => 0
  | .y0, .y1 => 1
  | .y1, .y0 => 1
  | _, _ => ⊤

instance zeroInfCounterDist_extendedPseudoMetric :
    ∀ i : Unit, ExtendedPseudoMetric ZeroInfCounterX .bot (zeroInfCounterDist i) := by
  intro _
  refine
    { nonabsorbing := ⟨.x0, by intro h; cases h⟩
      dist_self := fun p => by cases p <;> rfl
      symm := fun p q => by cases p <;> cases q <;> rfl
      triangle := fun p q r => by
        cases p <;> cases q <;> cases r <;> simp [zeroInfCounterDist]
      isolate_bot := fun p hp => by
        cases p with
        | bot => exact False.elim (hp rfl)
        | x0 | x1 | y0 | y1 => rfl }

/-- 五点反例空间上的合法算子：将输入对 `(x0, x1)`（距离 `⊤`）映射为 `(y0, y1)`（距离 `1`）。 -/
def zeroInfCounterOp : Operator ZeroInfCounterX .bot where
  func
    | .bot => .bot
    | .x0 => .y0
    | .x1 => .y1
    | .y0 => .y0
    | .y1 => .y1
  preserves_bot := rfl

/-- 五点反例空间上的非空合法评估域 $U = \{x_0, x_1\} \subseteq \mathrm{dom}(\phi)$。 -/
def zeroInfCounterDomain : Set ZeroInfCounterX := {.x0, .x1}

/--
OET anchor: h-57de7918859a9de2
**反例（零单通道下确界未必由 $0$ 实现）** (HC02-P23)
构造合法扩展规范空间、合法算子 $\phi$ 与非空 $U \subseteq \mathrm{dom}(\phi)$，
使得 $\underline{L}_{i \to j}(\phi; U) = 0$，但 $\lambda = 0$ 不满足相应单通道标量上界。
-/
theorem zeroInfCounter_inf_zero_but_zero_not_feasible :
    zeroInfCounterDomain.Nonempty ∧
      zeroInfCounterDomain ⊆ dom zeroInfCounterOp ∧
      singleChannelLipConst zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () = 0 ∧
      (0 : ENNReal) ∉
        SingleChannelFeasibleSet zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () := by
  have h_ne : zeroInfCounterDomain.Nonempty := ⟨.x0, Or.inl rfl⟩
  have h_dom : zeroInfCounterDomain ⊆ dom zeroInfCounterOp := by
    intro x hx
    rcases hx with rfl | rfl
    · intro h; cases h
    · intro h; cases h
  have h_pos_mem :
      ∀ r : ENNReal, 0 < r →
        r ∈ SingleChannelFeasibleSet zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () := by
    intro r hr x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp [zeroInfCounterOp, zeroInfCounterDist]
    · simp [zeroInfCounterOp, zeroInfCounterDist, ENNReal.mul_top hr.ne']
    · simp [zeroInfCounterOp, zeroInfCounterDist, ENNReal.mul_top hr.ne']
    · simp [zeroInfCounterOp, zeroInfCounterDist]
  have h_inf_zero :
      singleChannelLipConst zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () = 0 := by
    by_contra h_ne_zero
    set a := singleChannelLipConst zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () ()
    have ha_pos : 0 < a := pos_iff_ne_zero.mpr h_ne_zero
    by_cases ha_top : a = ⊤
    · have h1_mem := h_pos_mem 1 zero_lt_one
      have h_le : a ≤ 1 := sInf_le h1_mem
      rw [ha_top] at h_le
      exact ENNReal.one_ne_top (le_antisymm le_top h_le)
    · have ha2_pos : 0 < a / 2 := ENNReal.div_pos ha_pos.ne' (by norm_num)
      have ha2_lt : a / 2 < a := ENNReal.half_lt_self ha_pos.ne' ha_top
      have ha2_mem := h_pos_mem (a / 2) ha2_pos
      exact (not_le_of_gt ha2_lt) (sInf_le ha2_mem)
  have h_zero_not_mem :
      (0 : ENNReal) ∉
        SingleChannelFeasibleSet zeroInfCounterDist zeroInfCounterOp zeroInfCounterDomain () () := by
    intro h0
    have h_bad := h0 .x0 (Or.inl rfl) .x1 (Or.inr rfl)
    simp [zeroInfCounterOp, zeroInfCounterDist] at h_bad
  exact ⟨h_ne, h_dom, h_inf_zero, h_zero_not_mem⟩

/-- 零单通道下确界未必由 $0$ 实现的存在性封装定理 (HC02-P23)。 -/
theorem exists_zero_singleChannelLipConst_not_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ k : I, ExtendedPseudoMetric X bot (d k))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
        singleChannelLipConst d ϕ U i j = 0 ∧
        (0 : ENNReal) ∉ SingleChannelFeasibleSet d ϕ U i j :=
  ⟨ZeroInfCounterX, Unit, .bot, inferInstance, inferInstance,
    zeroInfCounterDist, zeroInfCounterDist_extendedPseudoMetric,
    zeroInfCounterOp, zeroInfCounterDomain, (), (),
    zeroInfCounter_inf_zero_but_zero_not_feasible⟩

/--
用于说明单通道常数 $\underline{L}_{i \to j}(\phi; U)$ 与合法 Lip 矩阵条目 $[\mathbf{L}]_{i \to j}$ 为不同对象的双分量见证空间 (HC02-D08)。
-/
def twoBitDist (i : Bool) (p q : Option (Bool × Bool)) : ENNReal :=
  match p, q with
  | none, none => 0
  | some u, some v =>
    match i with
    | false => if u.1 = v.1 then 0 else 1
    | true => if u.2 = v.2 then 0 else 1
  | _, _ => ⊤

instance twoBitDist_extendedPseudoMetric :
    ∀ i : Bool, ExtendedPseudoMetric (Option (Bool × Bool)) none (twoBitDist i) := by
  intro i
  refine
    { nonabsorbing := ⟨some (false, false), by intro h; cases h⟩
      dist_self := fun p => by
        cases p with
        | none => rfl
        | some u => cases i <;> simp [twoBitDist]
      symm := fun p q => by
        cases p <;> cases q <;> cases i <;> simp [twoBitDist, eq_comm]
      triangle := fun p q r => by
        cases p with
        | none =>
          cases q <;> cases r <;> simp [twoBitDist]
        | some u =>
          cases r with
          | none =>
            cases q <;> simp [twoBitDist]
          | some w =>
            cases q with
            | none =>
              simp [twoBitDist]
            | some v =>
              rcases u with ⟨u1, u2⟩
              rcases v with ⟨v1, v2⟩
              rcases w with ⟨w1, w2⟩
              cases i <;>
                cases u1 <;> cases v1 <;> cases w1 <;>
                cases u2 <;> cases v2 <;> cases w2 <;>
                simp [twoBitDist]
      isolate_bot := fun p hp => by
        cases p with
        | none => exact False.elim (hp rfl)
        | some _ => rfl }

/-- 单通道常数 $\underline{L}_{i \to j}(\phi; U)$ 不等于一般合法 Lip 矩阵条目 $[\mathbf{L}]_{i \to j}$ 的具体见证 (HC02-D08)。 -/
theorem singleChannelLipConst_ne_lipMatrix_entry_witness :
    let ϕ : Operator (Option (Bool × Bool)) none := idOperator
    let U : Set (Option (Bool × Bool)) := dom ϕ
    channelId Bool ∈ RestrictedLipCertSet twoBitDist ϕ U ∧
      channelId Bool false true = 0 ∧
      singleChannelLipConst twoBitDist ϕ U false true = ⊤ ∧
      singleChannelLipConst twoBitDist ϕ U false true ≠ channelId Bool false true := by
  intro ϕ U
  have h_id_mem : channelId Bool ∈ RestrictedLipCertSet twoBitDist ϕ U := by
    refine ⟨Set.Subset.rfl, ?_⟩
    intro x _ y _ j
    rw [sum_channelId_mul_dist]
    exact le_rfl
  have h_off : channelId Bool false true = 0 :=
    channelId_offDiag (by intro h; cases h)
  have hx : some (false, false) ∈ U := by intro h; cases h
  have hy : some (false, true) ∈ U := by intro h; cases h
  have h_empty : SingleChannelFeasibleSet twoBitDist ϕ U false true = ∅ := by
    ext r
    refine ⟨fun hr => ?_, False.elim⟩
    have hle := hr _ hx _ hy
    simp [ϕ, idOperator, twoBitDist] at hle
  have h_top : singleChannelLipConst twoBitDist ϕ U false true = ⊤ := by
    simp [singleChannelLipConst, h_empty]
  refine ⟨h_id_mem, h_off, h_top, ?_⟩
  rw [h_top, h_off]
  exact ENNReal.top_ne_zero

/--
OET anchor: h-57de7918859a9de2
**注（单通道常数有限当且仅当存在有限可行标量常数）** (HC02-P24)
-/
theorem singleChannelLipConst_lt_top_iff
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} (hU : U ⊆ dom ϕ) (i j : I) :
    singleChannelLipConst d ϕ U i j < ⊤ ↔
      ∃ r : ENNReal, r < ⊤ ∧ r ∈ SingleChannelFeasibleSet d ϕ U i j := by
  constructor
  · intro ha_lt_top
    by_cases ha0 : singleChannelLipConst d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact singleChannelFeasibleSet_of_const_eq_zero d ϕ hU ha0 zero_lt_one ENNReal.one_lt_top
    · have ha_pos : 0 < singleChannelLipConst d ϕ U i j := pos_iff_ne_zero.mpr ha0
      exact ⟨singleChannelLipConst d ϕ U i j, ha_lt_top,
        singleChannelLipConst_mem_of_pos_lt_top d ϕ hU ha_pos ha_lt_top⟩
  · rintro ⟨r, hr_lt_top, hr_mem⟩
    exact lt_of_le_of_lt (sInf_le hr_mem) hr_lt_top

/-!
## 通道隔离、行/列解耦、对角体系与分辨保持 (HC02-D07, HC02-P25 .. HC02-P32)
-/

/-- 上界矩阵证书在通道 $(i, j)$ 处通道隔离：$L_{i \to j} = 0$ (HC02-D07)。 -/
def IsChannelIsolated {I : Type} (L : ChannelMatrix I) (i j : I) : Prop :=
  L i j = 0

/-- co-Lip 证书在通道 $(i, j)$ 处给出正下界传递：$K_{i \to j} > 0$ (HC02-D07)。 -/
def HasPosCoLipChannel {I : Type} (K : ChannelMatrix I) (i j : I) : Prop :=
  0 < K i j

/-- 单行稀疏谓词 `Row(L, i, j)`：固定输出行 $j$，除输入位置 $i$ 外其余条目全为 $0$ ($\forall k \ne i, L_{k \to j} = 0$) (HC02-D07)。 -/
def IsRowSparseAt {I : Type} (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- 矩阵关于输出分量 $j$ 行解耦：存在某个输入分量 $i \in I$ 使 `IsRowSparseAt L i j` 成立 (HC02-D07)。 -/
def IsRowDecoupledMatrix {I : Type} (L : ChannelMatrix I) (j : I) : Prop :=
  ∃ i : I, IsRowSparseAt L i j

/-- 算子 $\phi$ 在 $U$ 上关于输出分量 $d_j$ 行解耦：存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 使第 $j$ 行至多一项非零 (HC02-D07)。 -/
def IsRowDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (j : I) : Prop :=
  ∃ L ∈ RestrictedLipCertSet d ϕ U, IsRowDecoupledMatrix L j

/-- 单列稀疏谓词 `Col(L, i, j)`：固定输入列 $i$，除输出位置 $j$ 外其余条目全为 $0$ ($\forall k \ne j, L_{i \to k} = 0$) (HC02-D07)。 -/
def IsColSparseAt {I : Type} (L : ChannelMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/-- 矩阵关于输入分量 $i$ 列解耦：存在某个输出分量 $j \in I$ 使 `IsColSparseAt L i j` 成立 (HC02-D07)。 -/
def IsColDecoupledMatrix {I : Type} (L : ChannelMatrix I) (i : I) : Prop :=
  ∃ j : I, IsColSparseAt L i j

/-- 算子 $\phi$ 在 $U$ 上关于输入分量 $d_i$ 列解耦：存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 使第 $i$ 列至多一项非零 (HC02-D07)。 -/
def IsColDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (i : I) : Prop :=
  ∃ L ∈ RestrictedLipCertSet d ϕ U, IsColDecoupledMatrix L i

/-- 对角通道矩阵（完全解耦体系证书）：所有非对角条目全为 $0$ ($\forall i \ne j, L_{i \to j} = 0$) (HC02-D07)。 -/
def IsDiagonalChannelMatrix {I : Type} (L : ChannelMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- 给出完全解耦体系的合法受限上界证书谓词 (HC02-D07)。 -/
def IsFullyDecoupledCert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    (U : Set X) (L : ChannelMatrix I) : Prop :=
  L ∈ RestrictedLipCertSet d ϕ U ∧ IsDiagonalChannelMatrix L

theorem isDiagonalChannelMatrix_iff_forall_rowSparseAt {I : Type} (L : ChannelMatrix I) :
    IsDiagonalChannelMatrix L ↔ ∀ j : I, IsRowSparseAt L j j :=
  ⟨fun h j k hk => h k j hk, fun h i j hij => h j i hij⟩

/--
当 $L_{i \to j} = 0$ 时，允许任意扩展实数距离值（含 $d_i = +\infty$）下乘积项 $L_{i \to j} \cdot v = 0$ (HC02-P25)。
-/
theorem zero_coeff_mul_eq_zero {I : Type} {L : ChannelMatrix I} {i j : I}
    (h_iso : IsChannelIsolated L i j) (v : ENNReal) :
    L i j * v = 0 := by
  rw [h_iso, zero_mul]

/--
当 $L_{i \to j} = 0$ 时，输出分量 $j$ 的证书求和可删除输入项 $i$（允许 $d_i(x, y) = +\infty$）(HC02-P25)。
-/
theorem restrictedLip_sum_erase_of_zero_coeff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I} (hL : L ∈ RestrictedLipCertSet d ϕ U)
    {i j : I} (h_iso : IsChannelIsolated L i j) :
    (∀ x y : X, L i j * d i x y = 0) ∧
      (∀ x y : X, (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y) ∧
      (∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y) := by
  have h_term : ∀ x y : X, L i j * d i x y = 0 :=
    fun x y => zero_coeff_mul_eq_zero h_iso (d i x y)
  have h_sum : ∀ x y : X, (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
    intro x y
    rw [← Finset.add_sum_erase Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i),
      h_term x y, zero_add]
  refine ⟨h_term, h_sum, ?_⟩
  intro x hx y hy
  rw [← h_sum x y]
  exact hL.2 x hx y hy j

/--
任意唯一可能非零输入位置 $i$（不必有 $i = j$）下的单行化简：
若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 且 $\forall k \ne i, L_{k \to j} = 0$，
则 $\forall x, y \in U,\; d_j(\phi(x), \phi(y)) \le L_{i \to j} \cdot d_i(x, y)$ (HC02-P26)。
-/
theorem restrictedLip_bound_of_rowSparseAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I} (hL : L ∈ RestrictedLipCertSet d ϕ U)
    {i j : I} (h_row : IsRowSparseAt L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have h := hL.2 x hx y hy j
  rwa [Fintype.sum_eq_single i (fun k hk => by rw [h_row k hk, zero_mul])] at h

/-- 行解耦算子存在给出单输入分量标量上界的受限证书 (HC02-P26)。 -/
theorem exists_single_input_bound_of_rowDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {j : I} (h_dec : IsRowDecoupled d ϕ U j) :
    ∃ L ∈ RestrictedLipCertSet d ϕ U, ∃ i : I,
      IsRowSparseAt L i j ∧ ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  rcases h_dec with ⟨L, hL, i, h_row⟩
  exact ⟨L, hL, i, h_row, restrictedLip_bound_of_rowSparseAt d ϕ hL h_row⟩

/--
任意单列支撑证书的贡献范围：若固定输入 $i$ 列仅输出 $j$ 可能非零（`IsColSparseAt L i j`），
则对一切 $k \ne j$ 恒有 $L_{i \to k} d_i(x, y) = 0$，该证书中输入 $i$ 至多向输出 $j$ 的上界贡献非零项 (HC02-P27)。
-/
theorem colSparseAt_contribution_range {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I} (hL : L ∈ RestrictedLipCertSet d ϕ U)
    {i j : I} (h_col : IsColSparseAt L i j) :
    (∀ k : I, k ≠ j → ∀ x y : X, L i k * d i x y = 0) ∧
      (∀ k : I, ∀ x y : X, L i k * d i x y ≠ 0 → k = j) ∧
      (∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y) := by
  have h_zero : ∀ k : I, k ≠ j → ∀ x y : X, L i k * d i x y = 0 := by
    intro k hkj x y
    rw [h_col k hkj, zero_mul]
  have h_only_j : ∀ k : I, ∀ x y : X, L i k * d i x y ≠ 0 → k = j := by
    intro k x y h_ne
    by_contra hkj
    exact h_ne (h_zero k hkj x y)
  refine ⟨h_zero, h_only_j, ?_⟩
  intro k hkj x hx y hy
  exact (restrictedLip_sum_erase_of_zero_coeff d ϕ hL (h_col k hkj)).2.2 x hx y hy

/--
完全解耦（对角）Lip 矩阵给出所有分量的独立标量放缩上界 (HC02-P28)。
-/
theorem diagonalLip_componentwise_upper_bounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U) (h_diag : IsDiagonalChannelMatrix L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact restrictedLip_bound_of_rowSparseAt d ϕ hL (fun k hk => h_diag k j hk)

/-- 任一合法受限 co-Lip 矩阵在任意通道 $(i, j)$ 上均给出单输入项下界 $K_{i \to j} d_i(x, y) \le d_j(\phi(x), \phi(y))$。 -/
theorem restrictedCoLip_single_channel_lower_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {K : ChannelMatrix I} (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  calc
    K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
OET anchor: h-6a98a58b5bc95360
**引理（对角输入项的标量双侧界）** (HC02-P29)
仅假设 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 在输出行 $j$ 满足 $\forall k \ne j, L_{k \to j} = 0$，
以及一般合法 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$（无需假设 $\mathbf{K}$ 行稀疏），
即得 $K_{j \to j} d_j(x, y) \le d_j(\phi(x), \phi(y)) \le L_{j \to j} d_j(x, y)$。
-/
theorem scalar_two_sided_bound_of_diag_lip_row {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {j : I}
    {L K : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U)
    (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (h_row : IsRowSparseAt L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  exact ⟨restrictedCoLip_single_channel_lower_bound d ϕ hK j j x hx y hy,
    restrictedLip_bound_of_rowSparseAt d ϕ hL h_row x hx y hy⟩

/--
当对角输入项 Lip 行条件对所有 $j \in I$ 成立时，全部分量同时满足标量双侧不等式 (HC02-P30)。
-/
theorem componentwise_two_sided_bounds_of_all_diag_lip_rows
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L K : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U)
    (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (h_rows : ∀ j : I, IsRowSparseAt L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  fun j => scalar_two_sided_bound_of_diag_lip_row d ϕ hL hK (h_rows j)

/--
逐分量双侧界的有限标量系数分支：若另有 $\forall j \in I,\; L_{j \to j}, K_{j \to j} < +\infty$，
则可提取有限非负实数标量族 `k_fin l_fin : I → NNReal` 实现全部分量的有限标量双侧放缩界 (HC02-P30)。
-/
theorem finite_componentwise_two_sided_bounds
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {L K : ChannelMatrix I}
    (hL : L ∈ RestrictedLipCertSet d ϕ U)
    (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (h_rows : ∀ j : I, IsRowSparseAt L j j)
    (h_fin : ∀ j : I, L j j < ⊤ ∧ K j j < ⊤) :
    ∃ (k_fin l_fin : I → NNReal),
      (∀ j : I, (k_fin j : ENNReal) = K j j ∧ (l_fin j : ENNReal) = L j j) ∧
      (∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
        (k_fin j : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ (l_fin j : ENNReal) * d j x y) := by
  refine ⟨fun j => (K j j).toNNReal, fun j => (L j j).toNNReal, ?_, ?_⟩
  · intro j
    exact ⟨ENNReal.coe_toNNReal (h_fin j).2.ne, ENNReal.coe_toNNReal (h_fin j).1.ne⟩
  · intro j x hx y hy
    rw [ENNReal.coe_toNNReal (h_fin j).2.ne, ENNReal.coe_toNNReal (h_fin j).1.ne]
    exact componentwise_two_sided_bounds_of_all_diag_lip_rows d ϕ hL hK h_rows j x hx y hy

/--
OET anchor: h-f82672ec0dd48f28
**命题（正 co-Lip 通道的可分辨保持 (i)）** (HC02-P31)
若 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且 $K_{i \to j} > 0$，
则对任意 $x, y \in U$，$d_i(x, y) > 0 \Rightarrow d_j(\phi(x), \phi(y)) > 0$。
-/
theorem pos_coLip_channel_preserves_distinguishability
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {K : ChannelMatrix I} (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    {i j : I} (hK_pos : HasPosCoLipChannel K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hd_pos
  have h_prod_pos : 0 < K i j * d i x y := ENNReal.mul_pos hK_pos.ne' hd_pos.ne'
  exact lt_of_lt_of_le h_prod_pos
    (restrictedCoLip_single_channel_lower_bound d ϕ hK i j x hx y hy)

/--
OET anchor: h-f82672ec0dd48f28
**命题（正 co-Lip 对角通道反射族零距关系 (ii)）** (HC02-P32)
若 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且对所有 $j \in I$ 有 $K_{j \to j} > 0$，
则对任意 $x, y \in U$，$\phi(x) \sim_{\mathcal{G}} \phi(y) \Rightarrow x \sim_{\mathcal{G}} y$。
-/
theorem pos_diag_coLip_reflects_gaugeZeroRelated
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    [∀ k : I, ExtendedPseudoMetric X bot (d k)]
    {U : Set X} {K : ChannelMatrix I} (hK : K ∈ RestrictedCoLipCertSet d ϕ U)
    (hK_diag : ∀ j : I, HasPosCoLipChannel K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy h_img_zero j
  by_contra h_ne
  have hd_pos : 0 < d j x y := pos_iff_ne_zero.mpr h_ne
  have h_out_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_coLip_channel_preserves_distinguishability d ϕ hK (hK_diag j) x hx y hy hd_pos
  exact h_out_pos.ne' (h_img_zero j)

end

end formal_oet.vol_01.ch_02_operator_bounds
