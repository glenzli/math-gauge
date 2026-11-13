import GaugeMatrix

/-!
# 第 2 章 算子界：分量通道、通道可分辨性与标量双侧界

对应 `source/02-operator-bounds.md` §2.2 与 §2.3 习题 2.2：
- `CH02-D07`（锚点 `oet-7fa97eb6e24d5527`）：单输入通道、单行稀疏与对角特例
- `CH02-P19`（锚点 `oet-7fa97eb6e24d5527`）：单一输入项行化简（含对角特例）
- `CH02-P20`（锚点 `oet-f82672ec0dd48f28`）：命题 2.8(i)，正 co-Lip 通道保持正距离
- `CH02-P21`（锚点 `oet-f82672ec0dd48f28`）：命题 2.8(ii)，全对角正 co-Lip 反射族零距（不加强为点相等）
- `CH02-P25`（锚点 `oet-6a98a58b5bc95360`）：习题 2.2，对角输入项的标量双侧界
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-! ## CH02-D07：单输入通道、单行稀疏与对角特例 -/

/--
分量通道：从输入分量 `d_{input}` 到输出分量 `d_{output}` 的有序对 `(input, output)`。
-/
@[ext]
structure ComponentChannel (I : Type) where
  input : I
  output : I
  deriving DecidableEq

/-- 同分量通道 `(i, i)`。 -/
def sameComponentChannel {I : Type} (i : I) : ComponentChannel I :=
  ⟨i, i⟩

/-- 规范矩阵 `M` 在分量通道 `c` 上对应的系数 `M_{c.input → c.output}`。 -/
def channelCoeff {I : Type} (M : GaugeMatrix I) (c : ComponentChannel I) : ENNReal :=
  channelEntry M c.input c.output

@[simp]
theorem channelCoeff_mk {I : Type} (M : GaugeMatrix I) (i j : I) :
    channelCoeff M ⟨i, j⟩ = channelEntry M i j := rfl

@[simp]
theorem channelCoeff_sameComponentChannel {I : Type} (M : GaugeMatrix I) (i : I) :
    channelCoeff M (sameComponentChannel i) = channelEntry M i i := rfl

/--
通道零系数谓词：`M_{c.input → c.output} = 0`，表示该输入分量不参与对应输出分量的上界。
-/
def IsInactiveChannel {I : Type} (M : GaugeMatrix I) (c : ComponentChannel I) : Prop :=
  channelCoeff M c = 0

/--
单行稀疏 / 单一输入项谓词：
矩阵 `M` 的第 `j` 行（对应输出分量 `d_j`）除通道 `(i, j)` 的条目 `M_{i → j}` 外均为零。
-/
def IsSingleInputRow {I : Type} (M : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → channelEntry M k j = 0

/--
第 `j` 行仅保留对角输入项 `M_{j → j}` 的特殊情形：`∀ k ≠ j, M_{k → j} = 0`。
-/
abbrev IsDiagonalInputRow {I : Type} (M : GaugeMatrix I) (j : I) : Prop :=
  IsSingleInputRow M j j

/--
对角规范矩阵谓词：所有非对角分量通道 `(i, j)` (`i ≠ j`) 均取零。
-/
def IsDiagonalMatrix {I : Type} (M : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → channelEntry M i j = 0

/-- 由对角权函数 `w : I → ENNReal` 构造对角规范矩阵。 -/
def diagonalGaugeMatrix {I : Type} [DecidableEq I] (w : I → ENNReal) : GaugeMatrix I :=
  Matrix.diagonal w

@[simp]
theorem channelEntry_diagonalGaugeMatrix {I : Type} [DecidableEq I]
    (w : I → ENNReal) (i j : I) :
    channelEntry (diagonalGaugeMatrix w) i j = if j = i then w i else 0 := by
  by_cases h : j = i
  · subst h
    simp [channelEntry, diagonalGaugeMatrix]
  · simp [channelEntry, diagonalGaugeMatrix, h]

theorem diagonalGaugeMatrix_isDiagonal {I : Type} [DecidableEq I] (w : I → ENNReal) :
    IsDiagonalMatrix (diagonalGaugeMatrix w) := by
  intro i j hij
  simp [hij.symm]

theorem one_isDiagonalMatrix {I : Type} [DecidableEq I] :
    IsDiagonalMatrix (1 : GaugeMatrix I) := by
  intro i j hij
  simp [channelEntry_one, hij.symm]

/-- 矩阵为对角矩阵当且仅当每一行均仅保留同分量（对角）输入项。 -/
theorem isDiagonalMatrix_iff_forall_singleInputRow {I : Type} (M : GaugeMatrix I) :
    IsDiagonalMatrix M ↔ ∀ i : I, IsSingleInputRow M i i := by
  constructor
  · intro hdiag i k hki
    exact hdiag k i hki
  · intro hrows i j hij
    exact hrows j i hij

/-! ## CH02-P19：单一输入项行化简；包含对角特例 -/

/--
零条目不参与输出上界求和：若 `M_{c.input → c.output} = 0`，
则从全指标和中剔除 `c.input` 后和不变。
-/
theorem sum_omit_of_inactive_channel {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (M : GaugeMatrix I) (c : ComponentChannel I)
    (hc : IsInactiveChannel M c) (x y : X) :
    ∑ k : I, channelEntry M k c.output * d k x y =
      ∑ k ∈ Finset.univ.erase c.input, channelEntry M k c.output * d k x y := by
  have hterm : channelEntry M c.input c.output * d c.input x y = 0 := by
    have hc' : channelEntry M c.input c.output = 0 := hc
    simp [hc']
  rw [← Finset.add_sum_erase Finset.univ (fun k => channelEntry M k c.output * d k x y)
    (Finset.mem_univ c.input), hterm, zero_add]

/--
单行稀疏矩阵求和坍缩引理：
若第 `j` 行除 `L_{i → j}` 外均为零，则 `∑ k, L_{k → j} * d_k(x, y) = L_{i → j} * d_i(x, y)`。
-/
theorem sum_eq_single_of_singleInputRow {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) (i j : I)
    (hrow : IsSingleInputRow L i j) (x y : X) :
    ∑ k : I, channelEntry L k j * d k x y = channelEntry L i j * d i x y := by
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/--
单一输入项行化简：
设 `L ∈ ℒ(ϕ)|_U`，且第 `j` 行除 `L_{i → j}` 外均为零，则对任意 `x, y ∈ U`，
Lip 不等式化为 `d_j(ϕ(x), ϕ(y)) ≤ ∑ k, L_{k → j} * d_k(x, y) = L_{i → j} * d_i(x, y)`
及直接标量上界 `d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} * d_i(x, y)`。
-/
theorem singleInputRow_lip_reduction {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (i j : I) (hL : L ∈ restrictedLipMatrices d ϕ U) (hrow : IsSingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k j * d k x y ∧
      ∑ k : I, channelEntry L k j * d k x y = channelEntry L i j * d i x y ∧
      d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L i j * d i x y := by
  intro x hx y hy
  have hlip : d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k j * d k x y :=
    hL.2 x hx y hy j
  have hsum : ∑ k : I, channelEntry L k j * d k x y = channelEntry L i j * d i x y :=
    sum_eq_single_of_singleInputRow d L i j hrow x y
  refine ⟨hlip, hsum, ?_⟩
  rw [← hsum]
  exact hlip

/--
对角特例化简：
若 `L ∈ ℒ(ϕ)|_U` 为对角矩阵，则对每个同分量通道 `(i, i)` 与任意 `x, y ∈ U`，
均有 `d_i(ϕ(x), ϕ(y)) ≤ ∑ k, L_{k → i} * d_k(x, y) = L_{i → i} * d_i(x, y)`
及直接标量上界 `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} * d_i(x, y)`。
-/
theorem diagonal_lip_reduction {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipMatrices d ϕ U) (hdiag : IsDiagonalMatrix L) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k i * d k x y ∧
      ∑ k : I, channelEntry L k i * d k x y = channelEntry L i i * d i x y ∧
      d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  intro i
  have hrow : IsSingleInputRow L i i :=
    (isDiagonalMatrix_iff_forall_singleInputRow L).mp hdiag i
  exact singleInputRow_lip_reduction d ϕ U L i i hL hrow

/-! ## CH02-P20 与 CH02-P21：命题 2.8（正 co-Lip 通道保持可分辨性与反射族零距） -/

/--
**命题 2.8(i)（正 co-Lip 通道保持正距离）**
设 `K ∈ 𝒦(ϕ)|_U`。若 `K_{i → j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x, y) > 0 → d_j(ϕ(x), ϕ(y)) > 0`。
-/
theorem pos_colip_channel_preserves_pos_dist {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (i j : I) (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hKpos : 0 < channelEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdpos
  have hcolip : ∑ k : I, channelEntry K k j * d k x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    hK.2.2 x hx y hy j
  have hterm : channelEntry K i j * d i x y ≤ ∑ k : I, channelEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k => channelEntry K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have hmul : 0 < channelEntry K i j * d i x y :=
    ENNReal.mul_pos hKpos.ne' hdpos.ne'
  exact lt_of_lt_of_le hmul (le_trans hterm hcolip)

/-- 命题 2.8(i) 的 `ComponentChannel` 形式封装。 -/
theorem pos_colip_componentChannel_preserves_pos_dist {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (c : ComponentChannel I) (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hcpos : 0 < channelCoeff K c) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d c.input x y → 0 < d c.output (ϕ.func x) (ϕ.func y) :=
  pos_colip_channel_preserves_pos_dist d ϕ U K c.input c.output hK hcpos

/--
**命题 2.8(ii)（全对角正 co-Lip 反射族零距关系）**
设 `K ∈ 𝒦(ϕ)|_U`。若 `K_{j → j} > 0` 对所有 `j ∈ I` 成立，则 `ϕ` 在 `U` 上反射族零距关系：
对任意 `x, y ∈ U`，`GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y`。
按正文约定不预设族分离性，结论不加强为 `x = y`。
-/
theorem diag_pos_colip_reflects_gauge_zero_related {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hdiag : ∀ j : I, 0 < channelEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hne
  have hdpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have himgpos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_colip_channel_preserves_pos_dist d ϕ U K j j hK (hdiag j) x hx y hy hdpos
  exact himgpos.ne' (hzero j)

/--
不加强为点相等的反例验证：
在完全满足 `ExtendedPseudoMetric` 与有限非空指标族 `I` 的扩展规范空间上，
即使存在 `K ∈ 𝒦(ϕ)|_U` 且所有对角元 `K_{j → j} > 0`，对满足 `ϕ(x) ∼_𝒢 ϕ(y)` 的 `x, y ∈ U`
仍不能推出 `x = y`。
-/
theorem diag_pos_colip_not_implies_eq :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i : I, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I),
      K ∈ restrictedCoLipMatrices d ϕ U ∧
      (∀ j : I, 0 < channelEntry K j j) ∧
      ∃ x ∈ U, ∃ y ∈ U, GaugeZeroRelated d (ϕ.func x) (ϕ.func y) ∧ x ≠ y := by
  let bot : Fin 3 := 2
  let d : Unit → Fin 3 → Fin 3 → ENNReal := fun _ x y =>
    if x = y then 0 else if x = bot ∨ y = bot then ⊤ else 0
  have hd : ∀ i : Unit, ExtendedPseudoMetric (Fin 3) bot (d i) := fun _ =>
    { nonabsorbing := ⟨0, by decide⟩
      dist_self := fun x => by simp [d]
      symm := fun x y => by
        dsimp [d]
        by_cases hxy : x = y
        · subst hxy; simp
        · have hyx : y ≠ x := Ne.symm hxy
          simp [hxy, hyx, or_comm]
      triangle := fun x y z => by
        fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [d, bot]
      isolate_bot := fun x hx => by
        fin_cases x <;> simp_all [d, bot] }
  let ϕ : Operator (Fin 3) bot := operator_identity
  let U : Set (Fin 3) := {0, 1}
  let K : GaugeMatrix Unit := 1
  refine ⟨Fin 3, Unit, bot, inferInstance, inferInstance, d, hd, ϕ, U, K, ?_, ?_, ?_⟩
  · refine ⟨⟨0, by simp [U]⟩, ?_, ?_⟩
    · intro x hx
      rcases hx with rfl | rfl <;> simp [dom, ϕ, operator_identity, bot]
    · intro x hx y hy j
      simp [K, channelEntry, ϕ, operator_identity]
  · intro j
    simp [K, channelEntry]
  · refine ⟨0, by simp [U], 1, by simp [U], ?_, by decide⟩
    intro i
    simp [d, ϕ, operator_identity, bot]

/-! ## CH02-P25：习题 2.2（对角输入项的标量双侧界） -/

/--
**习题 2.2（对角输入项的标量双侧界）**
设 `L ∈ ℒ(ϕ)|_U` 与 `K ∈ 𝒦(ϕ)|_U`（均已蕴含 `U ⊆ dom ϕ`，且 `K` 蕴含 `U.Nonempty`）。
若第 `j` 行仅保留对角输入项（`∀ k ≠ j, L_{k → j} = 0`），则对任意 `x, y ∈ U`：
`K_{j → j} * d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} * d_j(x, y)`。
-/
theorem scalar_two_sided_bound_of_diagonal_input {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L K : GaugeMatrix I) (j : I)
    (hL : L ∈ restrictedLipMatrices d ϕ U)
    (hK : K ∈ restrictedCoLipMatrices d ϕ U)
    (hdiag_row : IsDiagonalInputRow L j) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L j j * d j x y := by
  intro x hx y hy
  constructor
  · have hterm : channelEntry K j j * d j x y ≤ ∑ k : I, channelEntry K k j * d k x y :=
      Finset.single_le_sum (f := fun k => channelEntry K k j * d k x y)
        (fun _ _ => zero_le _) (Finset.mem_univ j)
    exact le_trans hterm (hK.2.2 x hx y hy j)
  · exact (singleInputRow_lip_reduction d ϕ U L j j hL hdiag_row x hx y hy).2.2

end LCH01
