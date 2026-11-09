import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lch02_matrix

/-!
# LCH02 · 第 2 章 · Lip / co-Lip 矩阵证书族

（原文：Zhe Li 著 *The Operator Evolution Theory*，CC BY 4.0；署名与改动说明见 `Main.lean`。）

对应 `source/02-operator-bounds.md` §2.1 中的

* Lipschitz 上界矩阵：全域与子集受限的谓词与证书族 `ℒ(ϕ)`、`ℒ(ϕ)|_U`（`CH02-D01`）；
* co-Lipschitz 下界矩阵：含非空条件的受限谓词与证书族 `𝒦(ϕ)|_U`（`CH02-D02`）；
* 单分量退化（`CH02-P01`）、引理 2.1（`CH02-P02`、`CH02-P03`）、
  引理 2.3（`CH02-P05`、`CH02-P06`）、co-Lip 条目为零的充分条件（`CH02-P07`）。

**表示约定**

* 规范族 `𝒢 = {d_i}_{i∈I}` 取为 `d : I → X → X → ENNReal`；定理中保留正文的标准语境：
  `I` 有限非空（`[Fintype I] [Nonempty I]`），每个 `d i` 是以 `bot` 为吸收元的扩展伪度量
  （`hd : ∀ i, ExtendedPseudoMetric X bot (d i)`，来自冻结模块 `gauge_space`）。
  本文件的证明不使用这些公理，故它们仅作语境保留（相应的未使用变量提示已关闭）。
* 算子取冻结模块 `operator_space` 的 `Operator X bot`，`dom ϕ` 取该模块的 `dom`。
* 矩阵取 `Matrix I I ENNReal`，`L_{i→j}` 记为 `arrowEntry L i j`（第 `j` 行第 `i` 列，见
  `lch02_matrix`）；`ℝ̄₊` 算术即 `ENNReal` 算术（`0 * ⊤ = 0`，`a * ⊤ = ⊤`（`a > 0`））。
* 受限证书族 `ℒ(ϕ)|_U` 的定义本身以 `U ⊆ dom ϕ` 为前提（正文 "对子集 `U ⊆ dom(ϕ)`"），
  故该条件写入成员谓词；`𝒦(ϕ)|_U` 另含非空条件 `U ≠ ∅`（正文 "凡出现 `𝒦(ϕ)|_U`，
  均包含这里的非空性条件"）。证书族是 `Set (Matrix I I ENNReal)`，不预设极值矩阵。
-/

set_option linter.unusedVariables false

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-! ### CH02-D01 · 全域/受限 Lip 矩阵谓词与证书族 -/

/--
OET anchor: h-af85899693cc8750 （CH02-D01）
**合法 Lipschitz 矩阵（全域）**：对所有 `x y ∈ dom ϕ` 与所有 `j ∈ I`，
`d_j(ϕ x, ϕ y) ≤ ∑_{i ∈ I} L_{i→j} · d_i(x, y)`。
-/
def IsLipMatrix [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (L : Matrix I I ENNReal) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y

/--
OET anchor: h-af85899693cc8750 （CH02-D01）
**子集受限 Lip 矩阵**：对子集 `U ⊆ dom ϕ`，若对任意 `x y ∈ U` 与所有 `j ∈ I` 上述距离放缩不等式成立，
则称 `L` 为 `ϕ` 在 `U` 上的受限 Lip 矩阵。
-/
def IsLipMatrixOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : Matrix I I ENNReal) : Prop :=
  U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, arrowEntry L i j * d i x y

/-- OET anchor: h-af85899693cc8750 （CH02-D01）全体合法 Lip 矩阵之集 `ℒ(ϕ)`（证书族）。 -/
def lipCerts [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    Set (Matrix I I ENNReal) :=
  {L | IsLipMatrix d ϕ L}

/-- OET anchor: h-af85899693cc8750 （CH02-D01）`ϕ` 在 `U` 上的全体受限 Lip 矩阵之集 `ℒ(ϕ)|_U`（证书族）。 -/
def lipCertsOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {L | IsLipMatrixOn d ϕ U L}

/-- 广义 Lip 约定：`d_i(x,y) = 0` 时，无论 `L_{i→j}` 取何值（含 `+∞`），该项对右端求和的贡献为零。 -/
theorem lip_term_eq_zero_of_dist_eq_zero (d : I → X → X → ENNReal) (L : Matrix I I ENNReal)
    (i j : I) {x y : X} (h : d i x y = 0) : arrowEntry L i j * d i x y = 0 := by
  rw [h, mul_zero]

section lipBasic

variable [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)

theorem mem_lipCerts_iff (L : Matrix I I ENNReal) : L ∈ lipCerts d ϕ ↔ IsLipMatrix d ϕ L :=
  Iff.rfl

theorem mem_lipCertsOn_iff (U : Set X) (L : Matrix I I ENNReal) :
    L ∈ lipCertsOn d ϕ U ↔ IsLipMatrixOn d ϕ U L :=
  Iff.rfl

/-- 全域 Lip 矩阵就是在 `U = dom ϕ` 上的受限 Lip 矩阵。 -/
theorem isLipMatrix_iff_isLipMatrixOn_dom (L : Matrix I I ENNReal) :
    IsLipMatrix d ϕ L ↔ IsLipMatrixOn d ϕ (dom ϕ) L :=
  ⟨fun h => ⟨subset_rfl, h⟩, fun h => h.2⟩

/-- `ℒ(ϕ) = ℒ(ϕ)|_{dom ϕ}`。 -/
theorem lipCerts_eq_lipCertsOn_dom : lipCerts d ϕ = lipCertsOn d ϕ (dom ϕ) := by
  ext L
  exact isLipMatrix_iff_isLipMatrixOn_dom d ϕ L

/-- 受限 Lip 矩阵的成员蕴含定义域条件 `U ⊆ dom ϕ`。 -/
theorem subset_dom_of_mem_lipCertsOn {U : Set X} {L : Matrix I I ENNReal}
    (h : L ∈ lipCertsOn d ϕ U) : U ⊆ dom ϕ := h.1

/-- 广义 Lip 约定：`L_{i→j} = +∞` 且 `d_i(x,y) > 0` 时，该项为 `+∞`，故右端求和为 `+∞`，不等式平凡成立。 -/
theorem lip_sum_eq_top_of_entry_top (L : Matrix I I ENNReal) (i j : I) {x y : X}
    (hL : arrowEntry L i j = ⊤) (hpos : 0 < d i x y) :
    ∑ k, arrowEntry L k j * d k x y = ⊤ := by
  have hterm : arrowEntry L i j * d i x y = ⊤ := by
    rw [hL, ENNReal.top_mul hpos.ne']
  have hle : arrowEntry L i j * d i x y ≤ ∑ k, arrowEntry L k j * d k x y :=
    Finset.single_le_sum (f := fun k => arrowEntry L k j * d k x y) (fun _ _ => zero_le _)
      (Finset.mem_univ i)
  rw [hterm] at hle
  exact top_le_iff.1 hle

end lipBasic

/-! ### CH02-D02 · 含非空条件的受限 co-Lip 矩阵及证书族 -/

/--
OET anchor: h-af85899693cc8750 （CH02-D02）
**合法受限 co-Lipschitz 矩阵**：对 `ϕ` 与给定的**非空**子集 `U ⊆ dom ϕ`，
若对所有 `x y ∈ U` 与所有 `j ∈ I`，`d_j(ϕ x, ϕ y) ≥ ∑_{i ∈ I} K_{i→j} · d_i(x, y)`，
则称 `K` 为 `ϕ` 在 `U` 上的合法受限 co-Lip 矩阵。非空性 `U ≠ ∅` 是成员谓词的一部分。
-/
def IsCoLipMatrixOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : Matrix I I ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i, arrowEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- OET anchor: h-af85899693cc8750 （CH02-D02）`ϕ` 在 `U` 上的全体合法 co-Lip 矩阵之集 `𝒦(ϕ)|_U`（下界证书族，含 `U ≠ ∅`）。 -/
def coLipCertsOn [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {K | IsCoLipMatrixOn d ϕ U K}

/-- OET anchor: h-893b1d33535f7245 / h-88784dcbfff0ea66 （CH02-D02）全域 co-Lip 矩阵之集 `𝒦(ϕ)|_{dom ϕ}`。 -/
def coLipCerts [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    Set (Matrix I I ENNReal) :=
  coLipCertsOn d ϕ (dom ϕ)

section coLipBasic

variable [Fintype I] (d : I → X → X → ENNReal) (ϕ : Operator X bot)

theorem mem_coLipCertsOn_iff (U : Set X) (K : Matrix I I ENNReal) :
    K ∈ coLipCertsOn d ϕ U ↔ IsCoLipMatrixOn d ϕ U K :=
  Iff.rfl

/-- 全域 co-Lip 矩阵之集即 `𝒦(ϕ)|_{dom ϕ}`。 -/
theorem coLipCerts_eq : coLipCerts d ϕ = coLipCertsOn d ϕ (dom ϕ) := rfl

/-- 凡出现 `𝒦(ϕ)|_U` 的成员，均含非空性条件 `U ≠ ∅`。 -/
theorem nonempty_of_mem_coLipCertsOn {U : Set X} {K : Matrix I I ENNReal}
    (h : K ∈ coLipCertsOn d ϕ U) : U.Nonempty := h.1

/-- co-Lip 成员蕴含定义域条件 `U ⊆ dom ϕ`。 -/
theorem subset_dom_of_mem_coLipCertsOn {U : Set X} {K : Matrix I I ENNReal}
    (h : K ∈ coLipCertsOn d ϕ U) : U ⊆ dom ϕ := h.2.1

/-- 空集上没有 co-Lip 矩阵（非空性条件）。 -/
theorem coLipCertsOn_empty : coLipCertsOn d ϕ (∅ : Set X) = ∅ := by
  ext K
  simp [coLipCertsOn, IsCoLipMatrixOn]

end coLipBasic

/-! ### CH02-P01 · 单分量求和退化为标量 Lip 界 -/

/--
OET anchor: h-c4369c63c86cbacf （CH02-P01）
**注（单分量情形下的标量 Lip 界）**：当 `|I| = 1` 且 `I = {i}` 时，Lip 矩阵条件退化为单个标量不等式
`d_i(ϕ x, ϕ y) ≤ L_{i→i} d_i(x, y)`（`x y ∈ dom ϕ`）。
-/
theorem mem_lipCerts_iff_scalar [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot)
    (L : Matrix I I ENNReal) {i : I} (hI : ∀ j : I, j = i) :
    L ∈ lipCerts d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ arrowEntry L i i * d i x y := by
  have hsum : ∀ f : I → ENNReal, ∑ k, f k = f i := fun f =>
    Fintype.sum_eq_single i fun k hk => absurd (hI k) hk
  constructor
  · intro h x hx y hy
    have := h x hx y hy i
    rwa [hsum] at this
  · intro h x hx y hy j
    obtain rfl := hI j
    rw [hsum]
    exact h x hx y hy

/-- `CH02-P01` 的子集受限形式：`L ∈ ℒ(ϕ)|_U` 当且仅当 `U ⊆ dom ϕ` 且标量不等式在 `U` 上成立。 -/
theorem mem_lipCertsOn_iff_scalar [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (L : Matrix I I ENNReal) {i : I} (hI : ∀ j : I, j = i) :
    L ∈ lipCertsOn d ϕ U ↔
      U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U,
        d i (ϕ.func x) (ϕ.func y) ≤ arrowEntry L i i * d i x y := by
  have hsum : ∀ f : I → ENNReal, ∑ k, f k = f i := fun f =>
    Fintype.sum_eq_single i fun k hk => absurd (hI k) hk
  constructor
  · rintro ⟨hU, h⟩
    refine ⟨hU, fun x hx y hy => ?_⟩
    have := h x hx y hy i
    rwa [hsum] at this
  · rintro ⟨hU, h⟩
    refine ⟨hU, fun x hx y hy j => ?_⟩
    obtain rfl := hI j
    rw [hsum]
    exact h x hx y hy

/-! ### CH02-P02 / CH02-P03 · 引理 2.1（受限 Lip 矩阵族的单调性） -/

/--
OET anchor: h-4ff5c58d71e1651f （CH02-P02）
**引理 2.1（反单调）**：固定算子 `ϕ`。若 `U ⊆ V ⊆ dom ϕ`，则 `ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U`。
-/
theorem lipCertsOn_antitone [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) : lipCertsOn d ϕ V ⊆ lipCertsOn d ϕ U := by
  intro L hL
  exact ⟨hUV.trans hV, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/--
OET anchor: h-4ff5c58d71e1651f （CH02-P03）
**引理 2.1（全域证书可限制）**：对任意 `U ⊆ dom ϕ`，`ℒ(ϕ) ⊆ ℒ(ϕ)|_U`。
证明即取 `V = dom ϕ` 的特例。
-/
theorem lipCerts_subset_lipCertsOn [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom ϕ) : lipCerts d ϕ ⊆ lipCertsOn d ϕ U := by
  rw [lipCerts_eq_lipCertsOn_dom]
  exact lipCertsOn_antitone d hd ϕ hU subset_rfl

/-! ### CH02-P05 / CH02-P06 · 引理 2.3（受限 co-Lip 矩阵族的单调性） -/

/--
OET anchor: h-893b1d33535f7245 （CH02-P05）
**引理 2.3（反单调）**：固定算子 `ϕ`。若 `∅ ≠ U ⊆ V ⊆ dom ϕ`，则 `𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U`。
-/
theorem coLipCertsOn_antitone [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) {U V : Set X}
    (hU : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    coLipCertsOn d ϕ V ⊆ coLipCertsOn d ϕ U := by
  intro K hK
  exact ⟨hU, hUV.trans hV, fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

/--
OET anchor: h-893b1d33535f7245 （CH02-P06）
**引理 2.3（全域证书可限制）**：对任意非空子集 `U ⊆ dom ϕ`，`𝒦(ϕ)|_{dom ϕ} ⊆ 𝒦(ϕ)|_U`。
证明即取 `V = dom ϕ` 的特例。
-/
theorem coLipCerts_subset_coLipCertsOn [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) {U : Set X}
    (hU : U.Nonempty) (hUd : U ⊆ dom ϕ) :
    coLipCertsOn d ϕ (dom ϕ) ⊆ coLipCertsOn d ϕ U :=
  coLipCertsOn_antitone d hd ϕ hU hUd subset_rfl

/-! ### CH02-P07 · co-Lip 条目为零的充分条件 -/

/--
OET anchor: h-88784dcbfff0ea66 （CH02-P07）
**注（co-Lip 条目为零的充分条件）**：若存在 `x y ∈ dom ϕ` 使
`d_j(ϕ x, ϕ y) = 0` 且 `d_i(x, y) > 0`，则任一全域 co-Lip 矩阵 `K ∈ 𝒦(ϕ)|_{dom ϕ}`
必满足 `K_{i→j} = 0`。
-/
theorem coLipCerts_entry_eq_zero [Fintype I] [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (i j : I)
    (h : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y)
    {K : Matrix I I ENNReal} (hK : K ∈ coLipCertsOn d ϕ (dom ϕ)) :
    arrowEntry K i j = 0 := by
  obtain ⟨x, hx, y, hy, h0, hpos⟩ := h
  have h1 := hK.2.2 x hx y hy j
  rw [h0] at h1
  have h2 : arrowEntry K i j * d i x y ≤ ∑ k, arrowEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k => arrowEntry K k j * d k x y) (fun _ _ => zero_le _)
      (Finset.mem_univ i)
  have h3 : arrowEntry K i j * d i x y = 0 := le_antisymm (h2.trans h1) (zero_le _)
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact h4
  · exact absurd h4 hpos.ne'

end formal_oet.vol_01.ch_02_operator_bounds
