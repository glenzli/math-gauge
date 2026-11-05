import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped Classical

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# LCH01 · 通道接口节群 (Channel Interface Section Group)

本模块形式化 OET 第一卷第 2 章关于算子界（Operator Bounds）的核心接口与通道性质，
涵盖 `obligations.json` 中指定的全部 8 项交付义务：
- CH02-D01: 全域/受限 Lip 矩阵谓词与证书族
- CH02-D02: 含非空条件的受限 co-Lip 矩阵及证书族
- CH02-D03: 输入/输出矩阵指标约定与乘法
- CH02-D07: 单输入通道、单行稀疏与对角特例
- CH02-P19: 单一输入项行化简；包含对角特例
- CH02-P20: 正 co-Lip 通道保持正距离
- CH02-P21: 全对角正 co-Lip 反射族零距；不加强为点相等
- CH02-P25: 习题 2.2：标量双侧界
-/

/-! ### 1. 矩阵指标约定与乘法 (CH02-D03) -/

/--
OET anchor: oet-af85899693cc8750 (CH02-D03)
扩展非负矩阵类型别名。
约定：行指标为输出分量 j，列指标为输入分量 i，即 (M)_{ji} = M_{i → j}。
-/
def MatrixBound (I : Type) : Type := Matrix I I ENNReal

/--
OET anchor: oet-af85899693cc8750 (CH02-D03)
矩阵条目访问：`matrix_entry M i j` 给出通道 i → j 对应的矩阵条目 M_{i → j} = (M)_{ji}。
-/
def matrix_entry {I : Type} (M : Matrix I I ENNReal) (i j : I) : ENNReal :=
  M j i

/--
OET anchor: oet-af85899693cc8750 (CH02-D03)
扩展非负矩阵乘法：(M₂ · M₁)_{i → j} = ∑_{k ∈ I} (M₂)_{k → j} (M₁)_{i → k}。
在行列约定下即为标准矩阵乘法 M₂ * M₁。
-/
noncomputable def matrix_mul {I : Type} [Fintype I] (M₂ M₁ : Matrix I I ENNReal) : Matrix I I ENNReal :=
  M₂ * M₁

/--
OET anchor: oet-af85899693cc8750 (CH02-D03)
矩阵乘法条目公式：验证条目定义与代数乘法的一致性。
-/
theorem matrix_mul_entry {I : Type} [Fintype I] (M₂ M₁ : Matrix I I ENNReal) (i j : I) :
    matrix_entry (matrix_mul M₂ M₁) i j = ∑ k : I, matrix_entry M₂ k j * matrix_entry M₁ i k := by
  dsimp [matrix_entry, matrix_mul]
  exact Matrix.mul_apply

/--
OET anchor: oet-af85899693cc8750 (CH02-D03)
矩阵乘法在标准矩阵索引下的展开式。
-/
theorem matrix_mul_apply {I : Type} [Fintype I] (M₂ M₁ : Matrix I I ENNReal) (j i : I) :
    (matrix_mul M₂ M₁) j i = ∑ k : I, M₂ j k * M₁ k i := by
  dsimp [matrix_mul]
  exact Matrix.mul_apply

/-! ### 2. 全域/受限 Lip 矩阵谓词与证书族 (CH02-D01) -/

/--
OET anchor: oet-af85899693cc8750 (CH02-D01)
子集受限 Lip 放缩不等式：
对所有 x, y ∈ U 及所有输出分量 j ∈ I，
d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i → j} d_i(x, y)。
-/
def LipBoundOn {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : Matrix I I ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L j i * d i x y

/--
OET anchor: oet-af85899693cc8750 (CH02-D01)
受限 Lip 矩阵谓词：包含子集约束 U ⊆ dom(ϕ) 及受限放缩不等式。
-/
def HasRestrictedLip {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : Matrix I I ENNReal) : Prop :=
  U ⊆ dom ϕ ∧ LipBoundOn d ϕ U L

/--
OET anchor: oet-af85899693cc8750 (CH02-D01)
受限 Lip 证书族 ℒ(ϕ)|_U。
-/
def restrictedLipSet {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (Matrix I I ENNReal) :=
  { L | HasRestrictedLip d ϕ U L }

/--
OET anchor: oet-af85899693cc8750 (CH02-D01)
全域 Lip 矩阵谓词：在全定义域 dom(ϕ) 上的受限 Lip 矩阵。
-/
def HasLip {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : Matrix I I ENNReal) : Prop :=
  HasRestrictedLip d ϕ (dom ϕ) L

/--
OET anchor: oet-af85899693cc8750 (CH02-D01)
全域 Lip 证书族 ℒ(ϕ)。
-/
def lipSet {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (Matrix I I ENNReal) :=
  { L | HasLip d ϕ L }

/-- 全域 Lip 条件的显式逐点充要条件。 -/
theorem hasLip_iff {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : Matrix I I ENNReal) :
    HasLip d ϕ L ↔ ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L j i * d i x y := by
  dsimp [HasLip, HasRestrictedLip, LipBoundOn]
  simp

/-- 全域证书族等于全定义域上的受限证书族。 -/
theorem restrictedLipSet_dom {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedLipSet d ϕ (dom ϕ) = lipSet d ϕ :=
  rfl

/-! ### 3. 含非空条件的受限 co-Lip 矩阵及证书族 (CH02-D02) -/

/--
OET anchor: oet-af85899693cc8750 (CH02-D02)
子集受限 co-Lip 放缩不等式：
对所有 x, y ∈ U 及所有输出分量 j ∈ I，
∑_{i ∈ I} K_{i → j} d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))。
-/
def CoLipBoundOn {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : Matrix I I ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, ∑ i : I, K j i * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/--
OET anchor: oet-af85899693cc8750 (CH02-D02)
含非空条件的受限 co-Lip 矩阵谓词：
明确包含非空条件 U.Nonempty，以及 U ⊆ dom(ϕ) 与下界放缩不等式。
-/
def HasRestrictedCoLip {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : Matrix I I ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ CoLipBoundOn d ϕ U K

/--
OET anchor: oet-af85899693cc8750 (CH02-D02)
受限 co-Lip 证书族 𝒦(ϕ)|_U。
遵循原文约定：“凡出现 𝒦(ϕ)|_U，均包含这里的非空性条件 U ≠ ∅”。
-/
def restrictedCoLipSet {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (Matrix I I ENNReal) :=
  { K | HasRestrictedCoLip d ϕ U K }

/--
OET anchor: oet-af85899693cc8750 (CH02-D02)
全域 co-Lip 矩阵谓词：在全定义域 dom(ϕ) 上评估（包含非空条件）。
-/
def HasCoLip {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (K : Matrix I I ENNReal) : Prop :=
  HasRestrictedCoLip d ϕ (dom ϕ) K

/--
OET anchor: oet-af85899693cc8750 (CH02-D02)
全域 co-Lip 证书族 𝒦(ϕ)|_{dom(ϕ)}。
-/
def coLipSet {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (Matrix I I ENNReal) :=
  { K | HasCoLip d ϕ K }

/-- 受限 co-Lip 证书必有非空评估域。 -/
theorem restrictedCoLipSet_nonempty {X I : Type} [Fintype I] {bot : X}
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : Matrix I I ENNReal}
    (hK : K ∈ restrictedCoLipSet d ϕ U) : U.Nonempty :=
  hK.1

/-- 受限 co-Lip 证书之评估域必包含于定义域。 -/
theorem restrictedCoLipSet_subset_dom {X I : Type} [Fintype I] {bot : X}
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : Matrix I I ENNReal}
    (hK : K ∈ restrictedCoLipSet d ϕ U) : U ⊆ dom ϕ :=
  hK.2.1

/-! ### 4. 单输入通道、单行稀疏与对角特例 (CH02-D07) -/

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-D07)
分量通道：有序对 (i, j) 表示从输入分量 d_i 到输出分量 d_j 的通道。
-/
def ComponentChannel (I : Type) : Type := I × I

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-D07)
单输入通道 / 单行稀疏条件：
输出分量 j 的第 j 行中，除输入分量 i 外的所有条目均为零。
即：对所有 k ≠ i，(M)_{jk} = M_{k → j} = 0。
-/
def SingleRowSparse {I : Type} (M : Matrix I I ENNReal) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → M j k = 0

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-D07)
对角矩阵特例：所有非对角条目均为零。
即：对所有输出分量 j 与输入分量 k（k ≠ j），(M)_{jk} = 0。
-/
def IsDiagonal {I : Type} (M : Matrix I I ENNReal) : Prop :=
  ∀ j k : I, k ≠ j → M j k = 0

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-D07)
对角矩阵对每个分量 j 均在同分量通道 (j, j) 处满足单行稀疏条件。
-/
theorem isDiagonal_singleRowSparse {I : Type} (M : Matrix I I ENNReal) (h : IsDiagonal M) (j : I) :
    SingleRowSparse M j j :=
  h j

/-! ### 5. 单一输入项行化简；包含对角特例 (CH02-P19) -/

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-P19)
单行稀疏性下的求和项折叠：
若第 j 行除输入分量 i 外均为零，则对任意点对 x, y，求和项化简为单一输入分量项：
∑_{k ∈ I} L_{k → j} d_k(x, y) = L_{i → j} d_i(x, y)。
-/
theorem sum_eq_single_of_singleRowSparse {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (x y : X) (L : Matrix I I ENNReal) {i j : I}
    (h_sparse : SingleRowSparse L i j) :
    ∑ k : I, L j k * d k x y = L j i * d i x y := by
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [h_sparse k hk, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-P19)
单一输入项行化简（基于 LipBoundOn）：
若 L 为受限 Lip 矩阵且满足单行稀疏条件 SingleRowSparse L i j，
则对任意 x, y ∈ U，d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} d_i(x, y)。
-/
theorem lip_bound_of_singleRowSparse {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {L : Matrix I I ENNReal}
    (hL : LipBoundOn d ϕ U L) {i j : I} (h_sparse : SingleRowSparse L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j i * d i x y := by
  have h_le := hL x hx y hy j
  have h_sum := sum_eq_single_of_singleRowSparse d x y L h_sparse
  rwa [h_sum] at h_le

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-P19)
单一输入项行化简（基于证书族 ℒ(ϕ)|_U）：
L ∈ restrictedLipSet d ϕ U 时的同形特化。
-/
theorem restricted_lip_bound_of_singleRowSparse {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {L : Matrix I I ENNReal}
    (hL : L ∈ restrictedLipSet d ϕ U) {i j : I} (h_sparse : SingleRowSparse L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j i * d i x y :=
  lip_bound_of_singleRowSparse d ϕ hL.2 h_sparse hx hy

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-P19)
对角特例行化简：
若 L 为对角矩阵，则对任意输出分量 j 与 x, y ∈ U，
d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} d_j(x, y)。
-/
theorem lip_bound_of_isDiagonal {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {L : Matrix I I ENNReal}
    (hL : LipBoundOn d ϕ U L) (h_diag : IsDiagonal L) (j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  lip_bound_of_singleRowSparse d ϕ hL (isDiagonal_singleRowSparse L h_diag j) hx hy

/--
OET anchor: oet-7fa97eb6e24d5527 (CH02-P19)
对角特例行化简（基于证书族 ℒ(ϕ)|_U）。
-/
theorem restricted_lip_bound_of_isDiagonal {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {L : Matrix I I ENNReal}
    (hL : L ∈ restrictedLipSet d ϕ U) (h_diag : IsDiagonal L) (j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  restricted_lip_bound_of_singleRowSparse d ϕ hL (isDiagonal_singleRowSparse L h_diag j) hx hy

/-! ### 6. 正 co-Lip 通道保持正距离 (CH02-P20) -/

/-- 非负有限和的单项下界辅助引理。 -/
theorem single_term_le_sum {I : Type} [Fintype I] (f : I → ENNReal) (i : I) :
    f i ≤ ∑ k : I, f k :=
  Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)

/--
OET anchor: oet-f82672ec0dd48f28 (CH02-P20)
命题 2.8(i)（正 co-Lip 通道保持可分辨性）：
设 K ∈ 𝒦(ϕ)|_U。若 K_{i → j} > 0，则对任意 x, y ∈ U，
d_i(x, y) > 0 ⟹ d_j(ϕ(x), ϕ(y)) > 0。
-/
theorem pos_coLip_channel_preserves_pos_dist {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {K : Matrix I I ENNReal}
    (hK : K ∈ restrictedCoLipSet d ϕ U) {i j : I} (hK_pos : 0 < K j i)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hdist : 0 < d i x y) :
    0 < d j (ϕ.func x) (ϕ.func y) := by
  have h_bound : ∑ k : I, K j k * d k x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    hK.2.2 x hx y hy j
  have h_term : K j i * d i x y ≤ ∑ k : I, K j k * d k x y :=
    single_term_le_sum (fun k => K j k * d k x y) i
  have h_pos : 0 < K j i * d i x y :=
    ENNReal.mul_pos hK_pos.ne' hdist.ne'
  exact lt_of_lt_of_le (lt_of_lt_of_le h_pos h_term) h_bound

/--
OET anchor: oet-f82672ec0dd48f28 (CH02-P20)
正 co-Lip 通道保持可分辨性（基于 CoLipBoundOn 的直接表述）。
-/
theorem colip_bound_channel_preserves_pos_dist {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {K : Matrix I I ENNReal}
    (hK : CoLipBoundOn d ϕ U K) {i j : I} (hK_pos : 0 < K j i)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hdist : 0 < d i x y) :
    0 < d j (ϕ.func x) (ϕ.func y) := by
  have h_bound : ∑ k : I, K j k * d k x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    hK x hx y hy j
  have h_term : K j i * d i x y ≤ ∑ k : I, K j k * d k x y :=
    single_term_le_sum (fun k => K j k * d k x y) i
  have h_pos : 0 < K j i * d i x y :=
    ENNReal.mul_pos hK_pos.ne' hdist.ne'
  exact lt_of_lt_of_le (lt_of_lt_of_le h_pos h_term) h_bound

/-! ### 7. 全对角正 co-Lip 反射族零距 (CH02-P21) -/

/--
OET anchor: oet-f82672ec0dd48f28 (CH02-P21)
命题 2.8(ii)（全对角正 co-Lip 反射族零距关系）：
设 K ∈ 𝒦(ϕ)|_U。若对所有 j ∈ I 均有 K_{j → j} > 0，则 ϕ 反射族零距关系：
对任意 x, y ∈ U，ϕ(x) ~_𝒢 ϕ(y) ⟹ x ~_𝒢 y。
注：严格遵循原文与义务要求，“不加强为点相等 x = y”。
-/
theorem all_diagonal_pos_coLip_reflects_gaugeZeroRelated {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {K : Matrix I I ENNReal}
    (hK : K ∈ restrictedCoLipSet d ϕ U) (hK_diag : ∀ j : I, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_zero : GaugeZeroRelated d (ϕ.func x) (ϕ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra h_ne
  have h_pos : 0 < d j x y := pos_iff_ne_zero.mpr h_ne
  have h_out_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_coLip_channel_preserves_pos_dist d ϕ hK (hK_diag j) hx hy h_pos
  have h_out_zero : d j (ϕ.func x) (ϕ.func y) = 0 := h_zero j
  rw [h_out_zero] at h_out_pos
  exact lt_irrefl 0 h_out_pos

/-! ### 8. 习题 2.2：标量双侧界 (CH02-P25) -/

/--
OET anchor: oet-6a98a58b5bc95360 (CH02-P25)
习题 2.2 下界部分：
若 K ∈ 𝒦(ϕ)|_U，则对任意 x, y ∈ U 与输出分量 j，
K_{j → j} · d_j(x, y) ≤ d_j(ϕ(x), ϕ(y))。
-/
theorem exercise_2_2_lower_bound {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (j : I) (K : Matrix I I ENNReal) (hK : K ∈ restrictedCoLipSet d ϕ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  have h_colip := hK.2.2 x hx y hy j
  have h_single := single_term_le_sum (fun k => K j k * d k x y) j
  exact le_trans h_single h_colip

/--
OET anchor: oet-6a98a58b5bc95360 (CH02-P25)
习题 2.2 上界部分：
若 L ∈ ℒ(ϕ)|_U 且输出分量 j 满足单行对角稀疏条件 L_{k → j} = 0 (∀ k ≠ j)，
则对任意 x, y ∈ U，
d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} · d_j(x, y)。
-/
theorem exercise_2_2_upper_bound {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (j : I) (L : Matrix I I ENNReal) (hL : L ∈ restrictedLipSet d ϕ U)
    (hL_diag : SingleRowSparse L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  restricted_lip_bound_of_singleRowSparse d ϕ hL hL_diag hx hy

/--
OET anchor: oet-6a98a58b5bc95360 (CH02-P25)
习题 2.2 完整标量双侧界：
设 ϕ ∈ 𝒳_op，U ⊆ dom(ϕ)，j ∈ I。给定 L ∈ ℒ(ϕ)|_U 与 K ∈ 𝒦(ϕ)|_U。
若 ϕ 在 U 上关于输出分量 d_j 满足只保留对角输入项的 Lip 上界：
  L_{k → j} = 0 (∀ k ≠ j)，
则对任意 x, y ∈ U 有标量双侧不等式：
  K_{j → j} · d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} · d_j(x, y)。
-/
theorem exercise_2_2_scalar_two_sided_bound {X I : Type} [Fintype I] {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (j : I) (L K : Matrix I I ENNReal)
    (hL : L ∈ restrictedLipSet d ϕ U) (hK : K ∈ restrictedCoLipSet d ϕ U)
    (hL_diag : SingleRowSparse L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  ⟨exercise_2_2_lower_bound d ϕ j K hK hx hy,
   exercise_2_2_upper_bound d ϕ j L hL hL_diag hx hy⟩

end formal_oet.vol_01.ch_02_operator_bounds
