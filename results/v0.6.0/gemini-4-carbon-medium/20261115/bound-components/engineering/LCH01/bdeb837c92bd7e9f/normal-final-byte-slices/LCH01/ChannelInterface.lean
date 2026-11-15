import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

open scoped BigOperators Matrix
open formal_oet.vol_01.ch_01_foundations

/-!
# CH02-D03: 输入/输出矩阵指标约定与乘法

书写矩阵 `M` 时，以输出分量 `j` 为行指标、输入分量 `i` 为列指标，
因此通道条目 `M_{i → j}` 位于第 `j` 行、第 `i` 列，即 `(M)_{j,i} = M_{i → j}`。
-/

/-- 以 `I` 为指标集的扩展非负规范界矩阵（行指标为输出分量，列指标为输入分量）。 -/
abbrev GaugeMatrix (I : Type) : Type := Matrix I I ENNReal

/-- 矩阵的通道条目读取函数：`chanEntry M i j` 表示 `M_{i → j} = (M)_{j,i}`。 -/
def chanEntry {I : Type} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

/-- 由通道系数映射 `(i, j) ↦ f i j`（输入 `i` 到输出 `j`）构造规范界矩阵。 -/
def ofChanEntry {I : Type} (f : I → I → ENNReal) : GaugeMatrix I :=
  Matrix.of fun j i => f i j

/-- 行列指标约定恒等式：`(M)_{j,i} = M_{i → j}`。 -/
@[simp] theorem chanEntry_eq_row_col {I : Type} (M : GaugeMatrix I) (i j : I) :
    chanEntry M i j = M j i :=
  rfl

/-- 由通道映射构造的矩阵在通道 `(i, j)` 处还原为 `f i j`。 -/
@[simp] theorem chanEntry_ofChanEntry {I : Type} (f : I → I → ENNReal) (i j : I) :
    chanEntry (ofChanEntry f) i j = f i j :=
  rfl

/-- 由通道映射构造的矩阵在第 `j` 行、第 `i` 列处等于 `f i j`。 -/
@[simp] theorem ofChanEntry_apply {I : Type} (f : I → I → ENNReal) (j i : I) :
    ofChanEntry f j i = f i j :=
  rfl

/-- 扩展非负规范界矩阵的乘法（沿用输出行、输入列的标准矩阵乘法）。 -/
noncomputable def gaugeMatrixMul {I : Type} [Fintype I] (M₂ M₁ : GaugeMatrix I) : GaugeMatrix I :=
  M₂ * M₁

/-- 标准矩阵乘法在通道指标约定下的展开式：
`(M₂ · M₁)_{i → j} = ∑ k, M₂_{k → j} * M₁_{i → k}`。 -/
@[simp] theorem chanEntry_mul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    chanEntry (M₂ * M₁) i j = ∑ k : I, chanEntry M₂ k j * chanEntry M₁ i k :=
  Matrix.mul_apply

/-- `gaugeMatrixMul` 的通道条目展开式。 -/
@[simp] theorem chanEntry_gaugeMatrixMul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    chanEntry (gaugeMatrixMul M₂ M₁) i j = ∑ k : I, chanEntry M₂ k j * chanEntry M₁ i k :=
  Matrix.mul_apply

/-- 规范界矩阵乘法满足结合律。 -/
theorem gaugeMatrixMul_assoc {I : Type} [Fintype I]
    (M₃ M₂ M₁ : GaugeMatrix I) :
    gaugeMatrixMul (gaugeMatrixMul M₃ M₂) M₁ = gaugeMatrixMul M₃ (gaugeMatrixMul M₂ M₁) :=
  Matrix.mul_assoc M₃ M₂ M₁

/-- 矩阵对输入分量向量的作用在第 `j` 个输出分量处展开为 `∑ i, M_{i → j} * v_i`。 -/
theorem mulVec_eq_sum_chanEntry {I : Type} [Fintype I]
    (M : GaugeMatrix I) (v : I → ENNReal) (j : I) :
    (M *ᵥ v) j = ∑ i : I, chanEntry M i j * v i :=
  rfl

/-!
# CH02-D01: 全域/受限Lip矩阵谓词与证书族
-/

/-- 算子 `ϕ` 在全域定义域 `dom ϕ` 上的合法 Lipschitz 矩阵谓词。 -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, chanEntry L i j * d i x y

/-- 算子 `ϕ` 的全体合法全域 Lipschitz 矩阵证书族 `ℒ(ϕ)`。 -/
def lipCerts {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/-- 算子 `ϕ` 在子集 `U ⊆ dom ϕ` 上的合法受限 Lipschitz 矩阵谓词。 -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, chanEntry L i j * d i x y

/-- 算子 `ϕ` 在子集 `U` 上的受限 Lipschitz 矩阵证书族 `ℒ(ϕ)|_U`。 -/
def restrictedLipCerts {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

@[simp] theorem mem_lipCerts_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    L ∈ lipCerts d ϕ ↔ IsLipMatrix d ϕ L :=
  Iff.rfl

@[simp] theorem mem_restrictedLipCerts_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) :
    L ∈ restrictedLipCerts d ϕ U ↔ IsRestrictedLipMatrix d ϕ U L :=
  Iff.rfl

/-- 在 `U = dom ϕ` 上受限 Lip 矩阵谓词与全域 Lip 矩阵谓词等价。 -/
theorem isRestrictedLipMatrix_dom_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsRestrictedLipMatrix d ϕ (dom ϕ) L ↔ IsLipMatrix d ϕ L := by
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Set.Subset.rfl, h⟩

/-- 在 `U = dom ϕ` 上受限 Lip 证书族等于全域 Lip 证书族 `ℒ(ϕ)|_{dom(ϕ)} = ℒ(ϕ)`。 -/
@[simp] theorem restrictedLipCerts_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedLipCerts d ϕ (dom ϕ) = lipCerts d ϕ := by
  ext L
  exact isRestrictedLipMatrix_dom_iff d ϕ L

/-!
# CH02-D02: 含非空条件的受限co-Lip矩阵及证书族
-/

/-- 算子 `ϕ` 在非空子集 `U ⊆ dom ϕ` 上的合法受限 co-Lipschitz 矩阵谓词（显式含 `U.Nonempty`）。 -/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, chanEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- 算子 `ϕ` 在子集 `U` 上的受限 co-Lipschitz 矩阵证书族 `𝒦(ϕ)|_U`（含非空条件 `U ≠ ∅`）。 -/
def restrictedCoLipCerts {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

@[simp] theorem mem_restrictedCoLipCerts_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) :
    K ∈ restrictedCoLipCerts d ϕ U ↔ IsRestrictedCoLipMatrix d ϕ U K :=
  Iff.rfl

/-- 空集不满足 `𝒦(ϕ)|_U` 的非空性前提，因此空集上的受限 co-Lip 证书族为空。 -/
@[simp] theorem restrictedCoLipCerts_empty {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    restrictedCoLipCerts d ϕ ∅ = ∅ := by
  ext K
  simp [restrictedCoLipCerts, IsRestrictedCoLipMatrix]

/-- 辅助引理：受限 co-Lip 证书给出任一单个输入通道 `(i, j)` 的标量下界。 -/
theorem restricted_coLip_entry_mul_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipCerts d ϕ U) (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U, chanEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  have hsum := hK.2.2 x hx y hy j
  have hsingle : chanEntry K i j * d i x y ≤ ∑ k : I, chanEntry K k j * d k x y :=
    Finset.single_le_sum (f := fun k : I => chanEntry K k j * d k x y)
      (fun k _ => zero_le _) (Finset.mem_univ i)
  exact le_trans hsingle hsum

/-!
# CH02-D07: 单输入通道、单行稀疏与对角特例
-/

/-- 从输入分量 `i` 到输出分量 `j` 的分量通道有序对 `(i, j)`。 -/
abbrev ComponentChannel (I : Type) : Type := I × I

/-- 同分量（对角）通道 `(i, i)`。 -/
def diagChannel {I : Type} (i : I) : ComponentChannel I := (i, i)

/-- 读取矩阵 `M` 在分量通道 `c = (i, j)` 上的系数 `M_{i → j}`。 -/
def channelCoeff {I : Type} (M : GaugeMatrix I) (c : ComponentChannel I) : ENNReal :=
  chanEntry M c.1 c.2

/-- 单行稀疏谓词：第 `j` 行（输出分量 `j`）除单一输入通道 `(i, j)` 条目 `M_{i → j}` 外其余条目均为零。 -/
def IsSingleInputRow {I : Type} (M : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → chanEntry M k j = 0

/-- 对角单行稀疏特例：第 `j` 行仅保留同分量对角输入项 `M_{j → j}`，即对一切 `k ≠ j` 有 `M_{k → j} = 0`。 -/
def IsDiagInputRow {I : Type} (M : GaugeMatrix I) (j : I) : Prop :=
  IsSingleInputRow M j j

/-- 对角规范界矩阵谓词：所有非对角通道条目 `M_{i → j}` (`i ≠ j`) 均为零。 -/
def IsDiagonalGaugeMatrix {I : Type} (M : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → chanEntry M i j = 0

/-- 矩阵为对角矩阵当且仅当每一行 `i` 都是只保留同分量通道 `(i, i)` 的单输入稀疏行。 -/
theorem isDiagonalGaugeMatrix_iff_forall_diagInputRow {I : Type} (M : GaugeMatrix I) :
    IsDiagonalGaugeMatrix M ↔ ∀ i : I, IsDiagInputRow M i := by
  constructor
  · intro hDiag i k hki
    exact hDiag k i hki
  · intro hRows i j hij
    exact hRows j i hij

/-- 由对角通道系数 `diag : I → ENNReal` 构造对角规范界矩阵。 -/
def diagonalGaugeMatrix {I : Type} [DecidableEq I] (diag : I → ENNReal) : GaugeMatrix I :=
  Matrix.diagonal diag

/-- `diagonalGaugeMatrix diag` 满足对角规范界矩阵谓词 `IsDiagonalGaugeMatrix`。 -/
theorem isDiagonalGaugeMatrix_diagonal {I : Type} [DecidableEq I] (diag : I → ENNReal) :
    IsDiagonalGaugeMatrix (diagonalGaugeMatrix diag) := by
  intro i j hij
  exact Matrix.diagonal_apply_ne' diag hij

/-- `diagonalGaugeMatrix diag` 在同分量通道 `(i, i)` 处的条目等于 `diag i`。 -/
@[simp] theorem chanEntry_diagonalGaugeMatrix_self {I : Type} [DecidableEq I]
    (diag : I → ENNReal) (i : I) :
    chanEntry (diagonalGaugeMatrix diag) i i = diag i :=
  Matrix.diagonal_apply_eq diag i

/-!
# CH02-P19: 单一输入项行化简；包含对角特例
-/

/-- 单行稀疏下的行求和化简：若第 `j` 行除 `L_{i → j}` 外均为零，则行加权和化为单项 `L_{i → j} * d_i(x, y)`。 -/
theorem single_input_row_sum_eq {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) (i j : I)
    (hRow : IsSingleInputRow L i j) (x y : X) :
    (∑ k : I, chanEntry L k j * d k x y) = chanEntry L i j * d i x y := by
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hki
    rw [hRow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- 单一输入项行化简（含中间和等式链）：
若 `L ∈ ℒ(ϕ)|_U` 且第 `j` 行除 `L_{i → j}` 外均为零，则对任意 `x, y ∈ U`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑ k, L_{k → j} d_k(x, y) = L_{i → j} d_i(x, y)`。 -/
theorem restricted_lip_single_input_row_reduction
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipCerts d ϕ U) (i j : I)
    (hRow : IsSingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, chanEntry L k j * d k x y ∧
      (∑ k : I, chanEntry L k j * d k x y) = chanEntry L i j * d i x y ∧
      d j (ϕ.func x) (ϕ.func y) ≤ chanEntry L i j * d i x y := by
  intro x hx y hy
  have hsum_le := hL.2 x hx y hy j
  have hsum_eq := single_input_row_sum_eq d L i j hRow x y
  exact ⟨hsum_le, hsum_eq, hsum_eq ▸ hsum_le⟩

/-- 单一输入项行化简后的受限 Lip 标量上界：
若 `L ∈ ℒ(ϕ)|_U` 且第 `j` 行除 `L_{i → j}` 外均为零，则对任意 `x, y ∈ U` 有
`d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} d_i(x, y)`。 -/
theorem restricted_lip_single_input_row_bound
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipCerts d ϕ U) (i j : I)
    (hRow : IsSingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ chanEntry L i j * d i x y := by
  intro x hx y hy
  exact (restricted_lip_single_input_row_reduction d ϕ U L hL i j hRow x hx y hy).2.2

/-- 对角矩阵特例（含中间和等式链）：
若 `L ∈ ℒ(ϕ)|_U` 为对角矩阵，则对每个同分量通道 `(i, i)` 及任意 `x, y ∈ U`，
`d_i(ϕ(x), ϕ(y)) ≤ ∑ k, L_{k → i} d_k(x, y) = L_{i → i} d_i(x, y)`。 -/
theorem restricted_lip_diagonal_reduction
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipCerts d ϕ U)
    (hDiag : IsDiagonalGaugeMatrix L) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, chanEntry L k i * d k x y ∧
      (∑ k : I, chanEntry L k i * d k x y) = chanEntry L i i * d i x y ∧
      d i (ϕ.func x) (ϕ.func y) ≤ chanEntry L i i * d i x y := by
  intro i
  have hRow : IsDiagInputRow L i :=
    (isDiagonalGaugeMatrix_iff_forall_diagInputRow L).mp hDiag i
  exact restricted_lip_single_input_row_reduction d ϕ U L hL i i hRow

/-- 对角矩阵特例的同分量通道标量上界：
若 `L ∈ ℒ(ϕ)|_U` 为对角矩阵，则对每个 `i ∈ I` 与任意 `x, y ∈ U` 有
`d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} d_i(x, y)`。 -/
theorem restricted_lip_diagonal_bound
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipCerts d ϕ U)
    (hDiag : IsDiagonalGaugeMatrix L) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ chanEntry L i i * d i x y := by
  intro i x hx y hy
  exact (restricted_lip_diagonal_reduction d ϕ U L hL hDiag i x hx y hy).2.2

/-- 全域 Lip 证书下的单输入行标量上界推论。 -/
theorem lip_single_input_row_bound
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hL : L ∈ lipCerts d ϕ) (i j : I)
    (hRow : IsSingleInputRow L i j) :
    ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
      d j (ϕ.func x) (ϕ.func y) ≤ chanEntry L i j * d i x y := by
  have hL' : L ∈ restrictedLipCerts d ϕ (dom ϕ) := by
    rwa [restrictedLipCerts_dom]
  exact restricted_lip_single_input_row_bound d ϕ (dom ϕ) L hL' i j hRow

/-- 全域对角 Lip 证书下的同分量通道标量上界推论。 -/
theorem lip_diagonal_bound
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hL : L ∈ lipCerts d ϕ)
    (hDiag : IsDiagonalGaugeMatrix L) :
    ∀ i : I, ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
      d i (ϕ.func x) (ϕ.func y) ≤ chanEntry L i i * d i x y := by
  have hL' : L ∈ restrictedLipCerts d ϕ (dom ϕ) := by
    rwa [restrictedLipCerts_dom]
  exact restricted_lip_diagonal_bound d ϕ (dom ϕ) L hL' hDiag

/-!
# CH02-P20: 命题 2.8(i) 正co-Lip通道保持正距离
-/

/-- **命题 2.8(i)（正 co-Lip 通道保持可分辨性 / 正距离）**
设 `K ∈ 𝒦(ϕ)|_U`。若 `K_{i → j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x, y) > 0 ⟹ d_j(ϕ(x), ϕ(y)) > 0`。 -/
theorem pos_coLip_channel_preserves_pos_dist
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipCerts d ϕ U)
    (i j : I) (hKij : 0 < chanEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hd_pos
  have hle := restricted_coLip_entry_mul_le d ϕ U K hK i j x hx y hy
  have hmul_pos : 0 < chanEntry K i j * d i x y :=
    ENNReal.mul_pos hKij.ne' hd_pos.ne'
  exact lt_of_lt_of_le hmul_pos hle

/-!
# CH02-P21: 命题 2.8(ii) 全对角正co-Lip反射族零距；不加强为点相等
-/

/-- **命题 2.8(ii)（全对角正 co-Lip 反射族零距关系）**
设 `K ∈ 𝒦(ϕ)|_U`。若对所有 `j ∈ I` 均有 `K_{j → j} > 0`，则 `ϕ` 在 `U` 上反射族零距关系：
对任意 `x, y ∈ U`，`ϕ(x) ∼_𝒢 ϕ(y) ⟹ x ∼_𝒢 y`（保留非分离规范空间一般性，不加强为 `x = y`）。 -/
theorem pos_diag_coLip_reflects_gauge_zero
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipCerts d ϕ U)
    (hDiagPos : ∀ j : I, 0 < chanEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hZero j
  by_contra hne
  have hd_pos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have h_out_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    pos_coLip_channel_preserves_pos_dist d ϕ U K hK j j (hDiagPos j) x hx y hy hd_pos
  exact h_out_pos.ne' (hZero j)

/-!
# CH02-P25: 习题 2.2 对角输入项的标量双侧界
-/

/-- **习题 2.2（对角输入项的标量双侧界）**
设 `ϕ ∈ 𝒳_op`，`U ⊆ dom(ϕ)`，`j ∈ I`，给定 `L ∈ ℒ(ϕ)|_U` 与 `K ∈ 𝒦(ϕ)|_U`。
若第 `j` 行满足只保留对角输入项的 Lip 条件 `∀ k ≠ j, L_{k → j} = 0`，
则对任意 `x, y ∈ U` 有标量双侧不等式：
`K_{j → j} · d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} · d_j(x, y)`。 -/
theorem exercise_2_2_scalar_two_sided_bound
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I)
    (L K : GaugeMatrix I)
    (hL : L ∈ restrictedLipCerts d ϕ U)
    (hK : K ∈ restrictedCoLipCerts d ϕ U)
    (hDiagRow : IsDiagInputRow L j) :
    ∀ x ∈ U, ∀ y ∈ U,
      chanEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ chanEntry L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · exact restricted_coLip_entry_mul_le d ϕ U K hK j j x hx y hy
  · exact restricted_lip_single_input_row_bound d ϕ U L hL j j hDiagRow x hx y hy
