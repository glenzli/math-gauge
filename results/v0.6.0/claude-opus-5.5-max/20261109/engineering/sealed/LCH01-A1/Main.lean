import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.IsDiag
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# LCH01 · 通道接口节群（第 2 章选段）

Source: Zhe Li (Glen Li / glenzli), *The Operator Evolution Theory*, Volume I, Chapter 2,
licensed under CC BY 4.0. This file is a new formalization of the selected items.

本文件只依赖冻结前置模块 `formal_oet.vol_01.ch_01_foundations.*` 与 mathlib，
在所给 Lake 工程中可直接以 `lake env lean Main.lean` 检查。

* §1 `arrow` / `ofArrow`：输入/输出矩阵指标约定与乘法（CH02-D03）；
* §2 全域/受限 Lip 矩阵谓词与证书族 `lipCerts`、`restrictedLipCerts`（CH02-D01）；
* §3 含非空条件的受限 co-Lip 矩阵谓词与证书族 `restrictedCoLipCerts`（CH02-D02）；
* §4 分量通道、单行稀疏（单一输入项）与对角特例（CH02-D07）及行化简（CH02-P19）；
* §5 命题 2.8：正 co-Lip 通道保持正距离（CH02-P20）、全对角正 co-Lip 反射族零距（CH02-P21）；
* §6 习题 2.2：标量双侧界（CH02-P25）。

每条主要结论都给出两种形式：一般形式只假设实际用到的前提；`*_textbook` 形式
保留正文的完整语境（`I` 有限非空、每个分量为扩展伪度量、正文列出的 `U ⊆ dom ϕ`）。
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations

/-! ## §1 输入/输出矩阵指标约定与乘法（CH02-D03） -/

section MatrixConvention

variable {I : Type}

/-- **约定（行列指标）**：`arrow L i j` 表示 `L_{i→j}`，即从输入分量 `d_i` 到输出分量
`d_j` 的系数。矩阵以输出分量为行指标、输入分量为列指标，故 `L_{i→j}` 位于第 `j` 行、
第 `i` 列：`(L)_{ji} = L_{i→j}`。条目取值于 `ENNReal = [0, +∞]`，因而矩阵自动非负。 -/
def arrow (L : Matrix I I ENNReal) (i j : I) : ENNReal := L j i

@[simp] theorem arrow_apply (L : Matrix I I ENNReal) (i j : I) : arrow L i j = L j i := rfl

/-- 矩阵条目非负：`0 ≤ L_{i→j}`（条目取值于 `[0, +∞]`）。 -/
theorem arrow_nonneg (L : Matrix I I ENNReal) (i j : I) : 0 ≤ arrow L i j := zero_le _

/-- 由按 `i → j` 标记的系数族 `f i j = L_{i→j}` 写出矩阵：第 `j` 行、第 `i` 列放 `f i j`。 -/
def ofArrow (f : I → I → ENNReal) : Matrix I I ENNReal := Matrix.of fun j i => f i j

@[simp] theorem arrow_ofArrow (f : I → I → ENNReal) (i j : I) :
    arrow (ofArrow f) i j = f i j := rfl

@[simp] theorem ofArrow_arrow (L : Matrix I I ENNReal) : ofArrow (arrow L) = L := rfl

/-- 矩阵与按 `i → j` 标记的系数族一一对应。 -/
def arrowEquiv : Matrix I I ENNReal ≃ (I → I → ENNReal) where
  toFun := arrow
  invFun := ofArrow
  left_inv _ := rfl
  right_inv _ := rfl

/-- 第 `j` 行汇集指向输出分量 `d_j` 的全部系数 `L_{i→j}`（`i ∈ I`）。 -/
theorem row_eq_arrow (L : Matrix I I ENNReal) (j : I) : L j = fun i => arrow L i j := rfl

/-- 第 `i` 列汇集从输入分量 `d_i` 出发的全部系数 `L_{i→j}`（`j ∈ I`）。 -/
theorem col_eq_arrow (L : Matrix I I ENNReal) (i : I) :
    L.transpose i = fun j => arrow L i j := rfl

/-- 正文 `I = {1,2,3}` 的书写示例（`Fin 3` 中以 `0,1,2` 编号分量 `1,2,3`）：
第一行为 `L_{1→1}, L_{2→1}, L_{3→1}`；例如 `L_{2→1}` 位于第一行、第二列。 -/
theorem ofArrow_fin_three (f : Fin 3 → Fin 3 → ENNReal) :
    ofArrow f = !![f 0 0, f 1 0, f 2 0;
                   f 0 1, f 1 1, f 2 1;
                   f 0 2, f 1 2, f 2 2] := by
  ext j i
  fin_cases j <;> fin_cases i <;> rfl

/-- 正文示例：`L_{2→1}` 位于第一行、第二列（`Fin 3` 中即第 `0` 行、第 `1` 列）。 -/
theorem ofArrow_fin_three_row_one_col_two (f : Fin 3 → Fin 3 → ENNReal) :
    ofArrow f 0 1 = f 1 0 := rfl

variable [Fintype I]

/-- **乘法**：在上述约定下，代数矩阵乘积 `L₂ * L₁` 的条目为
`(L₂ · L₁)_{i→j} = ∑_k L₂_{k→j} · L₁_{i→k}`。 -/
theorem arrow_mul (L₂ L₁ : Matrix I I ENNReal) (i j : I) :
    arrow (L₂ * L₁) i j = ∑ k, arrow L₂ k j * arrow L₁ i k := by
  simp [arrow, Matrix.mul_apply]

/-- Lip/co-Lip 不等式右端 `∑_i L_{i→j} v_i` 就是矩阵—列向量乘积的第 `j` 个分量。 -/
theorem sum_arrow_eq_mulVec (L : Matrix I I ENNReal) (v : I → ENNReal) (j : I) :
    ∑ i, arrow L i j * v i = L.mulVec v j := by
  simp [arrow, Matrix.mulVec, dotProduct]

/-- 乘法与求和次序交换（`ENNReal` 中有限和的分配律与交换律）：
`∑_k L₂_{k→j} (∑_i L₁_{i→k} v_i) = ∑_i (L₂ · L₁)_{i→j} v_i`。 -/
theorem sum_arrow_mul_sum (L₂ L₁ : Matrix I I ENNReal) (v : I → ENNReal) (j : I) :
    ∑ k, arrow L₂ k j * ∑ i, arrow L₁ i k * v i = ∑ i, arrow (L₂ * L₁) i j * v i := by
  simp only [sum_arrow_eq_mulVec]
  rw [← Matrix.mulVec_mulVec]

omit [Fintype I] in
/-- 单位矩阵：`𝐈_{i→j} = 1`（`i = j`）且 `= 0`（`i ≠ j`）。 -/
theorem arrow_one [DecidableEq I] (i j : I) :
    arrow (1 : Matrix I I ENNReal) i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [arrow]
  · simp [arrow, h, Ne.symm h]

end MatrixConvention

/-! ## §2 全域/受限 Lip 矩阵谓词与证书族（CH02-D01） -/

section LipCertificates

variable {X I : Type} {bot : X} [Fintype I]

/-- **定义（Lipschitz 矩阵）**：`L` 是算子 `ϕ` 的合法 Lip 矩阵，当且仅当对所有
`x, y ∈ dom(ϕ)` 与所有输出分量 `j ∈ I`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i→j} · d_i(x, y)`。 -/
def IsLipMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : Matrix I I ENNReal) :
    Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, arrow L i j * d i x y

/-- `𝓛(ϕ)`：`ϕ` 的全体合法 Lip 矩阵组成的证书族（只是一个集合，不指定任何极值矩阵）。 -/
def lipCerts (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (Matrix I I ENNReal) :=
  {L | IsLipMatrix d ϕ L}

/-- **定义（子集受限 Lip 矩阵）**：对子集 `U ⊆ dom(ϕ)`，`L` 是 `ϕ` 在 `U` 上的受限 Lip
矩阵，当且仅当对所有 `x, y ∈ U` 与所有 `j ∈ I` 满足同一距离放缩不等式。
正文只对 `U ⊆ dom(ϕ)` 定义此概念，故把 `U ⊆ dom ϕ` 作为谓词的第一个合取项。 -/
def IsRestrictedLipMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : Matrix I I ENNReal) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, arrow L i j * d i x y

/-- `𝓛(ϕ)|_U`：`ϕ` 在 `U` 上的全体合法受限 Lip 矩阵组成的证书族。 -/
def restrictedLipCerts (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {L | IsRestrictedLipMatrix d ϕ U L}

variable {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {L : Matrix I I ENNReal}

theorem mem_lipCerts_iff :
    L ∈ lipCerts d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
        d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, arrow L i j * d i x y :=
  Iff.rfl

theorem mem_restrictedLipCerts_iff :
    L ∈ restrictedLipCerts d ϕ U ↔
      U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
        d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, arrow L i j * d i x y :=
  Iff.rfl

/-- 受限 Lip 证书的域条件。 -/
theorem subset_dom_of_mem_restrictedLipCerts (hL : L ∈ restrictedLipCerts d ϕ U) :
    U ⊆ dom ϕ :=
  hL.1

/-- 受限 Lip 证书的不等式（取 `x, y ∈ U` 与输出分量 `j`）。 -/
theorem lip_le_of_mem_restrictedLipCerts (hL : L ∈ restrictedLipCerts d ϕ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, arrow L i j * d i x y :=
  hL.2 x hx y hy j

/-- 全域证书族就是限制在 `U = dom(ϕ)` 上的受限证书族：`𝓛(ϕ) = 𝓛(ϕ)|_{dom(ϕ)}`。 -/
theorem lipCerts_eq_restrictedLipCerts_dom :
    lipCerts d ϕ = restrictedLipCerts d ϕ (dom ϕ) := by
  ext L
  exact ⟨fun h => ⟨subset_rfl, h⟩, fun h => h.2⟩

/-- 受限 Lip 矩阵不要求 `U` 非空：空集上任意矩阵都是合法受限 Lip 矩阵
（与 co-Lip 的非空性条件对照，见 `restrictedCoLipCerts_empty`）。 -/
theorem restrictedLipCerts_empty : restrictedLipCerts d ϕ (∅ : Set X) = Set.univ := by
  ext L
  simp only [Set.mem_univ, iff_true]
  exact ⟨Set.empty_subset _, fun x hx => absurd hx (Set.notMem_empty x)⟩

/-- 证书族向上封闭：逐条目放大合法 Lip 矩阵仍得合法 Lip 矩阵。 -/
theorem mem_restrictedLipCerts_of_le {L' : Matrix I I ENNReal}
    (hL : L ∈ restrictedLipCerts d ϕ U) (hle : ∀ i j : I, arrow L i j ≤ arrow L' i j) :
    L' ∈ restrictedLipCerts d ϕ U := by
  refine ⟨hL.1, fun x hx y hy j => (hL.2 x hx y hy j).trans ?_⟩
  exact Finset.sum_le_sum fun i _ => mul_le_mul_left (hle i j) _

omit [Fintype I] in
/-- **约定（广义 Lip，`(+∞) · 0 = 0`）**：只要 `d_i(x, y) = 0`，无论 `L_{i→j}` 是否等于
`+∞`，项 `L_{i→j} · d_i(x, y)` 对右端求和的贡献都为零。 -/
theorem arrow_mul_eq_zero_of_dist_eq_zero (L : Matrix I I ENNReal) {i j : I} {x y : X}
    (h : d i x y = 0) : arrow L i j * d i x y = 0 := by
  rw [h, mul_zero]

/-- **约定（广义 Lip）**：若 `L_{i→j} = +∞` 且 `d_i(x, y) > 0`，该项为 `+∞`，
`d_j` 的 Lip 不等式平凡成立。 -/
theorem lip_ineq_of_arrow_eq_top (L : Matrix I I ENNReal) {i j : I} {x y : X} (a b : X)
    (htop : arrow L i j = ⊤) (hpos : 0 < d i x y) :
    d j a b ≤ ∑ k : I, arrow L k j * d k x y := by
  have hterm : arrow L i j * d i x y = ⊤ := by
    rw [htop]
    exact ENNReal.top_mul hpos.ne'
  calc d j a b ≤ ⊤ := le_top
    _ = arrow L i j * d i x y := hterm.symm
    _ ≤ ∑ k : I, arrow L k j * d k x y :=
        Finset.single_le_sum (f := fun k => arrow L k j * d k x y)
          (fun _ _ => zero_le _) (Finset.mem_univ i)

end LipCertificates

/-! ## §3 含非空条件的受限 co-Lip 矩阵及证书族（CH02-D02） -/

section CoLipCertificates

variable {X I : Type} {bot : X} [Fintype I]

/-- **定义（子集受限 co-Lipschitz 矩阵）**：对非空子集 `U ⊆ dom(ϕ)`，`K` 是 `ϕ` 在 `U`
上的合法受限 co-Lip 矩阵，当且仅当对所有 `x, y ∈ U` 与所有 `j ∈ I`，
`d_j(ϕ(x), ϕ(y)) ≥ ∑_{i ∈ I} K_{i→j} · d_i(x, y)`。
正文规定凡出现 `𝓚(ϕ)|_U` 均包含非空性条件 `U ≠ ∅`，且 `U ⊆ dom(ϕ)`；
二者作为谓词的前两个合取项。 -/
def IsRestrictedCoLipMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : Matrix I I ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, ∑ i : I, arrow K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- `𝓚(ϕ)|_U`：`ϕ` 在 `U` 上的全体合法受限 co-Lip 矩阵组成的下界证书族。 -/
def restrictedCoLipCerts (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Set (Matrix I I ENNReal) :=
  {K | IsRestrictedCoLipMatrix d ϕ U K}

variable {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : Matrix I I ENNReal}

theorem mem_restrictedCoLipCerts_iff :
    K ∈ restrictedCoLipCerts d ϕ U ↔
      U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
        ∑ i : I, arrow K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) :=
  Iff.rfl

/-- 非空性条件包含在 `𝓚(ϕ)|_U` 之中。 -/
theorem nonempty_of_mem_restrictedCoLipCerts (hK : K ∈ restrictedCoLipCerts d ϕ U) :
    U.Nonempty :=
  hK.1

/-- 域条件包含在 `𝓚(ϕ)|_U` 之中。 -/
theorem subset_dom_of_mem_restrictedCoLipCerts (hK : K ∈ restrictedCoLipCerts d ϕ U) :
    U ⊆ dom ϕ :=
  hK.2.1

/-- 受限 co-Lip 证书的不等式（取 `x, y ∈ U` 与输出分量 `j`）。 -/
theorem coLip_le_of_mem_restrictedCoLipCerts (hK : K ∈ restrictedCoLipCerts d ϕ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    ∑ i : I, arrow K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) :=
  hK.2.2 x hx y hy j

/-- 空集上没有合法受限 co-Lip 矩阵（非空性条件的直接推论）。 -/
theorem restrictedCoLipCerts_empty : restrictedCoLipCerts d ϕ ∅ = ∅ := by
  ext K
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hK
  exact Set.not_nonempty_empty hK.1

/-- 下界证书族向下封闭：逐条目缩小合法 co-Lip 矩阵仍得合法 co-Lip 矩阵。 -/
theorem mem_restrictedCoLipCerts_of_le {K' : Matrix I I ENNReal}
    (hK : K ∈ restrictedCoLipCerts d ϕ U) (hle : ∀ i j : I, arrow K' i j ≤ arrow K i j) :
    K' ∈ restrictedCoLipCerts d ϕ U := by
  refine ⟨hK.1, hK.2.1, fun x hx y hy j => le_trans ?_ (hK.2.2 x hx y hy j)⟩
  exact Finset.sum_le_sum fun i _ => mul_le_mul_left (hle i j) _

end CoLipCertificates

/-! ## §4 分量通道、单行稀疏与对角特例（CH02-D07）；行化简（CH02-P19） -/

section Channels

variable {I : Type}

/-- **定义（分量通道）**：有序对 `(i, j) : I × I` 称为从输入分量 `d_i` 到输出分量 `d_j`
的分量通道。 -/
abbrev Channel (I : Type) := I × I

/-- 通道的输入分量 `i`。 -/
def Channel.input (c : Channel I) : I := c.1

/-- 通道的输出分量 `j`。 -/
def Channel.output (c : Channel I) : I := c.2

/-- 通道 `(i, j)` 在矩阵 `L` 中的系数 `L_{i→j}`。 -/
def Channel.coeff (L : Matrix I I ENNReal) (c : Channel I) : ENNReal :=
  arrow L c.input c.output

@[simp] theorem Channel.coeff_mk (L : Matrix I I ENNReal) (i j : I) :
    Channel.coeff L (i, j) = arrow L i j := rfl

/-- **单行稀疏（单一输入通道）**：矩阵 `L` 的第 `j` 行除 `L_{i→j}` 外均为零，
即输出分量 `d_j` 的界中只有通道 `(i, j)` 的系数可能非零。 -/
def RowSingleInput (L : Matrix I I ENNReal) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → arrow L k j = 0

/-- 用矩阵的行写出单行稀疏：第 `j` 行在第 `i` 列之外为零。 -/
theorem rowSingleInput_iff_row (L : Matrix I I ENNReal) (i j : I) :
    RowSingleInput L i j ↔ ∀ k : I, k ≠ i → L j k = 0 :=
  Iff.rfl

/-- **对角特例**：`L` 为对角矩阵（mathlib 的 `Matrix.IsDiag`），当且仅当每一行 `j`
都只含同分量通道 `(j, j)` 的系数。 -/
theorem isDiag_iff_forall_rowSingleInput (L : Matrix I I ENNReal) :
    L.IsDiag ↔ ∀ j : I, RowSingleInput L j j := by
  constructor
  · intro h j k hk
    exact h (Ne.symm hk)
  · intro h a b hab
    exact h a b (Ne.symm hab)

/-- 对角矩阵的非对角条目 `L_{i→j}`（`i ≠ j`）为零。 -/
theorem arrow_eq_zero_of_isDiag {L : Matrix I I ENNReal} (h : L.IsDiag) {i j : I} (hij : i ≠ j) :
    arrow L i j = 0 :=
  h (Ne.symm hij)

variable [Fintype I]

/-- 条目 `L_{i→j}` 为零时，通道 `(i, j)` 的项不参与输出分量 `d_j` 的上界：
`∑_k L_{k→j} v_k = ∑_{k ≠ i} L_{k→j} v_k`。 -/
theorem sum_arrow_eq_sum_erase_of_arrow_eq_zero [DecidableEq I] {L : Matrix I I ENNReal}
    {i j : I} (h : arrow L i j = 0) (v : I → ENNReal) :
    ∑ k : I, arrow L k j * v k = ∑ k ∈ Finset.univ.erase i, arrow L k j * v k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), h, zero_mul, zero_add]

/-- 单行稀疏时，第 `j` 行的系数和只剩通道 `(i, j)` 一项：
`∑_k L_{k→j} v_k = L_{i→j} v_i`。 -/
theorem sum_arrow_eq_single_of_rowSingleInput {L : Matrix I I ENNReal} {i j : I}
    (hrow : RowSingleInput L i j) (v : I → ENNReal) :
    ∑ k : I, arrow L k j * v k = arrow L i j * v i := by
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rw [hrow k hk, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable {X : Type} {bot : X}

/-- **CH02-P19（单一输入项行化简）**：设 `L ∈ 𝓛(ϕ)|_U` 且第 `j` 行除 `L_{i→j}` 外均为零，
则对任意 `x, y ∈ U`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{k} L_{k→j} d_k(x, y) = L_{i→j} d_i(x, y)`。 -/
theorem lip_row_single_input {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L : Matrix I I ENNReal} {i j : I}
    (hL : L ∈ restrictedLipCerts d ϕ U) (hrow : RowSingleInput L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, arrow L k j * d k x y ∧
        ∑ k : I, arrow L k j * d k x y = arrow L i j * d i x y := by
  intro x hx y hy
  exact ⟨hL.2 x hx y hy j, sum_arrow_eq_single_of_rowSingleInput hrow (fun k => d k x y)⟩

/-- 条目 `L_{i→j}` 为零时，通道 `(i, j)` 的项不参与 `d_j` 的 Lip 上界：对任意 `x, y ∈ U`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{k ≠ i} L_{k→j} d_k(x, y)`。 -/
theorem lip_le_sum_erase_of_arrow_eq_zero [DecidableEq I] {d : I → X → X → ENNReal}
    {ϕ : Operator X bot} {U : Set X} {L : Matrix I I ENNReal} {i j : I}
    (hL : L ∈ restrictedLipCerts d ϕ U) (h : arrow L i j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, arrow L k j * d k x y := by
  intro x hx y hy
  rw [← sum_arrow_eq_sum_erase_of_arrow_eq_zero h (fun k => d k x y)]
  exact hL.2 x hx y hy j

/-- CH02-P19 的标量形式：`d_j(ϕ(x), ϕ(y)) ≤ L_{i→j} d_i(x, y)`。 -/
theorem lip_row_single_input_le {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L : Matrix I I ENNReal} {i j : I}
    (hL : L ∈ restrictedLipCerts d ϕ U) (hrow : RowSingleInput L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ arrow L i j * d i x y := by
  intro x hx y hy
  obtain ⟨hle, heq⟩ := lip_row_single_input hL hrow x hx y hy
  exact heq ▸ hle

/-- **CH02-P19（对角特例）**：若 `L ∈ 𝓛(ϕ)|_U` 为对角矩阵，则对每个同分量通道 `(i, i)`
与任意 `x, y ∈ U`，`d_i(ϕ(x), ϕ(y)) ≤ ∑_k L_{k→i} d_k(x, y) = L_{i→i} d_i(x, y)`。 -/
theorem lip_diag_channel {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L : Matrix I I ENNReal}
    (hL : L ∈ restrictedLipCerts d ϕ U) (hdiag : L.IsDiag) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, arrow L k i * d k x y ∧
        ∑ k : I, arrow L k i * d k x y = arrow L i i * d i x y := by
  intro i
  exact lip_row_single_input hL ((isDiag_iff_forall_rowSingleInput L).1 hdiag i)

set_option linter.unusedVariables false in
/-- **CH02-P19（正文同形）**：在扩展规范空间语境（`I` 有限非空、各 `d_i` 为扩展伪度量）中，
设 `ϕ ∈ 𝓧_op`、`U ⊆ dom(ϕ)`、`L ∈ 𝓛(ϕ)|_U`。
(a) 若第 `j` 行除 `L_{i→j}` 外均为零，则对任意 `x, y ∈ U`，
`d_j(ϕ(x), ϕ(y)) ≤ ∑_k L_{k→j} d_k(x, y) = L_{i→j} d_i(x, y)`；
(b) 若 `L` 为对角矩阵，则上述化简对每个同分量通道 `(i, i)` 成立。 -/
theorem lip_row_single_input_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (hU : U ⊆ dom ϕ)
    (L : Matrix I I ENNReal) (hL : L ∈ restrictedLipCerts d ϕ U) :
    (∀ i j : I, (∀ k : I, k ≠ i → arrow L k j = 0) →
      ∀ x ∈ U, ∀ y ∈ U,
        d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, arrow L k j * d k x y ∧
          ∑ k : I, arrow L k j * d k x y = arrow L i j * d i x y) ∧
    (L.IsDiag →
      ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
        d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, arrow L k i * d k x y ∧
          ∑ k : I, arrow L k i * d k x y = arrow L i i * d i x y) :=
  ⟨fun _ _ hrow => lip_row_single_input hL hrow, fun hdiag => lip_diag_channel hL hdiag⟩

end Channels

/-! ## §5 命题 2.8：正 co-Lip 通道保持可分辨性（CH02-P20、CH02-P21） -/

section CoLipChannels

variable {X I : Type} {bot : X} [Fintype I]
variable {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : Matrix I I ENNReal}

/-- co-Lip 不等式与非负性：对 `x, y ∈ U` 与任意通道 `(i, j)`，
`d_j(ϕ(x), ϕ(y)) ≥ ∑_k K_{k→j} d_k(x, y) ≥ K_{i→j} d_i(x, y)`。 -/
theorem coLip_channel_lower_bound (hK : K ∈ restrictedCoLipCerts d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ i j : I,
      arrow K i j * d i x y ≤ ∑ k : I, arrow K k j * d k x y ∧
        ∑ k : I, arrow K k j * d k x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy i j
  refine ⟨?_, hK.2.2 x hx y hy j⟩
  exact Finset.single_le_sum (f := fun k => arrow K k j * d k x y)
    (fun _ _ => zero_le _) (Finset.mem_univ i)

/-- **命题 2.8 (i)（CH02-P20）**：设 `K ∈ 𝓚(ϕ)|_U`。若 `K_{i→j} > 0`，则对任意
`x, y ∈ U`，`d_i(x, y) > 0 ⟹ d_j(ϕ(x), ϕ(y)) > 0`。 -/
theorem coLip_pos_channel_preserves_pos (hK : K ∈ restrictedCoLipCerts d ϕ U) {i j : I}
    (hij : 0 < arrow K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hxy
  obtain ⟨h1, h2⟩ := coLip_channel_lower_bound hK x hx y hy i j
  have hpos : 0 < arrow K i j * d i x y := ENNReal.mul_pos hij.ne' hxy.ne'
  exact lt_of_lt_of_le hpos (h1.trans h2)

/-- 命题 2.8 (i) 的通道写法：若通道 `c = (i, j)` 的 co-Lip 系数为正，则 `c` 把输入分量
`d_i` 上的正距离传为输出分量 `d_j` 上的正距离。 -/
theorem coLip_pos_channel_preserves_pos' (hK : K ∈ restrictedCoLipCerts d ϕ U) (c : Channel I)
    (hc : 0 < Channel.coeff K c) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d c.input x y → 0 < d c.output (ϕ.func x) (ϕ.func y) :=
  coLip_pos_channel_preserves_pos hK hc

/-- **命题 2.8 (ii)（CH02-P21）**：设 `K ∈ 𝓚(ϕ)|_U`。若对所有 `j ∈ I` 有 `K_{j→j} > 0`，
则 `ϕ` 在 `U` 上反射族零距关系：对任意 `x, y ∈ U`，`ϕ(x) ∼_𝒢 ϕ(y) ⟹ x ∼_𝒢 y`。
结论是族零距关系 `GaugeZeroRelated d x y`，不加强为点相等（见 `NonSeparatingExample`）。 -/
theorem coLip_diag_pos_reflects_zero (hK : K ∈ restrictedCoLipCerts d ϕ U)
    (hdiag : ∀ j : I, 0 < arrow K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have himg : 0 < d j (ϕ.func x) (ϕ.func y) :=
    coLip_pos_channel_preserves_pos hK (hdiag j) x hx y hy hpos
  exact himg.ne' (hrel j)

set_option linter.unusedVariables false in
/-- **命题 2.8 (i)（正文同形，CH02-P20）**：扩展规范空间语境中，设 `K ∈ 𝓚(ϕ)|_U`
（含 `U ≠ ∅`、`U ⊆ dom(ϕ)`）。若 `K_{i→j} > 0`，则对任意 `x, y ∈ U`，
`d_i(x, y) > 0 ⟹ d_j(ϕ(x), ϕ(y)) > 0`。 -/
theorem coLip_pos_channel_preserves_pos_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (K : Matrix I I ENNReal)
    (hK : K ∈ restrictedCoLipCerts d ϕ U) (i j : I) (hij : 0 < arrow K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) :=
  coLip_pos_channel_preserves_pos hK hij

set_option linter.unusedVariables false in
/-- **命题 2.8 (ii)（正文同形，CH02-P21）**：扩展规范空间语境中，设 `K ∈ 𝓚(ϕ)|_U`。
若 `K_{j→j} > 0` 对所有 `j ∈ I` 成立，则对任意 `x, y ∈ U`，
`ϕ(x) ∼_𝒢 ϕ(y) ⟹ x ∼_𝒢 y`。 -/
theorem coLip_diag_pos_reflects_zero_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (K : Matrix I I ENNReal)
    (hK : K ∈ restrictedCoLipCerts d ϕ U) (hdiag : ∀ j : I, 0 < arrow K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y :=
  coLip_diag_pos_reflects_zero hK hdiag

end CoLipChannels

/-! ### CH02-P21 的结论不能加强为点相等

非分离规范空间中，全对角正 co-Lip 证书只能反射族零距关系，不能给出 `x = y`。
例：`X = Option Bool`、`⊥ = none`、单分量 `I = Unit`，`d(a, b) = 0`（`a, b` 同为非吸收点或同为
`⊥`），否则 `= +∞`；取 `ϕ = id`、`U = dom(ϕ)`、`K = 𝐈`。 -/

namespace NonSeparatingExample

/-- 单分量扩展伪度量：两个非吸收点之间距离为零，与吸收元之间距离为 `+∞`。 -/
def gaugeDist : Unit → Option Bool → Option Bool → ENNReal :=
  fun _ a b => if a.isSome = b.isSome then 0 else ⊤

/-- `gaugeDist` 满足扩展伪度量四公理与非吸收点存在性。 -/
@[reducible] def pseudo : ∀ i : Unit, ExtendedPseudoMetric (Option Bool) none (gaugeDist i) :=
  fun _ =>
  { nonabsorbing := ⟨some true, by simp⟩
    dist_self := by intro x; simp [gaugeDist]
    symm := by
      intro x y
      by_cases h : x.isSome = y.isSome
      · simp [gaugeDist, h]
      · simp [gaugeDist, h, Ne.symm h]
    triangle := by
      intro x y z
      rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;> simp [gaugeDist]
    isolate_bot := by
      intro x hx
      rcases x with _ | x
      · exact absurd rfl hx
      · simp [gaugeDist] }

/-- 恒等算子。 -/
def op : Operator (Option Bool) none := ⟨id, rfl⟩

/-- 限制域 `U = dom(id)`。 -/
def U : Set (Option Bool) := dom op

/-- 单位矩阵作为 co-Lip 证书。 -/
def K : Matrix Unit Unit ENNReal := 1

theorem K_mem : K ∈ restrictedCoLipCerts gaugeDist op U := by
  refine ⟨⟨some true, by simp [U, dom, op]⟩, subset_rfl, ?_⟩
  intro x _ y _ j
  simp [K, arrow, op]

theorem K_diag_pos : ∀ j : Unit, 0 < arrow K j j := by
  intro j
  simp [K, arrow]

/-- 满足命题 2.8 (ii) 全部前提的实例中存在 `x, y ∈ U`，`ϕ(x) ∼_𝒢 ϕ(y)` 但 `x ≠ y`。 -/
theorem exists_zero_related_ne :
    ∃ x ∈ U, ∃ y ∈ U, GaugeZeroRelated gaugeDist (op.func x) (op.func y) ∧ x ≠ y := by
  refine ⟨some true, by simp [U, dom, op], some false, by simp [U, dom, op], ?_, by simp⟩
  intro i
  simp [gaugeDist, op]

end NonSeparatingExample

/-- **CH02-P21（不加强为点相等）**：存在有限非空指标族上的扩展规范空间、算子 `ϕ`、
受限 co-Lip 证书 `K ∈ 𝓚(ϕ)|_U` 满足全对角条目为正，但有 `x, y ∈ U` 使
`ϕ(x) ∼_𝒢 ϕ(y)` 而 `x ≠ y`。故命题 2.8 (ii) 的结论 `x ∼_𝒢 y` 一般不能加强为 `x = y`。 -/
theorem coLip_diag_pos_not_point_eq :
    ∃ (X : Type) (bot : X) (d : Unit → X → X → ENNReal)
      (_ : ∀ i : Unit, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (K : Matrix Unit Unit ENNReal),
      K ∈ restrictedCoLipCerts d ϕ U ∧ (∀ j : Unit, 0 < arrow K j j) ∧
        ∃ x ∈ U, ∃ y ∈ U, GaugeZeroRelated d (ϕ.func x) (ϕ.func y) ∧ x ≠ y :=
  ⟨Option Bool, none, NonSeparatingExample.gaugeDist, NonSeparatingExample.pseudo,
    NonSeparatingExample.op, NonSeparatingExample.U, NonSeparatingExample.K,
    NonSeparatingExample.K_mem, NonSeparatingExample.K_diag_pos,
    NonSeparatingExample.exists_zero_related_ne⟩

/-! ## §6 习题 2.2：对角输入项的标量双侧界（CH02-P25） -/

section Exercise

variable {X I : Type} {bot : X} [Fintype I]

/-- **习题 2.2（CH02-P25）**：设 `L ∈ 𝓛(ϕ)|_U`、`K ∈ 𝓚(ϕ)|_U`、`j ∈ I`，且关于输出分量
`d_j` 的 Lip 上界只保留对角输入项：`L_{k→j} = 0`（`∀ k ≠ j`）。则对任意 `x, y ∈ U`，
`K_{j→j} d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j→j} d_j(x, y)`。 -/
theorem scalar_two_sided_bound {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}
    {L K : Matrix I I ENNReal} {j : I}
    (hL : L ∈ restrictedLipCerts d ϕ U) (hK : K ∈ restrictedCoLipCerts d ϕ U)
    (hrow : ∀ k : I, k ≠ j → arrow L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      arrow K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ arrow L j j * d j x y := by
  intro x hx y hy
  obtain ⟨h1, h2⟩ := coLip_channel_lower_bound hK x hx y hy j j
  exact ⟨h1.trans h2, lip_row_single_input_le hL hrow x hx y hy⟩

set_option linter.unusedVariables false in
/-- **习题 2.2（正文同形，CH02-P25）**：扩展规范空间语境中，设 `ϕ ∈ 𝓧_op`、`U ⊆ dom(ϕ)`、
`j ∈ I`，给定 `L ∈ 𝓛(ϕ)|_U` 与 `K ∈ 𝓚(ϕ)|_U`。若 `L_{k→j} = 0`（`∀ k ≠ j`），
则对任意 `x, y ∈ U`，`K_{j→j} d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j→j} d_j(x, y)`。 -/
theorem scalar_two_sided_bound_textbook [Nonempty I] (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (hU : U ⊆ dom ϕ) (j : I)
    (L K : Matrix I I ENNReal)
    (hL : L ∈ restrictedLipCerts d ϕ U) (hK : K ∈ restrictedCoLipCerts d ϕ U)
    (hrow : ∀ k : I, k ≠ j → arrow L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      arrow K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ arrow L j j * d j x y :=
  scalar_two_sided_bound hL hK hrow

end Exercise

end LCH01
