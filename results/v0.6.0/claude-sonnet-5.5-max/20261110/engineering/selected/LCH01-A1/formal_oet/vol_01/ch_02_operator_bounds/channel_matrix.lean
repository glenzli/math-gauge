import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_02_operator_bounds

/-!
# 第 2 章 §2.1：输入/输出矩阵指标约定与矩阵乘法（CH02-D03）

扩展非负矩阵用 `Matrix I I ENNReal` 表示（条目取值于 `[0, +∞]`）。
按正文约定，书写矩阵时以**输出分量为行指标、输入分量为列指标**：
条目 `L_{i→j}`（输入 `i`，输出 `j`）位于第 `j` 行、第 `i` 列，即 `(L)_{ji} = L_{i→j}`。
`chanEntry L i j` 即 `L_{i→j}`。矩阵乘积用 Mathlib 的 `Matrix` 乘法，
其条目公式恰为正文的 `(M₂ · M₁)_{i→j} = ∑ₖ (M₂)_{k→j} (M₁)_{i→k}`。
-/

section ChannelMatrix

variable {I : Type}

/--
OET anchor: h-af85899693cc8750
**指标约定**：条目 `M_{i→j}`（输入分量 `i`、输出分量 `j`）。
矩阵以输出分量为行指标、输入分量为列指标，故 `M_{i→j}` 位于第 `j` 行、第 `i` 列，
即 `(M)_{ji} = M_{i→j}`。
-/
def chanEntry (M : Matrix I I ENNReal) (i j : I) : ENNReal := M j i

/-- `(M)_{ji} = M_{i→j}`：条目 `M_{i→j}` 位于第 `j` 行、第 `i` 列。 -/
theorem chanEntry_eq_apply (M : Matrix I I ENNReal) (i j : I) :
    chanEntry M i j = M j i := rfl

/-- 第 `j` 行汇集指向输出分量 `d_j` 的全部系数 `L_{i→j}`（`i ∈ I`）。 -/
theorem row_eq_coefficients_into_output (M : Matrix I I ENNReal) (j : I) :
    (fun i => M j i) = fun i => chanEntry M i j := rfl

/-- 第 `i` 列汇集从输入分量 `d_i` 出发的全部系数 `L_{i→j}`（`j ∈ I`）。 -/
theorem col_eq_coefficients_from_input (M : Matrix I I ENNReal) (i : I) :
    (fun j => M j i) = fun j => chanEntry M i j := rfl

/--
正文中 `I = {1,2,3}` 时的展示：第一行汇集指向输出 `d₁` 的系数，第一列汇集从输入 `d₁` 出发的系数，
例如 `L_{2→1}` 位于第一行、第二列。此处以 `Fin 3` 的 `0, 1, 2` 表示分量 `1, 2, 3`。
-/
theorem matrix_display_fin3 (L : Matrix (Fin 3) (Fin 3) ENNReal) :
    L = !![chanEntry L 0 0, chanEntry L 1 0, chanEntry L 2 0;
           chanEntry L 0 1, chanEntry L 1 1, chanEntry L 2 1;
           chanEntry L 0 2, chanEntry L 1 2, chanEntry L 2 2] := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

/--
OET anchor: h-af85899693cc8750（行列约定）；h-193cebcc1a7f9259（命题 2.2 证明中的乘法条目）
**矩阵乘积的条目公式**：`(M₂ · M₁)_{i→j} = ∑ₖ (M₂)_{k→j} · (M₁)_{i→k}`。
先作用的矩阵 `M₁` 写在右侧。
-/
theorem chanEntry_mul [Fintype I] (M₂ M₁ : Matrix I I ENNReal) (i j : I) :
    chanEntry (M₂ * M₁) i j = ∑ k : I, chanEntry M₂ k j * chanEntry M₁ i k := by
  simp only [chanEntry, Matrix.mul_apply]

/-- 单位矩阵的条目：`𝐈_{i→j} = 1`（`i = j`），否则为 `0`。 -/
theorem chanEntry_one [DecidableEq I] (i j : I) :
    chanEntry (1 : Matrix I I ENNReal) i j = if i = j then 1 else 0 := by
  simp only [chanEntry, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- 矩阵作用于输入分量量值向量 `v`：`∑ᵢ M_{i→j} · v_i` 是通常的矩阵-向量乘积的第 `j` 个分量。 -/
theorem sum_chanEntry_mul_eq_mulVec [Fintype I] (M : Matrix I I ENNReal) (v : I → ENNReal)
    (j : I) :
    ∑ i : I, chanEntry M i j * v i = (M.mulVec v) j := by
  simp [Matrix.mulVec, dotProduct, chanEntry]

/--
**乘积作用于向量**：`∑ᵢ (M₂ · M₁)_{i→j} v_i = ∑ₖ (M₂)_{k→j} · (∑ᵢ (M₁)_{i→k} v_i)`。
这是两步系数先后作用与矩阵乘积一致所需的代数恒等式（有限和交换次序）。
-/
theorem sum_chanEntry_mul [Fintype I] (M₂ M₁ : Matrix I I ENNReal) (v : I → ENNReal) (j : I) :
    ∑ i : I, chanEntry (M₂ * M₁) i j * v i
      = ∑ k : I, chanEntry M₂ k j * ∑ i : I, chanEntry M₁ i k * v i := by
  have h := congrFun (Matrix.mulVec_mulVec v M₂ M₁) j
  rw [sum_chanEntry_mul_eq_mulVec, ← h, Matrix.mulVec, dotProduct]
  simp [Matrix.mulVec, dotProduct, chanEntry]

/-- 条目取值于 `[0, +∞]`：Lip/co-Lip 矩阵是非负矩阵。 -/
theorem chanEntry_nonneg (M : Matrix I I ENNReal) (i j : I) : 0 ≤ chanEntry M i j :=
  zero_le _

end ChannelMatrix

end formal_oet.vol_01.ch_02_operator_bounds
