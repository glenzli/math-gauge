import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

/-!
# 第 2 章 算子界：通道矩阵的指标约定与乘法（义务 CH02-D03）

本文件形式化正文 § 2.1 中矩阵 `𝐋` 的书写约定与乘法：
条目以 `i → j`（输入分量 `i`、输出分量 `j`）标记，取值于 `ℝ̄₊`；
书写矩阵时以输出分量为行指标、输入分量为列指标，
即 `(𝐋)_{ji} = L_{i→j}`；并给出命题 2.2 证明中使用的代数矩阵乘法。
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

/--
OET anchor: oet-af85899693cc8750
**约定（通道矩阵）**
以 `L i j` 表示条目 `L_{i→j}`：输入分量为 `i`，输出分量为 `j`。
条目取值于 `ℝ̄₊`（`ENNReal`），非负性由值类型保证。
-/
abbrev ChannelMatrix (I : Type) : Type := I → I → ENNReal

section Conventions

variable {I : Type}

/--
OET anchor: oet-af85899693cc8750
**约定（行/列指标）**
书写矩阵 `𝐋` 时，以输出分量为行指标、输入分量为列指标：
`L_{i→j}` 位于第 `j` 行、第 `i` 列，即 `(𝐋)_{ji} = L_{i→j}`。
`toRowMatrix L` 即 `L` 在该行列约定下的矩阵形式。 -/
def toRowMatrix (L : ChannelMatrix I) : Matrix I I ENNReal := fun j i => L i j

@[simp] theorem toRowMatrix_apply (L : ChannelMatrix I) (j i : I) :
    toRowMatrix L j i = L i j := rfl

/--
OET anchor: oet-af85899693cc8750
**第 `j` 行**：汇集指向输出分量 `d_j` 的系数（以输入分量为参变量）。 -/
def outputRow (L : ChannelMatrix I) (j : I) : I → ENNReal := fun i => L i j

/--
OET anchor: oet-af85899693cc8750
**第 `i` 列**：汇集自输入分量 `d_i` 出发的系数（以输出分量为参变量）。 -/
def inputCol (L : ChannelMatrix I) (i : I) : I → ENNReal := fun j => L i j

@[simp] theorem outputRow_apply (L : ChannelMatrix I) (j i : I) :
    outputRow L j i = L i j := rfl

@[simp] theorem inputCol_apply (L : ChannelMatrix I) (i j : I) :
    inputCol L i j = L i j := rfl

/-- 行列约定下的第 `j` 行即 `outputRow L j`。 -/
theorem toRowMatrix_eq_outputRow (L : ChannelMatrix I) (j : I) :
    toRowMatrix L j = outputRow L j := rfl

end Conventions

section Multiplication

variable {I : Type} [Fintype I]

/--
OET anchor: oet-af85899693cc8750
**定义（矩阵乘法的通道形式）**
对应命题 2.2 证明中的代数矩阵乘法元素：
`(𝐋² · 𝐋¹)_{i→j} = ∑_{k ∈ I} L²_{k→j} · L¹_{i→k}`
（左因子 `L2` 后作用；`I` 有限保证求和合法）。 -/
noncomputable def matMul (L2 L1 : ChannelMatrix I) : ChannelMatrix I :=
  fun i j => ∑ k : I, L2 k j * L1 i k

@[simp] theorem matMul_apply (L2 L1 : ChannelMatrix I) (i j : I) :
    matMul L2 L1 i j = ∑ k : I, L2 k j * L1 i k := rfl

/--
OET anchor: oet-af85899693cc8750
通道形式的乘法与正文行列约定下的代数矩阵乘法一致：
`toRowMatrix (matMul L2 L1) = toRowMatrix L2 * toRowMatrix L1`。 -/
theorem toRowMatrix_matMul (L2 L1 : ChannelMatrix I) :
    toRowMatrix (matMul L2 L1) = toRowMatrix L2 * toRowMatrix L1 := by
  ext j i
  simp [Matrix.mul_apply]

/--
OET anchor: oet-af85899693cc8750
通道矩阵乘法满足结合律
（`ℝ̄₊` 的有限和可按分配律展开并交换求和次序）。 -/
theorem matMul_assoc (L3 L2 L1 : ChannelMatrix I) :
    matMul (matMul L3 L2) L1 = matMul L3 (matMul L2 L1) := by
  funext i j
  have h1 : matMul (matMul L3 L2) L1 i j
      = ∑ k : I, ∑ m : I, (L3 m j * L2 k m) * L1 i k := by
    simp only [matMul_apply, Finset.sum_mul]
  have h2 : ∑ k : I, ∑ m : I, (L3 m j * L2 k m) * L1 i k
      = ∑ m : I, ∑ k : I, (L3 m j * L2 k m) * L1 i k := Finset.sum_comm
  have h3 : ∑ m : I, ∑ k : I, (L3 m j * L2 k m) * L1 i k
      = ∑ m : I, ∑ k : I, L3 m j * (L2 k m * L1 i k) :=
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  have h4 : ∑ m : I, ∑ k : I, L3 m j * (L2 k m * L1 i k)
      = matMul L3 (matMul L2 L1) i j := by
    simp only [matMul_apply, Finset.mul_sum]
  rw [h1, h2, h3, h4]

end Multiplication

end formal_oet.vol_01.ch_02_operator_bounds
