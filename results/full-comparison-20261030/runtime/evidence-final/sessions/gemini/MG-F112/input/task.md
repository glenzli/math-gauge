# 有限乘法上界的形式化

给定任意集合 $X$ 及函数 $d,e:X\to[0,+\infty]$。采用扩展非负实数算术，特别是 $0\cdot(+\infty)=0$。有限系数 $c\in[0,+\infty)$ 称为可行，如果对所有 $x$ 都有 $e(x)\le c\,d(x)$。最小有限可行系数是一个有限可行系数，且不大于任何其他有限可行系数。

定义
\[
Z:\ \forall x,\ d(x)=0\Rightarrow e(x)=0,\qquad
H:\ \forall x,\ d(x)=+\infty\Rightarrow e(x)=0,
\]
以及
\[
r=\sup\left\{\frac{e(x)}{d(x)}:0<d(x)<+\infty\right\},
\]
空集上确界取 $0$。

请以 $Z,H,r$ 给出并形式化有限可行系数存在的充要条件、最小有限可行系数存在的充要条件，以及存在时的最小值公式。再给出一组实际数据，形式化验证“存在有限可行系数”并不保证“存在最小有限可行系数”。

附件 `ExtendedData.lean` 只提供背景定义。自行陈述所需定理并给出完整 Lean 证明，不得改变函数的取值域。提交每个完整文件的 `lean` 代码块，块前标明文件名，并说明各声明对应的数学结论。允许使用等价编码及其他正确证明路线。

环境：Lean 4.29.1，Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。


File: `ExtendedData.lean`
```lean
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

namespace MathGauge.F112

open ENNReal
variable {X : Type*}

def Bound (d e : X → ℝ≥0∞) (c : ℝ≥0∞) : Prop := ∀ x, e x ≤ c * d x

def ZeroCompatible (d e : X → ℝ≥0∞) : Prop := ∀ x, d x = 0 → e x = 0

def TopCompatible (d e : X → ℝ≥0∞) : Prop := ∀ x, d x = ∞ → e x = 0

noncomputable def ratioSup (d e : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ x : {x : X // d x ≠ 0 ∧ d x ≠ ∞}, e x / d x

def LeastFinite (d e : X → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  c ≠ ∞ ∧ Bound d e c ∧ ∀ b, b ≠ ∞ → Bound d e b → c ≤ b

end MathGauge.F112
```
