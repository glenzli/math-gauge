# 扩展非负值上界与最小系数

设 $X$ 为任意集合，$d,e:X\to[0,+\infty]$。采用扩展非负实数的通常序与算术，特别是 $0\cdot(+\infty)=0$。称有限系数 $c\in[0,+\infty)$ 可行为
\[
\forall x\in X,\qquad e(x)\le c\,d(x).
\]
令
\[
Z:\ \forall x,\ d(x)=0\Rightarrow e(x)=0,\qquad
H:\ \forall x,\ d(x)=+\infty\Rightarrow e(x)=0,
\]
并令
\[
r=\sup\left\{\frac{e(x)}{d(x)}:x\in X,\ 0<d(x)<+\infty\right\},
\]
空集上确界取 $0$。

作者提交附件并声称覆盖以下完整结论：有限可行系数存在当且仅当 $Z$ 且 $r<+\infty$；最小有限可行系数存在当且仅当
\[
Z,\qquad r<+\infty,\qquad r=0\Rightarrow H;
\]
存在时其值为 $r$。此外，单点集合上 $d=+\infty,e=1$ 有有限可行系数但没有最小有限可行系数。

请审核全部附件与这些陈述的对应关系，分别说明前提、量词、边界和实际覆盖范围。给出可定位依据；不要仅凭编译状态或声明名称作结论。

环境：Lean 4.29.1，Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`；附件依次为 `ExtendedBounds.lean`、`CoefficientClassification.lean`、`BoundaryExample.lean`。
