# 有限记录上的演化筛选

设 $X,Y$ 为任意集合，$B\subseteq Y$ 有限，$q:X\to Y$，$f:X\to X$，$g:Y\to Y$。令 $A=q^{-1}(B)$。只假定对每个 $x\in A$，
\[
q(f(x))=q(x)\quad\text{或}\quad q(f(x))=g(q(x)).
\]
这里允许一次实际演化保持记录不变。域外没有约束，也不要求 $q$ 单射、满射或 $X$ 有限。

定义 $T_0=B$，$T_{n+1}=\{y\in B:g(y)\in T_n\}$，以及
\[
K=\{x\in X:\forall n\in\mathbb N,\ f^n(x)\in A\}.
\]
作者希望用 $T_{|B|}$ 完整描述 $K$，声称
\[
K=q^{-1}(T_{|B|}),
\]
并把这个集合识别为包含于 $A$ 的最大 $f$-前向不变集。

附件为作者提交的完整 Lean 实现。审核它的定义、前提、依赖和结论是否覆盖上述目标，给出可定位的数学依据，并分别判断代码中的定理与作者的自然语言主张。若存在范围差异，说明差异是否影响原主张，并给出决定性的论证或反例。无需修改文件。

环境：Lean 4.29.1，Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。仅附件为候选输入；`RecordLayers.lean`、`OrbitModel.lean`、`Candidate.lean` 按此顺序组成项目。
