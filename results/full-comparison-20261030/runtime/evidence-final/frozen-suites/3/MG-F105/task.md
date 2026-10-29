# 陪集切片与有限覆盖

设 $G$ 为任意阿贝尔群，$A\subset G$ 为有限集合，$H\le G$ 为子群，$x\in G$，$K\in\mathbb R$。记
$$B=\{a\in A:a-x\in H\}.$$
假设 $B\ne\varnothing$ 且 $|A+A|\le K|A|$。构造有限集合 $F\subseteq A$，使
$$|F|\le\frac{K|A|}{|B|},\qquad
\forall a\in A\ \exists t\in F:\ a-t\in H.$$
基数在不等式中视为实数。背景定义以附件 `Core.lean` 为准；允许使用 Mathlib 及经典逻辑。

附件 `Core.lean`、`Bridge.lean`、`Candidate.lean` 被提交为这一目标的形式化。审核其声明、定义和依赖是否完整对应目标，给出逐项数学依据，并区分代码有效性与覆盖范围。

Lean 4.29.1，Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6。
