# 一族映射诱导的拓扑

设 $X$ 为任意集合，$A$ 为任意指标集。对每个 $a\in A$，给定拓扑空间 $(Y_a,\tau_a)$ 和映射 $f_a:X\to Y_a$。构造 $X$ 上使全部 $f_a$ 连续的最粗拓扑 $\tau$，并证明这个拓扑唯一。

还须证明其映射性质：对任意拓扑空间 $(Z,\sigma)$ 及映射 $g:Z\to X$，$g:(Z,\sigma)\to(X,\tau)$ 连续，当且仅当每个 $f_a\circ g:(Z,\sigma)\to(Y_a,\tau_a)$ 连续。

审核附件作为上述结果的形式化提交是否完整对齐。说明各声明实际使用的前提、证明的结论及它们和正文的对应关系，并给出支持判断的数学依据。编译结果和语义判断分别报告；不能把自己补充的论证说成附件已经完成。

附件为 Core.lean、Construction.lean、Candidate.lean。

环境为 Lean 4.29.1，Mathlib 固定修订 5e932f97dd25535344f80f9dd8da3aab83df0fe6。
