# 商环层中的理想

设 $R$ 为任意交换含幺环，$I$ 为 $R$ 的理想。对每个 $n\in\mathbb N$，令
\[
Q_n=R/I^{n+1},\qquad q_n:R\longrightarrow Q_n,\qquad J_n=q_n(I),
\]
其中 $q_n(I)$ 表示理想的像。若 $m\le n$，令 $\rho_{m,n}:Q_n\to Q_m$ 为满足 $\rho_{m,n}q_n=q_m$ 的商环同态。

所要求的结果是：每个 $J_n^{n+1}$ 都等于零理想；对于 $m\le n$，$\rho_{m,n}(J_n)=J_m$；对于 $l\le m\le n$，$\rho_{l,m}\circ\rho_{m,n}=\rho_{l,n}$。

审核附件作为上述结果的形式化提交是否完整对齐。说明各声明实际使用的前提、证明的结论及它们和正文的对应关系，并给出支持判断的数学依据。编译结果和语义判断分别报告；不能把自己补充的论证说成附件已经完成。

附件为 Core.lean、Transfer.lean、Candidate.lean。

环境为 Lean 4.29.1，Mathlib 固定修订 5e932f97dd25535344f80f9dd8da3aab83df0fe6。
