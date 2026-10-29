# 商环层中的理想

设 $R$ 为任意交换含幺环，$I$ 为 $R$ 的理想。对每个 $n\in\mathbb N$，令
\[
Q_n=R/I^{n+1},\qquad q_n:R\longrightarrow Q_n,\qquad J_n=q_n(I),
\]
其中 $q_n(I)$ 表示理想的像。若 $m\le n$，令 $\rho_{m,n}:Q_n\to Q_m$ 为满足 $\rho_{m,n}q_n=q_m$ 的商环同态。

所要求的结果是：每个 $J_n^{n+1}$ 都等于零理想；对于 $m\le n$，$\rho_{m,n}(J_n)=J_m$；对于 $l\le m\le n$，$\rho_{l,m}\circ\rho_{m,n}=\rho_{l,n}$。

请从上述数据完成 Lean 形式化。Core.lean 提供商环层、像理想和过渡同态的定义；最终定理的类型及证明由你编写。

提交完整 Lean 文件和覆盖说明。每个文件用独立的代码块交付，格式为 ` ```lean filename=文件名.lean `（实际使用三个反引号），不得只引用本地文件路径。允许等价表述和不同证明路线。说明最终各声明对应正文哪一部分，以及尚未完成的部分。

环境为 Lean 4.29.1，Mathlib 固定修订 5e932f97dd25535344f80f9dd8da3aab83df0fe6。
