# 线性观测的完整载体与最优恢复

在 ZFC 中，设 $E$ 为实向量空间，$H$ 为实 Hilbert 空间，$A:E\to H$ 为线性映射。记代数商 $Q=E/\ker A$，商映射为 $q:E\to Q$。在 $Q$ 上考虑
\[
\|q(x)\|_A=\|Ax\|_H.
\]

构造这一赋范空间的完备化 $\widehat Q$ 及线性等距映射 $J:\widehat Q\to H$，使得 $J\iota q=A$，并确定 $J$ 的像。对固定的完备化，证明满足 $J\iota q=A$ 的线性等距映射 $J$ 唯一；其中 $\iota:Q\to\widehat Q$ 是完备化映射。

对每个 $y\in H$，研究
\[
\inf_{u\in\widehat Q}\|y-Ju\|_H.
\]
构造其唯一极小点 $R(y)$，证明 $R$ 线性且为 $1$-Lipschitz，并确定这个最小值与 $\inf_{x\in E}\|y-Ax\|_H$ 的关系。最后，给出原空间中
\[
M_y=\left\{x\in E:\|y-Ax\|_H
            =\inf_{z\in E}\|y-Az\|_H\right\}
\]
非空的充要条件，以及非空时 $M_y$ 的完整描述。
