# 无限凸约束的有限问题恢复

设 $H$ 是实 Hilbert 空间，$I$ 是任意指标集。对每个 $i\in I$ 给定闭凸集 $C_i\subseteq H$。已知存在有限常数 $B\ge0$，使对每个有限集 $F\subseteq I$ 都有

$$
\exists z_F\in H:\quad \|z_F\|\le B,\qquad z_F\in C_i\quad(i\in F).
$$

记

$$C_F=\bigcap_{i\in F}C_i,\qquad C_\varnothing=H,\qquad C=\bigcap_{i\in I}C_i.$$

对 $x\in H$，令 $P_Fx$ 是 $\|x-z\|$ 在 $z\in C_F$ 上的最小点。有限子集按包含关系排序。

从这些有限约束问题建立全约束的恢复理论。目标是构造映射 $P:H\to C$，使 $Px$ 对每个 $x$ 都是 $\|x-z\|$ 在 $C$ 上的唯一最小点，证明网 $(P_Fx)_F$ 在范数中收敛到 $Px$，由有限问题的最优值确定全局最优值，并证明

$$\|Px-Py\|\le\|x-y\|\qquad(x,y\in H).$$

请给出构造和完整论证。
