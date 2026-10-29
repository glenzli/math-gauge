# 双重平均与不变记录

设 $E$ 为实 Banach 空间，$T,S:E\to E$ 为交换的有界线性算子。已知

$$K_T=\sup_{n\ge0}\|T^n\|<\infty,\qquad K_S=\sup_{m\ge0}\|S^m\|<\infty.$$

令

$$A_{N,M}=\frac1{NM}\sum_{i=0}^{N-1}\sum_{j=0}^{M-1}T^iS^j\qquad(N,M\ge1),$$

并把状态的记录定义为其在 Banach 商空间

$$Q=E/Y,\qquad Y=\overline{(I-T)E+(I-S)E}$$

中的像。闭包取范数闭包。双重平均的极限按 $\min(N,M)\to\infty$ 理解。

建立这套记录的平均化恢复理论：证明平均过程保持记录，并且 $A_{N,M}x$ 在范数下趋于零当且仅当 $x$ 的记录为零，刻画范数极限能够定义的全部状态，并在该域上构造平均过程确定的有界投影。请给出主定理及完整论证。
