# 参考论证：多项式范数记录与谱恢复

原强目标为假。下述反例不仅保留每个多项式的渐近范数，而且对每个固定多项式，在全部充分大的模型上给出完全相同的范数。独立语义审核和人工审核待定；未运行候选模型。形式化对应见 `formal/COVERAGE.md`。

## 共同空间与有限模型

取 $E=c_0(\mathbb N_0;\mathbb C)$，范数为 $\|x\|_\infty=\sup_j|x_j|$。该空间非零且完备；这是离散自然数空间上消失于无穷远的连续函数 Banach 空间。令

$$
(Sx)_0=0,\qquad(Sx)_{j+1}=x_j,
$$

以及

$$
(N_nx)_0=0,\qquad
(N_nx)_{j+1}=\begin{cases}x_j,&j+1<n,\\0,&j+1\ge n.\end{cases}
$$

两者线性并保持 $c_0$，且范数均不超过 $1$。$N_n$ 的输出在所有坐标 $j\ge n$ 为零，其像空间通过前 $n$ 个坐标单射到 $\mathbb C^n$，因此有限维。

对 $m\ge0$，逐次代入给出

$$
(S^mx)_j=\begin{cases}x_{j-m},&m\le j,\\0,&m>j,\end{cases}
$$

而对 $m\ge1$，

$$
(N_n^mx)_j=\begin{cases}x_{j-m},&m\le j<n,\\0,&\text{其余情形}.\end{cases}\tag{1}
$$

特别地 $N_n^{n+1}=0$，这个统一表述也覆盖 $n=0$。对于给定 $x\in c_0$，$N_nx-Sx$ 在头部坐标为零，在其余坐标等于 $-x_{j-1}$。因为 $x_j\to0$，得到 $\|N_nx-Sx\|_\infty\to0$。所以题设的强收敛与一致收缩界均成立。

## 核验全部多项式范数

固定 $p(z)=\sum_{k=0}^d a_kz^k$，并记 $A=\sum_{k=0}^d|a_k|$。由收缩界和三角不等式，

$$\|p(S)\|\le A,\qquad\|p(N_n)\|\le A\quad(n\ge0).\tag{2}$$

该估计包含常数项 $a_0I_E$；$p(N_n)$ 作为算子作用在整个共同空间 $E$ 上，未把它误换成像空间上的限制。

构造一个有限支撑测试向量 $v\in c_0$：对 $0\le k\le d$，令

$$
v_{d-k}=\begin{cases}|a_k|/a_k,&a_k\ne0,\\0,&a_k=0,\end{cases}
$$

其余坐标取零。则 $\|v\|_\infty\le1$，并且 $a_kv_{d-k}=|a_k|$。因此

$$
(p(S)v)_d=\sum_{k=0}^da_kv_{d-k}=A.
$$

若 $n>d$，式 (1) 对 $k\ge1$ 给出同样的第 $d$ 坐标，$k=0$ 项则由 $N_n^0=I_E$ 直接给出。故

$$
(p(N_n)v)_d=A\qquad(n>d).
$$

由坐标值不超过向量范数及 $\|v\|\le1$，得到上述算子范数至少为 $A$。结合 (2)，有精确等式

$$\boxed{\ \|p(N_n)\|=\|p(S)\|=\sum_{k=0}^d|a_k|\quad(n>d).\ }\tag{3}$$

零多项式和常数多项式均包括在论证中；不需要测试向量范数严格等于 $1$。因此每个题设多项式都可取 $N_p=d+1$。

## 有限模型的全部谱与极限谱点

每个 $N_n$ 都幂零。对 $\lambda\ne0$，有限几何级数

$$
R_{n,\lambda}=\lambda^{-1}\sum_{k=0}^{n}(\lambda^{-1}N_n)^k
$$

是有界算子，并由 $N_n^{n+1}=0$ 直接望远镜相乘得到

$$(\lambda I-N_n)R_{n,\lambda}=R_{n,\lambda}(\lambda I-N_n)=I.$$

另一方面，标准坐标向量 $e_n\ne0$ 满足 $N_ne_n=0$，所以 $0\in\sigma(N_n)$。于是

$$\sigma(N_n)=\{0\}\qquad(n\ge0).\tag{4}$$

现在考察 $I-S$。若存在 $x\in c_0$ 满足 $(I-S)x=e_0$，第零坐标强迫 $x_0=1$，后续坐标依次强迫 $x_{j+1}=x_j$。因此 $x_j=1$ 对所有 $j$，与 $x\in c_0$ 矛盾。所以 $I-S$ 不满射，进而不可能有有界双侧逆，即

$$1\in\sigma(S).\tag{5}$$

式 (4) 表明任何选择 $\lambda_n\in\sigma(N_n)$ 都只能是恒零序列，不能收敛到 (5) 的谱点 $1$。这已经完整反驳题面目标，不需要计算 $S$ 的整个谱。

## 审核与来源范围

合法反例必须同时核验共同的非零复 Banach 空间、有限维像、一致范数界、逐点强收敛，以及题面给定的每个多项式最终范数相等。只有熟悉的“有限截断谱可能失败”陈述，而没有核验额外多项式条件，不构成完整反例。接受任何其他满足全部条件的短反例；不要求本稿的空间、相位向量或先证明完整谱公式。

谱半径公式涉及对幂次数的极限，而题设对每个固定多项式给出的阈值依赖该多项式；不能无证明地交换这两个过程。明确附加条件后成立的谱恢复定理可另记为贡献，不能当作原目标已经成立。

公开背景是 A. C. Hansen 在 Cambridge 官方页面提供的有限截断谱近似讨论：*On the approximation of spectra of linear Hilbert space operators*, PhD thesis，Chapter 6, p.84：<https://www.damtp.cam.ac.uk/research/afha/anders/PhD_thesis.pdf>；同类移位例亦见其官方预印本 <https://www.damtp.cam.ac.uk/research/afha/anders/Inf_Num_Lin_Alg_Final.pdf> 的 p.3。访问于 2026-10-29。来源支持有限截断移位与谱近似失败的公开背景；本题的 $c_0$ 实现、全体多项式最终精确范数条件及逐项证明独立构造。未使用未公开 OET 内容。
