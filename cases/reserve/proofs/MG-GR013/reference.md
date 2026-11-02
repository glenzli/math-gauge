# 多项式记录、预解与谱的连续比较：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 共同有限维空间

判定：true。

取基 e_1,…,e_d。坐标泛函有界，故对 ||x||≤1，各坐标之和有统一界，||A_n−A||≤C max_j||(A_n−A)e_j||→0。特征多项式系数连续，故 χ_n 在每个有界圆周上一致趋于 χ。围绕 λ 取不含其他根的小圆，Rouché 定理保证充分大 n 时圆内有与 λ 重数相同的根。令 δ_n=dist(λ,σ(A_n))；对任意这样的半径最终 δ_n 小于它，所以 δ_n→0。每个有限非空谱取最近点，前面有限项任意取谱点，即得整列。

判准：从有限基推出范数收敛；以根的连续性给整列选取。

## S2 紧集上的预解

判定：true。

记 R(λ)=(λI−A)^{-1}。逆映射连续，紧性给 M=sup_K||R||<∞。当 M||A_n−A||<1/2 时，λI−A_n=(λI−A)(I−R(λ)(A_n−A)) 的第二因子由几何级数可逆，逆范数≤2，故 ||R_n−R||≤2M²||A_n−A||。多项式结论用 A_n^m−A^m=Σ_{j=0}^{m−1}A_n^j(A_n−A)A^{m−1−j}；各算子范数有界且项数固定。

判准：统一 Neumann 界；固定次数多项式差估计。

## S3 共同 Banach 空间的多项式作用

判定：true。

归纳：A_n^{m+1}x−A^{m+1}x=A_n(A_n^mx−A^mx)+(A_n−A)A^mx，两项趋零，故有限多项式和强收敛。对 ||x||≤1，有 ||p(A)x||=lim||p(A_n)x||≤liminf||p(A_n)||；对 x 取上确界。这里不能把对每个 x 的极限交换为算子单位球上的一致极限。

判准：固定次数归纳；liminf 下界。

## S4 整体对象与全部恢复目标

判定：false。

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

判准：Resolve the universal spectral recovery target with a valid proof or a complete legal counterexample.；A counterexample must verify one common nonzero complex Banach space, bounded finite-dimensional-range models, the specified contraction bounds and strong convergence.；Verify the extra condition for every complex polynomial, including its constant term: eventual exact operator-norm equality, rather than just convergence of powers or pointwise polynomial evaluations.；Identify a spectral point of the limiting operator that cannot be approached by model spectral points.。

## S5 截断移位的预解大小

判定：true。

n=0 时 N_n=0，范数为 1。n≥1 时 N_n^n=0，逆为 Σ_{k=0}^{n−1}N_n^k，故范数≤n。取前 n 坐标均为 1、其余为零的单位向量，第 n−1 坐标的逆像值为 n，所以范数=n。即值为 max(1,n)，不一致有界。谱均为 {0} 并未给 λ=1 处统一预解界。

判准：有限几何级数；单位向量取得下界。

## S6 两种极限顺序

判定：classification。

固定 n，m≥max(1,n) 时幂为零，内层极限为 0，因此第一个迭代极限是 0。固定 m，n>m 时 N_n^m e_0=e_m，且收缩界给范数恰为 1，故第二个内层极限为 1，外层仍为 1。∀m∃N_m 的记录允许先固定 m 再令 n 大，不能选出一个有限 n 同时超过所有 N_m。S5 还显示谱点距离不控制预解的统一大小。

判准：两内层极限逐项证明；量词次序说明。
