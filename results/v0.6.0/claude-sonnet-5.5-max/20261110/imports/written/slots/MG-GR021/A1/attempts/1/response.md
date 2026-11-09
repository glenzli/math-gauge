下面按 1→2→3 的顺序作答。证明所依赖的结构引理放在第一部分。我另外对随机合法 $A$ 做了穷举核对，范围是 $d\le3$、$L=\mathbb Q_2$，以及 $d=2$、$L=K_{-1},K_2$，$M\le6$。基数、约化像、纤维、固定点结构和判准都与下文公式一致。

## 记号

- $\mathcal O=\mathcal O_L$，$\mathfrak p=\pi\mathcal O$。三种 $L$ 的剩余域都是 $\mathbb F_2$：$F$ 取 $\pi=2$，$K_{-1}$ 取 $\pi_{-1}=1+\theta$（$\pi^2=2\theta$），$K_2$ 取 $\pi_2=\theta$（$\pi^2=2$）。
- $e=v_\pi(2)$：$F$ 时 $e=1$，$K_\mu$ 时 $e=2$。于是 $2^k\mathcal O=\mathfrak p^{ek}$，$|\mathcal O/2^k|=2^{ek}$。另有 $\sigma(\pi_\mu)=\pi_\mu-2\theta$。
- $d=\sum n_j$，$s=\sum_j\binom{n_j}2$，$\hat I_j=\{1..d\}\setminus I_j$。
- $\mathrm{Alt}(\mathbf n)$、$\mathrm{Sym}(\mathbf n)$ 分别是 $\mathbb F_2$ 上按块对角嵌入 $M_d(\mathbb F_2)$ 的"对称且对角为 0"、"对称"矩阵空间，$|\mathrm{Alt}|=2^s$，$|\mathrm{Sym}|=2^{d+s}$。
- 模 4 不变量：$\tau_j(A)=\#\{(k,l):k\in I_j,\ l\in\hat I_j,\ (A_j)_{kl}\equiv2\pmod 4\}\bmod 2$。这里 $(A_j)_{kl}$ 因 $A_j\equiv E_j$ 而全为偶数。
- $\kappa(A)=1$ 当且仅当 $\tau_1=\dots=\tau_r=0$，否则 $\kappa(A)=0$。$r=1$ 时恒有 $\kappa=1$。

## 结果

**定理 A（$L\in\{F,K_{-1},K_2\}$，$M\ge2$）**

1. $\mathscr S_L(A)\ne\emptyset\iff\kappa(A)=1$，判准与 $L$ 无关。等价地，$\operatorname{tr}\big((\epsilon_j)_{I_jI_j}\big)\equiv n_j\pmod 8$ 对所有 $j$ 成立，其中 $\epsilon_j$ 是引理 1 的规范幂等元。
2. 基数：
   - $|\mathscr R_{L,M}(A)|=\kappa(A)\,2^{\,r+e(M-1)s}$。
   - $M\ge3$ 时 $|\mathscr C_{L,M}(A)|=\kappa(A)\,2^{\,ed+r+e(M-1)s}$。
   - $M=2$ 时 $|\mathscr C_{L,2}(A)|=2^{e(d+s)}$，与 $A$ 无关。
3. 空集条件：
   - $\mathscr R_{L,M}(A)=\emptyset\iff\kappa=0$。
   - $\mathscr C_{L,M}(A)=\emptyset\iff M\ge3$ 且 $\kappa=0$。
   - $M=2$ 时 $\mathscr C_{L,2}$ 永不为空，但 $\kappa=0$ 时它与 $\mathscr R_{L,2}=\emptyset$ 无交。
4. 判准：设 $\bar U\in\mathscr C_{L,M}(A)$，$U\in M_d(\mathcal O)$ 是它的任一提升。则
$$\bar U\in\mathscr R_{L,M}(A)\iff \sum_{l=1}^dU_{lk}^2\equiv1\pmod{2^{M+1}\mathcal O}\quad(k=1,\dots,d).$$
   左边模 $2^{M+1}$ 与提升的选取无关。
5. 精度 $M+1\to M$ 的约化：
   - $\mathscr R_{L,M+1}\to\mathscr R_{L,M}$ 是满射，所有纤维大小为 $2^{es}$。
   - $\mathscr C_{L,M+1}\to\mathscr C_{L,M}$ 的像恰为 $\mathscr R_{L,M}$，所有非空纤维大小为 $2^{e(d+s)}$。
   - $\kappa=0$ 时两个像都为空。

**定理 B（$K=K_\mu$，$\theta=\theta_\mu$，$\sigma=\sigma_\mu$，$M\ge2$）**

1. 模 $2^M$ 的类 $\bar Y$ 是 $\sigma$-固定的，当且仅当 $\bar Y=\bar W+2^{M-1}\theta V$，其中 $\bar W\in M_d(\mathbb Z/2^M)$，$V\in M_d(\mathbb F_2)$，表示唯一。$M=2$ 时 $\sigma$ 在 $\mathscr R_{K,2}$、$\mathscr C_{K,2}$ 上平凡。
2. 固定点集：
$$\mathscr R_{K,M}(A)^\sigma=\mathscr R_{F,M}(A)+2^{M-1}\pi_\mu\,\mathrm{Alt}(\mathbf n),\qquad \mathscr C_{K,M}(A)^\sigma=\mathscr C_{F,M}(A)+2^{M-1}\theta\,\mathrm{Sym}(\mathbf n).$$
   - 两式右边的并都是无交并。
   - 当 $M\ge3$ 或 $\mu=2$ 时，第一式的 $\pi_\mu$ 可换成 $\theta$。
   - $\mathscr R_{F,M}=\mathscr R_{K,M}\cap M_d(\mathbb Z/2^M)$，它是 $V=0$ 的固定类。
3. 固定点数：
   - $|\mathscr R^\sigma_{K,M}|=2^s|\mathscr R_{F,M}|=\kappa 2^{r+Ms}$。
   - $M\ge3$ 时 $|\mathscr C^\sigma_{K,M}|=2^{d+s}|\mathscr C_{F,M}|=\kappa 2^{2d+r+Ms}$；$M=2$ 时为 $2^{2d+2s}$。
4. $\langle\sigma\rangle$ 轨道数：轨道数 $=(|\mathscr X|+|\mathscr X^\sigma|)/2$。
   - $\mathscr R_{K,M}$ 的轨道数为 $\kappa2^{r-1}(2^{2(M-1)s}+2^{Ms})$。
   - $\mathscr C_{K,M}$ 的轨道数，$M\ge3$ 时为 $\kappa2^{2d+r-1}(2^{2(M-1)s}+2^{Ms})$，$M=2$ 时为 $2^{2d+2s}$。
   - 固定点集内部每个固定点自成一轨道，轨道数就是固定点数。
5. 约化 $M+1\to M$：
   - $(\mathscr R_{K,M+1})^\sigma\to(\mathscr R_{K,M})^\sigma$ 的像是 $\mathscr R_{F,M}$，纤维大小 $2^{2s}$。
   - $(\mathscr C_{K,M+1})^\sigma\to(\mathscr C_{K,M})^\sigma$ 的像也是 $\mathscr R_{F,M}$，纤维大小 $2^{2(d+s)}$。
6. 固定类的提升：
   - 固定类能提升为 $\sigma$-固定的真解，当且仅当它属于 $\mathscr R_{F,M}(A)$。理由是 $\sigma$-固定的真解恰为 $\mathscr S_F(A)$。
   - 固定类能成为逐层相容的固定类序列在精度 $M$ 的分量，条件同样是属于 $\mathscr R_{F,M}(A)$。
   - 因此 $\varprojlim\mathscr R^\sigma_{K,M}=\varprojlim\mathscr C^\sigma_{K,M}=\mathscr S_F(A)$。
   - 只要固定类能再延一层，它就已经在 $\mathscr R_{F,M}$ 中。

**定理 C（下降）**

1. 若 $n_1=\dots=n_r=1$（即 $d=r$），则 $N_{\max}=M$。此时 $\mathscr S_{K}(A)=\mathscr S_F(A)$。
2. 若某个 $n_j\ge2$，则对每个 $M\ge2$ 和两个 $\mu$，都有 $N_{\max}=M-1$。
3. 对给定的 $A$ 和 $U$，能取 $N=M$ 当且仅当 $\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}$。等价地，把 $U=U_a+\theta U_b$（$U_a,U_b\in M_d(\mathbb Z_2)$）展开，条件是 $U_b\equiv0\pmod{2^M}$。
4. $M=2$ 时假设 $\sigma U\equiv U\pmod 4$ 自动成立。

## 一、结构引理

**引理 0。** 设 $Q\in M_d(\mathcal O)$ 满足 $Q\equiv0\pmod2$ 且 $Q^2\equiv Q\pmod{2^M}$，则 $Q\equiv0\pmod{2^M}$。

证明：若 $Q\in2^tM_d$，则 $Q\equiv Q^2\in 2^{2t}M_d\pmod{2^M}$，对 $t$ 迭代即得。∎

**引理 1（规范幂等元）。** 存在对称幂等矩阵 $\epsilon_1,\dots,\epsilon_r\in M_d(\mathbb Z_2)$，满足：

- $\epsilon_j\epsilon_k=0$（$j\ne k$），$\sum_j\epsilon_j=I$，$\epsilon_j\equiv E_j\pmod 2$。
- $\epsilon_j$ 与所有 $A_i$ 可交换。
- $\epsilon_j\equiv E_j+2(E_jY_j+Y_jE_j)\pmod4$，其中 $Y_j=(A_j-E_j)/2$。

证明：取 $a_0=A_j$，$a_{n+1}=3a_n^2-2a_n^3$，$f_n=a_n^2-a_n$。直接计算得
$$f_{n+1}=-f_n^2(3-2a_n)(1+2a_n),\qquad a_{n+1}-a_n=-(2a_n-1)f_n.$$

- 每个 $a_n$ 都是 $A_j$ 的 $\mathbb Z_2$-系数多项式，故对称，并与所有 $A_i$ 可交换。
- $f_0\in2M_d$，所以 $f_n\in2^{2^n}M_d$，$a_n$ 收敛到某个 $\epsilon_j$。它是幂等的，且 $\epsilon_j\equiv A_j\equiv E_j\pmod2$。
- 当 $j\ne k$ 时，$\epsilon_j\epsilon_k$ 是幂等元，且 $\equiv E_jE_k=0\pmod 2$，由引理 0 知它为 $0$。
- $I-\sum_j\epsilon_j$ 是幂等元，且 $\equiv0\pmod2$，故为 $0$。
- 对任意 $n\ge1$ 有 $a_{n+1}-a_n\in4M_d$，所以 $\epsilon_j\equiv3A_j^2-2A_j^3\pmod4$。代入 $A_j\equiv E_j+2Y_j$ 即得最后一条。∎

**引理 2（刚性）。** 设 $M\ge1$，$P\in M_d(\mathcal O)$ 满足 $P^2\equiv P\pmod{2^M}$，$P\equiv E_j\pmod2$，且 $[A_i,P]\equiv0\pmod{2^M}$ 对所有 $i$ 成立。则 $P\equiv\epsilon_j\pmod{2^M}$。

证明：记 $P_{kl}=\epsilon_kP\epsilon_l$。

- 当 $k\ne l$ 时，由 $\epsilon_k[A_k,P]\epsilon_l\equiv0$ 得 $A_kP_{kl}\equiv P_{kl}A_k\pmod{2^M}$。
- 因 $A_k\epsilon_k\equiv\epsilon_k$ 且 $A_k\epsilon_l\equiv0\pmod 2$，有 $A_kP_{kl}=P_{kl}+2(\cdots)$，$P_{kl}A_k=2(\cdots)$。于是 $P_{kl}\in2P_{kl}M_d+2^MM_d$，逐步迭代得 $P_{kl}\equiv0\pmod{2^M}$。
- 因此 $P_{kk}^2\equiv P_{kk}\pmod{2^M}$，且 $P_{kk}\equiv\delta_{jk}\epsilon_k\pmod2$。
- $k\ne j$ 时，对 $P_{kk}$ 用引理 0，得 $P_{kk}\equiv0$。
- $k=j$ 时，对 $\epsilon_k-P_{kk}$ 用引理 0，得 $P_{kk}\equiv\epsilon_k$。∎

**引理 3（Gram 矩阵）。** 设 $\tilde E_j$ 是 $\epsilon_j$ 的 $I_j$ 列构成的 $d\times n_j$ 矩阵，$G_j=\tilde E_j^{\mathsf T}\tilde E_j=(\epsilon_j)_{I_jI_j}$。则：

1. $\epsilon_j=\tilde E_jG_j^{-1}\tilde E_j^{\mathsf T}$。
2. $G_j=I+4T_j$，其中 $T_j$ 为对称的 $\mathbb Z_2$-矩阵。
3. $\operatorname{tr}T_j\equiv\tau_j(A)\pmod2$。

证明：

- (1) 令 $\Pi=\tilde E_jG_j^{-1}\tilde E_j^{\mathsf T}$。它是对称幂等元，且 $\Pi\equiv E_j\pmod 2$。由 $\epsilon_j\tilde E_j=\tilde E_j$ 得 $\epsilon_j\Pi=\Pi=\Pi\epsilon_j$。于是 $\epsilon_j-\Pi$ 是幂等元，且 $\equiv0\pmod2$，由引理 0 知 $\Pi=\epsilon_j$。
- (2)(3) 把 $\epsilon_j$ 写成分块 $\begin{pmatrix}G&C\\C^{\mathsf T}&*\end{pmatrix}$。$\epsilon_j^2=\epsilon_j$ 给出 $G-G^2=CC^{\mathsf T}$。因 $C=2C'$，有 $G(I-G)=4C'C'^{\mathsf T}$，所以 $G=I+4T$，且 $T=-G^{-1}C'C'^{\mathsf T}\equiv C'C'^{\mathsf T}\pmod2$。
- 于是 $\operatorname{tr}T\equiv\sum C'^2_{kl}\equiv\sum C'_{kl}\pmod 2$。由引理 1 的模 4 公式，$C\equiv(A_j)_{I_j\hat I_j}\pmod4$，故这个和等于 $\tau_j$。∎

**命题 4（分块化）。** 对 $M\ge1$，下面的映射是双射：
$$\prod_j\mathscr G_j(\mathcal O/2^M)\to\mathscr C_{L,M}(A),\qquad(\bar g_j)\mapsto\bar U=[\tilde E_1\bar g_1|\cdots|\tilde E_r\bar g_r].$$
其中 $\mathscr G_j(\mathcal O/2^M)=\{\bar g\in M_{n_j}(\mathcal O/2^M):\bar g\equiv I\ (2),\ \bar g^{\mathsf T}G_j\bar g=I\}$。对精确解（$M=\infty$）同样成立。此时 $\mathscr R_{L,M}(A)$ 对应各块精确解的约化之积，$\bar U\in\mathscr R_{L,M}$ 当且仅当每个 $\bar g_j$ 是 $\mathscr G_j$ 精确解的约化。

证明：

1. 设 $\bar U\in\mathscr C_{L,M}(A)$，取提升 $U\equiv I\pmod 2$，令 $P=UE_jU^{-1}$。它是精确幂等元，$\equiv E_j\pmod 2$。又 $U^{-1}\equiv U^{\mathsf T}\pmod{2^M}$，所以 $[A_i,P]=U[U^{-1}A_iU,E_j]U^{-1}\equiv0$。由引理 2，$\bar UE_j\bar U^{\mathsf T}=\bar\epsilon_j$。
2. 因此 $\bar\epsilon_j\bar U_{(j)}=\bar U_{(j)}$，其中 $\bar U_{(j)}$ 是 $\bar U$ 的 $I_j$ 列。由引理 3(1)，$\bar U_{(j)}=\tilde E_j\bar g_j$，$\bar g_j=G_j^{-1}\tilde E_j^{\mathsf T}\bar U_{(j)}$ 唯一。
3. 因 $\tilde E_j\equiv E_j^{\rm col}$（$E_j$ 的 $I_j$ 列），得 $\bar g_j\equiv I\pmod2$。由 $\bar U^{\mathsf T}\bar U=I$ 得 $\bar g_j^{\mathsf T}G_j\bar g_j=I$。
4. 反过来，对给定的 $(\bar g_j)$：不同块之间 $\tilde E_j^{\mathsf T}\tilde E_k=0$，所以 $\bar U^{\mathsf T}\bar U=I$，从而 $\bar U\bar U^{\mathsf T}=I$。又 $\bar g_j\bar g_j^{\mathsf T}=G_j^{-1}$，于是 $\bar UE_j\bar U^{\mathsf T}=\tilde E_jG_j^{-1}\tilde E_j^{\mathsf T}=\bar\epsilon_j$。
5. 因此 $[\bar U^{\mathsf T}A_i\bar U,E_j]=\bar U^{\mathsf T}[A_i,\bar\epsilon_j]\bar U=0$。精确情形用引理 2 对所有 $M$ 取极限。∎

## 二、单块计数

取 $G=I+4T$，$n\ge1$，$g=I+2X$，$X\in M_n(\mathcal O)$。则
$$g^{\mathsf T}Gg-I=2\Phi(X),\quad \Phi=X+X^{\mathsf T}+2X^{\mathsf T}X+2T+4(X^{\mathsf T}T+TX)+8X^{\mathsf T}TX.$$

- $\Phi$ 对称，且对角元为偶数。坐标取 $\psi_{kk}=\Phi_{kk}/2$ 和 $\psi_{kl}=\Phi_{kl}$（$k<l$），共 $N=n(n+1)/2$ 个。
- 模 $\mathfrak p$：$\bar\psi_{kk}=\bar X_{kk}+\sum_l\bar X_{lk}^2+\bar T_{kk}$，$\bar\psi_{kl}=\bar X_{kl}+\bar X_{lk}$。
- 雅可比矩阵模 $2\mathcal O$ 恒等于常数矩阵 $\Lambda$：$\Lambda\xi=(\xi_{kk};\ \xi_{kl}+\xi_{lk})$，秩为 $N$。

**引理 5（光滑 Hensel）。** 设 $m\ge1$，$c\in\mathcal O^N$。

- 模 $\mathfrak p^m$ 的每个解 $\psi(X)\equiv c$ 恰有 $2^{\binom n2}$ 个模 $\mathfrak p^{m+1}$ 的提升，并可提升为精确解。
- 模 $\mathfrak p^m$ 的解数等于 $2^{(m-1)\binom n2}$ 乘以模 $\mathfrak p$ 的解数。

证明：$\psi(X'+\pi^m\xi)\equiv\psi(X')+\pi^m\Lambda\xi\pmod{\mathfrak p^{m+1}}$，而 $\Lambda$ 满秩，解集是维数 $n^2-N=\binom n2$ 的仿射空间。逐层提升并取极限即得。∎

**引理 6（图的度数奇偶）。** 设 $\bar c\in\mathbb F_2^n$，则
$$\#\{\bar X\in\mathrm{Sym}_n(\mathbb F_2):\ \bar X_{kk}+\textstyle\sum_l\bar X_{lk}^2+\bar T_{kk}=\bar c_{kk}\}=\begin{cases}2^{\binom n2+1},&\sum_k(\bar T_{kk}+\bar c_{kk})=0,\\0,&\text{否则。}\end{cases}$$

证明：在 $\mathbb F_2$ 上 $x^2=x$，方程化为 $\sum_{l\ne k}\bar X_{lk}=\bar T_{kk}+\bar c_{kk}$。把 $\bar X$ 的严格上三角看作 $n$ 个顶点上的简单图，方程要求第 $k$ 个顶点度数的奇偶等于 $\bar T_{kk}+\bar c_{kk}$。

- 每条边改变两个顶点的度数奇偶，所以右端之和必为 $0$。
- 边 $ab$ 的像是 $e_a+e_b$，它们生成所有和为 $0$ 的向量，所以像恰为和为 $0$ 的向量，核的维数为 $\binom n2-n+1$。
- 对角元任意，有 $2^n$ 种取法。∎

**命题 7。** 令 $m=e(M-1)$，$t=\operatorname{tr}T\bmod2$，并记 $\mathscr G(\mathcal O/2^M)$ 为单块解集，$\mathscr G^R_M$ 为精确解的约化。

1. 精确解存在当且仅当 $t=0$。
2. $\bar g\leftrightarrow X\bmod 2^{M-1}=\mathfrak p^m$，且
$$\mathscr G(\mathcal O/2^M)=\{X:\ \psi_{kl}\equiv0\ (\mathfrak p^{m}),\ \psi_{kk}\equiv0\ (\mathfrak p^{m-e})\},$$
$$\mathscr G^R_M=\{X:\ \psi(X)\equiv0\ (\mathfrak p^m)\}.$$
   这是因为对角元的方程是 $2\psi_{kk}\equiv0\pmod{2^{M-1}}$，比非对角方程弱一个因子 $2$。
3. 基数：
   - $|\mathscr G^R_M|=[t=0]\,2^{1+m\binom n2}$。
   - $M\ge3$ 时 $|\mathscr G(\mathcal O/2^M)|=[t=0]\,2^{en+1+m\binom n2}$。
   - $M=2$ 时 $|\mathscr G(\mathcal O/2^2)|=2^{en+e\binom n2}$。
4. 定义缺陷 $\delta_k=(\|u_k\|^2-1)/2^M\bmod 2$（$u_k$ 为第 $k$ 列）。则 $\delta_k=\psi_{kk}/2^{M-2}\bmod 2$，$\mathscr G^R_M=\{\delta=0\}$。这给出定理 A(4)。
5. 约化：$\mathscr G(\mathcal O/2^{M+1})\to\mathscr G(\mathcal O/2^M)$ 的像是 $\mathscr G^R_M$，纤维大小 $2^{e(n+\binom n2)}$。$\mathscr G^R_{M+1}\to\mathscr G^R_M$ 是满射，纤维大小 $2^{e\binom n2}$。

证明：

- (1) 用引理 5（取 $m=1$，$c=0$）和引理 6。
- (3)（精确解的约化）把 $c=0$ 代入引理 5 和引理 6。
- (3)（$M\ge3$）此时 $\psi_{kk}$ 的允许值 $c_{kk}\in\mathfrak p^{m-e}/\mathfrak p^m$ 共 $2^{en}$ 个。因 $m-e\ge1$，$\bar c=0$，各 $c$ 的纤维大小相同，所以总数为 $2^{en}\cdot[t=0]\cdot2^{(m-1)\binom n2+\binom n2+1}$。
- (3)（$M=2$）此时 $c_{kk}\in\mathcal O/2$ 任意。可解的 $c$ 满足 $\sum_k(\bar T_{kk}+\bar c_{kk})=0$，恰占一半，共 $2^{en-1}$ 个。总数为 $2^{en-1}\cdot2^{(e-1)\binom n2}\cdot2^{\binom n2+1}=2^{en+e\binom n2}$，与 $t$ 无关。
- (4) $\|u_k\|^2=(g^{\mathsf T}Gg)_{kk}=1+4\psi_{kk}$。列模长平方模 $2^{M+1}$ 与提升无关，因为 $2M\ge M+1$。
- (5) 提升 $X=X_1+\pi^m\xi$（$\xi$ 模 $\mathfrak p^e$）时，$\psi(X)\equiv\psi(X_1)+\pi^m\Lambda\xi$，条件 $m\ge e$ 使二阶项可忽略。非对角方程决定 $\xi_{lk}$（$k<l$）。
  - 对松弛的对角方程，$\xi_{kk}$ 自由，$\xi_{kl}$（$k<l$）自由。纤维大小为 $2^{e(n+\binom n2)}$。
  - 对严格的对角方程，$\xi_{kk}$ 也被决定。纤维大小为 $2^{e\binom n2}$。
  - 像的刻画：层 $M$ 的严格对角条件只依赖 $X_1\bmod\mathfrak p^m$。∎

## 三、定理 A 的证明

**(1)(3) 可行性与空集。** 由命题 4，$\mathscr S_L(A)\neq\emptyset$ 当且仅当每个 $G_j$ 都有精确解。由命题 7(1) 和引理 3，这等价于 $\tau_j=0$（所有 $j$），与 $L$ 无关。$\mathscr R_{L,M}$ 是 $\mathscr S_L$ 的像，所以它空当且仅当 $\kappa=0$。$\mathscr C_{L,M}$ 的空集条件来自命题 7(3)：$M\ge3$ 且 $t_j=1$ 时某块解集为空，而 $M=2$ 时永不为空。

**(2) 基数。** 命题 4 把集合分解为各块之积，把命题 7(3) 的公式按块相乘。$\sum_j1=r$，$\sum_jn_j=d$，$\sum_j\binom{n_j}2=s$，即得公式。

**(4) 判准。** 命题 4 把 $\bar U$ 对应到 $(\bar g_j)$，且 $\|u_k\|^2=(\bar g_j^{\mathsf T}G_j\bar g_j)_{kk}$。再用命题 7(4)。

**(5) 约化。** 对各块用命题 7(5) 再取乘积。$M=2$ 时，$\delta$ 的像恰为 $\{\delta:\sum_{k\in I_j}\bar\delta_k\equiv\tau_j\ (\mathfrak p),\ \forall j\}$。

**可行性判准的有限可计算性。** $\tau_j$ 只依赖 $A_j\bmod4$ 的 $I_j$ 行，所以判准可由 $A_i\bmod4$ 有限计算。∎

## 四、定理 B 的证明

**(1)** $\bar Y=\bar Y_a+\theta\bar Y_b$ 固定当且仅当 $2\bar Y_b=0$，即 $\bar Y_b\in2^{M-1}$。对 $\bar Y=I+2X$，固定等价于 $X=X_0+2^{M-2}\theta V\pmod{2^{M-1}}$。$M=2$ 时这对所有 $X$ 成立，所以 $\sigma$ 平凡。

**(2)** 因 $\tilde E_j$ 是 $\mathbb Z_2$ 矩阵且有左逆，$\sigma\bar U=\bar U$ 当且仅当各 $\sigma\bar g_j=\bar g_j$。于是归结为单块。记 $\delta=2^{M-2}\theta V$，展开 $\Phi(X_0+\delta)$，按 $\theta^0$ 和 $\theta$ 分量：

- $\theta$ 分量：$2^{M-2}(V+V^{\mathsf T})+2^{M-1}(X_0^{\mathsf T}V+V^{\mathsf T}X_0)+2^M(\cdots)$。
  - 非对角项模 $2^{M-1}$ 为零，等价于 $V$ 对称。
  - 对角项为 $2^{M-1}V_{kk}+2^M(\cdots)$。松弛条件（$\mathscr C$，模 $2^{M-1}$）自动成立。严格条件（$\mathscr R$，模 $2^M$）等价于 $V_{kk}=0$。
- $\theta^0$ 分量：$\Phi(X_0)+2^{2M-3}\mu V^{\mathsf T}V+2^{2M-1}\mu V^{\mathsf T}TV$。
  - 非对角项和松弛对角项里的附加项都消失，因为 $2M-3\ge M-1$。
  - 严格对角项里的附加项 $2^{2M-3}\mu V^{\mathsf T}V$：$M\ge3$ 时模 $2^M$ 消失，$M=2,\mu=2$ 时消失。
  - 只有 $M=2,\mu=-1$ 时附加项为 $-2\sum_lV_{lk}^2\equiv2\sum_lV_{lk}\pmod 4$，条件变为 $\psi_{kk}(X_0)\equiv\sum_lV_{lk}\pmod2$，即 $\psi_{kk}(X_0+V)\equiv0$。令 $X_0'=X_0+V$，则 $X=X_0'+(1+\theta)V=X_0'+\pi_{-1}V$。

于是：

- $\mathscr C$：$X_0$ 满足 $F$ 上的松弛方程，$V\in\mathrm{Sym}$ 任意，得 $\mathscr C_{F,M}+2^{M-1}\theta\,\mathrm{Sym}$。
- $\mathscr R$：$X_0$（或 $X_0'$）满足 $F$ 上的严格方程，$V\in\mathrm{Alt}$，得 $\mathscr R_{F,M}+2^{M-1}\pi_\mu\mathrm{Alt}$。
- $\tilde E_jV_j\equiv E_j^{\rm col}V_j\pmod 2$，所以块对角的 $V_j$ 拼成 $\mathrm{diag}(V_j)$。

**(3)(4)** 直接计数。轨道数由 Burnside 引理得到。

**(5)** 约化 $\bar W+2^M\pi V\mapsto\bar W\bmod2^M$，因为 $2^M\pi V\equiv0\pmod{2^M}$。

- 对 $\mathscr R^\sigma$，像是 $\mathscr R_{F,M}$，纤维为 $2^s\cdot2^s=2^{2s}$。
- 对 $\mathscr C^\sigma$，像是 $\mathscr C_{F,M+1}\to\mathscr C_{F,M}$ 的像，即 $\mathscr R_{F,M}$（定理 A(5)，取 $e=1$），纤维为 $2^{d+s}\cdot2^{d+s}$。

**(6)** $\sigma$-固定的真解就是 $\mathscr S_F(A)$，其约化构成 $\mathscr R_{F,M}$。由 (5)，能延一层的固定类已在 $\mathscr R_{F,M}$ 中；反过来 $\mathscr R_{F,M}$ 中的类都是精确 $W\in\mathscr S_F(A)$ 的约化序列的分量。∎

## 五、定理 C 的证明与最优性

**下界 $N\ge M-1$。** 设 $U\in\mathscr S_K(A)$，$\sigma U\equiv U\pmod{2^M}$。则 $\bar U\in\mathscr R^\sigma_{K,M}=\mathscr R_{F,M}+2^{M-1}\pi V$。取 $W\in\mathscr S_F(A)$ 使 $\bar W$ 为其中的 $\mathscr R_{F,M}$ 分量，则 $U\equiv W\pmod{2^{M-1}\mathcal O}$。

**$N=M$ 的充要条件。** 展开 $U=U_a+\theta U_b$。

- $U\equiv W\pmod{2^M}$ 对某个 $W\in M_d(\mathbb Z_2)$ 成立，必要地推出 $U_b\equiv0\pmod{2^M}$。
- 反过来，若 $U_b\equiv0\pmod{2^M}$，则 $\bar U\in\mathscr R_{K,M}\cap M_d(\mathbb Z/2^M)=\mathscr R_{F,M}$，故存在 $W\in\mathscr S_F(A)$ 与 $U$ 模 $2^M$ 同余。
- $U-\sigma U=2\theta U_b$，所以 $U_b\equiv0\pmod{2^M}$ 等价于 $\sigma U\equiv U\pmod{2^{M+1}}$。

**全为一阶块（$d=r$）时 $N_{\max}=M$。** 此时 $s=0$，$|\mathscr R_{K,M}|=|\mathscr R_{F,M}|=2^r$，故 $\mathscr R_{K,M}=\mathscr R_{F,M}$。取逆极限得 $\mathscr S_K(A)=\mathscr S_F(A)$，$W=U$ 即可。

**某个 $n_j\ge2$ 时的统一反例。** 取 $A_i=E_i$（对称、可交换、$\equiv E_i$）。此时 $\epsilon_i=E_i$，$G_i=I$，$\mathscr S_L=\prod_j\Gamma_{n_j}(\mathcal O_L)$（块对角矩阵，各块 $g_j\in O_{n_j}(\mathcal O_L)$ 且 $g_j\equiv I\pmod 2$）。设 $s_0=2^{M-2}\pi_\mu$，令
$$g=\frac1{1+s_0^2}\begin{pmatrix}1-s_0^2&-2s_0\\2s_0&1-s_0^2\end{pmatrix}\oplus I_{n_j-2},$$
放在第 $j$ 块，其余块取 $I$。

- $g$ 是 Cayley 型正交矩阵，$g^{\mathsf T}g=I$ 精确成立。
- 因 $s_0\in\mathfrak p$，$1+s_0^2$ 是单位。$g\equiv I\pmod 2$，所以 $U\in\mathscr S_K(A)$。
- 展开：$2s_0/(1+s_0^2)\equiv2^{M-1}\pi_\mu\pmod{2^M}$，$(1-s_0^2)/(1+s_0^2)=1-2s_0^2/(1+s_0^2)\equiv1\pmod{2^M}$。
- 所以 $\bar g\equiv\begin{pmatrix}1&-2^{M-1}\pi_\mu\\2^{M-1}\pi_\mu&1\end{pmatrix}\oplus I\pmod{2^M}$。因 $\pi_\mu-\sigma(\pi_\mu)=2\theta$，这个类是 $\sigma$-固定的。
- 它的 $\theta$ 分量 $2^{M-1}\not\equiv0\pmod{2^M}$，所以对任意 $W\in M_d(\mathbb Z_2)$ 都有 $U\not\equiv W\pmod{2^M}$。故 $N=M$ 不成立，$N_{\max}=M-1$。

数值核对：两个 $\mu$ 下，$M=2,\dots,6$ 都精确验证了 $g^{\mathsf T}g=I$、上述同余式，以及 $y$ 的 $\theta$ 分量的 $2$-进赋值恰为 $M-1$。∎

## 六、反例汇总

1. $\mathscr C\ne\mathscr R$（任意 $M\ge3$）：$d=r=1$，$A_1=(1)$。$\bar U=1+2^{M-1}\in\mathscr C_{F,M}$。它的列模长平方 $\equiv1+2^M\pmod{2^{M+1}}$，故不属于 $\mathscr R_{F,M}=\{\pm1\}$。
2. 不可行例：$d=2$，$n=(1,1)$，$A_1=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix}$，$A_2=I-A_1$。
   - 这里 $\tau_1=\tau_2=1$。直接证明：若 $U\in\mathscr S_L$，则 $U^{\mathsf T}v=(\alpha,0)^{\mathsf T}$（$v=(1,2)^{\mathsf T}$），$\alpha^2=v^{\mathsf T}v=5$，而 $5$ 在 $\mathbb Q_2$、$\mathbb Q_2(i)$、$\mathbb Q_2(\sqrt2)$ 中都不是平方。
   - $M=2$ 时 $\bar U=\begin{pmatrix}1&2\\2&1\end{pmatrix}\in\mathscr C_{L,2}$，但 $\mathscr R_{L,2}=\emptyset$。
   - $M\ge3$ 时 $\mathscr C_{L,M}=\emptyset$。
3. 固定类不可提升：$d=r=1$，$M\ge3$，$\bar U=1+2^{M-1}\theta\in\mathscr C^\sigma_{K,M}$。它不在 $\mathscr R_{F,M}$ 中，也不能成为逐层相容固定序列的分量。
4. 精度 $M$ 的固定类不可提升为真解且不可下降的族：见第五部分，任意 $M\ge2$、两个 $\mu$ 均适用。

## 总表

| 量 | 公式 |
|---|---|
| 可行 | $\forall j$：$\tau_j(A)=0$ |
| $\lvert\mathscr R_{L,M}\rvert$ | $\kappa\,2^{r+e(M-1)s}$ |
| $\lvert\mathscr C_{L,M}\rvert$ | $M\ge3$：$\kappa\,2^{ed+r+e(M-1)s}$；$M=2$：$2^{e(d+s)}$ |
| $\lvert\mathscr R^\sigma_{K,M}\rvert$ | $\kappa\,2^{r+Ms}$ |
| $\lvert\mathscr C^\sigma_{K,M}\rvert$ | $M\ge3$：$\kappa\,2^{2d+r+Ms}$；$M=2$：$2^{2d+2s}$ |
| $\mathscr R$ 的约化纤维 | $2^{es}$ |
| $\mathscr C$ 的约化像与纤维 | 像 $=\mathscr R_{L,M}$，纤维 $2^{e(d+s)}$ |
| 固定点集的约化像与纤维 | 像 $=\mathscr R_{F,M}$；纤维 $2^{2s}$（$\mathscr R$），$2^{2(d+s)}$（$\mathscr C$） |
| $N_{\max}$ | 全为一阶块：$M$；否则：$M-1$（与 $\mu$ 无关） |

$M=2$ 时，$\sigma_\mu$ 在 $\mathscr R_{K,2}$ 和 $\mathscr C_{K,2}$ 上平凡，因为 $\bar U\equiv I\pmod2$ 蕴含 $\sigma\bar U\equiv\bar U\pmod4$。