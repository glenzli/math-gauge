**说明：** 前期论证得出 $e_0>0$（单元能有严格正间隙），这个结论不成立。六个行列式算得对，两两之间确实没有秩一连接，但四口井合起来构成一个 $T_4$ 构型（Tartar 方块）。下面证明 $e_0=0$。

## 结论

1. $e_0=0$。没有 $u\in\mathcal A$ 能使 $E(u)=0$，即下确界取不到。
2. 极限必然唯一。对任意满足 $E(u_j)\to e_0$ 的序列，
 $$\pi(u_j)\to\pi^*=\Big(\tfrac1{10},\tfrac3{10},\tfrac3{10},\tfrac3{10}\Big),$$
 这是唯一可能的极限。更定量地，对一切 $u\in\mathcal A$：
 $$\max_i|\pi_i(u)-\pi_i^*|\le\tfrac{11}{10}E(u)^{1/2}+\tfrac3{20}E(u).$$
3. 构造是一个显式的 $T_4$ 层合截断 $u_N$，满足 $u_N|_{\partial\Omega}=0$，$\|\nabla u_N\|_F\le\sqrt{10}<4$，并且 $E(u_N)\le 56\cdot 6^{-N}\to0$。

## 前期论证错在哪里

两两不相容只排除了"两口井之间"的一阶层合。层合也可以在一口井和一个**不属于 $K$ 的辅助矩阵**之间进行，再把这个辅助矩阵用下一层层合替换掉。

记 $D(a,b)=\mathrm{diag}(a,b)$，取单位正方形的四个顶点
$$J_1=0,\quad J_2=D(1,0),\quad J_3=D(1,1),\quad J_4=D(0,1).$$

每口井都与一个顶点秩一相连：
- $A_1-J_1=3e_1\otimes e_1$
- $A_2-J_2=2e_2\otimes e_2$
- $A_3-J_3=-3e_1\otimes e_1$
- $A_4-J_4=-4e_2\otimes e_2$

并且有四个分解：
- (T1) $J_1=\tfrac14A_4+\tfrac34J_4$
- (T2) $J_4=\tfrac13A_3+\tfrac23J_3$
- (T3) $J_3=\tfrac12A_2+\tfrac12J_2$
- (T4) $J_2=\tfrac13A_1+\tfrac23J_1$

等价地，$A_i=J_i+\kappa_i(J_{i+1}-J_i)$，其中 $\kappa=(3,2,3,4)$。

边界数据的梯度 $0$ 恰好就是内方块的顶点 $J_1$。按 (T1)→(T2)→(T3)→(T4) 循环层合一轮，未处理的体积乘以 $\tfrac34\cdot\tfrac23\cdot\tfrac12\cdot\tfrac23=\tfrac16$。过程中用到的矩阵范数都 $\le3$，所以统一 Lipschitz 上界并不构成障碍。

两两不相容真正能推出的只有：不存在精确解。这正是下面定理 1 中"取不到"的部分。

## 0. 预备

记号：$|\cdot|$ 为 Frobenius 范数，$(\nabla u)_{ij}=\partial_j u_i$。

**(F1)** 若 $D$ 为对角阵，$O$ 的对角元为零，则 $|D+O|^2=|D|^2+|O|^2$。

**(F2)** 对 $2\times2$ 矩阵：
- $\det(A+R)=\det A+\mathrm{cof}A:R+\det R$；
- $|\mathrm{cof}A:R|\le|A||R|$，$|\det R|\le\tfrac12|R|^2$；
- $\det F-\det G=\tfrac12\mathrm{cof}(F+G):(F-G)$，因此 $|\det F-\det G|\le\tfrac12(|F|+|G|)|F-G|$。

**(F3)** 范数：$|A_1|=|A_4|=3$，$|A_2|=|A_3|=\sqrt5$，$|J_i|\le\sqrt2$。行列式：$\det A_1=\det A_4=0$，$\det A_2=2$，$\det A_3=-2$。另有 $E(0)=\mathrm{dist}^2(0,K)=5$。

**Lipschitz 代表元。** $\Omega$ 是凸的，所以每个 $u\in W^{1,\infty}$ 都有在 $\bar\Omega$ 上 Lipschitz 的代表元，迹为 0 就是 $u|_{\partial\Omega}=0$。

零延拓 $\tilde u$ 在 $\mathbb R^2$ 上也是 Lipschitz 的。理由：对 $x\in\bar\Omega$、$y\notin\bar\Omega$，设 $z$ 是线段 $[x,y]$ 上最后一个属于 $\bar\Omega$ 的点，则 $z\in\partial\Omega$，且
$$|\tilde u(x)-\tilde u(y)|=|u(x)-u(z)|\le L|x-y|.$$
此外 $\nabla\tilde u=\mathbf 1_\Omega\nabla u$ a.e.。

**引理 1.** 若 $u\in\mathcal A$，则 $\int_\Omega\nabla u=0$，且 $\int_\Omega\det\nabla u=0$。

*证明.* 令 $u_\varepsilon=\tilde u*\rho_\varepsilon\in C_c^\infty$，则 $\nabla u_\varepsilon\to\nabla\tilde u$ 于 $L^2$。对 $u_\varepsilon$ 有 $\int\nabla u_\varepsilon=0$。又
$$\det\nabla u_\varepsilon=\partial_1(u^1_\varepsilon\partial_2u^2_\varepsilon)-\partial_2(u^1_\varepsilon\partial_1u^2_\varepsilon),$$
所以 $\int\det\nabla u_\varepsilon=0$。由 (F2) 与 Cauchy–Schwarz，$\det\nabla u_\varepsilon\to\det\nabla\tilde u$ 于 $L^1$。取极限即得两个等式。∎

**引理 2（对角刚性）.** 若 $u\in\mathcal A$ 且 $\nabla u$ a.e. 为对角阵，则 $u\equiv0$。

*证明.* 由假设 $\partial_2u^1=0$ a.e.。由 Fubini，对 a.e. $x_1$，有 $\partial_2u^1(x_1,\cdot)=0$ a.e.。而 $t\mapsto u^1(x_1,t)$ 绝对连续，所以 $u^1(x_1,t)=u^1(x_1,0)=0$。由连续性得 $u^1\equiv0$。同理，由 $\partial_1u^2=0$ 和 $u^2(0,x_2)=0$ 得 $u^2\equiv0$。∎

## 1. 任务 1

**定理 1.** $e_0=0$，且不可达。

*证明.* 因 $E\ge0$，有 $e_0\ge0$。定理 3（§3）给出 $u_N\in\mathcal A$，满足 $E(u_N)\le56\cdot6^{-N}\to0$，所以 $e_0=0$。

假设 $E(u)=0$。那么 $\nabla u\in K$ a.e.，因而 $\nabla u$ a.e. 为对角阵。由引理 2，$u\equiv0$，于是 $\nabla u=0\notin K$。但 $E(0)=5>0$，矛盾。∎

## 2. 任务 2

**定理 2.** 对一切 $u\in\mathcal A$，
$$\max_i|\pi_i(u)-\pi_i^*|\le\tfrac{11}{10}E^{1/2}+\tfrac3{20}E.$$

*证明.*

**记号.** 设 $i(x)$ 为点 $x$ 被分配到的编号。它是 $\nabla u(x)$ 的 Borel 函数，因此可测。令 $R(x)=\nabla u(x)-A_{i(x)}$，则 $|R|^2=\min_l|\nabla u-A_l|^2$。于是 $\int|R|^2=E$，且
$$\sigma:=\int|R|\le E^{1/2}\quad(|\Omega|=1).$$

**三个约束.**
- (a) $\sum_i\pi_i=1$。
- (b) 由引理 1，$0=\int\nabla u=\sum_i\pi_iA_i+\int R$。取 $(1,1)$ 元和 $(2,2)$ 元：
 - $p:=3\pi_1+\pi_2-2\pi_3=-\int R_{11}$，
 - $q:=2\pi_2+\pi_3-3\pi_4=-\int R_{22}$，
 
 因此 $|p|,|q|\le\sigma$。
- (c) 由引理 1 与 (F2)，
 $$0=\int\det\nabla u=\sum_i\pi_i\det A_i+\int\big(\mathrm{cof}A_{i(x)}:R+\det R\big).$$
 所以 $d:=2\pi_2-2\pi_3$ 满足 $|d|\le3\sigma+\tfrac12E$。

**求解.** 记
$$M=\begin{pmatrix}1&1&1&1\\3&1&-2&0\\0&2&1&-3\\0&2&-2&0\end{pmatrix},$$
则 $M\pi=(1,p,q,d)^T$。这里 $\det M=60$，且
$$M^{-1}=\frac1{30}\begin{pmatrix}3&9&1&-7\\9&-3&3&9\\9&-3&3&-6\\9&-3&-7&4\end{pmatrix},\qquad M^{-1}(1,0,0,0)^T=\pi^*.$$
于是
$$\pi-\pi^*=\tfrac1{30}\big(9p+q-7d,\ -3p+3q+9d,\ -3p+3q-6d,\ -3p-7q+4d\big).$$

**代入界.**
- $|\rho_1|\le\tfrac{31}{30}\sigma+\tfrac7{60}E$
- $|\rho_2|\le\tfrac{11}{10}\sigma+\tfrac3{20}E$
- $|\rho_3|\le\tfrac45\sigma+\tfrac1{10}E$
- $|\rho_4|\le\tfrac{11}{15}\sigma+\tfrac1{15}E$

其中 $\rho=\pi-\pi^*$。取最大值，再用 $\sigma\le E^{1/2}$，即得结论。∎

**推论（任务 2 的回答）.** 若 $E(u_j)\to e_0=0$，则整个序列（不必取子列）满足 $\pi(u_j)\to\pi^*$。由定理 3，最小化序列确实存在，所以全部可能极限恰为 $\{\pi^*\}$。平局时取最小编号的规则不影响结论，因为证明只用到 $|R|=\mathrm{dist}(\nabla u,K)$。

**注 1：为什么只看凸组合不够.** 若只用 $\sum\pi_i=1$、$\sum\pi_iA_i=0$、$\pi\ge0$，解集是一整条线段
$$\pi^*+\tau(-7,9,-6,4),\qquad \tau\in\big[-\tfrac1{30},\tfrac1{70}\big],$$
端点为 $(\tfrac13,0,\tfrac12,\tfrac16)$ 与 $(0,\tfrac37,\tfrac3{14},\tfrac5{14})$。真正选出 $\tau=0$ 的是零 Lagrange 量 $\det$ 给出的约束 $\pi_2=\pi_3$。这个 $\pi^*$ 正是 $T_4$ 无穷阶层合测度的权重：由
$$\nu_{J_1}=\tfrac1{12}\delta_{A_1}+\tfrac14(\delta_{A_2}+\delta_{A_3}+\delta_{A_4})+\tfrac16\nu_{J_1}$$
解得 $\nu_{J_1}=\tfrac1{10}\delta_{A_1}+\tfrac3{10}(\delta_{A_2}+\delta_{A_3}+\delta_{A_4})$。

**注 2：局部版本（补充，只给证明要点）.** 对任意最小化序列，还有：
- $u_j\to0$ 一致收敛；
- 对任意可测 $\omega\subset\Omega$，$|\omega\cap\Omega_i(u_j)|\to\pi_i^*|\omega|$。

要点如下。取子列使弱* 极限 $\mathbf 1_{\Omega_i}\rightharpoonup^*\lambda_i$ 存在。则 $\nabla u=\sum_i\lambda_iA_i$ 为对角阵，由引理 2 得 $u=0$。行列式弱连续，给出 $\sum_i\lambda_i\det A_i=0$。于是 $\lambda(x)$ 满足与 $\pi$ 相同的线性方程组，故 $\lambda\equiv\pi^*$。

## 3. 任务 3：显式构造

**各步数据.** 每一步把当前矩阵 $B$ 分解为井 $W$ 与下一个辅助矩阵 $B'$，满足 $W-B'=a\,e_k\otimes e_k$，$B=\lambda W+(1-\lambda)B'$。

| 类型 | $B$ | $W$ | $B'$ | $k$ | $\lambda$ | $a$ | $\lambda(1-\lambda)\lvert a\rvert$ |
|---|---|---|---|---|---|---|---|
| 1 | $J_1$ | $A_4$ | $J_4$ | 2 | 1/4 | −4 | 3/4 |
| 2 | $J_4$ | $A_3$ | $J_3$ | 1 | 1/3 | −3 | 2/3 |
| 3 | $J_3$ | $A_2$ | $J_2$ | 2 | 1/2 | 2 | 1/2 |
| 4 | $J_2$ | $A_1$ | $J_1$ | 1 | 1/3 | 3 | 2/3 |

**引理 3（矩形上的一步截断层合）.**

*设定.* 取表中一行，记 $k'=3-k$。设
$$R=\prod_{j=1}^{2}(\alpha_j,\alpha_j+\ell_j),\qquad v(x)=Bx+c.$$
取 $\theta\in(0,1)$，$\delta=\theta\ell_{k'}/2$，整数 $M\ge 2\ell_k/(\theta\ell_{k'})$，$\epsilon=\ell_k/M$，于是 $\epsilon\le\delta$。

*锯齿函数.* $g_\lambda$ 是 1-周期函数：在 $[0,\lambda]$ 上 $g_\lambda(\tau)=(1-\lambda)\tau$，在 $[\lambda,1]$ 上 $g_\lambda(\tau)=\lambda(1-\tau)$。它满足 $0\le g_\lambda\le\lambda(1-\lambda)$，$g_\lambda'\in\{1-\lambda,-\lambda\}$，且在整数点为 0。

*定义.*
- $h(t)=a\epsilon\, g_\lambda\big((t-\alpha_k)/\epsilon\big)$
- $\phi(r)=\min\{1,\ (r-\alpha_{k'})/\delta,\ (\alpha_{k'}+\ell_{k'}-r)/\delta\}$
- $w=v+\phi(x_{k'})\,h(x_k)\,e_k$

*结论.*
- **(a)** $w$ 在 $\bar R$ 上 Lipschitz，且在 $\partial R$ 上 $w=v$。原因：$\phi$ 在 $x_{k'}$ 方向的两边为零；在 $x_k=\alpha_k$ 与 $x_k=\alpha_k+M\epsilon$ 处 $h=0$。
- **(b)** a.e. 有 $\nabla w=D+O$，其中
 - $D=B+\phi h'\,e_k\otimes e_k\in[B',W]$。原因：$h'=(1-\lambda)a$ 时 $B+h'e_k\otimes e_k=W$，$h'=-\lambda a$ 时为 $B'$，且 $\phi\in[0,1]$。
 - $O=\phi' h\,e_k\otimes e_{k'}$，满足 $|O|\le\lambda(1-\lambda)|a|\epsilon/\delta\le\lambda(1-\lambda)|a|$。
- **(c)** 核心区 $S=\{\alpha_{k'}+\delta<x_{k'}<\alpha_{k'}+\ell_{k'}-\delta\}$ 满足 $|R\setminus S|=\theta|R|$，且在 $S$ 上 $\phi\equiv1$。对 $m=0,\dots,M-1$：
 - 在 $P_m=S\cap\{x_k-\alpha_k\in(m\epsilon,(m+\lambda)\epsilon)\}$ 上，$\nabla w=W$；
 - 在 $Q_m=S\cap\{x_k-\alpha_k\in((m+\lambda)\epsilon,(m+1)\epsilon)\}$ 上，$w$ 是仿射的且 $\nabla w=B'$。
 
 体积：$\sum_m|P_m|=\lambda(1-\theta)|R|$，$\sum_m|Q_m|=(1-\lambda)(1-\theta)|R|$。∎

**构造.** 取 $N\in\mathbb N$，$n=4N$，$\theta=6^{-N}$。第 $s$ 步的类型为 $t(s)=((s-1)\bmod4)+1$。

1. 起点：$u^{(0)}=0$，$\mathcal R_0=\{\Omega\}$。
2. 归纳假设：$\mathcal R_{s-1}$ 是有限个互不相交的开矩形，$u^{(s-1)}$ 在每个矩形上仿射，梯度为第 $t(s)$ 型的 $B$。
3. 第 $s$ 步：取 $M_s=\lceil 2\ell_k/(\theta\ell_{k'})\rceil$，在每个 $R\in\mathcal R_{s-1}$ 上用引理 3（$v=u^{(s-1)}|_R$）得到 $w_R$。令 $u^{(s)}=w_R$ 于 $\bar R$，其余处不变，并令 $\mathcal R_s=\{Q_m(R)\}$。第 $t$ 型的 $B'$ 正是第 $t+1$ 型的 $B$，所以归纳假设得以保持。
4. 合起来：
 $$u_N=\sum_{s=1}^{4N}\ \sum_{R\in\mathcal R_{s-1}}\mathbf 1_{\bar R}\,\phi_R(x_{k'})\,h_R(x_k)\,e_k.$$

第一步的具体形式：$u^{(1)}=\big(0,\ \phi_1(x_1)h_1(x_2)\big)$，其中
$$\phi_1=\min\{1,\ 2x_1/\theta,\ 2(1-x_1)/\theta\},\qquad h_1=-4\epsilon_1 g_{1/4}(x_2/\epsilon_1),\qquad \epsilon_1=1/\lceil2/\theta\rceil.$$
在 $\theta/2<x_1<1-\theta/2$ 内，高 $\epsilon_1/4$ 的水平带上 $\nabla u^{(1)}=A_4$，高 $3\epsilon_1/4$ 的水平带上 $\nabla u^{(1)}=J_4$。

**定理 3.** $u_N\in\mathcal A$，$\|\nabla u_N\|_F\le\sqrt{10}$ a.e.，且
$$E(u_N)\le51\theta+5\cdot6^{-N}=56\cdot6^{-N}.$$

*证明.*

**零边界与 Lipschitz 性.** 由 (a)，每一项 $\mathbf 1_{\bar R}(w_R-v_R)$ 都在 $\mathbb R^2$ 上 Lipschitz，并且在 $\partial R\supseteq\bar R\cap\partial\Omega$ 上为零。$u_N$ 是有限个这样的项之和，所以 $u_N$ Lipschitz 且 $u_N|_{\partial\Omega}=0$。

**区域划分.** 第 $r>s$ 步的修改只发生在 $\bigcup_{Q\in\mathcal R_s}\bar Q$ 内。因此在开集 $U_s=\bigcup_R\big(R\setminus\bigcup_m\bar Q_m\big)$ 上 $u_N=w_R$。$U_s$ 由截断带 $C_s=\bigcup(R\setminus S)$ 和纯井区 $Z_s=\bigcup P_m$ 组成。在剩余集 $F=\bigcup\mathcal R_{4N}$ 上 $\nabla u_N=J_1=0$。

**梯度界.** 在 $U_s$ 上，由 (b)，$|D|\le\max(|B'|,|W|)\le3$（范数在线段上是凸的，再用 (F3)），$|O|\le\tfrac34$（见表）。由 (F1)，
$$|\nabla u_N|^2\le9+\tfrac9{16}<10.$$
在 $F$ 上 $|\nabla u_N|=0$。

**能量密度.**
- 在 $Z_s$ 上为 0。
- 在 $C_s$ 上：$\min_l|\nabla u_N-A_l|^2\le|D-W|^2+|O|^2\le a^2+\tfrac9{16}<17$。
- 在 $F$ 上为 $\mathrm{dist}^2(0,K)=5$。

**体积.** 记 $\mu_s=|\bigcup\mathcal R_s|$。则 $\mu_s=(1-\theta)(1-\lambda_{t(s)})\mu_{s-1}$，$|C_s|=\theta\mu_{s-1}$。每一轮的乘积 $\prod(1-\lambda)=\tfrac16$，所以
$$\sum_{s=1}^{4N}\mu_{s-1}\le\Big(1+\tfrac34+\tfrac12+\tfrac14\Big)\tfrac65=3,\qquad \mu_{4N}\le6^{-N}.$$
因此
$$E(u_N)\le17\cdot3\theta+5\cdot6^{-N}.$$
∎

**体积分数核对.** 第 $s=4c+t$ 步留下的纯井区面积为 $|Z_s|=\lambda_t p_t(1-\theta)^s6^{-c}$，其中 $\lambda_tp_t=(\tfrac14,\tfrac14,\tfrac14,\tfrac1{12})$，对应的井依次为 $(A_4,A_3,A_2,A_1)$。截断带与剩余集的总面积 $\le3\theta+6^{-N}\to0$。所以 $\pi(u_N)\to\tfrac65\big(\tfrac1{12},\tfrac14,\tfrac14,\tfrac14\big)=\pi^*$，与定理 2 一致。

**数值核对（不属于证明）.** 我用精确有理数算术实现了这个构造，并在 $2\times10^4$ 个随机点上做 Monte Carlo 抽样。取 $N=3$、$\theta=1/216$：
- 边界值恰为 0；
- $\max|\nabla u|^2=9.0$；
- $E\approx0.055$，低于理论界 $0.26$；
- 体积分数 $\approx(0.097,\ 0.308,\ 0.290,\ 0.305)$。

另外抽查了 Lipschitz 比值（最大约 9.0，低于 10）和有限差分梯度，与公式一致。