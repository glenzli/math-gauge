**结论：** 前期推理的结论不成立。六个行列式 −4、−5、9、3、5、−8 都算对了，任意两井之间确实没有秩一连接，但单元能**没有**正的间隙。正确结论如下：

1. $e_0=0$，且没有任何 $u\in\mathcal A$ 能达到它。
2. 只要 $E(u_j)\to e_0=0$，就有 $(\pi_1,\dots,\pi_4)(u_j)\to\lambda^*=(\tfrac1{10},\tfrac3{10},\tfrac3{10},\tfrac3{10})$。这是唯一可能的极限。定量地，对所有 $u\in\mathcal A$ 有 $\max_i|\pi_i(u)-\lambda^*_i|\le\tfrac54\sqrt{E(u)}$。
3. 第 2 节给出显式位移 $u_M\in\mathcal A$：零边界，$|\nabla u_M|_F\le 3.1$，且 $E(u_M)\le 6^{1-M}$。

**前提错在哪里：** 二相刚性只适用于两个井。四个井可以借助不属于 $K$ 的辅助矩阵 $P_i$ 依次秩一相连，形成 Tartar 方阵（T4 构型），而零矩阵恰好是其中一个角点。

---

## 0. 记号与 T4 结构

- 记 $\operatorname{diag}(a,b)\leftrightarrow(a,b)$，于是 $A_1=(3,0)$，$A_2=(1,2)$，$A_3=(-2,1)$，$A_4=(0,-3)$。
- 梯度记为 $(\nabla u)_{ij}=\partial_ju_i$。
- 引入辅助矩阵 $P_1=0$，$P_2=(1,0)$，$P_3=(1,1)$，$P_4=(0,1)$，即单位方形的四个角。
- 下表各步都满足 $P=\mu Q+(1-\mu)A$ 和 $Q-A=t\,e_k\otimes e_k$，所以 $Q$ 与 $A$ 秩一相连：

| 步 | $P$ | $Q$ | $A$ | $\mu$ | $k$ | $t$ | $\mu(1-\mu)\lvert t\rvert$ |
|---|---|---|---|---|---|---|---|
| I | $P_1$ | $P_4$ | $A_4$ | 3/4 | 2 | 4 | 3/4 |
| II | $P_4$ | $P_3$ | $A_3$ | 2/3 | 1 | 3 | 2/3 |
| III | $P_3$ | $P_2$ | $A_2$ | 1/2 | 2 | −2 | 1/2 |
| IV | $P_2$ | $P_1$ | $A_1$ | 2/3 | 1 | −3 | 2/3 |

逐行验算：
- I：$\tfrac34(0,1)+\tfrac14(0,-3)=(0,0)$；
- II：$\tfrac23(1,1)+\tfrac13(-2,1)=(0,1)$；
- III：$\tfrac12(1,0)+\tfrac12(1,2)=(1,1)$；
- IV：$\tfrac23(0,0)+\tfrac13(3,0)=(1,0)$。

由 IV、III、II 依次可知 $P_2,P_3,P_4\in\operatorname{conv}K$。又 $P_1=0=\tfrac1{10}A_1+\tfrac3{10}(A_2+A_3+A_4)\in\operatorname{conv}K$。Frobenius 范数是凸函数，在 $\operatorname{conv}K$ 上的最大值取在顶点，即 $\max(3,\sqrt5,\sqrt5,3)=3$。所以 $\operatorname{conv}K$ 中每个矩阵的范数都 $\le3$。

## 1. 两个预备引理

**引理 A（零边界恒等式）。** 对 $u\in\mathcal A$，有 $\int_\Omega\nabla u=0$ 和 $\int_\Omega\det\nabla u=0$。

*证明：*
- 由于 $\Omega$ 是凸集，$u$ 有 Lipschitz 代表元，连续到 $\bar\Omega$，并且在 $\partial\Omega$ 上为 0。
- 令 $\tilde u$ 为 $u$ 的零延拓。若 $x\in\bar\Omega$、$y\notin\bar\Omega$，取线段 $[x,y]$ 与 $\partial\Omega$ 的交点 $z$，则 $|\tilde u(x)-\tilde u(y)|=|u(x)-u(z)|\le L|x-y|$。所以 $\tilde u$ 在 $\mathbb R^2$ 上 Lipschitz、紧支，并且在 $\Omega$ 内 $\nabla\tilde u=\nabla u$，在 $\bar\Omega$ 外 $\nabla\tilde u=0$。
- 第一个恒等式：取 $\chi\in C_c^\infty$ 在 $\operatorname{supp}\tilde u$ 上恒为 1，则 $\int\partial_j\tilde u=-\int\tilde u\,\partial_j\chi=0$。
- 第二个恒等式：令 $\tilde u_\varepsilon=\rho_\varepsilon*\tilde u\in C_c^\infty$。由
  $$\det\nabla w=\partial_1(w_1\partial_2w_2)-\partial_2(w_1\partial_1w_2)$$
  得 $\int\det\nabla\tilde u_\varepsilon=0$。又 $\nabla\tilde u_\varepsilon\to\nabla\tilde u$ 几乎处处成立，且一致有界，支集都在一个固定球内，由控制收敛定理得 $\int_\Omega\det\nabla u=0$。∎

**引理 B（拼接）。** 设 $\bar\Omega$ 是有限个内部互不相交的闭矩形 $\bar R_j$ 之并，$u\in C(\bar\Omega)$，并且每个 $u|_{\bar R_j}$ 是多项式，$\sup_{R_j}|\nabla u|_F\le L$。则 $u$ 在 $\bar\Omega$ 上 $L$-Lipschitz，$u\in W^{1,\infty}$，ess sup$|\nabla u|_F\le L$。

*证明：*
- 在每个凸的 $\bar R_j$ 上，由中值不等式加上取极限得 $|u(p)-u(q)|\le L|p-q|$（算子范数 $\le$ Frobenius 范数）。
- 对一般的 $x,y$，线段 $[x,y]$ 与各 $\bar R_j$ 的交是有限条闭子线段，它们覆盖 $[x,y]$。按顺序取分点 $x=p_0,\dots,p_r=y$，使每段 $[p_{i-1},p_i]$ 落在同一个 $\bar R_j$ 内，求和即得 $|u(x)-u(y)|\le L|x-y|$。
- 由 Rademacher 定理，弱梯度几乎处处等于逐片的经典梯度。∎

## 2. 任务 3：显式近最优位移

**单步层合引理。** 取上表中某一步 $(P,Q,A,\mu,k,t)$，记 $k'=3-k$。设矩形 $R=\prod_i(\alpha_i,\alpha_i+\ell_i)$，$z(x)=Px+c$，$\theta\in(0,\tfrac14]$，并令
$$N=\lceil \ell_k/(\theta\ell_{k'})\rceil,\qquad h=\ell_k/N .$$

构造如下：
- $\varphi$ 连续，$\varphi(\alpha_k)=0$。在 $(\alpha_k+mh,\ \alpha_k+mh+\mu h)$ 上 $\varphi'=(1-\mu)t$，在 $(\alpha_k+mh+\mu h,\ \alpha_k+(m+1)h)$ 上 $\varphi'=-\mu t$（$m=0,\dots,N-1$）。每个周期上的积分为 0，所以 $\varphi(\alpha_k+mh)=0$，且 $|\varphi|\le\mu(1-\mu)|t|h$。
- $\psi(s)=\min\{1,\ (s-\alpha_{k'})/(\theta\ell_{k'}),\ (\alpha_{k'}+\ell_{k'}-s)/(\theta\ell_{k'})\}$。
- $v(x)=z(x)+\varphi(x_k)\psi(x_{k'})\,e_k$。

于是 $v=z$ 在 $\partial R$ 上成立，并且
$$\nabla v=\underbrace{P+\psi\varphi'\,e_k\otimes e_k}_{D}+\underbrace{\varphi\psi'\,e_k\otimes e_{k'}}_{\omega}.$$

分片情况：
- **$Q$ 矩形：** $[\alpha_k+mh,\ \alpha_k+mh+\mu h]\times[\alpha_{k'}+\theta\ell_{k'},\ \alpha_{k'}+\ell_{k'}-\theta\ell_{k'}]$，共 $N$ 个，在其上 $v$ 仿射且 $\nabla v=P+(1-\mu)(Q-A)=Q$。总面积为 $\mu(1-2\theta)|R|$。
- **$A$ 矩形：** 同理，$\nabla v=P-\mu(Q-A)=A$。总面积为 $(1-\mu)(1-2\theta)|R|$。
- **边界层 $S$：** 即 $x_{k'}$ 距端点小于 $\theta\ell_{k'}$ 的部分，$|S|=2\theta|R|$，分成 $4N$ 个闭矩形，$v$ 在每一块上是多项式。

在 $S$ 上：
- 因为 $\psi\in[0,1]$，$D$ 落在线段 $[Q,A]\subset\operatorname{conv}K$ 上，所以 $|D|\le3$。
- $|\omega|\le\mu(1-\mu)|t|\,h/(\theta\ell_{k'})\le\mu(1-\mu)|t|\le\tfrac34$，这里用到了 $h\le\theta\ell_{k'}$。
- 因此 $|\nabla v|_F^2=|D|^2+|\omega|^2\le 9+\tfrac9{16}$。
- 又 $\operatorname{dist}^2(\nabla v,K)\le|D-A|^2+|\omega|^2\le t^2+\tfrac9{16}<17$。

**递归构造。** 取 $M\ge1$，$\theta\in(0,\tfrac14]$。
1. 令 $u^{(0)}\equiv0$，$\mathcal G_0=\{\Omega\}$。此时梯度为 $P_1$。
2. 对 $n=0,\dots,4M-1$：在每个 $R\in\mathcal G_n$ 上，按步型 I, II, III, IV 循环（步型为 $n\bmod 4$），以 $z=u^{(n)}|_R$ 用 $v_R$ 替换 $u^{(n)}$；在 $\bigcup\mathcal G_n$ 之外保持不变。
3. 令 $\mathcal G_{n+1}$ 为新产生的全部 $Q$ 矩形。$A$ 矩形和 $S$ 片从此冻结，不再修改。
4. 令 $u_M:=u^{(4M)}$。

例如第一步的具体形式为 $u^{(1)}=(0,\ \varphi_1(x_2)\psi_1(x_1))$，其中 $N=\lceil1/\theta\rceil$，$\varphi_1$ 的斜率交替取 $1$ 和 $-3$（所占比例分别为 3/4 和 1/4），$\psi_1(x_1)=\min\{1,x_1/\theta,(1-x_1)/\theta\}$。在条带 $[\theta,1-\theta]\times[\tfrac mN,\tfrac{m+3/4}N]$ 上，$u^{(1)}=(0,\ x_2-\tfrac mN)$，梯度为 $P_4$，下一步就在这些条带内进行。

**验证：**
- **零边界：** 每次替换都在开矩形内进行，且 $v_R=u^{(n)}$ 在 $\partial R$ 上成立。归纳可知 $u_M$ 连续，且 $u_M|_{\partial\Omega}=0$。
- **一致梯度上界：** $\bar\Omega$ 被有限个闭矩形划分，各片上 $u_M$ 是多项式：
  - $A$ 片上 $|\nabla u_M|=|A_i|\le3$；
  - 最终剩余片上 $\nabla u_M=P_1=0$；
  - $S$ 片上 $|\nabla u_M|\le\sqrt{9+9/16}\approx3.09$。

  由引理 B，$u_M\in W^{1,\infty}$，且 ess sup$|\nabla u_M|_F\le3.1<4$，所以 $u_M\in\mathcal A$。
- **能量估计：** 面积满足 $|\bigcup\mathcal G_{n+1}|=\mu_n(1-2\theta)|\bigcup\mathcal G_n|$。
  - 在第 $m$ 个循环内，四个面积之和不超过 $6^{-m}(1+\tfrac34+\tfrac12+\tfrac14)$，所以 $\sum_n|\bigcup\mathcal G_n|\le\tfrac52\cdot\tfrac65=3$，边界层总面积 $\le6\theta$。
  - 最终剩余集的面积为 $6^{-M}(1-2\theta)^{4M}$，其上被积函数为 $\operatorname{dist}^2(0,K)=5$。
  - 在 $A$ 片上被积函数为 0。

  因此
  $$E(u_M)\le5\cdot6^{-M}+17\cdot6\theta .$$
  取 $\theta=6^{-M}/102$，得 $E(u_M)\le6^{1-M}\to0$。

**数值核对：** 我用 Python 实现了这个构造，并以精确有理数运算在随机点上取样。在 $M=2$、$\theta=0.01$ 时，边界值为 0，最大梯度范数约 3.007，能量估计值约 0.26，低于上界 1.16。以 $M=1$ 和 $M=2$ 检查，各类区域的面积与上面的公式一致。

## 3. 任务 1：$e_0=0$，且不被达到

由 $E\ge0$ 和第 2 节，$e_0=0$。

下面证明不可达。假设 $E(u)=0$，则 $\nabla u\in K$ 几乎处处成立。
1. 所有 $A_i$ 的非对角元都为 0，所以 $\partial_2u_1=0$ 几乎处处成立。
2. 由 Rademacher 和 Fubini 定理，对几乎所有 $x_1$，函数 $x_2\mapsto u_1(x_1,x_2)$ 是 Lipschitz 函数且导数几乎处处为 0，因而为常数，等于边界值 $u_1(x_1,0)=0$。由连续性，$u_1\equiv0$。
3. 于是 $\partial_1u_1=0$。在 $K$ 中，$(1,1)$ 元为 0 的只有 $A_4$，所以 $\nabla u=A_4$ 几乎处处成立，从而 $\partial_2u_2=-3$ 几乎处处成立。
4. 同理，由 $\partial_1u_2=0$ 得 $u_2\equiv0$，从而 $\partial_2u_2=0$，矛盾。

所以没有任何 $u\in\mathcal A$ 能达到 $e_0$。

推论：任何极小化序列都没有在 $W^{1,2}$ 中强收敛的子列。否则由 $E$ 关于梯度 $L^2$ 收敛的连续性，极限 $u\in\mathcal A$ 满足 $E(u)=0$，与上面矛盾。

## 4. 任务 2：相分数唯一确定

**定理。** 对任意 $u\in\mathcal A$，有 $\max_i|\pi_i(u)-\lambda^*_i|\le\tfrac54\sqrt{E(u)}$，其中 $\lambda^*=(\tfrac1{10},\tfrac3{10},\tfrac3{10},\tfrac3{10})$。

*证明：*
1. 令 $B(x)=A_{\sigma(x)}$ 为 $x$ 被分配到的井。$\sigma$ 是可测的，并且 $|\nabla u-B|^2=\min_i|\nabla u-A_i|^2$，所以 $\int|\nabla u-B|^2=E(u)$，且 $\sum_i\pi_i=1$。
2. 由引理 A，$\int\partial_1u_1=0$。于是 $\varepsilon_1:=\sum\pi_ia_i=\int(B_{11}-\partial_1u_1)$，由 Cauchy–Schwarz（$|\Omega|=1$）得 $|\varepsilon_1|\le\sqrt E$。同理 $\varepsilon_2:=\sum\pi_ib_i$ 满足 $|\varepsilon_2|\le\sqrt E$。
3. 令 $\varepsilon_3:=\sum\pi_ia_ib_i=\int\det B=\int(\det B-\det\nabla u)$。
   - 有恒等式 $\det F-\det G=\beta(F-G,F+G)$，其中 $\beta(X,Y)=\tfrac12(X_{11}Y_{22}+X_{22}Y_{11}-X_{12}Y_{21}-X_{21}Y_{12})$。
   - 由 Cauchy–Schwarz，$|\beta(X,Y)|\le\tfrac12|X||Y|$。
   - 结合 $|\nabla u|\le4$ 和 $|B|\le3$，得 $|\varepsilon_3|\le\tfrac72\sqrt E$。
4. 这些条件构成一个线性方程组：$3\pi_1+\pi_2-2\pi_3=\varepsilon_1$，$2\pi_2+\pi_3-3\pi_4=\varepsilon_2$，$2\pi_2-2\pi_3=\varepsilon_3$，$\sum\pi_i=1$。系数行列式为 $-60\ne0$，唯一解为
$$\pi_1=\tfrac1{10}+\tfrac{9\varepsilon_1+\varepsilon_2-7\varepsilon_3}{30},\quad \pi_2=\tfrac3{10}+\tfrac{-\varepsilon_1+\varepsilon_2+3\varepsilon_3}{10},\quad \pi_3=\tfrac3{10}+\tfrac{-\varepsilon_1+\varepsilon_2-2\varepsilon_3}{10},\quad \pi_4=\tfrac3{10}+\tfrac{-3\varepsilon_1-7\varepsilon_2+4\varepsilon_3}{30}.$$
5. 代入第 2、3 步的界，四个分量的系数和分别为 $\tfrac{69}{60}$、$\tfrac54$、$\tfrac9{10}$、$\tfrac45$，取最大值即得 $\tfrac54$。∎

因此只要 $E(u_j)\to e_0=0$，整个序列（不只是某个子列）就满足 $\pi(u_j)\to\lambda^*$。

这个极限确实能取到：第 2 节的 $u_M$ 实现了它。直接从构造计算也得到同样的结果：一个循环产出 $A_4,A_3,A_2,A_1$ 的比例为 $\tfrac14,\tfrac14,\tfrac14,\tfrac1{12}$，留下 $\tfrac16$ 回到 $P_1$。乘以 $\tfrac65$ 后正是 $\tfrac3{10},\tfrac3{10},\tfrac3{10},\tfrac1{10}$。

## 5. 对前期论证的修正

- **错误所在：** 两井刚性（Ball–James 型）只排除两个井之间的层合。在 T4 构型中，层合发生在井 $A_i$ 与非井矩阵 $P_{i+1}$ 之间，而不是两个井之间。零矩阵 $0=P_1$ 位于秩一凸包中。Lipschitz 上界也挡不住这种构造，因为构造的梯度范数始终 $\le3.1<4$。所以"单元能有正间隙"应当撤回。
- **仍然成立的部分：** 精确解不存在（第 3 节，理由来自对角结构加零边界，而不是两两相容性）；体积分数是刚性的，由线性约束唯一确定为 $\lambda^*$（第 4 节）。