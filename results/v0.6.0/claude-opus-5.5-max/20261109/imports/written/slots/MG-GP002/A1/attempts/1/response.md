# Fourier 逆、截断误差与参数边界：逐项解答

**结论速览**
- **S1**：$N_\alpha$ 在 $H_N$ 上的逆就是频率逐点除以 $2\pi i(\alpha k_1+k_2)$。对每个实数 $r$，逆在 $H^r\to H^r$ 下的范数都等于 $\big(2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|\big)^{-1}$，与 $r$ 无关。
- **S2、S3**：题中两个不等式都成立，证明见下。
- **S4**：所列目标全部成立。每个 $F\in C_0^\infty$ 都有唯一光滑零均值解，当且仅当 $\alpha$ 是 Diophantine 数（即非 Liouville 的无理数）。损失 $s$ 可用当且仅当 $\inf_{k\ne0}\langle k\rangle^s|\alpha k_1+k_2|>0$，最优常数是这个下确界乘 $2\pi$ 后取倒数，与 $r$ 无关；任何无理 $\alpha$ 都不允许 $s<1$。对 $\alpha_*=\sqrt2-1$：最小损失 $s=1$，并且取到；最优常数是 $1/(2\pi\sin\frac\pi8)$。$C^m$ 估计成立，可取与 $m$ 无关的 $C_m=\cos(\pi/8)/(6\pi^3)$。
- **S5**：不存在这样的 $J,s,C$。
- **S6**：$\alpha$ 无理，并给出一个具体的单一 $F$。它的形式解系数增长快于任何多项式，所以没有光滑解（连 $C^1$ 解或分布解都没有）。

---

## 0. 记号与基本事实

**记号。**
- $e_k(y)=e^{2\pi i k\cdot y}$；小除数 $\lambda_\alpha(k)=\alpha k_1+k_2$；$\|k\|_\infty=\max(|k_1|,|k_2|)$。
- $K_N=\{k\in\mathbb Z^2:0<|k|\le N\}$，$P_NF=\sum_{k\in K_N}\hat F(k)e_k$。
- 对 $k\ne0$：$\|k\|_\infty\le|k|\le\sqrt2\|k\|_\infty$，$\langle k\rangle\le\sqrt3\|k\|_\infty$。
- $\#\{k:\|k\|_\infty=j\}=8j$，所以 $\sum_{k\ne0}\|k\|_\infty^{-3}=8\zeta(2)=4\pi^2/3$。

**基本事实。**
- **(F1)** 若 $u\in C^1(\mathbb T^2)$，则 $\widehat{\partial_ju}(k)=2\pi i k_j\hat u(k)$。理由：用 Fubini 后对 $y_j$ 分部积分，边界项因周期性抵消。于是 $\widehat{N_\alpha u}(k)=2\pi i\lambda_\alpha(k)\hat u(k)$；特别地 $\widehat{N_\alpha u}(0)=0$，所以 $N_\alpha(C^\infty)\subset C^\infty_0$。
- **(F2)** $|\hat u(k)|\le\sup|u|$。
- **(F3)** $\{e_k\}$ 是 $L^2(\mathbb T^2)$ 的标准正交基（标准事实），所以连续函数由其 Fourier 系数唯一决定。
- **(F4)** 称 $(c_k)$ **速降**，若对每个 $m$ 有 $\sup_k\langle k\rangle^m|c_k|<\infty$。因为 $\sum_k\langle k\rangle^{-3}<\infty$，这等价于对每个 $m$ 有 $\sum_k\langle k\rangle^m|c_k|<\infty$。此时：
  - 由 $|\partial^a e_k|\le(2\pi\langle k\rangle)^{|a|}$、Weierstrass 判别法和逐项求导定理，$v=\sum c_ke_k$ 的各阶逐项导数级数都绝对一致收敛；
  - 因而 $v\in C^\infty$，$\partial^a v=\sum c_k(2\pi i k)^a e_k$，且 $\hat v(k)=c_k$。
- **(F5)** 设 $u\in C^n$，$k\ne0$。取 $j$ 使 $|k_j|=\|k\|_\infty$，由 (F1)(F2) 得 $|\hat u(k)|\le(2\pi\|k\|_\infty)^{-n}\|u\|_{C^n}$。因此 $u\in C^\infty$ 时 $\hat u$ 速降，$u=\sum\hat u(k)e_k$ 在每个 $C^m$ 中绝对收敛，并且对一切 $r$ 有 $\|u\|_{H^r}<\infty$。
- **(F6)** 对 $u,F\in C^1$：$N_\alpha u=F\iff 2\pi i\lambda_\alpha(k)\hat u(k)=\hat F(k)$ 对一切 $k$ 成立（由 (F1)(F3)）。
- **(F7)** 若 $\alpha\notin\mathbb Q$ 且 $k\ne0$，则 $\lambda_\alpha(k)\neq0$。理由：$k_1\ne0$ 时否则 $\alpha=-k_2/k_1$；$k_1=0$ 时 $\lambda_\alpha(k)=k_2\ne0$。
- **(F8)** 对 $k\ne0$、$a+b\le m$：$\sup|\partial_1^a\partial_2^b e_k|=(2\pi)^{a+b}|k_1|^a|k_2|^b\le(2\pi\|k\|_\infty)^m$。把全部求导放在较大分量上即取到等号，所以 $\|e_k\|_{C^m}=(2\pi\|k\|_\infty)^m$。

总之，$N_\alpha$ 是符号为 $2\pi i\lambda_\alpha(k)$ 的 Fourier 乘子；以下所有问题都归结为 $|\lambda_\alpha(k)|$ 的大小。

---

## S1 有限频带上的逆

**定理 S1.** 设 $\alpha\notin\mathbb Q$，$N\ge1$。对 $F\in H_N$ 令
$$T_NF=\sum_{k\in K_N}\frac{\hat F(k)}{2\pi i(\alpha k_1+k_2)}\,e_k ,$$
等价地 $T_NF=G_N*F$，其中 $G_N=\sum_{K_N}e_k/(2\pi i\lambda_\alpha(k))$。则 $N_\alpha T_N=T_NN_\alpha=\mathrm{id}_{H_N}$，并且对每个 $r\in\mathbb R$，
$$\|N_\alpha^{-1}\|_{(H_N,H^r)\to(H_N,H^r)}=\max_{0<|k|\le N}\frac{1}{2\pi|\alpha k_1+k_2|}=\frac1{2\pi\delta_N(\alpha)},\qquad \delta_N(\alpha):=\min_{0<|k|\le N}|\alpha k_1+k_2|>0 .$$
这个范数与 $r$ 无关。

*证明.*
1. **可逆性。** $N_\alpha e_k=2\pi i\lambda_\alpha(k)e_k$，所以 $N_\alpha$ 保持 $H_N$，并在基 $\{e_k\}_{k\in K_N}$ 下是对角的。由 (F7)，特征值非零；$T_N$ 是取倒数特征值的对角算子，因此是两侧逆。
2. **范数上界。** 对 $F\in H_N$，
$$\|T_NF\|_{H^r}^2=\sum_{K_N}\frac{\langle k\rangle^{2r}|\hat F(k)|^2}{4\pi^2\lambda_\alpha(k)^2}\le\frac{\|F\|_{H^r}^2}{4\pi^2\delta_N^2}.$$
3. **取到。** $K_N$ 是有限非空集（含 $(1,0)$），设 $k_*$ 为 $|\lambda_\alpha|$ 在 $K_N$ 上的极小点，则 $\delta_N>0$，且 $F=e_{k_*}$ 使上式取等号。∎

在整个 $H^r$ 上，$T_NP_N$ 的范数也是这个值。由 S4 中的 Dirichlet 论证，$\delta_N(\alpha)\to0$，所以这些范数关于 $N$ 无界。

---

## S2 有算术界的截断误差

**定理 S2.** 设 $|\lambda_\alpha(k)|\ge c\langle k\rangle^{-s}$ 对一切 $k\ne0$ 成立，$F\in C_0^\infty$。令
$$u=\sum_{k\ne0}\frac{\hat F(k)}{2\pi i\lambda_\alpha(k)}e_k .$$
则：
- $\alpha\notin\mathbb Q$（若 $\alpha=p/q$，取 $k=(q,-p)$ 会得到 $\lambda_\alpha(k)=0$）；
- $u\in C_0^\infty$，$N_\alpha u=F$，且这样的 $u$ 唯一；
- 对一切 $r\in\mathbb R$、$q\ge0$：
$$\|u-u_N\|_{H^r}\le(2\pi c)^{-1}(1+N^2)^{-q/2}\|F\|_{H^{r+s+q}} .$$

*证明.*
1. **光滑性与方程。** $|\hat u(k)|\le(2\pi c)^{-1}\langle k\rangle^s|\hat F(k)|$。由 (F5)，$\hat F$ 速降，故 $\hat u$ 速降；由 (F4)，$u\in C^\infty$，且 $\hat u(0)=0$，即零均值。又 $2\pi i\lambda_\alpha\hat u=\hat F$ 对 $k\ne0$ 成立，$k=0$ 时两边都为 $0$；由 (F6) 得 $N_\alpha u=F$。
2. **唯一性。** 由 (F6)(F7)：解的非零频系数被唯一确定，零均值又确定 $\hat u(0)=0$。
3. **截断。** 按 S1，$u_N=T_N(P_NF)=\sum_{K_N}\frac{\hat F(k)}{2\pi i\lambda_\alpha(k)}e_k=P_Nu$，所以 $u-u_N=\sum_{|k|>N}\hat u(k)e_k$。
4. **误差估计。** 当 $|k|>N$ 时 $\langle k\rangle^2>1+N^2$，又 $q\ge0$，故 $\langle k\rangle^{-2q}\le(1+N^2)^{-q}$。于是
$$\|u-u_N\|_{H^r}^2=\sum_{|k|>N}\frac{\langle k\rangle^{2r}|\hat F(k)|^2}{4\pi^2\lambda_\alpha(k)^2}\le\frac{1}{4\pi^2c^2}\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}\langle k\rangle^{-2q}|\hat F(k)|^2\le\frac{(1+N^2)^{-q}}{4\pi^2c^2}\|F\|^2_{H^{r+s+q}}.$$
开方即得所求不等式。∎

---

## S3 固定频带内改变方向

**定理 S3.** 设 $|\lambda_\alpha(k)|,|\lambda_\beta(k)|\ge\delta$ 对一切 $k\in K_N$ 成立，$F\in H_N$，$u_\gamma=N_\gamma^{-1}F$（按 S1）。则
$$\|u_\alpha-u_\beta\|_{H^r}\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.$$

*证明.* 由 $\lambda_\beta(k)-\lambda_\alpha(k)=(\beta-\alpha)k_1$，对 $k\in K_N$，
$$\hat u_\alpha(k)-\hat u_\beta(k)=\frac{\hat F(k)}{2\pi i}\Big(\frac1{\lambda_\alpha(k)}-\frac1{\lambda_\beta(k)}\Big)=\frac{(\beta-\alpha)k_1\,\hat F(k)}{2\pi i\,\lambda_\alpha(k)\lambda_\beta(k)} .$$
因为 $|k_1|\le|k|\le N$，$|\lambda_\alpha\lambda_\beta|\ge\delta^2$，所以 $|\hat u_\alpha(k)-\hat u_\beta(k)|\le\frac{|\alpha-\beta|N}{2\pi\delta^2}|\hat F(k)|$。乘以 $\langle k\rangle^{2r}$ 并求和即可。∎

算子形式：$N_\alpha^{-1}-N_\beta^{-1}=(\beta-\alpha)N_\alpha^{-1}\partial_1N_\beta^{-1}$，其中在 $H_N$ 上 $\|\partial_1\|\le2\pi N$，且由 S1 有 $\|N_\gamma^{-1}\|\le(2\pi\delta)^{-1}$；结果相同。

---

## S4 整体理论

**定义.**
- $\sigma_s(\alpha):=\inf_{k\ne0}\langle k\rangle^s|\lambda_\alpha(k)|$，$S_\alpha:=\{s\ge0:\sigma_s(\alpha)>0\}$。
- 称 $\alpha$ 为 **Diophantine**，若 $S_\alpha\neq\emptyset$，即存在 $c>0,s\ge0$ 使 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 对一切 $k\ne0$ 成立。这等价于经典条件 $|q\alpha-p|\ge c'|q|^{-s}$（$q\ne0$）：当 $|q\alpha-p|<1$ 时 $\langle (q,-p)\rangle\le(2+|\alpha|)|q|$。
- 无理但非 Diophantine 的数称为 **Liouville** 数。

### 定理 4.1（唯一性）

- 若 $\alpha\notin\mathbb Q$，则 $N_\alpha$ 在零均值 $C^1$ 函数上是单射：由 $N_\alpha u=0$ 得 $\lambda_\alpha(k)\hat u(k)=0$，再由 (F7)(F3) 得 $u=0$。
- 若 $\alpha=p/q$，取 $k_0=(q,-p)$，则 $N_\alpha e_{k_0}=0$（唯一性失败），并且 $e_{k_0}$ 不在像中，因为 $\widehat{N_\alpha u}(k_0)=0\neq1$（存在性失败）。

### 定理 4.2（最优常数；容许损失的完全刻画）

设 $\alpha\notin\mathbb Q$，$s\ge0$，$r\in\mathbb R$。则
$$\sup_{0\ne u\in C^\infty_0}\frac{\|u\|_{H^r}}{\|N_\alpha u\|_{H^{r+s}}}=\frac1{2\pi\sigma_s(\alpha)}\in(0,\infty].$$
由此得到：
1. 估计对某一个 $r$ 成立 $\iff$ 对一切 $r$ 成立 $\iff$ $\sigma_s(\alpha)>0$。最优常数 $C_{\alpha,r,s}=(2\pi\sigma_s(\alpha))^{-1}$ 与 $r$ 无关。所以**全部容许的 $s$ 恰为 $S_\alpha$**。
2. $S_\alpha$ 向上封闭，因为 $\langle k\rangle\ge1$。
3. $S_\alpha\subset[1,\infty)$ 对一切无理 $\alpha$ 成立。
4. 令 $s_0(\alpha):=\limsup_{|k|\to\infty}\frac{\log(1/|\lambda_\alpha(k)|)}{\log\langle k\rangle}\in[1,\infty]$，则 $(s_0,\infty)\subset S_\alpha\subset[s_0,\infty)$。因此 $S_\alpha$ 是 $\emptyset$（$s_0=\infty$，即 Liouville）、$[s_0,\infty)$ 或 $(s_0,\infty)$ 之一。端点是否属于 $S_\alpha$，正是 $\sigma_{s_0}(\alpha)>0$ 是否成立。

*证明.*
- **最优常数。** 由 (F5)，两边范数都有限；由定理 4.1，$u\neq0$ 时 $N_\alpha u\ne0$，比值有定义。直接计算
$$\|N_\alpha u\|^2_{H^{r+s}}=\sum_{k\ne0}4\pi^2\langle k\rangle^{2s}\lambda_\alpha(k)^2\langle k\rangle^{2r}|\hat u(k)|^2\ge4\pi^2\sigma_s^2\|u\|_{H^r}^2 .$$
反过来，取 $u=e_k$ 得比值 $(2\pi\langle k\rangle^s|\lambda_\alpha(k)|)^{-1}$，再对 $k$ 取上确界。
- **(3) Dirichlet 论证。** 对整数 $Q\ge1$，$Q+1$ 个点 $\{j\alpha\}$（$0\le j\le Q$）落在 $Q$ 个长 $1/Q$ 的区间中，必有两点同区间。于是存在 $1\le q\le Q$ 和整数 $p$ 使 $|q\alpha-p|<1/Q$。令 $k_Q=(q,-p)$，则 $|p|<q|\alpha|+1$，$\langle k_Q\rangle\le(2+|\alpha|)Q$，从而
$$\sigma_s\le(2+|\alpha|)^sQ^{s-1}\to0\qquad(s<1).$$
同时 $|\lambda_\alpha(k_Q)|\to0$，故 $|k_Q|\to\infty$，并且 $\frac{\log(1/|\lambda|)}{\log\langle k_Q\rangle}\ge\frac{\log Q}{\log Q+\log(2+|\alpha|)}\to1$，所以 $s_0\ge1$。
- **(4)。**
  - 若 $s>s_0$：除有限个 $k$ 外 $\langle k\rangle^s|\lambda_\alpha(k)|\ge1$；剩下的有限个值都为正，故 $\sigma_s>0$。
  - 若 $s<s'<s_0$：存在无穷多 $k$ 满足 $\langle k\rangle^s|\lambda_\alpha(k)|<\langle k\rangle^{s-s'}\to0$，故 $\sigma_s=0$。∎

*附注（标准事实，不参与上面的证明）：* $s_0(\alpha)=\mu(\alpha)-1$，$\mu$ 为无理性指数。端点两种情形都会出现：$\alpha_*$ 属于端点在内的情形（见定理 4.4）；由 Khintchine 定理，几乎处处的 $\alpha$ 满足 $s_0=1\notin S_\alpha$。

### 定理 4.3（可解性刻画）

设 $\alpha\notin\mathbb Q$。以下三条等价：
- (a) 每个 $F\in C_0^\infty$ 都有（必然唯一的）解 $u\in C^\infty_0$ 使 $N_\alpha u=F$；
- (b) $\alpha$ 是 Diophantine 数；
- (c) 存在 $s\ge0$ 和 $C<\infty$，使 $\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}$ 对一切 $u\in C_0^\infty$ 成立。

此时 $N_\alpha^{-1}F=\sum_{k\ne0}\frac{\hat F(k)}{2\pi i\lambda_\alpha(k)}e_k$，并且对 $s\in S_\alpha$ 与一切 $r$，$\|N_\alpha^{-1}F\|_{H^r}\le(2\pi\sigma_s)^{-1}\|F\|_{H^{r+s}}$。所以 $N_\alpha:C^\infty_0\to C^\infty_0$ 是拓扑同构（Fréchet 拓扑）。

结合定理 4.1，在全体实数 $\alpha$ 中，满足 (a) 的恰好是 Diophantine 无理数。

*证明.*
- **(b)⇒(a)：** 即 S2，取 $c=\sigma_s(\alpha)$。
- **(b)⇔(c)：** 定理 4.2 取 $r=0$。
- **(a)⇒(b)，用逆否命题。** 设对一切 $n\in\mathbb N$ 有 $\sigma_n(\alpha)=0$。
  1. 归纳选取 $k^{(n)}\ne0$，使 $|k^{(n)}|>|k^{(n-1)}|$ 且 $\langle k^{(n)}\rangle^n|\lambda_\alpha(k^{(n)})|<1$。这是可以做到的：在有限集 $\{0<|k|\le|k^{(n-1)}|\}$ 上 $\langle k\rangle^n|\lambda_\alpha|$ 的最小值 $m_n>0$；由 $\sigma_n=0$，存在 $k$ 使该值 $<\min(1,m_n)$，这样的 $k$ 必满足 $|k|>|k^{(n-1)}|$。
  2. 令 $F=\sum_n\langle k^{(n)}\rangle^{-n/2}e_{k^{(n)}}$。对固定 $m$，当 $n\ge2m$ 时 $\langle k^{(n)}\rangle^{m-n/2}\le1$，所以系数速降。由 (F4)，$F\in C^\infty_0$。
  3. 若某个 $u\in C^1$ 满足 $N_\alpha u=F$，则
$$|\hat u(k^{(n)})|=\frac{\langle k^{(n)}\rangle^{-n/2}}{2\pi|\lambda_\alpha(k^{(n)})|}>\frac{\langle k^{(n)}\rangle^{n/2}}{2\pi}\ge\frac{2^{n/4}}{2\pi}\to\infty,$$
  与 (F2) 矛盾。∎

正则性（全局亚椭圆性）：若 $\alpha$ 为 Diophantine，$u\in L^2$ 且 $N_\alpha u\in C^\infty$（分布意义），则同样由 $|\hat u(k)|\le\langle k\rangle^s|\widehat{N_\alpha u}(k)|/(2\pi\sigma_s)$ 得到 $u\in C^\infty$。

### 定理 4.4（$\alpha_*=\sqrt2-1$：最小损失 $s=1$，并且取到）

记 $\lambda=\lambda_{\alpha_*}$，$M(k)=k_2-(1+\sqrt2)k_1$，$\nu(k)=k_2^2-2k_1k_2-k_1^2$。

1. **范数恒等式。** 展开得 $\lambda M=\nu\in\mathbb Z$。又 $\nu=(k_2-k_1)^2-2k_1^2$，由 $\sqrt2\notin\mathbb Q$，$k\ne0$ 时 $\nu\ne0$，所以 $|\nu|\ge1$。
2. **正交分解。** $(\alpha_*,1)\cdot(-(1+\sqrt2),1)=-(\sqrt2-1)(\sqrt2+1)+1=0$，两向量的模平方分别为 $4-2\sqrt2$ 和 $4+2\sqrt2$。故
$$|k|^2=\frac{\lambda^2}{4-2\sqrt2}+\frac{M^2}{4+2\sqrt2}.$$
3. **下界。** 将上式乘以 $\lambda^2$ 并用 (1)：
$$\langle k\rangle^2\lambda^2=\lambda^2+\frac{\lambda^4}{4-2\sqrt2}+\frac{\nu^2}{4+2\sqrt2}>\frac1{4+2\sqrt2}=\frac{2-\sqrt2}{4}=\sin^2\tfrac\pi8 .$$
同理 $|k|\,|\lambda(k)|\ge\sin\frac\pi8$ 对一切 $k\ne0$ 成立。
4. **Pell 向量取到下确界。** 令 $P_0=0$，$P_1=1$，$P_{n+1}=2P_n+P_{n-1}$，$k^{(n)}=(P_n,-P_{n-1})$。
   - 由 $\alpha_*^2=1-2\alpha_*$ 归纳得 $\lambda(k^{(n+1)})=-\alpha_*\lambda(k^{(n)})$，所以 $|\lambda(k^{(n)})|=\alpha_*^n\to0$。
   - 记 $a=k_2-k_1$，$b=k_1$，则 $\lambda=a+b\sqrt2$，$M=a-b\sqrt2$ 是它的共轭。所以 $M(k^{(n)})=\pm(-1-\sqrt2)^n$，$\nu(k^{(n)})=(-1)^n$。
   - 代入 (3)：$\langle k^{(n)}\rangle|\lambda(k^{(n)})|\downarrow\sin\frac\pi8$，且由 (2)，$\langle k^{(n)}\rangle\to\infty$。

**结论.**
- $\sigma_1(\alpha_*)=\sin\frac\pi8$（下确界不被任何单个 $k$ 取到）。
- 对 $s<1$：$\langle k^{(n)}\rangle^s|\lambda(k^{(n)})|=\langle k^{(n)}\rangle^{s-1}\cdot\langle k^{(n)}\rangle|\lambda(k^{(n)})|\to0$。所以 $S_{\alpha_*}=[1,\infty)$：**最小允许损失是 $s=1$，并且取到**。
- 对每个 $r$，$s=1$ 时的最优常数是
$$C_{\alpha_*,r,1}=\frac1{2\pi\sin(\pi/8)}=\frac{\sqrt{4+2\sqrt2}}{2\pi}\approx0.4159,$$
并且对 $u\ne0$ 不等式严格成立。

### 定理 4.5（$C^m$ 估计：成立）

对一切 $m\in\mathbb N_0$ 和 $F\in C^\infty_0$，
$$\|N_{\alpha_*}^{-1}F\|_{C^m}\le\frac{\cos(\pi/8)}{6\pi^3}\,\|F\|_{C^{m+4}},$$
即可取与 $m$ 无关的 $C_m=\cos(\pi/8)/(6\pi^3)\approx4.97\times10^{-3}$。

*证明.* 令 $u=N^{-1}_{\alpha_*}F$。
1. 由定理 4.4，$|\lambda(k)|^{-1}\le|k|/\sin\frac\pi8\le\sqrt2\|k\|_\infty/\sin\frac\pi8$。
2. 由 (F5) 取 $n=m+4$：$|\hat F(k)|\le(2\pi\|k\|_\infty)^{-m-4}\|F\|_{C^{m+4}}$。
3. 由 (F4)(F8)，对 $a+b\le m$，
$$\sup|\partial_1^a\partial_2^bu|\le\sum_{k\ne0}(2\pi\|k\|_\infty)^m\frac{\sqrt2\|k\|_\infty}{2\pi\sin\frac\pi8}\cdot\frac{\|F\|_{C^{m+4}}}{(2\pi\|k\|_\infty)^{m+4}}=\frac{\sqrt2\,\|F\|_{C^{m+4}}}{(2\pi)^5\sin\frac\pi8}\sum_{k\ne0}\|k\|_\infty^{-3}.$$
4. 代入 $\sum_{k\ne0}\|k\|_\infty^{-3}=\frac{4\pi^2}3$，并用 $\frac{\sqrt2}{\sin(\pi/8)}=4\cos\frac\pi8$，常数化简为 $\frac{\cos(\pi/8)}{6\pi^3}$。∎

两点补充：
- 用 Cauchy–Schwarz 和 Parseval，其实 $C^{m+3}$ 就够。
- 至少要损失一阶导数：取 $F=e_{k^{(n)}}$，比值 $\|N^{-1}F\|_{C^m}/\|F\|_{C^m}=1/(2\pi\alpha_*^n)\to\infty$。

---

## S5 邻近方向的一致估计：不存在

假设存在这样的 $J,s,C$，推出矛盾：
1. 在 $J$ 中取有理数 $p/q$（$q\ge1$），并取 $\eta>0$ 使 $(p/q-\eta,p/q+\eta)\subset J$。
2. 对整数 $M>\sqrt2/\eta$，令 $\alpha_M=p/q+\sqrt2/M\in J\setminus\mathbb Q$。
3. 取 $k=(q,-p)$，$u=e_k\in C_0^\infty$。则 $\|u\|_{L^2}=1$，而
$$C\|N_{\alpha_M}u\|_{H^s}=2\pi C|q\alpha_M-p|\langle k\rangle^s=\frac{2\sqrt2\,\pi Cq\langle k\rangle^s}{M}\to0 .$$
4. 当 $M$ 足够大时，不等式 $\|u\|_{L^2}\le C\|N_{\alpha_M}u\|_{H^s}$ 不成立，矛盾。

等价说法：由定理 4.2，对每个 $s$ 都有 $\sup_{\alpha\in J\setminus\mathbb Q}(2\pi\sigma_s(\alpha))^{-1}=\infty$。

几点说明：
- 每个 $\alpha_M$ 自身都满足 $s=1$ 的估计。因为 $(\alpha_Mk_1+k_2)(\bar\alpha_Mk_1+k_2)\in\frac1{q^2M^2}\mathbb Z\setminus\{0\}$，可推出 $|\lambda_{\alpha_M}(k)|\ge c_M/|k|$。所以失败完全来自常数不一致。
- 这正是 S3 的反面：当 $\alpha\to p/q$ 时，$\delta_N(\alpha)\to0$。
- 一致估计在闭集 $\{\alpha:\sigma_s(\alpha)\ge c\}$ 上成立（常数为 $(2\pi c)^{-1}$），但这个集合会错开每个有理数的一个邻域，所以不包含任何区间。

---

## S6 $\alpha=\sum_{n\ge1}10^{-n!}$ 与一个不可解的 $F$

**有理逼近。** 令 $q_n=10^{n!}$，$p_n=\sum_{j\le n}10^{n!-j!}\in\mathbb N$，$\epsilon_n=q_n\alpha-p_n=\sum_{j>n}10^{n!-j!}$。指数 $j!-n!$（$j>n$）是严格递增的整数，且都 $\ge n\cdot n!$，所以
$$q_n^{-n}\le\epsilon_n\le\tfrac{10}9q_n^{-n}.$$

**$\alpha$ 无理。** 若 $\alpha=a/b$（$b\in\mathbb N$），则 $b\epsilon_n=aq_n-bp_n$ 是正整数，故 $\ge1$；但 $b\epsilon_n\le\frac{10b}{9}q_n^{-n}\to0$，矛盾。

**频率。**
- 由 $0<\alpha<1/9$ 得 $1\le p_n<q_n$。
- 令 $k^{(n)}=(q_n,-p_n)$。这些向量两两不同（第一分量严格递增）且非零。
- $\lambda_\alpha(k^{(n)})=\epsilon_n$，$\langle k^{(n)}\rangle^2<3q_n^2$。
- 顺便：$\sigma_s(\alpha)\le\frac{10}{9}3^{s/2}q_n^{s-n}\to0$，所以 $S_\alpha=\emptyset$（$\alpha$ 是 Liouville 数）。

**单一的 $F$：**
$$F(y)=\sum_{n\ge1}10^{-n\cdot n!/2}\,e^{2\pi i(q_ny_1-p_ny_2)}=\sum_n q_n^{-n/2}e_{k^{(n)}} .$$

- **光滑且零均值。** $\sum_n\langle k^{(n)}\rangle^mq_n^{-n/2}\le3^{m/2}\sum_nq_n^{m-n/2}<\infty$，因为 $n\ge2m+2$ 时每项 $\le10^{-n!}$。由 (F4)，$F\in C^\infty$，$\hat F(k^{(n)})=q_n^{-n/2}$，其余系数为 $0$，特别是 $\hat F(0)=0$。
- **无解。** 若某个 $u\in C^1$（任意均值）满足 $N_\alpha u=F$，由 (F1)，$2\pi i\epsilon_n\hat u(k^{(n)})=q_n^{-n/2}$，从而
$$|\hat u(k^{(n)})|=\frac{q_n^{-n/2}}{2\pi\epsilon_n}\ge\frac9{20\pi}q_n^{n/2}\to\infty,$$
与 (F2) 矛盾。所以 $N_\alpha u=F$ 没有光滑零均值解。∎

这同一个 $F$ 同时排除了所有估计；把它的实部取作数据也可以，因为 $\lambda(-k)=-\lambda(k)$。此外，形式解的系数增长快于任何多项式（$\ge c(\langle k^{(n)}\rangle/\sqrt3)^{n/2}$），所以连分布解也不存在。