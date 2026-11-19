# Fourier 逆、截断误差与参数边界：逐项解答

**结论速览**
- S1：有限频带上的逆按频率逐项相除得到；其 $H^r\to H^r$ 范数等于 $1/(2\pi\delta_N(\alpha))$，与 $r$ 无关。
- S2、S3：所要求的不等式都成立，证明见下文。
- S4：所列目标全部成立。唯一光滑可解当且仅当 $\alpha$ 是 Diophantine 数（等价地，不是 Liouville 数）。对 $\alpha_*=\sqrt2-1$，最小允许损失 $s=1$，并且取到。$C^m$ 估计成立，实际上只需 $C^{m+3}$。
- S5：这样的区间、$s$ 和 $C$ 不存在。
- S6：$\alpha$ 是无理数，并且可以写出一个固定的光滑零均值 $F$，使方程无光滑零均值解，也无任何分布解。

## 记号与预备事实

记 $e_k(y)=e^{2\pi i k\cdot y}$，$\lambda_\alpha(k)=\alpha k_1+k_2$。

- **(P1) 导数的 Fourier 系数。** 对 $u\in C^\infty(\mathbb T^2)$，在环面上分部积分没有边界项，所以 $\widehat{\partial_j u}(k)=2\pi i k_j\hat u(k)$。因此
 $$\widehat{N_\alpha u}(k)=2\pi i\lambda_\alpha(k)\hat u(k).$$
 特别地 $\widehat{N_\alpha u}(0)=0$，所以 $N_\alpha$ 把 $C^\infty$ 映入 $C^\infty_0$。
- **(P2) 光滑函数的系数速降。** 若 $u\in C^\infty$，则对每个 $M$ 有 $\sup_k\langle k\rangle^M|\hat u(k)|<\infty$。理由：把 (P1) 用于 $(1-\Delta/4\pi^2)^j u$，其系数为 $\langle k\rangle^{2j}\hat u(k)$，而该系数的绝对值不超过这个函数的上确界。
- **(P3) 一个求和常数。** 令 $Z:=\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}$。由 $(1+a+b)^2\ge(1+a)(1+b)$ 得
 $$Z\le\Big(\sum_{n\in\mathbb Z}\frac1{1+n^2}\Big)^2\le\Big(1+\frac{\pi^2}3\Big)^2.$$
 若 $(a_k)$ 速降，则对每个 $m$ 有 $\sum_k\langle k\rangle^m|a_k|\le Z\sup_k\langle k\rangle^{m+4}|a_k|<\infty$。于是 $\sum_k a_ke_k$ 连同各阶逐项导数都绝对且一致收敛，定义出一个 $v\in C^\infty$，满足 $\hat v=a$。
- **(P4) Parseval 与唯一性。** $\|u\|_{L^2}^2=\sum_k|\hat u(k)|^2$。若连续函数的全部 Fourier 系数为零，则它恒为零。
- **(P5) 系数的平凡上界。** $|\hat u(k)|\le\|u\|_{L^1}\le\|u\|_{C^0}$。
- **(P6) 小除数不为零。** 若 $\alpha\notin\mathbb Q$ 且 $k\ne0$，则 $\lambda_\alpha(k)\neq0$。若 $k_1\ne0$，否则会有 $\alpha=-k_2/k_1\in\mathbb Q$；若 $k_1=0$，则 $\lambda_\alpha(k)=k_2\neq0$。
- **(P7) 范数比较。** 对 $j\in\mathbb N_0$ 有 $\|F\|_{H^j}\le 3^{j/2}\|F\|_{C^j}$。理由：展开
 $$\langle k\rangle^{2j}=\sum_{a+b+c=j}\frac{j!}{a!b!c!}k_1^{2a}k_2^{2b},$$
 再用 (P1)、(P4) 得
 $$\|F\|_{H^j}^2=\sum_{a+b+c=j}\frac{j!}{a!b!c!}(2\pi)^{-2(a+b)}\|\partial_1^a\partial_2^bF\|_{L^2}^2\le 3^j\|F\|_{C^j}^2.$$
 最后一步用到 $\|g\|_{L^2}\le\sup|g|$（概率测度）。

**引理 D（Dirichlet）。** 设 $\alpha\notin\mathbb Q$。存在无穷多个 $k=(q,-p)$，其中 $q\to\infty$，使 $|\lambda_\alpha(k)|<1/q$，且 $\langle k\rangle\le(|\alpha|+2)q$。因此对每个 $s<1$，有 $\inf_{k\ne0}\langle k\rangle^s|\lambda_\alpha(k)|=0$。

*证明。*
1. 对整数 $Q\ge1$，把 $\{j\alpha\}$（$j=0,\dots,Q$）这 $Q+1$ 个点放进 $Q$ 个区间 $[i/Q,(i+1)/Q)$。由抽屉原理，存在 $1\le q\le Q$ 和 $p\in\mathbb Z$，使 $|q\alpha-p|<1/Q\le1/q$。
2. 这样得到的 $q$ 无界。否则设 $q\le B$，则 $|q\alpha-p|\ge\min_{1\le q\le B}\operatorname{dist}(q\alpha,\mathbb Z)>0$，与 $|q\alpha-p|<1/Q\to0$ 矛盾。
3. 由 $|p|\le|\alpha|q+1$ 得 $\langle k\rangle^2\le 1+q^2+(|\alpha|q+1)^2\le(|\alpha|+2)^2q^2$。
4. 于是 $\langle k\rangle^s|\lambda_\alpha(k)|<(|\alpha|+2)^sq^{s-1}\to0$。∎

**引理 L（大频率）。** 设 $\alpha\notin\mathbb Q$ 且不满足条件
$$(\mathrm D)\qquad \exists\,c>0,\ s\ge0:\ |\lambda_\alpha(k)|\ge c\langle k\rangle^{-s}\quad(\forall k\ne0).$$
则对任意 $\tau\ge0$、$R\ge0$，存在 $k$，满足 $|k|>R$ 且 $0<|\lambda_\alpha(k)|<\langle k\rangle^{-\tau}$。

*证明。* 令 $m_R=\min_{0<|k|\le R}|\lambda_\alpha(k)|$。这是有限集上的最小值，由 (P6) 知 $m_R>0$（若该集为空，取 $m_R=1$）。由于 (D) 对 $c=\min(1,m_R)$、$s=\tau$ 不成立，存在 $k\neq0$，使 $|\lambda_\alpha(k)|<c\langle k\rangle^{-\tau}$。这个 $k$ 同时满足 $|\lambda_\alpha(k)|<\langle k\rangle^{-\tau}$ 和 $|\lambda_\alpha(k)|<m_R$，后者推出 $|k|>R$。∎

---

## S1 有限频带上的逆

令 $\Lambda_N=\{k\in\mathbb Z^2:0<|k|\le N\}$，$H_N=\operatorname{span}\{e_k:k\in\Lambda_N\}$，这是有限维空间。

1. $N_\alpha e_k=2\pi i\lambda_\alpha(k)e_k$，所以 $N_\alpha$ 把 $H_N$ 映入自身，并且在正交基 $\{e_k\}$ 下是对角的。
2. 令
 $$\delta_N(\alpha):=\min_{k\in\Lambda_N}|\alpha k_1+k_2|.$$
 由 (P6) 知 $\delta_N(\alpha)>0$；取 $k=(0,1)$ 知 $\delta_N(\alpha)\le1$。
3. **逆的构造。** 对 $F\in H_N$，定义
 $$N_\alpha^{-1}F=\sum_{k\in\Lambda_N}\frac{\hat F(k)}{2\pi i(\alpha k_1+k_2)}\,e_k .$$
 直接验证 $N_\alpha N_\alpha^{-1}=\mathrm{id}_{H_N}$ 且 $N_\alpha^{-1}N_\alpha=\mathrm{id}_{H_N}$。
4. **上界。** 对任意 $r\in\mathbb R$，
 $$\|N_\alpha^{-1}F\|_{H^r}^2=\sum_{k\in\Lambda_N}\frac{\langle k\rangle^{2r}|\hat F(k)|^2}{4\pi^2\lambda_\alpha(k)^2}\le\frac{\|F\|_{H^r}^2}{(2\pi\delta_N)^2}.$$
5. **取到。** 若 $k^*$ 达到最小值，则 $F=e_{k^*}$ 使第 4 步的不等式取等号。

因此，对一切 $r\in\mathbb R$，
$$\boxed{\ \|N_\alpha^{-1}\|_{(H_N,\|\cdot\|_{H^r})\to(H_N,\|\cdot\|_{H^r})}=\frac{1}{2\pi\,\min_{0<|k|\le N}|\alpha k_1+k_2|}\ }$$
这个值与 $r$ 无关。

注：由引理 D，$\delta_N\to0$，所以当 $N\to\infty$ 时该范数趋于 $\infty$。

## S2 有算术界的截断误差

**$\alpha$ 是无理数。** 若 $\alpha=p/q$，取 $k=(q,-p)$ 得 $\lambda_\alpha(k)=0$，与假设 $|\lambda_\alpha(k)|\ge c\langle k\rangle^{-s}>0$ 矛盾。

**构造光滑解。** 令 $F_N=\sum_{k\in\Lambda_N}\hat F(k)e_k$，$u_N=N_\alpha^{-1}F_N$（S1），并定义
$$u=\sum_{k\ne0}\frac{\hat F(k)}{2\pi i\lambda_\alpha(k)}e_k .$$
- 由假设，$|\hat u(k)|\le(2\pi c)^{-1}\langle k\rangle^s|\hat F(k)|$。由 (P2)，$\hat F$ 速降，所以 $\hat u$ 也速降，由 (P3) 得 $u\in C^\infty$。
- $\hat u(0)=0$，所以 $u$ 零均值。
- 由 (P1)，$\widehat{N_\alpha u}(k)=\hat F(k)$ 对一切 $k$ 成立（$k=0$ 时两边都是 $0$），再由 (P4) 得 $N_\alpha u=F$。
- 唯一性见 S4 定理 A。

**截断误差估计。** $u-u_N$ 只含频率 $|k|>N$。对这些 $k$ 有 $\langle k\rangle^2=1+|k|^2>1+N^2$，所以当 $q\ge0$ 时 $\langle k\rangle^{-2q}\le(1+N^2)^{-q}$。于是
$$\|u-u_N\|_{H^r}^2=\sum_{|k|>N}\frac{\langle k\rangle^{2r}|\hat F(k)|^2}{4\pi^2\lambda_\alpha(k)^2}\le\frac{1}{(2\pi c)^2}\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}\langle k\rangle^{-2q}|\hat F(k)|^2\le\frac{(1+N^2)^{-q}}{(2\pi c)^2}\|F\|_{H^{r+s+q}}^2 .$$
开方即得
$$\|u-u_N\|_{H^r}\le(2\pi c)^{-1}(1+N^2)^{-q/2}\|F\|_{H^{r+s+q}}.$$

## S3 固定频带内改变方向

假设：对一切 $k\in\Lambda_N$，$|\lambda_\alpha(k)|\ge\delta$ 且 $|\lambda_\beta(k)|\ge\delta$。

1. 对 $F\in H_N$ 和 $k\in\Lambda_N$，
 $$\hat u_\alpha(k)-\hat u_\beta(k)=\frac{\hat F(k)}{2\pi i}\Big(\frac1{\lambda_\alpha(k)}-\frac1{\lambda_\beta(k)}\Big)=\frac{\hat F(k)}{2\pi i}\cdot\frac{(\beta-\alpha)k_1}{\lambda_\alpha(k)\lambda_\beta(k)}.$$
2. 由 $|k_1|\le|k|\le N$ 得 $|\hat u_\alpha(k)-\hat u_\beta(k)|\le\dfrac{|\alpha-\beta|N}{2\pi\delta^2}|\hat F(k)|$。
3. 乘以 $\langle k\rangle^{2r}$ 后对 $k$ 求和，得
 $$\|u_\alpha-u_\beta\|_{H^r}\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.$$

## S4 整体理论

**判定：所列目标全部成立。**

### 定理 A（唯一可解性的刻画）

设 $\alpha\notin\mathbb Q$。

1. $N_\alpha:C^\infty_0\to C^\infty_0$ 恒为单射。
2. 下列条件等价：
 - (i) 每个 $F\in C^\infty_0$ 都有唯一的光滑零均值解；
 - (ii) $N_\alpha$ 在 $C^\infty_0$ 上是满射；
 - (iii) $\alpha$ 满足 (D)，即 $\alpha$ 是 Diophantine 数；
 - (iv) $\alpha$ 不是 Liouville 数。这里 Liouville 数指：对每个 $n$，都存在 $p\in\mathbb Z$、$q\ge2$，使 $0<|\alpha-p/q|<q^{-n}$。

*单射。* 若 $N_\alpha u=0$，则 $\lambda_\alpha(k)\hat u(k)=0$。由 (P6)，$\hat u(k)=0$ 对 $k\ne0$ 成立；零均值给出 $\hat u(0)=0$。由 (P4)，$u=0$。

*(iii)⇒(i)。* 用 S2 的构造即可，所用常数就是 (D) 中的 $c,s$。

*(i)⇒(ii)。* 显然。

*(ii)⇒(iii)。* 设 (D) 不成立。
1. 由引理 L 归纳选取 $k^{(j)}$（$j\ge1$），使 $|k^{(j)}|>|k^{(j-1)}|$ 且 $0<|\lambda_\alpha(k^{(j)})|<\langle k^{(j)}\rangle^{-j}$。这些 $k^{(j)}$ 两两不同且非零。
2. 令 $F=\sum_j\langle k^{(j)}\rangle^{-j/2}e_{k^{(j)}}$。当 $j\ge2M$ 时 $\langle k^{(j)}\rangle^{M}\langle k^{(j)}\rangle^{-j/2}\le1$，所以系数速降。由 (P3)，$F\in C^\infty_0$。
3. 若 $u\in C^\infty_0$ 满足 $N_\alpha u=F$，由 (P1) 得
 $$|\hat u(k^{(j)})|=\frac{\langle k^{(j)}\rangle^{-j/2}}{2\pi|\lambda_\alpha(k^{(j)})|}>\frac{\langle k^{(j)}\rangle^{j/2}}{2\pi}\ge\frac{2^{j/4}}{2\pi}\to\infty,$$
 这与 (P5) 矛盾。

*非(iv)⇒非(iii)。* 设 $\alpha$ 是 Liouville 数，任给 $c>0$、$s\ge0$。
1. 取 $n$ 使 $2^{\,n-1-s}>(|\alpha|+2)^s/c$。
2. 取 $p$、$q\ge2$，使 $0<|\alpha-p/q|<q^{-n}$，令 $k=(q,-p)$。则 $|\lambda_\alpha(k)|<q^{1-n}$，且（同引理 D 的第 3 步）$\langle k\rangle\le(|\alpha|+2)q$。
3. 于是
 $$|\lambda_\alpha(k)|<q^{-s}\,2^{-(n-1-s)}<c(|\alpha|+2)^{-s}q^{-s}\le c\langle k\rangle^{-s}.$$
 所以 (D) 不成立。

*非(iii)⇒非(iv)。* 给定 $n$。
1. 取 $R=(1+(|\alpha|+1)^2)^{1/2}$，由引理 L 得 $k$，满足 $|k|>R$ 且 $0<|\lambda_\alpha(k)|<\langle k\rangle^{-(n+1)}$。
2. 若 $k_1=0$，则 $|\lambda_\alpha(k)|=|k_2|\ge1$，不可能。必要时把 $k$ 换成 $-k$，可设 $k_1>0$。
3. 令 $q=k_1$，$p=-k_2$。若 $q=1$，则 $|\alpha-p|<1$，于是 $|k|^2<1+(|\alpha|+1)^2=R^2$，矛盾。所以 $q\ge2$。
4. 于是 $0<|\alpha-p/q|<\langle k\rangle^{-(n+1)}/q\le q^{-n}$，即 $\alpha$ 是 Liouville 数。∎

（补充：若 $\alpha=p/q$ 是有理数，则 $e_{(q,-p)}\in\ker N_\alpha$，唯一性已经失败。）

### 定理 B（允许损失 $s$ 的完全分类）

设 $\alpha\notin\mathbb Q$，$s\ge0$，令 $\kappa_s(\alpha):=\inf_{k\ne0}\langle k\rangle^s|\alpha k_1+k_2|$。下列三条等价：
- (a) 对每个 $r$，都存在常数 $C_{\alpha,r,s}$ 使所述不等式成立；
- (b) 对某一个 $r$，存在这样的常数；
- (c) $\kappa_s(\alpha)>0$。

并且最优常数为 $C_{\alpha,r,s}=1/(2\pi\kappa_s)$，与 $r$ 无关。

*(c)⇒(a)。* 由 Parseval 及 $\hat u(0)=0$，
$$\|N_\alpha u\|_{H^{r+s}}^2=\sum_{k\ne0}\langle k\rangle^{2r+2s}4\pi^2\lambda_\alpha(k)^2|\hat u(k)|^2\ge(2\pi\kappa_s)^2\|u\|_{H^r}^2 .$$

*(b)⇒(c)。* 取 $u=e_k$ 代入，得 $\langle k\rangle^r\le C\cdot2\pi|\lambda_\alpha(k)|\langle k\rangle^{r+s}$，即 $\langle k\rangle^s|\lambda_\alpha(k)|\ge1/(2\pi C)$ 对一切 $k\ne0$ 成立。同一计算也说明常数 $1/(2\pi\kappa_s)$ 是最优的。∎

**允许集合的结构。** 全部允许的 $s$ 构成集合 $S_\alpha=\{s\ge0:\kappa_s(\alpha)>0\}$。
- 因为 $\langle k\rangle\ge1$，$\kappa_s$ 关于 $s$ 单调不减，所以 $S_\alpha$ 是向上封闭的区间。
- $S_\alpha\ne\emptyset$ 当且仅当 (D) 成立，即 $\alpha$ 不是 Liouville 数。
- 由引理 D，对任何无理 $\alpha$ 都有 $S_\alpha\subset[1,\infty)$。
- 因此 $S_\alpha$ 是 $\emptyset$、$[\sigma,\infty)$ 或 $(\sigma,\infty)$ 之一，其中 $\sigma\ge1$。

### 定理 C（$\alpha_*=\sqrt2-1$）

1. **$\kappa_1(\alpha_*)\ge1/3$。** 记共轭 $\alpha'=-\sqrt2-1$。
 - $\lambda(k)\lambda'(k)=(k_2-k_1)^2-2k_1^2$。当 $k\ne0$ 时这是非零整数，因为 $\sqrt2\notin\mathbb Q$。所以 $|\lambda(k)|\,|\lambda'(k)|\ge1$。
 - 若 $|\lambda(k)|\ge1$，显然 $\langle k\rangle|\lambda(k)|\ge1$。
 - 否则，由 Cauchy–Schwarz，$|\lambda'(k)|\le|\lambda(k)|+2\sqrt2|k_1|<1+2\sqrt2|k_1|\le3\langle k\rangle$，于是 $|\lambda(k)|>1/(3\langle k\rangle)$。
 - 数值检验：在 $|k_1|\le3000$ 范围内，$\langle k\rangle|\alpha_*k_1+k_2|$ 的最小值约为 $0.3827$，与下界 $1/3$ 一致。
2. **最小损失。** 由此 $\alpha_*$ 满足 (D)，$N_{\alpha_*}$ 在 $C^\infty_0$ 上可逆。结合引理 D，$S_{\alpha_*}=[1,\infty)$。所以**最小允许损失是 $s=1$，并且取到**：
 $$\|u\|_{H^r}\le\frac{3}{2\pi}\|N_{\alpha_*}u\|_{H^{r+1}}.$$
 任何 $s<1$ 都不允许。
3. **$C^m$ 估计成立，且对每个 $m$ 都成立。** 令 $u=N_{\alpha_*}^{-1}F$，则 $|\hat u(k)|\le\frac{3}{2\pi}\langle k\rangle|\hat F(k)|$。由 (P3) 可逐项求导，再用 $|k_i|\le\langle k\rangle$、Cauchy–Schwarz、(P3) 和 (P7)：
 $$\|u\|_{C^m}\le(2\pi)^m\sum_k\langle k\rangle^m|\hat u(k)|\le3(2\pi)^{m-1}\sum_k\langle k\rangle^{m+1}|\hat F(k)|\le3(2\pi)^{m-1}Z^{1/2}\|F\|_{H^{m+3}}.$$
 继续估计：
 $$\|u\|_{C^m}\le 3(2\pi)^{m-1}\Big(1+\frac{\pi^2}{3}\Big)3^{(m+3)/2}\,\|F\|_{C^{m+3}}\le C_m\|F\|_{C^{m+4}} .$$
 所以所问估计成立，常数为 $C_m=3(2\pi)^{m-1}(1+\pi^2/3)\,3^{(m+3)/2}$；实际上右端用 $C^{m+3}$ 就已足够。

## S5 邻近方向的一致估计

**结论：不存在。**

设 $J\ni\alpha_*$ 是开区间，$s\ge0$，$C<\infty$。

1. 取有理数 $p/q\in J$（$q\ge1$），令 $k=(q,-p)$，$u=e_k\in C^\infty_0$。
2. 取无理数 $\alpha\in J$，使 $|\alpha-p/q|<\big(2\pi Cq\langle k\rangle^s\big)^{-1}$。
3. 则 $\|u\|_{L^2}=1$，而
 $$C\|N_\alpha u\|_{H^s}=C\cdot2\pi q|\alpha-p/q|\langle k\rangle^s<1,$$
 与所设不等式矛盾。

补充两点：
- 第 2 步中的 $\alpha$ 可以取二次无理数 $p/q+\sqrt2/M$（$M$ 足够大）。所以即使只看单个方向都满足 $s=1$ 估计的那些 $\alpha$，一致常数也不存在。
- 更强地，每个这样的 $J$ 都含有 Liouville 数，例如 S6 中的 $\alpha$ 加上一个适当的有理数（见 S6 末尾）。对这些方向，按定理 B，任何 $s$ 都不成立。

## S6 一个具体方向的不可解数据

令 $\alpha=\sum_{n\ge1}10^{-n!}$，并对每个 $n\ge1$ 令
$$q_n=10^{n!},\qquad p_n=\sum_{j=1}^n10^{\,n!-j!}\in\mathbb Z .$$

**尾项估计。** 由于 $j!$ 在 $j\ge1$ 时严格递增，
$$0<q_n\alpha-p_n=10^{n!}\sum_{j>n}10^{-j!}\le\frac{10}{9}10^{\,n!-(n+1)!}=\frac{10}{9}q_n^{-n}.$$

**$\alpha$ 是无理数。** 若 $\alpha=a/b$（$b\ge1$），则 $q_n\alpha-p_n=(aq_n-bp_n)/b$ 是正数，所以至少为 $1/b$。于是 $1/b\le\frac{10}{9}q_n^{-n}\to0$，矛盾。

**构造 $F$。** 令 $k^{(n)}=(q_n,-p_n)$。由 $0\le p_n<q_n\alpha<q_n$ 得 $\langle k^{(n)}\rangle\le\sqrt3\,q_n\le2q_n$。由于 $q_n$ 严格递增，这些频率两两不同且非零。定义
$$F(y)=\sum_{n\ge1}2\,q_n^{-n/2}\cos\!\big(2\pi(q_ny_1-p_ny_2)\big),$$
即 $\hat F(\pm k^{(n)})=q_n^{-n/2}$，其余系数为零。
- 当 $n\ge2M$ 时，$\langle k^{(n)}\rangle^M q_n^{-n/2}\le2^Mq_n^{M-n/2}\le2^M$，所以系数速降。
- 由 (P3)，$F$ 是光滑的实值函数，并且零均值。

**$N_\alpha u=F$ 无光滑零均值解。** 若有这样的 $u$，由 (P1) 得
$$|\hat u(k^{(n)})|=\frac{q_n^{-n/2}}{2\pi(q_n\alpha-p_n)}\ge\frac{9}{20\pi}q_n^{n/2}\to\infty,$$
与 (P5) 矛盾。这对同一个固定的 $F$ 成立。

补充：
- 由 $q_n^{n/2}\ge(\langle k^{(n)}\rangle/2)^{n/2}$，这些系数增长快于 $\langle k\rangle$ 的任何多项式，所以连分布意义下的解也不存在。
- 同时有 $\langle k^{(n)}\rangle^s|\lambda_\alpha(k^{(n)})|\le\frac{10}9(2q_n)^sq_n^{-n}\to0$ 对一切 $s$ 成立，与定理 A、B 一致。
- 对有理数 $p/q$，把 $k=(m,n)$ 换成 $(qm,\,qn-pm)$ 可知 $\alpha+p/q$ 同样是 Liouville 数，所以 Liouville 数在每个区间中都存在。