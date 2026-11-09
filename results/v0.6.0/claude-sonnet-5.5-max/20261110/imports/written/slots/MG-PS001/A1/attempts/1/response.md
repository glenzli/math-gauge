# 答案

记 $\alpha_f:=\limsup_{n\to\infty} f(n)/n\in[1,+\infty]$。因为 $f$ 严格递增，所以 $f(n)\ge n$。

**第 1 问。**
- $P_f$ 能诱导 $T_f$ ⇔ $\alpha_f<\infty$，即存在常数 $C$ 使 $f(n)\le Cn$ 对一切 $n$ 成立。
- 此时 $T_f$ 是 Lipschitz 映射，因而连续。最小 Lipschitz 常数恰为 $L_1=\alpha_f=\limsup_n f(n)/n$。它总是有限的，所以"$+\infty$"的约定用不上。
- $T_f$ 总是满射。
- $T_f$ 是单射 ⇔ $\alpha_f=1$ ⇔ $f(n)/n\to1$。此时 $T_f$ 是等距双射。若 $\alpha_f>1$，则 $T_f$ 不是单射。

**第 2 问。**
- $L_k=\limsup_n f^{k}(n)/n$，其中 $f^k$ 是 $f$ 的 $k$ 次迭代。
- $L_{k+m}\le L_kL_m$，所以 $R_f=\lim L_k^{1/k}=\inf_k L_k^{1/k}$ 存在，且 $1\le R_f\le L_1<\infty$。
- 全部可能的有序对恰为 $\{(\ell,r)\in\mathbb R^2:\ 1\le r\le \ell<\infty\}$，每一对的构造见 §2.3。

---

# 0. 记号

对 $z\in E$ 记 $\|z\|:=\limsup_N\frac1N\sum_{j\le N}|z_j|$。则 $d(x,y)=\|x-y\|$，$\|\cdot\|$ 是半范数，$\bar d([x],[y])=\|x-y\|$，$P_f$ 线性。故

**(0.1)** $T_f$ 有定义 ⇔ 对一切 $z\in E$：$\|z\|=0\Rightarrow\|P_fz\|=0$。此时 $\bar d(T_f[x],T_f[y])=\|P_f(x-y)\|$。

严格递增的 $f$ 是单射，且 $f(n)\to\infty$。记值域 $S=f(\mathbb N)$，partial sums 记 $\Sigma_M=\sum_{m\le M}|z_m|$。每个 $f(n)/n$ 有限，所以 $\alpha_f<\infty\iff\sup_n f(n)/n<\infty$。

最小 Lipschitz 常数指 $\inf\{\Lambda:\bar d(Tu,Tv)\le\Lambda\bar d(u,v)\ \forall u,v\}$。

# 1. 第 1 问

**引理 1.1（上界）。** 若 $\alpha_f<\infty$，则对一切 $z\in E$ 有 $\|P_fz\|\le\alpha_f\|z\|$。

*证。* $f(1)<\dots<f(N)$ 是 $[1,f(N)]$ 中互异的整数，故 $\sum_{j\le N}|z_{f(j)}|\le\Sigma_{f(N)}$，从而
$$\frac1N\sum_{j\le N}|z_{f(j)}|\le\frac{f(N)}N\cdot\frac{\Sigma_{f(N)}}{f(N)}.$$
任给 $\varepsilon>0$。$N$ 大时 $f(N)/N\le\alpha_f+\varepsilon$。又 $f(N)\to\infty$，故 $\Sigma_{f(N)}/f(N)\le\|z\|+\varepsilon$。于是 $\|P_fz\|\le(\alpha_f+\varepsilon)(\|z\|+\varepsilon)$，令 $\varepsilon\to0$。∎

**引理 1.2（必要性）。** 若 $\alpha_f=\infty$，则存在 $A\subset\mathbb N$ 使 $\|1_A\|=0$，而 $\|P_f1_A\|\ge\frac12$。故 $T_f$ 无定义。

*证。* 归纳取 $n_1<n_2<\cdots$，使 $f(n_k)\ge k\,n_k$ 且 $n_{k+1}\ge2n_k$。令 $B=\bigcup_k(n_k,2n_k]\cap\mathbb N$（各区间不交），$A=f(B)$。

对 $M\ge f(n_1+1)$，令 $k=k(M)$ 为满足 $f(n_k+1)\le M$ 的最大 $k$。若 $j\in B$ 且 $f(j)\le M$，设 $j\in(n_i,2n_i]$，则 $f(n_i+1)\le f(j)\le M$，故 $i\le k$。于是
$$|A\cap[1,M]|\le\sum_{i\le k}n_i\le2n_k,\qquad M\ge f(n_k+1)>f(n_k)\ge kn_k.$$
所以 $|A\cap[1,M]|/M\le2/k(M)$。当 $M\to\infty$ 时 $k(M)\to\infty$，故 $\|1_A\|=0$。

另一方面 $f$ 单射，所以 $P_f1_A=1_{f^{-1}(A)}=1_B$。而 $|B\cap[1,2n_k]|\ge n_k$，故 $\|P_f1_A\|\ge\frac12$。∎

**引理 1.3（最优性）。** 设 $\alpha_f<\infty$，$0<\lambda<\alpha_f$，$0<\gamma<1$，$C=\lambda/\gamma$。则存在 $w\in E$，$0\le w\le C$，使 $\|w\|\le1$，$\|P_fw\|\ge\lambda/(1+\gamma)$。因此任一 Lipschitz 常数 $\Lambda\ge\alpha_f$。

*证。* 有无穷多个 $n$ 满足 $f(n)\ge\lambda n$。从中选 $N_1<N_2<\cdots$，使 $N_k\ge k(N_1+\dots+N_{k-1})$ $(k\ge2)$。令 $q_k=\lfloor\gamma N_k\rfloor$，$J_k=\{N_k+1,\dots,N_k+q_k\}$，它们两两不交。令 $B=\bigcup_kf(J_k)$，$w=C\cdot 1_B$。

(i) $f$ 单射，故 $P_fw=C\cdot1_{\bigcup J_k}$。取 $N=N_k+q_k$：
$$\frac1N\sum_{j\le N}(P_fw)_j\ge\frac{C\lfloor\gamma N_k\rfloor}{(1+\gamma)N_k}\to\frac{\lambda}{1+\gamma}.$$

(ii) 令 $W(M)=\sum_{m\le M}w_m=C|B\cap[1,M]|$。设 $k\ge2$，$f(N_{k-1})<M\le f(N_k)$。当 $i\ge k$ 时，$f(J_i)$ 的元素 $f(j)$ 满足 $j>N_k$，故 $f(j)>f(N_k)\ge M$。所以 $B\cap[1,M]\subset\bigcup_{i\le k-1}f(J_i)$，从而
$$W(M)\le C\sum_{i\le k-1}q_i\le\lambda\sum_{i\le k-1}N_i\le\lambda\Big(1+\tfrac1{k-1}\Big)N_{k-1},$$
这里用了 $N_{k-1}\ge(k-1)\sum_{i\le k-2}N_i$。又 $M>f(N_{k-1})\ge\lambda N_{k-1}$，故 $W(M)/M\le1+\frac1{k-1}$。$M\to\infty$ 时 $k\to\infty$，所以 $\|w\|\le1$。

(iii) 若 $\Lambda$ 是 Lipschitz 常数，则 $\frac{\lambda}{1+\gamma}\le\|P_fw\|=\bar d(T_f[w],T_f[0])\le\Lambda\|w\|\le\Lambda$。令 $\lambda\uparrow\alpha_f$，$\gamma\downarrow0$ 即得 $\Lambda\ge\alpha_f$。∎

**引理 1.4（满射）。** 对任意 $y\in E$，令 $x_{f(j)}=y_j$，$x_m=0$（$m\notin S$）。则 $x\in E$ 且 $P_fx=y$。故 $T_f$ 满射（对任何 $f$ 成立）。∎

**引理 1.5（单射性）。** 设 $\alpha_f<\infty$。

(1) 若 $\alpha_f>1$，则 $T_f$ 不单射。取 $\lambda\in(1,\alpha_f)$，令 $z=1_{\mathbb N\setminus S}$。因 $f(j)\in S$，有 $P_fz=0$，所以 $T_f[z]=T_f[0]$。对满足 $f(n)\ge\lambda n$ 的 $n\ge2$ 取 $M=f(n)-1$。此时 $S\cap[1,M]=\{f(1),\dots,f(n-1)\}$ 恰有 $n-1$ 个元素，故
$$\frac1M\sum_{m\le M}z_m=\frac{f(n)-n}{f(n)-1}\ge1-\frac1\lambda.$$
于是 $\|z\|\ge1-\frac1\lambda>0$，$[z]\ne[0]$。

(2) 若 $\alpha_f=1$（即 $f(n)/n\to1$），则对一切 $z$ 有 $\|P_fz\|=\|z\|$。"$\le$"由引理 1.1 得到。反向：设 $|z|\le C_0$。对 $M$ 令 $N=|S\cap[1,M]|$，则 $f(N)\le M<f(N+1)$，且 $M\to\infty$ 时 $N\to\infty$。于是
$$\Sigma_M\le\sum_{j\le N}|z_{f(j)}|+C_0(M-N),\qquad \frac{M-N}{M}\le\frac{M-N}{N}<\frac{f(N+1)}{N+1}\cdot\frac{N+1}{N}-1\to0.$$
又 $N\le M$，所以 $\frac{\Sigma_M}{M}\le\frac1N\sum_{j\le N}|z_{f(j)}|+o(1)$，故 $\|z\|\le\|P_fz\|$。因此 $T_f$ 是等距，从而单射。结合引理 1.4，它是等距双射。∎

**定理 1 的证明汇总。**
- (a)：由引理 1.1 与 (0.1)，$\alpha_f<\infty$ 时 $T_f$ 有定义；由引理 1.2，$\alpha_f=\infty$ 时无定义。
- Lipschitz 性与最小常数 $=\alpha_f$：由引理 1.1 与 1.3。
- 满射：引理 1.4。
- 单射性：引理 1.5。∎

注：这里是 $\limsup$ 而不是 $\sup$。例如 $f(n)=n+99$ 有 $\sup f(n)/n=100$，但 $\alpha_f=1$，$T_f$ 是等距。

# 2. 第 2 问

## 2.1 $L_k$ 的表达式

设 $\alpha_f<\infty$。由 $(P_f^{k+1}x)_j=(P_f^kx)_{f(j)}=x_{f^{k+1}(j)}$ 知 $P_f^k=P_{f^k}$，故 $T_f^k=T_{f^k}$。$f^k$ 严格递增，且 $f^k(n)/n=\prod_{i<k}\frac{f(f^i(n))}{f^i(n)}\le(\sup_n f(n)/n)^k<\infty$。对 $f^k$ 用定理 1：
$$L_k=\alpha_{f^k}=\limsup_{n\to\infty}\frac{f^k(n)}n\in[1,\infty).$$

## 2.2 极限存在，且 $1\le R_f\le L_1$

Lipschitz 常数在复合下相乘，所以 $L_{k+m}\le L_kL_m$。令 $a_k=\log L_k\ge0$，则 $a_{k+m}\le a_k+a_m$。这就是 Fekete 引理，下面给出证明。

固定 $q$。对 $k=sq+t$（$0\le t<q$，$a_0:=0$）有 $a_k\le sa_q+a_t$，故
$$\frac{a_k}{k}\le\frac{a_q}{q}+\frac{\max_{t<q}a_t}{k}.$$
所以 $\limsup_k a_k/k\le a_q/q$。对 $q$ 取下确界得 $\limsup\le\inf_q a_q/q\le\liminf$。故 $R_f=\lim L_k^{1/k}=\inf_k L_k^{1/k}$ 存在。由 $1\le L_k\le L_1^k$ 得 $1\le R_f\le L_1<\infty$。

因此**可能的有序对必落在 $\{1\le r\le \ell<\infty\}$ 内**。

## 2.3 构造：任给 $1\le r\le\ell<\infty$，造 $f$ 使 $(L_1,R_f)=(\ell,r)$

令 $\kappa=\ell+1$，$a_m=2^{m^2}$（$m\ge0$；$a_0=1$，$a_{m+2}/a_{m+1}=2^{2m+3}\to\infty$），$c_m=\lceil\ell a_m\rceil-a_m$，并定义
$$f(n)=\max\{\lceil rn\rceil,\ n+c_m\}\qquad(a_m\le n<a_{m+1}).$$
直观上：每个区间起点处 $f$ 以加性偏移 $c_m$ 爆发到 $\ell a_m$，之后以斜率 $r$ 增长。爆发在迭代中只按加法累积，不会指数放大。

**(A) 基本性质。**
- 因 $\ell\ge1$，$h(a)=\lceil\ell a\rceil-a$ 满足 $h(a+1)\ge h(a)\ge0$（因为 $\lceil\ell(a+1)\rceil\ge\lceil\ell a\rceil+1$）。故 $0\le c_0\le c_1\le\cdots$，且 $c_m<(\ell-1)a_m+1$。
- 区间内：$n\mapsto\lceil rn\rceil$（$r\ge1$）与 $n\mapsto n+c_m$ 都严格增，故其最大值严格增。
- 区间衔接处：$f(a_{m+1})=\lceil\ell a_{m+1}\rceil$（因 $\ell\ge r$）。一方面
$$\lceil\ell a_{m+1}\rceil\ge\lceil ra_{m+1}\rceil\ge\lceil r(a_{m+1}-1)\rceil+1;$$
另一方面 $\lceil\ell a_{m+1}\rceil=a_{m+1}+c_{m+1}\ge a_{m+1}+c_m>a_{m+1}-1+c_m$。故 $f(a_{m+1})>f(a_{m+1}-1)$。
- 所以 $f:\mathbb N\to\mathbb N$ 严格递增。

**(B) 估计。**
1. $f(n)\ge rn$。
2. $f(a_m)=\lceil\ell a_m\rceil\ge\ell a_m$。
3. $f(n)<\ell n+1$：因为 $\lceil rn\rceil<rn+1\le\ell n+1$，且 $n+c_m<n+(\ell-1)a_m+1\le\ell n+1$。
4. 当 $a_m\le n<a_{m+1}$ 时 $f(n)<rn+\kappa a_m$：因为 $\lceil rn\rceil<rn+1\le rn+\kappa a_m$，且 $n+c_m\le rn+c_m<rn+(\ell-1)a_m+1\le rn+\kappa a_m$。

**(C) $L_1=\ell$。** 由 B2、B3，$f(a_m)/a_m\ge\ell$，且 $f(n)/n<\ell+1/n$。故 $\alpha_f=\ell$，由定理 1 得 $L_1=\ell$。

**(D) $r^k\le L_k\le r^k(1+k\kappa)^2$。**

下界：由 B1，$f^k(n)\ge r^kn$，故 $L_k\ge r^k$。

上界：固定 $k$，取 $m_0$ 使 $m\ge m_0$ 时 $2^{2m+3}\ge\kappa^k$，即 $a_{m+2}\ge\kappa^ka_{m+1}$。设 $m\ge m_0$，$a_m\le n<a_{m+1}$，记 $n_i=f^i(n)$。

- 由 B3，$f(x)<\ell x+1\le\kappa x$，故 $n\le n_i\le\kappa^in<a_{m+2}$（$i\le k$）。所以每个 $n_i$ 属于第 $m$ 块或第 $m+1$ 块。
- $n_i$ 单调不减。令 $t=\min\{i\le k:\ n_i\ge a_{m+1}\}$，若无这样的 $i$ 则取 $t=k$。
- 展开引理：若 $x_{i+1}\le rx_i+\beta$（$0\le i<s$，$\beta\ge0$），则 $x_s\le r^s(x_0+s\beta)$。
- 当 $i<t$ 时 $n_i$ 在第 $m$ 块，由 B4，$n_{i+1}<rn_i+\kappa a_m\le rn_i+\kappa n$。故 $n_t\le r^t(1+t\kappa)n$。
- 若 $t=k$，已得结论。若 $t<k$，则对 $t\le i<k$ 有 $n_i\in[a_{m+1},a_{m+2})$，由 B4，$n_{i+1}<rn_i+\kappa a_{m+1}\le rn_i+\kappa n_t$。故 $n_k\le r^{k-t}(1+k\kappa)n_t$。
- 合并得 $f^k(n)\le r^k(1+k\kappa)^2n$ 对一切 $n\ge a_{m_0}$ 成立，于是 $L_k\le r^k(1+k\kappa)^2$。

**(E)** 由 D，$r\le L_k^{1/k}\le r(1+k\kappa)^{2/k}\to r$，故 $R_f=r$。

## 2.4 结论

2.2 说明 $(L_1,R_f)$ 必满足 $1\le R_f\le L_1<\infty$。2.3 对每个这样的 $(\ell,r)$ 给出了 $f$，使 $(L_1,R_f)=(\ell,r)$。因此全部可能的有序对恰为
$$\boxed{\{(L,R)\in\mathbb R^2:\ 1\le R\le L<\infty\}}.$$

特殊情形：$(\ell,\ell)$ 对应 $f(n)=\lceil\ell n\rceil$，$(1,1)$ 对应 $f=\mathrm{id}$。$(\ell,1)$（$\ell>1$）对应 $f(n)=n+c_m$，此时 $L_k$ 线性增长。

*数值抽查（非证明的一部分）：* 我对若干组 $(\ell,r)$ 用精确算术检验了 $f$ 的严格单调性与 $r^k\le L_k\le r^k(1+k\kappa)^2$。对引理 1.3 的构造也做了数值检验，其中 $\sup W(M)/M<1$，$P_fw$ 的平均值趋于 $\lambda/(1+\gamma)$。