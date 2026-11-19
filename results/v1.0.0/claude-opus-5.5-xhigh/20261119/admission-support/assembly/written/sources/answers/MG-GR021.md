下面给出完整解答：先把问题化归到一组正交幂等元和一族局部正交群，再依次回答三问。结论都给出证明；另外用计算机对小参数做了穷举核对（$n\le3$、$M\le4$ 的各个计数，以及若干随机例子的可行性判准），结果全部一致。

# 0 记号与所用标准事实

- $L\in\{F,K_{-1},K_2\}$，$\mathcal O=\mathcal O_L$。$e=e_L$ 取值为：$e_F=1$，$e_{K_\mu}=2$。
- 素元 $\pi$：$\pi_F=2$，$\pi_{-1}=\theta_{-1}-1$，$\pi_2=\theta_2$。于是 $2\mathcal O=\pi^{e}\mathcal O$，剩余域为 $\mathbb F_2$。
- $\beta:=\sum_j\binom{n_j}{2}$；$\varepsilon_M:=1$（当 $M\ge3$），$\varepsilon_2:=0$。
- $\mathrm{Sym}_{bd}$：$M_d(\mathbb F_2)$ 中分块对角（即与所有 $E_j$ 交换）的对称矩阵，共 $2^{d+\beta}$ 个。$\mathrm{Alt}_{bd}$：其中对角线为零者，共 $2^{\beta}$ 个。$\deg_Z(k):=\sum_{l\ne k}Z_{lk}$。
- 列范数：对 $\bar U\in M_d(\mathcal O/2^M)$，令 $\nu_k(\bar U):=\sum_l\tilde U_{lk}^2\in\mathcal O/2^{M+1}$，其中 $\tilde U$ 是任一提升。它与提升的选取无关，因为 $(u+2^Mz)^2\equiv u^2 \pmod{2^{M+1}}$。
- $\omega_\mu:=\mu+\theta_\mu=\theta_\mu(1+\theta_\mu)$。
- **障碍量** $\tau_j(A):=\tfrac12\sum_{k\in I_j}\sum_{m\notin I_j}(A_j)_{km}\bmod 2\in\mathbb F_2$。各项为偶数，所以 $\tau_j$ 只依赖 $A_j\bmod 4$。
- 局部群：
  - $\Gamma_n(L)=\{V\in GL_n(\mathcal O):V\equiv I\ (2),\ V^{\mathsf T}V=I\}$；
  - $\bar\Gamma_n(L,M)$ 为 $\Gamma_n(L)$ 在模 $2^M$ 下的像；
  - $C_n(L,M)=\{\bar V\in GL_n(\mathcal O/2^M):\bar V\equiv I\ (2),\ \bar V^{\mathsf T}\bar V=I\}$。

**(F1) 二次扩张。** $\theta_2$ 满足 Eisenstein 多项式 $x^2-2$，$\pi_{-1}$ 满足 $x^2+2x+2$。所以 $K_\mu/F$ 是完全分歧二次扩张，并且：
- $\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu$ 是整数环；
- $\mathcal O_\mu^{\sigma}=\mathbb Z_2$；
- $2^M\mathcal O_\mu=2^M\mathbb Z_2\oplus 2^M\mathbb Z_2\theta_\mu$；
- $\mathbb Z_2$ 中元素的 $\pi$-赋值都是偶数；
- $v_\pi(\omega_\mu)=1$（$\omega_{-1}=\pi_{-1}$；$1+\theta_2$ 是单位）。

**(F2) 剩余域为 $\mathbb F_2$ 的推论。** $y^2\equiv y\pmod\pi$，从而 $y(1+y)\in\pi\mathcal O$，$(1+2y)^2=1+4y(1+y)\in 1+4\pi\mathcal O$。$1+4\pi\mathcal O$ 是乘法群，且 $(1+4\pi\mathcal O)\cap\mathbb Z_2=1+8\mathbb Z_2$。

**(F3) 多元 Hensel 引理（计数形式）。**
- 条件：$\mathcal O$ 是完备离散赋值环，剩余域有 $q$ 个元素；$g\in\mathcal O[x_1,\dots,x_N]^R$；对每个 $x\in\mathcal O^N$，$Dg(x)\bmod\pi$ 的秩为 $R$；$c\in\mathcal O^R$，$s\ge1$。
- (i) 若 $g(x)\equiv c\ (\pi^s)$，则在 $x$ 之上、模 $\pi^{s+1}$ 仍满足方程的类恰有 $q^{N-R}$ 个。
- (ii) 存在 $x^*\equiv x\ (\pi^s)$ 使 $g(x^*)=c$。
- (iii) $\#\{x\bmod\pi^s: g\equiv c\ (\pi^s)\}=q^{(s-1)(N-R)}\cdot\#\{x\bmod\pi:g\equiv c\ (\pi)\}$。
- 证明：Taylor 展开 $g(x+\pi^sh)=g(x)+\pi^sDg(x)h+\pi^{2s}r(x,h)$，其中 $r$ 是整系数多项式。由 $2s\ge s+1$，条件化为 $\mathbb F_q$ 上一个秩为 $R$ 的仿射方程组，解得 (i)；迭代并利用完备性得 (ii)；对 $s$ 归纳得 (iii)。

**(F3′) 单变量 Hensel。** 若 $f\in\mathcal O[x]$ 且 $v(f(a))>2v(f'(a))$，则存在根 $\alpha$，满足 $v(\alpha-a)\ge v(f(a))-v(f'(a))$。

**(F4) 幂等元。** 设 $R=\mathcal O_L$ 或 $\mathcal O_L/2^M$。$M_n(R)$ 中幂等元 $Q\equiv0\ (2)$ 必为 $0$：因为 $Q=Q^k\in 2^kM_n(R)$ 对所有 $k$ 成立，而 $\bigcap_k 2^kR=0$。若 $Q\equiv I\ (2)$，则 $I-Q$ 是 $\equiv0$ 的幂等元，故 $Q=I$。

# 1 化归为一组正交幂等元

**引理 1.1（幂等元提升）。** 令 $\phi(x)=3x^2-2x^3$，$x_0=A_j$，$x_{k+1}=\phi(x_k)$。则 $x_k\to P_j$，并且：
- (a) $P_j$ 对称幂等，$P_j\equiv x_k\pmod{2^{2^k}}$；特别地 $P_j\equiv E_j\ (2)$，$P_j\equiv3A_j^2-2A_j^3\ (4)$。
- (b) $P_j$ 与所有 $A_i,P_i$ 交换；$P_iP_j=0$（$i\neq j$）；$\sum_jP_j=I$。
- (c) 对 $k\in I_j$、$m\notin I_j$，有 $(P_j)_{km}\equiv(A_j)_{km}\pmod 4$。

*证明。*
- 在 $\mathbb Z[x]$ 中有恒等式 $\phi(x)-x=(x^2-x)(1-2x)$ 与 $\phi(x)^2-\phi(x)=(x^2-x)^2(4x^2-4x-3)$。由 $x_0^2-x_0\equiv E_j^2-E_j=0\ (2)$ 归纳得 $x_k^2-x_k\in2^{2^k}M_d$ 且 $x_{k+1}-x_k\in 2^{2^k}M_d$。所以 $x_k$ 收敛，极限是幂等元，并且 $P_j\equiv x_k \pmod{2^{2^k}}$。
- 每个 $x_k$ 都是 $A_j$ 的整系数多项式，因此对称，并与所有 $A_i$ 交换；取极限得 (a) 和 (b) 的交换部分。
- $i\neq j$ 时 $P_iP_j$ 是幂等元且 $\equiv E_iE_j=0$，由 (F4) 为 $0$。$\sum_jP_j$ 是幂等元且 $\equiv I$，故等于 $I$。
- (c)：写 $A_j=E_j+2Q'$。模 4 有 $3A_j^2-2A_j^3\equiv E_j+2(E_jQ'+Q'E_j)$，而 $E_jQ'+Q'E_j$ 的 $(I_j,I_j^c)$ 块正是 $Q'_{I_j,I_j^c}$。∎

**引理 1.2。** 设 $R\in\{\mathcal O_L,\mathcal O_L/2^M\}$，$\bar U\equiv I\ (2)$，$\bar U^{\mathsf T}\bar U=I$。则
$$[\bar U^{\mathsf T}A_i\bar U,E_j]=0\ (\forall i,j)\iff P_j\bar U=\bar UE_j\ (\forall j).$$

*证明。*
- (⇐)：$\bar U^{\mathsf T}A_i\bar U$ 与 $\bar U^{\mathsf T}P_j\bar U=E_j$ 交换。
- (⇒)：$\bar U^{\mathsf T}P_j\bar U$ 等于 $x_k(\bar U^{\mathsf T}A_j\bar U)$（在 $\mathcal O/2^M$ 上取足够大的 $k$；在 $\mathcal O$ 上取极限），因此是分块对角的幂等元。它的各对角块是模 2 同余于 $\delta_{ij}I$ 的幂等元，由 (F4) 即得 $\bar U^{\mathsf T}P_j\bar U=E_j$。∎

**引理 1.3（Gram 描述）。** 令 $U_*:=\sum_jP_jE_j\in M_d(\mathbb Z_2)$，即对 $k\in I_j$，第 $k$ 列为 $P_je_k$。
- 基本性质：$U_*\equiv I\ (2)$，$P_jU_*=U_*E_j$，$U_*^{\mathsf T}U_*=\operatorname{diag}(G_1,\dots,G_r)$，其中 $G_j:=(P_j)_{I_j,I_j}$。
- 写 $P_j=E_j+2Q_j$，$b_j:=(Q_j)_{I_j,I_j^c}$。则 $G_j\equiv I-4b_jb_j^{\mathsf T}\ (16)$，$\det G_j\equiv 1+4\tau_j\ (8)$，并且恒有 $\sum_j\tau_j=0$。
- 对 $R$ 同上，满足 $\bar U\equiv I\ (2)$、$\bar U^{\mathsf T}\bar U=I$、$P_j\bar U=\bar UE_j$ 的 $\bar U$ 恰为
$$U_*\operatorname{diag}(T_1,\dots,T_r),\qquad T_j\in M_{n_j}(R),\ T_j\equiv I\ (2),\ T_j^{\mathsf T}G_jT_j=I .$$

*证明。*
- 基本性质：$P_iP_j=\delta_{ij}P_j$ 且 $P_j$ 对称，直接验证。
- $G_j$ 的同余：幂等性给出 $Q_j=E_jQ_j+Q_jE_j+2Q_j^2$。取 $(I_j,I_j)$ 块得 $(Q_j)_{11}=-2\big((Q_j)_{11}^2+b_jb_j^{\mathsf T}\big)$。所以 $(Q_j)_{11}$ 是偶的，从而 $(Q_j)_{11}\equiv-2b_jb_j^{\mathsf T}\ (8)$，即 $G_j=I+2(Q_j)_{11}\equiv I-4b_jb_j^{\mathsf T}\ (16)$。
- 行列式：$\det(I+4X)\equiv1+4\operatorname{tr}X\ (16)$，故 $\det G_j\equiv1-4\sum b_{km}^2\equiv1+4\sum b_{km}\ (8)$。由引理 1.1(c)，$\sum b_{km}\equiv\tau_j$。
- $\sum_j\tau_j=0$：$\prod_j\det G_j=(\det U_*)^2\in1+8\mathbb Z_2$（用 (F2)）。
- 参数化：若 $P_j\bar U=\bar UE_j$，则 $T:=U_*^{-1}\bar U$ 满足 $E_jT=U_*^{-1}P_j\bar U=TE_j$，即 $T$ 分块对角；反向同理。再由 $\bar U^{\mathsf T}\bar U=T^{\mathsf T}\operatorname{diag}(G_j)T$ 得到其余条件。∎

**推论 1.4（主齐性空间结构）。**
- $\mathscr S_L(A)$ 为空，或是 $\prod_j\Gamma_{n_j}(L)$（分块对角嵌入，右乘）的主齐性空间。
- $\mathscr C_{L,M}(A)$ 为空，或是 $\prod_jC_{n_j}(L,M)$ 的主齐性空间。
- 若 $U_0\in\mathscr S_L(A)$，则 $\mathscr R_{L,M}(A)=\bar U_0\cdot\prod_j\bar\Gamma_{n_j}(L,M)$。

*证明。* 设 $U_*T,U_*T'$ 都满足条件，$V_j=T_j^{-1}T'_j$。由 $(T_j^{-1})^{\mathsf T}T_j^{-1}=G_j$ 得 $V_j^{\mathsf T}V_j=T_j'^{\mathsf T}G_jT'_j=I$，且 $V_j\equiv I\ (2)$。反向同理。∎

# 2 局部群

**引理 2.1。** 对 $X\in M_n(\mathcal O)$，有 $(I+2X)^{\mathsf T}(I+2X)=I+2f(X)$，其中 $f(X)=X+X^{\mathsf T}+2X^{\mathsf T}X$。令
$$g_{kl}=f_{kl}\ (k<l),\qquad g_{kk}=\tfrac12 f_{kk}=X_{kk}+\sum_lX_{lk}^2,$$
得到 $g:\mathcal O^{n^2}\to\mathcal O^{\binom{n+1}2}$。
- (1) $I+2X$ 正交 $\iff g(X)=0$。
- (2) 对 $X\bmod 2^{M-1}$：$(I+2X)^{\mathsf T}(I+2X)\equiv I\ (2^M)\iff$ 对 $k<l$ 有 $g_{kl}\equiv0\ (2^{M-1})$，且 $g_{kk}\equiv0\ (2^{M-2})$。
- (3) $\nu_k(I+2X)=1+4g_{kk}(X)$。
- (4) 在变量 $\{X_{kk}\}\cup\{X_{lk}\}_{k<l}$ 上，$Dg$ 的子式模 $\pi$ 为单位阵。因此 (F3) 的条件处处成立，且 $N-R=\binom n2$。
- (5) 由 (F2)，模 $\pi$ 有 $g_{kl}\equiv X_{kl}+X_{lk}$，$g_{kk}\equiv\sum_{l\ne k}X_{lk}$。

**引理 2.2（$\mathbb F_2$ 上的线性代数）。** 线性映射 $\lambda:X\mapsto\big((X_{kl}+X_{lk})_{k<l},(\sum_{l\neq k}X_{lk})_k\big)$ 满足：
- 核 $W_0$ 由这样的 $X$ 组成：非对角部分对称，且是 $K_n$ 的一个各顶点度数均为偶数的子图；对角线任意。所以 $|W_0|=2^{n}\cdot2^{\binom n2-n+1}=2^{\binom n2+1}$。
- 像是超平面 $\sum_kc_{kk}=\sum_{k<l}c_{kl}$。像含于其中是双重计数；维数为 $n^2-\binom n2-1=\binom{n+1}2-1$，故相等。

**命题 2.3。** 对 $n\ge1$、$M\ge2$：
- (a) $|\bar\Gamma_n(L,M)|=2^{1+e(M-1)\binom n2}$。
- (b) $|C_n(L,M)|=2^{e(n+(M-1)\binom n2)+\varepsilon_M}$。
- (c) $\bar V\in C_n(L,M)$ 属于 $\bar\Gamma_n(L,M)$，当且仅当对所有 $k$ 有 $\nu_k(\bar V)=1$（在 $\mathcal O/2^{M+1}$ 中）。
- (d) $C_n(L,M+1)\to C_n(L,M)$ 的像为 $\bar\Gamma_n(L,M)$，核的阶为 $2^{e(n+\binom n2)}$；$\bar\Gamma_n(L,M+1)\to\bar\Gamma_n(L,M)$ 的核的阶为 $2^{e\binom n2}$。

*证明。* 记 $s=e(M-1)$，则 $\bar V=I+2X\bmod 2^M$ 对应于 $X\bmod\pi^s$。
- (a)：由 (F3)(ii)，所有模 $\pi^s$ 解都可提升，故 $\bar\Gamma$ 与 $\{X\bmod \pi^s:g\equiv0\}$ 一一对应。由 (F3)(iii) 与 $|W_0|$，其个数为 $2^{\binom n2+1}\cdot 2^{(s-1)\binom n2}$。
- (b)，$M=2$：条件只有 $X_{kl}+X_{lk}\equiv0\ (2)$，对角线与上三角任意，共 $2^{e(n+\binom n2)}$ 个。
- (b)，$M\ge3$：按 $t=(g_{kk}\bmod\pi^s)\in(\pi^{s-e}\mathcal O/\pi^s)^n$ 分类，共 $2^{en}$ 类。由于 $s-e\ge1$，有 $t\equiv0\ (\pi)$，每类由 (F3)(iii) 有 $2^{\binom n2+1}\cdot2^{(s-1)\binom n2}$ 个元素。
- (c)：由 (F3)(ii)，$\bar V$ 可提升 $\iff g(X)\equiv0\ (\pi^s)$。在 (2) 已成立的前提下，这等价于 $g_{kk}\equiv0\ (2^{M-1})$，再由 (3) 等价于 $\nu_k=1$。
- (d)：$C_{M+1}$ 中元素约化后列范数为 1，由 (c) 落入 $\bar\Gamma_M$；反过来 $\bar\Gamma_M$ 是 $\bar\Gamma_{M+1}\subseteq C_{M+1}$ 的像。两个核的阶由基数之比得到。∎

# 3 可行性

**定理 3.1。** 下列各条等价：
- (i) $\mathscr S_F(A)\ne\emptyset$；
- (ii) 对某个（等价地，对每个）$L$，$\mathscr S_L(A)\neq\emptyset$；
- (iii) 对某个 $L$ 和某个 $M\ge3$，$\mathscr C_{L,M}(A)\ne\emptyset$；
- (iv) 存在 $\bar U\in\mathscr C_{L,2}(A)$，使所有 $\nu_k(\bar U)=1$（模 8）；
- (v) 对所有 $j$，$\tau_j(A)=0$（等价地，$\det G_j\equiv1\ (8)$）。

此外 $U_*\bmod4\in\mathscr C_{L,2}(A)$ 总成立（因为 $G_j\equiv I\ (4)$），所以 $\mathscr C_{L,2}(A)$ 恒非空。

*证明。*
- (i)⇒(ii)⇒(iii)⇒(iv)：包含与约化。约化到模 4 后，$\bar U^{\mathsf T}\bar U\equiv I\ (8)$ 给出对角元 $\equiv1\ (8)$。
- (iv)⇒(v)：取 $\bar U=U_*T$ 和提升 $\tilde T\equiv I$。该块的 Gram 矩阵 $N_j=\tilde T_j^{\mathsf T}G_j\tilde T_j=I+4R$，其中 $R_{kk}\in2\mathcal O$。于是 $\det N_j\equiv 1+4\operatorname{tr}R\equiv1\ (8)$。又 $\det N_j=(\det\tilde T_j)^2\det G_j$，且 $(\det \tilde T_j)^2\in1+4\pi\mathcal O$（(F2)），所以 $\det G_j\in(1+4\pi\mathcal O)\cap\mathbb Z_2=1+8\mathbb Z_2$。
- (v)⇒(i)：在 $\mathbb Z_2$ 上求 $S_j=I+2Y\equiv I$ 使 $S_j^{\mathsf T}S_j=G_j$，即 $g(Y)=c$，其中 $c_{kl}=G_{kl}/2$，$c_{kk}=(G_{kk}-1)/4$。由 $G_j\equiv I-4b_jb_j^{\mathsf T}$ 得 $\bar c_{kl}=0$，$\sum_k\bar c_{kk}=\tau_j$。按引理 2.2，模 2 可解当且仅当 $\tau_j=0$；再由 (F3)(ii) 提升。取 $T_j=S_j^{-1}$ 即得 $\mathscr S_F(A)$ 中元素。∎

# 4 第 1 问的答案

**定理 4.1。**
1. **可行性判准**（与 $L$ 无关，只用 $A_j\bmod4$）：
$$\mathscr S_L(A)\ne\emptyset\iff\ \sum_{k\in I_j,\ m\notin I_j}(A_j)_{km}\equiv0\pmod 4\quad\text{对所有 }j .$$
   由于 $\sum_j\tau_j=0$，至多有 $r-1$ 个独立条件；$r=1$ 时恒可行。
2. $|\mathscr R_{L,M}(A)|=2^{\,r+e(M-1)\beta}$（可行时）；不可行时为 $0$。
3. $\mathscr C_{L,M}(A)$ 的基数：
   - $|\mathscr C_{L,2}(A)|=2^{\,e(d+\beta)}$，永不为空；
   - $M\ge3$ 时，可行则 $|\mathscr C_{L,M}(A)|=2^{\,e(d+(M-1)\beta)+r}$，不可行则为空。
4. **提升判准。** 对 $\bar U\in\mathscr C_{L,M}(A)$：
$$\bar U\in\mathscr R_{L,M}(A)\iff \sum_{l}\tilde U_{lk}^2\equiv1\pmod{2^{M+1}\mathcal O_L}\ \ (\forall k)\iff \bar U\text{ 可提升到 }\mathscr C_{L,M+1}(A).$$

*证明。*
- 1–3 由推论 1.4、命题 2.3 与定理 3.1 得到。
- 4 的 (⇒)：真解的列范数恰为 1。
- 4 的 (⇐)：由定理 3.1(iv) 先得可行。取 $U_0\in\mathscr S_L(A)$，则 $U_0^{\mathsf T}\bar U\in\prod_j C_{n_j}$，且列范数不变（$U_0$ 精确正交）。由命题 2.3(c)，它属于 $\prod_j\bar\Gamma_{n_j}$。∎

# 5 第 2 问

$\mathcal O_\mu/2^M$ 中 $\sigma$-不动的元素恰为 $a+2^{M-1}z\theta$，其中 $a\in\mathbb Z/2^M$、$z\in\mathbb F_2$。所以 $\sigma$-不动的矩阵可以唯一写成 $V+2^{M-1}\theta Z$，其中 $V\in M_d(\mathbb Z/2^M)$、$Z\in M_d(\mathbb F_2)$。记 $\partial(\bar U):=Z$。对满足 $\sigma U\equiv U\ (2^M)$ 的 $U$，有 $\partial=\frac{U-\sigma U}{2^M\theta}\bmod2$。

**定理 5.1（具体矩阵类）。**
- (a) 不需要可行性假设：
$$\mathscr C_{K_\mu,M}(A)^{\sigma}=\{V+2^{M-1}\theta Z:\ V\in\mathscr C_{F,M}(A),\ Z\in\mathrm{Sym}_{bd}\}.$$
- (b) 下面的映射是双射：
$$\mathscr R_{K_\mu,M}(A)^{\sigma}=\{W+2^{M-1}\omega_\mu Z:\ W\in\mathscr R_{F,M}(A),\ Z\in\mathrm{Alt}_{bd}\}.$$
  等价地，$\mathscr R^{\sigma}=\mathscr R_{F,M}(A)\cdot\mathcal J_M$，其中 $\mathcal J_M=\{J_Z=I+2^{M-1}\omega_\mu Z\}\cong(\mathrm{Alt}_{bd},+)$。
  - 当 $M\ge3$ 或 $\mu=2$ 时，也可写成 $\{W+2^{M-1}\theta Z\}$。
  - 当 $\mu=-1,M=2$ 时，它等于 $\{V+2iZ:\ Z\in\mathrm{Alt}_{bd},\ V\in\mathscr C_{F,2}(A),\ \nu_k(V)\equiv1+4\deg_Z(k)\ (8)\}$；有理部分 $V$ 可以不在 $\mathscr R_{F,2}$ 中。
- (c) **与基域集合的关系。** $\mathscr X^\sigma_{K,M}\cap M_d(\mathbb Z/2^M)=\ker\partial=\mathscr X_{F,M}$（$\mathscr X=\mathscr R,\mathscr C$）。$\partial$ 把 $\mathscr C^\sigma$ 映满 $\mathrm{Sym}_{bd}$、把 $\mathscr R^\sigma$ 映满 $\mathrm{Alt}_{bd}$，各纤维分别是 $\mathscr C_{F,M}$、$\mathscr R_{F,M}$ 的平移。所以 $\mathscr R^\sigma=\mathscr R_F\iff\beta=0$，而 $\mathscr C^\sigma\supsetneq\mathscr C_F$ 总成立。

*证明。*
- (a)：用 $\{1,\theta\}$ 分量展开 $\bar U^{\mathsf T}\bar U=I$ 与 $P_j\bar U=\bar UE_j$（由 $2^{2M-2}\equiv0$ 与 $V\equiv I\ (2)$）。有理部分给出 $V\in\mathscr C_F$，$\theta$ 部分给出 $Z+Z^{\mathsf T}=0$ 与 $E_jZ=ZE_j$。
- (b)：取提升 $\tilde V,\tilde Z$，则
$$\nu_k(\bar U)=\|\tilde V_k\|^2+2^M\theta\langle\tilde V_k,\tilde Z_k\rangle+2^{2M-2}\mu\|\tilde Z_k\|^2,\qquad \langle\tilde V_k,\tilde Z_k\rangle\equiv Z_{kk}\ (2).$$
  - 记 $\delta=[\mu=-1,M=2]$，最后一项模 $2^{M+1}$ 为 $-4\delta\|\tilde Z_k\|^2$。
  - 由定理 4.1(4)：$\bar U\in\mathscr R$ $\iff$ $Z_{kk}=0$，且 $\|\tilde V_k\|^2\equiv1+4\delta\deg_Z(k)$。
  - 令 $W=V-2^{M-1}\mu Z$。同样展开可得 $W\in\mathscr C_{F,M}(A)$，且 $\|\tilde W_k\|^2\equiv\|\tilde V_k\|^2-4\delta\deg_Z(k)\ (2^{M+1})$。所以上述条件等价于 $Z\in\mathrm{Alt}_{bd}$ 且 $W\in\mathscr R_{F,M}$，并且 $\bar U=W+2^{M-1}\omega_\mu Z$。反向的计算相同。∎

**定理 5.2（固定点数与轨道数）。** 在可行时：
- $|\mathscr R^\sigma_{K,M}|=2^{r+M\beta}$；
- $|\mathscr C^\sigma_{K,M}|=2^{2d+M\beta+r\varepsilon_M}$。

由 Burnside 引理（非固定点组成长度为 2 的自由轨道）：
- $\#\big(\mathscr R_{K,M}/\langle\sigma\rangle\big)=2^{r+M\beta-1}\big(2^{(M-2)\beta}+1\big)$；
- $\#\big(\mathscr C_{K,M}/\langle\sigma\rangle\big)=2^{2d+M\beta+r\varepsilon_M-1}\big(2^{(M-2)\beta}+1\big)$。

$M=2$ 或 $\beta=0$ 时全体都是固定点。不可行时：$\mathscr R$ 全为空；$M=2$ 时 $|\mathscr C_{K,2}|=|\mathscr C_{K,2}^\sigma|=2^{2(d+\beta)}$，且全部固定。

**定理 5.3（从精度 $M+1$ 到 $M$ 的约化）。**

| 映射 | 像 | 每个非空纤维的大小 |
|---|---|---|
| $\mathscr R_{L,M+1}\to\mathscr R_{L,M}$ | 满射 | $2^{e\beta}$ |
| $\mathscr C_{L,M+1}\to\mathscr C_{L,M}$ | $\mathscr R_{L,M}$ | $2^{e(d+\beta)}$ |
| $\mathscr R^\sigma_{K,M+1}\to\mathscr R^\sigma_{K,M}$ | $\mathscr R_{F,M}$ | $2^{2\beta}$ |
| $\mathscr C^\sigma_{K,M+1}\to\mathscr C^\sigma_{K,M}$ | $\mathscr R_{F,M}$ | $2^{2(d+\beta)}$ |

*证明。*
- 前两行：映射对 $\prod_j\bar\Gamma$ 与 $\prod_jC$ 等变，纤维是核的主齐性空间；再用命题 2.3(d) 与定理 4.1(4)。
- 后两行：$2^M\omega Z'\equiv2^M\theta Z'\equiv0\ (2^M)$，所以像就是有理部分的像。纤维大小为（有理部分纤维）×（$Z'$ 的个数）。∎

**定理 5.4（可提升的固定类）。** 在 $\mathscr X^\sigma_{K,M}$ 中，以下三类相同，都等于 $\mathscr R_{F,M}(A)$（共 $2^{r+(M-1)\beta}$ 个）：
- 能提升为 $\sigma$-固定真解的类（$\mathscr S_K(A)^\sigma=\mathscr S_F(A)$，因为 $\mathcal O^\sigma=\mathbb Z_2$）；
- 能作为一条逐层相容的固定类序列在精度 $M$ 的分量的类（$\varprojlim_N\mathscr C^\sigma_{K,N}=\varprojlim_N\mathscr R^\sigma_{K,N}=\mathscr S_F(A)$）；
- 在精度 $M+1$ 有固定提升的类。

可核验的判别：在 $\mathscr R^\sigma$ 中只需 $\partial=0$；在 $\mathscr C^\sigma$ 中需 $\partial=0$ 且所有 $\nu_k\equiv1\ (2^{M+1})$。$\partial\ne0$ 的 $\mathscr R^\sigma$ 中的类能提升为（非固定的）真解，但在精度 $M+1$ 已没有任何固定提升，障碍一步即显现。

*证明。* 由定理 5.3：任何相容序列在精度 $M$ 的分量落在精度 $M+1$ 固定集的像中，即 $\mathscr R_{F,M}$；反之，$\mathscr R_{F,M}$ 中每个元素来自某个 $W\in\mathscr S_F(A)$，取 $(W\bmod 2^N)_N$ 即可。∎

# 6 第 3 问

**定理 6.1。** 对任意 $\mu$ 和 $M\ge2$：
$$N_{\max}=\begin{cases}M,& \text{所有 } n_j=1,\\ M-1,&\text{某个 } n_j\ge2.\end{cases}$$
对给定的 $(A,U)$，可以取 $N=M$，当且仅当以下任一（彼此等价）条件成立：
- $\partial(U\bmod2^M)=0$；
- $U\bmod 2^M\in M_d(\mathbb Z/2^M)$；
- $\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}$。

*证明。*
- **下界 $N\ge M-1$。** 由定理 5.1(b)，$U\bmod2^M=W_0+2^{M-1}\omega Z$，其中 $W_0\in\mathscr R_{F,M}$。取 $W\in\mathscr S_F(A)$ 提升 $W_0$，则 $U\equiv W\ (2^{M-1})$。这也用到了可行性在三个域之间的传递（定理 3.1）。
- **$N=M$ 的判据。** 若 $W\equiv U\ (2^M)$ 且 $W$ 有理，则 $\partial=0$；反之 $\partial=0$ 时 $U\bmod 2^M\in\mathscr R_{F,M}$。写 $U=U_0+\theta U_1$：前提给出 $U_1\in2^{M-1}M_d(\mathbb Z_2)$，而 $\partial=0\iff U_1\in2^M M_d(\mathbb Z_2)\iff 2\theta U_1\in2^{M+1}M_d(\mathcal O)$。对 $\mu=2$ 的最后一步用到 $\sqrt2 U_1$ 的有理分量为 0、$\theta$ 分量为 $U_1$。
- **精确下降。** 若所有 $n_j=1$，则 $\Gamma_1(L)=\{\pm1\}$。于是 $\mathscr S_K(A)=U_0\{\pm1\}^d=\mathscr S_F(A)$，取 $W=U$ 即可，对任意 $N$ 成立。
- **最优性（统一构造）。** 取 $A_i=E_i$，$p\ne q$ 属于同一个块 $I_j$（$n_j\ge2$）。
  - 令 $b_M=2^{M-1}\omega_\mu$，则 $v_\pi(b_M)=2M-1\ge3$。
  - 对 $f(x)=x^2+b_M^2-1$ 用 (F3′)：$v_\pi(f(1))=4M-2>4=2v_\pi(f'(1))$，得根 $a_M\in1+2^{2M-2}\mathcal O$。
  - 令 $U_M=I+(a_M-1)(e_pe_p^{\mathsf T}+e_qe_q^{\mathsf T})+b_M(e_qe_p^{\mathsf T}-e_pe_q^{\mathsf T})$。则 $U_M\in\mathscr S_{K_\mu}(E)$，且 $U_M\equiv I+b_M(e_qe_p^{\mathsf T}-e_pe_q^{\mathsf T})\ (2^M)$。
  - $\sigma(b_M)-b_M=-2^M\theta\equiv0$，所以 $\sigma U_M\equiv U_M\ (2^M)$。
  - 但 $(U_M)_{qp}=b_M$ 的 $\theta$ 分量为 $2^{M-1}\not\equiv0\ (2^M)$，所以不存在 $W\in M_d(\mathbb Z_2)$ 使 $W\equiv U_M\ (2^M)$。另一方面 $W=I$ 满足 $W\equiv U_M\ (2^{M-1})$。
  - $\mu=-1,M=2$ 时即为 $\begin{pmatrix}1&2+2i\\2+2i&1\end{pmatrix}\bmod4$，它的有理部分 $\begin{pmatrix}1&2\\2&1\end{pmatrix}$ 的列范数为 $5\not\equiv1\ (8)$，正是定理 5.1(b) 中的扭曲情形。∎

# 7 否定结论的具体例子

- **不可行（但 $\mathscr C_{L,2}\ne\emptyset$）。** $d=r=2$，$A_1=\tfrac15\begin{pmatrix}1&2\\2&4\end{pmatrix}$，$A_2=I-A_1$。两者对称、交换，且 $A_i\equiv E_i\ (2)$。此时 $\tau_1=\tfrac15\equiv1$，三个域上都无解；直接看：需要 $\lambda^2=1/5\equiv5\ (8)$，不可能。但 $U_*\bmod4=\begin{pmatrix}1&2\\2&1\end{pmatrix}\in\mathscr C_{L,2}$，其列范数 $\equiv5\ (8)$，与定理 4.1(4) 一致。
- **$\mathscr C\supsetneq\mathscr R$。** $d=1$ 时，$3\in\mathscr C_{F,3}$，但 $9\not\equiv1\ (16)$，故 $3\notin\mathscr R_{F,3}=\{1,7\}$。
- **不可下降的固定类。** 任意 $J_Z$（$Z\ne0$），以及第 6 节的族 $U_M$，对每个 $M$ 都成立。