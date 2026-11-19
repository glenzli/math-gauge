# 序列空间上取样映射 $T_f$ 的解答

**记号。** 对严格递增的 $f$，令
$$
c_f:=\limsup_{N\to\infty}\frac{f(N)}{N}\in[1,+\infty],\qquad A:=f(\mathbb N).
$$

## 结论

**第 1 问**
- $T_f$ 有定义，当且仅当 $c_f<\infty$。这等价于 $\sup_N f(N)/N<\infty$，也等价于 $A$ 的下密度为正；事实上 $\underline d(A)=1/c_f$。
- 对每个允许的 $f$：
  - $T_f$ 总是连续的，而且是 Lipschitz 映射，最小 Lipschitz 常数恰为 $c_f$。这个常数总是有限的，因此约定中的 $+\infty$ 不会出现。
  - $T_f$ 总是满射。
  - $T_f$ 是单射，当且仅当 $c_f=1$。这等价于 $f(N)/N\to1$，也等价于 $\mathbb N\setminus A$ 的密度为 $0$。此时 $T_f$ 是等距映射。

**第 2 问**
- $L_k=\limsup_N f^{\circ k}(N)/N$，其中 $f^{\circ k}$ 表示 $f$ 的 $k$ 次复合。
- $R_f=\lim_k L_k^{1/k}=\inf_k L_k^{1/k}$ 存在。
- 全部可能的有序对为
$$
\{(a,b)\in\mathbb R^2:\ 1\le b\le a<\infty\}.
$$
- 对 $1\le r\le c<\infty$，取
$$
f(n)=\lceil rn\rceil+\lceil (c-r)\,j!\rceil\qquad (j!\le n<(j+1)!,\ j\ge1),
$$
则 $(L_1,R_f)=(c,r)$。

---

## 0. 预备

**(0.1) 半范数与商空间。** 令 $\rho(z):=\limsup_N\frac1N\sum_{j\le N}|z_j|$。它满足：
- $0\le\rho(z)\le\|z\|_\infty$；
- $\rho(z+w)\le\rho(z)+\rho(w)$；
- $\rho(tz)=|t|\rho(z)$。

并且 $d(x,y)=\rho(x-y)$。于是 $Z:=\{\rho=0\}$ 是线性子空间，$x\sim y\iff x-y\in Z$，$X=E/Z$ 是向量空间，且 $\bar d([x],[y])=\rho(x-y)$。

**(0.2) $P_f$ 的基本性质。**
- $P_f$ 是线性的，且 $\|P_fz\|_\infty\le\|z\|_\infty$。
- 由 $f(1)\ge1$ 和 $f(N+1)\ge f(N)+1$，归纳得 $f(N)\ge N$，故 $c_f\ge1$。
- 由 $(P_f(P_gx))_j=x_{g(f(j))}$ 得 $P_fP_g=P_{g\circ f}$，因此 $P_f^k=P_{f^{\circ k}}$。

**(0.3) 良定义的判据。** $T_f$ 有定义当且仅当 $P_f(Z)\subseteq Z$。
- 若 $P_f(Z)\subseteq Z$ 且 $x\sim y$，则 $P_fx-P_fy=P_f(x-y)\in Z$。
- 反之，若 $T_f$ 有定义且 $z\in Z$，由 $z\sim0$ 得 $P_fz\sim P_f0=0$。

有定义时，$T_f$ 是线性的，并且 $\bar d(T_f[x],T_f[y])=\rho(P_f(x-y))$。

**(0.4) 上极限的乘积。** 若 $a_N,b_N\ge0$ 且上极限 $a,b$ 都有限，则 $\limsup a_Nb_N\le ab$。理由：对任意 $\varepsilon>0$，最终有 $a_Nb_N\le(a+\varepsilon)(b+\varepsilon)$。

**(0.5) 示性函数。** 对 $S\subseteq\mathbb N$，$\rho(\mathbf 1_S)=\limsup_M|S\cap[1,M]|/M$。由于 $f$ 是单射，对 $J\subseteq\mathbb N$ 有 $P_f\mathbf 1_{f(J)}=\mathbf 1_J$。

## 1. 第 1 问

**引理 1（上界）。** 若 $c_f<\infty$，则对所有 $z\in E$ 有 $\rho(P_fz)\le c_f\,\rho(z)$。

*证明。* $f(1),\dots,f(N)$ 是 $[1,f(N)]$ 中互不相同的整数，所以
$$
\frac1N\sum_{j\le N}|z_{f(j)}|\le\frac{f(N)}N\cdot\sigma_{f(N)},\qquad \sigma_M:=\frac1M\sum_{i\le M}|z_i|.
$$
$(\sigma_{f(N)})_N$ 是 $(\sigma_M)$ 的子列，故 $\limsup_N\sigma_{f(N)}\le\rho(z)$。由 (0.4) 即得结论。∎

**引理 2。** 若 $c_f=\infty$，则存在 $B\subseteq\mathbb N$，使得 $\rho(\mathbf 1_B)=0$ 而 $\rho(P_f\mathbf 1_B)=1$。

*证明。*

*构造。* 对任意 $K$，集合 $\{N:f(N)\ge KN\}$ 都是无限集。约定 $N_0=m_0=0$，记 $S_{k-1}=m_1+\dots+m_{k-1}$。归纳地选取 $N_k$，使得
$$
N_k>N_{k-1}+m_{k-1},\qquad N_k\ge kS_{k-1},\qquad f(N_k)\ge k^2N_k,
$$
再令 $m_k=\lceil f(N_k)/k\rceil$。令 $J_k=\{N_k+1,\dots,N_k+m_k\}$，$J=\bigcup_k J_k$，$B=f(J)$。

*$P_f\mathbf 1_B$ 的密度为 1。* 由 (0.5)，$P_f\mathbf 1_B=\mathbf 1_J$。又 $N_k\le f(N_k)/k^2\le m_k/k$，所以
$$
\rho(\mathbf 1_J)\ge\limsup_k\frac{m_k}{N_k+m_k}\ge\limsup_k\frac{k}{k+1}=1.
$$

*$B$ 的密度为 0。*
- 若 $M\le f(N_1)$，则 $B\cap[1,M]=\varnothing$。
- 若 $M>f(N_1)$，令 $k$ 为满足 $f(N_k)<M$ 的最大下标。对 $i>k$，$f(J_i)$ 中的元素都大于 $f(N_{k+1})\ge M$，所以 $|B\cap[1,M]|\le S_{k-1}+m_k$。
- 又 $M>f(N_k)\ge N_k\ge kS_{k-1}$，且 $m_k<M/k+1$，于是
$$
\frac{|B\cap[1,M]|}M\le\frac2k+\frac1M.
$$
- 当 $M\to\infty$ 时 $k\to\infty$，故 $\rho(\mathbf 1_B)=0$。∎

**定理 1。** $T_f$ 有定义 $\iff c_f<\infty$。

*证明。*
- 若 $c_f<\infty$，由引理 1 得 $P_f(Z)\subseteq Z$。
- 若 $c_f=\infty$，引理 2 给出 $\mathbf 1_B\sim0$，但 $P_f\mathbf 1_B\not\sim 0=P_f0$。

再由 (0.3) 得结论。∎

**附注（下密度表述）。** 当 $f(N)\le M<f(N+1)$ 时，
$$
\frac{N}{f(N+1)}<\frac{|A\cap[1,M]|}{M}\le\frac{N}{f(N)},
$$
且在 $M=f(N)$ 处取到右端。因此 $\underline d(A)=\liminf_N N/f(N)=1/c_f$（约定 $1/\infty=0$）。

以下各结论均设 $c:=c_f<\infty$。

**引理 3（下界）。** 对每个 $\eta\in(0,1)$，存在 $B$，使得
$$
\rho(P_f\mathbf 1_B)\ge\frac{\eta}{1+\eta},\qquad \rho(\mathbf 1_B)\le\frac{\eta}{c+\eta}.
$$

*证明。*

*构造。* 记 $p_k=\lfloor\eta N_k\rfloor$，$S_{k-1}=p_1+\dots+p_{k-1}$。归纳地选取 $N_k$，使得
$$
N_k>N_{k-1}+p_{k-1},\qquad N_k\ge kS_{k-1},\qquad f(N_k)\ge(c-1/k)N_k.
$$
这是可行的，因为满足最后一个条件的 $N$ 有无穷多个。令 $J_k=\{N_k+1,\dots,N_k+p_k\}$，$J=\bigcup_k J_k$，$B=f(J)$。

*$P_f\mathbf 1_B$ 的估计。* $P_f\mathbf 1_B=\mathbf 1_J$。由 $p_k\ge\eta N_k-1$ 得
$$
\rho(\mathbf 1_J)\ge\limsup_k\frac{p_k}{N_k+p_k}\ge\frac{\eta}{1+\eta}.
$$

*$B$ 的估计。* 对 $M>f(N_1)$，令 $k$ 为满足 $f(N_k)<M$ 的最大下标（若 $M\le f(N_1)$，则 $B\cap[1,M]=\varnothing$）。
- 与引理 2 同理，下标 $i>k$ 的块不贡献元素。
- 设 $f(J_k)$ 中有 $t$ 个元素 $\le M$。由单调性，它们是 $f(N_k+1),\dots,f(N_k+t)$，所以 $M\ge f(N_k+t)\ge f(N_k)+t$；当 $t=0$ 时这也成立。
- 利用 $t\mapsto\frac{t}{a+t}$ 关于 $t$ 递增、关于 $a$ 递减，得
$$
\frac{|B\cap[1,M]|}{M}\le\frac{S_{k-1}}{N_k}+\frac{t}{f(N_k)+t}\le\frac1k+\frac{\eta N_k}{(c-\frac1k)N_k+\eta N_k}=\frac1k+\frac{\eta}{c-\frac1k+\eta}.
$$
- 令 $M\to\infty$（从而 $k\to\infty$），即得 $\rho(\mathbf 1_B)\le\frac{\eta}{c+\eta}$。∎

**定理 2（Lipschitz 常数与连续性）。** $T_f$ 的最小 Lipschitz 常数等于 $c_f$。特别地，$T_f$ 连续。

*证明。*
- 由引理 1，$\bar d(T_fu,T_fv)\le c\,\bar d(u,v)$。
- 设 $L$ 是任意一个 Lipschitz 常数。由引理 3，
$$
\frac{\eta}{1+\eta}\le L\cdot\frac{\eta}{c+\eta},\quad\text{即}\quad L\ge\frac{c+\eta}{1+\eta}.
$$
令 $\eta\to0^+$ 得 $L\ge c$。∎

**定理 3（满射性）。** $T_f$ 是满射。

*证明。* 给定 $y\in E$，令 $x_{f(j)}=y_j$，且对 $i\notin A$ 令 $x_i=0$。则 $x\in E$，$P_fx=y$，从而 $T_f[x]=[y]$。∎

**定理 4（单射性）。** $T_f$ 是单射 $\iff c_f=1$，并且此时 $T_f$ 是等距映射。

*证明。*

*若 $c_f>1$，则不是单射。* 取 $z=\mathbf 1_{\mathbb N\setminus A}$，则 $P_fz=0$。在 $M=f(N)$ 处，$[1,M]$ 中不属于 $A$ 的整数有 $f(N)-N$ 个，所以
$$
\rho(z)\ge\limsup_N\Bigl(1-\frac{N}{f(N)}\Bigr)=1-\frac1{c_f}>0.
$$
于是 $[z]\ne0$ 而 $T_f[z]=0$，$T_f$ 不是单射。

*若 $c_f=1$，则是等距。* 由于 $f(n)/n\ge1$ 且其上极限为 $1$，有 $f(n)/n\to1$。对 $M\ge f(1)$，令 $N=|A\cap[1,M]|$，则 $f(N)\le M<f(N+1)$。于是
$$
\frac1M\sum_{i\le M}|z_i|\le\frac1N\sum_{j\le N}|z_{f(j)}|+\|z\|_\infty\Bigl(1-\frac{N}{f(N+1)}\Bigr).
$$
当 $M\to\infty$ 时 $N\to\infty$，且 $\frac{N}{f(N+1)}=\frac{N}{N+1}\cdot\frac{N+1}{f(N+1)}\to1$，所以 $\rho(z)\le\rho(P_fz)$。结合引理 1 的 $\rho(P_fz)\le\rho(z)$，得 $\rho(P_fz)=\rho(z)$，即 $T_f$ 是等距，从而是单射。∎

## 2. 第 2 问

**命题 5。** 对允许的 $f$：
- $T_f^k=T_{f^{\circ k}}$；
- $L_k=c_{f^{\circ k}}$；
- $1\le L_k\le L_1^k$；
- $L_{k+m}\le L_kL_m$。

*证明。*
- 由 (0.2)，$T_f^k[x]=[P_f^kx]=[P_{f^{\circ k}}x]$。
- $T_f^k$ 作为 Lipschitz 映射的复合，有常数 $L_1^k$，所以 $L_k\le L_1^k<\infty$。另一方面 $T_f^k=T_{f^{\circ k}}$，于是 $f^{\circ k}$ 是允许的，由定理 2 得 $L_k=c_{f^{\circ k}}$。
- 由 $f^{\circ k}(N)\ge N$ 得 $L_k\ge1$。
- 由 $T_f^{k+m}=T_f^k\circ T_f^m$ 得 $L_{k+m}\le L_kL_m$。∎

**命题 6（极限存在）。** $R_f=\lim_k L_k^{1/k}$ 存在，等于 $\inf_k L_k^{1/k}$，且 $1\le R_f\le L_1$。

*证明（Fekete 引理）。*
- 令 $a_k=\log L_k\ge0$，它是次可加的。约定 $a_0=0$，令 $\lambda=\inf_k a_k/k$。
- 固定 $m$。对 $k=qm+s$（$0\le s<m$），有 $a_k\le qa_m+a_s$，所以
$$
\frac{a_k}{k}\le\frac{qm}{k}\cdot\frac{a_m}{m}+\frac{\max_{s<m}a_s}{k}.
$$
- 因此 $\limsup_k a_k/k\le a_m/m$。对 $m$ 取下确界，得 $\limsup_k a_k/k\le\lambda\le\liminf_k a_k/k$。
- 故 $R_f=e^\lambda=\inf_k L_k^{1/k}$，它介于 $1$ 与 $L_1$ 之间。∎

因此每个允许的 $f$ 都满足 $1\le R_f\le L_1<\infty$。

**命题 7（构造）。** 设 $1\le r\le c<\infty$。对 $n\in\mathbb N$，令 $\nu(n)=j!$，其中 $j\ge1$ 满足 $j!\le n<(j+1)!$。定义
$$
f(n)=\lceil rn\rceil+\lceil (c-r)\nu(n)\rceil .
$$
则 $L_1=c$，$R_f=r$。特别地，$r=c$ 时 $f(n)=\lceil cn\rceil$；$r=1$ 时 $f(n)=n+\lceil (c-1)\nu(n)\rceil$。

*证明。*

*$f$ 严格递增。* 由 $r\ge1$ 得 $\lceil r(n+1)\rceil\ge\lceil rn\rceil+1$；又 $\nu$ 不减。所以 $f$ 严格递增，且取值在 $\mathbb N$ 中。

*基本估计。* 由 $\nu(n)\le n$ 得
$$
rn+(c-r)\nu(n)\le f(n)\le rn+(c-r)\nu(n)+2\le cn+2.
$$

*$L_1=c$。* 由 $f(n)/n\le c+2/n$ 得 $c_f\le c$；由 $f(j!)\ge c\,j!$ 得 $c_f\ge c$。所以 $c_f=c<\infty$，$f$ 是允许的，并由定理 2 得 $L_1=c$。

*下界 $R_f\ge r$。* 由 $f(m)\ge rm$ 得 $f^{\circ k}(n)\ge r^kn$，故 $L_k\ge r^k$，$R_f\ge r$。

*上界 $R_f\le r$。* 固定 $k$，令 $D=c-r+2$，并取 $j_0$ 使 $j_0+2\ge(c+2)^k$。
- 设 $n\ge j_0!$，且 $j!\le n<(j+1)!$，则 $j\ge j_0$。令 $m_0=n$，$m_{i+1}=f(m_i)$。
- 由 $f(m)\le(c+2)m$ 得，对 $i\le k$，
$$
j!\le m_i\le (c+2)^kn<(j+2)(j+1)!=(j+2)!,
$$
所以 $\nu(m_i)\in\{j!,(j+1)!\}$。
- 令 $s$ 为满足 $m_i<(j+1)!$ 的下标个数，有 $s\ge1$。
- 对 $i<s$：$\nu(m_i)=j!\le n$，故 $m_{i+1}\le rm_i+(c-r)n+2\le rm_i+Dn$。
- 对 $s\le i<k$：$\nu(m_i)=(j+1)!\le m_s$，故 $m_{i+1}\le rm_i+Dm_s$。
- 若 $u_{i+1}\le ru_i+Dv$ 对 $i<t$ 成立，则由 $r\ge1$ 得 $u_t\le r^tu_0+Dv\sum_{l<t}r^l\le r^t(u_0+tDv)$。
- 由此，若 $s\le k$，则 $m_s\le r^sn(1+sD)$，且
$$
m_k\le r^{k-s}m_s\bigl(1+(k-s)D\bigr)\le r^kn(1+kD)^2;
$$
若 $s>k$，则 $m_k\le r^kn(1+kD)$。
- 因此对所有 $n\ge j_0!$ 有 $f^{\circ k}(n)/n\le r^k(1+kD)^2$，即 $L_k\le r^k(1+kD)^2$。
- 于是 $L_k^{1/k}\le r(1+kD)^{2/k}\to r$。

综合两方面，$R_f=r$。∎

**第 2 问结论。** 由命题 6，每个允许的 $f$ 都满足 $1\le R_f\le L_1<\infty$；由命题 7，每个满足 $1\le b\le a<\infty$ 的实数对 $(a,b)$ 都能实现。所以全部可能的有序对恰为
$$
\{(L_1,R_f)\}=\{(a,b):1\le b\le a<\infty\}.
$$
对 $(a,b)$，取命题 7 中 $c=a$、$r=b$ 的函数即可。