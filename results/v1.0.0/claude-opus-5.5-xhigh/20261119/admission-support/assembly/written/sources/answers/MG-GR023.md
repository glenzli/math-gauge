# 有限测试记录与群作用：分类、构造与证明

## 结论一览

1. **$R_m(X)$ 的分类。**
   - $R_m(\varnothing)=\varnothing$。
   - 设 $X\neq\varnothing$：$R_1(X)$ 是单点集；$R_2(X)$ 与 $X$ 上的“自对偶族”一一对应；当 $m\ge 3$（含 $\infty$）时，$R_m(X)$ 与超滤子集合 $\beta X$ 一一对应。
   - 当 $k\ge3$ 时 $q_{m,k}$ 是双射。当 $m\geq 3$ 时，$q_{m,2}$ 是单射，它的像恰为超滤子；它是满射当且仅当 $|X|\le2$。$q_{m,1}$ 映到单点。
   - 有限 $G$ 集合 $X$ 的不动记录：
     - $|R_1(X)^G|=[X\ne\varnothing]$；
     - $m\ge3$ 时 $|R_m(X)^G|=|X^G|$；
     - $R_2(X)^G\ne\varnothing$ 当且仅当每个 $g_X$ 都有奇数长的轮换，此时 $|R_2(X)^G|=2^{|\mathcal P(X)/G|/2-1}$。
   - 第 2 层的不动记录能延拓为完整不动记录，当且仅当它是某个 $G$ 不动点处的主族。
2. **完整不动记录的空间。**
   - $R_\infty(X)^G$ 与 $\beta_GX=\{\mathcal U\in\beta X:\ X^g\in\mathcal U\ \forall g\}$ 同胚。
   - $R_\infty(X)^G$ 非空，当且仅当每个有限生成子群 $H$ 都满足 $X^H\neq\varnothing$。
   - $\overline{\eta(X^G)}=\{r: r_2(\chi_{X^G})=1\}\cong\beta(X^G)$。它等于 $R_\infty(X)^G$，当且仅当存在有限生成子群 $H$ 使 $X^H=X^G$。
   - 对每个 $G$ 集合都成立该等式的群恰为有限生成群。
   - 可数例：有限子集群 $(\mathcal P_{\rm fin}(\mathbb N),\triangle)$ 作用于 $\mathbb N$。此时 $X^G=\varnothing$，不动记录恰为 $\mathbb N$ 上的全体非主超滤子，共 $2^{\mathfrak c}$ 个。
3. **乘积比较。**
   - $\Pi$ 良定义、连续，并且总是满射。
   - 平凡群时，$\Pi_{X,Y}$ 是单射当且仅当 $X$ 或 $Y$ 有限。
   - 命题“至少一个因子有限 ⟹ 双射”为**真**。
   - 命题“$X^G=Y^G=\varnothing$ ⟹ 单射”为**假**。

---

## 记号与标准事实

**示性函数与 $\mathcal U_r$。** $[2]=\{0,1\}$。$\chi_A:X\to[2]$ 是 $A\subseteq X$ 的示性函数。$A\mapsto\chi_A$ 是 $\mathcal P(X)\to\mathrm{Map}(X,[2])$ 的双射，且 $\chi_B\circ h=\chi_{h^{-1}(B)}$。对 $S\subseteq[n]$ 同样记 $\chi_S:[n]\to[2]$。当 $m\ge2$ 且 $r\in R_m(X)$ 时，令 $\mathcal U_r=\{A\subseteq X: r_2(\chi_A)=1\}$。

**超滤子。** 超滤子是满足以下条件的 $\mathcal U\subseteq\mathcal P(X)$：$\varnothing\notin\mathcal U$；对有限交与取超集封闭；对每个 $A$，$A$ 与 $X\setminus A$ 中至少一个属于 $\mathcal U$。超滤子全体记为 $\beta X$（$\beta\varnothing=\varnothing$）。主超滤子记为 $\delta_x=\{A:x\in A\}$。记 $\widehat A=\{\mathcal U\in\beta X:A\in\mathcal U\}$。

**自对偶族。** $\mathcal S(X)$ 是满足以下条件的 $\mathcal U\subseteq\mathcal P(X)$ 的全体：$\varnothing\notin\mathcal U$，且对每个 $A$ 有 $A\in\mathcal U\iff X\setminus A\notin\mathcal U$。显然 $\beta X\subseteq\mathcal S(X)$。取 $A=\varnothing=X\setminus A$ 即得矛盾，故 $\mathcal S(\varnothing)=\varnothing$。

**推前。** $h_*\mathcal U=\{B: h^{-1}(B)\in\mathcal U\}$。$h^{-1}$ 保持 $\varnothing$、补、交和包含，所以 $h_*$ 把 $\beta X$ 映到 $\beta Y$，把 $\mathcal S(X)$ 映到 $\mathcal S(Y)$。并且 $(h'h)_*=h'_*h_*$，$h_*\delta_x=\delta_{h(x)}$。对置换 $\sigma$ 有 $\sigma_*\mathcal U=\{\sigma(A):A\in\mathcal U\}$。

**不动点集。** $X^g=\{x:gx=x\}$，$X^H=\bigcap_{h\in H}X^h$。有 $X^{g_1}\cap\dots\cap X^{g_k}=X^{\langle g_1,\dots,g_k\rangle}$；$k=0$ 时两边都等于 $X=X^{\{1\}}$。

**标准事实。**
- **(U1)** 设 $\mathcal U\in\beta X$，$B\in\mathcal U$，$B=A_1\sqcup\dots\sqcup A_k$（有限不交并，允许空块）。则恰有一个 $A_j\in\mathcal U$。
  - 至多一个：两个不交成员之交为 $\varnothing$。
  - 至少一个：否则诸 $X\setminus A_j$ 与 $B$ 之交 $=\varnothing$ 属于 $\mathcal U$。
- **(U2)** 若超滤子满足 $\mathcal U\subseteq\mathcal V$，则 $\mathcal U=\mathcal V$。否则取 $B\in\mathcal V\setminus\mathcal U$，则 $X\setminus B\in\mathcal U\subseteq\mathcal V$，矛盾。
- **(U3) 超滤子引理（ZFC）。** 具有有限交性质的族含于某个超滤子。推论：若 $\mathcal F$ 是滤子且 $S\notin\mathcal F$，则存在超滤子 $\mathcal U\supseteq\mathcal F$ 且 $X\setminus S\in\mathcal U$。理由：若 $\mathcal F\cup\{X\setminus S\}$ 无有限交性质，则某 $F\in\mathcal F$ 满足 $F\subseteq S$，于是 $S\in\mathcal F$。
- **(U4)** 有限 $X$ 上的超滤子都是主超滤子（对单点划分用 (U1)），且 $x\mapsto\delta_x$ 是单射。一般地，一个超滤子含全部余有限集当且仅当它非主：若它含有限集，由 (U1) 它含某个 $\{x\}$，再由 (U2) 它等于 $\delta_x$。
- **(U5) Pospíšil 定理。** $X$ 无限时 $|\beta X|=2^{2^{|X|}}$。

## 0. 基本引理

**引理 0.1（函子性与等变性）。**
- (a) $R_m(h)$ 良定义；$R_m(\mathrm{id})=\mathrm{id}$，$R_m(h'h)=R_m(h')R_m(h)$。因此 $g\cdot r$ 是左作用。
- (b) $\eta_{m,X}(x)\in R_m(X)$。并且 $q_{k,l}q_{m,k}=q_{m,l}$，$q_{m,k}R_m(h)=R_k(h)q_{m,k}$，$q_{m,k}\eta_{m,X}=\eta_{k,X}$，$R_m(h)\eta_{m,X}=\eta_{m,Y}h$。
- (c) $G$ 等变映射 $h$ 给出等变的 $R_m(h)$；$q_{m,k}$ 与 $\eta$ 等变。因此它们把不动点送到不动点，特别地 $\eta_{m,X}(X^G)\subseteq R_m(X)^G$。

*证明。*
- (a) 自然性：$a\big((R_m(h)r)_n(f)\big)=a(r_n(fh))=r_k(afh)=(R_m(h)r)_k(af)$。函子性：$(R_m(h')R_m(h)r)_n(f)=r_n(fh'h)$。于是 $g\cdot(g'\cdot r)=(gg')\cdot r$。
- (b) $a(f(x))=(af)(x)$ 给出 $\eta_{m,X}(x)$ 的自然性。其余等式在每个坐标 $(n,f)$ 上两边相同，例如 $(R_m(h)\eta_{m,X}(x))_n(f)=f(h(x))$。
- (c) 由 $hg_X=g_Yh$ 得 $R(h)R(g_X)=R(g_Y)R(h)$。再对 $h=g_X$ 应用 (b)。∎

**引理 0.2（三染色）。** 若 $\sigma$ 是 $Y$ 的无不动点置换，则存在划分 $Y=C_0\sqcup C_1\sqcup C_2$，使 $\sigma(C_j)\cap C_j=\varnothing$。

*证明。* 用选择公理在每个 $\langle\sigma\rangle$ 轨道中选一个基点 $y$。
- 无限轨道 $\{\sigma^jy\}_{j\in\mathbb Z}$：给 $\sigma^jy$ 染色 $j\bmod2$。
- 长度为偶数 $\ell$ 的轨道：给 $\sigma^jy$（$0\le j<\ell$）染色 $j\bmod 2$。
- 长度为奇数 $\ell\ge3$ 的轨道：$j\le\ell-2$ 时染色 $j\bmod2$，$\sigma^{\ell-1}y$ 染色 $2$。
- 由于没有不动点，不存在 $\ell=1$。

逐一检查可知 $z$ 与 $\sigma z$ 总是异色。∎

**引理 0.3（不变性判据）。** 设 $\sigma$ 是 $X$ 的置换，$\mathcal U\in\beta X$。则 $\sigma_*\mathcal U=\mathcal U\iff X^\sigma\in\mathcal U$。

*证明。*
- (⇐) 设 $F=X^\sigma\in\mathcal U$。若 $A\in\mathcal U$，则 $A\cap F\in\mathcal U$ 且 $A\cap F\subseteq\sigma^{-1}(A)$，所以 $A\in\sigma_*\mathcal U$。于是 $\mathcal U\subseteq\sigma_*\mathcal U$，由 (U2) 二者相等。
- (⇒) 设 $F\notin\mathcal U$，则 $Y=X\setminus F\in\mathcal U$，且 $\sigma|_Y$ 无不动点。取引理 0.2 的划分；由 (U1)，某个 $C_j\in\mathcal U$。若 $\sigma_*\mathcal U=\mathcal U$，则 $\sigma(C_j)\in\mathcal U$，于是 $\varnothing=C_j\cap\sigma(C_j)\in\mathcal U$，矛盾。∎

## 1. 截断及其相容关系

**(★) 关键公式。** 设 $m\ge2$，$r\in R_m(X)$，$1\le n\le m$，$f:X\to[n]$，$i\in[n]$。则 $r_n(f)=i\iff f^{-1}(i)\in\mathcal U_r$。

*证明。* 取 $a=\chi_{\{i\}}:[n]\to[2]$，则 $a\circ f=\chi_{f^{-1}(i)}$，于是 $r_2(\chi_{f^{-1}(i)})=a(r_n(f))$。∎

**定理 1.1（分类）。**
- (i) 对一切 $m$，$R_m(\varnothing)=\varnothing$。
- (ii) $X\ne\varnothing$ 时，$R_1(X)$ 只有一个元素（$r_0$ 为空映射，$r_1\equiv0$）。
- (iii) $X\neq\varnothing$ 时，$\Phi_2:R_2(X)\to\mathcal S(X)$，$r\mapsto\mathcal U_r$ 是双射。
- (iv) 当 $m\ge3$（含 $\infty$）时，$\Phi_m:r\mapsto\mathcal U_r$ 是双射 $R_m(X)\to\beta X$。其逆为 $\mathcal U\mapsto r^{\mathcal U}$，其中 $r^{\mathcal U}_n(f)$ 是唯一使 $f^{-1}(i)\in\mathcal U$ 的 $i$（即 $f$ 的 $\mathcal U$-极限）。
- **基数**（$|X|=N$ 有限且 $N\geq 1$ 时）：$|R_1|=1$，$|R_2|=2^{2^{N-1}-1}$，$|R_{m\ge3}|=N$。$X$ 无限时：$|R_2(X)|=|R_{m\geq 3}(X)|=2^{2^{|X|}}$。

*证明。*

(i) $\mathrm{Map}(\varnothing,[0])$ 是单点集，而 $[0]=\varnothing$，所以 $r_0$ 不存在。

(ii) $X\ne\varnothing$ 时 $\mathrm{Map}(X,[0])=\varnothing$，$\mathrm{Map}(X,[1])$ 是单点集，所以 $r_0,r_1$ 唯一。当 $n,k\le1$ 时，自然性条件要么是空的（$n=0$ 时没有 $f$；$k=0<n$ 时没有 $a$），要么是平凡的。

(iii) 逐一列出 $n,k\le2$ 的条件。凡涉及 $n=0$、$k=0$ 或 $k=1$ 的条件都是空的或平凡的。
- $n=1,\ k=2$：给出 $r_2(\chi_\varnothing)=0$ 和 $r_2(\chi_X)=1$。
- $n=k=2$，$a$ 为常值映射：给出同样的条件。
- $n=k=2$，$a(i)=1-i$：给出 $r_2(\chi_{X\setminus A})=1-r_2(\chi_A)$。

因此 $R_2(X)$ 恰好对应满足 $\varphi(\varnothing)=0$ 和 $\varphi(X\setminus A)=1-\varphi(A)$ 的函数 $\varphi:\mathcal P(X)\to[2]$（这两条推出 $\varphi(X)=1$），也就是对应 $\mathcal S(X)$。

(iv) 由 (★)，$r$ 被 $\mathcal U_r$ 决定（$r_0$ 是空映射），所以 $\Phi_m$ 是单射。由 (iii)，$\mathcal U_r\in\mathcal S(X)$。
- 对划分 $X=P_0\sqcup P_1\sqcup P_2$，取 $f|_{P_j}\equiv j$。由 (★)，恰有一个 $P_j\in\mathcal U_r$。
- 取超集封闭：设 $A\in\mathcal U_r$，$A\subseteq B$。考虑划分 $A,\ B\setminus A,\ X\setminus B$，得 $X\setminus B\notin\mathcal U_r$，所以 $B\in\mathcal U_r$。
- 交封闭：设 $A,B\in\mathcal U_r$。考虑划分 $A\cap B,\ A\setminus B,\ X\setminus A$。若 $A\setminus B\in\mathcal U_r$，则其超集 $X\setminus B\in\mathcal U_r$，与 $B\in\mathcal U_r$ 矛盾。所以 $A\cap B\in\mathcal U_r$。
- 因此 $\mathcal U_r$ 是超滤子。
- 反之，对 $\mathcal U\in\beta X$，由 (U1)，$r^{\mathcal U}_n(f)$ 存在且唯一。由 $(af)^{-1}(a(i))\supseteq f^{-1}(i)$ 得自然性，且 $\mathcal U_{r^{\mathcal U}}=\mathcal U$。

基数：互补对 $\{A,X\setminus A\}$ 把 $\mathcal P(X)$ 划分为二元块，共 $2^{N-1}$ 个；$X$ 无限时为 $2^{|X|}$ 个。$\mathcal S(X)$ 的元素就是在每个块中选一个成员，其中 $\{\varnothing,X\}$ 块必须选 $X$。超滤子的基数由 (U4) 和 (U5) 给出。∎

**命题 1.2（$q_{m,k}$ 的像与纤维）。** 设 $X=\varnothing$，则所有 $q_{m,k}$ 都是空映射。下设 $X\ne\varnothing$。
- $m=k$：$q_{m,k}$ 是恒等映射。
- $k\ge3$：$\mathcal U_r$ 只依赖于 $r_2$，所以 $\Phi_kq_{m,k}=\Phi_m$，$q_{m,k}$ 是双射，纤维都是单点。
- $m\ge3$，$k=2$：$\Phi_2q_{m,2}\Phi_m^{-1}$ 是包含映射 $\beta X\hookrightarrow\mathcal S(X)$。
  - 它是单射，像为 $\{s\in R_2(X): s_2(\chi_{A\cap B})=s_2(\chi_A)s_2(\chi_B)\ \forall A,B\}$。理由：对交封闭的自对偶族也对取超集封闭，因为若 $A\in\mathcal U$、$A\subseteq B\notin\mathcal U$，则 $A\cap(X\setminus B)=\varnothing\in\mathcal U$。
  - 像中元素的纤维是单点 $\{r^{\mathcal U_s}\}$；像外元素的纤维为空。
  - 它是满射当且仅当 $|X|\le2$。$|X|\le2$ 时 $|\mathcal S|=|\beta X|$（$1=1$，$2=2$）。$|X|\ge3$ 时，取不同的 $x_0,x_1,x_2$，“多数族” $\{A:|A\cap\{x_0,x_1,x_2\}|\ge2\}$ 是自对偶族，但 $\{x_0,x_1\}\cap\{x_1,x_2\}$ 不属于它，所以它不是超滤子。
- $k=1$：$q_{m,1}$ 映到单点集，唯一的纤维是整个 $R_m(X)$（非空，因为含 $\eta(x)$）。

**命题 1.3（与集合映射 $h$ 的相容）。**
- 当 $m\ge2$ 时，$\Phi_m\circ R_m(h)=h_*\circ\Phi_m$。理由：$(R_m(h)r)_2(\chi_B)=r_2(\chi_{h^{-1}B})$。
- $\Phi_m\eta_{m,X}(x)=\delta_x$。
- 因此第 1.1 节的分类关于 $h$ 是自然的：包含 $\beta\subseteq\mathcal S$ 与 $h_*$ 交换。由引理 0.1(b)，$R_m(h)$ 把 $q_{m,k}^{-1}(s)$ 映入 $q_{m,k}^{-1}(R_k(h)s)$。
- 取 $h=g_X$ 得 $\Phi_m(g\cdot r)=\{gA:A\in\mathcal U_r\}$。
- 若 $X=\varnothing$，$R_m(h)$ 是空映射；若 $X\ne\varnothing=Y$，则不存在 $h$。∎

**定理 1.4（有限 $G$ 集合 $X$ 的不动记录）。** 记 $\bar G$ 为作用的像（$\bar G\le\mathrm{Sym}(X)$），$c(\sigma)$ 为 $\sigma$ 的轮换个数，$N_G=|\mathcal P(X)/G|$。
- (a) $|R_1(X)^G|=1$ 若 $X\ne\varnothing$，否则为 $0$。
- (b) $m\ge3$：$\eta_{m,X}$ 是双射 $X^G\to R_m(X)^G$。因此 $R_m(X)^G$ 非空当且仅当 $X^G\neq\varnothing$，且 $|R_m(X)^G|=|X^G|$。
- (c) $m=2$：$R_2(X)^G\ne\varnothing$ 当且仅当

  **(E)** 每个 $g\in G$ 的置换 $g_X$ 都至少有一个奇数长的轮换。

  (E) 等价于：没有 $g$ 使 $g_X$ 是 2-幂阶的无不动点置换。成立 (E) 时，$N_G$ 为偶数，且
  $$|R_2(X)^G|=2^{N_G/2-1},\qquad N_G=\frac{1}{|\bar G|}\sum_{\sigma\in\bar G}2^{c(\sigma)}.$$

  关于 (E) 的补充：$X=\varnothing$ 时 (E) 不成立（$g=1$ 没有轮换）；$|X|$ 为奇数、$X^G\ne\varnothing$、或 $|\bar G|$ 为奇数且 $X\neq\varnothing$ 时 (E) 都成立。例：$S_3$ 作用于 3 个点时 $|R_2^G|=2$，但 $R_3^G=\varnothing$。

*证明。*

(b) 由 (U4)，$\Phi_m$ 把 $R_m(X)$ 等同于 $\{\delta_x\}$；又 $g\cdot\delta_x=\delta_{gx}$，且 $x\mapsto\delta_x$ 是单射。

(c) 由命题 1.3，$R_2(X)^G$ 对应于 $G$ 不变的自对偶族。补集运算与 $G$ 交换，所以对轨道 $O$，$O^c=\{X\setminus A:A\in O\}$ 也是轨道。

- **若存在 $g,A$ 使 $gA=X\setminus A$，则没有不变的自对偶族。** 对不变族 $\mathcal U$ 有 $A\in\mathcal U\iff gA=X\setminus A\in\mathcal U$，与自对偶性矛盾。
- **若所有轨道都满足 $O\ne O^c$，则恰有 $2^{N_G/2-1}$ 个不变自对偶族。** 此时 $X\ne\varnothing$，因为 $X=\varnothing$ 时取 $g=1,A=\varnothing$ 即满足 $gA=X\setminus A$。轨道配成二元块 $\{O,O^c\}$。不变自对偶族恰好是“从每个块中选一个轨道之并”，其中块 $\{\{\varnothing\},\{X\}\}$ 必须选 $\{X\}$。共 $2^{N_G/2-1}$ 种选法。
- **存在 $A$ 使 $gA=X\setminus A$ ⟺ $g_X$ 的轮换全为偶数长。**
  - (⇒) $g$ 交换 $A$ 与 $X\setminus A$，所以沿每个轮换成员归属交替，长度必为偶数。
  - (⇐) 在每个轮换中取基点 $x$，令 $A=\{g^{2j}x\}$，则 $gA=X\setminus A$。
- **与 2-幂阶条件等价。** 若 $g_X$ 的阶为 $2^eu$（$u$ 奇数），则 $g_X$ 的长为 $\ell$ 的轮换在 $g_X^u$ 下分裂为 $\gcd(\ell,u)$ 个长为 $\ell/\gcd(\ell,u)$ 的轮换，后者仍为偶数长。$g_X^u$ 是 2-幂阶的，且无不动点。反之，2-幂阶无不动点置换的轮换长度都是大于 1 的 2 的幂，故为偶数。
- **Burnside 引理。** $\sigma$ 固定 $A$ 当且仅当 $A$ 是 $\sigma$ 的若干轮换之并，这样的 $A$ 共 $2^{c(\sigma)}$ 个。∎

**命题 1.5（限制映射与延拓范围）。** $q_{m,k}$ 等变，所以限制为 $q^G_{m,k}:R_m(X)^G\to R_k(X)^G$。

对一般的 $X$，“能延拓为完整不动记录”即属于 $q^G_{\infty,k}$ 的像：
- **$k\ge3$**：每个元素都能延拓，且延拓唯一。$q_{\infty,k}$ 是等变双射，其逆也等变。
- **$k=2$**：恰为 $\{s\in R_2(X)^G:\mathcal U_s\in\beta X\}$，延拓唯一，为 $r^{\mathcal U_s}$。该延拓自动是不动的：由 $q(gr)=gq(r)=q(r)$ 和 $q$ 的单射性得 $gr=r$。
- **$k=1$**：唯一元素能延拓，当且仅当 $R_\infty(X)^G\ne\varnothing$（见定理 2.3）。

把 $\infty$ 换成任意 $m\ge3$ 结论不变。$q^G_{2,1}$ 是满射当且仅当 $R_2(X)^G\ne\varnothing$。

对有限 $X$：
- $m\ge k\ge3$ 时，限制映射是 $X^G$ 上的恒等映射。
- $m\ge3$ 时，$q^G_{m,2}:X^G\to R_2(X)^G$，$x\mapsto\eta_{2,X}(x)$（主族 $\delta_x$）是单射，其像是全部可延拓的第 2 层不动记录，共 $|X^G|$ 个，其余都不能延拓。
- 在 $k=1$ 层，唯一元素能延拓当且仅当 $X^G\ne\varnothing$，此时延拓集合为 $\eta(X^G)$。
- $q^G_{m,2}$ 是双射，当且仅当 $|X|\le2$ 或 $R_2(X)^G=\varnothing$。
  - $|X|\le2$ 时 $\mathcal S=\beta$。
  - $|X|\ge3$ 且 $R_2^G\ne\varnothing$ 时，$\{\varnothing\}$、$\{X\}$、$\{\{x\}\}$、$\{X\setminus\{x\}\}$（$x\in X^G$）是互不相同的轨道，所以 $N_G\ge2+2|X^G|$，从而 $|R_2^G|\ge2^{|X^G|}>|X^G|$。

## 2. 完整不动记录的空间

**命题 2.1。**
- (a) 记 $\Phi=\Phi_\infty$。它是 $R_\infty(X)$ 到 $\beta X$ 的同胚，其中 $\beta X$ 取以 $\widehat A$ 为基的 Stone 拓扑。
- (b) $R_\infty(X)$ 是紧 Hausdorff 空间；$G$ 以同胚作用；$R_\infty(X)^G$ 是闭集。
- (c) 对 $S\subseteq X$，$\overline{\eta_{\infty,X}(S)}=\{r:r_2(\chi_S)=1\}=\Phi^{-1}(\widehat S)$。包含映射 $\iota:S\hookrightarrow X$ 给出同胚 $R_\infty(\iota):R_\infty(S)\to\overline{\eta(S)}$。

*证明。*

(a) 当 $n\ge1$ 时，由 (★)，$\{r:r_n(f)=i\}=\Phi^{-1}(\widehat{f^{-1}(i)})$；$n=0$ 时没有观察（或 $X=\varnothing$，此时一切为空）。反之，$\Phi^{-1}(\widehat A)=\{r:r_2(\chi_A)=1\}$ 正是一个观察集。又 $\widehat A\cap\widehat B=\widehat{A\cap B}$，所以 $\{\widehat A\}$ 构成基。

(b) 初始拓扑等于积 $\prod_{n,f}[n]$ 上的子空间拓扑。积空间是紧 Hausdorff 的（Tychonoff）。每条自然性条件只涉及两个坐标，因此是闭条件，于是 $R_\infty(X)$ 是紧 Hausdorff 的。$(g\cdot r)_n(f)=r_n(fg_X)$ 是 $r$ 的一个坐标，所以 $g$ 的作用连续，逆为 $g^{-1}$。$R_\infty(X)^G=\bigcap\{r: r_n(fg_X)=r_n(f)\}$ 是闭集。

(c) $\mathcal U\in\overline{\{\delta_x:x\in S\}}$ 当且仅当每个 $A\in\mathcal U$ 都与 $S$ 相交，当且仅当 $S\in\mathcal U$。若 $S\notin\mathcal U$，则 $X\setminus S\in\mathcal U$ 与 $S$ 不交；若 $S\in\mathcal U$，则 $A\cap S\in\mathcal U$，非空。

再看 $\iota_*$。它是单射，因为 $\mathcal V=\{B\subseteq S: B\in\iota_*\mathcal V\}$。它的像是 $\widehat S$：若 $S\in\mathcal U$，则 $\mathcal U|_S=\{B\subseteq S:B\in\mathcal U\}\in\beta S$，且 $\iota_*(\mathcal U|_S)=\mathcal U$。$R_\infty(\iota)$ 的每个坐标都是 $r$ 的坐标，所以连续。紧空间到 Hausdorff 空间的连续单射是嵌入。∎

**定理 2.2（内在分类）。** 令 $\mathcal F_G(X)=\{A:\ \exists\,H\le G \text{ 有限生成},\ X^H\subseteq A\}$，即由 $\{X^g\}$ 生成的滤子；它可能是非真的。令
$$\beta_GX=\{\mathcal U\in\beta X:\ \mathcal F_G(X)\subseteq\mathcal U\}=\bigcap_{g\in G}\widehat{X^g},$$
取 Stone 子空间拓扑。则 $\Phi$ 限制为同胚 $R_\infty(X)^G\cong\beta_GX$，并且
$$R_\infty(X)^G=\{r:\ r_2(\chi_{X^g})=1\ \forall g\}=\bigcap_{H\le G\text{ 有限生成}}\overline{\eta_{\infty,X}(X^H)}.$$

*证明。* $r$ 不动 ⟺ 对所有 $g$ 有 $(g_X)_*\mathcal U_r=\mathcal U_r$（命题 1.3）⟺ 对所有 $g$ 有 $X^g\in\mathcal U_r$（引理 0.3）。第二个等式由命题 2.1(c) 以及 $X^{g_1}\cap\dots\cap X^{g_k}=X^{\langle g_1,\ldots,g_k\rangle}$ 得到。∎

**推论 2.3（非空判据）。** $R_\infty(X)^G\ne\varnothing$，当且仅当 $\{X^g\}$ 有有限交性质，当且仅当每个有限生成子群 $H$ 都满足 $X^H\ne\varnothing$。取 $H=1$ 即知其中包含 $X\ne\varnothing$。

*证明。* 必要性由定理 2.2 得出，充分性由 (U3) 得出。∎

两个特例：
- 若 $G$ 有限生成，则 $R_\infty(X)^G\cong\beta(X^G)$。
- 若 $X$ 有限，$\{X^g\}$ 只有有限多个，于是 $X^G=X^H$ 对某个有限生成子群 $H$ 成立，结论与定理 1.4(b) 一致。

**定理 2.4（闭包与等式判据）。** $\overline{\eta(X^G)}=\{r:r_2(\chi_{X^G})=1\}\cong\beta(X^G)$，且它包含于 $R_\infty(X)^G$。二者相等，当且仅当存在有限生成子群 $H\le G$ 使 $X^H=X^G$。

*证明。* 包含关系：$\eta(X^G)\subseteq R^G_\infty$，且 $R^G_\infty$ 是闭集（命题 2.1）。
- (⇐) $R^G_\infty\subseteq\Phi^{-1}(\widehat{X^H})=\Phi^{-1}(\widehat{X^G})=\overline{\eta(X^G)}$。
- (⇒) 若每个有限生成 $H$ 都满足 $X^H\supsetneq X^G$，则 $\mathcal F_G\cup\{X\setminus X^G\}$ 有有限交性质。由 (U3) 得超滤子 $\mathcal U$，它属于 $\beta_GX$，但 $X^G\notin\mathcal U$。

$X=\varnothing$ 时两边都为空，判据也成立（取 $H=1$）。∎

**定理 2.5。** 对每个 $G$ 集合都有 $\overline{\eta(X^G)}=R_\infty(X)^G$，当且仅当 $G$ 有限生成。

*证明。* 若 $G$ 有限生成，取 $H=G$。

若 $G$ 不是有限生成的，令 $X=\bigsqcup_{H\text{ 有限生成}}G/H$。此时每个有限生成的 $H$ 都是真子群。
- $X^G=\varnothing$：$gH$ 被 $G$ 固定 ⟺ $g^{-1}Gg\subseteq H$ ⟺ $H=G$，不可能。
- 每个有限生成 $H$ 都满足 $1H\in X^H\ne\varnothing$。
- 由定理 2.4，等式不成立。∎

**例 2.6（可数例）。**
- **群与作用。** 令 $G=(\mathcal P_{\rm fin}(\mathbb N),\triangle)$，它可数。令 $X=\mathbb N$，$\tau$ 交换 $2j\leftrightarrow2j+1$。定义：若 $\lfloor k/2\rfloor\in S$ 则 $S\cdot k=\tau(k)$，否则 $S\cdot k=k$。由 $\tau^2=\mathrm{id}$ 以及 $\lfloor\tau k/2\rfloor=\lfloor k/2\rfloor$，这是一个作用。
- **不动点集。** $X^S=\mathbb N\setminus\bigcup_{j\in S}\{2j,2j+1\}$ 是余有限集，所以 $X^G=\varnothing$。每个余有限集都包含某个 $X^S$，因此 $\mathcal F_G$ 恰为余有限滤子。
- **全部不动记录。** 由定理 2.2 和 (U4)，$R_\infty(\mathbb N)^G=\{r^{\mathcal U}:\mathcal U\text{ 非主}\}=R_\infty(\mathbb N)\setminus\eta(\mathbb N)=\{r:\ r_2(\chi_{\{k\}})=0\ \forall k\}$。其中 $r^{\mathcal U}_n(f)$ 是唯一使 $f^{-1}(i)\in\mathcal U$ 的 $i$。特别地，最终取常值 $i$ 的 $f$ 在每个不动记录处的值都是 $i$。
- **直接验证。** 非主超滤子含每个 $X^S$，由引理 0.3(⇐) 是不动的。$\delta_k$ 被 $S=\{\lfloor k/2\rfloor\}$ 映为 $\delta_{\tau k}\ne\delta_k$，所以不是不动的。
- **基数与拓扑。** 由 (U5)，共 $2^{\mathfrak c}$ 个不动记录。作为空间，它同胚于闭集 $\beta\mathbb N\setminus\mathbb N$。$\overline{\eta(X^G)}=\varnothing$ 与它不等，这与定理 2.5 一致，因为 $G$ 不是有限生成的。

## 3. 乘积比较

**命题 3.1（良定义与连续性）。**
- **良定义。** 对角作用满足 $p_ig_{\Pi}=g_{X_i}p_i$。由引理 0.1(c)，$R_\infty(p_i)$ 等变，把不动记录映为不动记录。
- **连续性。** 目标取积拓扑。$(R(p_i)r)_n(f)=r_n(fp_i)$ 是 $r$ 的一个坐标，所以每个分量连续。由子空间与积的泛性质，$\Pi$ 连续。
- **超滤子表述。** $\Phi(\Pi(r))=((p_i)_*\mathcal U_r)_i$。
- **空指标族。** 两边都是单点集（$R_\infty(\mathrm{pt})=\{\delta_*\}$），$\Pi$ 是同胚。
- **闭映射。** 定义域是紧的，目标是 Hausdorff 的，所以 $\Pi$ 是闭映射。∎

**定理 3.2。** 对任意 $G$ 和任意指标族，$\Pi$ 都是满射，从而是商映射。

*证明。* 若目标为空，或 $I=\varnothing$，结论显然。否则取不变超滤子 $(\mathcal U_i)_i$，此时每个 $X_i\neq\varnothing$。记 $P=\prod X_i$，则 $P^g=\prod_iX_i^g$。考虑族
$$\{P^g\}_{g\in G}\cup\{p_i^{-1}(A):i\in I,\ A\in\mathcal U_i\}.$$
其中任意有限个成员之交形如 $\prod_i\big(\bigcap_jX_i^{g_j}\cap B_i\big)$，其中 $B_i\in\mathcal U_i$。由引理 0.3(⇒)，$X_i^{g_j}\in\mathcal U_i$，所以每个因子都属于 $\mathcal U_i$，因而非空；由选择公理，乘积非空。

由 (U3)，存在超滤子 $\mathcal W$ 包含该族。由引理 0.3(⇐)，$\mathcal W$ 是 $G$ 不变的。又 $(p_i)_*\mathcal W\supseteq\mathcal U_i$，由 (U2) 二者相等。∎

**定理 3.3（平凡群）。** $\Pi_{X,Y}$ 是单射，当且仅当 $X$ 或 $Y$ 有限（包括为空）。

*证明。*

**充分性。** 若某一因子为空，两边都为空。设 $X$ 有限且非空，则 $p_{X*}\mathcal W=\delta_x$，即 $\{x\}\times Y\in\mathcal W$。对 $C\subseteq X\times Y$，记 $C_x=\{y:(x,y)\in C\}$。则
$$C\in\mathcal W\iff\{x\}\times C_x\in\mathcal W\iff X\times C_x\in\mathcal W\iff C_x\in p_{Y*}\mathcal W.$$
所以 $\mathcal W$ 由两个投影决定。$Y$ 有限的情形对称。

**必要性。** 设 $X,Y$ 都是无限集，取单射 $\iota:\mathbb N\to X$ 和 $\kappa:\mathbb N\to Y$，以及 $\mathbb N$ 上的非主超滤子 $\mathcal U$（存在性由 (U3) 对余有限滤子应用得到）。
- 令 $\mathcal W_1=\Delta_*\mathcal U$，它含对角线 $\Delta$。
- 令 $D=\{(m,n):m<n\}$。族 $\{A\times B:A,B\in\mathcal U\}\cup\{D\}$ 有有限交性质：$A\neq\varnothing$，$B$ 是无限集，所以可取 $m\in A$ 和 $n\in B$ 使 $n>m$。由 (U3) 得含此族的超滤子 $\mathcal W_2$。
- $\Delta\cap D=\varnothing$，所以 $\mathcal W_1\ne\mathcal W_2$，而二者的两个投影都是 $(\mathcal U,\mathcal U)$。
- 单射推前是单射（因为 $j^{-1}(jC)=C$），而 $p_X(\iota\times\kappa)=\iota p_1$。因此 $(\iota\times\kappa)_*\mathcal W_1$ 和 $(\iota\times\kappa)_*\mathcal W_2$ 是两个不同的元素，但在 $\Pi$ 下的像相同。∎

**定理 3.4。**

**(a) 为真。** 若 $X,Y$ 至少一个有限，则对任意 $G$，$\Pi_{X,Y}$ 是双射（实际上是同胚）。
- 单射：$\Pi^G$ 是平凡群比较映射在不动点上的限制，由定理 3.3 得出。
- 满射：由定理 3.2 得出。
- 同胚：紧空间到 Hausdorff 空间的连续双射。
- 例如 $X$ 有限时，$R^G_\infty(X\times Y)\cong X^G\times R_\infty(Y)^G$。

**(b) 为假。** 反例：取例 2.6 中的 $G$，令 $X=Y=\mathbb N$，则 $X^G=Y^G=\varnothing$。取非主超滤子 $\mathcal U$，以及定理 3.3 中构造的 $\mathcal W_1,\mathcal W_2$。
- $\mathcal W_1=\Delta_*\mathcal U$ 是不变的，因为 $\Delta$ 等变。
- $\mathcal W_2$ 含 $X^S\times X^S$（因为 $X^S\in\mathcal U$），而 $(X\times X)^S=X^S\times X^S$。由引理 0.3(⇐)，$\mathcal W_2$ 是不变的。
- 于是 $r^{\mathcal W_1}\ne r^{\mathcal W_2}$ 都属于 $R_\infty(\mathbb N^2)^G$，但它们在 $\Pi$ 下的像都是 $(r^{\mathcal U},r^{\mathcal U})$，所以 $\Pi$ 不是单射。∎