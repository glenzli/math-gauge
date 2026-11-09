# 有限测试记录与群作用：答卷

**记号。** $A^c=X\setminus A$。$\chi_A:X\to[2]$ 是指示函数，$c_j:X\to[2]$ 是常值 $j$，$\sigma(j)=1-j$，$\iota_j:[1]\to[2]$ 取 $0\mapsto j$，$!:X\to[1]$ 是唯一映射。$X^g=\{x:gx=x\}$，$X^H=\bigcap_{h\in H}X^h$。$gS=\{gA:A\in S\}$，$h_*S=\{B:h^{-1}B\in S\}$。

$\beta X$ 是 $X$ 上超滤子之集。$\emptyset$ 上的滤子含 $\emptyset=X$，不是真滤子，故 $\beta\emptyset=\emptyset$。$\mathcal P_x=\{A:x\in A\}$ 是主超滤子，$\hat A=\{U:A\in U\}$。因 $\hat A\cap\hat B=\widehat{A\cap B}$，这些 $\hat A$ 构成 Stone 拓扑的基。

**自对偶选择子。** $X\ne\emptyset$ 时，$\mathrm{Sd}(X)$ 是满足 $X\in S$ 且 $\forall A\,(A\in S\iff A^c\notin S)$ 的 $S\subseteq\mathcal P(X)$。它等价于对每对 $\{A,A^c\}$（$\emptyset\neq A\neq X$）恰选其一。

**标准事实（ZFC）。**

* (U1) 有有限交性质（FIP）的族可扩成超滤子。
* (U2) 超滤子对 $X$ 的有限划分（允许空块）恰含一块。证明：真滤子至多含一块；若无块属于 $U$，则各块的补集都在 $U$ 中，其交 $\emptyset\in U$，矛盾。特别地，有限集上的超滤子都是主的。
* (U3) 真滤子等于包含它的超滤子之交。若 $A\notin\mathcal F$，则 $\mathcal F\cup\{A^c\}$ 有 FIP，可扩成含 $A^c$ 的超滤子。
* (U4) $h_*$ 把超滤子映成超滤子，$h_*\mathcal P_x=\mathcal P_{h(x)}$。
* (U5) 非主超滤子含全部余有限集，且每个成员无限。

## 结论一览

1. 当 $X=\emptyset$ 时，所有 $R_m(X)=\emptyset$。当 $X\neq\emptyset$ 时：
   * $R_1(X)$ 是单点。
   * $R_2(X)\cong\mathrm{Sd}(X)$。
   * $3\le m\le\infty$ 时 $R_m(X)\cong\beta X$。
   * $q_{m,k}$ 在 $m\ge k\ge3$ 时为双射；在 $k=2<m$ 时为 $\beta X\subseteq \mathrm{Sd}(X)$ 的包含映射；在 $k=1$ 时为常值映射。
   * 有限 $G$ 集合 $X$ 上：
     * $R_1(X)^G$ 非空 $\iff X\ne\emptyset$，基数为 1。
     * $R_2(X)^G$ 非空 $\iff$ 没有 $g\in G$ 在 $X$ 上的轮换全为偶长，基数为 $2^{N_G(X)/2-1}$。
     * $m\ge3$ 时 $R_m(X)^G=\eta(X^G)$，基数为 $|X^G|$。
   * 有限层不动记录延拓为完整不动记录，当且仅当它是某个 $G$-不动点的点值记录。所以 $k\ge3$ 时必可延拓，$k=1,2$ 时一般不能。
2. $R_\infty(X)\cong\beta X$（同胚、$G$-等变）。$R_\infty(X)^G\cong\{U\in\beta X:X^g\in U\ \forall g\}$。
   * 它非空 $\iff$ $G$ 的每个有限生成子群在 $X$ 中有公共不动点。
   * $\overline{\eta(X^G)}=\widehat{X^G}$。它等于 $R_\infty(X)^G$ $\iff$ 存在有限生成子群 $H$ 使 $X^H=X^G$。
   * 对所有 $G$ 集合都成立的群恰是有限生成群。
   * 例：$G=\mathrm{FSym}(\mathbb N)$ 作用于 $\mathbb N$，全部不动记录对应 $\mathbb N^*=\beta\mathbb N\setminus\mathbb N$。
3. $\Pi$ 良定义且连续，且总为满射。
   * 平凡群、两个集合：单射 $\iff X$ 或 $Y$ 有限，此时为双射。
   * 命题“至少一个有限 $\Rightarrow$ 双射”为真。
   * 命题“$X^G=Y^G=\emptyset\Rightarrow$ 单射”为假。

---

## 1. 截断及其相容关系

### 1.1 基本相容性

**命题 1.1。**

(a) $R_m(h)r\in R_m(Y)$，且 $R_m(h'h)=R_m(h')R_m(h)$。
(b) $q_{m,k}R_m(h)=R_k(h)q_{m,k}$，且 $q_{k,l}q_{m,k}=q_{m,l}$。
(c) $\eta_{m,X}(x)\in R_m(X)$，$R_m(h)\eta_{m,X}=\eta_{m,Y}h$，$q_{m,k}\eta_{m,X}=\eta_{k,X}$。
(d) $g\cdot r=R_m(g_X)r$ 是左作用，$q_{m,k}$ 等变，$g\cdot\eta(x)=\eta(gx)$。

*证明。*

(a) 对 $f:Y\to[n]$：$a((R_m(h)r)_n(f))=a(r_n(fh))=r_k(afh)=(R_m(h)r)_k(af)$。又 $(R_m(h')R_m(h)r)_n(f)=r_n(fh'h)$。
(b) 两边分量公式相同。
(c) $a(f(x))=(af)(x)$，其余同理。
(d) 由 (a)，$(gg')_X=g_Xg'_X$ 给出 $R_m((gg')_X)=R_m(g_X)R_m(g'_X)$。$\square$

**空底集。** $X=\emptyset$ 时 $\mathrm{Map}(\emptyset,[0])=\{\emptyset\}$，而 $r_0$ 要把它映入 $[0]=\emptyset$，不可能。故所有 $R_m(\emptyset)=\emptyset$。

以下设 $X\ne\emptyset$。此时 $\mathrm{Map}(X,[0])=\emptyset$，$r_0$ 为空映射，涉及 $n=0$ 的条件空真，且不存在 $a:[n]\to[0]$（$n\ge1$）。所以只需检验 $1\le n,k\le m$。

### 1.2 分类定理

对 $m\ge2$ 与 $r\in R_m(X)$，令 $U_r=\{A:r_2(\chi_A)=1\}$。

**定理 1.2。** 设 $X\neq\emptyset$。

(a) $R_1(X)=\{*\}$，其中 $r_1(!)=0$。
(b) $r\mapsto U_r$ 是 $R_2(X)\to\mathrm{Sd}(X)$ 的双射，逆为 $S\mapsto r^S$：$r^S_2(f)=1\iff f^{-1}(1)\in S$。
(c) $3\le m\le\infty$ 时，$r\mapsto U_r$ 是 $R_m(X)\to\beta X$ 的双射，逆为 $U\mapsto r^U$：$r^U_n(f)$ 是唯一使 $f^{-1}(i)\in U$ 的 $i\in[n]$（即 $U$-极限）。

*证明。*

(a) $\mathrm{Map}(X,[1])$ 与 $[1]$ 都是单点，$r_1$ 唯一，且唯一的条件 $a=\mathrm{id}$ 显然成立。

(b) 设 $m\ge2$。

* $c_j=\iota_j!$，故 $r_2(c_j)=\iota_j(r_1(!))=j$。
* $\chi_{A^c}=\sigma\chi_A$，故 $r_2(\chi_{A^c})=1-r_2(\chi_A)$。
* 所以 $U_r\in\mathrm{Sd}(X)$。
* 每个 $f:X\to[2]$ 都等于 $\chi_{f^{-1}(1)}$，故 $(*)$：$r_2(f)=1\iff f^{-1}(1)\in U_r$。
* 于是 $m=2$ 时 $r$ 由 $U_r$ 决定（$r_1,r_0$ 强制），即单射。

满射：对 $S\in\mathrm{Sd}(X)$ 验证 $r^S$ 的自然性，只需检验 $[1],[2]$ 之间的映射。

* $\iota_j$：$r^S_2(c_j)=j$，因 $X\in S,\ \emptyset\notin S$。
* $[2]\to[1]$：两边都是 0。
* $\mathrm{id}$：平凡。
* $\sigma$：$(\sigma f)^{-1}(1)=(f^{-1}(1))^c$，由自对偶得 $r_2(\sigma f)=1-r_2(f)$。
* $c_j$：$r_2(c_jf)=j=c_j(r_2f)$。

(c) 设 $m\ge3$，$r\in R_m(X)$。

(c1) 对划分 $X=A_0\sqcup A_1\sqcup A_2$（可有空块），恰有一块属于 $U_r$。取 $f|_{A_i}=i$，$f:X\to[3]$，令 $i_0=r_3(f)$。对 $a_i=\chi_{\{i\}}:[3]\to[2]$ 有 $a_if=\chi_{A_i}$，故 $r_2(\chi_{A_i})=a_i(i_0)=[i=i_0]$。

(c2) $U_r$ 是超滤子。
* $X\in U_r$，$\emptyset\notin U_r$。
* 上封闭：设 $A\in U_r$，$A\subseteq B$。对划分 $A\sqcup(B\setminus A)\sqcup B^c$ 用 (c1)，得 $B^c\notin U_r$，故 $B\in U_r$。
* 交封闭：设 $A,B\in U_r$，对划分 $(A\cap B)\sqcup(A\setminus B)\sqcup A^c$ 用 (c1)。$A^c\notin U_r$。若 $A\setminus B\in U_r$，则由上封闭 $B^c\in U_r$，与 $B\in U_r$ 矛盾。所以 $A\cap B\in U_r$。
* 对每个 $A$，$A,A^c$ 恰有一个属于 $U_r$，所以 $U_r$ 是极大真滤子。

(c3) 设 $n\le m$，$i=r_n(f)$。对 $a=\chi_{\{i\}}:[n]\to[2]$，$r_2(\chi_{f^{-1}(i)})=a(i)=1$，故 $f^{-1}(i)\in U_r$。各 $f^{-1}(j)$ 互不相交，所以 $i$ 是唯一的这样的指标，即 $r=r^{U_r}$，从而单射。

(c4) 对 $U\in\beta X$，由 (U2) $r^U_n(f)$ 良定义。对 $a:[n]\to[k]$，设 $i=r^U_n(f)$，则 $(af)^{-1}(a(i))\supseteq f^{-1}(i)\in U$，故 $r^U_k(af)=a(i)$。又 $U_{r^U}=U$，满射得证。$\square$

**基数。** $X$ 有限非空时，$|R_1|=1$，$|R_2(X)|=2^{2^{|X|-1}-1}$，$m\ge3$ 时 $|R_m(X)|=|X|$。（验证：$|X|=3,4$ 时 $|R_2|=8,128$，$|X|=3,4,5$ 时 $|R_3|=3,4,5$，$|X|=4$ 时 $|R_4|=4$。我对 $|X|\le5$ 的小情形用 z3 枚举验证了这些数值。）

### 1.3 $q_{m,k}$ 的像与纤维，与 $h$ 的相容

由 $U_{q_{m,k}(r)}=U_r$ 可得 $\Phi_k\circ q_{m,k}=\Phi_m$，其中 $\Phi$ 是上述分类双射。因此（$X\ne\emptyset$）：

* $k=m$ 时 $q_{m,k}=\mathrm{id}$。
* $m\ge k\ge3$ 时 $q_{m,k}$ 是双射，每个纤维是单点。
* $k=2<m$ 时 $q_{m,2}$ 是包含映射 $\beta X\hookrightarrow\mathrm{Sd}(X)$。
  * 像恰是超滤子。
  * 超滤子上的纤维是单点，非超滤子上的纤维为空。
  * $q_{m,2}$ 满射 $\iff|X|\le2$。
  * 证明：$|X|\le2$ 时 $\mathrm{Sd}(X)=\beta X$（逐一检查）。$|X|\ge3$ 时取三点 $x_0,x_1,x_2$，$S=\{A:|A\cap\{x_0,x_1,x_2\}|\ge2\}\in\mathrm{Sd}(X)$。但 $\{x_0,x_1\},\{x_1,x_2\}\in S$ 而交 $\{x_1\}\notin S$，故 $S\notin\beta X$。
* $k=1$ 时 $q_{m,1}$ 是常值满射，唯一纤维是整个 $R_m(X)$。

**命题 1.3（与 $h$ 相容）。** 对 $m\ge2$：

* $U_{R_m(h)r}=h_*U_r$，因为 $(R_m(h)r)_2(\chi_B)=r_2(\chi_{h^{-1}B})$。
* $U_{\eta(x)}=\mathcal P_x$。
* $U_{g\cdot r}=gU_r$，因为 $\chi_A\circ g_X=\chi_{g^{-1}A}$。

所以分类双射对 $h$、$q$、$\eta$、$G$-作用都自然。$h_*$ 保持 $\mathrm{Sd}$ 与 $\beta$：$h^{-1}(B^c)=(h^{-1}B)^c$。

### 1.4 有限 $G$ 集合

设 $X$ 有限，$\bar G\le\mathrm{Sym}(X)$ 是 $G$ 的像（有限）。$N_G(X)$ 是 $G$ 在 $\mathcal P(X)$ 上的轨道数，由 Burnside 引理（有限群 $\bar G$ 作用于有限集 $\mathcal P(X)$，条件满足）得
$$N_G(X)=\frac1{|\bar G|}\sum_{\pi\in\bar G}2^{c(\pi)},$$
其中 $c(\pi)$ 是 $\pi$ 的轮换数（$\pi$ 的不变子集是轮换之并）。

**定理 1.4。**

(i) $R_1(X)^G=R_1(X)$：$X\ne\emptyset$ 时为单点，否则为空。

(ii) $R_2(X)^G\ne\emptyset$ 当且仅当不存在 $g\in G$ 与 $A\subseteq X$ 使 $gA=A^c$。等价于：每个 $g\in G$ 在 $X$ 上都有奇长轮换。（$X=\emptyset$ 时恒等元没有轮换，判准自动不成立。）此时 $|R_2(X)^G|=2^{N_G(X)/2-1}$。$G$ 平凡时为 $2^{2^{|X|-1}-1}$。

(iii) $3\le m\le\infty$：$R_m(X)^G=\eta_{m,X}(X^G)$，故非空 $\iff X^G\ne\emptyset$，基数为 $|X^G|$。

(iv) 限制映射 $q^G_{m,k}$：
* $m\ge k\ge3$：在 $\eta$ 的等同下是 $\mathrm{id}_{X^G}$。
* $k=2$，$m\ge3$：$X^G\hookrightarrow R_2(X)^G$，$x\mapsto\mathcal P_x$。
* $k=1$：映到单点。

*证明。*

(iii) $X$ 有限，由 (U2) 所有超滤子是主的，故 $\eta_{m,X}:X\to R_m(X)$ 是等变双射。

(ii) 通过 $\Phi_2$，$R_2(X)^G$ 是 $G$-不变的 $S\in\mathrm{Sd}(X)$。记 $\mathcal P^\circ=\mathcal P(X)\setminus\{\emptyset,X\}$，$\mathcal O=\mathcal P^\circ/G$。补运算 $\kappa$ 与 $G$ 交换，故在 $\mathcal O$ 上诱导对合 $\bar\kappa$。不变的 $S$ 等价于 $\mathcal P^\circ$ 中若干 $G$-轨道之并，且对每个 $A$ 恰含 $A,A^c$ 之一。

* 若某轨道 $\mathcal O_0=\bar\kappa\mathcal O_0$（即 $\exists g:\ gA=A^c$）：若 $A\in S$，则 $A^c\in\mathcal O_0\subseteq S$，矛盾；若 $A\notin S$，则 $A^c\in S$，故 $\mathcal O_0\subseteq S$，得 $A\in S$，矛盾。所以不存在不变的 $S$。
* 否则 $\bar\kappa$ 无不动点，$\mathcal O$ 分成 $|\mathcal O|/2$ 个对子，每对恰选一个轨道，共 $2^{|\mathcal O|/2}$ 个，而 $|\mathcal O|=N_G(X)-2$。

“存在 $g,A$ 使 $gA=A^c$”$\iff$“存在 $g$ 的轮换全为偶长”：

* ($\Rightarrow$) 沿每个轮换，属于 $A$ 与否交替出现，故轮换长度为偶。
* ($\Leftarrow$) 在每个偶长轮换上隔点取点，所得 $A$ 满足 $gA=A^c$；因 $X\ne\emptyset$ 至少有一个长度 $\ge2$ 的轮换，故 $A\in\mathcal P^\circ$。

(iv) 由 §1.3 与等变性。$\square$

### 1.5 延拓范围

设 $X$ 有限，$k<\infty$。$q^G_{\infty,k}:R_\infty(X)^G\to R_k(X)^G$ 的像为：

* $k\ge3$：全部 $R_k(X)^G$，延拓唯一。
* $k=2$：恰为 $\{\mathcal P_x:x\in X^G\}$，其余 $|R_2(X)^G|-|X^G|$ 个不延拓到第 3 层。
* $k=1$：$X^G\ne\emptyset$ 时为 $\{*\}$，否则为空。

即延拓范围恰是点值记录 $\eta_k(x)$，$x\in X^G$。第 3 层是临界层，$k\le2$ 时不能保证延拓。例子：

* $X=\{0,1\}$，$G=\mathbb Z/2$ 交换：$R_1(X)^G=\{*\}$，但 $R_2(X)^G=\emptyset$。
* $X=\mathbb Z/3$，$G=\mathbb Z/3$：$R_2(X)^G=\{\{X\}\cup\{|A|=2\},\ \{X\}\cup\{|A|=1\}\}$，而 $R_m(X)^G=\emptyset$（$m\ge3$）。
* $G$ 平凡且 $|X|\ge3$：$|R_2(X)|>|X|=|R_3(X)|$。

对任意 $X$，$q_{\infty,k}$（$k\ge3$）仍是 $G$-等变双射。

---

## 2. 完整不动记录的空间

**定理 2.1。** $\Phi:R_\infty(X)\to\beta X$ 是同胚（Stone 拓扑），且 $G$-等变，其中 $g\cdot U=gU=(g_X)_*U$。

*证明。* 双射由定理 1.2(c) 得到。由 (c3)，次基元 $\{r:r_n(f)=i\}=\Phi^{-1}(\widehat{f^{-1}(i)})$。取 $n=2$，$f=\chi_A$，$i=1$，则每个 $\hat A$ 都出现。$\hat A$ 对有限交封闭，所以生成的拓扑恰是 Stone 拓扑。等变性由命题 1.3 得到。$\square$

**引理 2.2。** 无不动点的置换 $g$ 作用于集合 $Y$ 时，存在 $c:Y\to\{0,1,2\}$ 使 $c(gy)\ne c(y)$ 对所有 $y$ 成立。

*证明。* 对 $\langle g\rangle$ 的每条轨道取基点 $y_O$（选择公理）。

* 无限轨道或偶长 $\ell$ 的有限轨道：令 $c(g^ky_O)=k\bmod 2$。
* 奇长 $\ell\ge3$：对 $k\le\ell-2$ 令 $c=k\bmod2$，$c(g^{\ell-1}y_O)=2$。

逐一检验相邻点（含绕回）颜色不同。$\square$

**命题 2.3。** 对 $U\in\beta X$ 与 $g\in G$：$gU=U\iff X^g\in U$。

*证明。*

($\Leftarrow$) 若 $A\in U$，则 $gA\supseteq g(A\cap X^g)=A\cap X^g\in U$，故 $gU\subseteq U$。对 $g^{-1}$ 同理，所以相等。

($\Rightarrow$) 令 $Y=X\setminus X^g$，它是 $g$-稳定的且 $g|_Y$ 无不动点。由引理 2.2 得 $Y=A_0\sqcup A_1\sqcup A_2$，$gA_i\cap A_i=\emptyset$。由 (U2)，划分 $X=X^g\sqcup A_0\sqcup A_1\sqcup A_2$ 恰有一块属于 $U$。若 $A_i\in U$，则 $gA_i\in gU=U$，但 $A_i\cap gA_i=\emptyset$，矛盾。$\square$

**定理 2.4（内在分类与非空判准）。**
$$R_\infty(X)^G\;\cong\;\{U\in\beta X:\ X^g\in U\ \ \forall g\in G\}=\bigcap_{g}\widehat{X^g}.$$
这是 $\beta X$ 的闭（实为一族闭开集之交）子空间，同胚意义下与 §2.1 相容。以下四条等价：

1. $R_\infty(X)^G\ne\emptyset$。
2. $\{X^g\}_{g\in G}$ 有 FIP。
3. 对每个有限 $S\subseteq G$，存在 $x\in X$ 被 $S$ 全体固定。
4. $G$ 的每个有限生成子群在 $X$ 中有公共不动点。

特别地，$X=\emptyset$ 时条件不成立（平凡子群 $\{e\}$ 在 $\emptyset$ 中没有不动点）。

*证明。* 第一个等式由定理 2.1 与命题 2.3 得到。

* (1)$\Rightarrow$(2)：$U\ni X^g$，所以有限交属于 $U$，非空。
* (2)$\Rightarrow$(1)：由 (U1) 得超滤子 $U\supseteq\{X^g\}$，再用命题 2.3。
* (2)$\Leftrightarrow$(3)$\Leftrightarrow$(4)：$\bigcap_{s\in S}X^s=X^{\langle S\rangle}$。$\square$

**旁注。** 此空间也是 $\varprojlim_H\beta(X^H)$，$H$ 取遍有限生成子群。理由：相容族由 $V_{\{e\}}=U\in\beta X$ 决定，且 $X^H\in U$。又 $\mathrm{incl}_*:\beta S\to\beta X$ 是单射，像为 $\hat S$。$G$ 有限生成时，它就是 $\widehat{X^G}\cong\beta(X^G)$。

**定理 2.5（闭包）。** $\overline{\eta(X^G)}=\widehat{X^G}=\{r:r_2(\chi_{X^G})=1\}\cong\beta(X^G)$，它包含于 $R_\infty(X)^G$。该闭包等于 $R_\infty(X)^G$ 当且仅当存在有限生成子群 $H\le G$ 使 $X^H=X^G$。

*证明。* 对 $S\subseteq X$，$\hat S$ 是闭开集，且含 $\eta(S)$。任意 $U\in\hat S$ 的基本邻域 $\hat A$ 满足 $A\in U$，从而 $A\cap S\in U$ 非空，因此 $\hat A$ 含 $\eta(S)$ 中的点。所以 $\overline{\eta(S)}=\hat S$。又 $X^G\subseteq X^g$，故 $\widehat{X^G}\subseteq\bigcap_g\widehat{X^g}=R_\infty(X)^G$。

($\Leftarrow$) 设 $X^H=X^G$，$H=\langle h_1,\dots,h_k\rangle$。对 $U\in R_\infty(X)^G$，$X^{h_j}\in U$，故 $X^H=X^G\in U$，即 $U\in\widehat{X^G}$。

($\Rightarrow$) 分两种情形。

* 若 $\{X^g\}$ 无 FIP：存在 $g_1,\dots,g_k$ 使 $\bigcap X^{g_i}=\emptyset$，于是 $X^G=\emptyset$。取 $H=\langle g_1,\dots,g_k\rangle$ 即有 $X^H=\emptyset=X^G$。
* 若有 FIP：设 $\mathcal F$ 是它们生成的滤子，则 $R_\infty(X)^G=\{U\supseteq\mathcal F\}$。假设等式成立，则每个这样的 $U$ 含 $X^G$。由 (U3) $X^G\in\mathcal F$，即存在 $g_i$ 使 $X^{g_1}\cap\cdots\cap X^{g_k}\subseteq X^G$。取 $H=\langle g_1,\dots,g_k\rangle$，则 $X^H=X^G$。$\square$

**定理 2.6（哪些群）。** 对 $G$ 的每个集合 $X$ 都有 $\overline{\eta(X^G)}=R_\infty(X)^G$，当且仅当 $G$ 有限生成。

*证明。* 若 $G$ 有限生成，取 $H=G$ 用定理 2.5。若 $G$ 不是有限生成的，令 $X=\bigsqcup_{H}G/H$，$H$ 取遍有限生成子群（子群全体是集合）。

* $X^G=\emptyset$：$G/H$ 中的不动点 $xH$ 蕴含 $x^{-1}Gx\subseteq H$，即 $H=G$，而 $G$ 不是有限生成的，所以不可能。
* 每个有限生成子群 $K$ 固定 $eK\in G/K$，由定理 2.4 得 $R_\infty(X)^G\ne\emptyset$。

于是 $\overline{\eta(\emptyset)}=\emptyset\ne R_\infty(X)^G$。$\square$

**例 2.7。** 取 $G=\mathrm{FSym}(\mathbb N)$（有限支撑置换，可数，因为它是各 $\mathrm{Sym}(F)$（$F$ 有限）之并），$X=\mathbb N$，自然作用。

* $X^G=\emptyset$：$(n\ n{+}1)$ 移动 $n$。
* 每个有限集 $S\subseteq G$ 有有界支撑，固定所有大的 $n$，故 $R_\infty(X)^G\ne\emptyset$。
* **全部不动记录。** $X^g=\mathbb N\setminus\mathrm{supp}(g)$ 是余有限集。由定理 2.4，$U$ 是不动的当且仅当 $U$ 含所有这些 $X^g$。
  * 主超滤子 $\mathcal P_n$ 被 $(n\ n{+}1)$ 移动，不是不动的。
  * 非主超滤子含全部余有限集（(U5)），因此含每个 $X^g$，是不动的。
* 所以全部不动记录是 $\{r^U:U\in\mathbb N^*=\beta\mathbb N\setminus\mathbb N\}$，其中 $r^U_n(f)$ 是唯一使 $f^{-1}(i)\in U$ 的 $i$。
* 等价刻画：$r$ 不动 $\iff r_n(f)=r_n(f')$ 对任意仅在有限点上不同的 $f,f'$ 成立。
  * ($\Rightarrow$) 设 $r_n(f)=i$，则 $f^{-1}(i)\in U_r$，故 $f'^{-1}(i)\supseteq f^{-1}(i)\setminus F\in U_r$，$F$ 为有限的差异集。
  * ($\Leftarrow$) $f\circ g$ 与 $f$ 只在 $\mathrm{supp}(g)$ 上不同。
* 拓扑上，该集合同胚于 $\mathbb N^*$（闭子空间，因每个 $\mathcal P_n=\widehat{\{n\}}$ 是孤立点）。基数为 $2^{\mathfrak c}$（Pospíšil 定理：$|\beta\mathbb N|=2^{\mathfrak c}$，条件是底集无限）。
* 对 $3\le k<\infty$，$q_{\infty,k}$ 把它们一一映到 $R_k(\mathbb N)^G$。存在性用到选择公理。

---

## 3. 乘积比较

**命题 3.1（良定义与连续）。** 令 $P=\prod X_i$。$p_i$ 是 $G$-等变的，所以
$$R_\infty(p_i)(g\cdot r)=R_\infty(p_ig_P)r=R_\infty(g_{X_i}p_i)r=g\cdot R_\infty(p_i)r.$$
不动点映到不动点，$\Pi$ 良定义。

连续性：$\{s:s_n(f)=j\}$ 在 $R_\infty(p_i)$ 下的原像是 $\{r:r_n(fp_i)=j\}$，仍是次基开集。每个分量连续，故 $\Pi$ 对乘积拓扑连续。

空指标族：$P$ 是单点（平凡作用），$R_\infty(P)^G$ 与目标 $\prod_{\emptyset}$ 都是单点，$\Pi$ 是同胚。若某 $X_i=\emptyset$，则源、靶皆空。

**定理 3.2（总为满射）。** 对任意 $G$ 与任意集合指标族，$\Pi$ 是满射。

*证明。* 取 $(U_i)\in\prod R_\infty(X_i)^G$，设每个 $R_\infty(X_i)^G\ne\emptyset$（否则靶为空，无需证）。令
$$\mathcal S=\{p_i^{-1}(A):A\in U_i\}\cup\{P^g:g\in G\},\qquad P^g=\prod_iX_i^g.$$
$\mathcal S$ 的有限子族之交是 $\prod_jB_j$，其中
$$B_j=\bigcap_tX_j^{g_t}\cap\bigcap_{k:i_k=j}A_k\in U_j.$$
这里用到命题 2.3：不动的 $U_j$ 含各 $X_j^{g_t}$。所以每个 $B_j\ne\emptyset$，由选择公理 $\prod_jB_j\neq\emptyset$。因此 $\mathcal S$ 有 FIP（适用 (U1) 的条件成立）。

取超滤子 $U\supseteq\mathcal S$。$P^g\in U$，由命题 2.3，$U$ 是 $G$-不变的。又 $(p_i)_*U\supseteq U_i$，两者都是超滤子，故相等。$\square$

**引理 3.3（两因子的纤维）。** 设 $W_X\in R_\infty(X)^G$，$W_Y\in R_\infty(Y)^G$，$\mathcal F_0$ 是由矩形 $A\times B$（$A\in W_X$，$B\in W_Y$）生成的滤子。则
$$\Pi^{-1}(W_X,W_Y)=\{U\in\beta(X\times Y):U\supseteq\mathcal F_0\}.$$
纤维是单点当且仅当 $\mathcal F_0$ 已是超滤子。

*证明。*

* ($\subseteq$) $(p_1)_*U=W_X$ 即 $A\times Y\in U$，同理 $X\times B\in U$，故矩形在 $U$ 中。
* ($\supseteq$) 边缘 $\supseteq W_X,W_Y$ 故相等。又 $(X\times Y)^g=X^g\times Y^g=(X^g\times Y)\cap(X\times Y^g)\in\mathcal F_0$（因 $X^g\in W_X$，$Y^g\in W_Y$），由命题 2.3 知 $U$ 不变。

由 (U1)，$\mathcal F_0$ 能扩成超滤子，且当且仅当 $\mathcal F_0$ 不是超滤子时扩法不唯一。$\square$

**定理 3.4（平凡群）。** $\Pi_{X,Y}:\beta(X\times Y)\to\beta X\times\beta Y$ 总是满射。它是单射当且仅当 $X$ 或 $Y$ 有限（含空集），此时为双射（同胚）。

*证明。*

($\Leftarrow$) 设 $X$ 有限。取 $(\mathcal P_x,W_Y)$，则 $\mathcal F_0\ni\{x\}\times B$（$B\in W_Y$）。对任意 $T\subseteq X\times Y$，令 $T_x=\{y:(x,y)\in T\}$。若 $T_x\in W_Y$，则 $\{x\}\times T_x\subseteq T$；否则 $T_x^c\in W_Y$，$\{x\}\times T_x^c\subseteq T^c$。所以 $\mathcal F_0$ 是超滤子，纤维是单点。$Y$ 有限同理。

($\Rightarrow$) 设 $X,Y$ 都无限。取单射 $\alpha:\mathbb N\to X$，$\beta:\mathbb N\to Y$，非主超滤子 $W$ 于 $\mathbb N$，$W_X=\alpha_*W$，$W_Y=\beta_*W$。令 $\Gamma=\{(\alpha n,\beta n)\}$。对 $A\in W_X$，$B\in W_Y$：$N_A=\alpha^{-1}A$ 与 $N_B=\beta^{-1}B$ 属于 $W$。

* $\Gamma$ 与 $A\times B$ 相交：取 $n\in N_A\cap N_B$。
* $\Gamma^c$ 与 $A\times B$ 相交：因 $N_A$ 无限，取 $n_0\in N_B$，$n\in N_A\setminus\{n_0\}$。则 $(\alpha n,\beta n_0)\in A\times B$。若它在 $\Gamma$ 中，则 $(\alpha n,\beta n_0)=(\alpha k,\beta k)$，由单射性得 $n=k=n_0$，矛盾。

所以 $\Gamma$ 与 $\Gamma^c$ 都与 $\mathcal F_0$ 的每个成员相交，$\mathcal F_0$ 不是超滤子。由引理 3.3，纤维至少两个点。

双射为同胚：源是紧致空间 $\beta(X\times Y)$ 的闭子空间，靶是 Hausdorff 空间，连续双射是同胚。$\square$

**定理 3.5（命题 (1) 为真）。** 若 $X,Y$ 至少一个有限，则 $\Pi_{X,Y}$ 是双射（同胚）。

*证明。* 设 $X$ 有限，则 $R_\infty(X)^G=\eta(X^G)$（定理 1.4(iii)）。

* 若 $X^G=\emptyset$，靶为空；源也空，因为 $U\in R_\infty(X\times Y)^G$ 的第一边缘是不动的。
* 否则取 $(\mathcal P_x,V)$，$x\in X^G$，$V\in R_\infty(Y)^G$。由定理 3.4 的论证（引理 3.3 的 $\mathcal F_0$ 是超滤子），纤维是单点，且非空（$\mathcal F_0$ 有 FIP）。
* 具体逆映射是 $(x,V)\mapsto(j_x)_*V$，$j_x(y)=(x,y)$，$j_x$ 等变因为 $x\in X^G$。

$Y$ 有限同理。拓扑同胚同定理 3.4。$\square$

**定理 3.6（命题 (2) 为假）。** 取 $G=\mathrm{FSym}(\mathbb N)$，$X=Y=\mathbb N$。则 $X^G=Y^G=\emptyset$，但 $\Pi_{X,Y}$ 不是单射。

*证明。* 取非主超滤子 $W$ 于 $\mathbb N$（例 2.7 中的不动记录）。令 $W_X=W_Y=W$，$\Gamma=\Delta=\{(n,n)\}$。

* 对 $A,B\in W$，$A\cap B\in W$ 非空，故 $\Delta$ 与 $A\times B$ 相交。
* 又 $B$ 无限，取 $a\in A$，$b\in B\setminus\{a\}$，则 $(a,b)\in(A\times B)\setminus\Delta$。

所以 $\Delta$ 与其补集都与 $\mathcal F_0$ 的每个成员相交。由引理 3.3，纤维至少两个点（一个含 $\Delta$，一个含 $\Delta^c$），即存在两个不同的 $G$-不动记录有相同的 $\Pi$-像 $(W,W)$。$\square$

**注。** 若 $G$ 有限生成，则命题 (2) 平凡成立：$X^G=\emptyset$ 蕴含 $R_\infty(X)^G=\emptyset$（由定理 2.4），源靶皆空。所以反例必须来自非有限生成群。此时 $R_\infty(Z)^G=\widehat{Z^G}\cong\beta(Z^G)$，$\Pi$ 化为平凡群时 $(X^G,Y^G)$ 的比较映射，因而单射 $\iff X^G$ 或 $Y^G$ 有限。

**总结。** $\Pi$ 对任意 $G$ 与任意集合指标族总是满射。命题 (1)（至少一个有限 $\Rightarrow$ 双射）为真，命题 (2)（$X^G=Y^G=\emptyset\Rightarrow$ 单射）为假。