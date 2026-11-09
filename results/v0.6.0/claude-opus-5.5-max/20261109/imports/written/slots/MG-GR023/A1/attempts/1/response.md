**说明.** 我在本地用穷举核对了以下结果：$|X|\le4$、$m\le4$ 时 $R_m(X)$ 的基数（z3 直接按定义求解），以及 $S_N$（$N\le5$）的全部子群上 $R_2(X)^G$ 的计数公式和延拓判准，结果均与定理相符。下面的证明不依赖这些计算。

---

# 约定与基本事实

全文在 ZFC 中进行，可用选择公理和超滤子引理。对 $A\subseteq X$，$\chi_A:X\to[2]$ 表示示性函数；$A\mapsto\chi_A$ 是 $P(X)\to\operatorname{Map}(X,[2])$ 的双射。

**超滤子.** $\mathcal U\subseteq P(X)$ 称为超滤子，若 $X\in\mathcal U$，$\varnothing\notin\mathcal U$，$\mathcal U$ 上闭且对有限交封闭，并且对每个 $A$，$A$ 与 $X\setminus A$ 恰有一个属于 $\mathcal U$。全体超滤子记为 $\beta X$。主超滤子记为 $\mathcal U_x=\{A:x\in A\}$。记 $\widehat A=\{\mathcal U\in\beta X:A\in\mathcal U\}$。由于需要 $\varnothing=X\in\mathcal U\not\ni\varnothing$，故 $\beta\varnothing=\varnothing$。

- **(U1)** 若 $X=A_0\sqcup\dots\sqcup A_{n-1}$（$n\ge1$，允许空块），则恰有一个 $A_i\in\mathcal U$。理由：若一个都没有，则各补集之交 $\varnothing\in\mathcal U$；若有两个，则二者之交 $\varnothing\in\mathcal U$。
- **(U2)** 有限集上的超滤子都是主超滤子（对单点分解用 (U1)）。并且 $\mathcal U_x=\mathcal U_y\iff x=y$。
- **(U3)** 若超滤子 $\mathcal V\subseteq\mathcal U$，则 $\mathcal V=\mathcal U$。理由：若 $B\in\mathcal U\setminus\mathcal V$，则 $X\setminus B\in\mathcal V\subseteq\mathcal U$，矛盾。
- **(U4)** 超滤子引理：有有限交性质（FIP）的族含于某个超滤子。
  - 推论：设 $\mathcal F=\{A:\exists B_1,\dots,B_k\in\mathcal B\ (k\ge0),\ A\supseteq B_1\cap\dots\cap B_k\}$ 是由 $\mathcal B$ 生成的滤子（可以含 $\varnothing$）。则 $A\in\mathcal F$ 当且仅当 $A$ 属于每个包含 $\mathcal B$ 的超滤子。
  - 推论的证明：若 $A\notin\mathcal F$，则 $\mathcal B\cup\{X\setminus A\}$ 有 FIP，否则会有某个 $B_1\cap\dots\cap B_k\subseteq A$。
- **(U5)** 对 $h:X\to Y$，令 $h_*\mathcal S=\{B\subseteq Y:h^{-1}B\in\mathcal S\}$。$h_*$ 保持超滤子，且 $(h'h)_*=h'_*h_*$。对置换 $g$，有 $g_*\mathcal S=\{gA:A\in\mathcal S\}$，记作 $g\mathcal S$。

**自对偶族.** 令
$$\mathrm{SD}(X)=\{\mathcal S\subseteq P(X):\ X\in\mathcal S,\ \forall A\ (A\in\mathcal S\Leftrightarrow X\setminus A\notin\mathcal S)\}.$$
- 取 $A=X=\varnothing$ 即得矛盾，所以 $\mathrm{SD}(\varnothing)=\varnothing$。
- $\beta X\subseteq\mathrm{SD}(X)$。
- 因为 $h^{-1}(Y\setminus B)=X\setminus h^{-1}B$ 且 $h^{-1}Y=X$，所以 $h_*$ 保持 $\mathrm{SD}$。
- 自对偶族若对交封闭，则是超滤子。理由：若 $A\in\mathcal S$，$A\subseteq B$，$B\notin\mathcal S$，则 $X\setminus B\in\mathcal S$，从而 $\varnothing=A\cap(X\setminus B)\in\mathcal S$，但 $X\in\mathcal S$ 推出 $\varnothing\notin\mathcal S$，矛盾。

**引理 A（不动点引理）.** 设 $g$ 是 $X$ 的置换，$\mathcal U\in\beta X$，$X^g=\{x:gx=x\}$。则 $g\mathcal U=\mathcal U\iff X^g\in\mathcal U$。

*证明.*
- (⇐) 对 $A\in\mathcal U$，有 $A\cap X^g\in\mathcal U$，且 $A\cap X^g=g(A\cap X^g)\subseteq gA$，故 $gA\in\mathcal U$。于是 $g\mathcal U\subseteq\mathcal U$，由 (U5)(U3) 得两者相等。
- (⇒) 构造三染色：
  - 令 $Y=X\setminus X^g$。则 $gY=Y$，且 $g|_Y$ 无不动点。
  - 在每个 $\langle g\rangle$-轨道 $O\subseteq Y$ 中选一点 $y_O$（选择公理）。
  - 若 $O$ 无限，把 $g^jy_O$（$j\in\mathbb Z$）放入 $C_{j\bmod 2}$。
  - 若 $|O|=\ell$ 有限，则 $\ell\ge2$。把 $g^jy_O$（$0\le j\le\ell-2$）放入 $C_{j\bmod2}$，把 $g^{\ell-1}y_O$ 放入 $C_2$。
  - 逐一核对可知，每个 $y\in Y$ 与 $gy$ 不在同一块中，即 $C_i\cap gC_i=\varnothing$。
  - 若 $X^g\notin\mathcal U$，由 (U1) 应用于 $X=X^g\sqcup C_0\sqcup C_1\sqcup C_2$，某个 $C_i\in\mathcal U$。于是 $gC_i\in g\mathcal U=\mathcal U$，进而 $\varnothing=C_i\cap gC_i\in\mathcal U$，矛盾。∎

**引理 B（反转引理）.** 设 $g$ 是有限集 $X$ 的置换。存在 $A\subseteq X$ 使 $gA=X\setminus A$，当且仅当 $g$ 的每个轮换长度都是偶数（$X=\varnothing$ 时两边皆真）。

*证明.*
- 若 $gA=X\setminus A$，则 $g(X\setminus A)=A$，所以 $\chi_A(gy)=1-\chi_A(y)$，从而 $\chi_A(g^jx)\equiv\chi_A(x)+j\pmod 2$。在长为 $\ell$ 的轮换上 $g^\ell x=x$，故 $\ell$ 为偶数。
- 反之，若每个轮换 $O$ 的长度 $\ell_O$ 都是偶数，取 $A=\bigcup_O\{g^jx_O:0\le j<\ell_O,\ j\text{ 为偶数}\}$，则 $gA=X\setminus A$。∎

---

# 第一部分：截断及其相容关系

**引理 1.0.**
- $R_m(\varnothing)=\varnothing$：$\operatorname{Map}(\varnothing,[0])=\{\varnothing\}$，而不存在 $\{\varnothing\}\to[0]=\varnothing$ 的映射。
- 若 $X\ne\varnothing$，则 $\operatorname{Map}(X,[0])=\varnothing$，故 $r_0$ 是空映射，含 $n=0$ 的条件都空真。
- 当 $n\ge1$ 时不存在 $[n]\to[0]$ 的映射，所以含 $k=0$ 的条件也都空真。
- $\operatorname{Map}(X,[1])=\{c\}$ 只含常值映射，$r_1(c)=0$ 是被迫的。

**引理 1.1.** 设 $X\ne\varnothing$，$m\ge2$，$r\in R_m(X)$，令 $\mathcal S_r=\{A:r_2(\chi_A)=1\}$。

- (i) $\mathcal S_r\in\mathrm{SD}(X)$。
- (ii) 对 $1\le n\le m$、$f:X\to[n]$、$i\in[n]$，有 $r_n(f)=i\iff f^{-1}(i)\in\mathcal S_r$。因此 $r$ 由 $r_2$ 决定。
- (iii) 若 $m\ge3$，则 $\mathcal S_r\in\beta X$。

*证明.*
- (i)
  - 取对换 $\sigma:[2]\to[2]$，得 $r_2(\chi_{X\setminus A})=\sigma(r_2(\chi_A))$。
  - 取 $a:[1]\to[2]$，$a(0)=1$，得 $1=a(r_1(c))=r_2(\chi_X)$。
- (ii) 取 $a=\chi_{\{i\}}:[n]\to[2]$。由 $a\circ f=\chi_{f^{-1}(i)}$ 得 $[r_n(f)=i]=r_2(\chi_{f^{-1}(i)})$。
- (iii) 由 (ii) 取 $n=3$：对 $X$ 的每个三块有序分解（允许空块），恰有一块属于 $\mathcal S_r$。
  - 由 (i) 有 $\varnothing\notin\mathcal S_r$。
  - 上闭：设 $A\in\mathcal S_r$，$A\subseteq B$。考虑 $(A,B\setminus A,X\setminus B)$，得 $X\setminus B\notin\mathcal S_r$，故 $B\in\mathcal S_r$。
  - 对交封闭：设 $A,B\in\mathcal S_r$ 但 $A\cap B\notin\mathcal S_r$。由 $(A\cap B,A\setminus B,X\setminus A)$ 得 $A\setminus B\in\mathcal S_r$。但分解 $(A\setminus B,B,X\setminus(A\cup B))$ 中有两块属于 $\mathcal S_r$，矛盾。∎

**定理 1.1（分类）.** 对任意集合 $X$（含 $\varnothing$）有：

1. $R_1(X)=\varnothing$（若 $X=\varnothing$）；否则 $R_1(X)$ 恰为一点 $\eta_{1,X}(x)$，与 $x$ 无关。
2. $\Phi_2:R_2(X)\to\mathrm{SD}(X)$，$r\mapsto\mathcal S_r$ 是双射。
   - 因此 $R_2(X)\cong\prod_{p}p$，其中 $p$ 取遍互补对 $\{A,X\setminus A\}\neq\{\varnothing,X\}$。
   - $|R_2(X)|=2^{2^{|X|-1}-1}$（$X$ 有限且非空）；$|R_2(X)|=2^{2^{|X|}}$（$X$ 无限）；$|R_2(\varnothing)|=0$。
3. 当 $3\le m\le\infty$ 时，$\Phi_m:R_m(X)\to\beta X$，$r\mapsto\mathcal S_r$ 是双射。
   - 逆映射为 $\mathcal U\mapsto r^{\mathcal U}$，其中 $r^{\mathcal U}_n(f)$ 是唯一满足 $f^{-1}(i)\in\mathcal U$ 的 $i$。
   - 基数：$X$ 有限时为 $|X|$；$X$ 无限时为 $2^{2^{|X|}}$（Pospíšil 定理，条件是 $X$ 无限）。
4. 当 $m\ge2$ 时，$\Phi_m(\eta_{m,X}(x))=\mathcal U_x$。

*证明.* $X=\varnothing$ 的情形由引理 1.0 和 $\mathrm{SD}(\varnothing)=\beta\varnothing=\varnothing$ 得到。下设 $X\ne\varnothing$。

- (1) 由引理 1.0，唯一剩下的条件是 $(n,k)=(1,1)$、$a=\mathrm{id}$，它是平凡的。
- (2) 由引理 1.0，只需考虑 $n,k\in\{1,2\}$ 的条件：
  - $(1,1)$ 与 $(2,1)$ 是平凡的。
  - $(1,2)$ 等价于 $r_2(\chi_X)=1$ 且 $r_2(\chi_\varnothing)=0$。
  - $(2,2)$ 中 $a\in\{\mathrm{id},\sigma,c_0,c_1\}$：$\sigma$ 给出自对偶性；常值映射 $c_j$ 给出 $r_2(\text{const}_j)=j$。
  - 所以对 $\mathcal S\in\mathrm{SD}(X)$，令 $r_2(\chi_A)=[A\in\mathcal S]$（$r_0,r_1$ 被迫），即得到一个记录。再由引理 1.1(i) 知这两种对应互逆。
  - 基数：$P(X)$ 被划分为互补对（每对含两个不同元素），共 $2^{|X|-1}$ 对（$X$ 无限时为 $2^{|X|}$ 对）。除 $\{\varnothing,X\}$ 外每对自由选一个元素。
- (3) 设 $\mathcal U\in\beta X$。由 (U1)，$r^{\mathcal U}$ 有定义；$n=0$ 时它是空映射。
  - 相容性：设 $i=r^{\mathcal U}_n(f)$，则 $(a\circ f)^{-1}(a(i))\supseteq f^{-1}(i)\in\mathcal U$，所以 $r^{\mathcal U}_k(a\circ f)=a(i)$。
  - $\mathcal S_{r^{\mathcal U}}=\{A:\chi_A^{-1}(1)\in\mathcal U\}=\mathcal U$。
  - 由引理 1.1(ii)(iii) 得 $r^{\mathcal S_r}=r$。
- (4) 由 $\eta(x)_2(\chi_A)=\chi_A(x)$ 直接得到。∎

**命题 1.2（$q_{m,k}$ 的像与纤维）.** 设 $m\ge k\ge1$。
- 若 $X=\varnothing$：$q_{m,k}$ 是 $\varnothing\to\varnothing$，像为空，没有纤维。
- 设 $X\ne\varnothing$。由于 $\Phi_k\circ q_{m,k}=\Phi_m$（$k\ge2$，二者都只读 $r_2$），有：
  - $k=1$：$q_{m,1}$ 映到一点，是满射（因为 $\eta(x)\in R_m(X)$）。唯一的纤维是 $R_m(X)$ 本身，即一点、$\mathrm{SD}(X)$ 或 $\beta X$。
  - $k=m$：$q_{m,m}$ 是恒等映射。
  - $3\le k\le m$：$q_{m,k}$ 是双射，每个纤维是单点。
  - $k=2<m$（即 $m\ge3$）：在分类下 $q_{m,2}$ 就是包含映射 $\beta X\hookrightarrow\mathrm{SD}(X)$。
    - 它是单射。
    - 像为 $\{s\in R_2(X):\mathcal S_s\in\beta X\}=\{s:s_2(\chi_{A\cap B})=s_2(\chi_A)s_2(\chi_B)\ \forall A,B\}$。
    - 纤维：若 $\mathcal S_s\in\beta X$，则纤维为 $\{r^{\mathcal S_s}\}$；否则为空集。
    - $q_{m,2}$ 满射当且仅当 $|X|\le2$：
      - $|X|=1$ 时 $\mathrm{SD}=\beta$ 显然。
      - $|X|=2$ 时，两种选法都是主超滤子。
      - $|X|\ge3$ 时，取不同的 $x,y,z$，多数族 $\{A:|A\cap\{x,y,z\}|\ge2\}$ 是自对偶的，但 $\{x,y\}\cap\{y,z\}=\{y\}$ 不在其中，所以它不是超滤子。

**命题 1.3（与 $h:X\to Y$ 的相容性）.**
- (i) $R_m(h)$ 有定义，因为 $a(r_n(f\circ h))=r_k(a\circ f\circ h)$。并且 $R_m(\mathrm{id})=\mathrm{id}$，$R_m(h'h)=R_m(h')R_m(h)$。
- (ii) $q_{m,k}R_m(h)=R_k(h)q_{m,k}$，$q_{k,j}q_{m,k}=q_{m,j}$（逐分量定义）。
- (iii) $R_m(h)\eta_{m,X}=\eta_{m,Y}h$，$q_{m,k}\eta_{m,X}=\eta_{k,X}$。
- (iv) 当 $m\ge2$ 时，$\Phi_m(R_m(h)r)=h_*\Phi_m(r)$，因为 $(R_m(h)r)_2(\chi_B)=r_2(\chi_{h^{-1}B})$。所以分类对 $h$ 是自然的，$h_*$ 保持 $\mathrm{SD}$ 和 $\beta$。
  - 若 $X=\varnothing$，则 $R_m(h)$ 是空映射。
  - 若 $X\ne\varnothing=Y$，则不存在 $h$。
- (v) 取 $h=g_X$：$g\mapsto R_m(g_X)$ 是左作用；$\Phi_m(g\cdot r)=g\Phi_m(r)$；$q_{m,k}$ 是等变的。等变映射 $h$ 把不动记录映为不动记录。

**定理 1.4（有限 $G$ 集合）.** 设 $X$ 有限，$\bar G\le\mathrm{Sym}(X)$ 为 $G$ 的像（这是有限群），$c(\sigma)$ 为 $\sigma$ 在 $X$ 上的轮换数。

1. **$m=1$.** $R_1(X)^G$ 在 $X\ne\varnothing$ 时为一点，在 $X=\varnothing$ 时为空。
2. **$m\ge3$.** $R_m(X)^G=\{\eta_{m,X}(x):x\in X^G\}$，所以 $|R_m(X)^G|=|X^G|$，非空当且仅当 $X^G\ne\varnothing$。
   - 证明：由 (U2)，$\beta X=\{\mathcal U_x\}$；又 $g\mathcal U_x=\mathcal U_{gx}$。
3. **$m=2$.** $R_2(X)^G\neq\varnothing$ 当且仅当不存在 $g\in G$ 使其在 $X$ 上的所有轮换都为偶长。
   - $X=\varnothing$ 时恒等元空真地满足此条件，所以此时为空。$|X|$ 为奇数时总非空。
   - 非空时有
   $$|R_2(X)^G|=2^{N-1},\qquad N=|\mathcal P(X)/G|=\tfrac12|P(X)/G|=\frac1{2|\bar G|}\sum_{\sigma\in\bar G}2^{c(\sigma)},$$
   其中 $\mathcal P(X)$ 为互补对 $\{A,X\setminus A\}$ 的集合。
4. **限制映射.**
   - $3\le k\le m\le\infty$：$\eta_m(x)\mapsto\eta_k(x)$，是 $X^G$ 上的恒等映射，即双射。
   - $m\ge3,\ k=2$：$\eta_m(x)\mapsto\eta_2(x)$（主族 $\mathcal U_x$）。这是单射，像为 $R_2(X)^G$ 中恰好是超滤子的那 $|X^G|$ 个元素。
   - $k=1$：常值映射到一点，满射当且仅当定义域非空。

*证明 (3).* 设 $X\ne\varnothing$。
- 不动的 2-记录 ↔ $G$-不变的 $\mathcal S\in\mathrm{SD}(X)$ ↔ 等变截面 $s:\mathcal P(X)\to P(X)$，满足 $s(p)\in p$ 且 $s(\{\varnothing,X\})=X$。
- 取一个轨道 $Gp$，$p=\{A,X\setminus A\}$。
  - 若有 $g$ 使 $gA=X\setminus A$，则 $gp=p$，但 $g$ 交换 $p$ 的两个元素，与 $s(p)=gs(p)$ 矛盾，故无解。
  - 否则 $\mathrm{Stab}(p)$ 固定 $A$ 与 $X\setminus A$。$s(p)$ 的两种选法各自唯一地等变延拓到整个轨道：令 $s(gp)=gs(p)$，这是良定的。
- 不同轨道互相独立；$\{\{\varnothing,X\}\}$ 单独成一轨道且选择被迫。由此得到 $2^{N-1}$。存在性判准由引理 B 给出。
- 无反转时，$P(X)\to\mathcal P(X)$ 在轨道层面是二对一的：$GA\ne G(X\setminus A)$。
- 最后用 Burnside 引理（$\bar G$ 是有限群，作用在有限集 $P(X)$ 上，$G$-轨道与 $\bar G$-轨道相同；$\sigma$-不变子集即轮换的并，共 $2^{c(\sigma)}$ 个）。∎

**推论 1.5（延拓范围）.** 对任意 $G$ 集合 $X$ 和有限 $m$，令 $E_m=q_{\infty,m}(R_\infty(X)^G)$。

- **$m\ge3$.** $E_m=R_m(X)^G$，且延拓唯一。
- **$m=2$.** $E_2=\{s\in R_2(X)^G:\mathcal S_s\in\beta X\}$，延拓唯一。
  - 对有限 $X$：$E_2=\{\eta_2(x):x\in X^G\}$。
  - 对有限 $X$：$E_2=R_2(X)^G$ 当且仅当 $|X|\le2$ 或 $R_2(X)^G=\varnothing$。
- **$m=1$.** 若 $R_\infty(X)^G\ne\varnothing$（$X$ 有限时即 $X^G\ne\varnothing$），则 $E_1=R_1(X)$，并有 $|R_\infty(X)^G|$ 种延拓；否则 $E_1=\varnothing$。

因此，"对所有（有限）$G$ 集合，每个不动的 $m$ 层记录都能延拓"恰好对 $m\ge3$ 成立。反例：$\mathbb Z/3$ 旋转作用于 $[3]$ 时，$|R_1^G|=1$，$|R_2^G|=2$（包括多数族），而 $R_3^G=\varnothing$。

*证明.*
- 当 $m\ge2$ 时，$q_{\infty,m}$ 是单射且等变，所以不动记录的任何延拓自动是不动的：$q(g\tilde r)=gr=r=q(\tilde r)$。再由命题 1.2 得到 $m\ge2$ 的结论。
- $|X|\ge3$ 且 $R_2(X)^G\ne\varnothing$ 时：
  - 各对 $\{\{x\},X\setminus\{x\}\}$（$x\in X^G$）互不相同，都是不动的单点轨道，且都不等于 $\{\varnothing,X\}$。
  - 此外这样的非平凡对总是存在，所以 $N-1\ge\max(|X^G|,1)$。
  - 于是 $2^{N-1}>|X^G|$，即 $E_2\ne R_2(X)^G$。
- $|X|\le2$ 时：
  - $|X|=0$：两边都是空集。
  - $|X|=1$：$R_2(X)^G=\{\eta_2(x)\}$。
  - $|X|=2$：$G$ 平凡作用时两个元素都是不动主族；否则有对换，所有轮换为偶长，$R_2(X)^G=\varnothing$。∎

---

# 第二部分：完整不动记录的空间

**定理 2.1.** $\Phi_\infty:R_\infty(X)\to\beta X$ 是同胚，其中 $\beta X$ 取 Stone 拓扑（基为 $\{\widehat A\}$）。

*证明.*
- 观察拓扑的子基为 $O_{n,f,i}=\{r:r_n(f)=i\}$，且由引理 1.1(ii) 有 $\Phi(O_{n,f,i})=\widehat{f^{-1}(i)}$。
- $\widehat A=\Phi(O_{2,\chi_A,1})$；$\widehat A\cap\widehat B=\widehat{A\cap B}$，且 $\widehat X=\beta X$。所以两边的子基对应，$\{\widehat A\}$ 构成基。
- 该空间是 Hausdorff 的：若 $A\in\mathcal U\setminus\mathcal V$，则 $\widehat A$ 与 $\widehat{X\setminus A}$ 分离 $\mathcal U,\mathcal V$。
- 该空间是紧的：它是 $\prod_{(n,f)}[n]$ 的闭子空间，每个相容条件只涉及两个坐标；用 Tychonoff 定理，各因子是有限离散空间。
- 由于 $r\mapsto(gr)_n(f)=r_n(f\circ g_X)$ 仍是一个观察，$G$ 以同胚作用。∎

**定理 2.2（内在分类）.** 令 $X^F=\bigcap_{g\in F}X^g$（约定 $X^\varnothing=X$，并有 $X^F=X^{\langle F\rangle}$）。令 $\mathcal F_G(X)$ 为 $\{A:\exists$ 有限 $F\subseteq G,\ A\supseteq X^F\}$，即由不动点集生成的滤子。则 $\Phi_\infty$ 限制为同胚
$$R_\infty(X)^G\ \cong\ \beta_GX:=\{\mathcal U\in\beta X:\mathcal F_G(X)\subseteq\mathcal U\}=\bigcap_{g\in G}\widehat{X^g},$$
后者是 $\beta X$ 的闭子空间，取子空间拓扑。

用记录的语言说：$r$ 是不动记录当且仅当对每个 $g\in G$ 都有 $r_2(\chi_{X^g})=1$。当 $X=\varnothing$ 时两边都是空集。

*证明.* 由命题 1.3(v)，$\Phi(gr)=g\Phi(r)$。所以 $r$ 不动当且仅当 $\Phi(r)$ 对每个 $g$ 不变，由引理 A 这当且仅当 $X^g\in\Phi(r)$ 对每个 $g$ 成立。同胚性由定理 2.1 及子空间拓扑得到。∎

**推论 2.3（非空判准）.** $R_\infty(X)^G\ne\varnothing$ 当且仅当对每个有限 $F\subseteq G$ 都有 $X^F\neq\varnothing$，即 $G$ 的每个有限生成子群在 $X$ 上都有不动点。$X=\varnothing$ 时，$F=\varnothing$ 已使条件不成立。

*证明.* 必要性：$X^F\in\mathcal U$。充分性：$\{X^g\}$ 有 FIP，用 (U4) 取超滤子，再用定理 2.2。∎

**定理 2.4（闭包）.**
$$\overline{\eta_{\infty,X}(X^G)}=\{r\in R_\infty(X):r_2(\chi_{X^G})=1\}\cong\widehat{X^G}\subseteq R_\infty(X)^G,$$
且等号成立当且仅当存在有限 $F\subseteq G$ 使 $X^F=X^G$。

*证明.*
- $\widehat A$ 是闭集，因为其补集为 $\widehat{X\setminus A}$。
- 若 $\mathcal U\in\widehat A$ 且 $\widehat B\ni\mathcal U$，则 $A\cap B\in\mathcal U$ 非空；取其中一点 $x$，有 $\mathcal U_x\in\widehat B$。所以 $\overline{\{\mathcal U_x:x\in A\}}=\widehat A$。
- 由于 $X^G\subseteq X^g$，包含关系成立。
- 等号成立 ⟺ $X^G$ 属于每个包含 $\{X^g\}$ 的超滤子 ⟺（由 (U4) 的推论）$X^G\in\mathcal F_G(X)$ ⟺ 某个 $X^F\subseteq X^G$，即 $X^F=X^G$。∎

**定理 2.5.** 对 $G$ 的每个 $G$ 集合都有等式成立，当且仅当 $G$ 是有限生成群。

*证明.*
- 若 $G=\langle S\rangle$，$S$ 有限，则 $X^S=X^G$。
- 若 $G$ 不是有限生成的，令 $X=\bigsqcup_{H}G/H$，其中 $H$ 取遍 $G$ 的有限生成子群。
  - 由于 $H\ne G$，$G/H$ 中的点 $gH$ 不被 $G$ 固定，所以 $X^G=\varnothing$。
  - 对任意有限 $F$，陪集 $\langle F\rangle\in G/\langle F\rangle$ 被 $F$ 固定，所以 $X^F\ne\varnothing$。
  - 于是 $R_\infty(X)^G\neq\varnothing=\overline{\eta(X^G)}$。∎

**例 2.6.** 取 $G=\mathrm{FSym}(\mathbb N)$（有限支撑置换群）作用于 $X=\mathbb N$。

- $G=\bigcup_N\mathrm{Sym}(\{0,\dots,N\})$ 是可数多个有限集之并，故可数。
- $x$ 被对换 $(x\ x{+}1)$ 移动，所以 $X^G=\varnothing$。
- 对有限 $F$，$X^F=\mathbb N\setminus\bigcup_{g\in F}\mathrm{supp}\,g$ 是余有限集，非空。所以 $R_\infty(\mathbb N)^G\ne\varnothing$。
- 每个余有限集 $\mathbb N\setminus T$ 都包含 $X^{\{(t\ t+1):t\in T\}}$，所以 $\mathcal F_G$ 恰为 Fréchet 滤子。
- 超滤子包含全部余有限集 ⟺ 不含有限集 ⟺ 是非主超滤子（由 (U1)：若含有限集，则含其中某个单点）。

因此全部不动记录为
$$R_\infty(\mathbb N)^G=R_\infty(\mathbb N)\setminus\eta(\mathbb N)=\{r:\ r_2(\chi_{\{x\}})=0\ \forall x\},$$
即 $r^{\mathcal U}$，其中 $\mathcal U$ 取遍自由超滤子，记为 $\mathbb N^*=\beta\mathbb N\setminus\mathbb N$。这些记录的性质：

- 若 $f,f'$ 只在有限个点上不同，则 $r_n(f)=r_n(f')$。
- $r_n(f)$ 总是 $f$ 取无穷多次的某个值。
- 该空间紧且 Hausdorff，没有孤立点：无限集 $A$ 可分成两个无限集，二者分别含于不同的自由超滤子中。
- 基数为 $2^{\mathfrak c}$（Pospíšil 定理）。
- 闭包 $\overline{\eta(X^G)}=\varnothing$，与 $G$ 不是有限生成群一致。

---

# 第三部分：乘积比较

**命题 3.1（良定义与连续性）.**
- $p_i$ 是等变的，所以 $R_\infty(p_i)$ 把不动记录映为不动记录（命题 1.3(i)(v)），$\Pi$ 有定义。
- 在分类下 $\Pi(\mathcal W)=((p_i)_*\mathcal W)_i$。
- 连续性：
  - 观察 $s\mapsto s_n(f)$（$f:X_i\to[n]$）与 $R_\infty(p_i)$ 的复合是观察 $r\mapsto r_n(f\circ p_i)$。
  - 由始拓扑的性质，各分量连续；再由子空间与乘积拓扑的泛性质，$\Pi$ 连续。
- 空指标族：$\prod_\varnothing X_i=\{*\}$，$R_\infty(\{*\})^G=\{\eta(*)\}$（因为 $\beta\{*\}$ 为一点），目标为 $\{()\}$。$\Pi$ 是双射且连续。
- 若某个 $X_{i_0}=\varnothing$：乘积为空集，源与目标都是空集，$\Pi$ 是双射。

**定理 3.2.** 对任意 $G$ 和任意指标族，$\Pi$ 都是满射。由于是紧空间到 Hausdorff 空间的连续映射，它还是商映射。

*证明.* 设各 $X_i\ne\varnothing$，给定不变超滤子 $\mathcal U_i$。令 $\mathcal B=\{p_i^{-1}(A):A\in\mathcal U_i\}\cup\{X^g:g\in G\}$。
- 对角作用给出 $X^g=\prod_iX_i^g$。
- 有限交的形式为 $\prod_iB_i$，其中 $B_i=X_i^F\cap(\text{有限个 }A\in\mathcal U_i)$。
- 由引理 A 有 $X_i^g\in\mathcal U_i$，所以 $B_i\in\mathcal U_i$，$B_i\ne\varnothing$。由选择公理 $\prod_iB_i\ne\varnothing$，故 $\mathcal B$ 有 FIP。
- 用 (U4) 取超滤子 $\mathcal W\supseteq\mathcal B$。它含所有 $X^g$，由引理 A 是不变的。
- $(p_i)_*\mathcal W\supseteq\mathcal U_i$，由 (U3) 两者相等。∎

**定理 3.3（平凡群）.** $\Pi_{X,Y}$ 是单射当且仅当 $X$ 或 $Y$ 有限（含空集）。此时由定理 3.2，它是双射。

*证明.*
- 设 $X$ 有限且非空（$X$ 为空时显然）。
  - 由 (U2)，$(p_X)_*\mathcal W=\mathcal U_{x_0}$，所以 $\{x_0\}\times Y\in\mathcal W$。
  - 于是 $C\in\mathcal W\iff\{x_0\}\times C_{x_0}\in\mathcal W\iff C_{x_0}\in(p_Y)_*\mathcal W$，其中 $C_{x_0}=\{y:(x_0,y)\in C\}$。
  - 所以 $\mathcal W$ 由其投影决定。
- 设 $X,Y$ 都无限。
  - 取单射 $u:\mathbb N\to X$、$v:\mathbb N\to Y$，以及非主超滤子 $\mathcal V$（对 Fréchet 滤子用 (U4)）。
  - 令 $D=\{(u(n),v(n))\}$，$\mathcal W_1=\{C:\{n:(u(n),v(n))\in C\}\in\mathcal V\}$，它的投影为 $(u_*\mathcal V,v_*\mathcal V)$。
  - 令 $\mathcal W_2$ 为包含下列族的超滤子：$\{p_X^{-1}A:A\in u_*\mathcal V\}\cup\{p_Y^{-1}B:B\in v_*\mathcal V\}\cup\{(X\times Y)\setminus D\}$。
  - 该族有 FIP：$u^{-1}A$ 与 $v^{-1}B$ 都无限，可取 $n\in u^{-1}A$、$n'\in v^{-1}B$ 且 $n\ne n'$；由单射性，$(u(n),v(n'))\in(A\times B)\setminus D$。
  - 由 (U3)，$\mathcal W_2$ 的投影也是 $(u_*\mathcal V,v_*\mathcal V)$。但 $D\in\mathcal W_1\setminus\mathcal W_2$。∎

**定理 3.4.**

- **(a) 命题成立.** 设 $X$ 与 $Y$ 至少一个有限。
  - 满射性由定理 3.2 给出。
  - 不动层的 $\Pi$ 是定理 3.3 中单射的限制，故也是单射。
  - 所以 $\Pi$ 是双射，而且是紧 Hausdorff 空间之间的连续双射，因此是同胚。
- **(b) 命题不成立.** 反例取例 2.6 中的作用，$X=Y=\mathbb N$，$u=v=\mathrm{id}$，$\mathcal W_1,\mathcal W_2$ 如定理 3.3 的证明。
  - 两者的投影都是 $\mathcal V$，而 $\mathcal V$ 是非主的，含余有限集 $X^g$。
  - 所以 $(\mathbb N^2)^g=p_X^{-1}X^g\cap p_Y^{-1}X^g\in\mathcal W_j$，由引理 A，$\mathcal W_1,\mathcal W_2$ 都是不动记录。
  - 于是 $X^G=Y^G=\varnothing$，$\Pi(\mathcal W_1)=\Pi(\mathcal W_2)=(\mathcal V,\mathcal V)$，但 $\mathcal W_1\ne\mathcal W_2$：$r_2(\chi_\Delta)$ 分别为 $1,0$，其中 $\Delta$ 为对角线。
  - 反例必须用非有限生成群：若 $G$ 有限生成，由定理 2.4 两边都是空集，命题空真地成立。

---

# 结论

1. $R_m(\varnothing)=\varnothing$。对 $X\ne\varnothing$：
   - $R_1$ 为一点；
   - $R_2\cong\mathrm{SD}(X)$，即自对偶族；
   - 当 $m\ge3$ 时 $R_m\cong\beta X$，即超滤子。
   - $q_{m,k}$ 的像与纤维见命题 1.2。对有限 $G$ 集合，不动集合的判准、基数和限制映射见定理 1.4；"每个不动记录都可延拓"恰好对 $m\ge3$ 成立。
2. $R_\infty(X)^G\cong\{\mathcal U\in\beta X:X^g\in\mathcal U\ \forall g\}$，同胚。
   - 非空当且仅当每个有限生成子群都有不动点。
   - 闭包为 $\widehat{X^G}$；与不动集合相等当且仅当对某个有限 $F$ 有 $X^F=X^G$。
   - 满足"每个 $G$ 集合都相等"的群恰为有限生成群。
   - 例：$\mathrm{FSym}(\mathbb N)$ 作用于 $\mathbb N$，全部不动记录为自由超滤子，即 $\mathbb N^*$。
3. $\Pi$ 良定义、连续，且总是满射。
   - 平凡群时，单射当且仅当 $X$ 或 $Y$ 有限。
   - (a) 成立：此时比较映射是双射。
   - (b) 不成立：反例为例 2.6。