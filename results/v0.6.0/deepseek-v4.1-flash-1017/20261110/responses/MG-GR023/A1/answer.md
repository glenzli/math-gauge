# 有限测试记录与群作用

以下所有结论都在 ZFC 中解释。把空函数也算作集合之间的函数；因此当 $n=0$ 时，$X\to[0]$ 恰在 $X=\varnothing$ 时有一个元素，而目标 $[0]=\varnothing$ 没有任何元素。空族乘积按题意为单点集。

后文用“真超滤子”表示不含空集、对有限交和扩张封闭，并且对每个 $A\subseteq X$ 恰含 $A,A^c$ 之一的超滤子。记这种超滤子的集合为 $\beta X$；特别地 $\beta\varnothing=\varnothing$。对 $x\in X$，记 $p_x=\{A\subseteq X:x\in A\}$。ZFC 足以保证非空集合上的真超滤子存在。

## 0. 贯穿全文的记号和基本引理

对集合 $X$ 与 $A\subseteq X$，令
\[
\chi_A:X\longrightarrow[2],\qquad
\chi_A(x)=\begin{cases}0,&x\in A,\\1,&x\notin A.\end{cases}
\]
当 $r\in R_m(X)$ 且 $m\ge2$ 时，令
\[
\rho_r(A):=r_2(\chi_A)\in\{0,1\}. \tag{0.1}
\]
这里把 $00$ 视为零纤维是方便的画法；$\rho_r(A)=0$ 当且仅当所选零纤维包含 $A$。

对 $n\ge1$，$r_1:\operatorname{Map}(X,[1])\to[1]$ 只能是常值 $0$；$r_0$ 是唯一的空函数（在它存在的范围内）。此外，$a:[n]\to[k]$ 的常值映射强制
\[
\rho_r(\varnothing)=1,\qquad \rho_r(X)=0, \tag{0.2}
\]
而交换映射 $[2]\to[2]$ 强制
\[
\rho_r(A^c)=1-\rho_r(A). \tag{0.3}
\]
最后，当 $h:X\to Y$ 时，
\[
\rho_{R_m(h)r}(A)=\rho_r(h^{-1}A). \tag{0.4}
\]

还要用到一个关于置换不变超滤子的引理。

**引理 0.1.** 设 $T:X\to X$ 是双射，$X^T=\{x:Tx=x\}$，$\mathcal U$ 是 $X$ 上的真超滤子。若 $T_*\mathcal U=\{A:T^{-1}A\in\mathcal U\}=\mathcal U$，则 $X^T\in\mathcal U$。

证明：若 $E=X\setminus X^T\in\mathcal U$，则 $E$ 是非平凡 $T$-轨道的并。将其中无限轨道及偶长度有限轨道放在 $E_2$，将奇长度有限轨道放在 $E_3$。每一个 $E_i$ 都是 $T$-不变的。由于 $E=E_2\sqcup E_3$，超滤子恰取其中之一。在 $E_2$ 的每个轨道上按 $T$ 的迭代方向作二着色，并使 $T$ 交换两种颜色；在 $E_3$ 的每个轨道上作三着色，使 $T$ 把颜色 $0,1,2$ 循环置换。于是所取的 $E_i$ 被分成有限多个非空色类，$T$ 把这些色类循环置换；超滤子取其中一类，而 $T$-不变性又迫使它取一个不相交的下一类，矛盾。证毕。

## 1. 截断记录与有限群作用

### 1.1 对每个集合 $X$ 完全分类 $R_m(X)$

先处理空底集。对任意 $m$（包括 $m=\infty$），
\[
R_m(\varnothing)=\varnothing. \tag{1.1}
\]
原因是在 $n=0$ 时，$\operatorname{Map}(\varnothing,[0])$ 是单点集，而目标 $[0]$ 为空；若 $m\ge2$，交换 $[2]$ 的映射还会直接要求一个值同时等于 $0$ 和 $1$。

以下假设 $X\ne\varnothing$。

**情形 $m=0$ 或 $1$.** 有
\[
R_0(X)=R_1(X)=\{\ast_X\},\qquad |R_0(X)|=|R_1(X)|=1. \tag{1.2}
\]
这里 $\ast_X$ 由空的 $r_0$ 与唯一的常值 $r_1$ 组成。确实，当 $X\ne\varnothing$ 时，定义域 $\operatorname{Map}(X,[0])$ 为空；而 $\operatorname{Map}(X,[1])$ 非空，所以 $r_1$ 的唯一可能值是 $0$。

**情形 $m=2$.** 记录与函数 $\rho:\mathcal P(X)\to\{0,1\}$ 一一对应，其中 $\rho=\rho_r$ 由 (0.1) 给出，并且满足
\[
\rho(\varnothing)=1,\qquad \rho(X)=0,\qquad
\rho(A^c)=1-\rho(A)\quad(A\subseteq X). \tag{1.3}
\]
反过来，任意满足 (1.3) 的 $\rho$ 都唯一决定一个 $R_2(X)$-记录。事实上 $r_2^{-1}(0)$ 中的函数就是零纤维 $A$ 满足 $\rho(A)=0$ 的函数 $\chi_A$，而 (1.3) 正是 $[2]$ 的全部四个自映射的自然性条件。

因此 $\rho$ 只需在每一对互补集合 $\{A,A^c\}$ 上选一个值；固定的那一对 $\{\varnothing,X\}$ 已由 (1.3) 确定。若 $X$ 有 $N=|X|$ 个元素，则
\[
|R_2(X)|=2^{\,2^{N-1}-1}\qquad(N\ge1). \tag{1.4}
\]
例如 $|X|=1,2,3,4$ 时依次为 $1,2,8,128$。若 $X$ 无限且 $|X|=\kappa$，则互补配对数为 $2^\kappa$，所以 $|R_2(X)|=2^{2^\kappa}$。

**情形 $m\ge3$（包括 $m=\infty$）.** 令 $\beta X$ 表示 $X$ 上全体真超滤子。对 $\mathcal U\in\beta X$，定义
\[
r_n(f):=j\quad\Longleftrightarrow\quad f^{-1}(j)\in\mathcal U. \tag{1.5}
\]
由于 $\{f^{-1}(j):0\le j<n\}$ 是有限划分，而超滤子恰取其中一个成员，这个故事唯一且良定义。若 $a:[n]\to[k]$，那么 $a(r_n(f))=j$ 当且仅当 $(a\circ f)^{-1}(j)=f^{-1}(a^{-1}(j))\in\mathcal U$，这正是 $r_k(a\circ f)=j$。故 (1.5) 给出一个记录。

反过来，设 $r\in R_m(X)$，$m\ge3$。首先令 $\rho=\rho_r$。对任意 $h:X\to[3]$，令 $y=r_3(h)$。对每个 $S\subseteq[3]$，取 $a_S:[3]\to[2]$ 使其零纤维为 $S$。自然性给出
\[
\rho(h^{-1}(S))=1-\mathbf 1_{y\in S}. \tag{1.6}
\]
对任意 $A,B\subseteq X$，取 $h$ 的三条纤维分别为
\[
h^{-1}(0)=A\cap B,\qquad h^{-1}(1)=A\setminus B,\qquad
h^{-1}(2)=X\setminus A.
\]
把 $S=\{0\},\{0,1\},\{0,2\}$ 代入 (1.6)，得到
\[
\rho(A\cap B)=\rho(A)\wedge\rho(B). \tag{1.7}
\]
再由 (1.3) 得
\[
\rho(A\cup B)=\rho(A)\vee\rho(B).
\]
因此
\[
\mathcal U_r:=\{A\subseteq X:\rho(A)=0\} \tag{1.8}
\]
是真超滤子。(1.5) 定义的超滤子记录在 $n=0,1,2$ 层与其相同；特别地在 $n=2$ 层选择零纤维的函数正是 $\chi_A$。这核对了 (1.6) 的三条等式，故也已确定其 $r_3$。高于 $3$ 的层由 (1.5) 唯一确定，并与 $r$ 相同。于是
\[
R_m(X)\cong\beta X\qquad(m\ge3). \tag{1.9}
\]
这个同构与每个具体的 $r_2$ 一起由 $\mathcal U_r=\rho_r^{-1}(0)$ 给出。若 $X$ 是有限集，真超滤子全是主超滤子 $p_x$，故
\[
|R_m(X)|=|X|\qquad(m\ge3,\ X\ \text{有限非空}). \tag{1.10}
\]
若 $X$ 无限，$\beta X$ 还包含非主超滤子。

### 1.2 遗忘映射 $q_{m,k}$ 的像与纤维

下面的分类直接由 1.1 得到；当 $X=\varnothing$ 时，定义域、目标及所有纤维都为空，结论按空映射解释。设 $X\ne\varnothing$。

1. $q_{1,1}$ 和 $q_{2,2}$ 是恒等映射，像是整个空间，所有纤维都是单点。
2. $q_{2,1}:R_2(X)\to R_1(X)$ 是常值映射。其像是唯一的记录 $\ast_X$，唯一纤维是整个 $R_2(X)$。
3. 若 $m\ge3$ 而 $k=1$，则 $q_{m,k}$ 仍为常值映射；像是 $\{\ast_X\}$，唯一纤维是整个 $\beta X$。
4. 若 $m\ge3$ 而 $k\ge3$，则在 (1.9) 下 $q_{m,k}$ 恒等，从而是双射；像是整个 $R_k(X)$，每个纤维为单点。
5. 若 $m\ge3$ 而 $k=2$，则
   \[
   q_{m,2}(\mathcal U)=\rho_{\mathcal U},\qquad
   \rho_{\mathcal U}(A)=0\Longleftrightarrow A\in\mathcal U. \tag{1.11}
   \]
   其像是
   \[
   \{\rho_{\mathcal U}:\mathcal U\in\beta X\},
   \]
   等价地，$\rho$ 满足 (1.3) 且 $\rho^{-1}(0)$ 是超滤子。这个映射是单射，因为 $\mathcal U=\rho^{-1}(0)$ 可由像恢复；所以每个纤维至多一个点，实际上在其像上恰为单点。若 $X$ 有限，其像是 $\{\rho_x:x\in X\}$，其中
   \[
   \rho_x(A)=0\Longleftrightarrow x\in A. \tag{1.12}
   \]
   此时像只有 $|X|$ 个点，而 $R_2(X)$ 已有 (1.4) 那么多个点；所以除很小的集合外，此限制并不满。

### 1.3 与集合映射的相容性

对任意 $r\in R_m(X)$ 和 $f:X\to[n]$，若 $h:X\to Y$，则 $\bigl(R_m(h)r\bigr)_n$ 的定义域正确，且
\[
a\bigl((R_m(h)r)_n(f)\bigr)
=a(r_n(f\circ h))
=r_k(a\circ f\circ h)
=(R_m(h)r)_k(a\circ f),
\]
所以 $R_m(h)r$ 确实属于 $R_m(Y)$。显然 $R_m(\operatorname{id}_X)=\operatorname{id}$；而对 $g:X\to Y,\ k:Y\to Z$，
\[
R_m(k\circ g)=R_m(k)\circ R_m(g).
\]
遗忘映射也满足
\[
q_{m,k}\circ R_m(h)=R_k(h)\circ q_{m,k}\qquad(m\ge k\ge1).
\]
点值记录满足
\[
R_m(h)(\eta_{m,X}(x))=\eta_{m,Y}(h(x)), \tag{1.13}
\]
因为两边在 $f$ 处的值都是 $f(h(x))$。在超滤子模型中，$R_m(h)$（$m\ge3$）就是推前映射
\[
h_*\mathcal U=\{A\subseteq Y:h^{-1}A\in\mathcal U\}. \tag{1.14}
\]
在 $m=2$ 模型中，(0.4) 表明它把 $\rho$ 送到 $A\mapsto\rho(h^{-1}A)$。两种描述都验证了自然性。

### 1.4 有限 $G$-集的固定记录

设 $X$ 有限。空集仍先单独处理：由 (1.1)，对每个 $m$ 都有 $R_m(\varnothing)^G=\varnothing$。现设 $X\ne\varnothing$。

对 $m=0,1$，$R_m(X)$ 是单点集，故
\[
|R_0(X)^G|=|R_1(X)^G|=1. \tag{1.15}
\]

对 $m=2$，固定记录就是满足
\[
\rho(gA)=\rho(A)\qquad(g\in G,\ A\subseteq X) \tag{1.16}
\]
的 (1.3) 型函数。令 $\mathcal O$ 为 $G$ 作用在布尔集 $\mathcal P(X)$ 上的轨道集，补集映射 $A\mapsto A^c$ 在 $\mathcal O$ 上给出一个无固定点的对合；注意 $\varnothing$ 和 $X$ 是两个不同的固定轨道。

- 若存在轨道 $O$ 满足 $O^c=O$，则不存在固定记录：固定性要求 $\rho$ 在 $O$ 上为常数，而 (0.3) 要求在 $A$ 与 $A^c$ 处相反。
- 若没有自互补轨道，令 $s$ 为补集对合作用在 $\mathcal O$ 上的轨道数。每一对非固定的互补轨道给出一个自由二进制选择；$\{\varnothing,X\}$ 这一对则被 (0.2) 强制。因此
  \[
  |R_2(X)^G|=
  \begin{cases}
  0,&\text{存在自互补轨道},\\
  2^{s-1},,&\text{否则}.
  \end{cases} \tag{1.17}
  \]
  特别地，存在固定记录的判准就是补集不保持任何 $G$-轨道。此判准比“$X^G\ne\varnothing$”弱：若 $C_3$ 正则作用于三点集，则 $X^G=\varnothing$，但三个单点轨道与三个二点轨道配对，故 $|R_2(X)^G|=2$。另一方面，若交换映射 $C_2$ 作用于两点集，则 $\{\{x\},\{y\}\}$ 是自互补轨道，因此 $R_2(X)^{C_2}=\varnothing$。

对 $m\ge3$（包括 $m=\infty$），由 (1.10) 和超滤子分类，$X$ 有限时固定超滤子只能是主超滤子，而 $p_x$ 固定当且仅当 $x\in X^G$。故
\[
R_m(X)^G\cong X^G, \qquad
|R_m(X)^G|=|X^G|,
\qquad R_m(X)^G\ne\varnothing\Longleftrightarrow X^G\ne\varnothing. \tag{1.18}
\]
具体的同构为 $x\mapsto\eta_{m,X}(x)$。

固定集合之间的限制如下，并设 $X$ 有限非空。

- 若 $m\ge k\ge3$，则 $q_{m,k}:R_m(X)^G\to R_k(X)^G$ 是双射，并在同构 (1.18) 下等于 $X^G$ 上的恒等映射。
- 若 $m\ge3$ 且 $k=2$，则它是嵌入 $X^G\to R_2(X)^G$，$x\mapsto\rho_x$；像是 $\{\rho_x:x\in X^G\}$，每个纤维为单点。
- 若 $m\ge3$ 且 $k=1$，则它是常值映射到唯一的 $R_1(X)^G$；当 $X^G\ne\varnothing$ 时唯一纤维是整个 $X^G$，当 $X^G=\varnothing$ 时定义域与目标都为空。
- 若 $m=k=2$，则为恒等；若 $m=2,k=1$，则为从 $R_2(X)^G$ 到单点集的常值映射。

因此有限层记录延拓为完整不动记录的准确范围是：

1. $m=0,1$ 的唯一记录有完整延拓当且仅当 $X^G\ne\varnothing$；若有延拓，完整记录是 $X^G$ 中的点值记录之一。
2. $m=2$ 的固定记录 $\rho$ 有完整延拓当且仅当存在 $x\in X^G$ 使 $\rho=\rho_x$，即
   \[
   \rho(A)=0\Longleftrightarrow x\in A.
   \]
   这样的候选 $x$ 若存在则唯一，因而延拓也是唯一的。哪怕 $R_2(X)^G$ 非空，只要 $X^G=\varnothing$，所有二阶层固定记录都不能延拓。
3. $m\ge3$ 的每个固定记录都有唯一的完整延拓，沿 $q_{\infty,m}$ 延拓；在其超滤子模型中就是同一个超滤子。有限 $X$ 时每一个都对应某个 $x\in X^G$。

## 2. 完整记录、拓扑与不变超滤子

### 2.1 与 $X$ 及作用直接相关的分类

对非空 $X$，1.1 中的 (1.5) 已经给出自然双射
\[
\Phi_X:R_\infty(X)\longrightarrow\beta X,\qquad
\Phi_X(r):=\{A\subseteq X:r_2(\chi_A)=0\}. \tag{2.1}
\]
其逆映射由 (1.5) 给出。对空集，两边都为空。

在 $R_\infty(X)$ 的题设拓扑下，集合
\[
A^+:=\{r:\Phi_X(r)\ni A\}=\{r:r_2(\chi_A)=0\}
\]
是开集，并且其余集是 $\{r:r_2(\chi_A)=1\}$，所以它也是闭集。若 $f:X\to[n]$、$j\in[n]$，则
\[
\Phi_X(\{r:r_n(f)=j\})=(f^{-1}(j))^+.
\]
因此题设的“全部点值观察”拓扑正是 $\beta X$ 上的 Stone 拓扑，$\Phi_X$ 是同胚。这不是额外的分类假设，而是由 (1.5) 直接算出的：每个记录在每个测试函数上的取值只说明哪一个有限纤维属于它的超滤子。

群 $G$ 在 $\beta X$ 上的左作用为
\[
g\cdot\mathcal U:=(g_X)_*\mathcal U
=\{A\subseteq X:g_X^{-1}A\in\mathcal U\}. \tag{2.2}
\]
这与记录作用一致。由引理 0.1，$\mathcal U$ 固定当且仅当它对每个 $g\in G$ 都含有 $X^g:=\operatorname{Fix}(g)$。事实上必要性就是引理；反过来，若 $X^g\in\mathcal U$，则对 $A\in\mathcal U$，有
\[
X^g\cap A\subseteq g_X^{-1}A,\qquad
X^g\cap g_X^{-1}A\subseteq A.
\]
于是 $A\in\mathcal U\Longleftrightarrow g_X^{-1}A\in\mathcal U$。故
\[
R_\infty(X)^G\cong
\{\mathcal U\in\beta X:X^g\in\mathcal U\quad\forall g\in G\}. \tag{2.3}
\]
右边取 $\beta X$ 的子空间拓扑。这个描述只用了底集、各元素的固定点集和 Stone 拓扑，是“内在”的。

### 2.2 $R_infty(X)^G$ 何时非空

令 $\mathcal F_G$ 为 $\{X^g:g\in G\}$ 生成的滤子。由 (2.3)，$R_infty(X)^G\ne\varnothing$ 当且仅当 $\mathcal F_G$ 是真滤子，也就是这些固定点集具有有限交性质。任意有限交满足
\[
X^{g_1}\cap\cdots\cap X^{g_s}=X^{\langle g_1,\dots,g_s\rangle},
\]
其中右边是这些元素生成的子群的固定点集。于是得到准确的判准
\[
\boxed{R_\infty(X)^G\ne\varnothing
\Longleftrightarrow
X^H\ne\varnothing\quad\text{对每个有限生成子群 }H\le G.} \tag{2.4}
\]
充分性是把 $\mathcal F_G$ 扩张为超滤子；必要性来自若某个 $X^H=\varnothing$，真滤子会含有空集。

特别地，若 $G$ 有限或更一般地有限生成，则 (2.4) 退化为 $X^G\ne\varnothing$。对有限 $X$，这与 (1.18) 一致。对无限 $X$，只需要每个有限生成子群各自有固定点，不要求它们有共同的固定点；这正是非主超滤子能弥补 $X^G=\varnothing$ 的原因。

### 2.3 点值记录的闭包与相等判准

点值记录对应主超滤子 $p_x$。因此
\[
\Phi_X(\eta_{\infty,X}(X^G))=\{p_x:x\in X^G\}.
\]
若 $A:=X^G$，则主超滤子的集合 $\{p_x:x\in A\}$ 在 $\beta X$ 中的闭包是
\[
A^+:=\{\mathcal U\in\beta X:A\in\mathcal U\}. \tag{2.5}
\]
因此题所需的闭包，在 $\Phi_X$ 下是“含 $A$ 的所有真超滤子”。与 (2.3) 比较，等式成立当且仅当每个含所有 $X^g$ 的超滤子也含 $A$。由 Stone 空间的紧性，这又等价于 $A$ 属于由 $\{X^g\}$ 生成的滤子，即存在有限个 $g_1,\dots,g_s$ 使得
\[
\bigcap_{i=1}^s X^{g_i}\subseteq A.
\]
但 $A=X^G\subseteq X^H$ 对每个 $H\le G$ 成立，所以上式只能是等号。于是准确判准是
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\Longleftrightarrow
\exists H\le_{\mathrm{fg}}G,\quad X^H=X^G.} \tag{2.6}
\]
当 $X^G=\varnothing$ 时，左边为空，所以 (2.6) 同时准确描述了右边也为空的情形。

### 2.4 对所有 $G$-集都成立等式的群

由 (2.6)，一个群 $G$ 对所有 $G$-集都满足
\[
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\]
当且仅当对每个 $G$-集 $X$，$X^G$ 都是某个有限生成子群的固定点集。

**定理.** 这类群恰好是全部有限生成群。

若 $G$ 有限生成，任取 $H=G$，就有 $X^H=X^G$。反过来，设 $G$ 不有限生成。令 $X$ 为一切有限生成子群 $H\le G$ 的左陪集空间的互不相交并：
\[
X=\bigsqcup_{H\le_{\mathrm{fg}}G}G/H.
\]
每个 $G/H$ 中的陪集 $aH$ 被整个 $G$ 固定意味着 $G\subseteq aHa^{-1}$，从而 $H=G$，与 $G$ 不有限生成矛盾；所以 $X^G=\varnothing$。但任取有限生成子群 $K$，在分量 $G/K$ 中，陪集 $K$ 被 $K$ 固定，故 $X^K\ne\varnothing$。于是 (2.6) 失败，并顺带由 (2.4) 知此 $X$ 仍然有完整不动记录。证毕。

### 2.5 可数群与可数底集的具体例子

令
\[
G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N)
=\{g:\mathbb N\to\mathbb N\mid g\text{ 是双射且只有有限多个点被移动}\},
\]
并令 $G$ 自然作用于 $X=\mathbb N$。群 $G$ 可数，底集 $X$ 也可数。任何 $n\in\mathbb N$ 都被某个交换 $(n\ m)$ 移动，所以
\[
X^G=\varnothing. \tag{2.7}
\]
另一方面，任取 $\mathbb N$ 上的非主超滤子 $\mathcal U$。因为每个 $g\in G$ 的固定点集是余有限集，而每个非主超滤子都含全部余有限集，故 $X^g\in\mathcal U$。由 (2.3)，$\mathcal U$ 是固定超滤子。反过来，若固定超滤子 $\mathcal U$ 是主超滤子 $p_n$，取交换 $(n\ m)$ 就把 $n$ 移走，违反 $X^{(n\ m)}\in\mathcal U$。所以
\[
R_\infty(\mathbb N)^G
\cong\beta\mathbb N\setminus\mathbb N, \tag{2.8}
\]
其中右边是全部非主超滤子。

这就给出了 (2.7) 所需的例子。全部不动记录可以完整描述为：对每个非主超滤子 $\mathcal U\in\beta\mathbb N\setminus\mathbb N$，唯一对应一个记录
\[
r^{\mathcal U}_n(f)=j\quad\Longleftrightarrow\quad f^{-1}(j)\in\mathcal U. \tag{2.9}
\]
没有其它固定记录。此时
\[
\overline{\eta_{\infty,\mathbb N}(\mathbb N^G)}=\varnothing,
\qquad R_\infty(\mathbb N)^G\ne\varnothing;
\]
而 $G$ 不是有限生成群，这也与上一小节的群分类相容。

## 3. 乘积比较

设 $P=\prod_{i\in I}X_i$，沿每个 $p_i:P\to X_i$ 取推前。由 (2.3) 和自然性，$\Pi_{(X_i)}$ 在超滤子模型中的公式是
\[
\Pi_{(X_i)}(\mathcal U)=\bigl((p_i)_*\mathcal U\bigr)_{i\in I}. \tag{3.1}
\]
若 $\mathcal U$ 被对角 $G$-作用固定，则每个 $(p_i)_*\mathcal U$ 也被相应的 $X_i$-作用固定，因为 $p_i$ 是 $G$-等变映射。故 (3.1) 良定义。对每个测试 $f:X_i\to[n]$，
\[
((p_i)_*\mathcal U)_n(f)=j
\Longleftrightarrow \mathcal U_n(f\circ p_i)=j,
\]
所以各分量连续；因此 $\Pi$ 在乘积拓扑下连续。反方向用超滤子坐标也可直接看出它是连续同态，但连续性所需的全部就是这些测试函数的拉回。

### 3.1 任意指标族的满射性

**定理.** 对任意群 $G$、任意集合指标族 $(X_i)_{i\in I}$，$\Pi_{(X_i)}$ 恒为满射。

证明分三种边界情形。若 $I=\varnothing$，则 $P$ 是单点集，两边都只有唯一的固定记录，$\Pi$ 是双射。若某个 $X_i=\varnothing$，则 $P=\varnothing$，由 (1.1) 有 $R_\infty(P)=\varnothing$，而右边也因含空因子 $R_\infty(X_i)=\varnothing$ 而为空，所以从空集到空集的唯一映射是满射。

现在设所有 $X_i$ 非空。取右边一点，即每个 $\mathcal U_i\in\beta X_i$ 都在 $G$-作用下固定。考虑集合族
\[
\left\{
P^H\cap\bigcap_{i\in F}p_i^{-1}B_i:
H\le_{\mathrm{fg}}G,\ F\subseteq I\text{ 有限},
B_i\in\mathcal U_i\right\}. \tag{3.2}
\]
其中 $P^H$ 是 $H$ 在 $P$ 上的公共固定点集。对每个 $i\in F$，由固定性有 $X_i^H\in\mathcal U_i$，所以可取
\[
x_i\in B_i\cap X_i^H;
\]
对 $i\notin F$，任取 $x_i\in X_i^H$。于是 $x=(x_i)_{i\in I}\in P^H$，并且在每个 $p_i^{-1}B_i$ 中。这说明 (3.2) 的任意有限交非空。把生成的滤子扩张成 $P$ 上的超滤子 $\mathcal U$。它包含所有 $p_i^{-1}B_i$，故
\[
\mathcal U_i\subseteq(p_i)_*\mathcal U;
\]
两者都是超滤子，所以相等。它又包含每个 $P^H$，特别地包含每个 $P^g$，故由 (2.3) 是 $G$-固定的。因此预像是非空的。证毕。

所以尽管 $\Pi$ 通常不是双射，满射性没有有限性、可数性或指标集大小的限制。

### 3.2 平凡群：两因子比较何时为单射

令 $G=\{e\}$。此时 $R_\infty(X)\cong\beta X$（空集对应空集），两因子比较为
\[
\Pi_{X,Y}:\beta(X\times Y)\longrightarrow\beta X\times\beta Y. \tag{3.3}
\]

**定理.** (3.3) 是单射当且仅当 $X$ 或 $Y$ 有限。

若 $X$ 有限，取两个超滤子 $\mathcal U,\mathcal V\in\beta(X\times Y)$，并设其 $X$-投影相同。有限集上的超滤子是主超滤子；设该投影为 $p_x$。于是两个超滤子都含 $\{x\}\times Y$。对任意 $A\subseteq X\times Y$，在纤维 $\{x\}\times Y$ 上判断 $A$ 是否属于 $\mathcal U$，只依赖于 $Y$-投影的同一个超滤子；因为 $Y$-投影也相同，故 $A\in\mathcal U\Leftrightarrow A\in\mathcal V$。所以 $\mathcal U=\mathcal V$。若 $X=\varnothing$ 或 $Y=\varnothing$，两边同样为空并映射为空映射。

反之设 $X,Y$ 都无限。选取可数无限子集 $X_0\subseteq X,Y_0\subseteq Y$，与 $\mathbb N$ 双射。取 $\mathbb N$ 的两个非主超滤子 $\mathcal U,\mathcal V$，并令
\[
\mathcal A=\{(m,n)\in\mathbb N^2:m+n\equiv0\pmod2\}.
\]
矩形族
\[
\{B\times C:B\in\mathcal U,\ C\in\mathcal V\}
\]
具有有限交性质；例如有限交含有一个 $B'\times C'$，且 $B',C'$ 无限。把上述矩形族分别与 $\mathcal A$ 或 $\mathcal A^c$ 相交，再生成的滤子也各自具有有限交性质，因为无限矩形与两种奇偶类都相交。将其分别扩张为 $\mathbb N^2$ 上的超滤子 $\mathcal W_+,\mathcal W_-$。二者投影恰为 $\mathcal U,\mathcal V$，但一个含 $\mathcal A$、另一个含 $\mathcal A^c$，所以不同。沿嵌入 $X_0\times Y_0\hookrightarrow X\times Y$ 推前，就得到两个不同超滤子具有相同的 $X$-和 $Y$-投影。因此 (3.3) 不是单射。证毕。

### 3.3 任意群的两个全称命题的判定

**命题 I（真）.** 对任意 $G$-集 $X,Y$，若 $X$ 或 $Y$ 至少一个有限，则
\[
\Pi_{(X,Y)}:R_\infty(X\times Y)^G
\longrightarrow R_\infty(X)^G\times R_\infty(Y)^G \tag{3.4}
\]
是双射。

证明：3.1 已证明任意两因子情形都满射。现证单射。假设 $X$ 有限。取两个固定超滤子 $\mathcal U,\mathcal V\in\beta(X\times Y)$，并设它们的两个投影分别相同。$\mathcal U$ 在有限集 $X$ 上的投影是主管超滤子 $p_x$，所以 $\{x\}\times Y\in\mathcal U$；同理对 $\mathcal V$。在这个共同纤维上，两超滤子的 $Y$-投影相同，故它们对纤维的每个子集给出一致判定。由扩张性，$\mathcal U$ 和 $\mathcal V$ 对整个 $X\times Y$ 的每个子集给出一致判定，因而相等。$Y$ 有限时对称。空集情形也由约定直接成立。满射加单射即双射。

**命题 II（假）.** “若 $X^G=Y^G=\varnothing$，则 (3.4) 必为单射”并非全称命题。用 2.5 的 $G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N)$ 和 $X=Y=\mathbb N$ 给出反例。

取任意非主超滤子 $\mathcal U\in\beta\mathbb N$。如 2.5 所述，$\mathcal U$ 在自然作用下固定，并且两个因子都没有固定点。令 $P=\mathbb N^2$，作集合族
\[
\mathcal B=\left\{
(B\times C)\cap(F\times F):
B,C\in\mathcal U,\ F\subseteq\mathbb N\text{ 余有限}
\right\}. \tag{3.5}
\]
它对有限交封闭到一个矩形与一个余有限方块的交；因 $B,C,F$ 都无限，这些交非空。再令
\[
\mathcal A=\{(m,n):m+n\text{ 为偶数}\}. \tag{3.6}
\]
在 (3.5) 的每个成员中，$\mathcal A$ 与 $\mathcal A^c$ 都有点，所以分别加入 $\mathcal A$ 或 $\mathcal A^c$ 后仍具有有限交性质。分别扩张成两个超滤子 $\mathcal W_+$ 和 $\mathcal W_-$。

两个超滤子都含全部方块 $F\times F$（$F$ 余有限）。对角作用的非恒等置换 $g$ 在 $P$ 上的固定点集正是 $X^g\times X^g$，而 $X^g$ 余有限。因此由 (2.3)，$\mathcal W_+$ 和 $\mathcal W_-$ 都在对角 $G$-作用下固定。它们也分别含相互补的 $\mathcal A,\mathcal A^c$，故不同。可是它们都含有所有 $B\times C$ 型柱集，$B,C\in\mathcal U$，所以两个投影都恰为 $\mathcal U$。故 (3.4) 把两个不同的固定记录送到同一个二元组。命题 II 为假。

这同时显示了第一部分关于无固定点的结论不能提高为“非主不变超滤子必为点值记录”；非主不变超滤子正是完整层与有限层之间真正产生差异的对象。

## 结论汇总

- 空底集：$R_m(\varnothing)=\varnothing$。非空有限 $X$：$R_0(X)$、$R_1(X)$ 各一点；$R_2(X)$ 由满足互补条件的二元赋值 (1.3) 分类，计数为 (1.4)；$m\ge3$ 时 $R_m(X)\cong X$。任意非空 $X$：$m\ge3$ 时 $R_m(X)\cong\beta X$。
- $q_{m,k}$ 只有在 $k\ge3$ 且 $m\ge3$ 时为双射；$k=2$ 时为超滤子求值嵌入；$k=1$ 时为常值映射。
- 完整不动记录与包含所有 $\operatorname{Fix}(g)$ 的真超滤子一一对应；非空判准为每个有限生成子群都有固定点。点值固定记录的闭包与完整固定记录空间相等，当且仅当某个有限生成子群的固定点集恰好等于 $X^G$。群对所有 $G$-集满足该等式当且仅当群有限生成。
- 乘积比较对任意群和任意集合指标族都满射且连续；若任何因子为空，或指标族为空，边界情形也分别退化为相应的空映射或单点双射。
- 平凡群的两因子比较为单射当且仅当至少一个底集有限；任意群下“至少一个因子有限推出双射”成立；而“两因子都没有不动点则比较为单射”不成立，$\operatorname{Sym}_{\mathrm{fin}}(\mathbb N)$ 在 $\mathbb N$ 上的自然作用给出反例。
