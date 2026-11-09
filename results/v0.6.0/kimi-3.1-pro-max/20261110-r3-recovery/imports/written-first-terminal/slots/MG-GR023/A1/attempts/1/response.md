以下把集合 \(X\) 上的超滤子全体记为 \(\beta X\)，并令
\[
C_A=\{U\in\beta X:A\in U\}\qquad(A\subseteq X).
\]
主超滤子记为 \(\delta_x\)。

## 1. 截断、相容性及有限底集上的不动记录

### 1.1 \(R_m(X)\) 的完全分类

首先，由 \(n=0\) 的测试立得
\[
R_m(\varnothing)=\varnothing\qquad(m\geq1).
\]
事实上， \(\operatorname{Map}(\varnothing,[0])\) 有一个元素，而不存在从单点集到 \(\varnothing\) 的函数 \(r_0\)。

若 \(X\neq\varnothing\)，则 \(r_0\) 唯一存在，而 \(r_1\) 也被唯一确定。因此
\[
R_1(X)\cong 1.
\]

对 \(m\geq2\)（包括 \(m=\infty\)），有自然双射
\[
\boxed{\quad R_m(X)\cong\beta X.\quad}
\]
具体构造如下。给定 \(U\in\beta X\)，定义 \(r^U\in R_m(X)\) 为
\[
r_n^U(f)=\text{唯一满足 }f^{-1}(i)\in U\text{ 的 }i\in[n].
\]
因为 \(f^{-1}(0),\ldots,f^{-1}(n-1)\) 是 \(X\) 的有限划分，这样的 \(i\) 恰好有一个。若 \(a:[n]\to[k]\)，且 \(f^{-1}(i)\in U\)，则
\[
(a\circ f)^{-1}(a(i))\supseteq f^{-1}(i),
\]
故 \((a\circ f)^{-1}(a(i))\in U\)，从而
\[
a(r_n^U(f))=r_k^U(a\circ f).
\]
所以 \(r^U\) 确实属于 \(R_m(X)\)。

反过来，给定 \(r\in R_m(X)\)，定义
\[
U_r=\{A\subseteq X:r_2(\chi_A)=1\},
\]
其中 \(\chi_A:X\to[2]\) 在 \(A\) 上取值 \(1\)。由相容性可知：

- \(\varnothing\notin U_r\)，而 \(X\in U_r\)；
- \(U_r\) 对有限交和超集封闭；
- 对任意 \(A\subseteq X\)，\(A\) 与 \(X\setminus A\) 恰有一个属于 \(U_r\)。

所以 \(U_r\) 是超滤子。并且对任意 \(f:X\to[n]\)，若 \(i=r_n(f)\)，取 \(a:[n]\to[2]\) 为 \(\{i\}\) 的特征函数，则
\[
r_2(\chi_{f^{-1}(i)})=a(r_n(f))=1.
\]
故 \(f^{-1}(i)\in U_r\)，从而 \(r=r^{U_r}\)。这两个构造互为逆映射。

### 1.2 截断映射的像与纤维

设 \(X\neq\varnothing\)，\(m\geq k\geq1\)。

- 若 \(k=1\)，则 \(R_k(X)\cong1\)，所以 \(q_{m,k}\) 是唯一映射；其像为单点集，唯一纤维是整个 \(R_m(X)\)。
- 若 \(k\geq2\)，在上述与 \(\beta X\) 的认同下，
  \[
  q_{m,k}=\operatorname{id}_{\beta X}.
  \]
  因而它是双射，所有纤维均为单点集。

若 \(X=\varnothing\)，则所有相关集合和映射均为空。

### 1.3 与集合映射的相容性

对 \(h:X\to Y\)，直接由定义可得函子性
\[
R_m(\operatorname{id}_X)=\operatorname{id},\qquad
R_m(h'\circ h)=R_m(h')\circ R_m(h),
\]
以及
\[
q_{m,k}\circ R_m(h)=R_k(h)\circ q_{m,k}.
\]
在 \(m\geq2\) 时，上述双射下 \(R_m(h)\) 就是超滤子的推出：
\[
\boxed{\quad R_m(h)(U)=h_*U
=\{B\subseteq Y:h^{-1}(B)\in U\}.\quad}
\]
点值记录满足
\[
\eta_{m,X}(x)=
\begin{cases}
\delta_x,&m\geq2,\\[2mm]
R_1(X)\text{ 的唯一元素},&m=1,
\end{cases}
\]
并且
\[
R_m(h)\circ\eta_{m,X}=\eta_{m,Y}\circ h,\qquad
q_{m,k}\circ\eta_{m,X}=\eta_{k,X}.
\]

### 1.4 有限 \(G\)-集合上的不动记录

现在设 \(X\) 有限。此时 \(\beta X=X\)，所有超滤子均为主超滤子，并且
\[
g_*\delta_x=\delta_{gx}.
\]
因此：

- 若 \(X=\varnothing\)，则 \(R_m(X)^G=\varnothing\)，基数为 \(0\)。
- 若 \(X\neq\varnothing\) 且 \(m=1\)，则 \(R_1(X)^G\) 为单点集，基数为 \(1\)，无论 \(X^G\) 是否为空。
- 若 \(m\geq2\)，则
  \[
  \boxed{\quad R_m(X)^G=\{\delta_x:x\in X^G\}\cong X^G,\quad
  |R_m(X)^G|=|X^G|.\quad}
  \]
  它非空当且仅当 \(X^G\neq\varnothing\)。

限制映射随之完全确定：

- \(m\geq k\geq2\) 时，\(q_{m,k}\) 在不动记录上就是
  \[
  X^G\longrightarrow X^G,\qquad x\longmapsto x,
 \]
  因而是双射。
- \(k=1\) 且 \(X\neq\varnothing\) 时，目标是单点集；若源非空，则所有元素都被送到该唯一点，若源为空则映射为空。

特别地，有限层不动记录向完整不动记录的延拓情况为：

1. \(m\geq2\)：每个 \(r\in R_m(X)^G\) 都是某个 \(x\in X^G\) 的 \(\delta_x\)，并有唯一完整延拓，即 \(R_\infty(X)^G\) 中同一个 \(\delta_x\)。
2. \(m=1\)、\(X\neq\varnothing\)：唯一的不动记录存在完整不动延拓，当且仅当 \(X^G\neq\varnothing\)。此时其全部延拓恰好是
   \[
   \{\delta_x:x\in X^G\}.
   \]
   若 \(X^G=\varnothing\)，它没有完整不动延拓。
3. \(X=\varnothing\)：各层均无不不动记录。

---

## 2. 完整不动记录及其拓扑

### 2.1 单个置换的不动超滤子

关键在于以下引理。

**引理.** 设 \(s:X\to X\) 是双射，\(U\in\beta X\)。则
\[
\boxed{\quad s_*U=U\quad\Longleftrightarrow\quad X^s\in U,\quad}
\]
其中 \(X^s=\{x:sx=x\}\)。

**证明.** 若 \(X^s\in U\)，则对任意 \(A\subseteq X\)，
\[
A\cap X^s=s^{-1}(A)\cap X^s,
\]
所以 \(A\in U\iff s^{-1}(A)\in U\)，即 \(s_*U=U\)。

反过来，设 \(s_*U=U\)，但 \(B=X\setminus X^s\in U\)。在 \(B\) 的每条 \(s\)-轨道上选取起点，并沿轨道周期性地用颜色 \(0,1,2\) 染色；有限轨道长度至少为 \(2\)，无限轨道按 \(\mathbb Z\) 编号。这样，任意轨道上都不存在三个相继点具有同一颜色（有限轨道回绕处最多出现两个相继同色点）。

三个颜色类划分 \(B\)，故恰有一个颜色类 \(A\) 属于 \(U\)。由 \(s_*U=U\)，集合
\[
A,\quad s^{-1}A,\quad s^{-2}A
\]
都属于 \(U\)。但
\[
A\cap s^{-1}A\cap s^{-2}A
=\{x:x,sx,s^2x\text{ 同色}\}=\varnothing,
\]
矛盾。因此 \(X^s\in U\)。∎

### 2.2 不动记录的内在分类及非空判准

令 \(\mathcal F_G(X)\) 是由
\[
\{X^g:g\in G\}
\]
生成的滤子。有限交为
\[
X^{g_1}\cap\cdots\cap X^{g_k}
=X^{\langle g_1,\ldots,g_k\rangle}.
\]
由上述引理立即得到
\[
\boxed{\quad
R_\infty(X)^G\cong
\{U\in\beta X:\mathcal F_G(X)\subseteq U\}.\quad}
\]
等价地，这些就是包含所有 \(X^H\) 的超滤子，其中 \(H\) 遍历 \(G\) 的有限生成子群。

因此，由超滤子引理，
\[
\boxed{\quad
R_\infty(X)^G\neq\varnothing
\iff
\text{对每个有限集 }F\subseteq G,\ X^F\neq\varnothing .
\quad}
\]
也可表述为：每个有限生成子群 \(H\leq G\) 都在 \(X\) 中有不动点。特别地，若 \(G\) 本身有限生成，这等价于 \(X^G\neq\varnothing\)。

还有一种等价的布尔代数描述：令
\[
\mathcal I_G=
\{A\subseteq X:\text{存在有限生成 }H\leq G
\text{ 使 }A\cap X^H=\varnothing\}.
\]
则不动记录空间就是商布尔代数 \(\mathcal P(X)/\mathcal I_G\) 的 Stone 空间。

### 2.3 与观察拓扑的相容性

在 \(R_\infty(X)\cong\beta X\) 下，
\[
\{r:r_n(f)=i\}=C_{f^{-1}(i)}.
\]
反之，每个 \(C_A\) 都是观察 \(r_2(\chi_A)\) 的开条件。因此题给拓扑恰是 \(\beta X\) 的通常 Stone 拓扑，以
\[
C_A\qquad(A\subseteq X)
\]
为既开又闭的基本集；并且
\[
C_A\cap C_B=C_{A\cap B},\qquad
\beta X\setminus C_A=C_{X\setminus A}.
\]
所以 \(R_\infty(X)\) 是紧 Hausdorff 空间，而
\[
R_\infty(X)^G=\bigcap_{g\in G}C_{X^g}
\]
是其闭子空间。

### 2.4 点值记录的闭包及等式判准

记 \(A=X^G\)。在 \(\beta X\) 中有标准事实
\[
\boxed{\quad
\overline{\eta_{\infty,X}(X^G)}
=C_{X^G}
=\{U\in\beta X:X^G\in U\}.\quad}
\]
确实，若 \(A\in U\)，则任意 \(B\in U\) 都与 \(A\) 相交，所以 \(C_B\) 中含有某个 \(\delta_x\)，\(x\in A\)；若 \(A\notin U\)，则 \(C_{X\setminus A}\) 是 \(U\) 的邻域且不含任何所讨论的点值记录。\(A=\varnothing\) 时两边也都是空集。

由于总有 \(X^G\subseteq X^F\)，恒有
\[
C_{X^G}\subseteq R_\infty(X)^G.
\]
两者相等的充要条件是
\[
\boxed{\quad
\text{存在有限集 }F\subseteq G
\text{ 使得 }X^F=X^G.\quad}
\]

证明如下。若这样的 \(F\) 存在，则 \(X^G=X^F\in\mathcal F_G(X)\)，所以每个不动超滤子都包含 \(X^G\)。反之，若不存在这样的 \(F\)，则对每个有限 \(F\subseteq G\)，都有
\[
X^F\cap(X\setminus X^G)\neq\varnothing.
\]
因此 \(\mathcal F_G(X)\cup\{X\setminus X^G\}\) 具有限交性质，可延拓为超滤子 \(U\)。这个 \(U\) 是 \(G\)-不动的，但 \(X^G\notin U\)，故不在点值记录集的闭包中。

### 2.5 对所有 \(G\)-集合都满足等式的群

\[
\boxed{\quad
\text{以下性质对所有 }G\text{-集合 }X\text{ 都成立}
\iff G\text{ 有限生成}.\quad}
\]
这里的性质是
\[
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G.
\]

若 \(G\) 由有限集 \(F\) 生成，则 \(X^F=X^G\) 对所有 \(X\) 成立，故充分性由上一判准得到。

若 \(G\) 非有限生成，令 \(\mathcal H\) 为其全部有限生成子群，并取
\[
X=\bigsqcup_{H\in\mathcal H}G/H,
\]
各因子按左平移作用。对任意有限 \(F\subseteq G\)，令 \(H=\langle F\rangle\)，则分量 \(G/H\) 中的陪集 \(H\) 被 \(F\) 固定，所以 \(X^F\neq\varnothing\)，从而 \(R_\infty(X)^G\neq\varnothing\)。

另一方面，若某个陪集 \(gH\) 被整个 \(G\) 固定，则 \(G\subseteq gHg^{-1}\)，这将使 \(G\) 成为有限生成群，矛盾。因此 \(X^G=\varnothing\)。于是点值记录闭包为空，而不动记录空间非空，等式失败。

### 2.6 一个群和底集均可数的例子

取 Prüfer \(2\)-群
\[
G=C_{2^\infty}=\{z\in\mathbb C^\times:
z^{2^n}=1\text{ 对某个 }n\},
\]
并令 \(G_n\) 为其唯一的阶 \(2^n\) 子群。于是
\[
G_0<G_1<G_2<\cdots,\qquad G=\bigcup_nG_n.
\]
取
\[
X_n=G/G_n,\qquad X=\bigsqcup_{n\geq0}X_n,
\]
\(G\) 在每个 \(X_n\) 上左平移。\(G\) 和 \(X\) 均可数。

\(X_n\) 中每个点的稳定子都是 \(G_n\)。因此，若有限集 \(F\subseteq G\) 生成 \(G_N\)，则
\[
X^F=T_N:=\bigsqcup_{n\geq N}X_n.
\]
特别地 \(X^G=\varnothing\)，而所有 \(T_N\) 非空，故完整不动记录非空。

其全部不动记录可完整描述为
\[
\boxed{\quad
R_\infty(X)^G\cong
\{U\in\beta X:T_N\in U\text{ 对所有 }N\}.\quad}
\]
等价地，这些超滤子的任何成员都不能只包含在有限多个分量 \(X_n\) 的并中。对应记录仍由
\[
r_k^U(f)=\text{唯一使 }f^{-1}(i)\in U\text{ 的 }i
\]
给出。由于尾滤子 \(\{T_N\}\) 具有限交性质，这样的超滤子存在；以上条件就是全部条件，没有额外限制。

---

## 3. 乘积比较映射

### 3.1 良定义与连续性

令 \(P=\prod_iX_i\)，\(p_i:P\to X_i\)。因为
\[
p_i\circ g_P=g_{X_i}\circ p_i,
\]
由函子性，若 \(r\) 是 \(G\)-不动的，则
\[
g_{X_i}\cdot R_\infty(p_i)r
=R_\infty(p_i)(g_P\cdot r)
=R_\infty(p_i)r.
\]
所以 \(\Pi_{(X_i)}\) 良定义。

其第 \(i\) 个坐标上的观察满足
\[
\bigl((\Pi_{(X_i)}r)_i\bigr)_n(f)
=r_n(f\circ p_i).
\]
故每个坐标映射都连续，从而 \(\Pi_{(X_i)}\) 对积拓扑连续。

### 3.2 对任意群和任意指标族均为满射

\[
\boxed{\quad \Pi_{(X_i)}\text{ 对所有 }G\text{ 和所有指标族都是满射。}\quad}
\]

先处理退化情形：

- 若 \(I=\varnothing\)，则 \(P=1\)，其作用平凡，\(R_\infty(P)^G\) 和空积目标均为单点集，映射为双射。
- 若某个 \(X_i=\varnothing\)，则 \(P=\varnothing\)，源为空；目标也因该空因子而为空，故映射为满射。

现设 \(P\neq\varnothing\)。给定各坐标的不动超滤子 \(U_i\)，考虑以下集合族：

1. 所有柱集 \(p_i^{-1}(A_i)\)，其中 \(A_i\in U_i\)；
2. 所有 \(P^H=\prod_iX_i^H\)，其中 \(H\leq G\) 有限生成。

证明该族具有限交性质。任意有限个柱集的交可写成
\[
C=\{x\in P:x_i\in A_i\ (i\in F)\},
\]
其中 \(F\subseteq I\) 有限，\(A_i\in U_i\)。有限多个 \(P^{H_j}\) 的交仍是 \(P^H\)，其中 \(H=\langle H_j:j\rangle\) 有限生成。因为 \(U_i\) 不动，\(X_i^H\in U_i\)，所以：

- 对 \(i\in F\)，\(A_i\cap X_i^H\in U_i\)，故非空；
- 对其余 \(i\)，\(X_i^H\) 也非空。

用选择公理选取相应坐标，即得 \(C\cap P^H\neq\varnothing\)。

于是可将上述集合族延拓为 \(P\) 上的超滤子 \(U\)。包含所有 \(P^H\) 表明 \(U\) 是 \(G\)-不动的；包含所有柱集表明
\[
(p_i)_*U\supseteq U_i.
\]
两边都是超滤子，故 \((p_i)_*U=U_i\)。这证明了满射性。

### 3.3 平凡群时两因子比较映射的单射判准

对平凡群，
\[
\boxed{\quad
\Pi_{X,Y}\text{ 单射}
\iff X,Y\text{ 中至少一个有限}.\quad}
\]
结合上述满射性，这也正好是它为双射的判准。

先设 \(X\) 有限。对任意 \(W\in\beta(X\times Y)\)，其在 \(X\) 上的边缘是某个主超滤子 \(\delta_x\)，所以
\[
\{x\}\times Y\in W.
\]
若另一个边缘为 \(V\)，则对任意 \(A\subseteq X\times Y\)，
\[
A\in W
\iff
\{y\in Y:(x,y)\in A\}\in V.
\]
因此 \(W\) 由两个边缘唯一确定，单射成立。\(Y\) 有限时同理；空集情形也已包含。

下面证明两个因子均无限时不单射。先给出 \(\mathbb N\) 上的构造。设 \(U,V\) 是 \(\mathbb N\) 上的非主超滤子，定义
\[
W_1=
\{A\subseteq\mathbb N^2:
\{m:\{n:(m,n)\in A\}\in V\}\in U\},
\]
以及交换次序的
\[
W_2=
\{A\subseteq\mathbb N^2:
\{n:\{m:(m,n)\in A\}\in U\}\in V\}.
\]
两者都是超滤子，且两个边缘分别为 \(U,V\)。

取
\[
A=\{(m,n):m<n\}.
\]
对每个 \(m\)，\(\{n:m<n\}\) 是余有限集，故属于 \(V\)，所以 \(A\in W_1\)。而对每个 \(n\)，\(\{m:m<n\}\) 是有限集，故不属于 \(U\)，所以 \(A\notin W_2\)。因此 \(W_1\neq W_2\)。

对一般无限 \(X,Y\)，选取可数无限子集 \(X_0,Y_0\)，在 \(X_0\times Y_0\) 上作上述构造，再沿包含映射推到 \(X\times Y\)。所得两个超滤子仍有相同边缘但互不相同，故比较映射不单射。

### 3.4 至少一个因子有限时，对任意作用均为双射

\[
\boxed{\quad
\text{若 }X,Y\text{ 至少一个有限，则 }
R_\infty(X\times Y)^G\to
R_\infty(X)^G\times R_\infty(Y)^G
\text{ 为双射}.\quad}
\]

满射性已经在一般指标族情形证明。单射性的证明与平凡群情形完全相同：若 \(X\) 有限，任何 \(W\) 在 \(X\) 上的边缘都是某个 \(\delta_x\)，于是 \(W\) 集中于 \(\{x\}\times Y\)，并由其在 \(Y\) 上的边缘唯一确定。\(Y\) 有限时对称处理；若出现空底集，两边均为空，结论仍成立。

### 3.5 “均无不动点则单射”不成立

\[
\boxed{\quad
X^G=Y^G=\varnothing
\text{ 并不能推出两因子比较映射单射}.\quad}
\]

使用第 2.6 节的可数例子，并取 \(Y=X\)。任取一个不动超滤子 \(U\)。因为 \(X^G=\varnothing\)，\(U\) 必为非主超滤子。任取 \(X\) 与 \(\mathbb N\) 的双射，按上一节的公式构造 \(W_1,W_2\)，它们的两个边缘都等于 \(U\)，且 \(W_1\neq W_2\)。

还需确认它们都是 \(G\)-不动的。对任意有限生成子群 \(H\leq G\)，有 \(X^H\in U\)。而乘积中的不动点集为
\[
(X\times X)^H=X^H\times X^H.
\]
由 \(W_1,W_2\) 的定义，任何形如 \(C\times D\)（\(C,D\in U\)）的矩形都属于这两个超滤子，故它们都包含完整的乘积不动点滤子，从而是 \(G\)-不动的。

于是 \(W_1,W_2\) 在 \(\Pi_{X,X}\) 下有相同像 \((U,U)\)，却不相等，构成了所要求的反例。