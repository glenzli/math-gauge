记
\[
\operatorname{Fix}_X(F)=\{x\in X:gx=x\text{ 对所有 }g\in F\},
\qquad F\subseteq G.
\]
特别地，\(\operatorname{Fix}_X(\varnothing)=X\)，且 \(\operatorname{Fix}_X(G)=X^G\)。下面把超滤子都理解为**真超滤子**；空集上没有真超滤子。

主要结论是：从三元测试开始，记录恰为超滤子；二元测试则只要求对互补子集作一致选择。完整不动记录恰为包含每个 \(\operatorname{Fix}_X(g)\) 的超滤子。

## 1. 截断、相容性和有限作用

### 所有记录的分类

若 \(X=\varnothing\)，则对每个 \(m\)，都有
\[
R_m(X)=\varnothing.
\]
因为 \(\operatorname{Map}(\varnothing,[0])\) 是单点集，不能存在从它到 \([0]=\varnothing\) 的函数。

以下设 \(X\ne\varnothing\)。对 \(A\subseteq X\)，写 \(1_A:X\to[2]\) 为示性函数。一个二元记录确定子集族
\[
\mathcal C_r=\{A\subseteq X:r_2(1_A)=1\}.
\]
则：

- \(R_1(X)\) 是单点集。
- \(R_2(X)\) 等同于所有满足
  \[
  X\in\mathcal C,\qquad
  \text{对每个 }A\subseteq X，\quad
  A\in\mathcal C\ \Longleftrightarrow\ X\setminus A\notin\mathcal C
  \tag{1}
  \]
  的子集族 \(\mathcal C\)。
- 对每个 \(3\le m\le\infty\)，\(R_m(X)\) 等同于 \(X\) 上的真超滤子集合 \(\operatorname{Ult}(X)\)。

在最后一种情形，超滤子 \(U\) 对应的记录由
\[
r_n(f)=\text{满足 }f^{-1}(\{j\})\in U\text{ 的唯一 }j\in[n]
\tag{2}
\]
给出。有限分割中恰有一个部分属于超滤子，所以它存在且唯一；\(n=0\) 时，由于 \(X\ne\varnothing\)，没有需要赋值的 \(f:X\to[0]\)。

**证明。** 对 \(m=1\)，唯一非空测试的值只能是 \(0\)。对 \(m=2\)，把常值映射和交换 \([2]\) 两点的映射代入自然性，恰得到 (1)。反过来，任意满足 (1) 的 \(\mathcal C\) 决定所有二元测试的值；逐一检查 \([1]\) 与 \([2]\) 之间的映射，便得到自然性。

设 \(m\ge3\)。记录仍确定满足 (1) 的 \(\mathcal C\)。若 \(A,B\in\mathcal C\)，考虑至多三个部分组成的分割
\[
A\cap B,\qquad A\setminus B,\qquad X\setminus A.
\]
记录选择其中一个部分。与分割到示性函数 \(1_A,1_B\) 的合并映射相容，迫使所选部分是 \(A\cap B\)。因此 \(\mathcal C\) 对有限交封闭；结合 (1)，它是真超滤子。反之，(2) 对任何有限测试定义记录，且合并分割时所选部分合并到所选部分，故满足自然性。两种构造互逆。由于三元记录已经确定超滤子，也就唯一确定全部更大测试。

### 遗忘映射及其纤维

在以上识别下，对 \(X\ne\varnothing\)：

1. 若 \(k=1\)，则 \(q_{m,1}\) 是到单点集的唯一映射；其唯一纤维是整个 \(R_m(X)\)。
2. 若 \(m,k\ge3\)，则 \(q_{m,k}\) 是 \(\operatorname{Ult}(X)\) 上的恒等映射。
3. 若 \(m\ge3,\ k=2\)，则 \(q_{m,2}\) 把超滤子视为满足 (1) 的子集族。它是单射，其像恰为那些还对有限交封闭的 \(\mathcal C\)。因此，某个 \(\mathcal C\in R_2(X)\) 的纤维在它对有限交封闭时为单点，否则为空。
4. \(q_{2,2}\) 和 \(q_{1,1}\) 是恒等映射。

\(X=\varnothing\) 时，相关集合、像和纤维均为空。

这些识别与集合映射相容：对 \(h:X\to Y\)，二元选择和超滤子都按逆像推送，
\[
h_*\mathcal C=\{B\subseteq Y:h^{-1}(B)\in\mathcal C\}.
\tag{3}
\]
在超滤子情形它仍是真超滤子。直接由定义，
\[
q_{m,k}\circ R_m(h)=R_k(h)\circ q_{m,k},
\qquad
R_m(h)\eta_{m,X}=\eta_{m,Y}h.
\]
其中点值记录对应主超滤子
\[
\delta_x=\{A\subseteq X:x\in A\}.
\]

### 有限 \(G\) 集合

设 \(X\) 是有限 \(G\) 集合，\(G\) 本身不必有限。若 \(X=\varnothing\)，所有不动记录集合均为空。以下设 \(X\ne\varnothing\)。

- \(R_1(X)^G\) 是单点集。
- 每个有限集合上的超滤子都是主超滤子。因此对 \(m\ge3\)，
  \[
  R_m(X)^G=\{\delta_x:x\in X^G\},
  \qquad |R_m(X)^G|=|X^G|.
  \tag{4}
  \]
- 对 \(m=2\)，令 \(G\) 作用于互补对子
  \[
  \{A,X\setminus A\},\qquad A\subseteq X.
  \]
  若存在 \(g\in G\) 和 \(A\subseteq X\) 使
  \[
  gA=X\setminus A,
  \tag{5}
  \]
  则 \(R_2(X)^G=\varnothing\)。否则，令 \(c\) 为除去对子 \(\{\varnothing,X\}\) 后，互补对子的 \(G\)-轨道数；则
  \[
  |R_2(X)^G|=2^c.
  \tag{6}
  \]

最后一个公式是因为在每个互补对子中必须选一边，且选择须沿 \(G\)-轨道传递。条件 (5) 恰是传递过程中可能出现的矛盾；没有矛盾时，每个非平凡轨道有两个独立选择，而 \(\{\varnothing,X\}\) 的选择已被迫为 \(X\)。

不动集合之间的限制映射由上面的公式完全给出：\(m,k\ge3\) 时是 \(X^G\) 上的恒等映射；向第一层的映射是到单点的唯一映射；从 \(m\ge3\) 到第二层时，像恰为
\[
\{\mathcal C_{\delta_x}:x\in X^G\},
\]
且每个像点的纤维为单点。

因此，有限层不动记录延拓为完整不动记录的准确范围是：第一层的唯一记录当且仅当 \(X^G\ne\varnothing\) 时可延拓；第二层记录当且仅当它是某个 \(x\in X^G\) 的主超滤子时可延拓；第三层及以上的每个不动记录均唯一延拓。

## 2. 完整不动记录的空间

### 内在分类与非空条件

定义
\[
\mathfrak F_G(X)
=\{\operatorname{Fix}_X(F):F\subseteq G\text{ 有限}\}.
\]
在超滤子识别下，
\[
\boxed{\quad
R_\infty(X)^G
=
\{U\in\operatorname{Ult}(X):
\operatorname{Fix}_X(F)\in U\text{ 对每个有限 }F\subseteq G\}.
\quad}
\tag{7}
\]

要证明这一点，只需证明对单个 \(g\)，\(g\)-不变的超滤子恰是包含 \(\operatorname{Fix}_X(g)\) 的超滤子。

若 \(U\) 包含 \(\operatorname{Fix}_X(g)\)，则任意 \(A\) 与 \(gA\) 在该集合上的交相同，故 \(A\in U\) 当且仅当 \(gA\in U\)。

反过来，把 \(X\setminus\operatorname{Fix}_X(g)\) 按循环群 \(\langle g\rangle\) 的轨道分解。每条非平凡有限循环可用至多三种颜色作相邻异色染色，每条无限轨道也可如此染色。借助选择公理合并这些染色，得到三个集合 \(C_1,C_2,C_3\)，覆盖非不动点，且
\[
C_j\cap gC_j=\varnothing.
\]
如果 \(g\)-不变超滤子含有非不动点集合，它必含某个 \(C_j\)，也必含 \(gC_j\)，与两者不交矛盾。因此它包含 \(\operatorname{Fix}_X(g)\)。对有限多个 \(g\) 取交便得到 (7)。

于是，由超滤子扩张定理，
\[
\boxed{\quad
R_\infty(X)^G\ne\varnothing
\ \Longleftrightarrow\
\operatorname{Fix}_X(F)\ne\varnothing
\text{ 对每个有限 }F\subseteq G.
\quad}
\tag{8}
\]
这里这些集合具有有限交性质，因为
\(\operatorname{Fix}_X(F_1)\cap\operatorname{Fix}_X(F_2)
=\operatorname{Fix}_X(F_1\cup F_2)\)。
该判准也覆盖 \(X=\varnothing\)，因为可取 \(F=\varnothing\)。

拓扑上，对 \(A\subseteq X\) 令
\[
\widehat A=\{U\in\operatorname{Ult}(X):A\in U\}.
\]
这些集合构成 Stone 拓扑的开闭基。示性函数观察给出每个 \(\widehat A\)，而任意有限测试的观察纤维也等于某个 \(\widehat A\)。因此这一拓扑恰是题设拓扑。(7) 进而给出所求的内在拓扑分类：
\[
R_\infty(X)^G
=\bigcap_{\substack{F\subseteq G\\F\text{ 有限}}}
\widehat{\operatorname{Fix}_X(F)}
\subseteq\operatorname{Ult}(X).
\tag{9}
\]

### 真正不动点的闭包

对任意 \(S\subseteq X\)，主超滤子 \(\{\delta_x:x\in S\}\) 的闭包为
\[
\{U\in\operatorname{Ult}(X):S\in U\}=\widehat S.
\tag{10}
\]
确实，若 \(S\notin U\)，则开邻域 \(\widehat{X\setminus S}\) 不含这些主超滤子；若 \(S\in U\)，任何基本邻域 \(\widehat A\ni U\) 都满足 \(A\cap S\ne\varnothing\)，故包含某个 \(\delta_x\)，其中 \(x\in S\)。

取 \(S=X^G\)，得到
\[
\boxed{\quad
\overline{\eta_{\infty,X}(X^G)}
=\{U\in\operatorname{Ult}(X):X^G\in U\}.
\quad}
\tag{11}
\]
它总包含于 \(R_\infty(X)^G\)。由 (7) 和超滤子扩张定理，两者相等当且仅当
\[
\boxed{\quad
\text{存在有限 }F\subseteq G\text{ 使 }
\operatorname{Fix}_X(F)=X^G.
\quad}
\tag{12}
\]
若不存在这样的 \(F\)，则所有 \(\operatorname{Fix}_X(F)\) 与 \(X\setminus X^G\) 共同具有有限交性质；扩张成的超滤子是不动记录，却不属于 (11)。

对**每个** \(G\) 集合都满足该闭包等式的群，恰为**有限生成群**。有限生成时，在 (12) 中取有限生成集即可。反过来，若 \(G\) 非有限生成，令 \(H\) 遍历其有限生成子群，并取
\[
X=\coprod_H G/H
\]
及其左平移作用。每个 \(H\) 都是 \(G\) 的真子群，所以 \(X^G=\varnothing\)；但任意有限 \(F\subseteq G\) 固定分量 \(G/\langle F\rangle\) 中的陪集 \(\langle F\rangle\)。由 (8)，\(R_\infty(X)^G\ne\varnothing\)，故闭包等式不成立。

### 可数例子

取 \(X=\mathbb N\)，\(G\) 为 \(\mathbb N\) 的有限支撑置换群，以通常方式作用。\(G\) 和 \(X\) 都可数，而且 \(X^G=\varnothing\)。

每个 \(g\in G\) 的不动点集合余有限，因此每个非主超滤子都包含它，从而是不动记录。反过来，若不动超滤子包含单点 \(\{n\}\)，它就是 \(\delta_n\)，但交换 \(n\) 与另一点的置换不会固定它。因此全部不动记录恰为
\[
\boxed{\quad R_\infty(\mathbb N)^G
=\{\text{\(\mathbb N\) 上的非主超滤子}\}. \quad}
\]
ZFC 中由超滤子扩张定理，余有限滤子可扩张为这样的超滤子，故此集合非空。

## 3. 乘积比较

### 良定义、连续性与满射

投影 \(p_i:\prod_iX_i\to X_i\) 是等变映射，所以超滤子的推送把不动记录送到不动记录。目标的每个观察复合 \(\Pi_{(X_i)}\) 后，都是源上的观察
\[
r\longmapsto r_n(f\circ p_i),
\]
因此 \(\Pi_{(X_i)}\) 良定义且连续。

它对任意 \(G\) 和任意集合指标族都是**满射**。证明如下。给定各坐标的不动超滤子 \(U_i\)，在
\(P=\prod_iX_i\) 上考虑以下集合族：
\[
p_i^{-1}(A)\quad(A\in U_i),\qquad
\operatorname{Fix}_P(F)
=\prod_i\operatorname{Fix}_{X_i}(F)
\quad(F\subseteq G\text{ 有限}).
\tag{13}
\]
它具有有限交性质。确实，合并有限多个 \(F\) 后，每个被有限多个柱集约束的坐标都有一个属于 \(U_i\) 的交集；它还与 \(\operatorname{Fix}_{X_i}(F)\) 的交属于 \(U_i\)，故非空。其余坐标的 \(\operatorname{Fix}_{X_i}(F)\) 也非空。选择公理给出乘积中的点。

把 (13) 扩张为 \(P\) 上的超滤子 \(U\)。由 (7)，\(U\) 不动；并且其第 \(i\) 个边缘包含 \(U_i\)，因此恰等于 \(U_i\)。若目标为空，满射性自动成立。若指标族为空，源和目标都是单点集，比较映射也是满射。

### 平凡群的两因子单射判准

对平凡群，
\[
\boxed{\quad
\Pi_{X,Y}\text{ 为单射}
\ \Longleftrightarrow\
X\text{ 或 }Y\text{ 有限}.
\quad}
\tag{14}
\]
这里“有限”包括空集。

若 \(Y\) 有限，\(X\times Y\) 上的任意超滤子都集中于唯一一个切片 \(X\times\{y\}\)，且由它在 \(X\) 上的边缘唯一确定；\(Y=\varnothing\) 时源为空。因此比较映射单射，交换因子同理。

若 \(X,Y\) 都无限，选取互异点列 \((x_n)\)、\((y_n)\)，并取 \(\mathbb N\) 上的非主超滤子 \(U,V\)。在 \(\mathbb N^2\) 上定义
\[
\begin{aligned}
A\in W
&\Longleftrightarrow
\{n:\{m:(n,m)\in A\}\in V\}\in U,\\
A\in W'
&\Longleftrightarrow
\{m:\{n:(n,m)\in A\}\in U\}\in V.
\end{aligned}
\]
它们都是超滤子，两个边缘分别都是 \(U,V\)。但集合
\(\{(n,m):n<m\}\) 属于 \(W\) 而不属于 \(W'\)：其每一行余有限，每一列有限。将两者沿 \((n,m)\mapsto(x_n,y_m)\) 推送，便得到 \(X\times Y\) 上两个不同、边缘相同的超滤子，故比较映射不单射。

### 两个全称命题

**命题一为真：若 \(X,Y\) 至少一个有限，两因子的比较映射为双射。** 满射已证明。若例如 \(Y\) 有限，上述切片论证给出全部超滤子层面的单射，限制到不动记录后仍单射。

**命题二为假：\(X^G=Y^G=\varnothing\) 并不保证比较映射单射。** 取上面的有限支撑置换群 \(G\)，令 \(X=Y=\mathbb N\)。两者都没有不动点。取上面构造的 \(W,W'\)，其边缘 \(U,V\) 都是非主超滤子，所以是 \(G\)-不动的。实际上 \(W,W'\) 本身也不动：对每个 \(g\)，\(\operatorname{Fix}_{\mathbb N}(g)\) 余有限，故
\[
\operatorname{Fix}_{\mathbb N^2}(g)
=\operatorname{Fix}_{\mathbb N}(g)^2
\]
属于这两个超滤子。它们不同却具有相同边缘，因此该比较映射不是单射。