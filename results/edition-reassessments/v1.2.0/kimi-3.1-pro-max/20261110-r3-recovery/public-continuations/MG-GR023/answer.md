# 最终稿

记集合 \(X\) 上的超滤子全体为 \(\beta X\)，主超滤子为
\[
\delta_x=\{A\subseteq X:x\in A\},
\]
并对 \(A\subseteq X\) 记
\[
C_A=\{U\in\beta X:A\in U\}.
\]
下面反复使用 ZFC 中的超滤子引理：任何具有限交性质的集族都能延拓为超滤子。

## 1. 截断、相容性与有限底集上的不动记录

### 1.1 \(R_m(X)\) 的完全分类

若 \(X=\varnothing\)，则 \(\operatorname{Map}(\varnothing,[0])\) 是单点集，而不存在从单点集到 \(\varnothing\) 的函数 \(r_0\)。因此
\[
\boxed{R_m(\varnothing)=\varnothing\qquad(m\geq1).}
\]

以下设 \(X\neq\varnothing\)。此时 \(r_0\) 和 \(r_1\) 均被唯一确定，故
\[
R_1(X)\cong 1.
\]

当 \(m\geq2\)（包括 \(m=\infty\)）时，有自然双射
\[
\boxed{R_m(X)\cong\beta X.}
\]

给定 \(U\in\beta X\)，定义 \(r^U\) 为
\[
r_n^U(f)=\text{唯一满足 }f^{-1}(i)\in U\text{ 的 }i\in[n].
\]
因为 \(f^{-1}(0),\ldots,f^{-1}(n-1)\) 是 \(X\) 的有限划分，这样的 \(i\) 恰好存在一个。若 \(a:[n]\to[k]\) 且 \(f^{-1}(i)\in U\)，则
\[
(a\circ f)^{-1}(a(i))\supseteq f^{-1}(i),
\]
故左边也属于 \(U\)，从而
\[
a(r_n^U(f))=r_k^U(a\circ f).
\]
所以 \(r^U\in R_m(X)\)。

反过来，给定 \(r\in R_m(X)\)，令
\[
U_r=\{A\subseteq X:r_2(\chi_A)=1\},
\]
其中 \(\chi_A\) 在 \(A\) 上取值 \(1\)，在余集上取值 \(0\)。由 \(n=1,2\) 的常量测试和交换 \(0,1\) 的测试可得
\[
X\in U_r,\qquad \varnothing\notin U_r,\qquad
A\in U_r\iff X\setminus A\notin U_r.
\]
对任意 \(f:X\to[n]\)，若 \(i=r_n(f)\)，取 \(a=\chi_{\{i\}}:[n]\to[2]\)，则
\[
r_2(\chi_{f^{-1}(i)})=a(r_n(f))=1,
\]
所以
\[
f^{-1}(i)\in U_r. \tag{1}
\]
利用对 \((\chi_A,\chi_B):X\to[4]\) 及其两个投影的相容性，可得 \(U_r\) 对有限交封闭；再结合余集性质可得对超集封闭。因此 \(U_r\) 是超滤子。

式 (1) 表明 \(r=r^{U_r}\)；另一方面直接有 \(U_{r^U}=U\)。故两个构造互逆。

### 1.2 截断映射的像与纤维

设 \(X\neq\varnothing\)，\(m\geq k\geq1\)。

- 若 \(k=1\)，目标是单点集，\(q_{m,1}\) 的像为该单点集，唯一纤维是整个 \(R_m(X)\)。
- 若 \(k\geq2\)，在上述与 \(\beta X\) 的认同下，
  \[
  \boxed{q_{m,k}=\operatorname{id}_{\beta X}.}
  \]
  因而它是双射，每个纤维都是单点集。

若 \(X=\varnothing\)，相关集合均为空，截断映射为空映射。

### 1.3 与集合映射的相容性

由定义直接得到
\[
R_m(\operatorname{id}_X)=\operatorname{id},\qquad
R_m(h'\circ h)=R_m(h')\circ R_m(h),
\]
以及自然性
\[
q_{m,k}\circ R_m(h)=R_k(h)\circ q_{m,k}.
\]
在 \(m\geq2\) 时，\(R_m(h)\) 对应于超滤子的推出：
\[
\boxed{
R_m(h)(U)=h_*U
:=\{B\subseteq Y:h^{-1}(B)\in U\}.}
\]
点值记录满足
\[
\eta_{m,X}(x)=
\begin{cases}
\delta_x,&m\geq2,\\
R_1(X)\text{ 的唯一元素},&m=1,
\end{cases}
\]
并且
\[
R_m(h)\circ\eta_{m,X}=\eta_{m,Y}\circ h,\qquad
q_{m,k}\circ\eta_{m,X}=\eta_{k,X}.
\]
这些自然性也说明 \(q_{m,k}\) 将 \(G\)-不动记录送到 \(G\)-不动记录。

### 1.4 有限 \(G\)-集合

设 \(X\) 有限。此时所有超滤子均为主超滤子，并且
\[
g_*\delta_x=\delta_{gx}.
\]
因此：

- 若 \(X=\varnothing\)，则 \(R_m(X)^G=\varnothing\)。
- 若 \(X\neq\varnothing\) 且 \(m=1\)，则 \(R_1(X)^G\) 始终为单点集，即使 \(X^G=\varnothing\)。
- 若 \(m\geq2\)，则
  \[
  \boxed{
  R_m(X)^G=\{\delta_x:x\in X^G\}\cong X^G,\qquad
  |R_m(X)^G|=|X^G|.}
  \]
  它非空当且仅当 \(X^G\neq\varnothing\)。

限制映射为：

- \(m\geq k\geq2\) 时，在不动记录上是
  \[
  X^G\longrightarrow X^G,\qquad x\longmapsto x,
  \]
  因而是双射。
- \(k=1\) 且 \(X\neq\varnothing\) 时，目标是单点集；若源非空，则所有元素均送到该唯一点，若源为空则为空映射。

完整不动延拓的准确范围为：

1. **\(m\geq2\)**：每个有限层不动记录都有唯一完整不动延拓，即同一个 \(\delta_x\)，其中 \(x\in X^G\)。
2. **\(m=1\)，\(X\neq\varnothing\)**：唯一有限层不动记录存在完整不动延拓，当且仅当 \(X^G\neq\varnothing\)。此时全部延拓恰为
   \[
   \{\delta_x:x\in X^G\}.
   \]
3. **\(X=\varnothing\)**：各层均没有不动记录。

事实上，由第 1.2 节可知，\(m\geq2\) 时的唯一延拓结论对任意集合 \(X\) 也成立。

---

## 2. 完整不动记录的空间

### 2.1 单个双射的不动超滤子

**引理.** 若 \(s:X\to X\) 是双射，则
\[
\boxed{s_*U=U\iff X^s\in U,}
\]
其中 \(X^s=\{x:sx=x\}\)。

**证明.** 若 \(X^s\in U\)，则对任意 \(A\subseteq X\)，
\[
A\cap X^s=s^{-1}(A)\cap X^s,
\]
故 \(A\in U\iff s^{-1}(A)\in U\)，即 \(s_*U=U\)。

反之，设 \(s_*U=U\)，但 \(B=X\setminus X^s\in U\)。在 \(B\) 的每条 \(s\)-轨道上选取起点，并沿轨道周期性地用颜色 \(0,1,2\) 染色；无限轨道按 \(\mathbb Z\) 编号。这样不会有一条轨道上的三个相继点 \(x,sx,s^2x\) 同色：有限轨道回绕处至多出现两个相继同色点。

三个颜色类划分 \(B\)，恰有一个颜色类 \(A\) 属于 \(U\)。由 \(s_*U=U\)，
\[
A,\quad s^{-1}A,\quad s^{-2}A
\]
都属于 \(U\)。但
\[
A\cap s^{-1}A\cap s^{-2}A
=\{x:x,sx,s^2x\text{ 同色}\}=\varnothing,
\]
矛盾。故 \(X^s\in U\)。∎

### 2.2 内在分类、拓扑与非空判准

令 \(\mathcal F_G(X)\) 为由
\[
\{X^g:g\in G\}
\]
生成的滤子。其有限交形如
\[
X^{g_1}\cap\cdots\cap X^{g_k}
=X^{\langle g_1,\ldots,g_k\rangle}.
\]
由上述引理，
\[
\boxed{
R_\infty(X)^G
\cong\{U\in\beta X:\mathcal F_G(X)\subseteq U\}.}
\]
等价地，\(U\) 必须包含所有 \(X^H\)，其中 \(H\leq G\) 遍历有限生成子群。

因此
\[
\boxed{
R_\infty(X)^G\neq\varnothing
\iff
\text{对每个有限集 }F\subseteq G,\ X^F\neq\varnothing.}
\]
也就是说，每个有限生成子群都在 \(X\) 中有不动点。特别地，若 \(G\) 本身有限生成，这等价于 \(X^G\neq\varnothing\)。

在 \(R_\infty(X)\cong\beta X\) 下，
\[
\{r:r_n(f)=i\}=C_{f^{-1}(i)}.
\]
反之，每个 \(C_A\) 都是观察 \(r_2(\chi_A)\) 给出的开条件。因此题给拓扑恰为 \(\beta X\) 的 Stone 拓扑，以
\[
C_A\qquad(A\subseteq X)
\]
为既开又闭的基本集，并且
\[
C_A\cap C_B=C_{A\cap B},\qquad
\beta X\setminus C_A=C_{X\setminus A}.
\]
所以 \(R_\infty(X)\) 是紧 Hausdorff 空间，而
\[
\boxed{R_\infty(X)^G=\bigcap_{g\in G}C_{X^g}}
\]
是其闭子空间。

等价地，若令
\[
\mathcal I_G=
\{A\subseteq X:\text{存在有限生成 }H\leq G
\text{ 使 }A\cap X^H=\varnothing\},
\]
则 \(\mathcal I_G\) 是布尔理想，不动记录空间就是 \(\mathcal P(X)/\mathcal I_G\) 的 Stone 空间。

### 2.3 点值记录的闭包与等式判准

有标准闭包公式
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}
=C_{X^G}
=\{U\in\beta X:X^G\in U\}.}
\]
事实上，若 \(X^G\in U\)，则任意 \(B\in U\) 都与 \(X^G\) 相交，所以基本邻域 \(C_B\) 内含某个 \(\delta_x\)，\(x\in X^G\)。若 \(X^G\notin U\)，则 \(C_{X\setminus X^G}\) 是 \(U\) 的邻域且不含这些点值记录。\(X^G=\varnothing\) 时两边均为空。

因为 \(X^G\subseteq X^F\)，总有
\[
C_{X^G}\subseteq R_\infty(X)^G.
\]
两者相等的充要条件是
\[
\boxed{
\text{存在有限集 }F\subseteq G
\text{ 使得 }X^F=X^G.} \tag{2}
\]

若这样的 \(F\) 存在，则 \(X^G=X^F\in\mathcal F_G(X)\)，故每个不动超滤子都包含 \(X^G\)。反之，若不存在这样的 \(F\)，则对每个有限 \(F\subseteq G\)，
\[
X^F\cap(X\setminus X^G)\neq\varnothing.
\]
因此
\[
\mathcal F_G(X)\cup\{X\setminus X^G\}
\]
具有限交性质，可延拓为超滤子 \(U\)。这个 \(U\) 是 \(G\)-不动的，但 \(X^G\notin U\)，故不属于点值记录集的闭包。

### 2.4 对所有 \(G\)-集合均满足等式的群

\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\text{ 对所有 }G\text{-集合 }X\text{ 成立}
\iff G\text{ 有限生成}.}
\]

若 \(G\) 由有限集 \(F\) 生成，则 \(X^F=X^G\) 对所有 \(X\) 成立，充分性由式 (2) 得到。

若 \(G\) 非有限生成，令 \(\mathcal H\) 为其全部有限生成子群，取
\[
X=\bigsqcup_{H\in\mathcal H}G/H,
\]
各分量按左平移作用。对任意有限 \(F\subseteq G\)，令 \(H=\langle F\rangle\)，则分量 \(G/H\) 中的陪集 \(H\) 被 \(F\) 固定，所以 \(X^F\neq\varnothing\)，从而 \(R_\infty(X)^G\neq\varnothing\)。

另一方面，若陪集 \(aH\) 被整个 \(G\) 固定，则
\[
G\subseteq aHa^{-1}.
\]
右边是有限生成群，这将迫使 \(G\) 有限生成，矛盾。因此 \(X^G=\varnothing\)。于是点值记录闭包为空，而不动记录空间非空。

### 2.5 群和底集均可数的具体例子

取 Prüfer \(2\)-群
\[
G=C_{2^\infty}
=\{z\in\mathbb C^\times:z^{2^n}=1\text{ 对某个 }n\},
\]
并令 \(G_n\) 为其唯一的阶 \(2^n\) 子群。于是
\[
G_0<G_1<G_2<\cdots,\qquad G=\bigcup_nG_n.
\]
取
\[
X_n=G/G_n,\qquad X=\bigsqcup_{n\geq0}X_n,
\]
并令 \(G\) 在各分量上左平移。\(G\) 和 \(X\) 均可数。

\(X_n\) 中每个点的稳定子都是 \(G_n\)。任何有限 \(F\subseteq G\) 都生成某个 \(G_N\)，并且
\[
X^F=T_N:=\bigsqcup_{n\geq N}X_n.
\]
特别地 \(X^G=\varnothing\)，而所有 \(T_N\) 非空，所以
\[
X^G=\varnothing,\qquad R_\infty(X)^G\neq\varnothing.
\]

全部不动记录恰为
\[
\boxed{
R_\infty(X)^G
\cong\{U\in\beta X:T_N\in U\text{ 对所有 }N\}.}
\]
对应记录仍由
\[
r_k^U(f)=\text{唯一使 }f^{-1}(i)\in U\text{ 的 }i
\]
给出。这里没有额外条件：尾滤子 \(\{T_N\}\) 具有限交性质，任何延拓它的超滤子都是不动的；反之，不动性迫使所有 \(T_N\) 属于 \(U\)。特别地，这种 \(U\) 的任何成员都不可能只包含在有限多个初始分量 \(X_0,\ldots,X_{N-1}\) 的并中。

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
右边是源空间的基本连续观察，因此每个坐标映射连续，从而 \(\Pi_{(X_i)}\) 对积拓扑连续。

### 3.2 对任意群和任意指标族均为满射

\[
\boxed{\Pi_{(X_i)}\text{ 对所有 }G\text{ 和所有集合指标族都是满射。}}
\]

先处理退化情形：

- 若 \(I=\varnothing\)，则 \(P=1\)，源与空积目标均为单点集，映射为双射。
- 若某个 \(X_i=\varnothing\)，则 \(P=\varnothing\)，源为空；目标也因该空因子而为空，故映射为满射。

现设所有因子非空。给定各坐标的不动超滤子 \(U_i\)，考虑：

1. 所有柱集 \(p_i^{-1}(A_i)\)，其中 \(A_i\in U_i\)；
2. 所有 \(P^H=\prod_iX_i^H\)，其中 \(H\leq G\) 有限生成。

证明该族具有限交性质。有限多个柱集的交可写为
\[
C=\{x\in P:x_i\in A_i\ (i\in F)\},
\]
其中 \(F\subseteq I\) 有限，\(A_i\in U_i\)。有限多个 \(P^{H_j}\) 的交仍是 \(P^H\)，其中 \(H=\langle H_j:j\rangle\) 有限生成。

因为 \(U_i\) 不动，\(X_i^H\in U_i\)。因此：

- 对 \(i\in F\)，\(A_i\cap X_i^H\in U_i\)，故非空；
- 对其余 \(i\)，\(X_i^H\) 非空。

用选择公理选取相应坐标，即得 \(C\cap P^H\neq\varnothing\)。

将该族延拓为 \(P\) 上的超滤子 \(U\)。包含所有 \(P^H\) 表明 \(U\) 是 \(G\)-不动的；包含所有柱集表明
\[
(p_i)_*U\supseteq U_i.
\]
两边都是超滤子，故 \((p_i)_*U=U_i\)。满射性得证。

### 3.3 任意群的两因子纤维公式

下面给出一个对任意群都成立的精确描述，后文直接使用。

对 \(U\in R_\infty(X)^G\)、\(V\in R_\infty(Y)^G\)，有
\[
\boxed{
\Pi_{X,Y}^{-1}(U,V)
=
\{W\in\beta(X\times Y):
A\times B\in W\ \forall A\in U,\ B\in V\}.} \tag{3}
\]
并且该纤维非空、为 \(\beta(X\times Y)\) 的闭子空间。

**证明.** 若 \(W\) 的两个边缘为 \(U,V\)，则它包含所有柱集，从而包含所有矩形 \(A\times B\)。反之，若 \(W\) 包含所有这些矩形，取 \(B=Y\) 和 \(A=X\) 分别可知两个边缘包含 \(U,V\)；边缘与 \(U,V\) 都是超滤子，故必相等。

此外，对每个有限生成 \(H\leq G\)，有 \(X^H\in U\)、\(Y^H\in V\)，所以
\[
(X\times Y)^H=X^H\times Y^H\in W.
\]
故式 (3) 中每个 \(W\) 自动是 \(G\)-不动的。

所有 \(A\times B\) 具有限交性质，因为 \(A,B\) 非空且
\[
(A_1\times B_1)\cap(A_2\times B_2)
=(A_1\cap A_2)\times(B_1\cap B_2).
\]
故纤维非空。它是闭集，因为
\[
\Pi_{X,Y}^{-1}(U,V)
=\bigcap_{A\in U,\ B\in V}C_{A\times B}.
\]
∎

还有两条有用的纤维判据：

- **主边缘情形。** 若 \(U=\delta_x\)，则纤维只有一个元素 \(W\)，由
  \[
  S\in W\iff \{y\in Y:(x,y)\in S\}\in V
  \]
  给出。因为任何以 \(\delta_x\) 为边缘的 \(W\) 都集中于切片 \(\{x\}\times Y\)，之后便由 \(V\) 唯一确定。\(V\) 为主超滤子时同理。
- **可数支撑的非主边缘情形。** 若 \(U,V\) 均非主，且分别含有可数无限集 \(A\in U\)、\(B\in V\)，则纤维至少有两个元素。定义两个迭代超滤子
  \[
  S\in U\ltimes V
  \iff\{x:S_x\in V\}\in U,
  \]
  \[
  S\in V\rtimes U
  \iff\{y:S^y\in U\}\in V.
  \]
  两者都属于式 (3) 的纤维。取双射 \(A\cong\mathbb N\)、\(B\cong\mathbb N\)，令
  \[
  S=\{(a,b)\in A\times B:a<b\}.
  \]
  每个 \(a\)-切片在 \(B\) 中余有限，故属于 \(V\)，从而 \(S\in U\ltimes V\)；每个 \(b\)-切片在 \(A\) 中有限，故不属于 \(U\)，从而 \(S\notin V\rtimes U\)。所以两者不同。

### 3.4 平凡群的两因子单射判准

对平凡群，
\[
\boxed{
\Pi_{X,Y}\text{ 单射}
\iff X,Y\text{ 中至少一个有限}.}
\]
结合一般满射性，这也是它为双射的充要条件。

若 \(X\) 或 \(Y\) 有限，则该因子的任何边缘都是主超滤子，由第 3.3 节的主边缘判据，每个纤维至多一个元素，故单射。

若 \(X,Y\) 均无限，分别取可数无限子集 \(X_0,Y_0\)，并在 \(X_0,Y_0\) 上选取非主超滤子 \(U,V\)，例如延拓其余有限滤子。把它们推到 \(X,Y\) 后仍为非主超滤子，且分别含有可数成员 \(X_0,Y_0\)。由第 3.3 节，纤维 \(\Pi_{X,Y}^{-1}(U,V)\) 至少有两个元素，故不单射。

### 3.5 至少一个因子有限时，对任意作用均为双射

\[
\boxed{
\text{若 }X,Y\text{ 至少一个有限，则 }
R_\infty(X\times Y)^G\to
R_\infty(X)^G\times R_\infty(Y)^G
\text{ 为双射}.}
\]

满射性已由第 3.2 节给出。若 \(X\) 有限，则任何 \(W\) 在 \(X\) 上的边缘均为某个主超滤子 \(\delta_x\)，由第 3.3 节，\(W\) 由两个边缘唯一确定。\(Y\) 有限时对称处理；空底集情形两边均为空。

### 3.6 “均无不动点则单射”不成立

\[
\boxed{
X^G=Y^G=\varnothing
\text{ 并不能推出两因子比较映射单射}.}
\]

使用第 2.5 节的可数例子，并取 \(Y=X\)。任取不动超滤子 \(U\)。由于 \(X^G=\varnothing\)，\(U\) 必为非主超滤子；否则 \(U=\delta_x\) 的 \(G\)-不动性会给出 \(x\in X^G\)。又因为 \(X\) 可数，\(X\) 本身就是 \(U\) 的可数无限成员。

由第 3.3 节的可数支撑判据，纤维
\[
\Pi_{X,X}^{-1}(U,U)
\]
至少含两个不同的不动超滤子。它们在比较映射下有相同像 \((U,U)\)，故比较映射不单射。

---

## 4. 进一步结果：任意指标族的单射性完整分类

本节超出原题要求，给出乘积比较在任意集合指标族上的完整边界，并推广到所有有限生成群。

### 4.1 平凡群、任意指标族

**定理.** 设 \(G\) 为平凡群，\((X_i)_{i\in I}\) 为任意集合族。

1. 若某个 \(X_i=\varnothing\)，则比较映射是空集之间的双射。
2. 若所有 \(X_i\) 非空，令
   \[
   J=\{i\in I:|X_i|>1\}.
   \]
   则下列等价：
   \[
   \Pi_{(X_i)}\text{ 单射}
   \iff \Pi_{(X_i)}\text{ 双射}
   \iff
   \begin{cases}
   J\text{ 有限},\\
   \text{且至多有一个 }X_i\text{ 无限}.
   \end{cases}
   \]
   在这些条件下，它实际上是拓扑同胚。

**证明.** 一般满射性已经证明，所以单射与双射等价。

先证充分性。单点因子可以删去：其坐标在乘积中和边缘中都没有额外信息。因此可设 \(I=J\) 为有限集。若所有因子有限，则 \(P\) 有限，\(\beta P=P\)，超滤子由唯一的乘积点决定，故单射。若恰有一个无限因子，其余因子有限，则反复使用“一个因子有限时两因子比较映射单射”即可。

再证必要性。分两种情况。

**情况一：\(J\) 无限。** 对每个 \(i\in J\)，选取两个不同点 \(0_i,1_i\in X_i\)。令
\[
A_i=p_i^{-1}(\{0_i\}),
\]
并令 \(\mathcal F\) 为由所有 \(A_i\) 生成的滤子。考虑
\[
E=\left\{x\in P:
\{i\in J:x_i=1_i\}\text{ 无限}\right\}.
\]
任意有限个 \(A_i\) 只限制有限多个坐标，因此既能在其余无限多个指标上取 \(1_i\)，也能处处取 \(0_i\)。故
\[
\mathcal F\cup\{E\},\qquad
\mathcal F\cup\{P\setminus E\}
\]
分别具有限交性质。将它们分别延拓为超滤子 \(U,V\)。二者不同，但每个坐标边缘都包含 \(\{0_i\}\)，因而都是同一个 \(\delta_{0_i}\)。故比较映射不单射。

**情况二：\(J\) 有限但至少有两个无限因子。** 取其中两个因子 \(X_a,X_b\)，在 \(X_a\times X_b\) 上使用第 3.4 节的两个不同超滤子；把其余坐标固定为任意选定点，并将这两个超滤子沿所得嵌入推到整个 \(P\)。它们仍不同，所有坐标边缘分别相同，故比较映射不单射。

最后，源空间是紧 Hausdorff 空间，目标是 Hausdorff 空间；连续双射从紧空间到 Hausdorff 空间必为同胚。∎

### 4.2 所有有限生成群的任意族分类

若 \(G\) 有限生成，则 \(X^G\in\mathcal F_G(X)\)，所以
\[
R_\infty(X)^G=C_{X^G}.
\]
对任意 \(A\subseteq X\)，限制映射
\[
C_A\longrightarrow\beta A,\qquad
U\longmapsto\{B\subseteq A:B\in U\}
\]
是规范同胚；其逆将 \(V\in\beta A\) 送到由 \(V\) 在 \(X\) 上生成的超滤子。

因此，对任意 \(G\)-集合族 \((X_i)\)，令 \(A_i=X_i^G\)，有交换于规范同胚之下的识别
\[
R_\infty\!\left(\prod_iX_i\right)^G
\cong\beta\!\left(\prod_iA_i\right),\qquad
\prod_iR_\infty(X_i)^G\cong\prod_i\beta A_i.
\]
在此识别下，原比较映射正是平凡群族 \((A_i)\) 的乘积比较映射。

于是由第 4.1 节立即得到：

\[
\boxed{
\text{对任意有限生成群 }G\text{ 和任意 }G\text{-集合族，}
\Pi_{(X_i)}\text{ 的单射/双射性完全由不动点集 }X_i^G
\text{ 按第 4.1 节的同一判准决定。}}
\]

明确地说：

- 若某个 \(X_i^G=\varnothing\)，源和目标均为空，映射为双射。
- 否则，它是单射（等价地，双射、同胚）当且仅当
  \[
  \{i:|X_i^G|>1\}
  \]
  有限，且至多有一个 \(X_i^G\) 无限。

特别地，对有限生成群的两个因子，若两个不动点集均非空，则比较映射为双射当且仅当
\[
X^G,Y^G\text{ 中至少一个有限}.
\]
若其中一个不动点集为空，则相应不动记录空间为空，比较映射是空集之间的双射。

---

## 保留、新增与未完成部分

- **保留并核验：** 超滤子分类、全部截断与有限层延拓结论；不动记录的滤子/Stone 空间分类、闭包公式及有限生成群判准；Prüfer 群反例；任意乘积的满射性；原题三个乘积命题的判定及证明。
- **新增或强化：** 给出了任意群两因子比较映射的精确纤维公式 (3)，以及主边缘和可数支撑非主边缘的纤维判据；进一步完整分类了平凡群任意指标族的单射/双射情形，并通过不动点集约化推广到所有有限生成群和任意指标族，同时说明了同胚结论。
- **仍未完成：** 没有给出任意非有限生成群、任意指标族比较映射单射性的统一判准；本轮新增的一般分类覆盖平凡群的所有族以及有限生成群的所有族，任意群则有两因子纤维公式和相应反例。
- **自评：** 原题三项均有完整证明，覆盖空底集与空指标族，基线可自评为 **B2**。新增部分形成独立闭合的任意族分类和一般两因子纤维结构，保守自评研究增量为 **R2**；不将尚未解决的非有限生成群一般单射分类声称为已完成。