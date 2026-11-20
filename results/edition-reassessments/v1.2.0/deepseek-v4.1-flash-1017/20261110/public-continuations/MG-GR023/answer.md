# 有限测试记录与群作用

以下证明均在 ZFC 中。空函数视为合法函数。对集合 \(X\)，记 \(\beta X\) 为 \(X\) 上全体真超滤子的集合，并约定
\[
\beta\varnothing=\varnothing.
\]
对 \(x\in X\)，记主超滤子
\[
p_x=\{A\subseteq X:x\in A\}.
\]
对 \(A\subseteq X\)，记
\[
A^+=\{\mathcal U\in\beta X:A\in\mathcal U\}.
\]

若 \(m\ge2\)，定义
\[
\chi_A:X\longrightarrow[2],\qquad
\chi_A(x)=
\begin{cases}
0,&x\in A,\\
1,&x\notin A,
\end{cases}
\]
以及
\[
\mu_r(A):=1-r_2(\chi_A)\in\{0,1\}. \tag{0.1}
\]
于是 \(\mu_r(A)=1\) 表示记录 \(r\) 为函数 \(\chi_A\) 选择的零纤维包含 \(A\)。

## 1. 截断记录

### 1.1 \(R_m(X)\) 的完整分类

首先，对所有 \(m\)，包括 \(m=\infty\)，
\[
R_m(\varnothing)=\varnothing. \tag{1.1}
\]
事实上，\(r_0\) 必须是从单点集 \(\operatorname{Map}(\varnothing,[0])\) 到空集 \([0]\) 的函数，所以不存在。

以下假设 \(X\ne\varnothing\)。

#### 情形一：\(m=0,1\)

有
\[
R_0(X)=R_1(X)=\{\ast_X\}. \tag{1.2}
\]
其中 \(\ast_X\) 由唯一的空函数
\[
r_0:\operatorname{Map}(X,[0])=\varnothing\longrightarrow[0]
\]
和唯一的常值函数 \(r_1\equiv0\) 组成。因此
\[
|R_0(X)|=|R_1(X)|=1.
\]

#### 情形二：\(m=2\)

记录 \(r\) 完全由 \(\mu_r\) 决定，并且自然性条件等价于
\[
\mu_r(\varnothing)=0,\qquad
\mu_r(X)=1,\qquad
\mu_r(A^c)=1-\mu_r(A). \tag{1.3}
\]
前两个条件来自两个常值映射 \([2]\to[2]\)，第三个条件来自交换映射。

反过来，任意满足 (1.3) 的
\[
\mu:\mathcal P(X)\longrightarrow\{0,1\}
\]
唯一确定
\[
r_2(\chi_A):=\begin{cases}0,&\mu(A)=1,\\1,&\mu(A)=0.\end{cases}
\]
由于 \([2]\to[2]\) 只有四个映射，直接逐项核验即可，因此这确实给出全部记录。

每一对 \(\{A,A^c\}\) 恰有一个自由二进制选择。其中 \(\{\varnothing,X\}\) 已被 (1.3) 固定。所以若 \(|X|=N\ge1\)，则
\[
|R_2(X)|=2^{2^{N-1}-1}. \tag{1.4}
\]
若 \(|X|=\kappa\) 为无限基数，互补对共有 \(2^\kappa\) 个，因此
\[
|R_2(X)|=2^{2^\kappa}.
\]

#### 情形三：\(m\ge3\)

有自然双射
\[
R_m(X)\cong\beta X. \tag{1.5}
\]

从一个超滤子 \(\mathcal U\in\beta X\) 构造记录：
\[
r_n^{\mathcal U}(f)=j
\quad\Longleftrightarrow\quad
f^{-1}(j)\in\mathcal U. \tag{1.6}
\]
因为 \(\{f^{-1}(j):j\in[n]\}\) 是有限划分，超滤子恰好含其中一个成员，所以定义正确。若 \(a:[n]\to[k]\)，则
\[
a(r_n^{\mathcal U}(f))=j
\Longleftrightarrow
f^{-1}(a^{-1}(j))\in\mathcal U
\Longleftrightarrow
(a\circ f)^{-1}(j)\in\mathcal U,
\]
故自然性成立。

反过来，设 \(r\in R_m(X)\)，其中 \(m\ge3\)。令 \(\mu=\mu_r\)。对任意 \(h:X\to[3]\)，记 \(y=r_3(h)\)。对每个 \(S\subseteq[3]\)，取映射 \(a_S:[3]\to[2]\) 在每个 \(s\in S\) 上取值 \(0\)，并令 \(a_S(s)=1\) 当 \(s\notin S\)。自然性给出
\[
\mu(h^{-1}(S))=1
\quad\Longleftrightarrow\quad
y\in S. \tag{1.7}
\]

现在给定 \(A,B\subseteq X\)，取 \(h:X\to[3]\) 使
\[
h^{-1}(0)=A\cap B,\qquad
h^{-1}(1)=A\setminus B,\qquad
h^{-1}(2)=X\setminus A.
\]
把 (1.7) 用于 \(S=\{0\}\)、\(\{0,1\}\)、\(\{1,2\}\)，得到
\[
\mu(A\cap B)=1
\quad\Longleftrightarrow\quad
\mu(A)=\mu(B)=1.
\]
等价地，
\[
\mu(A\cap B)=\mu(A)\mu(B),\qquad
\mu(A\cup B)=\mu(A)+\mu(B)-\mu(A\cap B). \tag{1.8}
\]
结合 (1.3)，可见
\[
\mathcal U_r:=\{A\subseteq X:\mu(A)=1\} \tag{1.9}
\]
是真超滤子。

由 (1.7)，对任意 \(f:X\to[n]\) 和任意 \(j\in[n]\)，都有
\[
f^{-1}(j)\in\mathcal U_r
\quad\Longleftrightarrow\quad
r_n(f)=j.
\]
所以 \(r=r^{\mathcal U_r}\)。两个互为逆的构造给出 (1.5)。

特别地，若 \(X\) 有限非空，则所有超滤子均为主超滤子，所以
\[
R_m(X)\cong X,\qquad |R_m(X)|=|X| \qquad(m\ge3). \tag{1.10}
\]

### 1.2 遗忘映射 \(q_{m,k}\)

空集情形下，定义域、目标及纤维全部为空。以下设 \(X\ne\varnothing\)。

| 范围 | 映射 | 像 | 纤维 |
|---|---|---|---|
| \(m=1,k=1\) 或 \(m=k=2\) | \(q_{m,k}\) | 整个目标 | 每点一个原像 |
| \(m=2,k=1\) | 常值 | 唯一的 \(R_1(X)\) 元素 \(\ast_X\) | 唯一纤维是整个 \(R_2(X)\) |
| \(m\ge3,k=1\) | 常值 | \(\{\ast_X\}\) | 唯一纤维是整个 \(\beta X\) |
| \(m\ge3,k=2\) | \(\mathcal U\mapsto\mu_{\mathcal U}\) | \(\{\mu_{\mathcal U}:\mathcal U\in\beta X\}\) | 在像上每点一个原像，像外为空纤维 |
| \(m\ge k\ge3\) | \(\mathcal U\mapsto\mathcal U\) | 整个 \(\beta X\) | 每点一个原像 |

其中
\[
\mu_{\mathcal U}(A)=1
\quad\Longleftrightarrow\quad
A\in\mathcal U. \tag{1.11}
\]
映射 \(q_{m,2}\) 是单射，因为
\[
\mathcal U=\{A\subseteq X:\mu_{\mathcal U}(A)=1\}
\]
可由像恢复。

若 \(X\) 有限，则 \(m\ge3,k=2\) 的像为
\[
\{\mu_x:x\in X\},\qquad
\mu_x(A)=1\Longleftrightarrow x\in A. \tag{1.12}
\]

### 1.3 与集合映射的相容性

设 \(h:X\to Y\)、\(r\in R_m(X)\)。对 \(f:Y\to[n]\) 和 \(a:[n]\to[k]\)，
\[
a\bigl((R_m(h)r)_n(f)\bigr)
=a\bigl(r_n(f\circ h)\bigr)
=r_k(a\circ f\circ h),
\]
而右侧也是
\[
(R_m(h)r)_k(a\circ f).
\]
因此 \(R_m(h)r\in R_m(Y)\)。直接计算还给出
\[
R_m(\mathrm{id}_X)=\mathrm{id}_{R_m(X)},\qquad
R_m(k\circ h)=R_m(k)\circ R_m(h),
\]
以及
\[
q_{m,k}\circ R_m(h)=R_k(h)\circ q_{m,k}. \tag{1.13}
\]
点值记录满足
\[
R_m(h)\eta_{m,X}(x)=\eta_{m,Y}(h(x)). \tag{1.14}
\]

在超滤子模型中，\(m\ge3\) 时
\[
R_m(h)\mathcal U
=\{A\subseteq Y:h^{-1}(A)\in\mathcal U\}. \tag{1.15}
\]
这正是 \(\mathcal U\) 沿 \(h\) 的推前。

### 1.4 有限 \(G\)-集的不动记录

设 \(X\) 有限。若 \(X=\varnothing\)，则所有 \(R_m(X)^G=\varnothing\)。

以下设 \(X\ne\varnothing\)。

对 \(m=0,1\)，
\[
|R_0(X)^G|=|R_1(X)^G|=1. \tag{1.16}
\]

对 \(m=2\)，固定记录由 \(G\)-不变的函数 \(\mu\) 表示。这类函数只能在同一 \(\mathcal P(X)\)-轨道上取常值。令 \(\mathcal O\) 为 \(\mathcal P(X)\) 在 \(G\) 下的轨道集，并用 \(\tau\) 表示补集 \(A\mapsto A^c\) 在 \(\mathcal O\) 上诱导的对合。

若存在轨道 \(O\) 满足 \(\tau(O)=O\)，则不存在固定记录。因为固定性会使 \(\mu\) 在 \(O\) 上为常数，而 (1.3) 要求其在 \(A\) 与 \(A^c\) 处取相反值。

若不存在这种自互补轨道，则 \(\tau\) 把 \(\mathcal O\) 分成二元素轨道。设这种补集轨道的数目为 \(s\)。其中
\[
\{\{\varnothing\},\{X\}\}
\]
这一轨道被强制取值为 \(\mu(\varnothing)=0,\mu(X)=1\)，其余每个补集轨道独立选择。因此
\[
|R_2(X)^G|=
\begin{cases}
0,&\text{存在自互补 }G\text{-轨道},\\
2^{s-1},&\text{否则}.
\end{cases} \tag{1.17}
\]
所以 \(R_2(X)^G\ne\varnothing\) 当且仅当不存在被补集保持的 \(\mathcal P(X)\)-轨道。

对 \(m\ge3\)，有限集上的超滤子全是主超滤子，且 \(p_x\) 固定当且仅当 \(x\in X^G\)。因此
\[
R_m(X)^G
=\{\eta_{m,X}(x):x\in X^G\}\cong X^G.
\]
特别地，
\[
|R_m(X)^G|=|X^G|,\qquad
R_m(X)^G\ne\varnothing
\Longleftrightarrow X^G\ne\varnothing. \tag{1.18}
\]

固定子集之间的限制映射如下。这里先设 \(X\ne\varnothing\)。

- 若 \(m\ge k\ge3\)，则 \(q_{m,k}\) 在固定记录上是双射，并在同构 (1.18) 下等同于
  \[
  X^G\longrightarrow X^G,\qquad x\mapsto x.
  \]
- 若 \(m\ge3,k=2\)，则为嵌入
  \[
  X^G\longrightarrow R_2(X)^G,\qquad x\mapsto\mu_x.
  \]
  其像为 \(\{\mu_x:x\in X^G\}\)，像上每点一个原像。
- 若 \(m\ge3,k=1\) 且 \(X^G\ne\varnothing\)，则它为常值映射到唯一的 \(R_1(X)^G\) 元素，唯一纤维是整个 \(X^G\)。若 \(X^G=\varnothing\)，则源为空集，而目标仍为单点集，因此
  \[
  q_{m,1}:\varnothing\longrightarrow R_1(X)^G
  \]
  是唯一的空映射。
- 若 \(m=2,k=1\)，则为常值映射
  \[
  R_2(X)^G\longrightarrow R_1(X)^G.
  \]
  若 \(R_2(X)^G\ne\varnothing\)，像为该唯一元素；若源为空，则为空映射。
- \(m=k\) 时为恒等映射。

有限层记录延拓为 \(R_\infty(X)^G\) 中的完整记录的范围如下：

1. \(m=0\) 或 \(1\) 的唯一记录可延拓，当且仅当 \(X^G\ne\varnothing\)。若有延拓，则每个 \(x\in X^G\) 给出一个延拓 \(\eta_{\infty,X}(x)\)。
2. \(m=2\) 的固定记录可延拓，当且仅当存在 \(x\in X^G\) 使得
   \[
   \mu(A)=1\Longleftrightarrow x\in A.
   \]
   这样的 \(x\) 若存在则唯一，因此该记录的完整延拓也唯一。
3. \(m\ge3\) 的每个固定记录都有唯一完整延拓，其超滤子保持不变。

特别地，虽然当 \(X^G=\varnothing\) 时可以存在 \(R_2(X)^G\ne\varnothing\)，例如 \(C_3\) 正则作用于三点集时，这种二阶层记录仍不能延拓成完整固定记录。

## 2. 完整固定记录

### 2.1 超滤子模型与拓扑

对非空 \(X\)，定义
\[
\Phi_X:R_\infty(X)\longrightarrow\beta X,
\qquad
\Phi_X(r)=\{A\subseteq X:\mu_r(A)=1\}. \tag{2.1}
\]
由第 1 节的反向构造，\(\Phi_X\) 是自然双射。

对 \(f:X\to[n]\)、\(j\in[n]\)，
\[
\Phi_X\bigl(\{r:r_n(f)=j\}\bigr)
=\bigl(f^{-1}(j)\bigr)^+. \tag{2.2}
\]
这些集合在 Stone 拓扑下是开闭集。反过来，每个 \(A^+\) 可由测试函数 \(\chi_A\) 得到。因此 \(\Phi_X\) 不但是双射，而且是同胚：
\[
R_\infty(X)\cong\beta X. \tag{2.3}
\]

群在 \(\beta X\) 上的作用为
\[
g\cdot\mathcal U=(g_X)_*\mathcal U
=\{A\subseteq X:g_X^{-1}(A)\in\mathcal U\}. \tag{2.4}
\]

下面给出固定超滤子的基本刻画。

**引理 2.1.** 设 \(T:X\to X\) 是双射，\(\mathcal U\) 是 \(X\) 上的超滤子且 \(T_*\mathcal U=\mathcal U\)。则
\[
\operatorname{Fix}(T)\in\mathcal U.
\]

证明：假设非固定点集 \(E=X\setminus\operatorname{Fix}(T)\in\mathcal U\)。把由偶长度有限轨道和无限轨道组成的 \(E\) 的部分记为 \(E_2\)，把由奇数长度有限轨道组成的部分记为 \(E_3\)。两部分都是 \(T\)-不变的，故 \(\mathcal U\) 恰含其中一个。

在 \(E_2\) 的每个轨道上作二着色，使 \(T\) 交换两种颜色；在 \(E_3\) 的每个轨道上作三着色，使 \(T\) 循环置换三种颜色。取 \(\mathcal U\) 所含的那部分中的这些颜色类。由于这是有限划分，\(\mathcal U\) 恰含其中一个颜色类。但颜色类被 \(T\) 送到不同的颜色类，而 \(T\)-不变性又要求后者也属于 \(\mathcal U\)，矛盾。因此 \(\operatorname{Fix}(T)\in\mathcal U\)。证毕。

由引理 2.1，若 \(\mathcal U\in R_\infty(X)^G\)，则对每个 \(g\in G\)，
\[
X^g:=\operatorname{Fix}(g)\in\mathcal U. \tag{2.5}
\]
反过来，若超滤子包含所有这些 \(X^g\)，则对任意 \(A\subseteq X\)，
\[
A\cap X^g=g_X^{-1}(A)\cap X^g.
\]
因此
\[
A\in\mathcal U
\Longleftrightarrow
A\cap X^g\in\mathcal U
\Longleftrightarrow
g_X^{-1}(A)\in\mathcal U.
\]
所以 \(\mathcal U\) 在 \(G\) 下固定。于是
\[
R_\infty(X)^G
\cong
\{\mathcal U\in\beta X:X^g\in\mathcal U\quad\forall g\in G\}. \tag{2.6}
\]
这个刻画只依赖 \(X\) 及其作用。

### 2.2 非空判准

令 \(\mathcal F_G\) 为 \(\{X^g:g\in G\}\) 生成的滤子。由 (2.6)，
\[
R_\infty(X)^G\ne\varnothing
\]
当且仅当 \(\mathcal F_G\) 是真滤子。根据 ZFC 中的超滤子延拓定理，这又等价于这些集合具有有限交性质，即
\[
X^{g_1}\cap\cdots\cap X^{g_s}\ne\varnothing
\]
对任意有限个 \(g_1,\dots,g_s\) 都成立。

由于
\[
X^{g_1}\cap\cdots\cap X^{g_s}
=X^{\langle g_1,\dots,g_s\rangle},
\]
得到准确判准
\[
\boxed{
R_\infty(X)^G\ne\varnothing
\Longleftrightarrow
X^H\ne\varnothing
\text{ 对每个有限生成子群 }H\le G.} \tag{2.7}
\]

因此，若 \(G\) 有限生成，则
\[
R_\infty(X)^G\ne\varnothing
\Longleftrightarrow X^G\ne\varnothing.
\]
对于无限生成群，则只需要每个有限生成子群各自有固定点，而不要求这些固定点有公共元素。

### 2.3 点值记录的闭包

点值记录对应主超滤子：
\[
\Phi_X(\eta_{\infty,X}(X^G))
=\{p_x:x\in X^G\}. \tag{2.8}
\]
若 \(A=X^G\)，则
\[
\overline{\{p_x:x\in A\}}
=A^+
=\{\mathcal U\in\beta X:A\in\mathcal U\}. \tag{2.9}
\]
这包括 \(A=\varnothing\) 的情形，此时两边都为空。

因此，
\[
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\]
当且仅当每个包含全部 \(X^g\) 的超滤子都包含 \(X^G\)。

由紧性和 (2.9)，这等价于存在有限个 \(g_1,\dots,g_s\) 使
\[
X^{g_1}\cap\cdots\cap X^{g_s}\subseteq X^G.
\]
左侧总是 \(X^G\) 的超集，因此上式等价于相等。于是
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\Longleftrightarrow
\exists H\le_{\mathrm{fg}}G
\text{ 使 }X^H=X^G.} \tag{2.10}
\]
当 \(X^G=\varnothing\) 时也自动包含在内：此时闭包为空，而 (2.10) 精确判断完整固定记录集是否也为空。

### 2.4 对每个 \(G\)-集都满足等式的群

**定理 2.2.** 一个群 \(G\) 对每个 \(G\)-集 \(X\) 都满足
\[
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\]
当且仅当 \(G\) 有限生成。

证明：若 \(G\) 有限生成，在 (2.10) 中取 \(H=G\) 即可。

反过来，设 \(G\) 不有限生成。令
\[
X=\bigsqcup_{H\le_{\mathrm{fg}}G}G/H, \tag{2.11}
\]
其中并取遍所有有限生成子群 \(H\le G\)，并采用左陪集作用。

若陪集 \(aH\) 被整个 \(G\) 固定，则对每个 \(g\in G\) 都有
\[
gaH=aH,
\]
从而 \(a^{-1}Ga\subseteq H\)，即 \(G\subseteq aHa^{-1}\)。于是 \(G=H\)，这与 \(G\) 不有限生成矛盾。因此
\[
X^G=\varnothing.
\]
另一方面，任取有限生成子群 \(K\le G\)，在分量 \(G/K\) 中，陪集 \(K\) 被整个 \(K\) 固定。因此
\[
X^K\ne\varnothing.
\]
于是不存在有限生成子群 \(H\) 使 \(X^H=X^G\)，(2.10) 失败。证毕。

### 2.5 可数群与可数底集的具体例子

令
\[
G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N)
=\{g:\mathbb N\to\mathbb N:
g\text{ 是双射且只移动有限多个点}\}
\]
并令 \(G\) 自然作用于 \(X=\mathbb N\)。群 \(G\) 和底集 \(\mathbb N\) 均可数。

对任意 \(n\in\mathbb N\)，交换 \(n\) 与另一个点的对换会把 \(n\) 移走，所以
\[
X^G=\varnothing. \tag{2.12}
\]

另一方面，每个 \(g\in G\) 的固定点集都是余有限集。若 \(\mathcal U\) 是 \(\mathbb N\) 上的非主超滤子，则 \(\mathcal U\) 包含每个余有限集，所以对每个 \(g\in G\)，\(\operatorname{Fix}(g)\in\mathcal U\)。由 (2.6)，\(\mathcal U\) 是固定超滤子。

若 \(\mathcal U=p_n\) 是主超滤子，取一个移动 \(n\) 的有限对换 \(g\)，则 \(\operatorname{Fix}(g)\notin p_n\)，所以 \(p_n\) 不固定。因此
\[
R_\infty(\mathbb N)^G
\cong\beta\mathbb N\setminus\mathbb N. \tag{2.13}
\]

全部不动记录精确地由所有非主超滤子 \(\mathcal U\in\beta\mathbb N\) 给出：
\[
r_n^{\mathcal U}(f)=j
\quad\Longleftrightarrow\quad
f^{-1}(j)\in\mathcal U. \tag{2.14}
\]
由于 \(\eta_{\infty,\mathbb N}(\mathbb N^G)\) 的定义域为空，
\[
\overline{\eta_{\infty,\mathbb N}(\mathbb N^G)}
=\varnothing
\ne
R_\infty(\mathbb N)^G.
\]
这同时给出题面要求的可数群、可数底集且完整固定记录非空的实例。

## 3. 乘积比较

设
\[
P=\prod_{i\in I}X_i
\]
取对角 \(G\)-作用，并令 \(p_i:P\to X_i\) 为投影。在超滤子模型下，
\[
\Pi_{X_i}(\mathcal U)
=\bigl((p_i)_*\mathcal U\bigr)_{i\in I}. \tag{3.1}
\]

### 3.1 良定义与连续性

\(P^\ast\) 表示 \(p_i\) 诱导的 \(G\)-等变映射时，任意 \(G\)-不变超滤子都映到 \(G\)-不变超滤子，故 (3.1) 良定义。

对任意 \(i\)、任意测试函数 \(f:X_i\to[n]\) 和 \(j\in[n]\)，
\[
((p_i)_*\mathcal U)_n(f)=j
\Longleftrightarrow
\mathcal U_n(f\circ p_i)=j.
\]
因此每个投影分量都连续。由乘积拓扑的泛性质，\(\Pi\) 连续。

### 3.2 满射性

**定理 3.1.** 对任意群 \(G\) 和任意集合指标族 \((X_i)_{i\in I}\)，映射
\[
\Pi_{(X_i)}:
R_\infty(P)^G
\longrightarrow
\prod_{i\in I}R_\infty(X_i)^G
\]
总是满射。

证明：若 \(I=\varnothing\)，则 \(P\) 为单点集，两边都只有一个元素。

若某个 \(X_i=\varnothing\)，则 \(P=\varnothing\)，由 (1.1) 两边都为空，空映射是满射。

以下假设所有 \(X_i\ne\varnothing\)。取右边任意元素，即一族 \(G\)-不变超滤子 \(\mathcal U_i\in\beta X_i\)。考虑集合族
\[
\left\{
P^H\cap\bigcap_{i\in F}p_i^{-1}(B_i):
H\le_{\mathrm{fg}}G,\ 
F\subseteq I\text{ 有限},\ 
B_i\in\mathcal U_i
\right\}. \tag{3.2}
\]
它满足有限交性质。事实上，任意有限交可以合并为对某个有限生成子群 \(K\) 的 \(P^K\) 和有限多个坐标柱集的交。

对每个 \(i\in F\)，由于 \(\mathcal U_i\) 是固定超滤子，
\[
X_i^K\in\mathcal U_i.
\]
又 \(B_i\in\mathcal U_i\)，故
\[
B_i\cap X_i^K\ne\varnothing.
\]
选取 \(x_i\in B_i\cap X_i^K\)；对其余 \(i\)，选择 \(x_i\in X_i^K\)。这些坐标可以独立选择，所得 \(x=(x_i)_{i\in I}\) 属于 \(P^K\) 且属于所有选定的柱集。

所以 (3.2) 具有有限交性质。由超滤子延拓定理，它可以扩张为 \(P\) 上的超滤子 \(\mathcal U\)。对每个 \(i\)，所有 \(p_i^{-1}(B_i)\) 都在 \(\mathcal U\) 中，因此
\[
\mathcal U_i\subseteq(p_i)_*\mathcal U.
\]
两边都是超滤子，所以
\[
(p_i)_*\mathcal U=\mathcal U_i.
\]
此外 \(\mathcal U\) 包含每个 \(P^H\)，特别包含每个 \(P^g\)，故 \(\mathcal U\) 在 \(G\) 下固定。因此 \(\Pi(\mathcal U)\) 等于事先给定的元素。证毕。

### 3.3 平凡群的两因子单射判准

令 \(G=\{e\}\)。此时
\[
\Pi_{X,Y}:\beta(X\times Y)
\longrightarrow\beta X\times\beta Y \tag{3.3}
\]
就是两坐标推前映射。

**定理 3.2.** (3.3) 是单射当且仅当 \(X\) 或 \(Y\) 有限。

证明：若 \(X=\varnothing\) 或 \(Y=\varnothing\)，两边都为空，结论成立。否则，设 \(X\) 有限。取
\[
\mathcal U,\mathcal V\in\beta(X\times Y)
\]
且两坐标推前分别相同。有限集 \(X\) 上的超滤子必为主超滤子，所以存在 \(x\in X\) 使
\[
(p_X)_*\mathcal U=(p_X)_*\mathcal V=p_x.
\]
于是
\[
\{x\}\times Y\in\mathcal U\cap\mathcal V.
\]
在这条公共纤维上，两个超滤子的 \(Y\)-投影相同，故它们限制在该纤维上的判定相同。由于每个超滤子都包含整条纤维，对整个 \(X\times Y\) 中每个集合的判定也相同。因此 \(\mathcal U=\mathcal V\)。\(Y\) 有限时同理。

反过来，设 \(X,Y\) 都无限。取可数无限子集 \(X_0\subseteq X\)、\(Y_0\subseteq Y\)，并把它们与 \(\mathbb N\) 双射。取 \(\mathbb N\) 上两个非主超滤子 \(\mathcal A,\mathcal B\)，并令
\[
E=\{(m,n)\in\mathbb N^2:m+n\text{ 为偶数}\}.
\]
考虑
\[
\mathcal R=\{A\times B:A\in\mathcal A,\ B\in\mathcal B\}.
\]
每个 \(A,B\) 都无限，故每个 \(A\times B\) 与 \(E\) 和 \(E^c\) 均相交。因此
\[
\mathcal R\cup\{E\},\qquad
\mathcal R\cup\{E^c\}
\]
都分别具有有限交性质，从而分别可以扩张成 \(\mathbb N^2\) 上的两个不同超滤子 \(\mathcal U_+,\mathcal U_-\)。

两者投影都分别等于 \(\mathcal A,\mathcal B\)：以 \(\mathcal A\) 为例，所有柱集 \(A\times\mathbb N\) 属于两个超滤子，因此 \(\mathcal A\) 包含于其第一坐标推前；两边都是超滤子，所以相等。

最后沿包含映射 \(X_0\times Y_0\hookrightarrow X\times Y\) 作推前，得到 \(X\times Y\) 上的两个不同超滤子，它们仍有相同的两条坐标投影。因此 (3.3) 不是单射。证毕。

### 3.4 任意群下的两个全称命题

**命题一：真。**

设 \(X\) 或 \(Y\) 有限。由定理 3.1，两因子比较映射总是满射。

设 \(X\) 有限。取
\[
\mathcal U,\mathcal V\in R_\infty(X\times Y)^G
\]
且它们在两个因子上的投影分别相同。由于 \((p_X)_*\mathcal U\) 必须是 \(X\) 上的主超滤子，存在 \(x\in X^G\) 使
\[
\{x\}\times Y\in\mathcal U\cap\mathcal V.
\]
在公共纤维上，两者由相同的 \(Y\)-投影决定，因此对整个 \(X\times Y\) 上每个子集的判定相同，故 \(\mathcal U=\mathcal V\)。\(Y\) 有限时同理。空因子情形也退化为空映射。

所以，若至少一个因子有限，则两因子比较映射是双射。

**命题二：假。**

取第 2.5 节的
\[
G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N),\qquad X=Y=\mathbb N,
\]
采用自然作用，并在 \(\mathbb N^2\) 上取对角作用。此时
\[
X^G=Y^G=\varnothing.
\]

取一个非主超滤子 \(\mathcal U\in\beta\mathbb N\)，并令
\[
\mathcal B=\{B\times C:B,C\in\mathcal U\}.
\]
每个 \(B,C\in\mathcal U\) 都无限，故每个 \(B\times C\) 与
\[
E=\{(m,n):m+n\text{ 为偶数}\}
\]
及其余集 \(E^c\) 都相交。于是
\[
\mathcal B\cup\{E\},\qquad
\mathcal B\cup\{E^c\}
\]
分别可以扩张为两个超滤子 \(\mathcal W_+,\mathcal W_-\)。它们不同，因为一个含 \(E\)，另一个含 \(E^c\)。

两者的两个坐标投影都等于 \(\mathcal U\)：对任意 \(B\in\mathcal U\)，柱集 \(B\times\mathbb N\) 和 \(\mathbb N\times B\) 都属于两个超滤子，故 \(\mathcal U\) 包含于每个投影；投影本身也是超滤子，所以相等。

最后说明它们都固定。对任意 \(g\in G\)，其余有限固定点集 \(F_g=\mathbb N\setminus\operatorname{supp}(g)\) 属于 \(\mathcal U\)，所以
\[
F_g\times F_g\in\mathcal B\subseteq\mathcal W_\pm.
\]
而 \(F_g\times F_g\) 正是对角映射 \((x,y)\mapsto(gx,gy)\) 的固定点集。由 (2.6)，\(\mathcal W_+\) 和 \(\mathcal W_-\) 都在对角 \(G\)-作用下固定。

因此两因子比较把两个不同的固定超滤子送到同一个元素 \((\mathcal U,\mathcal U)\)，不是单射。命题二为假。

## 自评与修订记录

保留的超滤子分类、有限生成子群判准、闭包判准、有限生成群分类、乘积满射性、有限因子双射性以及 \(\operatorname{Sym}_{\mathrm{fin}}(\mathbb N)\) 的例子，均给出了完整论证。

本次主要修正了两处旧稿中的细节：

- 在由三层记录恢复超滤子时，改用 \(\mu_r=1-r_2(\chi_A)\)，从而交集公式准确写成
  　\[
  　\mu(A\cap B)=\mu(A)\mu(B),
  　\]
  避免了旧稿中把 \(0/1\) 编码与通常布尔“且”混用的问题。
- 修正了有限固定层限制映射的边界：当 \(X\ne\varnothing\) 但 \(X^G=\varnothing\) 时，
  \[
  q_{m,1}:R_m(X)^G\longrightarrow R_1(X)^G
  \]
  是从空集到单点集的空映射，而旧稿误写成了“目标也为空”。

题面范围内未留下已知缺口。由于本轮禁止联网检索，没有作文献原创性比较；这里所称研究性自评仅针对题面所要求的分类、判准、反例与证明的完整程度。按题面属于研究型分类测项，自评为
\[
B2/R3,
\]
在内部核验意义上无已知错误断言，满足严格完成所需的 \(B2\) 与 \(R3\) 条件。