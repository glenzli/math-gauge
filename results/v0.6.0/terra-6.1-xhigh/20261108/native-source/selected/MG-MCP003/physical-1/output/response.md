下面给出一种与 CH1 兼容的形式化：用非负扩展实矩阵分别表示距离的上界和下界，用布尔矩阵记录零距离的传递。矩阵通常不是唯一的；特别是，不应预设存在逐项最优矩阵。

## 1. 距离向量与矩阵运算

设
\[
(\mathcal X,\mathcal G,\bot),\qquad
\mathcal G=\{d_i\}_{i\in I}
\]
是 CH1 中的扩展规范空间，\(I\) 有限非空。记
\[
\mathbf d(x,y):=(d_i(x,y))_{i\in I}.
\]

对矩阵 \(M\in[0,\infty]^{I\times I}\)，定义
\[
(M\mathbf d(x,y))_i
:=\sum_{j\in I}M_{ij}d_j(x,y).
\]
矩阵乘法也按相同的扩展非负实数算术定义：
\[
(MN)_{ij}:=\sum_{k\in I}M_{ik}N_{kj}.
\]
这里特别使用 CH1 的约定 \(0\cdot\infty=0\)。由于指标集有限，上述求和没有无穷级数的歧义。向量和矩阵之间的不等式均按分量理解。

## 2. 上界与下界矩阵

对算子 \(\phi\in\mathcal X_{\mathrm{op}}\)，称矩阵
\[
L\in[0,\infty]^{I\times I}
\]
为 \(\phi\) 的一个**距离上界矩阵**，如果对所有 \(x,y\in\mathcal X\)，
\[
\boxed{\quad
\mathbf d(\phi(x),\phi(y))
\le L\mathbf d(x,y).
\quad}
\]
即对每个 \(i\in I\)，
\[
d_i(\phi(x),\phi(y))
\le \sum_{j\in I}L_{ij}d_j(x,y).
\]

类似地，称矩阵
\[
A\in[0,\infty]^{I\times I}
\]
为 \(\phi\) 的一个**距离下界矩阵**，如果对所有 \(x,y\in\mathcal X\)，
\[
\boxed{\quad
A\mathbf d(x,y)
\le \mathbf d(\phi(x),\phi(y)).
\quad}
\]

因此，同时给出 \(A,L\) 时，可写成
\[
A\mathbf d(x,y)
\le \mathbf d(\phi(x),\phi(y))
\le L\mathbf d(x,y).
\]

单分量、有限 \(L\) 的上界就是通常的 Lipschitz 条件。这里下界是一个独立要求；例如零矩阵始终是下界矩阵，但上界矩阵未必存在。

这些矩阵表示的是**有效界**，不是唯一的算子不变量。若 \(L\) 是上界矩阵且 \(L'\ge L\)，则 \(L'\) 也是上界矩阵；若 \(A\) 是下界矩阵且 \(0\le A'\le A\)，则 \(A'\) 也是下界矩阵。

### 复合

若 \(L_\phi,L_\psi\) 分别是 \(\phi,\psi\) 的上界矩阵，则
\[
\mathbf d(\psi\phi(x),\psi\phi(y))
\le L_\psi\mathbf d(\phi(x),\phi(y))
\le L_\psi L_\phi\mathbf d(x,y).
\]
所以 \(L_\psi L_\phi\) 是 \(\psi\circ\phi\) 的上界矩阵。

同理，若 \(A_\phi,A_\psi\) 分别是下界矩阵，则
\[
A_\psi A_\phi\mathbf d(x,y)
\le A_\psi\mathbf d(\phi(x),\phi(y))
\le \mathbf d(\psi\phi(x),\psi\phi(y)),
\]
故 \(A_\psi A_\phi\) 是复合的下界矩阵。这使用了扩展非负实数乘法和有限求和的单调性与分配律。

恒等算子的上下界矩阵都可以取单位矩阵。

## 3. 允许无穷大后的边界

允许矩阵元素为 \(\infty\)，可以统一表达一些没有有限 Lipschitz 常数的算子。例如，在 \([0,\infty)\) 上取通常距离并添入隔离的 \(\bot\)，令
\[
\phi(x)=\sqrt{x},\qquad \phi(\bot)=\bot.
\]
在 \(0\) 附近它没有有限 Lipschitz 常数，但 \([\infty]\) 是其上界矩阵。

不过，即使允许所有元素为 \(\infty\)，上界矩阵也**不一定存在**。定义共同零距离关系
\[
x\sim y
\quad\Longleftrightarrow\quad
d_j(x,y)=0\quad(\forall j\in I).
\]
则有以下准确结论：

> 算子 \(\phi\) 存在扩展实上界矩阵，当且仅当
> \[
> x\sim y\ \Longrightarrow\ \phi(x)\sim\phi(y).
> \]

**论证。** 若存在上界矩阵，输入所有分量都为零时，其矩阵乘积也为零，包括含 \(\infty\) 的项，因为 \(\infty\cdot0=0\)。因此输出所有分量都为零。

反过来，若 \(\phi\) 保持共同零距离，取每个元素均为 \(\infty\) 的矩阵。输入所有分量都为零时，上界成立；否则至少一个输入分量为正，右侧每一行都是 \(\infty\)，上界仍成立。∎

作为反例，取非吸收点 \(a,b\)，令 \(d(a,b)=0\)，并按 CH1 令它们到 \(\bot\) 的距离为 \(\infty\)。若
\[
\phi(a)=a,\qquad \phi(b)=\bot,\qquad \phi(\bot)=\bot,
\]
则零距离输入变成无穷距离输出，所以不存在上界矩阵。

允许 \(\infty\) 还意味着：有限上界矩阵不能把所有分量距离均有限的一对输入映成某个分量距离为 \(\infty\) 的输出。特别地，由于吸收元隔离，这样的输入对不能一个被送到 \(\bot\)、另一个不被送到 \(\bot\)。

## 4. 不可区分性的矩阵

对每个分量，定义关系
\[
x\sim_j y
\quad\Longleftrightarrow\quad
d_j(x,y)=0.
\]
由伪度量公理，\(\sim_j\) 是等价关系；但不同点可以属于同一个等价类。

定义 \(\phi\) 的**零距离传递矩阵**
\[
C(\phi)\in\{0,1\}^{I\times I}
\]
为
\[
\boxed{\quad
C(\phi)_{ij}=1
\quad\Longleftrightarrow\quad
\forall x,y\in\mathcal X,\ 
d_j(x,y)=0\ \Longrightarrow\
d_i(\phi(x),\phi(y))=0.
\quad}
\]

换言之，\(C(\phi)_{ij}=1\) 表示：每个输入的 \(\sim_j\) 等价类，经 \(\phi\) 映射后都落在某个输出的 \(\sim_i\) 等价类内。这正好表达“某类输入在输出分量 \(i\) 中不可区分”。

矩阵元素为 \(0\) 表示上述全称蕴含不成立；若只需要记录已经证明的性质，也可以使用一个逐项不超过 \(C(\phi)\) 的布尔矩阵作为证书。

### 复合

使用布尔矩阵乘法
\[
(BC)_{ij}:=\bigvee_{k\in I}(B_{ik}\wedge C_{kj}),
\]
有
\[
\boxed{\quad
C(\psi\circ\phi)\ \ge\ C(\psi)C(\phi).
\quad}
\]
这里 \(1\ge0\)。事实上，如果某个 \(k\) 满足
\(C(\phi)_{kj}=1\) 和 \(C(\psi)_{ik}=1\)，就可依次传递
\[
d_j(x,y)=0
\Longrightarrow d_k(\phi(x),\phi(y))=0
\Longrightarrow d_i(\psi\phi(x),\psi\phi(y))=0.
\]
一般只能保证不等式：复合可能产生额外的不可区分性。恒等算子满足 \(C(\mathrm{id})_{ii}=1\)；由于不同分量的零距离关系可能存在包含关系，非对角元素也可能为 \(1\)。

## 5. 三种矩阵之间的关系

上界矩阵可以给出零距离性质。若 \(L\) 是 \(\phi\) 的上界矩阵，并且第 \(i\) 行除第 \(j\) 个元素外全为零，则
\[
d_i(\phi(x),\phi(y))\le L_{ij}d_j(x,y),
\]
因而 \(C(\phi)_{ij}=1\)。即使 \(L_{ij}=\infty\)，这个结论仍成立，因为 \(\infty\cdot0=0\)。

更一般地，若令
\[
J_i:=\{j:L_{ij}\ne0\},
\]
则
\[
d_j(x,y)=0\quad(\forall j\in J_i)
\quad\Longrightarrow\quad
d_i(\phi(x),\phi(y))=0.
\]
这是一种由**多个输入分量共同决定**的不可区分性；它不一定能仅由单个布尔矩阵元素 \(C(\phi)_{ij}\) 表达。

下界矩阵则给出反方向的信息。若 \(A\) 是下界矩阵且 \(A_{ij}>0\)，包括 \(A_{ij}=\infty\) 的情况，则
\[
d_i(\phi(x),\phi(y))=0
\quad\Longrightarrow\quad
d_j(x,y)=0.
\]
因为
\[
A_{ij}d_j(x,y)
\le (A\mathbf d(x,y))_i
\le d_i(\phi(x),\phi(y)).
\]
所以，上界与零距离传递关注输入不可区分性如何传到输出；正的下界元素还限制输出把哪些输入区分信息抹去。

最后，一般不能把有效矩阵逐项取最小值或最大值，期望仍得到有效矩阵。例如若 \(d_1=d_2=d\)，恒等算子的某一输出分量既可由行向量 \((1,0)\) 上界，也可由 \((0,1)\) 上界，但逐项最小值 \((0,0)\) 通常不是上界。下界同样可能不存在逐项最大的有效矩阵。因此，上、下界宜视为各自的**矩阵集合**，而零距离传递矩阵 \(C(\phi)\) 则由上述蕴含唯一确定。