记
\[
\widehat A=\{\mathcal F\in U(X):A\in\mathcal F\}\qquad(A\subseteq X).
\]
因为
\[
\widehat{A\cap B}=\widehat A\cap\widehat B,\qquad
\widehat{X\setminus A}=U(X)\setminus\widehat A,
\]
定义中的 \(m_X(\mathfrak W)\) 确实是 \(X\) 上的超滤子。下面用 ZFC 中的超滤子延拓定理。

称 \(C\subseteq X\) 为 **\(a\)-闭集**，如果
\[
C\in\mathcal F\quad\Longrightarrow\quad a(\mathcal F)\in C
\qquad(\mathcal F\in U(X)).
\]
任意多个 \(a\)-闭集的交仍是 \(a\)-闭集；两个 \(a\)-闭集的并也是，因为超滤子包含一个有限并时，必包含其中一个成员。空集和 \(X\) 也满足该条件。因此这些集合是某个拓扑的闭集。

对 \(A\subseteq X\)，定义
\[
c(A)=a(\widehat A)
=\{a(\mathcal F):\mathcal F\in U(X),\ A\in\mathcal F\}.
\]
单位公理给出 \(A\subseteq c(A)\)。我们证明 \(c(A)\) 是 \(a\)-闭的。

设 \(c(A)\in\mathcal G\in U(X)\)。以下 \(U(X)\) 的子集构成的族有有限交性质：
\[
\{\widehat A\}\ \cup\
\{a^{-1}(B):B\in\mathcal G\}.
\]
事实上，对有限多个 \(B_i\in\mathcal G\)，交集
\(c(A)\cap\bigcap_i B_i\) 属于 \(\mathcal G\)，因此非空；其中任一点都形如某个 \(\mathcal H\in\widehat A\) 的 \(a\)-值。将该族延拓为 \(\mathfrak W\in U(U(X))\)。于是
\[
U(a)(\mathfrak W)=\mathcal G,\qquad A\in m_X(\mathfrak W).
\]
由给定的乘法公理，
\[
a(\mathcal G)
=a\bigl(U(a)(\mathfrak W)\bigr)
=a\bigl(m_X(\mathfrak W)\bigr)\in c(A).
\]
所以 \(c(A)\) 是 \(a\)-闭集。另一方面，任何包含 \(A\) 的 \(a\)-闭集都包含 \(c(A)\)。因此，在刚构造的拓扑中，
\[
\boxed{\quad
\overline A
=\{a(\mathcal F):\mathcal F\in U(X),\ A\in\mathcal F\}.
\quad} \tag{1}
\]

每个 \(\mathcal F\in U(X)\) 都收敛到 \(a(\mathcal F)\)。确实，若开集 \(O\) 包含 \(a(\mathcal F)\) 而 \(O\notin\mathcal F\)，则 \(X\setminus O\in\mathcal F\)；但 \(X\setminus O\) 是 \(a\)-闭集，这迫使 \(a(\mathcal F)\in X\setminus O\)，矛盾。

为证明没有其他极限，设 \(\mathcal F\to x\)。对每个 \(A\in\mathcal F\)，有 \(x\in\overline A\)。由 (1)，\(U(X)\) 中的集合族
\[
\{a^{-1}(\{x\})\}\ \cup\ \{\widehat A:A\in\mathcal F\}
\]
有有限交性质：有限多个 \(\widehat A\) 的交是
\(\widehat{\bigcap A}\)，而 \(\bigcap A\in\mathcal F\)。将该族延拓为 \(\mathfrak W\in U(U(X))\)，则
\[
m_X(\mathfrak W)=\mathcal F,\qquad
U(a)(\mathfrak W)=\delta_x.
\]
于是
\[
a(\mathcal F)
=a\bigl(m_X(\mathfrak W)\bigr)
=a\bigl(U(a)(\mathfrak W)\bigr)
=a(\delta_x)=x.
\]
所以每个超滤子恰好收敛到其 \(a\)-值。

该拓扑是紧 Hausdorff 的。紧性由每个超滤子都收敛推出：若某开覆盖没有有限子覆盖，其各成员的补集可延拓为一个不收敛的超滤子。若两个不同点没有不交的开邻域，则它们的所有邻域组成的族有有限交性质，可延拓为同时收敛到这两点的超滤子，违反极限唯一性；故空间是 Hausdorff。

拓扑也由极限运算唯一确定。一般地，在任意拓扑空间中，
\(x\in\overline C\) 当且仅当存在包含 \(C\) 且收敛到 \(x\) 的超滤子：正向将 \(C\) 和 \(x\) 的所有邻域延拓为超滤子即可。因此，在每个超滤子唯一收敛到其 \(a\)-值的拓扑中，闭集恰好是上述 \(a\)-闭集。

反过来，设 \(X\) 已是紧 Hausdorff 空间。每个超滤子 \(\mathcal F\) 有唯一极限：集合族 \(\{\overline A:A\in\mathcal F\}\) 有有限交性质，紧性给出交中的点，而 Hausdorff 性保证极限唯一。令 \(a(\mathcal F)\) 为这个极限，则 \(a(\delta_x)=x\)。

对 \(\mathfrak W\in U(U(X))\)，令
\[
x=a\bigl(U(a)(\mathfrak W)\bigr).
\]
若开集 \(O\) 包含 \(x\)，则 \(a^{-1}(O)\in\mathfrak W\)。对每个 \(\mathcal F\in a^{-1}(O)\)，由于 \(\mathcal F\to a(\mathcal F)\)，有 \(O\in\mathcal F\)。因此
\[
a^{-1}(O)\subseteq\widehat O,\qquad
\widehat O\in\mathfrak W,\qquad
O\in m_X(\mathfrak W).
\]
这说明 \(m_X(\mathfrak W)\to x\)，故
\[
a\bigl(m_X(\mathfrak W)\bigr)
=a\bigl(U(a)(\mathfrak W)\bigr).
\]
由上面的唯一性论证，从这个极限运算重建出的拓扑就是原拓扑。两种构造因而互为逆。

映射也完全对应。若 \(f:X\to Y\) 连续，则它将 \(\mathcal F\to a(\mathcal F)\) 送到
\(U(f)(\mathcal F)\to f(a(\mathcal F))\)；极限唯一性给出
\[
f\circ a=b\circ U(f).
\]
反之，若该等式成立，对 \(Y\) 的任意闭集 \(D\)，当 \(f^{-1}(D)\in\mathcal F\) 时，
\[
D\in U(f)(\mathcal F)
\quad\Longrightarrow\quad
b\bigl(U(f)(\mathcal F)\bigr)\in D
\quad\Longrightarrow\quad
a(\mathcal F)\in f^{-1}(D).
\]
故 \(f^{-1}(D)\) 是 \(a\)-闭集，\(f\) 连续。这证明了所要求的对象与全部态射的双向对应。

接下来直接由 \(a\) 构造有限观测空间。令
\[
\mathcal B_a=
\left\{B\subseteq X:
\forall\mathcal F\in U(X),\
B\in\mathcal F\iff a(\mathcal F)\in B
\right\}. \tag{2}
\]
按 \(a\)-闭集的定义，\(\mathcal B_a\) 恰好是重建拓扑的闭开集布尔代数：式 (2) 分别表示 \(B\) 和 \(X\setminus B\) 都是 \(a\)-闭集。

有限集合取离散拓扑时，其超滤子极限运算正是题中的 \(b_A\)。因此，由已证明的映射对应，
\[
f:X\to A\text{ 是有限值观测}
\quad\Longleftrightarrow\quad
f^{-1}(\{v\})\in\mathcal B_a\ \text{对每个 }v\in A.
\]
特别地，\(B\in\mathcal B_a\) 当且仅当特征函数
\(\mathbf1_B:X\to\{0,1\}\) 是有限值观测。

令
\[
P=\operatorname{Ult}(\mathcal B_a)
\]
为布尔代数 \(\mathcal B_a\) 的真超滤子所成的集合；这里的超滤子是布尔代数上的超滤子。对 \(B\in\mathcal B_a\)，记
\[
D_B=\{\mathfrak p\in P:B\in\mathfrak p\}.
\]
以所有 \(D_B\) 为基定义 \(P\) 的拓扑。由于
\[
D_B\cap D_C=D_{B\cap C},\qquad
P\setminus D_B=D_{X\setminus B},
\]
这些基集都是闭开的；不同的布尔代数超滤子可由某个 \(D_B\) 及其补集分开。因此 \(P\) 是 Hausdorff 且全不连通的。

定义
\[
q:X\longrightarrow P,\qquad
q(x)=\{B\in\mathcal B_a:x\in B\}.
\]
它满足 \(q^{-1}(D_B)=B\)，所以连续。它也是满射：任意 \(\mathfrak p\in P\) 是一族有有限交性质的闭集，紧性给出
\(\bigcap_{B\in\mathfrak p}B\ne\varnothing\)。取其中的 \(x\)，由超滤子对每个 \(B\) 必含 \(B\) 或其补集，得到 \(q(x)=\mathfrak p\)。于是 \(P=q(X)\) 紧，故是所需的 profinite 空间。

这个构造也可写成有限观测的逆极限。令 \(\Pi\) 为 \(X\) 的所有有限闭开分划，按加细排列，并把每个分划视作其分块组成的有限离散空间。每个 \(\mathfrak p\in P\) 在每个分划中恰好包含一个分块，这些选择与加细映射相容，并给出
\[
P\cong\varprojlim_{\pi\in\Pi}\pi.
\]
反过来，相容选择的分块有有限交性质，紧性给出同时属于这些分块的点；不同的 \(\mathfrak p\) 又可由二分划 \(\{B,X\setminus B\}\) 区分。这也证明上述同构是同胚。

为刻画纤维，先证明一个紧 Hausdorff 空间的事实：对 \(t\in K\)，令
\[
Q_t=\bigcap\{D\subseteq K:D\text{ 闭开且 }t\in D\}.
\]
则 \(Q_t\) 恰是 \(t\) 的连通分支。任何包含 \(t\) 的连通集都包含于 \(Q_t\)。另一方面，若 \(Q_t\) 分成两个非空不交闭集，因它们是紧 Hausdorff 空间中的不交紧集，可取不交开邻域 \(V_0,V_1\)。对紧集
\(K\setminus(V_0\cup V_1)\) 的每一点，可取一个包含 \(t\) 而不包含该点的闭开集；取有限多个的交，得到包含 \(Q_t\) 且包含于 \(V_0\cup V_1\) 的闭开集 \(D\)。此时 \(D\cap V_0\) 和 \(D\cap V_1\) 都是 \(K\) 的闭开集，并分开 \(Q_t\)，与 \(Q_t\) 的定义矛盾。因此 \(Q_t\) 连通。

由 \(q\) 的定义及这个事实，
\[
\boxed{\quad
q^{-1}(q(x))
=\bigcap_{\substack{B\in\mathcal B_a\\x\in B}}B
=\text{\(x\) 所在的连通分支}.
\quad} \tag{3}
\]
等价地，利用特征函数及有限观测的各个纤维，
\[
q(x)=q(y)
\quad\Longleftrightarrow\quad
f(x)=f(y)
\ \text{对所有有限值观测 }f:X\to A. \tag{4}
\]

现在验证泛性质。连续满射 \(q:X\to P\) 从紧空间到 Hausdorff 空间，因而是闭映射，也是商映射。设 \(Z\) 是 profinite 空间，\(g:X\to Z\) 连续。上面的紧 Hausdorff 事实说明，\(Z\) 的不同点可由闭开集分开，因为其连通分支都是单点。若 \(q(x)=q(y)\) 但 \(g(x)\ne g(y)\)，取分开 \(g(x),g(y)\) 的闭开集 \(V\subseteq Z\)，则 \(g^{-1}(V)\in\mathcal B_a\) 分开 \(x,y\)，矛盾。因此 \(g\) 在 \(q\) 的每个纤维上为常值，唯一地写成
\[
g=h\circ q.
\]
由于 \(q\) 是商映射，\(h:P\to Z\) 连续。这证明复合映射
\[
C(P,Z)\longrightarrow C(X,Z),\qquad h\longmapsto h\circ q
\]
是双射。该泛性质也使 \((P,q)\) 在 \(X\) 之上唯一到唯一同胚。

最后，由 (4)，**\(q\) 为单射当且仅当有限值观测分离 \(X\) 的点**。完全用原运算 \(a\) 表述，即
\[
\boxed{\quad
\begin{gathered}
\forall x\ne y,\ \exists B\subseteq X:\quad x\in B,\ y\notin B,\\
\text{且}\quad
\forall\mathcal F\in U(X),\
B\in\mathcal F\iff a(\mathcal F)\in B.
\end{gathered}
\quad}
\]
这里的 \(B\) 对应二值观测 \(\mathbf1_B\)。由 (3)，这些条件也等价于 \(X\) 的所有连通分支都是单点，即重建出的 \(X\) 本身是 profinite 空间。空集情形同样成立：此时 \(\mathcal B_a=\{\varnothing\}\) 没有真布尔代数超滤子，故 \(P=\varnothing\)。