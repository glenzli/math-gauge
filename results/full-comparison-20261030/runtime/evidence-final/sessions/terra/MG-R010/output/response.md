记
\[
\mathsf K(A,B)=
\{f:A\to B:\text{对每个紧子空间 }K\subseteq A,\ f|_K:K\to B\text{ 连续}\}.
\]
这样的函数未必在 \(A\) 上连续；探针恰好检测到的是这一较弱条件。

对 Hausdorff 空间 \(T\)，令 \(kT\) 有与 \(T\) 相同的底集，并规定 \(D\subseteq T\) 在 \(kT\) 中闭，当且仅当对每个在 \(T\) 中紧的子空间 \(K\subseteq T\)，交集 \(D\cap K\) 在 \(K\) 中闭。这称为 \(T\) 的紧生成化。

现在给 \(\mathsf K(X,Y)\) 赋予由以下集合生成的紧开拓扑：
\[
[K,V]=\{f\in\mathsf K(X,Y):f(K)\subseteq V\},
\]
其中 \(K\subseteq X\) 紧，\(V\subseteq Y\) 开。将所得空间记为 \(M_0(X,Y)\)，并定义
\[
\boxed{\quad M(X,Y)=kM_0(X,Y).\quad}
\]
也就是说，\(M(X,Y)\) 的底集是 \(\mathsf K(X,Y)\)；其闭集 \(D\) 恰好是那些满足下述条件的集合：对每个在上述紧开拓扑中紧的 \(L\subseteq\mathsf K(X,Y)\)，\(D\cap L\) 在 \(L\) 中闭。

这个空间是 Hausdorff 的。事实上，若 \(f\ne g\)，取 \(x\in X\) 及分离 \(f(x),g(x)\) 的不交开集 \(U,V\subseteq Y\)，则 \([\{x\},U]\) 与 \([\{x\},V]\) 分离 \(f,g\)。紧生成化只加细拓扑，因此仍为 Hausdorff 空间。

所需求值自然变换在每个探针 \(T\) 上由
\[
\operatorname{ev}_T(a,b)(t)=a(t)\bigl(b(t)\bigr),
\qquad
a\in C(T,M(X,Y)),\quad b\in C(T,X)
\]
给出。它满足题目中的两个自然双射。下面证明这些断言。

首先，紧生成化有两个基本性质。原拓扑包含于 \(kT\) 的拓扑；若 \(K\subseteq T\) 在原拓扑中紧，则 \(K\) 的原子空间拓扑与从 \(kT\) 继承的拓扑相同。因此 \(T\) 与 \(kT\) 有相同的紧子空间，且这些子空间上的拓扑相同。特别地，若 \(P\) 是紧 Hausdorff 空间，则恒等映射诱导
\[
C(P,kT)=C(P,T). \tag{1}
\]
这些性质也表明 \(k(kT)=kT\)。连续映射 \(v:T\to T'\) 诱导连续映射 \(kv:kT\to kT'\)：只需在 \(kT\) 的每个紧子空间上检查连续性，再使用其紧生成性。

接下来证明，对任意 Hausdorff 空间 \(A,B\)，有自然双射
\[
\operatorname{Nat}(h_A,h_B)\cong\mathsf K(A,B). \tag{2}
\]
一方面，若 \(f\in\mathsf K(A,B)\)，对于探针 \(S\) 和 \(p:S\to A\)，像 \(p(S)\) 是紧子空间，所以 \(f\circ p\) 连续；这给出自然变换。

另一方面，设 \(\eta:h_A\to h_B\)。它在单点空间上的分量给出函数 \(f:A\to B\)。对每个 \(s\in S\)，由点映射 \(1\to S\) 的自然性，
\[
\eta_S(p)(s)=f(p(s)).
\]
所以对每个探针映射 \(p:S\to A\)，复合 \(f\circ p\) 连续。要由此得到 \(f\in\mathsf K(A,B)\)，只需说明每个紧 Hausdorff 空间 \(K\) 都是某个属于 \(\operatorname{Prof}_{\mathcal U}\) 的空间的连续商像。

确实，令 \(\Omega_K\) 为集合 \(K\) 上所有超滤子的空间，取
\[
\widehat E=\{\mathfrak u:E\in\mathfrak u\}\qquad(E\subseteq K)
\]
为开闭基。由超滤子引理，\(\Omega_K\) 紧；这些开闭集分离不同超滤子，故它是 Hausdorff 且全不连通的。每个超滤子在紧 Hausdorff 空间 \(K\) 中有唯一极限，于是得到满射
\[
q:\Omega_K\longrightarrow K,\qquad \mathfrak u\longmapsto\lim\mathfrak u.
\]
此映射连续：若 \(\lim\mathfrak u\in V\) 且 \(V\) 开，取开邻域 \(W\) 使
\(\lim\mathfrak u\in W\subseteq\overline W\subseteq V\)，则
\(\mathfrak u\in\widehat W\subseteq q^{-1}(V)\)。
因此 \(q\) 是从紧空间到 Hausdorff 空间的连续满射，故为商映射。又
\(\Omega_K\subseteq\mathcal P(\mathcal P(K))\)，所以当 \(K\in\mathcal U\) 时，\(\Omega_K\in\operatorname{Prof}_{\mathcal U}\)。

将此应用于紧子空间 \(K\subseteq A\)，可知 \(f|_K\circ q\) 连续；由 \(q\) 为商映射，\(f|_K\) 连续。这证明了 (2)。

为处理映射空间，使用以下紧开拓扑的性质。设 \(P\) 为任意空间，\(v:P\to M_0(X,Y)\) 为函数，写
\[
\widetilde v:P\times X\to Y,\qquad \widetilde v(p,x)=v(p)(x).
\]
则
\[
v\text{ 连续}
\quad\Longleftrightarrow\quad
\text{对每个紧 }K\subseteq X,\ 
\widetilde v|_{P\times K}:P\times K\to Y\text{ 连续}. \tag{3}
\]
对于正向，限制映射 \(M_0(X,Y)\to C(K,Y)\) 在紧开拓扑下连续，而紧 Hausdorff 空间 \(K\) 上的通常求值
\(C(K,Y)\times K\to Y\) 连续。对于反向，若右侧成立，则管状邻域引理表明每个
\[
v^{-1}[K,V]=\{p:\widetilde v(\{p\}\times K)\subseteq V\}
\]
都是开集。

现在考虑点态求值函数
\[
e:M(X,Y)\times X\longrightarrow Y,\qquad e(f,x)=f(x).
\]
它属于 \(\mathsf K(M(X,Y)\times X,Y)\)。事实上，若 \(D\subseteq M(X,Y)\times X\) 紧，其两个投影分别为紧集 \(P\subseteq M(X,Y)\) 和 \(K\subseteq X\)。包含映射 \(P\to M_0(X,Y)\) 连续，因此由 (3)，\(e\) 在 \(P\times K\) 上连续，特别在 \(D\) 上连续。由 (2) 及
\(h_{M(X,Y)\times X}\cong h_{M(X,Y)}\times h_X\)，这正给出上面写出的求值自然变换。这里所需的是 \(e\) 在每个紧子空间上连续；它不必在普通乘积拓扑上连续。

对任意 Hausdorff 参数空间 \(Z\)，柯里化给出双射
\[
\mathsf K(Z,M(X,Y))
\longleftrightarrow
\mathsf K(Z\times X,Y),\qquad
g\longmapsto\bigl((z,x)\mapsto g(z)(x)\bigr). \tag{4}
\]
证明如下。若 \(f\in\mathsf K(Z\times X,Y)\)，则每个
\(g(z):x\mapsto f(z,x)\) 属于 \(\mathsf K(X,Y)\)，因为 \(\{z\}\times K\) 对紧 \(K\subseteq X\) 是紧的。对紧 \(P\subseteq Z\) 和紧 \(K\subseteq X\)，\(f\) 在紧空间 \(P\times K\) 上连续；由 (3)，\(g|_P:P\to M_0(X,Y)\) 连续，再由 (1) 得 \(g|_P:P\to M(X,Y)\) 连续。所以 \(g\in\mathsf K(Z,M(X,Y))\)。

反之，若 \(g\in\mathsf K(Z,M(X,Y))\)，取任意紧
\(D\subseteq Z\times X\)，令其投影为 \(P\subseteq Z\)、\(K\subseteq X\)。映射 \(g|_P:P\to M_0(X,Y)\) 连续，故由 (3)，\((z,x)\mapsto g(z)(x)\) 在 \(P\times K\) 上连续，从而在 \(D\) 上连续。这证明 (4)。

通过 (2)、\(h_Z\times h_X\cong h_{Z\times X}\) 及 (4)，得到所要求的自然双射
\[
\operatorname{Nat}(h_Z,h_{M(X,Y)})
\;\xrightarrow{\;\sim\;}\;
\operatorname{Nat}(h_Z\times h_X,h_Y),
\qquad
\alpha\longmapsto
\operatorname{ev}\circ(\alpha\times I_{h_X}).
\]
当 \(Z=S\in\operatorname{Prof}_{\mathcal U}\) 时，Yoneda 引理给出
\(\operatorname{Nat}(h_S,h_{M(X,Y)})\cong C(S,M(X,Y))\)，因此
\[
C(S,M(X,Y))\cong\mathcal H_{X,Y}(S).
\]
具体地，\(g:S\to M(X,Y)\) 对应的记录满足
\[
\alpha_T(p,q)(t)=g(p(t))(q(t)),
\quad
p:T\to S,\quad q:T\to X.
\]
自然性立即由此公式得到。

对连续映射 \(a:X'\to X\)、\(b:Y\to Y'\)，定义
\[
M(a,b):M(X,Y)\longrightarrow M(X',Y'),
\qquad f\longmapsto b\circ f\circ a.
\]
它确实取值于 \(\mathsf K(X',Y')\)。在紧开拓扑下，它对基本开集的原像为
\[
M(a,b)^{-1}[K',V']
=[a(K'),b^{-1}(V')],
\]
故连续；对两个映射空间取紧生成化后仍连续。点态公式同时表明这些映射与求值及上述双射相容；参数空间的连续变换则对应于对参数预复合。

所有构造均满足宇宙限制：\(\mathsf K(X,Y)\subseteq Y^X\) 属于 \(\mathcal U\)，其紧开拓扑和紧生成化拓扑都是其幂集的子集，因而也属于 \(\mathcal U\)。上面使用的超滤子空间同样属于 \(\mathcal U\)。

最后，**探针并不唯一确定实现空间的普通拓扑**；它们唯一确定的是其紧生成化。更准确地说，若 \(N\) 是另一实现，则 \(h_N\cong h_{M(X,Y)}\)，由 (2) 得到的双向点映射在紧子空间上连续，因而诱导同胚
\[
kN\cong M(X,Y).
\]
例如，取不可数集合 \(D=\mathcal P(\mathbb N)\)，加一点 \(\infty\)，令 \(D\) 的点均孤立，且 \(\infty\) 的邻域恰为补集至多可数的集合。所得 Hausdorff 空间 \(Y\) 的紧子空间全是有限集，故 \(kY\) 是离散空间，而 \(Y\) 不是。对于 \(X=1\)，\(Y\) 和 \(kY\) 都实现相同的探针记录；上述构造选出其中紧生成的 \(kY\)。