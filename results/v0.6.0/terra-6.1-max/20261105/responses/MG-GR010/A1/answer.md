以下记 \(1\) 为单点空间。所有所用函数空间、幂集及有限积仍是 \(\mathsf U\)-小的；例如本答卷中构造的超滤空间，其底集是 \(\mathcal P(\mathcal P(K))\) 的子集。

## S1　局部紧输入

**结论：求值连续，所述柯里化给出自然双射。**

先证求值。设 \(f\in C_{\mathrm{co}}(X,Y)\)、\(x\in X\)，且 \(f(x)\in O\)，其中 \(O\subseteq Y\) 开。由于 \(X\) 局部紧 Hausdorff，\(x\) 在开集 \(f^{-1}(O)\) 中有紧邻域：存在紧集 \(K\) 满足
\[
x\in \operatorname{int}K\subseteq K\subseteq f^{-1}(O).
\]
于是
\[
(f,x)\in [K,O]\times\operatorname{int}K
\]
且这个邻域在求值下映入 \(O\)。故通常求值
\[
\operatorname{ev}:C_{\mathrm{co}}(X,Y)\times X\longrightarrow Y
\]
连续。

若 \(F:Z\times X\to Y\) 连续，定义
\[
F^\sharp(z)(x)=F(z,x).
\]
每个 \(F^\sharp(z)\) 连续。对紧集 \(K\subseteq X\) 和开集 \(O\subseteq Y\)，若 \(F(\{z_0\}\times K)\subseteq O\)，由连续性及 \(K\) 的紧性，存在 \(z_0\) 的邻域 \(W\)，使
\[
F(W\times K)\subseteq O.
\]
因此 \((F^\sharp)^{-1}[K,O]\) 开，故 \(F^\sharp:Z\to C_{\mathrm{co}}(X,Y)\) 连续。

反过来，若 \(g:Z\to C_{\mathrm{co}}(X,Y)\) 连续，则其伴随映射
\[
g^\flat(z,x)=g(z)(x)
\]
是
\[
Z\times X\xrightarrow{\,g\times\mathrm{id}\,}
C_{\mathrm{co}}(X,Y)\times X\xrightarrow{\operatorname{ev}}Y
\]
的复合，因而连续。这两个操作逐点互逆。

该双射对 \(Z\) 的预复合、对 \(Y\) 的后复合自然。它对局部紧 Hausdorff 输入 \(X\) 也逆变自然：若 \(u:X'\to X\) 连续，且 \(X'\) 也局部紧 Hausdorff，则预复合算子连续，因为
\[
u^*[K,O]=[u(K),O].
\]

## S2　探针能检测的映射

### 1. Profinite 探针足够

每个 \(\mathsf U\)-小紧 Hausdorff 空间 \(K\) 都是某个 \(\mathsf U\)-小 profinite 空间的连续像。具体地，令 \(P\) 为底集 \(K\) 上所有超滤的集合，并以
\[
\widehat A=\{\mathcal U:A\in\mathcal U\}\qquad(A\subseteq K)
\]
为开闭基。由 ZFC 中的超滤引理，\(P\) 紧；上述开闭集分离点，所以 \(P\) 是 Hausdorff 且全不连通。

每个超滤在紧 Hausdorff 空间 \(K\) 中有唯一极限，故得到
\[
q:P\longrightarrow K,\qquad \mathcal U\longmapsto \lim\mathcal U.
\]
利用紧 Hausdorff 空间的正则性可知 \(q\) 连续；主超滤说明它满射。紧空间到 Hausdorff 空间的连续满射是商映射。空空间的情形直接成立。

因此，若 \(O\subseteq X\) 对所有 profinite 探针的原像均开，且 \(a:K\to X\) 是任意紧 Hausdorff 探针，则
\[
q^{-1}(a^{-1}O)=(a q)^{-1}O
\]
在 \(P\) 中开；由 \(q\) 是商映射，\(a^{-1}O\) 在 \(K\) 中开。反向蕴含显然。故两类探针定义同一 \(k\) 拓扑。

### 2. 关于 \(k\) 的基本事实

对任意 Hausdorff 空间 \(T\) 和紧 Hausdorff 空间 \(K\)，定义直接给出
\[
C(K,T)=C(K,kT)                                                   \tag{2.1}
\]
作为同一底集上的函数集合。因此 \(k(kT)=kT\)。此外，若 \(A=kA\)，则
\[
C(A,T)=C(A,kT).                                                   \tag{2.2}
\]
确实，若 \(a:A\to T\) 连续，对 \(kT\) 的每个开集 \(O\)，以及每个紧 Hausdorff 探针 \(p:K\to A\)，由 (2.1) 知 \((ap)^{-1}O\) 开；因 \(A=kA\)，所以 \(a^{-1}O\) 开。反向只需复合连续映射 \(kT\to T\)。

特别地，原拓扑连续映射 \(u:T\to T'\) 给出连续映射
\[
ku:kT\longrightarrow kT'.
\]
两个空间的紧探针逐坐标相同，也给出同一底集上的等式
\[
k(T\times T')=k(kT\times kT').                                   \tag{2.3}
\]

### 3. 自然变换的识别

给定 \(\tau:h_X\to h_Y\)，其单点分量确定函数
\[
f=\tau_1:X\longrightarrow Y.
\]
对任意 profinite \(P\)、\(a:P\to X\) 和 \(p\in P\)，对点映射 \(1\to P\) 使用自然性得到
\[
\tau_P(a)(p)=f(a(p)).
\]
所以 \(\tau_P(a)=f\circ a\)。反之，若函数 \(f:X\to Y\) 与每个 profinite 探针的复合均连续，这一公式定义自然变换。

由第 1 部分的商映射论证，该条件等价于：对每个紧 Hausdorff 探针 \(a:K\to X\)，\(fa:K\to Y\) 连续。再由 (2.1)，它等价于 \(f:kX\to kY\) 连续。因此有与复合及单位相容的双射
\[
\boxed{\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY).}                \tag{2.4}
\]

最后，若 \(X=kX\)，则 (2.4) 中的映射与 \(kY\to Y\) 复合，给出原拓扑连续的 \(X\to Y\)。

反之，取 \(Y=kX\)。恒等底集函数 \(X\to kX\) 由 (2.1) 定义自然变换 \(h_X\to h_{kX}\)。若该变换由原拓扑连续映射诱导，则看单点分量可知该连续映射只能是 \(\mathrm{id}:X\to kX\)。结合连续映射 \(kX\to X\)，得到 \(X=kX\)。这证明了所求充要条件。

## S3　全部参数化映射记录

### 1. 一个紧生成指数律

先对紧生成 Hausdorff 空间 \(A,B\) 证明
\[
C\!\left(T,kC_{\mathrm{co}}(A,B)\right)
\cong C(T\times_k A,B)                                           \tag{3.1}
\]
对每个紧生成 Hausdorff 空间 \(T\) 自然成立。

令 \(E=C_{\mathrm{co}}(A,B)\)。因 \(B\) Hausdorff，单点子基集可分离 \(E\) 中不同函数，所以 \(E\) Hausdorff，\(kE\) 也是紧生成 Hausdorff 空间。

通常逐点求值从 \(k(E\times A)\) 到 \(B\) 连续。确实，取任意紧 Hausdorff 探针
\[
p=(p_1,p_2):P\longrightarrow E\times A.
\]
令 \(L=p_2(P)\)。它是 \(A\) 的紧 Hausdorff 子空间，限制映射
\[
r_L:E\longrightarrow C_{\mathrm{co}}(L,B)
\]
连续，因为 \(L\) 中的紧集在 \(A\) 中仍紧。由 S1，输入 \(L\) 的通常求值连续，于是
\[
P\longrightarrow C_{\mathrm{co}}(L,B)\times L
\longrightarrow B
\]
连续。按 \(k\) 拓扑的定义，得到连续求值
\[
e:kE\times_k A=k(kE\times A)=k(E\times A)\longrightarrow B.        \tag{3.2}
\]

若 \(g:T\to kE\) 连续，则 \(e(g(t),a)\) 定义连续映射 \(T\times_k A\to B\)。

反之，设 \(F:T\times_k A\to B\) 连续。对固定 \(t\)，映射
\[
A\longrightarrow T\times_k A,\quad a\longmapsto(t,a)
\]
连续：它到普通积的对应映射连续，而 \(A=kA\)，可用 (2.2)。故 \(F^\sharp(t):a\mapsto F(t,a)\) 属于 \(E\)。

为证明 \(F^\sharp:T\to E\) 连续，取紧 Hausdorff 探针 \(p:P\to T\) 和紧集 \(K\subseteq A\)。\(K\) 是紧 Hausdorff，且 \(P\times K\) 也是紧 Hausdorff；连续映射
\[
P\times K\longrightarrow T\times A,\quad (s,a)\longmapsto(p(s),a)
\]
由 (2.1) 提升为到 \(T\times_k A\) 的连续映射。对复合
\[
P\times K\longrightarrow T\times_k A\xrightarrow{F}B
\]
应用 S1，可知其柯里化 \(P\to C_{\mathrm{co}}(K,B)\) 连续。因此每个
\[
p^{-1}\bigl((F^\sharp)^{-1}[K,O]\bigr)
\]
都开。由于 \(T=kT\)，\(F^\sharp:T\to E\) 连续；由 (2.2)，它也连续到 \(kE\)。两个操作逐点互逆，证明 (3.1)。

这里以及下文所用的 \(\times_k\) 确为紧生成 Hausdorff 空间范畴中的积：对紧生成 \(T\)，由 (2.2)，到 \(k(A\times B)\) 的连续映射恰为到普通积 \(A\times B\) 的连续映射。

### 2. 实现空间及其参数化性质

定义
\[
\boxed{M(X,Y)=kC_{\mathrm{co}}(kX,kY).}
\]
其底集是 \(C(kX,kY)\)；先赋予该集合紧开拓扑，再取 \(k\) 拓扑。由上面的 Hausdorff 性论证，\(M(X,Y)\) 是紧生成 Hausdorff 空间。

对 profinite \(S\)，因 \(S\) 紧 Hausdorff，\(kS=S\)。又有
\[
h_S\times h_X\cong h_{S\times X}.
\]
于是由 S2、(2.3) 和 (3.1)，自然地有
\[
\begin{aligned}
H_{X,Y}(S)
&\cong C(k(S\times X),kY)\\
&=C(S\times_k kX,kY)\\
&\cong C(S,M(X,Y)).
\end{aligned}                                                     \tag{3.3}
\]
所有步骤均与 \(S\) 的预复合相容，所以这是所求的关于 profinite \(S\) 的自然同构。

### 3. 求值与泛性质

对 profinite \(P\)、\(a:P\to M(X,Y)\) 和 \(b:P\to X\)，定义
\[
\operatorname{ev}_P(a,b)(p)=a(p)(b(p)).
\]
由 (2.1)，\(b\) 连续地提升为 \(P\to kX\)；配对映射连续到 \(M(X,Y)\times_k kX\)。再用 (3.2) 和 \(kY\to Y\)，可知上式是连续的 \(P\to Y\)。它显然关于 \(P\) 自然，故定义
\[
\operatorname{ev}:h_{M(X,Y)}\times h_X\longrightarrow h_Y.
\]

对任意 Hausdorff \(Z\)，S2、(2.3) 及 (3.1) 给出
\[
\begin{aligned}
\operatorname{Nat}(h_Z,h_M)
&\cong C(kZ,M)\\
&\cong C(kZ\times_k kX,kY)\\
&=C(k(Z\times X),kY)\\
&\cong\operatorname{Nat}(h_Z\times h_X,h_Y).
\end{aligned}
\]
逐点核验可知，此双射正是
\[
\alpha\longmapsto
\operatorname{ev}\circ(\alpha\times\mathrm{id}_{h_X}).
\]

### 4. \(X,Y\) 中的自然性

给定连续映射 \(u:X'\to X\)、\(v:Y\to Y'\)，定义
\[
M(u,v):M(X,Y)\longrightarrow M(X',Y'),\qquad
F\longmapsto (kv)\circ F\circ(ku).
\]
它连续：在取 \(k\) 之前，目标紧开子基 \([K,O]\) 的原像是
\[
[\,ku(K),(kv)^{-1}(O)\,]，
\]
其中 \(ku(K)\) 紧；取 \(k\) 后仍连续。

这些映射保持单位与复合，且逐点满足
\[
h_v\circ\operatorname{ev}_{X,Y}\circ
(\mathrm{id}\times h_u)
=
\operatorname{ev}_{X',Y'}\circ
(h_{M(u,v)}\times\mathrm{id}).
\]
因此 (3.3) 和上述泛性质都具有所要求的 \(X\) 中逆变、\(Y\) 中协变自然性。

## S4　可数邻域基的输入

**通常求值不一定连续；但第一可数性足以保证 \(kX=X\)。**

反例取 \(X=\mathbb Q\) 的通常拓扑、\(Y=\mathbb R\)，并考察零函数和 \(0\) 处的求值。每个紧集 \(K\subseteq\mathbb Q\) 在 \(\mathbb Q\) 中内部为空：它作为 \(\mathbb R\) 的子集仍紧，因而在 \(\mathbb R\) 中闭；若它包含一个非空有理开区间，就会由有理数的稠密性包含该区间中的无理数，矛盾。

若求值在 \((0,0)\) 连续，则对 \((-1/2,1/2)\)，存在 \(0\in U\subseteq\mathbb Q\) 开及零函数的有限子基邻域
\[
W=\bigcap_{i=1}^n[K_i,O_i]
\]
使得 \(W\times U\) 的求值落入 \((-1/2,1/2)\)。令 \(K=\bigcup_iK_i\)，取 \(x\in U\setminus K\)。若 \(K\ne\varnothing\)，定义
\[
g(t)=\frac{d(t,K)}{d(t,K)+|t-x|}\qquad(t\in\mathbb Q).
\]
由于 \(K\) 闭且 \(x\notin K\)，这是连续函数，满足 \(g|_K=0\)、\(g(x)=1\)。若 \(K=\varnothing\)，取常函数 \(g=1\)。于是 \(g\in W\)，但 \(g(x)=1\)，矛盾。

另一方面，设 \(X\) 第一可数，\(O\subseteq X\) 不是开集。取 \(x\in O\) 使每个 \(x\) 的邻域都遇到 \(X\setminus O\)，并取递减可数邻域基 \(U_n\)。选
\[
x_n\in U_n\setminus O.
\]
从紧 Hausdorff 空间
\[
K=\{0\}\cup\{1/n:n\ge1\}\subseteq\mathbb R
\]
定义 \(p(0)=x\)、\(p(1/n)=x_n\)。由邻域基的选择，\(p\) 连续，但 \(p^{-1}(O)\) 含 \(0\) 而不含任何 \(1/n\)，所以不是开集。故任何 \(kX\)-开集都在 \(X\) 中开；反向总成立，因而 \(kX=X\)。

## S5　空间实现的识别

**不一定是原拓扑的同胚。**

给出具体反例。取 \(\mathsf U\)-小不可数集 \(D\)，例如 \(D=\mathcal P(\mathbb N)\)，再取一点 \(\infty\notin D\)。令
\[
Y=D\sqcup\{\infty\},
\]
其中 \(D\) 的每个点孤立，而含 \(\infty\) 的开集恰是补集为 \(D\) 中至多可数集的集合。\(Y\) 是 Hausdorff，但 \(\{\infty\}\) 不开。

\(Y\) 的每个紧子集都是有限的。否则可在其与 \(D\) 的交中取可数无限集 \(A\)；开覆盖
\[
Y\setminus A,\qquad \{\{a\}:a\in A\}
\]
对该紧集没有有限子覆盖。

令 \(X\) 是同一底集上的离散空间，\(f:X\to Y\) 为恒等函数。它连续，但逆映射不连续。对任意 profinite \(P\)，连续映射 \(P\to Y\) 的像紧，故有限；有限 Hausdorff 子空间离散，所以该映射作为 \(P\to X\) 也连续。因此
\[
h_f(P):C(P,X)\longrightarrow C(P,Y)
\]
逐个都是双射，逆也自然。故 \(h_f\) 是自然同构，而 \(f\) 不是同胚。

## S6　复合与可识别范围

### 1. 连续复合、结合律和单位律

令
\[
P=M(Y,Z)\times_k M(X,Y).
\]
利用 S3 的求值和紧生成空间中的积，得到连续映射
\[
P\times_k kX\longrightarrow kZ,\qquad
(g,f,x)\longmapsto g(f(x)).
\]
由 S3 的指数律转置，得到连续复合
\[
\boxed{M(Y,Z)\times_k M(X,Y)\longrightarrow M(X,Z),\quad
(g,f)\longmapsto g\circ f.}
\]

由 (2.3)，不同括号下的有限 \(k\)-积由通常积的结合双射自然同胚识别。在此识别下，两种三重复合逐点都是
\[
(h,g,f)\longmapsto h\circ g\circ f,
\]
所以结合律成立。单位是
\[
\mathrm{id}_{kX}\in M(X,X),
\]
它定义连续映射 \(1\to M(X,X)\)；左右单位律同样逐点成立。

### 2. \(h_f\) 同构的充要条件

对连续 \(f:X\to Y\)，S2 的识别保持单位与复合，且 \(h_f\) 对应 \(kf:kX\to kY\)。因此
\[
\boxed{h_f\text{ 是自然同构}\quad\Longleftrightarrow\quad
kf:kX\to kY\text{ 是同胚}.}                                      \tag{6.1}
\]

也可表述为：\(f\) 双射，并且对每个紧集 \(C\subseteq Y\)，
\[
f^{-1}|_C:C\longrightarrow X
\]
连续。事实上，若 \(kf\) 是同胚，紧 Hausdorff 子空间 \(C\to Y\) 可提升到 \(kY\)，复合 \((kf)^{-1}\) 即得此连续性。反之，对任意紧 Hausdorff 探针 \(q:K\to Y\)，其像 \(C=q(K)\) 紧，所以上述条件使 \(f^{-1}q\) 连续；由 S2，\(f^{-1}\) 给出连续映射 \(kY\to kX\)，它与 \(kf\) 互逆。

最后，若 \(X,Y\) 均第一可数，S4 给出 \(kX=X\)、\(kY=Y\)。因此 (6.1) 中的 \(kf\) 就是原拓扑映射 \(f\)，所以此时 \(h_f\) 同构**确实能升级为 \(f\) 是普通同胚**。