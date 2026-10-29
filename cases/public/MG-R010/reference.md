# 参考论证：探针记录之间的映射空间

所要求的空间实现存在。一般应先处理输入空间的探针所决定的拓扑，再构造函数空间；底集不能一概取原拓扑下的 $C(X,Y)$。本题既没有假设输入已紧生成，也没有假设 $X$ 局部紧。

## 主定理与构造

对 Hausdorff 空间 $X$，在相同底集上定义 $kX$：子集 $O\subseteq X$ 开，当且仅当每个 $\mathcal U$ 小紧 Hausdorff 空间 $K$ 上的连续映射 $f:K\to X$ 都满足 $f^{-1}(O)$ 开。以下将证明也可只使用题目的 profinite 探针来定义这个拓扑。

令 $X_0=kX$、$Y_0=kY$。在集合 $C(X_0,Y_0)$ 上取紧开拓扑，记所得空间为 $C_{\mathrm{co}}(X_0,Y_0)$；其子基开集为

$$[K,O]=\{f\in C(X_0,Y_0):f(K)\subseteq O\},$$

其中 $K\subseteq X_0$ 紧，$O\subseteq Y_0$ 开。定义

$$M(X,Y)=k\,C_{\mathrm{co}}(kX,kY).\tag{1}$$

它是 $\mathcal U$ 小 Hausdorff 空间，具有题目所要求的全部自然对应。这里的最终结论是映射记录的空间实现与指数律；$k$ 构造本身只是证明中的一个环节。

## 紧 Hausdorff 空间具有 profinite 覆盖

设 $K$ 为 $\mathcal U$ 小紧 Hausdorff 空间，$D$ 为其底集。若 $D$ 为空，取空覆盖源。否则令 $\beta D$ 为 $D$ 上超滤子的集合，基本开闭集为

$$[A]=\{\mathfrak u:A\in\mathfrak u\},\qquad A\subseteq D.$$

超滤子可识别为布尔代数同态 $\mathcal P(D)\to\{0,1\}$。保持有限交、补及常元的等式在乘积 $\{0,1\}^{\mathcal P(D)}$ 中定义闭子集，Tychonoff 定理因此给出紧性；乘积拓扑给出 Hausdorff 性和开闭基。故 $\beta D$ 是 profinite。其底集包含于 $\mathcal P(\mathcal P(D))$，仍属于 $\mathcal U$。

每个超滤子在 $K$ 中有唯一极限。存在性来自闭集族 $\{\overline A:A\in\mathfrak u\}$ 的有限交性质和紧性。若 $x$ 属于它们的交，则 $x$ 的每个邻域 $O$ 属于 $\mathfrak u$：否则 $D\setminus O\in\mathfrak u$，与 $x\notin\overline{D\setminus O}$ 矛盾。两个不同交点有不交邻域，不能同时属于同一滤子，所以极限唯一。

令 $q:\beta D\to K$ 取超滤子极限。主超滤子给出满射性。若 $O$ 为 $q(\mathfrak u)$ 的开邻域，紧 Hausdorff 的正则性给出开集 $V$，满足

$$q(\mathfrak u)\in V\subseteq\overline V\subseteq O.$$

于是 $V\in\mathfrak u$，且 $[V]\subseteq q^{-1}(O)$，证明连续性。所用正则性可由紧 Hausdorff 性直接推出：把点与闭集中的每一点分离，利用闭集紧性取有限子覆盖，再交点侧的有限多个邻域。$q$ 是紧空间到 Hausdorff 空间的连续满射，故为闭商映射。

因此，一个子集被所有 profinite 探针检验为开，当且仅当它被所有 $\mathcal U$ 小紧 Hausdorff 探针检验为开：对后者的 $f:K\to X$，复合 $fq$ 是 profinite 探针；若 $(fq)^{-1}(O)$ 开，由商映射性知 $f^{-1}(O)$ 开。反向是因为 profinite 空间本身紧 Hausdorff。

## $k$ 构造和探针自然变换

定义中的子集族是拓扑，因为原像保持任意并和有限交。它细于原拓扑，所以恒等 $kX\to X$ 连续且 $kX$ 仍 Hausdorff。每个原有紧 Hausdorff 探针按定义连续到 $kX$；反向由恒等映射得到。因此这些探针集合完全相同，再作一次 $k$ 使用同一探针族，故 $k(kX)=kX$。紧 Hausdorff 空间本身满足 $kK=K$，因为定义可使用 $I_K$。

称 $A$ 紧生成，若 $kA=A$。一个集合映射 $b:kX\to Z$ 连续，当且仅当所有紧 Hausdorff 探针 $f:K\to X$ 的复合 $bf$ 连续，这只是所定义终拓扑的开集判别。于是从紧生成 $A$ 出发的连续映射 $A\to X$ 唯一提升为相同底集的连续映射 $A\to kX$：对 $A$ 的每个紧探针，复合到 $X$ 后也连续到 $kX$，再用该判别。连续映射 $X\to Y$ 同样诱导 $kX\to kY$，并保持恒等和复合。

特别地，$h_{kX}=h_X$。给定 $\eta:h_X\to h_Y$，在单点上取值定义集合映射 $b:X\to Y$。对任意 $s\in S$，将自然性用于 $s:*\to S$，得到

$$\eta_S(f)(s)=b(f(s)).$$

所以 $\eta_S(f)=bf$，且每个这样的复合连续。由 profinite 与紧 Hausdorff 检测相同，$b:kX\to Y$ 连续；再利用紧生成源的提升性质，得到 $b:kX\to kY$ 连续。反过来，一个这样的 $b$ 通过后复合给出自然变换。两构造互逆，且在底集上保持恒等和复合。因此

$$\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY).\tag{2}$$

这一步只识别了映射的底集，还没有构造参数化映射记录的拓扑。

## 乘积所需的拓扑

对两个紧生成 Hausdorff 空间 $A,B$，写

$$A\times_kB=k(A\times B),$$

其中括号内为普通乘积。从紧生成 $W$ 到这个空间的连续映射恰为一对连续映射 $W\to A$、$W\to B$：先组成到普通乘积的映射，再用前面的提升性质；反向用投影。因此它是紧生成 Hausdorff 范畴的积。

任意 $X,Z$ 的 profinite 乘积探针逐坐标给出

$$h_{Z\times X}=h_Z\times h_X=h_{kZ\times kX}.$$

相同底集上的两个普通乘积具有完全相同的 profinite 探针，所以施加 $k$ 后拓扑相同：

$$k(Z\times X)=k(kZ\times kX).\tag{3}$$

没有把普通乘积自动认作紧生成乘积。

## 紧开拓扑上的指数律

令 $A,B,W$ 为紧生成 Hausdorff 空间，令

$$N=kC_{\mathrm{co}}(A,B).$$

先说明 $C_{\mathrm{co}}(A,B)$ Hausdorff：两个不同函数在某个 $a\in A$ 处取不同值；在 $B$ 中分离这两个值，再用紧单点 $\{a\}$ 所给出的两个子基开集分离函数。$k$ 细化后仍 Hausdorff。

我们将完整证明

$$C(W,N)\cong C(W\times_k A,B).\tag{4}$$

从右向左，设 $f:W\times_k A\to B$ 连续。每个切片 $a\mapsto f(w,a)$ 连续，因为 $A\to W\times_k A$ 的切片嵌入由紧生成源的提升性质连续。因此可以定义 $\widehat f(w)(a)=f(w,a)$。

为证明 $\widehat f:W\to C_{\mathrm{co}}(A,B)$ 连续，只需检测每个紧 Hausdorff 探针 $u:K\to W$。对任一紧子集 $C\subseteq A$，映射

$$K\times C\longrightarrow W\times_k A,\qquad(k,c)\longmapsto(u(k),c)$$

连续：它先连续到普通乘积，紧 Hausdorff 源再提升到 $k$ 乘积。于是 $f(u(k),c)$ 在 $K\times C$ 上连续。若在某个 $k_0$ 处整个 $\{k_0\}\times C$ 都映入开集 $O\subseteq B$，逐个 $c$ 取矩形邻域，再用 $C$ 紧性取有限子覆盖并交相应的 $K$ 邻域，便得 $k_0$ 的邻域使所有 $c\in C$ 同时映入 $O$。所以

$$\{k:\widehat f(u(k))(C)\subseteq O\}$$

开，即 $\widehat f u$ 连续到紧开拓扑。紧生成 $W$ 的检测性质给出 $\widehat f$ 连续；再由提升性质，它连续到 $N$。

从左向右，设 $g:W\to N$ 连续，定义 $\widetilde g(w,a)=g(w)(a)$。为证明它从 $W\times_kA$ 到 $B$ 连续，取任意紧 Hausdorff 探针 $v:K\to W\times A$，写其两坐标为 $u:K\to W$、$b:K\to A$。像 $C=b(K)$ 是 $A$ 中紧 Hausdorff 子空间。限制映射

$$C_{\mathrm{co}}(A,B)\longrightarrow C_{\mathrm{co}}(C,B)$$

连续，因为 $C$ 的任意紧子集在 $A$ 中仍紧，所以子基开集的原像仍为紧开子基开集。

对于紧 Hausdorff $C$，通常求值

$$C_{\mathrm{co}}(C,B)\times C\longrightarrow B$$

连续：给定 $(f,c)$ 及包含 $f(c)$ 的开集 $O$，由 $C$ 正则性可取 $c$ 的邻域 $V$，使紧闭包 $\overline V\subseteq f^{-1}(O)$；则 $[\overline V,O]\times V$ 被求值映入 $O$。因此映射

$$k\longmapsto g(u(k))(b(k))$$

是上述连续求值与 $K\to C_{\mathrm{co}}(C,B)\times C$ 的复合，连续。对所有紧探针均如此，便得 $\widetilde g:W\times_k A\to B$ 连续。

两构造在底集上就是互逆的柯里化与反柯里化，且公式与预复合和后复合相容，证明 (4) 的双射和自然性。证明只对紧像 $C$ 使用了局部紧的求值事实，没有将任意 $A$ 当作局部紧空间。

## 表示参数化映射记录

取 $A=kX$、$B=kY$，则 $N=M(X,Y)$。对于 profinite $S$，依次使用 (2)、(3)、(4) 及 $kS=S$，得到

$$\begin{aligned}
\mathcal H_{X,Y}(S)
&=\operatorname{Nat}(h_S\times h_X,h_Y)\\
&=\operatorname{Nat}(h_{S\times X},h_Y)\\
&\cong C(k(S\times X),kY)\\
&=C(S\times_k kX,kY)\\
&\cong C(S,M(X,Y)).
\end{aligned}$$

每一步的公式都只是预复合、后复合或柯里化，因此此双射在 $S$ 上自然，确实给出 $h_M\cong\mathcal H_{X,Y}$，而不只是各值集合之间任意选择的双射。

将 (4) 用于恒等 $I_M:M\to M$，得到连续求值 $M\times_k kX\to kY$。由 (2)、(3) 得到题目要求的自然变换

$$\mathrm{ev}:h_M\times h_X\to h_Y.$$

其在 $S$ 上的公式为 $(u,v)\mapsto(s\mapsto u(s)(v(s)))$，连续性由刚证明的求值和紧探针提升保证。

对任意 Hausdorff 参数 $Z$，同样得到

$$\begin{aligned}
\operatorname{Nat}(h_Z,h_M)
&\cong C(kZ,M)\\
&\cong C(kZ\times_k kX,kY)\\
&=C(k(Z\times X),kY)\\
&\cong\operatorname{Nat}(h_Z\times h_X,h_Y).
\end{aligned}$$

按底集公式，这一对应正是 $\alpha\mapsto\mathrm{ev}\circ(\alpha\times I)$。各步自然，故满足全部参数相容性。对连续 $a:X'\to X$、$b:Y\to Y'$，实现空间上的映射为

$$M(X,Y)\longrightarrow M(X',Y'),\qquad
f\longmapsto(kb)\circ f\circ(ka).$$

其连续性由 (4) 得到：其反柯里化是连续求值与 $ka,kb$ 及积映射的复合。公式保持恒等与复合，所以题目要求的 $X,Y$ 自然性也成立。

## 大小与唯一性的准确范围

底集 $C(kX,kY)$ 是 $Y^X$ 的子集，属于 $\mathcal U$；紧开拓扑和 $k$ 拓扑都是相应幂集的子集，仍属于 $\mathcal U$。所有用于检测的紧空间与 $\beta D$ 都保持在 $\mathcal U$ 中。自然变换最初在 $\mathcal V$ 中定义，而 (2) 进一步识别出本题所需的 $\mathcal U$ 小映射集合。

构造给出一个紧生成 Hausdorff 实现。题面只要求 Hausdorff 实现，所以不能额外声称原拓扑意义下所有实现都唯一同胚；同一探针记录可能来自不同 Hausdorff 拓扑。但所有实现的 $k$ 化与此 $M$ 自然同胚：它们具有自然同构的探针函子，由 (2) 及自然同构的逆得到互逆连续映射。这是完整且恰当的唯一性范围，题面并未要求更强唯一性。

空 $X$ 时函数集为单点；非空 $X$ 与空 $Y$ 时函数集为空。前面的紧开定义、探针自然性和柯里化公式均包含这些情形，空参数亦然。

## 已证明的边界例一：底集不总是 $C(X,Y)$

取不可数 $\mathcal U$ 小集合 $D$，例如 $\mathcal P(\mathbb N)$。令 $X=D\cup\{\infty\}$，所有 $D$ 的子集为开集，含 $\infty$ 的集合开当且仅当它在 $D$ 中的补集至多可数。这是 Hausdorff 拓扑：两个 $D$ 点由单点分离，$d$ 与 $\infty$ 由 $\{d\}$ 和 $X\setminus\{d\}$ 分离。它不是离散的，因为 $\{\infty\}$ 不开。

每个紧子集有限。否则它含无限多个 $D$ 点，ZFC 可选出互异序列 $d_1,d_2,\ldots$；开集

$$X\setminus\{d_1,d_2,\ldots\},\quad\{d_1\},\quad\{d_2\},\ldots$$

覆盖该紧子集，却没有有限子覆盖。故任一紧 Hausdorff 探针的像有限，且有限 Hausdorff 子空间离散。因此该探针到相同底集的离散空间 $Y=X_{\mathrm{disc}}$ 仍连续，反向由恒等 $Y\to X$ 连续得到。于是 $h_X=h_Y$，且 $kX=Y$。

底集恒等定义了 $h_X\to h_Y$ 的自然变换，然而 $X\to Y$ 并不连续。任何实现的单点值都须对应 $\mathcal H_{X,Y}(*)=\operatorname{Nat}(h_X,h_Y)$。在由自然变换单点取值所规定的函数识别下，这个集合严格包含原有的 $C(X,Y)$；因此直接取原有连续函数并用通常函数求值，不能实现全部记录。这里没有排除把某个无关的等势集合重新标记后运输全部结构。

## 已证明的边界例二：普通紧开求值未必连续

即使输入已经紧生成，也不能直接宣称普通紧开求值始终连续。取 $A=\mathbb Q$ 的通常拓扑、$B=\mathbb R$。度量空间是紧生成的：若子集 $O$ 不开，可取 $x\in O$ 及 $x_n\notin O$ 满足 $x_n\to x$；包含极限的收敛序列是紧 Hausdorff 探针，检验出 $O$ 的原像不开。现在考虑零函数与 $0\in\mathbb Q$。任一包含零函数的基本紧开邻域只约束有限个紧集 $K_i\subseteq\mathbb Q$；其并 $K$ 紧。任一 $0$ 的开邻域 $V\subseteq\mathbb Q$ 均不包含于 $K$：否则 $K$ 作为 $\mathbb R$ 中的紧闭集，将包含某个有理开区间里的全部有理数，从而包含其中的无理极限点，矛盾。故可选 $a\in V\setminus K$。

若 $K$ 非空，定义连续函数

$$g(x)=\frac{2\,d(x,K)}{d(x,K)+|x-a|}\quad(x\in\mathbb Q).$$

分母处处为正，因为 $K$ 在 $\mathbb R$ 中闭且 $a\notin K$。该函数在 $K$ 上为零、在 $a$ 处为 $2$，因此满足所给全部紧开约束。若 $K$ 为空，直接取常数 $2$。所以任何这样的乘积邻域均有一点评值在 $(-1,1)$ 外，证明

$$C_{\mathrm{co}}(\mathbb Q,\mathbb R)\times\mathbb Q\to\mathbb R$$

在 $(0,0)$ 处不连续。参考证明采用的是 $k$ 函数空间与 $k$ 乘积，不曾声称这个普通求值连续。

## 最小完成与替代路线

完整答案须给出合法 Hausdorff 实现的底集及拓扑，证明对所有 profinite 参数的自然表示，并证明所给求值产生所有 Hausdorff 参数上的指数对应。可用紧生成 Hausdorff 范畴的笛卡尔闭性与探针全忠实性压缩论证，但须明确处理原输入到该范畴的转换、乘积与函数空间拓扑、固定宇宙和自然性。不存在规定的最低篇幅。

也可用连续收敛、由紧参数族定义的映射空间或其他等价构造，只要最终得到题目要求的 Hausdorff 空间及自然对应。仅重述单点探针恢复底集映射，或仅构造 $kX$，都尚未证明参数化映射记录可由一个空间实现。两个边界例只供核对更强声称，非最低必答内容。

## 公开来源与验证状态

profinite 探针、紧生成化及全忠实性背景参见 [Scholze, Lectures on Condensed Mathematics, Lecture I](https://www.math.uni-bonn.de/people/scholze/Condensed.pdf)。映射空间与紧生成指数律参见 [Charles Rezk, Compactly Generated Spaces, Section 8](https://www.rezk.web.illinois.edu/cg-spaces-better.pdf)。这里对 Hausdorff 情形直接给出完整紧开证明与固定宇宙核查，未使用未公开 OET 材料。

作者数学自查完成；独立 AI 复核与人工审定由外部记录分别登记。改版没有 Lean 文件、没有候选模型试跑；旧版仅重构原空间拓扑的审核记录不覆盖本次指数对象目标。
