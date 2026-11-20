## 总体判断

这份答卷不能判定为正确、完整。S2 在题设条件下成立，S3、S4、S6 正确；S1 的主要等化子证明正确，但对“\(S_i\) 不必是 \(S\) 的开子概形”所给解释有实质错误；S5 的证明依赖一个明显为假的“稠密开限制单射性”，因而其核心同构结论没有被证明。

S5 是原题必答部分，其证明失败足以使整份答卷不能算作完整完成。

## S1：主要结论正确，辅助解释有错误

主证明是有效的。令

\[
\mathcal I=\prod_{i=1}^n\mathcal I_{x_i},\qquad
\mathbf U=(U_1,\ldots,U_n),\qquad
U_{\mathbf U}=\bigcup_iU_i.
\]

对于每个 \(\mathbf U\)，诸 \(U_i\) 构成 \(U_{\mathbf U}\) 的 Zariski 开覆盖，所以层的等化子正合列成立：

\[
0\longrightarrow G(U_{\mathbf U})\longrightarrow \prod_iG(U_i)
\rightrightarrows \prod_{i,j}G(U_i\cap U_j).
\]

过滤余极限保持有限积，阿贝尔群中的过滤余极限又保持正合性，因此取余极限确实得到题述等化子。映射 \(\mathbf U\mapsto U_{\mathbf U}\) 在含 \(\Sigma\) 的开邻域中也是余终的。这些步骤均正确。

问题出在关于“不是开子概形”的说明。答卷写出的

\[
\mathfrak q\subset\mathfrak p_j
\quad\Longrightarrow\quad
\mathfrak q\not\subset\mathfrak p_i
\]

没有依据，而且一般情况下不成立。“不是有限生成，因此不是开浸入”也没有经过证明；此外，“开浸入必须是局部有限型”并不是一个无条件成立的必要条件。

可以采用以下直接反例。令

\[
X=\mathbb A_k^2,\qquad
\mathfrak p=(x,y),\qquad
\mathfrak q=(x-1,y),
\]

并取 \(\Sigma=\{\mathfrak p,\mathfrak q\}\)。设

\[
S=\operatorname{Spec}\mathcal O_{X,\Sigma},
\qquad
S_{\mathfrak p}=\operatorname{Spec}A_{\mathfrak p}.
\]

映射 \(S_{\mathfrak p}\to S\) 的拓扑像为

\[
U_{\mathfrak p}=\{\mathfrak r\in S:\mathfrak r\subset\mathfrak p\}.
\]

若 \(U_{\mathfrak p}\) 是开集，其补集就是闭集。但这个补集含有闭点 \(\mathfrak q\)，却不含泛点 \((0)\)，尽管 \((0)\in\operatorname{cl}(\mathfrak q)\)。因此补集不可能是闭集，\(U_{\mathfrak p}\) 不是开集。

所以原答的最终判断“\(S_i\) 不必是开子概形”本身正确，但答卷提供的是一个不可靠的解释。

## S2：在题设条件下，图追逐正确

把 S1 的两点等化子写成

\[
0\longrightarrow G(S)\longrightarrow G(S_1)\oplus G(S_2)
\xrightarrow{\delta_G}G(S_1\times_SS_2).
\]

其中

\[
\delta_G(g_1,g_2)
=g_1|_{S_1\times_SS_2}-g_2|_{S_1\times_SS_2}.
\]

原答的四引理式图追逐是正确的：

1. 中间竖向映射由 \(H(S_i)\to G(S_i)\) 的已知同构组成。
2. 对 \(g\in G(S)\)，可先找唯一的 \((h_1,h_2)\) 映射到 \((g|_{S_1},g|_{S_2})\)。
3. 底行正合及交换性给出右端像为零。
4. 右端 \(H(S_1\times_SS_2)\to G(S_1\times_SS_2)\) 单射，于是
   \[
   \delta_H(h_1,h_2)=0.
   \]
5. 顶行正合给出 \(h\in H(S)\) 使 \(\alpha_H(h)=(h_1,h_2)\)。
6. 因底行左映射单射，得到 \(\eta_S(h)=g\)。

单射性也可从中间映射为同构直接得到。

原答把 \(H\) 的正合行由各收缩覆盖取余极限得到，写得略压缩，但给定题设下可以补成标准论证，并不构成主要错误。

## S3：正确

对任意含 \(\Sigma\) 的开集 \(V\)，取

\[
U=V\cap W.
\]

因为 \(U\) 含 \(\Sigma\)、包含于 \(W\)，且 \(U\subset V\)，所以所要求的开邻域族在全部开邻域中余终。

对反变预层 \(\mathcal F\)，两种余极限之间的正向映射由包含关系给出，反向映射由

\[
\mathcal F(V)\longrightarrow \mathcal F(V\cap W)
\]

及其余极限像给出。卷卒复合均为恒等，所以得到典范同构。原答的证明完整。

## S4：正确

反例

\[
X=\mathbb A_k^1,\qquad
\Sigma=\{0\},\qquad
W=D(t)=X\setminus\{0\}
\]

满足全部条件。\(W\) 是非空稠密开集，但不存在同时满足

\[
0\in U\subset W
\]

的开集 \(U\)。因此限定在 \(W\) 内的邻域族为空，不可能在非空的“全部 \(\Sigma\) 开邻域”中余终。原答结论和反例均有效。

## S5：核心证明失败

### 成立的部分

从概形态射图得到有限转移限制、单点半局部邻域等同于茎，以及“层化诱导茎同构”，这些内容正确。如果 S2 的全部条件已独立建立，最后的两点图追逐也成立。

### 致命错误：任意稠密开限制的单射性

答卷断言：若 \(F\) 是 \(\mathbb A^1\) 不变的有限转移预层，\(W\subset Y\) 稠密开，则

\[
F(Y)\longrightarrow F(W)
\]

必为单射。这一断言是假的。

取标准 Chow 群预层

\[
F(Y)=\operatorname{CH}^1(Y).
\]

它带有有限转移作用，并满足

\[
\operatorname{CH}^1(Y\times\mathbb A^1)
\cong \operatorname{CH}^1(Y).
\]

令

\[
Y=\mathbb P^1_k,\qquad
W=\mathbb P^1_k\setminus\{p\}\cong\mathbb A^1_k,
\]

其中 \(p\) 是 \(k\)-有理点。则

\[
\operatorname{CH}^1(Y)=\mathbb Z[p]\cong\mathbb Z,
\qquad
\operatorname{CH}^1(W)=0.
\]

非零类 \([p]\) 沿限制映射送到 \(0\)。因此限制远非单射。

这个例子甚至是一个 Zariski 层，所以问题不能归因于“层化使预层不分离”。

答卷从此错误断言推出：

\[
F\ \text{是 Zariski 分离预层}
\Longrightarrow
\eta_T:F(T)\to F_{\mathrm{Zar}}(T)\ \text{对所有 }T\text{ 单射}.
\]

第一步已经失效，因此 \(\eta_{S_1\times_SS_2}\) 的单射性根本没有建立。S2 的满射图追逐正依赖这个右端单射性。

### 引用和归纳均没有闭合

答卷虽然简要引用了 Voevodsky 层化及 Artin 初等纤维化等结果，但没有准确陈述所用引理，也没有说明这些一般定理如何推出题中需要的有限转移 Mayer–Vietoris 行。尤其是答卷对下列正合行

\[
0\to F(S)\to F(S')\oplus F(S_n)
\to F(S'\times_SS_n)
\]

只给出了“MVW 收缩引理”和“移动技术”的名称，没有构造有限对应、说明同伦关系，也没有核验经过 \(F\) 后的正合性。

有限归纳中把 \(n-1\) 个点合并成 \(S'\)，也不能直接套用只针对两个闭点的 S2。这一合并需要另证的半局部 Mayer–Vietoris 正合列，答卷没有建立。

因此，S5 的最终陈述即使为真，这份答卷也没有提供有效证明。上述 Chow 群例子本身不反驳最终 S5 命题，因为 \(\operatorname{CH}^1\) 已经是 Zariski 层；它反驳的是答卷用来证明该命题的关键中间断言。

## S6：两部分均正确

第一问的反例有效。取每个复形

\[
\mathbb Z\xrightarrow{\times2}\mathbb Z,
\]

且所有链过渡映射也都乘以 \(2\)。每个阶段同调为 \(\mathbb Z/2\)，而余极限复形为

\[
\mathbb Z[1/2]\xrightarrow{\times2}\mathbb Z[1/2],
\]

其微分为同构，故余极限正合。因此余极限正合确实不推出充分后阶段正合。

第二问也正确。当每个阶段的每个同调类都在某个后阶段变为零时，任何余极限同调类都可先由某阶段类代表，再在那个阶段之后变为零。故余极限同调全为零。

也可以直接使用同调与阿贝尔群过滤余极限的交换：

\[
H_n\left(\varinjlim_i C_\bullet^{(i)}\right)
\cong
\varinjlim_i H_n(C_\bullet^{(i)}).
\]

指数类追逐和直接元素追逐均无误。

## 保留、新增与修正

- 保留：S1 的主等化子证明、S2 的条件式图追逐、S3、S4、S6 的有效判断。
- 修正：S5 需要指出真正的错误是“任意稠密开限制必单射”，并用 Chow 群给出反例；S1 的辅助说明需要改正。
- 仍需完成：S5 的最终同构命题没有被原答证明。若要在原题中完成 S5，需要重新建立有限转移下的半局部 Mayer–Vietoris 正合性，或者准确援引并验证能够直接推出该结论的标准定理。本次审阅不重做整套 S5 证明。

自评：本轮已逐项核查原答的数学断言，给出了主证明正确、逻辑依赖错误以及完整性问题，并用可核查反例定位了 S5 的关键失效点。待审答卷的主体进展明显，但 S5 缺失关键论证，不能判定为完整正确；按整体完成度属于有实质进展但未完成全部实质要求。