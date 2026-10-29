# 参考论证：逐层记录的承载与相容性分类

本题的终点是完整分类。单个不可表示塔只能给出一个例子，不能完成当前题面。以下论证不预设过渡单射、满射、秩有界或最终为同构。

## 主定理

记

$$Q_n=P_n^*=\operatorname{Hom}_{\mathbb Z}(P_n,\mathbb Z),\qquad
\alpha_{n,m}=\rho_{n,m}^*:Q_n\longrightarrow Q_m,\qquad
M_{\mathbf P}=\varinjlim_n Q_n.$$

则 $M_{\mathbf P}$ 是可数无挠阿贝尔群，且存在自然同构

$$F_{\mathbf P}(A)\cong M_{\mathbf P}\otimes_{\mathbb Z}A.$$

下列条件等价：

1. $F_{\mathbf P}$ 可由一个普通阿贝尔群表示。
2. $F_{\mathbf P}$ 保持题面中的全部可数图表极限。
3. 典范映射 $F_{\mathbf P}(\mathbb Z^{\mathbb N})\to F_{\mathbf P}(\mathbb Z)^{\mathbb N}$ 满射。
4. $M_{\mathbf P}$ 有限生成。
5. $M_{\mathbf P}$ 为有限秩自由群。

这些条件成立时，表示对象恰为与 $M_{\mathbf P}^*$ 同构的群；函子还保持任意 $\mathcal U$ 小极限。对任意两塔 $\mathbf P,\mathbf P'$，有与恒等和复合相容的双射

$$\operatorname{Nat}_{\mathbf{Ab}}(F_{\mathbf P},F_{\mathbf P'})
\cong\operatorname{Hom}_{\mathbb Z}(M_{\mathbf P},M_{\mathbf P'}).$$

因此两记录函子自然同构当且仅当其 $M$ 群同构。这是群值函子之间的自然变换，所有分量均为群同态。

## 从塔得到张量函子

在共同后继层相等的关系是等价关系：传递性把两个相等见证继续移到其层号的较大者。加法的定义不依赖共同层与代表，因为有限多个见证仍可移至同一后继层。后复合与这些相等和加法相容，所以原记录确实组成函子。

对任意有限秩自由群 $L$，映射

$$L^*\otimes A\longrightarrow\operatorname{Hom}(L,A),\qquad
\lambda\otimes a\longmapsto (x\mapsto\lambda(x)a)$$

为自然同构。选基 $e_1,\ldots,e_d$ 后，其逆把 $u$ 送到 $\sum_i e_i^*\otimes u(e_i)$；这验证了双射，正向公式本身不依赖基。对 $\rho_{n,m}$ 预复合恰对应 $\alpha_{n,m}\otimes I_A$。

再证

$$\varinjlim_n(Q_n\otimes A)\cong(\varinjlim_nQ_n)\otimes A.$$

从左到右的映射由各结构映射诱导。反向把纯张量 $[n,x]\otimes a$ 送到 $[n,x\otimes a]$；最终相等保证定义不依赖代表，把有限个层移到共同层即可验证双线性。两映射在纯张量上互逆，因而在全群上互逆。与前一个同构组合便得到 $F_{\mathbf P}\cong M_{\mathbf P}\otimes-$。

每个 $Q_n$ 可数，所以 $M_{\mathbf P}$ 是可数并的商，仍可数。若非零整数 $k$ 满足 $k[n,x]=0$，则存在 $m\ge n$ 使 $k\alpha_{n,m}x=0$。由于 $Q_m$ 无挠，$\alpha_{n,m}x=0$，故 $[n,x]=0$。这证明 $M_{\mathbf P}$ 无挠；没有假设 $Q_n\to M_{\mathbf P}$ 单射。

## 一个可数积检测有限生成

若 $F_{\mathbf P}\cong\operatorname{Hom}(P,-)$，它保持任意小极限：一个映射 $P\to\lim_jD(j)$ 与一族对图表箭头相容的映射 $P\to D(j)$ 等价。这一对应由各投影给出，所以正是典范比较，而非无关的抽象同构。故条件 1 蕴含 2，条件 2 蕴含 3。

通过张量识别，条件 3 是

$$\theta:M\otimes\mathbb Z^{\mathbb N}\longrightarrow M^{\mathbb N},
\qquad m\otimes(a_j)_j\longmapsto(a_jm)_j$$

满射，其中 $M=M_{\mathbf P}$。把 $M$ 的全部元素列为一个序列 $(m_j)_{j\ge0}$；若 $M$ 有限，则允许重复，零群也如此。取其原像

$$\sum_{\ell=1}^{s}y_\ell\otimes(a_{\ell,j})_{j\ge0}.$$

每个坐标都给出 $m_j=\sum_{\ell=1}^{s}a_{\ell,j}y_\ell$。因此有限多个 $y_\ell$ 生成整个 $M$。这一步使用了塔可数、层有限秩所给出的 $M$ 可数性；不能对一般不可数群直接套用同一个序列。

有限生成无挠阿贝尔群是有限秩自由群。可直接由整数矩阵的 Smith 标准形得到：对有限生成群取有限个生成元的自由呈示；其关系子群是有限秩自由群，Smith 变换将商分解为有限个循环挠群与一个自由群，无挠性使所有非零循环挠项消失。这也包含零群。故 4 蕴含 5。

若 $M$ 有限秩自由，令 $P=M^*$。上面已经证明的有限自由张量—Hom 同构及自然双对偶同构 $M\cong M^{**}$ 给出

$$M\otimes A\cong\operatorname{Hom}(M^*,A).$$

故 5 蕴含 1，并同时证明任意小极限相容性。

表示对象的唯一性可用 Yoneda，也可直接证明：若 $\operatorname{Hom}(P,-)\cong\operatorname{Hom}(R,-)$，把自然同构及其逆分别作用于恒等映射，可得到 $R\to P$ 和 $P\to R$；自然性与互逆性使两个复合均为恒等。因此全部表示对象正好是 $M^*$ 的同构类，不只是构造出一个候选。

## 全部自然变换

由张量模型，把自然变换写成 $\eta:M\otimes-\to N\otimes-$。在 $\mathbb Z$ 上取值得到群同态 $f:M\to N$。对每个 $a\in A$，令 $\lambda_a:\mathbb Z\to A$ 由 $1\mapsto a$ 定义。自然性给出

$$\eta_A(m\otimes a)
=(N\otimes\lambda_a)\eta_{\mathbb Z}(m)
=f(m)\otimes a.$$

纯张量生成整个张量积，而分量是群同态，所以 $\eta=f\otimes I$。反之任意群同态 $f$ 都由此定义自然变换。恒等及复合分别变为 $I_M\otimes I$ 和 $(g f)\otimes I$。自然同构对应群同构，因为其逆也由同一论证识别。

在可表示的情形，这与协变 Yoneda 的方向一致：$\operatorname{Nat}(\operatorname{Hom}(P,-),\operatorname{Hom}(P',-))\cong\operatorname{Hom}(P',P)$，通过有限自由对偶转换成 $\operatorname{Hom}(P^*,P'^*)$。

## 等价的有限层判据

这一段是已证明的替代表述，不要求候选必须采用。它使判据完全落在原塔的有限层同态上。

上述等价条件还等价于：存在 $n$ 及幂等同态 $d:P_n\to P_n$，使对每个 $m\ge n$，存在 $u_m:P_n\to P_m$ 和 $r\ge m$，满足

$$u_m d=u_m,\qquad \rho_{n,m}u_m=d,\qquad
u_m\rho_{n,r}=\rho_{m,r}.$$

这不要求各个 $u_m$ 在所有层上严格相容。

先设 $M$ 有限秩自由。取一组基并在一个共同层 $Q_n$ 选取全部基元的代表，得到 $j:M\to Q_n$，使 $i_nj=I_M$，其中 $i_n:Q_n\to M$ 为结构映射。令 $e=ji_n$，对 $m\ge n$ 令 $\beta_m=ji_m:Q_m\to Q_n$。于是

$$e^2=e,\qquad e\beta_m=\beta_m,\qquad
\beta_m\alpha_{n,m}=e.$$

映射 $\alpha_{n,r}\beta_m$ 与 $\alpha_{m,r}$ 在余极限中相等。因为 $Q_m$ 有限生成，可对一组有限生成元的最终相等见证取共同后继层 $r\ge m$，使它们作为 $Q_m\to Q_r$ 的同态相等。对偶化，取 $d=e^*$、$u_m=\beta_m^*$，得到所列三式；有限自由双对偶在此被自然识别。

反之，令 $e=d^*$、$\beta_m=u_m^*$、$L=\operatorname{im}e\subseteq Q_n$。对偶三式给出

$$e\beta_m=\beta_m,\qquad \beta_m\alpha_{n,m}=e,\qquad
\alpha_{n,r}\beta_m=\alpha_{m,r}.$$

映射 $L\to M$ 由 $i_n$ 限制而来。任一元素可在某个 $m\ge n$ 代表为 $[m,x]$；第三式说明它等于 $[n,\beta_mx]$，第一式说明 $\beta_mx\in L$，所以该映射满射。若 $x\in L$ 在 $M$ 中为零，存在 $m\ge n$ 使 $\alpha_{n,m}x=0$，于是第二式给出 $x=ex=0$。故 $L\cong M$。由于 $L$ 是有限生成群 $Q_n$ 的幂等像，它有限生成；又无挠，所以有限秩自由。

特别地，常值 $P_n=\mathbb Z^2$、过渡为 $(a,b)\mapsto(a,0)$ 的塔满足判据且由 $\mathbb Z$ 表示，尽管没有一个过渡为同构。因此不能把“最终所有过渡均为同构”误写为必要条件。

## 有限图表与旧反例的准确位置

所有题设塔都保持有限极限，即使上述分类条件不成立。有限积的记录可以把有限多个代表搬到共同层；若各坐标最终相等，再把有限多个相等见证搬到共同层便得单射性。等化子的满射性来自：$[n,fu]=[n,gu]$ 意味着某个后继层上 $fu\rho_{n,m}=gu\rho_{n,m}$，在那里 $u\rho_{n,m}$ 分解经过等化子；单射性由等化子包含映射单射得到。终对象的记录为零。有限极限由有限积和等化子构成。

对于乘二塔 $P_n=\mathbb Z$，有 $M=\mathbb Z[1/2]$，不是有限生成群：任意有限个分数的分母都被某个 $2^N$ 控制，生成的群不含 $2^{-(N+1)}$。于是旧题中的非表示性仍然正确，但现在它只是分类定理的一个实例，不能替代本题的充要判据与自然变换分类。

## 最小完成、替代路线与边界

完整作答至少要给出非循环的塔不变量或等价塔判据，证明表示性的两个方向并构造表示对象；独立解决可数图表极限的分类及二者关系；描述所有自然变换与复合。以 $M$ 有限秩自由作为判据已经满足题目，无需额外抄写有限层判据、单一积测试或例子。

可使用适用的标准张量、可表示函子、有限呈示或 pro-范畴定理压缩证明，但必须核对可数性、有限自由性、变换方向与普通群的表示范围。有效的短证明完整接受。仅展示乘二塔、仅证明有限极限保持、或仅找到某一个可表示塔都只是部分贡献。

大小方面，所有有限自由群、可数余极限、对偶和张量构造都在 $\mathcal U$ 中；$\mathcal U$ 小图表的极限亦在其中。自然变换在 $\mathcal V$ 中形成集合。秩零、零群和空图表均被上述论证覆盖。

## 公开来源与验证状态

滤过余极限背景参见 [Stacks Project, 04AX](https://stacks.math.columbia.edu/tag/04AX)。张量与乘积的判据参见 [Stacks Project, 059H](https://stacks.math.columbia.edu/tag/059H)，可数检测参见 [Stacks Project, 0AL8, Lemma 110.12.1](https://stacks.math.columbia.edu/tag/0AL8)。这里给出独立撰写的完整论证与有限层改写，没有使用未公开 OET 材料。

作者数学自查完成；独立 AI 复核及人工审定由外部记录分别登记。本改版没有 Lean 文件，没有新增候选模型试跑。旧题的数学审核或任何旧答卷不覆盖本题的新目标。
