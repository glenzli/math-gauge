# 塔记录的表示、有限层延拓与自然变换：参考与逐阶段验收

版本0.1.0；独立扩展草案。作者数学自查完成，人工待审；未运行模型，未做新增Lean验证。每阶段mandatory；总分100仅作诊断，严格pass须全部阶段通过。有效替代论证同样接受；依赖错误按根因和受影响节点记录，不把同一根因当多份独立样本。

## S1　实际记录与张量

在共同后继层相等的关系是等价关系：传递性把两个相等见证继续移到其层号的较大者。加法的定义不依赖共同层与代表，因为有限多个见证仍可移至同一后继层。后复合与这些相等和加法相容，所以原记录确实组成函子。

对任意有限秩自由群 $L$，映射

$$L^*\otimes A\longrightarrow\operatorname{Hom}(L,A),\qquad
\lambda\otimes a\longmapsto (x\mapsto\lambda(x)a)$$

为自然同构。选基 $e_1,\ldots,e_d$ 后，其逆把 $u$ 送到 $\sum_i e_i^*\otimes u(e_i)$；这验证了双射，正向公式本身不依赖基。对 $\rho_{n,m}$ 预复合恰对应 $\alpha_{n,m}\otimes I_A$。

再证

$$\varinjlim_n(Q_n\otimes A)\cong(\varinjlim_nQ_n)\otimes A.$$

从左到右的映射由各结构映射诱导。反向把纯张量 $[n,x]\otimes a$ 送到 $[n,x\otimes a]$；最终相等保证定义不依赖代表，把有限个层移到共同层即可验证双线性。两映射在纯张量上互逆，因而在全群上互逆。与前一个同构组合便得到 $F_{\mathbf P}\cong M_{\mathbf P}\otimes-$。

每个 $Q_n$ 可数，所以 $M_{\mathbf P}$ 是可数并的商，仍可数。若非零整数 $k$ 满足 $k[n,x]=0$，则存在 $m\ge n$ 使 $k\alpha_{n,m}x=0$。由于 $Q_m$ 无挠，$\alpha_{n,m}x=0$，故 $[n,x]=0$。这证明 $M_{\mathbf P}$ 无挠；没有假设 $Q_n\to M_{\mathbf P}$ 单射。

验收：记录运算良定；张量识别双向公式；无挠性不借结构映射单射。

关键错误：把滤过余极限直接视为子群并。

## S2　有限图表和变换

由张量模型，把自然变换写成 $\eta:M\otimes-\to N\otimes-$。在 $\mathbb Z$ 上取值得到群同态 $f:M\to N$。对每个 $a\in A$，令 $\lambda_a:\mathbb Z\to A$ 由 $1\mapsto a$ 定义。自然性给出

$$\eta_A(m\otimes a)
=(N\otimes\lambda_a)\eta_{\mathbb Z}(m)
=f(m)\otimes a.$$

纯张量生成整个张量积，而分量是群同态，所以 $\eta=f\otimes I$。反之任意群同态 $f$ 都由此定义自然变换。恒等及复合分别变为 $I_M\otimes I$ 和 $(g f)\otimes I$。自然同构对应群同构，因为其逆也由同一论证识别。

在可表示的情形，这与协变 Yoneda 的方向一致：$\operatorname{Nat}(\operatorname{Hom}(P,-),\operatorname{Hom}(P',-))\cong\operatorname{Hom}(P',P)$，通过有限自由对偶转换成 $\operatorname{Hom}(P^*,P'^*)$。

所有题设塔都保持有限极限，即使上述分类条件不成立。有限积的记录可以把有限多个代表搬到共同层；若各坐标最终相等，再把有限多个相等见证搬到共同层便得单射性。等化子的满射性来自：$[n,fu]=[n,gu]$ 意味着某个后继层上 $fu\rho_{n,m}=gu\rho_{n,m}$，在那里 $u\rho_{n,m}$ 分解经过等化子；单射性由等化子包含映射单射得到。终对象的记录为零。有限极限由有限积和等化子构成。

验收：有限积与等化子比较为同构；Nat=Hom(M_P,M_P′)正确方向；恒等复合。

关键错误：纯张量上的等式不利用分量加法；有限极限自动可表示。

## S3　完整表示分类

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

验收：M有限生成/有限自由充要判据；可数极限保持两个方向；表示对象唯一同构类；变换分类一致。

关键错误：只给一个不可表示例；无限族分别后移当共同层；把M⊗−写成Hom(M,−)。

## S4　秩一塔

秩恒1不保证可表示，a_n=2恒定时M=Z[1/2]非有限生成。完整分类如下：若a_n=0有无限多个，则任一有限层元素在某后层被杀死，M=0，F是零函子，由零群表示。若零仅有限多个，有零时取N超过最后一个零，无零时取N=0；忽略有限前缀不改余极限；尾部a_n非零。将第N层Z嵌为Z，并把后续第m层嵌为(1/D_m)Z⊂Q，D_m=∏_{j=N}^{m−1}a_j；这些嵌入与乘a_j过渡相容，M为这些子群的递增并。若只有有限多个|a_n|>1，尾部子群最终不变，M≅Z。反之任何有限生成子群的生成元都落在某(1/D_m)Z，取其后一个非单位a_j，新增1/D_{j+1}不在该子群，故M不有限生成。按S3，可表示恰当“零无限多，或在最后一个零之后非单位有限多”；后一情形等价于最终a_n∈{±1}。表示对象分别0或Z。

验收：否定仅秩条件；零无限多和有限多全部分支；非单位无限多非有限生成。

关键错误：忽略零过渡；有限秩误作有限生成。

## S5　稳定像中的延拓

每层直和项断言为假：P_n=Z，ρ₀=×2，n≥1时ρ_n=id，可取n₀=0；I₀=2Z，I_n=Z(n≥1)，限制过渡均为同构，但Z→2Z不存在回缩，否则r(2)=2r(1)=2强迫r(1)=1不在2Z。正确构造是选m≥n₀使imρ_n₀,m=I_n₀。限制J=ρ_n₀,m|I_m:I_m→I_n₀为同构，故r=J⁻¹ρ_n₀,m:P_m→I_m是回缩。对记录(n,u)，先后移至n≥n₀，再将u|I_n通过I_n₀≅I_n变为I_n₀→A；过渡同构保证选择无关。若它为0，取r≥n使imρ_n,r=I_n，得uρ_n,r=0，所以记录为0。任给f:I_n₀→A，在刚选m层用u=fρ_n₀,m:P_m→A，其限制通过J给f，故满射。公式对A自然且加法保持，给所需表示。不能把必要性证明中某层的分裂拿来循环证明这一充分性方向。

验收：固定层反例；正确后移层回缩；实际记录同构双射和自然性。

关键错误：对2Z⊂Z选不存在回缩；把足够后层换成任意当前层。

## S6　具体变换与无限积

由S1 M=Z[1/2]，S2使自同态对应Hom_Z(M,M)。同态由r=f(1)唯一确定，因为2^n f(2⁻ⁿ)=r，目标无2挠且r/2^n∈M，所以f为乘r；任意r∈M都成立。自同构是单位乘法，r=±2^k(k∈Z)：若r=a/2^n约成奇数分子a，逆在M中恰当|a|=1。考虑序列m_j=2⁻ʲ∈M^N。张量元素是有限和Σ_l r_l⊗z_l，坐标全部位于有限多个r_l生成的子群；该群包含于某2⁻ᴺZ，不能包含全部m_j。故该序列无原像。有限图表仅需把有限多个代表后移到共同层，S2仍有效；可数积需要无界分母的统一控制而失败。

验收：End环和Aut群完整计算；具体积元素无原像；有限与可数差异。

关键错误：将各坐标层号当共同有限层；自同构误作所有非零有理数。
