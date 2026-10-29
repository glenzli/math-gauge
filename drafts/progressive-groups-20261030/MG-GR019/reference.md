# 超滤子代数、有限观测商与连通纤维：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 已知拓扑的有限观察商

判定：construction。

e 连续，像紧，环境积为 Hausdorff 且开闭坐标分离点，故 P 紧 Hausdorff 全不连通。有限连续映射的各纤维开闭，故在 e 纤维上常值；因 e 是紧到 Hausdorff 的闭商映射，因子连续且唯一。纤维为所有含 x 开闭集之交 Q_x。连通分量 C_x⊂Q_x。若 Q_x 不连通，分为两非空不交紧集，取不交开邻域 V,W；由紧性有限个含 x 开闭集之交 H 满足 Q_x⊂H⊂V∪W。H∩V,H∩W 是 X 中开闭集，其中含 x 的一块应包含 Q_x，矛盾。因此 Q_x 连通，等于 C_x。

判准：实际像空间及因子连续；准分量等于分量的紧性证明。

## S2 两个空间的共同观察

判定：true。

包含 (x,y) 的连通分量恰为 C_x×C_y：投影使任何连通子集落在两分量中，反向两连通空间的积连通（固定一横截与所有交它的纵截之并即整个积）。因此 q_X×q_Y 的纤维正是 X×Y 的分量，它下降为双射 P(X×Y)→P(X)×P(Y)。下降连续，因为 q_{X×Y} 是商映射；源紧靶 Hausdorff，连续双射是同胚。任一空间空时两边均空。

判准：分量的积公式；连续双射到同胚。

## S3 连通纤维的满射

判定：true。

C 闭，f^{-1}(C) 紧。若它分成非空不交相对开闭 A,B，则 f(A),f(B) 为 C 中闭集，覆盖 C；每个纤维连通，不能同时交 A,B，故两像不交且非空，矛盾。于是每个分量的原像连通，且其像恰 C，说明该原像就是一个 X 分量。故分量集合双射；由连续 f 和商性质得到连续诱导映射，紧到 Hausdorff 的连续双射是同胚。

判准：利用闭映射分离像；分量双射及拓扑。

## S4 整体对象与全部恢复目标

判定：true。

目标成立。先从运算重建紧 Hausdorff 拓扑，再构造一个普遍的 profinite 商；该商的纤维恰为原空间的连通分量，也恰为所有有限值代数观测的共同纤维。第一阶段的关键是先在 $U(X)$ 已有的 Stone 拓扑中证明 $a$ 的核关系闭，再构造 $X$ 的商拓扑；在闭核步骤中不预先赋予 $X$ 任何拓扑。



## 已有的超滤子空间

对任意集合 $X$，在 $U(X)$ 上取开闭基

$$[A]=\{\mathcal F:A\in\mathcal F\}\qquad(A\subseteq X).$$

这是紧、Hausdorff、全不连通空间。主超滤子映射 $\delta:X\to U(X)$ 的像稠密，而且每个 $\mathfrak W\in U(U(X))$ 在这个 Stone 空间中的唯一极限就是 $m_X(\mathfrak W)$。后一个结论可直接由开闭基验证：$\mathfrak W$ 收敛于 $\mathcal F$，当且仅当对所有 $A\in\mathcal F$ 都有 $[A]\in\mathfrak W$；这恰为 $\mathcal F=m_X(\mathfrak W)$。所有这些结论只涉及集合 $X$ 及 $U(X)$ 的 Stone 拓扑。

还使用标准超滤子判别：子集闭，当且仅当它包含所有以该子集为成员的收敛超滤子的极限；连续映射保持超滤子收敛，且这也刻画连续性。上述背景在固定 Mathlib 中已由实际超滤子和实际拓扑证明。



## 代数律给出闭核

在 $K=U(X)$ 中令

$$E=\{(\mathcal F,\mathcal G)\in K^2:a(\mathcal F)=a(\mathcal G)\}.$$

取 $K^2$ 上的超滤子 $\mathfrak H$，假设 $E\in\mathfrak H$，并且 $\mathfrak H$ 收敛于 $(\mathcal F,\mathcal G)$。记两坐标推前为 $\mathfrak H_1,\mathfrak H_2\in U(K)$。由投影连续及 Stone 收敛公式，

$$\mathcal F=m_X(\mathfrak H_1),\qquad
\mathcal G=m_X(\mathfrak H_2).$$

在 $E$ 上两个函数 $a\pi_1$ 和 $a\pi_2$ 相等，所以它们的超滤子推前相等：

$$U(a)(\mathfrak H_1)=U(a)(\mathfrak H_2).$$

题设的结合律因此给出

$$a(\mathcal F)
=a(U(a)(\mathfrak H_1))
=a(U(a)(\mathfrak H_2))
=a(\mathcal G).$$

由闭集的超滤子判别，$E$ 闭。这一步的所有收敛都发生在 $K$ 或 $K^2$；没有使用尚未构造的 $X$ 拓扑。



## 闭核紧商的 Hausdorff 性

先证明一般事实。设 $K$ 紧 Hausdorff，$q:K\to Y$ 为集合满射，核关系

$$E_q=\{(k,l):q(k)=q(l)\}$$

在 $K^2$ 中闭。给 $Y$ 赋商拓扑。它紧，因为 $q$ 连续满射。

对闭集 $F\subseteq K$，其饱和集为

$$q^{-1}(q(F))=\pi_2\bigl((F\times K)\cap E_q\bigr).$$

右侧是紧集在连续投影下的像，因 $K$ Hausdorff 而闭。商拓扑的闭集判别因此说明 $q(F)$ 闭，即 $q$ 是闭映射。

每个纤维 $q^{-1}(y)$ 闭，因为可选 $k$ 满足 $q(k)=y$，再沿 $l\mapsto(l,k)$ 拉回闭关系 $E_q$。不同点 $y,z$ 的纤维是互不相交的紧集，所以可取互不相交的开邻域 $V,W\subseteq K$ 分别包含这两个纤维。定义

$$V'=Y\setminus q(K\setminus V),\qquad
W'=Y\setminus q(K\setminus W).$$

因为 $q$ 闭，$V',W'$ 开；它们分别包含 $y,z$。若某点同时在二者中，满射性给出其一个原像，而该原像必须同时在 $V,W$ 中，矛盾。因此 $Y$ Hausdorff。

回到本题，单位律说明 $a$ 满射。把一般事实应用于 $q=a:K\to X$ 和刚证明的闭核，得到 $X$ 上的紧 Hausdorff 拓扑

$$\tau_a:\quad O\text{ 开}\quad\Longleftrightarrow\quad a^{-1}(O)\text{ 在 }K\text{ 中开}.\tag{1}$$

这就是所需的实际构造。



## 指定运算就是全部超滤子极限

在已构造的紧 Hausdorff 空间 $(X,\tau_a)$ 中，任意集合映射 $X\to(X,\tau_a)$ 都有从 Stone 空间 $U(X)$ 出发的唯一连续延拓。把它用于底集恒等映射，得到连续映射 $\lambda:U(X)\to X$，其值 $\lambda(\mathcal F)$ 是 $\mathcal F$ 在 $(X,\tau_a)$ 中的唯一极限。

按商拓扑，$a:U(X)\to(X,\tau_a)$ 连续；按单位律，$a$ 和 $\lambda$ 在稠密的全部主超滤子上都等于恒等底集映射。目标 Hausdorff，因此 $a=\lambda$。于是对每个 $\mathcal F$ 与 $x$，

$$\mathcal F\longrightarrow x\quad\Longleftrightarrow\quad a(\mathcal F)=x.\tag{2}$$



## 唯一性与反向构造

拓扑由其收敛超滤子确定：$C\subseteq X$ 闭，当且仅当任意 $C\in\mathcal F$ 以及 $\mathcal F\to x$ 都蕴含 $x\in C$。因此若另一拓扑也满足式 (2)，它与 $\tau_a$ 有完全相同的闭集，故二者严格相等。

反之，给定紧 Hausdorff 拓扑，令 $a(\mathcal F)$ 是其唯一极限。主超滤子的极限为原点，单位律成立。该 $a$ 是 Stone 空间 $U(X)$ 到 $X$ 的连续延拓。对任意 $\mathfrak W\in U(U(X))$，它在 Stone 空间中收敛于 $m_X(\mathfrak W)$；连续性使 $U(a)(\mathfrak W)$ 在 $X$ 中收敛于 $a(m_X(\mathfrak W))$。按 $a$ 的定义，它的唯一极限同时是 $a(U(a)(\mathfrak W))$，故结合律成立。

从拓扑构造该运算再按式 (1) 重建，由唯一性得到原拓扑；从输入运算构造拓扑再取极限运算，由式 (2) 得到原运算。这建立了双向对应。



## 全部映射的识别

若 $f:(X,\tau_a)\to(Y,\tau_b)$ 连续，任意 $\mathcal F$ 收敛于 $a(\mathcal F)$，所以 $U(f)(\mathcal F)$ 收敛于 $f(a(\mathcal F))$。结合式 (2)，得到

$$f(a(\mathcal F))=b(U(f)(\mathcal F)).$$

反之若此等式对所有超滤子成立，$\mathcal F\to x$ 蕴含 $a(\mathcal F)=x$，进而

$$b(U(f)(\mathcal F))=f(x).$$

所以 $U(f)(\mathcal F)\to f(x)$。由连续性的超滤子判别，$f$ 连续。这同时覆盖所有底集映射，并没有先要求它连续。恒等与复合在两种描述中都是相同的底集映射，故得到相应范畴的同构。

空集合也包含在证明中：其超滤子集合为空，运算唯一，拓扑唯一且紧 Hausdorff；闭核商和映射判别无须非空假设。




## 普遍的 profinite 商

以下都使用已经重建并证明紧 Hausdorff 的拓扑 $\tau_a$。记 $C_x$ 为包含 $x$ 的连通分量。首先核实紧 Hausdorff 情形中的关键等式

$$C_x=\bigcap\{V\subseteq X:V\text{ 开闭且 }x\in V\}.\tag{3}$$

左侧包含于右侧，因为一个连通集不能同时交一个开闭集及其补集。为证反向，令右侧为 $Q_x$，它是包含 $x$ 的紧闭集。若 $Q_x$ 不连通，可将它分成两个不交的非空紧集；紧 Hausdorff 分离性给出分别包含它们的不交开集 $V,W$，且 $Q_x\subseteq V\cup W$。由紧性，有限多个含 $x$ 的开闭邻域的交 $H$ 已满足 $Q_x\subseteq H\subseteq V\cup W$：否则这些邻域与闭集 $X\setminus(V\cup W)$ 有有限交性质，矛盾。$H\cap V$ 与 $H\cap W$ 都是 $X$ 中的开闭集，其中一个含 $x$，故按 $Q_x$ 的定义，它应包含整个 $Q_x$，与另一块非空矛盾。因此 $Q_x$ 连通，必包含于 $C_x$，得式 (3)。

令

$$P=\pi_0(X)=X/(x\sim y\iff C_x=C_y),$$

赋商拓扑，$q:X\to P$ 为商映射。它连续、满射，故 $P$ 紧。任意开闭 $V\subseteq X$ 都是连通分量的并，因此 $q^{-1}(q(V))=V$，$q(V)$ 及其补集在 $P$ 中都开。对不同的分量，式 (3) 给出一个包含其中一点、避开另一点的开闭集；它的饱和性使对应的两个分量被 $P$ 中的开闭集分离。故 $P$ Hausdorff，而且任何包含两个不同点的子集都不连通；$P$ 全不连通，因而是 profinite。

若 $Z$ 为 profinite 空间，连续 $f:X\to Z$ 把每个 $C_x$ 送到连通子集；全不连通性迫使该像为单点。于是存在唯一集合映射 $\bar f:P\to Z$ 使 $\bar f q=f$。商拓扑又保证 $\bar f$ 连续。反向任意连续 $\bar f$ 可与 $q$ 复合，所以这正是题目所要求的全部 profinite 目标上的双射。这里的 $P$ 和 $q$ 已经实际构造，未把这一泛性质放进输入字段。

按构造，$q^{-1}(q(x))=C_x$。下面进一步用题目给出的原始运算识别同一关系。



## 有限代数观测的精确纤维和忠实性

有限集合 $A$ 上每个超滤子都主于唯一的点，因此 $b_A$ 良定义。给 $A$ 赋离散拓扑，它紧 Hausdorff，而 $b_A$ 恰为其超滤子极限运算。第一阶段的全部映射识别给出

$$f\circ a=b_A\circ U(f)
\quad\Longleftrightarrow\quad
f:(X,\tau_a)\to A_{\mathrm{disc}}\text{ 连续}.\tag{4}$$

因此每个有限值代数观测都唯一地连续因子化于 $q$，并在每个 $C_x$ 上常值。反之，若 $x,y$ 属于不同分量，式 (3) 给出开闭集 $V$，使 $x\in V$、$y\notin V$。其二值特征函数连续，由式 (4) 正是一个有限值代数观测，而且区分 $x,y$。于是对全部 $x,y$，

$$\begin{aligned}
q(x)=q(y)
&\Longleftrightarrow C_x=C_y\\
&\Longleftrightarrow
f(x)=f(y)\quad\text{对每个有限值代数观测 }f.
\end{aligned}\tag{5}$$

这不是仅仅单向的“有限观测在分量上常值”。反方向确实使用了紧 Hausdorff 情形的分量—开闭邻域交等式。

因而，$q$ 为单射，当且仅当对任意 $x\ne y$，存在有限集合 $A$ 及满足原代数等式的 $f:X\to A$，使 $f(x)\ne f(y)$。这是完全以 $a$ 和有限集合表述的充要判据。结合其纤维为连通分量，也可等价表述为 $(X,\tau_a)$ 全不连通。无需预先假定此性质；一般的输入运算会产生具有非单点连通分量的紧 Hausdorff 空间。

形式化采用有限序数 $\mathrm{Fin}(n)$ 作为区分点的测试骨架，并同时证明任意宇宙中的有限测试在这些纤维上常值且唯一因子化。任意有限集合同构于某个有限序数；有限离散双射及其逆连续，按式 (4) 都保持相应的有限代数，因此这和题面的全部有限集合观测完全等价。

判准：Starting only from the supplied set and two algebra equations, construct an actual topology and prove it is compact and Hausdorff.；Prove the exact ultrafilter convergence specification and uniqueness of the topology.；Construct the reverse operation from every compact Hausdorff topology and verify both algebra equations and both object round trips.；Prove that all algebra-compatible set maps are exactly all continuous maps for the constructed topologies, with the same identities and compositions.；Construct an actual profinite P and continuous surjection q from the reconstructed X such that every continuous map into every profinite target factors uniquely through q.；Identify the exact fibres of q and prove the necessary-and-sufficient injectivity criterion in terms of the original algebra operation and finite algebra observations; verify the full finite-observation kernel, not only one containment.。

## S5 代数侧的乘积构造

判定：construction。

主超滤子推前仍主，故单位律逐坐标成立。超滤子乘法对任意 h 自然：A∈U(h)m(W) 等价于 {F:h^{-1}A∈F}∈W，也等价于 A∈m(U(Uh)W)。用此式与 a,b 各自结合律，可逐坐标得 c m=c Uc，因为 π_X c=a Uπ_X，另一坐标同理。乘积紧 Hausdorff，F 在乘积中的唯一极限由两坐标极限组成，正是 c(F)，所以 S4 唯一性识别拓扑。有限观察商由 S2 为 P(X)×P(Y)，商映射是 q_X×q_Y。

判准：乘法自然性的成员公式；代数律及拓扑唯一性；观察商。

## S6 观察商同构的逆向

判定：false。

否。取 X=Y=[0,1]，f(x)=(2x−1)²，连续且满射。两空间连通，按 S1 它们的 P 都是单点，故诱导映射为同胚。但 f^{-1}(1)={0,1} 不连通。按 S4 连续映射也保持超滤子代数，因此该反例同样适用于代数描述；有限观察商只记录分量，不恢复每一映射的纤维。

判准：完整纤维反例；正确识别两观察商。
