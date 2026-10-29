# 参考审核：局部记录的有效下降商

有效商存在，且 $Q=h_S$。所得映射是 condensed sets 中的有效满态射；这并不表示每个测试空间上的连续映射都能全局提升到 $T$。

## 大小与可表示层

全过程在题面固定的宇宙中进行。$\operatorname{Prof}_{\mathcal U}$ 的对象与箭头构成 $\mathcal V$ 中的集合，因而所用函子范畴与自然变换无须在所有大小的 profinite 空间上取真类指标。有限积、闭子空间、有限不交并仍为 $\mathcal U$ 中的 profinite 空间。特别地，$R$ 是 $T\times T$ 的闭子空间，因为它是闭对角线 $\Delta_S\subset S\times S$ 的原像。

先证 $h_K$ 是层。给定有限联合满射覆盖 $\{U_i\to U\}$ 及两两一致的连续映射 $f_i:U_i\to K$。映射

$$v:\coprod_i U_i\longrightarrow U$$

连续满射，定义域紧，值域 Hausdorff，因此是闭映射，从而是商映射。两两一致性正好说合并的 $f:\coprod_iU_i\to K$ 在 $v$ 的每个纤维上常值，所以存在唯一集合映射 $\bar f:U\to K$ 满足 $\bar f v=f$。商映射性质保证 $\bar f$ 连续。空覆盖给出 $h_K(\varnothing)$ 为单点。故 $h_K$ 满足完整的层条件。

这里连续满射从紧空间到 Hausdorff 空间为闭映射的理由是：闭子集紧，其像紧，Hausdorff 空间中的紧子集闭。满射闭映射为商映射，则由闭集的原像判别立即得到。

## 余等化泛性质与核对

令 $Q=h_S$，$q=h_p:h_T\to h_S$。对任意 condensed set $Y$，Yoneda 对应把自然变换 $h_K\to Y$ 与元素 $y\in Y(K)$ 互相对应：从 $y$ 得到 $f:U\to K\mapsto f^*y$；反向取自然变换在 $I_K$ 的值。自然性直接验证这两步互逆。

因为单个满射 $p:T\to S$ 是覆盖，层条件给出双射

$$Y(S)\xrightarrow{\sim}
\{y\in Y(T):r_1^*y=r_2^*y\text{ in }Y(R)\}.$$

经 Yoneda，这恰为

$$\operatorname{Hom}(h_S,Y)\xrightarrow{\sim}
\operatorname{Eq}\!\left(
\operatorname{Hom}(h_T,Y)\rightrightarrows\operatorname{Hom}(h_R,Y)
\right).$$

因此 $h_R\rightrightarrows h_T\to h_S$ 是所求余等化图。泛性质使任何另一个有效商与 $h_S$ 唯一同构，并与 $h_T$ 的商映射相容。

纤维积层可逐测试对象计算。对每个 $U$，

$$h_R(U)=C(U,T\times_ST)
\cong C(U,T)\times_{C(U,S)}C(U,T),$$

因为右侧的一对映射恰好给出一个到纤维积的连续映射。这个同构自然于 $U$，并保留投影，所以

$$h_R\cong h_T\times_{h_S}h_T.$$

这里逐点纤维积确为层：两个坐标分别粘合后，约束等式由目标层的局部唯一性保持。于是所给关系正是商映射的核对，而不只是被商映射消去的一部分关系。

## 任意 condensed 基底上的稳定性

给定任意 condensed set $X$ 和态射 $a:X\to h_S$，令

$$E=X\times_{h_S}h_T,\qquad
K=E\times_XE\cong X\times_{h_S}h_R.$$

要证明 $K\rightrightarrows E\to X$ 也是有效商，不能把 $X$ 默认成某个空间的可表示层。

首先证明 $q_X:E\to X$ 局部满射。对 $x\in X(U)$，元素 $a_U(x)\in h_S(U)$ 对应连续映射 $f:U\to S$。取

$$U'=U\times_ST,\qquad v:U'\to U.$$

这是 profinite 空间间的连续满射，故为覆盖。令 $t:U'\to T$ 为另一投影，则

$$e=(v^*x,t)\in E(U'),\qquad q_X(e)=v^*x.$$

再设 $b:E\to Y$ 是任意层态射，并且在 $K$ 的两投影下取值相同。对给定 $x\in X(U)$，选上述局部提升 $e$。在 $U'\times_UU'$ 上，两个限制的 $E$ 元素在 $X$ 中相同，因而组成 $K$ 的元素；故 $b(e)$ 的两个限制相同。由 $Y$ 的层条件，$b(e)$ 唯一下降成 $y\in Y(U)$。

若换用另一覆盖及提升，在两个覆盖的纤维积上，两个提升又组成 $K$ 元素，所以所得局部 $Y$ 元素相同。层的唯一性给出同一个 $y$。对任何 $V\to U$，将所用覆盖拉回到 $V$，相同论证表明 $y$ 的限制就是 $x|_V$ 所定义的元素。因此 $x\mapsto y$ 定义自然变换 $\bar b:X\to Y$，且 $\bar b q_X=b$。任何另一分解在上述覆盖上与它相同，遂由层的唯一性全局相同。

这证明余等化泛性质。$K=E\times_XE$ 已在构造中明确，因此商的有效性在每个 condensed $X\to h_S$ 下稳定。该证明同时解释局部满射为何足以作商，没有使用逐测试对象的满射性。

## 相容局部记录与逐点商的区别

对 $s\in h_S(U)$，拉回覆盖 $U\times_ST\to U$ 自动给出一个局部 $T$ 记录。反过来，若覆盖 $\{U_i\to U\}$ 上有 $t_i\in h_T(U_i)$，且在每个 $U_i\times_UU_j$ 上满足 $pt_i=pt_j$，则相应的 $S$ 值映射粘合为唯一 $s\in h_S(U)$。这描述 $Q$ 的记录：局部 $T$ 记录可以在关系 $R$ 的意义下相容，不必作为 $T$ 值映射本身相等。

在预层范畴逐测试对象取余等化，得到

$$L(U)=C(U,T)/{\sim},\qquad
t\sim t'\ \Longleftrightarrow\ pt=pt'.$$

因为 $h_R(U)$ 正好包含所有满足此等式的对，这确为等价关系商。$L(U)$ 与 $C(U,T)\to C(U,S)$ 的像自然一一对应。$L$ 的层化为 $h_S$：每个 $S$ 记录局部在这个像中，且上述粘合给出唯一延拓。$L(U)$ 本身一般不是整个 $h_S(U)$。

## 无全局提升的显式见证

令 $S=\mathbb N\cup\{\infty\}$ 为离散 $\mathbb N$ 的一点紧化：各 $n$ 孤立，$\infty$ 的邻域包含所有但有限多个自然数。它紧、Hausdorff，且单点 $\{n\}$ 与含 $\infty$ 的余有限集合均为开闭集，故是 profinite。

令 $T=\beta\mathbb N$ 为 $\mathbb N$ 上所有超滤子的空间，基本开闭集为

$$[A]=\{\mathfrak u:A\in\mathfrak u\},\qquad A\subseteq\mathbb N.$$

为核对所用结构，可把超滤子识别为布尔代数同态 $\mathcal P(\mathbb N)\to\{0,1\}$；保持 $\varnothing,\mathbb N$、交与补的等式在乘积 $\{0,1\}^{\mathcal P(\mathbb N)}$ 中定义闭子集。Tychonoff 定理给出紧性，乘积给出 Hausdorff 性与开闭基。因此 $T$ 为 profinite。其底集是 $\mathcal P(\mathcal P(\mathbb N))$ 的子集，仍属于 $\mathcal U$。ZFC 中，余有限滤子延拓成超滤子，所得超滤子不含有限集，故存在非主超滤子。

将主超滤子记作对应的 $n$，定义

$$p:T\to S,\qquad p(n)=n,\qquad p(\mathfrak u)=\infty\quad(\mathfrak u\text{ 非主}).$$

它满射。任意不含 $\infty$ 的开集 $A\subseteq\mathbb N$ 的原像是主点的并 $\bigcup_{n\in A}[\{n\}]$，为开集；含 $\infty$ 的开集补集有限，其原像的补集是有限个开闭主点，仍为开集。因此 $p$ 连续。

若有连续截面 $\sigma:S\to T$，则 $p^{-1}(n)=\{n\}$ 强迫 $\sigma(n)=n$，且 $\sigma(\infty)=\mathfrak u$ 为某个非主超滤子。在偶数集 $E$ 与奇数集 $O$ 中，恰有一个属于 $\mathfrak u$；记为 $A$。则 $[A]$ 是 $\mathfrak u$ 的开邻域，而

$$\sigma^{-1}([A])=A\cup\{\infty\}$$

的补集是另一个无限的奇偶类，故它不是 $S$ 中 $\infty$ 的邻域，矛盾。因而没有连续截面。

在测试空间 $U=S$ 上，$I_S\in h_S(S)$ 没有来自 $h_T(S)$ 的原像。这完全保留题设的 profinite 满射，却否定逐测试对象满射的加强结论。原有效商定理仍成立，因为 $I_S$ 在覆盖 $T\to S$ 后有局部提升 $I_T$。

## 来源与审核范围

站点、拓扑空间对应的层与大小边界参见 [Scholze, Lectures on Condensed Mathematics, Lecture I](https://www.math.uni-bonn.de/people/scholze/Condensed.pdf)。局部满射与核对余等化的背景参见 [The Stacks Project, tag 00WL](https://stacks.math.columbia.edu/tag/00WL)。本题使用明示的固定宇宙版本；不把所有大小的站点混在一起。本稿独立展开下降、任意基底拉回及超滤子反例。

这是原创编排的公开数学初稿；AI 作者自查，人工待审；尚未 Lean 形式化。未运行模型校准，难度与区分度尚未确认。
