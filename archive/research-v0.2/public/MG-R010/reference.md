# 参考审核：由紧全不连通探针重构空间

题设允许在同一底集上作保持所有探针的幂等重构，且重构空间间的连续映射完全对应探针函子的自然变换。重构拓扑可以严格细于原拓扑。

## 同一底集上的终拓扑

设 $X$ 的原拓扑为 $\tau_X$。在其底集上定义

$$\tau_X^\dagger=
\{V\subseteq X:\ f^{-1}(V)\text{ 在 }S\text{ 中开，}
\ \forall S\in\operatorname{Prof}_{\mathcal U},\ \forall f\in C(S,X)\}.$$

空集、全集满足条件，任意并与有限交也满足，因为每个原像运算保持这些操作。故 $\tau_X^\dagger$ 是拓扑。这是令所有原有 profinite 探针连续的最细拓扑，即这族映射的终拓扑。虽然可用一个较大集合指标列出探针，此拓扑本身是 $\mathcal P(X)$ 的子集，仍在 $\mathcal U$ 中。

每个 $\tau_X$ 开集满足定义，故 $\tau_X\subseteq\tau_X^\dagger$。于是同底集恒等映射 $\varepsilon_X:X^\dagger\to X$ 连续。原有两个点的分离邻域仍然开，所以 $X^\dagger$ 仍为 Hausdorff 空间。

每个原有 $f:S\to X$ 按定义也连续到 $X^\dagger$。反过来，任意连续 $S\to X^\dagger$ 与 $\varepsilon_X$ 复合后连续到 $X$。因此对每个 $S$，连续映射集合字面上相等：

$$C(S,X^\dagger)=C(S,X).$$

预复合也没有变化，所以 $h_{X^\dagger}=h_X$ 是函子的相等，不只存在某个非规范同构。再作重构时使用完全相同的探针族，于是

$$\tau_{X^\dagger}^\dagger=\tau_X^\dagger.$$

## 终拓扑判别与函子性

对任意拓扑空间 $Z$，一个集合映射 $b:X^\dagger\to Z$ 连续，当且仅当对每个原有探针 $f:S\to X$，复合 $bf:S\to Z$ 连续。正向是复合；反向对每个 $Z$ 的开集 $O$，所有 $f^{-1}(b^{-1}O)$ 开，故 $b^{-1}O\in\tau_X^\dagger$。

若 $b:X\to Y$ 原本连续，则对每个 $f:S\to X$，$bf:S\to Y$ 连续，由记录保持性也连续到 $Y^\dagger$。上面的判别给出同底集的连续映射

$$b^\dagger:X^\dagger\to Y^\dagger.$$

它按底集映射保留恒等与复合；$\varepsilon$ 与这些映射交换。故这是一个自然的幂等重构函子。

## 从自然变换恢复映射

单点空间 $*$ 是允许的探针，且 $h_X(*)$ 自然识别为 $X$ 的底集。给定自然变换 $\alpha:h_X\to h_Y$，定义底集映射

$$b=\alpha_*:X\to Y.$$

对任意探针 $f:S\to X$ 和点 $s\in S$，将自然性用于该点的映射 $s:*\to S$，得

$$\alpha_S(f)(s)=\alpha_*(f(s))=b(f(s)).$$

因此 $\alpha_S(f)=bf$，自然变换完全由 $b$ 决定。由于 $\alpha_S(f)\in C(S,Y)$，每个 $bf$ 都连续；记录保持性进一步使其连续到 $Y^\dagger$。终拓扑判别遂给出 $b:X^\dagger\to Y^\dagger$ 连续。

反过来，给定连续 $b:X^\dagger\to Y^\dagger$，每个 $f\in h_X(S)$ 也连续到 $X^\dagger$，于是 $bf$ 连续到 $Y^\dagger$，再到 $Y$。定义 $\alpha_S(f)=bf$，复合的结合律给出自然性。这两个构造互逆，证明

$$\operatorname{Nat}(h_X,h_Y)\cong C(X^\dagger,Y^\dagger).$$

自然变换的恒等及复合在单点取值处分别成为底集映射的恒等及复合，因此该双射与两者相容，并在 $X,Y$ 的连续映射下自然。特别地，在拓扑已满足 $X=X^\dagger$ 的满子范畴上，$X\mapsto h_X$ 为全忠实函子。空空间的情形也包含在上述单点取值与映射集合论证中。

## 与紧生成拓扑的关系及大小核查

可以把定义中的 profinite 探针换成所有 $\mathcal U$ 小的紧 Hausdorff 探针，而不改变拓扑。关键是每个这样的 $K$ 都有一个来自 $\mathcal U$ 小 profinite 空间的连续满射。

为证此点，令 $D$ 为 $K$ 的底集并赋离散拓扑，令 $\beta D$ 为 $D$ 上的超滤子空间。其基本开闭集为 $[A]=\{\mathfrak u:A\in\mathfrak u\}$。把超滤子视作布尔代数同态 $\mathcal P(D)\to\{0,1\}$，保持交、补及常元的等式定义乘积 $\{0,1\}^{\mathcal P(D)}$ 中的闭子集。Tychonoff 定理给出紧性，且该子空间 Hausdorff 并有开闭基。因此 $\beta D$ 为 profinite。它是 $\mathcal P(\mathcal P(D))$ 的子集；宇宙对幂集和子集封闭，保证 $\beta D$ 仍属于 $\mathcal U$。$D=\varnothing$ 时取空空间，以下结论直接成立。

对非空 $D$，每个超滤子 $\mathfrak u$ 在紧 Hausdorff 空间 $K$ 中有唯一极限。存在性来自闭集族 $\{\overline A:A\in\mathfrak u\}$ 的有限交性质及紧性；若交中有两个不同点，取它们的不交开邻域。每个交中的点的每个邻域都属于 $\mathfrak u$，否则该邻域的闭补集属于 $\mathfrak u$，与该点在所有闭包中矛盾；两个不交邻域不能同时属于滤子，故唯一。

把该极限记为 $q(\mathfrak u)$，得到 $q:\beta D\to K$。每个主超滤子映到其主点，故 $q$ 满射。它也连续：若开集 $O$ 包含 $q(\mathfrak u)$，紧 Hausdorff 空间的正则性给出开集 $V$ 满足

$$q(\mathfrak u)\in V\subseteq\overline V\subseteq O.$$

由超滤子收敛，$V\in\mathfrak u$；而每个 $\mathfrak v\in[V]$ 的极限位于 $\overline V\subseteq O$。所以 $[V]\subseteq q^{-1}(O)$。此证明使用的正则性可由紧性得到：对点与不含它的闭集逐点取 Hausdorff 分离邻域，利用该闭集紧性选有限子覆盖，再交点侧的有限多个邻域。连续满射 $q$ 从紧空间到 Hausdorff 空间，因而是闭商映射。

若 $V\subseteq X$ 被所有 profinite 探针检验为开，对任意连续 $f:K\to X$，复合 $fq:\beta D\to X$ 是允许探针，故

$$q^{-1}(f^{-1}V)=(fq)^{-1}V$$

开。$q$ 是商映射，故 $f^{-1}V$ 开。反向因为 profinite 空间本来就是紧 Hausdorff 空间。两种终拓扑遂相等；$X^\dagger$ 正是这个固定宇宙内的紧生成化。

进一步，若 $K=K^\dagger$ 且 $b:K\to X$ 连续，则对 $K$ 的全部探针，复合在 $X^\dagger$ 中仍连续。终拓扑判别给出唯一的同底集连续映射 $K\to X^\dagger$。故该重构是紧生成 Hausdorff 空间包含到 Hausdorff 空间的右伴随，其余单位为 $X^\dagger\to X$。这些说法始终使用固定的 $\mathcal U$，没有移除大小界后再暗中调用全忠实性。

## 原拓扑未必能恢复

取一个 $\mathcal U$ 小的不可数集合 $D$，例如 $\mathcal P(\mathbb N)$。在 $X=D\cup\{\infty\}$ 上赋 Fortissimo 拓扑：所有 $D$ 的子集都是开集；含 $\infty$ 的集合开，当且仅当它在 $D$ 中的补集至多可数。

这确为拓扑。对不同的 $d,e\in D$，用单点邻域分离；对 $d$ 和 $\infty$，用 $\{d\}$ 与 $X\setminus\{d\}$ 分离，所以 $X$ Hausdorff。由于 $D$ 不可数，$\{\infty\}$ 不开，因此 $X$ 非离散。

每个紧子集都有限。若紧子集 $L$ 无限，则 $L\cap D$ 无限，可选互异序列 $d_1,d_2,\ldots$。开集族

$$X\setminus\{d_1,d_2,\ldots\},\quad\{d_1\},\quad\{d_2\},\quad\ldots$$

覆盖 $L$ 却没有有限子覆盖，矛盾。此处选序列使用题面采用的 ZFC。

任意 profinite 探针 $f:S\to X$ 的像紧，所以是有限集合。有限 Hausdorff 子空间离散：对其中一个点与其余有限多个点分别分离并交有限个邻域，即得在子空间中的开单点。因此 $f$ 到其有限像的映射连续且局部常值，也就连续到 $X$ 的离散版本 $X_{\mathrm{disc}}$。反向由恒等映射 $X_{\mathrm{disc}}\to X$ 连续可得。故按同一底集映射，

$$h_X=h_{X_{\mathrm{disc}}}.$$

所有子集在局部常值探针下的原像都开，所以 $X^\dagger$ 是离散拓扑。原 $X$ 并非离散，探针却完全相同。等同的探针函子给出自然变换 $h_X\to h_{X_{\mathrm{disc}}}$，但其底集恒等映射 $X\to X_{\mathrm{disc}}$ 不连续；在重构后的空间之间则连续。这也明确区分题面中的目标与对任意原 Hausdorff 空间直接声称全忠实的加强目标。

## 来源与审核范围

紧生成比较、profinite 覆盖及固定大小下的全忠实性背景核对于 [Scholze, Lectures on Condensed Mathematics, Lecture I, Example 1.5 and Proposition 1.7](https://www.math.uni-bonn.de/people/scholze/Condensed.pdf)。本稿在明示的宇宙约定下直接证明终拓扑、自然变换对应、幂等性与 Fortissimo 见证，没有把原空间默认成紧生成空间。

这是原创编排的公开数学初稿；AI 作者自查，人工待审；尚未 Lean 形式化。未运行模型校准，难度与区分度尚未确认。
