三值测试已经强制出超滤子，因而所有截断层从 \(m=3\) 起稳定。乘积比较总是满射；题末两个全称命题依次为真、假。

以下超滤子均指不含空集的真超滤子，记其集合为 \(\operatorname{Ult}(X)\)。

先分类截断记录。若 \(X=\varnothing\)，则
\[
\operatorname{Map}(X,[0])=\{\varnothing\},
\]
不存在从它到 \([0]=\varnothing\) 的映射，所以
\[
R_m(\varnothing)=\varnothing\qquad\text{对所有 }m.
\tag{1}
\]

现在设 \(X\ne\varnothing\)。定义
\[
\mathsf S(X)=
\left\{\mathcal D\subseteq\mathcal P(X):
X\in\mathcal D,\ \varnothing\notin\mathcal D,\
\forall A\subseteq X,\ 
\text{\(A,A^c\) 恰有一个属于 }\mathcal D
\right\}.
\]
则有自然分类
\[
\boxed{
R_1(X)\cong\{*\},\qquad
R_2(X)\cong\mathsf S(X),\qquad
R_m(X)\cong\operatorname{Ult}(X)\quad(3\le m\le\infty).
}
\tag{2}
\]

具体地，二值层对应
\[
\mathcal D_r=\{A\subseteq X:r_2(\chi_A)=1\}.
\tag{3}
\]
常值映射强制 \(X\in\mathcal D_r\)、\(\varnothing\notin\mathcal D_r\)，交换 \(0,1\) 的映射强制互补选择。反过来，\(\mathcal D\in\mathsf S(X)\) 给出
\[
r_2(f)=1\iff f^{-1}(1)\in\mathcal D.
\]
因为 \([2]\) 的自映射只有恒等、交换和两个常值映射，这已经满足二值层的全部条件。\(r_1\) 和 \(r_0\) 均唯一。

若有三值层，对任意三块分割
\[
X=A\sqcup B\sqcup C,
\]
取相应的 \(f:X\to[3]\)，再用三个单点指示映射 \([3]\to[2]\)，可知 \(A,B,C\) 恰有一个属于 \(\mathcal D_r\)。因此，对不交的 \(A,B\)，
\[
A\cup B\in\mathcal D_r
\iff A\in\mathcal D_r\ \text{或}\ B\in\mathcal D_r,
\tag{4}
\]
而且右边不能同时成立。

这推出向上封闭。若 \(A,B\in\mathcal D_r\) 而 \(A\cap B\notin\mathcal D_r\)，由
\(A=(A\cap B)\sqcup(A\setminus B)\) 得 \(A\setminus B\in\mathcal D_r\)，与它和 \(B\) 不交矛盾。因此 \(\mathcal D_r\) 是滤子；互补选择又说明它是超滤子。

反过来，给定 \(\mathcal U\in\operatorname{Ult}(X)\)，每个有限分割恰有一块属于 \(\mathcal U\)，故可定义
\[
r_n^{\mathcal U}(f)
=\text{唯一满足 }f^{-1}(j)\in\mathcal U\text{ 的 }j\in[n].
\tag{5}
\]
粗化分割保留所选块，所以这满足所有自然性条件。对任何原有记录，单点指示映射 \([n]\to[2]\) 又强制其 \(r_n\) 必须由式 (5) 给出。这证明了分类及三值层以上的唯一性。

特别地，二值记录可以独立选择每对非平凡互补子集中的一侧。若 \(|X|=N\ge1\)，则
\[
|R_2(X)|=2^{\,2^{N-1}-1}.
\]

在分类 (2) 下，所有限制映射如下；表中仍假定 \(X\ne\varnothing\)。

| 参数 | 限制映射及其像 | 目标记录的纤维 |
|---|---|---|
| \(m\ge k\ge3\) | \(\operatorname{Ult}(X)\) 上的恒等映射 | 单点 |
| \(m\ge3,\ k=2\) | 把超滤子视为互补选择族；像恰为超滤子 | 是超滤子时为单点，否则为空 |
| \(m=2,\ k=1\) | 到单点的映射，满射 | \(\mathsf S(X)\) |
| \(m\ge3,\ k=1\) | 到单点的映射，满射 | \(\operatorname{Ult}(X)\) |

另有 \(q_{1,1},q_{2,2}\) 为恒等映射。表中的满射性也可由任一点产生的点值记录看出。\(X=\varnothing\) 时所有这些映射均为空映射。

对 \(h:X\to Y\)，分类下的映射统一为
\[
h_*\mathcal D=\{B\subseteq Y:h^{-1}(B)\in\mathcal D\},
\tag{6}
\]
超滤子情形也是通常的推前。点值记录对应
\[
\mathcal U_x=\{A\subseteq X:x\in A\}.
\]
直接代入定义可得
\[
\begin{aligned}
R_m(t\circ h)&=R_m(t)\circ R_m(h),&
R_m(\mathrm{id})&=\mathrm{id},\\
q_{m,k}R_m(h)&=R_k(h)q_{m,k},&
R_m(h)\eta_{m,X}&=\eta_{m,Y}h,\\
q_{k,\ell}q_{m,k}&=q_{m,\ell}.
\end{aligned}
\tag{7}
\]
所以分类、限制和点值记录均与集合映射相容；对等变映射，它们相应限制到不动记录。

现设 \(X\) 是有限 \(G\) 集合。空集情形已由式 (1) 覆盖。设 \(N=|X|\ge1\)，令
\[
H=\operatorname{im}(G\to\operatorname{Sym}(X)),\qquad p=|X^G|.
\]
这里 \(H\) 是有限群，即使 \(G\) 本身无限。

令 \(\mathcal B_X\) 为所有非平凡无序二分割
\[
\{A,A^c\},\qquad \varnothing\ne A\ne X,
\]
组成的有限集合，并令 \(t=|\mathcal B_X/H|\)。考虑条件
\[
\mathsf C_X:\qquad
\text{不存在 }g\in G,\ A\subseteq X\text{ 使 }gA=A^c.
\tag{8}
\]
它等价于：每个 \(g_X\) 至少有一个奇长度循环。事实上，沿循环交替放入 \(A,A^c\) 能够闭合，当且仅当该循环长度为偶数。

准确基数为
\[
\boxed{
|R_m(X)^G|=
\begin{cases}
1,&m=1,\\
2^t,&m=2\text{ 且 }\mathsf C_X,\\
0,&m=2\text{ 且不满足 }\mathsf C_X,\\
p,&m\ge3.
\end{cases}}
\tag{9}
\]
二值情形的证明如下。不动记录就是 \(H\)-不变的互补选择族。若某元素交换一对互补子集，就不可能作不变选择。若没有这种交换，则在每个无序二分割的 \(H\)-轨道上，选择代表分割的一侧后可以唯一传播；稳定子不交换两侧保证其良定义。每个轨道恰有两个选择，各轨道彼此独立。

若需直接从循环数据计算 \(t\)，在满足 \(\mathsf C_X\) 时，Burnside 引理给出
\[
t=\frac1{2|H|}\sum_{h\in H}2^{c(h)}-1,
\tag{10}
\]
其中 \(c(h)\) 是 \(h\) 在 \(X\) 上的循环数。确实，\(h\) 固定的子集有 \(2^{c(h)}\) 个；去掉两个平凡子集并配成互补对，即得固定非平凡二分割数。这里 Burnside 引理作用于有限群和有限集合，条件满足。

三值以上的基数来自有限集上的超滤子全部为主超滤子：有限单点分割必有一个单点被选中。因此这些层的不动记录恰为
\[
\{\eta_{m,X}(x):x\in X^G\}.
\tag{11}
\]

这些不动集合之间的限制映射也完全确定：

- 三值以上各层之间均为双射，并在式 (11) 下保持 \(x\)。
- 从三值以上到二值层的像，恰为 \(p\) 个固定点的主选择族；这些记录的纤维是单点，其余纤维为空。
- 到一值层只有一个可能的纤维：从二值层来时其大小由式 (9) 给出，从三值以上来时大小为 \(p\)。

故对有限 \(X\)，一值不动记录能完整延拓当且仅当 \(p>0\)；二值不动记录能完整延拓当且仅当它是某个 \(x\in X^G\) 的点值记录；三值以上每条记录均唯一完整延拓。

下面给出任意 \(G\) 集合的完整分类及拓扑。

将 \(R_\infty(X)\) 识别为
\[
\beta X:=\operatorname{Ult}(X).
\]
对 \(A\subseteq X\)，记
\[
\widehat A=\{\mathcal U:A\in\mathcal U\}.
\]
观察条件 \(r_n(f)=j\) 对应 \(\widehat{f^{-1}(j)}\)，而每个 \(\widehat A\) 都由二值观察产生。因此题设拓扑正是布尔代数 \(\mathcal P(X)\) 的 Stone 拓扑，\(\widehat A\) 构成开闭基。Stone 空间定理说明它紧致且 Hausdorff；这里布尔代数是集合，\(X=\varnothing\) 时得到空空间。

关键是以下事实：对任意置换 \(\sigma:X\to X\)，
\[
\boxed{\sigma_*\mathcal U=\mathcal U
\iff \operatorname{Fix}(\sigma)\in\mathcal U.}
\tag{12}
\]

证明必要性时，把非固定点分成三个集合 \(C_0,C_1,C_2\)，使
\[
C_j\cap\sigma C_j=\varnothing.
\]
这样的划分存在：逐个循环着色，偶循环及无限双向循环交替用两色，奇循环最后一点用第三色；ZFC 允许选择各循环的代表。若固定点集不属于 \(\mathcal U\)，三个颜色类中必有一个属于 \(\mathcal U\)。不变性又使其像属于 \(\mathcal U\)，与两者不交矛盾。反之，若固定点集属于 \(\mathcal U\)，则 \(A\) 与 \(\sigma^{-1}A\) 在该集合上相同，因而两者属于 \(\mathcal U\) 的条件相同。这证明式 (12)。

对有限 \(F\subseteq G\)，定义
\[
X^F=\{x:\forall g\in F,\ gx=x\},\qquad X^\varnothing=X.
\]
于是
\[
R_\infty(X)^G
=\{\mathcal U\in\operatorname{Ult}(X):
X^F\in\mathcal U\text{ 对每个有限 }F\subseteq G\}.
\tag{13}
\]
特别地，它是闭子空间
\[
R_\infty(X)^G=\bigcap_{g\in G}\widehat{X^{\{g\}}}.
\]

一个完全由作用构造的内在布尔代数为
\[
\mathcal J_G(X)
=\{A\subseteq X:\exists F\subseteq G\text{ 有限},\
A\cap X^F=\varnothing\},
\qquad
B_G(X)=\mathcal P(X)/\mathcal J_G(X).
\tag{14}
\]
\(\mathcal J_G(X)\) 是理想：向下封闭显然，而有限并可使用相应有限指标集的并。标准商布尔代数的超滤子对应给出自然同胚
\[
\boxed{R_\infty(X)^G\cong\operatorname{Ult}(B_G(X)).}
\tag{15}
\]
具体地，商上的超滤子拉回为避开 \(\mathcal J_G(X)\) 的超滤子，这恰好等价于包含所有 \(X^F\)；记录仍由式 (5) 构造。基本开闭集对应 \([A]\) 的成员条件，所以确为同胚。若理想不真，商为退化布尔代数，其超滤子空间为空，亦包含在此结论中。

超滤子扩张定理现在给出准确非空判准：
\[
\boxed{
R_\infty(X)^G\ne\varnothing
\iff
\forall F\subseteq G\text{ 有限},\quad X^F\ne\varnothing.
}
\tag{16}
\]
右边正保证这些集合构成真滤子底，因为
\(X^F\cap X^E=X^{F\cup E}\)；ZFC 下可扩张为超滤子。必要性由式 (13) 立即成立。等价地，每个有限生成子群都在 \(X\) 上有固定点。取 \(F=\varnothing\) 已排除空底集。

因此，对任意底集，有限层不动记录的完整延拓范围是：

- 一值层唯一记录存在时，它能延拓当且仅当式 (16) 成立。
- 二值不动记录能延拓当且仅当其互补选择族本身是超滤子；延拓唯一。
- 每个三值以上的不动记录都唯一延拓。

第二条的延拓仍不变，因为推前与限制相容，且 \(q_{\infty,2}\) 单射。

点值固定记录的闭包为
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}
=\widehat{X^G}
=\{\mathcal U:X^G\in\mathcal U\}
\cong\operatorname{Ult}(X^G).
}
\tag{17}
\]
右边是包含这些点值记录的闭集。反过来，若 \(X^G\in\mathcal U\)，则每个包含 \(\mathcal U\) 的基本邻域 \(\widehat A\) 都满足
\(A\cap X^G\ne\varnothing\)，故含有固定点的点值记录。这也证明了空集情形。

由此得到等式的准确判准：
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\iff
\exists F\subseteq G\text{ 有限},\quad X^F=X^G.
}
\tag{18}
\]
若存在这样的 \(F\)，式 (13) 强制每个不变超滤子包含 \(X^G\)。若不存在，则每个
\(X^F\setminus X^G\) 都非空；集合族
\[
\{X^F:F\subseteq G\text{ 有限}\}\cup\{X\setminus X^G\}
\]
有有限交性质。扩张得到的不变超滤子不包含 \(X^G\)，从而不在式 (17) 的闭包中。

对每个 \(G\) 集合都满足该闭包等式的群，恰为有限生成群。若 \(G=\langle F\rangle\)，则对所有作用都有 \(X^F=X^G\)。反之，若 \(G\) 不有限生成，令 \(\mathcal H\) 为其全部有限生成子群，并取
\[
X=\coprod_{H\in\mathcal H}G/H.
\tag{19}
\]
每个 \(H\) 都是真子群，所以没有任何全局固定点。对每个有限 \(F\subseteq G\)，分支 \(G/\langle F\rangle\) 中的单位陪集被 \(F\) 固定。因此式 (16) 成立，完整不动记录非空，而固定点值记录的闭包为空。这里 \(\mathcal H\subseteq\mathcal P(G)\)，故该构造确实是集合。

一个群和底集都可数的具体例子是
\[
G=\bigoplus_{n\in\mathbb N}\mathbb Z/2,\qquad
X=\mathbb N\times[2],
\]
作用定义为
\[
g\cdot(n,\varepsilon)=(n,\varepsilon+g(n)\pmod2).
\tag{20}
\]
每个点都被对应坐标的生成元移动，故 \(X^G=\varnothing\)。每个群元素只移动有限多个二点块，因此其固定点集余有限。

这里全部不动超滤子恰为 \(X\) 上的非主超滤子。非主超滤子包含所有余有限集，因而由式 (12) 不变；反过来，不变超滤子包含每个二点块的补集，因而包含所有余有限集，不能是主超滤子。它们存在，因为 \(\mathbb N\) 上的余有限真滤子可扩张为非主超滤子。

还可逐一参数化全部记录。每个超滤子恰选择一张片
\(\mathbb N\times\{\varepsilon\}\)，因此全部不动记录唯一对应于
\[
(\varepsilon,\mathcal V),\qquad
\varepsilon\in[2],\quad
\mathcal V\in\mathbb N^*,
\]
其中 \(\mathbb N^*\) 是 \(\mathbb N\) 上非主超滤子的 Stone 空间。对应记录为
\[
r_n(f)=\text{唯一的 }j\in[n]\text{，使 }
\{k:f(k,\varepsilon)=j\}\in\mathcal V
\qquad(n\ge1).
\tag{21}
\]
\(r_0\) 唯一。由基本开闭集直接可见，这一参数化给出同胚
\[
R_\infty(X)^G\cong[2]\times\mathbb N^*.
\tag{22}
\]

最后讨论乘积。记 \(P=\prod_{i\in I}X_i\)。投影等变，式 (7) 因而保证 \(\Pi_{(X_i)}\) 良定义。每个坐标映射满足
\[
(R_\infty(p_i))^{-1}(\widehat A)
=\widehat{p_i^{-1}(A)},
\]
限制到不动子空间后仍成立，所以各坐标连续，进而 \(\Pi_{(X_i)}\) 对目标乘积拓扑连续。

它对任意 \(G\) 和任意集合指标族总是满射。给定目标中的一族不变超滤子 \((\mathcal U_i)_{i\in I}\)，在 \(P\) 上考虑集合族
\[
\mathscr A=
\{P^F:F\subseteq G\text{ 有限}\}
\ \cup\
\{p_i^{-1}(A):i\in I,\ A\in\mathcal U_i\}.
\tag{23}
\]
其有限交可写成
\[
P^F\cap\bigcap_{i\in J}p_i^{-1}(A_i),
\qquad J\subseteq I\text{ 有限},\ A_i\in\mathcal U_i.
\]
这里
\[
P^F=\prod_iX_i^F.
\]
对 \(i\in J\)，集合 \(X_i^F\cap A_i\) 属于 \(\mathcal U_i\)，故非空；其余坐标的 \(X_i^F\) 也非空。选择公理保证这些非空集合的乘积非空。因此 \(\mathscr A\) 有有限交性质，可扩张为超滤子 \(\mathcal W\)。

它包含所有 \(P^F\)，故由式 (13) 不变；同时
\[
(p_i)_*\mathcal W\supseteq\mathcal U_i,
\]
两个超滤子的包含关系必为相等，所以它正是所求预像。

若目标为空，满射性本身是空泛成立的，且良定义性保证源也为空。若 \(I=\varnothing\)，源和目标均为单点；上述构造也适用。由此覆盖所有空集及空指标族情形。

对两个因子还有一个有用事实：任意 \(\mathcal W\in\operatorname{Ult}(X\times Y)\) 满足
\[
\mathcal W\text{ 不变}
\iff
(p_X)_*\mathcal W,\ (p_Y)_*\mathcal W\text{ 都不变}.
\tag{24}
\]
必要性来自等变投影；充分性来自
\[
\operatorname{Fix}_{X\times Y}(g)
=p_X^{-1}(\operatorname{Fix}_X(g))
\cap p_Y^{-1}(\operatorname{Fix}_Y(g))
\]
及式 (12)。

若 \(X\) 有限，目标中的第一个超滤子必为某个 \(x\in X^G\) 的主超滤子。任何预像都包含 \(\{x\}\times Y\)，所以由第二个边缘超滤子 \(\mathcal V\) 唯一确定：
\[
E\in\mathcal W
\iff
\{y:(x,y)\in E\}\in\mathcal V.
\tag{25}
\]
这确实是不变超滤子，例如由等变映射 \(y\mapsto(x,y)\) 推前即可。\(X=\varnothing\) 时源和目标均为空；\(Y\) 有限时同理。因此题末第一个全称命题为真。

对于平凡群，准确的单射判准为
\[
\boxed{
\operatorname{Ult}(X\times Y)\longrightarrow
\operatorname{Ult}(X)\times\operatorname{Ult}(Y)
\text{ 单射}
\iff X\text{ 或 }Y\text{ 有限}.
}
\tag{26}
\]
充分性刚已证明。若两者都无限，ZFC 下可选两列互异元素
\[
x_n\in X,\qquad y_n\in Y,
\]
以及 \(\mathbb N\) 上的非主超滤子 \(\mathcal V\)。令两边缘超滤子为这两列对 \(\mathcal V\) 的推前，并记
\[
D=\{(x_n,y_n):n\in\mathbb N\}.
\]
沿 \(n\mapsto(x_n,y_n)\) 推前得到的超滤子 \(\mathcal W_D\) 包含 \(D\)。

另一方面，所有边缘矩形 \(A\times B\)，连同 \((X\times Y)\setminus D\)，具有有限交性质：相应的两个指标集合均属于 \(\mathcal V\)，所以都无限，可选不相等的指标 \(n,m\)。扩张得到超滤子 \(\mathcal W_{\ne D}\)，它具有相同边缘，却包含 \(D\) 的补集。因此两者不同，比较映射不单射。

题末第二个全称命题为假。取式 (20) 的作用，并令 \(Y=X\)。在刚才的构造中取
\[
x_n=y_n=(n,0).
\]
两边缘超滤子均为 \(X\) 上的非主超滤子，故均不变。由式 (24)，构造出的两个不同超滤子
\(\mathcal W_D,\mathcal W_{\ne D}\) 也都不变，却有相同的两个边缘。而此时
\[
X^G=Y^G=\varnothing,
\]
正是所要求条件下的反例。