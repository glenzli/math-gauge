## 1. 截断、限制映射与有限 \(G\) 集合

若 \(X=\varnothing\)，则 \(\operatorname{Map}(X,[0])\) 是单点集，无法定义从它到 \([0]\) 的 \(r_0\)。因此对每个 \(m\)，都有
\[
R_m(\varnothing)=R_m(\varnothing)^G=\varnothing.
\]
这些层之间的限制映射都是空映射。若 \(X\ne\varnothing\)，则 \(r_0\) 是唯一的空函数。

对非空 \(X\)，记 \(A^c=X\setminus A\)，并定义
\[
\mathscr D(X)=
\left\{\mathcal D\subseteq\mathcal P(X):
X\in\mathcal D,\quad
A\in\mathcal D\ \Longleftrightarrow\ A^c\notin\mathcal D
\ \text{对每个 }A\subseteq X\right\}.
\]
也就是说，每一对互补子集中恰选一个，且 \(\{\varnothing,X\}\) 这一对必须选 \(X\)。记 \(\operatorname{Ult}(X)\) 为 \(\mathcal P(X)\) 上所有真超滤子的集合。则有自然分类
\[
\boxed{
R_1(X)\cong\{*\},\qquad
R_2(X)\cong\mathscr D(X),\qquad
R_m(X)\cong\operatorname{Ult}(X)\quad(3\le m\le\infty).
}
\]

**分类的证明。** 一值测试的输出唯一。令 \(\chi_A:X\to[2]\) 在 \(A\) 上取 \(1\)，在 \(A^c\) 上取 \(0\)。对二值记录定义
\[
A\in\mathcal D_r\quad\Longleftrightarrow\quad r_2(\chi_A)=1.
\]
交换 \(0,1\) 得到互补选择条件，从 \([1]\) 到 \([2]\) 的两个映射得到常值测试的规定输出。反过来，每个二值测试都是某个 \(\chi_A\)，所以 \(\mathcal D\in\mathscr D(X)\) 唯一给出 \(r_2\)。这也满足全部相容条件，因为 \([2]\) 的自映射只有恒等、交换和两个常值映射，取值于 \([1]\) 的条件自动成立。

当 \(m\ge3\) 时，对任一允许的 \(f:X\to[n]\) 和 \(j\in[n]\)，将 \(\{j\}\) 的示性函数与 \(f\) 复合，得到
\[
f^{-1}(j)\in\mathcal D_r\quad\Longleftrightarrow\quad r_n(f)=j. \tag{1}
\]
特别地，对不交的 \(A,B\)，把 \(A,B,(A\cup B)^c\) 编为一个三值测试，允许其中有空集。三块中恰选一块，再用互补选择条件，得到
\[
A\cup B\in\mathcal D_r
\quad\Longleftrightarrow\quad
A\in\mathcal D_r\ \text{或}\ B\in\mathcal D_r .
\]
对 \(A\subseteq B\) 分解 \(B=A\sqcup(B\setminus A)\)，可知 \(\mathcal D_r\) 向上封闭。若 \(A,B\in\mathcal D_r\)，则 \(B^c\notin\mathcal D_r\)，故其子集 \(A\setminus B\) 也不在其中。分解 \(A=(A\cap B)\sqcup(A\setminus B)\)，便有 \(A\cap B\in\mathcal D_r\)。这证明 \(\mathcal D_r\) 是真滤子，互补选择条件使它成为超滤子。

反过来，超滤子在每个有限划分中恰含一块。两块同时属于它会使空集属于它，而所有块都不属于它会使所有块的补集之交属于它，该交也是空集。因此式 (1) 唯一确定每个输出。若选中了 \(f^{-1}(j)\)，则 \((a\circ f)^{-1}(a(j))\) 包含这一块，也属于超滤子，故得到所需的相容性。

**限制映射与集合映射。** 在上述分类下，对非空 \(X\)，所有 \(q_{m,k}\) 如下。

- 若 \(m=k\) 或 \(k\ge3\)，则为恒等映射，每个纤维都是单点。
- 若 \(m\ge3,\ k=2\)，则为包含映射 \(\operatorname{Ult}(X)\hookrightarrow\mathscr D(X)\)。二值记录的纤维在它是超滤子时为单点，否则为空。
- 若 \(m>1,\ k=1\)，则满射到单点，唯一纤维为整个 \(R_m(X)\)。任取 \(x\in X\) 即给出源中的点值记录。

对 \(h:X\to Y\)，在二值层和所有更高层，映射统一为
\[
h_*\mathcal D=\{B\subseteq Y:h^{-1}(B)\in\mathcal D\},
\]
因为 \(\chi_B\circ h=\chi_{h^{-1}(B)}\)。逆像保持互补、有限交和全集，所以该公式也保持超滤子。一值层上的映射由唯一性确定，空源上的映射同样唯一。逆像的复合律给出函子性，以上描述直接给出
\[
q_{m,k}R_m(h)=R_k(h)q_{m,k}.
\]
点值记录在二值及更高层对应主超滤子 \(\mathcal U_x=\{A:x\in A\}\)，故 \(R_m(h)\eta_{m,X}(x)=\eta_{m,Y}(h(x))\)，且 \(q_{m,k}\eta_{m,X}(x)=\eta_{k,X}(x)\)。

**有限 \(G\) 集合的精确计数。** 设 \(X\) 有限非空。令
\[
P_X=\{\{A,A^c\}:A\subseteq X\},\qquad t=|G\backslash P_X|.
\]
则
\[
\boxed{
\begin{aligned}
|R_1(X)^G|&=1,\\
|R_2(X)^G|&=
\begin{cases}
2^{t-1},&\text{每个 }g\in G\text{ 在 }X\text{ 上都有至少一个奇长度循环},\\
0,&\text{否则},
\end{cases}\\
|R_m(X)^G|&=|X^G|\qquad(3\le m\le\infty).
\end{aligned}}
\]

事实上，一个不动二值记录就是对 \(P_X\) 中每一对作 \(G\)-等变的选择。若有 \(gA=A^c\)，该对的两侧被交换，无法等变地选择。若没有这种交换，则在每个轨道的代表对中任选一侧，再由 \(G\) 搬运，结果与搬运元素的选取无关。含 \(\{\varnothing,X\}\) 的轨道选择已定，其余 \(t-1\) 个轨道各有两个选择。对于有限置换 \(g\)，条件 \(gA=A^c\) 等价于沿每个循环都能交替标记属于 \(A\) 和属于 \(A^c\) 的点，这恰在所有循环长度均为偶数时成立。最后，有限集上的超滤子在单点划分中选中唯一的 \(\{x\}\)，因而等于 \(\mathcal U_x\)，它不动恰当 \(x\in X^G\)。

所以在有限 \(X\) 上，三值及更高层的不动集合之间以 \(X^G\) 为标识作恒等映射，到二值层的映射是 \(x\mapsto\mathcal U_x\)，到一值层的映射是到单点的唯一映射。结合空底集情形，这也描述了所有不动集合之间的限制映射。

**有限层延拓。** 对任意非空 \(G\) 集合，三值及更高层的每条不动记录都有唯一的完整不动延拓。二值不动记录恰在它选出的 \(\mathcal D\) 是超滤子时有延拓，此时延拓唯一，且由自然性自动不动。一值记录的完整不动延拓集合就是 \(R_\infty(X)^G\)，其一般存在判准见下节的式 (3)。特别地，对有限非空 \(X\)，一值记录恰有 \(|X^G|\) 个完整不动延拓，二值层中可延拓的恰是各 \(x\in X^G\) 的点值记录。

三值这一普遍延拓界是精确的。若 \(|X|\ge3\) 且存在二值不动记录，可把其中每一对 \(\{\{x\},X\setminus\{x\}\}\) 的选择都改为 \(\{x\}\)。这些对互不相同，修改又与 \(G\) 作用相容，所得不动记录同时选中不同单点，故不能延拓。若 \(1\le |X|\le2\)，每个二值记录都由一个点给出。

## 2. 完整不动记录的空间

对有限 \(S\subseteq G\)，记
\[
F_S=\{x\in X:gx=x\text{ 对所有 }g\in S\},\qquad F_\varnothing=X.
\]
完整不动记录有如下描述，对空 \(X\) 也成立：
\[
\boxed{\quad R_\infty(X)^G
=\{\mathcal U\in\operatorname{Ult}(X):F_S\in\mathcal U
\text{ 对每个有限 }S\subseteq G\}.\quad} \tag{2}
\]

为证明它，先固定一个 \(g\)。若 \(F_{\{g\}}\in\mathcal U\)，则 \(A\) 与 \(g^{-1}A\) 在这个属于 \(\mathcal U\) 的集合上相同，所以 \(A\in\mathcal U\) 当且仅当 \(g^{-1}A\in\mathcal U\)，即 \(g_*\mathcal U=\mathcal U\)。

反过来，在 \(M=X\setminus F_{\{g\}}\) 上连接 \(x\) 与 \(gx\)，得到无环边、每个顶点至多有两个邻点的无向图。用 ZFC 将 \(M\) 良序化，依次给每个顶点选一种未被其先前邻点使用的颜色，三种颜色就够了。每个色类 \(C\) 都满足 \(C\cap gC=\varnothing\)。若 \(M\in\mathcal U\)，有限个色类中必有一个属于 \(\mathcal U\)；若同时 \(g_*\mathcal U=\mathcal U\)，则 \(gC\) 也属于它，产生矛盾。因此不动性必使 \(F_{\{g\}}\in\mathcal U\)。再取有限交即得式 (2)。

**拓扑与内在分类。** 对 \(A\subseteq X\) 写
\[
\widehat A=\{\mathcal U\in\operatorname{Ult}(X):A\in\mathcal U\}.
\]
由式 (1)，观察 \(r_n(f)=j\) 的原像就是 \(\widehat{f^{-1}(j)}\)，而每个 \(\widehat A\) 都来自一个二值观察。又有 \(\widehat A\cap\widehat B=\widehat{A\cap B}\)，且 \(\widehat A\) 的补集为 \(\widehat{A^c}\)。故这些集合构成题设拓扑的开闭基，式 (2) 将不动空间表示为闭子空间 \(\bigcap_{S\text{ 有限}}\widehat{F_S}\)。

也可以直接从作用构造一个布尔代数，其 Stone 空间就是所求空间。在 \(\mathcal P(X)\) 上规定
\[
A\sim B\quad\Longleftrightarrow\quad
A\cap F_S=B\cap F_S\ \text{对某个有限 }S\subseteq G.
\]
因 \(F_S\cap F_T=F_{S\cup T}\)，这是等价关系，且并、交、补均可传到商上。记所得布尔代数为 \(\mathcal B_X\)。它的每个真超滤子沿商映射拉回，都是包含全部 \(F_S\) 的超滤子，因为 \([F_S]=[X]\)。反之，包含全部 \(F_S\) 的超滤子对等价集合给出相同的成员判定，因而唯一降为 \(\mathcal B_X\) 的真超滤子。此双射把 \([A]\) 所定的基本开闭集对应到 \(\widehat A\cap R_\infty(X)^G\)，从而给出同胚。若商代数满足 \(0=1\)，其真超滤子空间为空。

特别地，
\[
\boxed{\quad R_\infty(X)^G\ne\varnothing
\quad\Longleftrightarrow\quad
F_S\ne\varnothing\ \text{对每个有限 }S\subseteq G.\quad} \tag{3}
\]
必要性来自真超滤子不含空集。充分性来自 \(F_S\cap F_T=F_{S\cup T}\)，所以这些集合具有有限交性质。在 ZFC 中，它们生成的真滤子可由佐恩引理延拓为超滤子。这里包括 \(S=\varnothing\)，故判准也覆盖空底集。

**不动点值记录的闭包。** 在整个 \(R_\infty(X)\) 中有
\[
\overline{\eta_{\infty,X}(X^G)}=\widehat{X^G}.
\]
若 \(X^G\in\mathcal U\)，则对 \(\mathcal U\) 的每个基本邻域 \(\widehat A\)，集合 \(A\cap X^G\) 都非空，其中任一点的点值记录就落在该邻域内。若 \(X^G\notin\mathcal U\)，则 \(\widehat{X\setminus X^G}\) 是与所有不动点值记录相离的邻域。因此
\[
\boxed{\quad
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\quad\Longleftrightarrow\quad
F_S=X^G\ \text{对某个有限 }S\subseteq G.\quad} \tag{4}
\]
若有这样的 \(S\)，式 (2) 给出等式。若没有，则每个 \(F_S\) 都与 \(X\setminus X^G\) 相交，故全部 \(F_S\) 连同 \(X\setminus X^G\) 具有有限交性质。延拓所得的超滤子是不动记录，且位于该闭包之外。

**对每个作用都满足闭包等式的群，恰为有限生成群。** 若有限 \(S\) 生成 \(G\)，则每个作用都有 \(F_S=X^G\)，因为每个点的稳定子是子群。若 \(G\) 非有限生成，取集合指标的不交并
\[
X=\coprod_{\substack{H\le G\\H\text{ 有限生成}}}G/H
\]
并在各分量上取左乘作用。每个 \(H\) 都是真子群，陪集的稳定子是 \(H\) 的共轭，故 \(X^G=\varnothing\)。但对每个有限 \(S\subseteq G\)，在 \(H=\langle S\rangle\) 的分量中，陪集 \(H\) 被 \(S\) 的所有元素固定。式 (3) 给出完整不动记录，故闭包等式失效。

**可数例及其全部不动记录。** 取
\[
G=\bigoplus_{n\in\mathbb N}\mathbb Z/2,\qquad
X=\mathbb N\times\mathbb Z/2,\qquad
g(n,b)=(n,b+g(n)).
\]
\(G\) 的元素由 \(\mathbb N\) 的有限子集标识，故 \(G,X\) 都可数。对每个点，第 \(n\) 个坐标的翻转都会移动它，故 \(X^G=\varnothing\)。另一方面，每个 \(g\) 只移动有限多个点，故其不动点集属于每个自由超滤子。由式 (2)，所有自由超滤子都是不动记录，而主超滤子均不动性失效。

具体地，每个不动记录唯一由一个 \(b\in\mathbb Z/2\) 和一个 \(\mathbb N\) 上的自由超滤子 \(\mathcal V\) 给出，公式为
\[
r_n(f)=j
\quad\Longleftrightarrow\quad
\{k\in\mathbb N:f(k,b)=j\}\in\mathcal V.
\]
这是因为 \(X\) 上的超滤子恰选中两个切片 \(\mathbb N\times\{b\}\) 之一，并由它在该切片上的限制唯一确定。自由超滤子可由余有限滤子延拓得到。两个切片各给出一个开闭分量，每个分量均同胚于 \(\mathbb N\) 上的自由超滤子空间。

## 3. 乘积比较

**对任意群和任意集合指标族，\(\Pi_{(X_i)}\) 都是连续满射。** 投影 \(p_i\) 是 \(G\)-等变的，故由函子性，\((p_i)_*\) 保持不动记录。它也连续，因为对每个 \(A\subseteq X_i\)，基本开闭集 \(\widehat A\) 的原像为 \(\widehat{p_i^{-1}(A)}\)。限制到不动子空间并使用乘积拓扑，即得所述映射的良定义与连续性。

为证满射，给定目标中的一族 \((\mathcal U_i)_{i\in I}\)。在 \(Z=\prod_iX_i\) 上考虑以下所有集合：
\[
p_i^{-1}(A)\quad(i\in I,\ A\in\mathcal U_i),\qquad
D_S=\prod_{i\in I}F_{i,S}\quad(S\subseteq G\text{ 有限}),
\]
其中 \(F_{i,S}\) 是 \(S\) 在 \(X_i\) 上的共同不动点集。\(D_S\) 正是 \(S\) 在 \(Z\) 上的共同不动点集。

这个集合族具有有限交性质。给定有限多个约束，先将所涉及的有限 \(S\) 取并为 \(T\)，无此约束时取 \(T=\varnothing\)。在每个坐标 \(i\)，将 \(F_{i,T}\) 与该坐标所有被要求的 \(A\) 取交。由式 (2)，此交属于 \(\mathcal U_i\)，因而非空。选择公理给出一个同时落在各坐标交集中的元组。于是整个族可延拓为 \(Z\) 上的超滤子 \(\mathcal W\)。它包含全部 \(D_S\)，故不动。其第 \(i\) 个投影超滤子包含 \(\mathcal U_i\)，由超滤子的极大性即等于 \(\mathcal U_i\)。

若 \(I=\varnothing\)，源和目标都是单点。若有空因子，源和目标都为空。其余目标为空的情形也由良定义性知源为空。

**对于平凡群，两因子比较映射为单射，当且仅当 \(X,Y\) 至少一个有限。** 若 \(X\) 有限非空，任何 \(X\times Y\) 上的超滤子 \(\mathcal W\) 的第一投影都是某个 \(\mathcal U_x\)。于是 \(\{x\}\times Y\in\mathcal W\)。写 \(\mathcal V=(p_Y)_*\mathcal W\)，对任何 \(E\subseteq X\times Y\) 都有
\[
E\in\mathcal W
\quad\Longleftrightarrow\quad
\{y:(x,y)\in E\}\in\mathcal V,
\]
因为 \(E\) 与右侧集合的投影逆像在 \(\{x\}\times Y\) 上相同。这就由两投影唯一确定了 \(\mathcal W\)。有限 \(Y\) 的情形由交换两因子得到，空因子情形已覆盖。

若 \(X,Y\) 都无限，在 ZFC 中可取单射 \(u:\mathbb N\to X,\ v:\mathbb N\to Y\)，再取 \(\mathbb N\) 上的自由超滤子 \(\mathcal L\)。令
\[
\mathcal U=u_*\mathcal L,\qquad
\mathcal V=v_*\mathcal L,\qquad
D=\{(u(n),v(n)):n\in\mathbb N\}.
\]
沿 \(n\mapsto(u(n),v(n))\) 推前 \(\mathcal L\)，得到一个包含 \(D\)、投影为 \(\mathcal U,\mathcal V\) 的超滤子。另一个可由全部矩形 \(A\times B\)（\(A\in\mathcal U,\ B\in\mathcal V\)）连同 \(D^c\) 延拓得到。事实上，这些矩形对有限交封闭，而 \(u^{-1}(A),v^{-1}(B)\) 均属于自由超滤子 \(\mathcal L\)，都是无限集，可从中分别取不同的 \(n,m\)。于是 \((u(n),v(m))\in(A\times B)\setminus D\)，证得有限交性质。第二个超滤子有同样的两投影，却包含 \(D^c\)，故单射性失效。

**对任意群，第一个全称命题成立，第二个不成立。** 至少一个因子有限时，刚才由两投影唯一确定 \(\mathcal W\) 的证明对底集上的所有超滤子都有效，因而对不动超滤子也有效。再用已证的满射性，即得双射。

对第二个命题，取上节的可数作用，让 \(Y=X=\mathbb N\times\mathbb Z/2\)，并在刚才的构造中取 \(u(n)=v(n)=(n,0)\)。所得两投影都是自由超滤子，故均不动。对于两个因子，**具有不动投影的每个超滤子 \(\mathcal W\) 都不动**。事实上，对每个 \(g\in G\)，两个因子中 \(g\) 的不动点集分别属于两投影超滤子，故它们的两个投影逆像之交属于 \(\mathcal W\)。这个交就是 \(g\) 在乘积上的不动点集，式 (2) 遂给出结论。因此上述分别包含 \(D\) 和 \(D^c\) 的两个超滤子都是完整不动记录，投影相同，而 \(X^G=Y^G=\varnothing\)。