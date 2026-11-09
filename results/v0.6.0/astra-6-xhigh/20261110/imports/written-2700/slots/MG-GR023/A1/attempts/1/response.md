关键截断值是 \(3\)：二值测试只给出“每对互补子集选一个”，三值测试便迫使这些选择构成超滤子。完整不动记录则恰好对应于包含每个群元素固定点集的超滤子。

以下把 \(X\) 上的超滤子集合记为 \(\operatorname{Ult}(X)\)，约定 \(\operatorname{Ult}(\varnothing)=\varnothing\)。

**1. 截断、限制映射及有限作用。**

首先，所有 \(m\) 都满足
\[
R_m(\varnothing)=\varnothing.
\]
因为 \(\operatorname{Map}(\varnothing,[0])\) 是单点集，不存在从它到 \([0]=\varnothing\) 的映射。以下分类中先设 \(X\ne\varnothing\)。

定义
\[
\mathcal C(X)=
\left\{\mathcal A\subseteq\mathcal P(X):
X\in\mathcal A,\ \varnothing\notin\mathcal A,\
\forall A\subseteq X,\ 
\text{\(A,A^c\) 中恰有一个属于 }\mathcal A
\right\}.
\]
则有自然的分类
\[
\boxed{
R_1(X)\cong\{*\},\qquad
R_2(X)\cong\mathcal C(X),\qquad
R_m(X)\cong\operatorname{Ult}(X)\quad(3\le m\le\infty).
}
\tag{1}
\]

证明如下。对于非空 \(X\)，零值测试没有输入，一值测试只有唯一可能，所以 \(R_1(X)\) 是单点集。对于 \(m\ge2\)，令
\[
\mathcal A_r=\{A\subseteq X:r_2(\mathbf1_A)=1\}.
\]
与常值映射、交换 \(0,1\) 的映射相容，分别给出
\[
X\in\mathcal A_r,\qquad \varnothing\notin\mathcal A_r,\qquad
A\in\mathcal A_r\Longleftrightarrow A^c\notin\mathcal A_r.
\]
反之，这些条件已足以核验所有大小至多为 \(2\) 的测试之间的相容性：二点集的自映射只有恒等、交换和两个常值映射。因此得到 \(R_2(X)\cong\mathcal C(X)\)。

若 \(m\ge3\)，对任意分割
\[
X=A_0\sqcup A_1\sqcup A_2
\]
允许某些块为空，使用对应的三值测试及三个指示映射 \([3]\to[2]\)，可知三个块中恰有一个属于 \(\mathcal A_r\)。令
\[
\nu(A)=\mathbf1_{\{A\in\mathcal A_r\}}.
\]
对不交的 \(A,B\)，将上述结论用于 \(A,B,(A\cup B)^c\)，得到
\[
\nu(A\cup B)=\nu(A)+\nu(B).
\]
故 \(\nu\) 是归一化的 \(\{0,1\}\) 值有限可加函数。这推出单调性；又若 \(\nu(A)=\nu(B)=1\)，则
\[
\nu(A\cap B)=\nu(A)+\nu(B)-\nu(A\cup B)=1.
\]
因此 \(\mathcal A_r\) 是超滤子。

对任意允许的 \(n\ge1\)，与指示映射 \([n]\to[2]\) 相容还表明
\[
r_n(f)=j\quad\Longleftrightarrow\quad f^{-1}(\{j\})\in\mathcal A_r.
\tag{2}
\]
所以整个记录被其超滤子唯一确定。反过来，超滤子对每个有限分割恰选一块，因而式 (2) 定义记录。若选中的块是 \(f^{-1}(\{j\})\)，它包含于
\((a\circ f)^{-1}(\{a(j)\})\)，超滤子的向上封闭性便给出所需相容性。这证明了 (1)。

于是所有遗忘映射的像和纤维如下；空底集时它们都是空集之间的唯一映射。

- \(k=1\)、\(X\ne\varnothing\) 时，\(q_{m,1}\) 的像是唯一的记录，其唯一纤维就是 (1) 所分类的整个 \(R_m(X)\)。
- \(m\ge3,\ k=2\) 时，\(q_{m,2}\) 是
  \[
  \operatorname{Ult}(X)\hookrightarrow\mathcal C(X).
  \]
  超滤子对应的纤维为单点，其他纤维为空。
- \(m\ge k\ge3\) 时，\(q_{m,k}\) 在上述分类下是恒等映射。
- \(q_{2,2}\) 当然也是恒等映射。

对集合映射 \(h:X\to Y\)，分类下的映射统一由逆像给出：
\[
h_*\mathcal A=\{B\subseteq Y:h^{-1}(B)\in\mathcal A\}.
\tag{3}
\]
它保持互补选择族，也保持超滤子；这正是题目中的 \(R_m(h)\)。点值记录对应主超滤子
\[
\mathcal U_x=\{A\subseteq X:x\in A\}.
\]
在 \(m=1\) 层，所有点值记录相同。由定义或式 (3) 立即得到
\[
R_m(h'\circ h)=R_m(h')R_m(h),\qquad R_m(\mathrm{id})=\mathrm{id},
\]
以及
\[
q_{m,k}R_m(h)=R_k(h)q_{m,k},\qquad
R_m(h)\eta_{m,X}=\eta_{m,Y}h.
\tag{4}
\]
故这些分类及限制映射都与集合映射相容。

现在设 \(X\) 是有限 \(G\) 集合。若 \(X=\varnothing\)，所有不动记录集合均为空。设 \(X\ne\varnothing\)，令
\[
H=\operatorname{im}\bigl(G\to\operatorname{Sym}(X)\bigr),\qquad
t=|X^G|,
\]
并令 \(b\) 为 \(H\) 在 \(\mathcal P(X)\) 上的轨道数。

在二值层，不动记录就是 \(H\)-不变的互补选择族。补集运算在 \(\mathcal P(X)/H\) 上诱导一个对合。这样的选择族存在，当且仅当这个对合没有不动轨道，即
\[
\boxed{\text{不存在 }h\in H,\ A\subseteq X\text{ 使 }hA=A^c.}
\tag{5}
\]
事实上，一个不动选择族在每个 \(H\)-轨道上必须取恒定选择；因此必须、也只需从每对互补轨道中选一个，其中强制选 \(\{X\}\) 而不选 \(\{\varnothing\}\)。

条件 (5) 还等价于
\[
\boxed{\text{每个 }h\in H\text{ 在 }X\text{ 上至少有一个奇数长度的循环。}}
\tag{6}
\]
因为 \(hA=A^c\) 要求成员资格沿每个循环交替，这恰好在所有循环长度均为偶数时可以实现。

因此精确基数为
\[
\begin{array}{c|c|c}
\text{层数}&\text{非空条件}&|R_m(X)^G|\\ \hline
m=1&\text{总是非空}&1\\
m=2&\text{条件 (5)，等价于 (6)}&
2^{\,b/2-1}\quad\text{条件成立时，否则为 }0\\
3\le m\le\infty&t>0&t
\end{array}
\tag{7}
\]
最后一行用了有限集上的超滤子必为主超滤子：对有限单点分割恰选一块；而 \(\mathcal U_x\) 不动当且仅当 \(x\in X^G\)。

其中 \(b\) 可以由有限群作用的 Burnside 公式明确计算：
\[
b=\frac1{|H|}\sum_{h\in H}2^{c(h)},
\tag{8}
\]
\(c(h)\) 是 \(h\) 的循环总数。适用条件成立，因为 \(H\) 和 \(\mathcal P(X)\) 都有限；被 \(h\) 固定的子集恰为其循环的并，共有 \(2^{c(h)}\) 个。

这些不动集合之间的全部限制映射为：

- 层数均至少为 \(3\) 时，都是 \(X^G\) 上的恒等映射。
- 从至少 \(3\) 层到第 \(2\) 层，是 \(x\mapsto\mathcal U_x\) 的单射；像恰为固定点处的主选择族。
- 到第 \(1\) 层的映射把整个定义域送到唯一记录；其纤维基数由 (7) 给出。
- 同层限制是恒等映射。

特别地，对有限非空 \(X\)，第 \(1\) 层记录有恰好 \(t\) 个完整不动延拓；第 \(2\) 层记录恰在它是某个固定点处的主选择族时可延拓，且延拓唯一；至少第 \(3\) 层的每个不动记录均唯一延拓。第 \(2\) 层确实不够：\(C_3\) 在三点集上的传递作用满足 (6)，有两个二值不动记录，却没有完整不动记录。

**2. 完整不动记录的内在空间。**

先证明一个关键事实。对任意置换 \(s:X\to X\) 和超滤子 \(\mathcal U\)，
\[
\boxed{s_*\mathcal U=\mathcal U
\quad\Longleftrightarrow\quad
\operatorname{Fix}(s)\in\mathcal U.}
\tag{9}
\]

若 \(\operatorname{Fix}(s)\in\mathcal U\)，则 \(A\) 与 \(s^{-1}A\) 在这个集合上相同，因而在 \(\mathcal U\) 中有相同的成员资格，证明了一个方向。

反之，\(X\setminus\operatorname{Fix}(s)\) 可以分成三个集合 \(C_0,C_1,C_2\)，使
\[
C_j\cap sC_j=\varnothing.
\tag{10}
\]
具体地，在每个非平凡的循环轨道上给相邻点着不同颜色：偶数有限循环和双向无限轨道用两色，奇数有限循环用三色。ZFC 允许选择轨道代表并同时完成这些着色。若 \(\operatorname{Fix}(s)\notin\mathcal U\)，有限分割性质迫使某个 \(C_j\in\mathcal U\)。不变性又给出 \(sC_j\in\mathcal U\)，与 (10) 矛盾。这证明了 (9)。

对有限集合 \(S\subseteq G\)，记
\[
F_S=X^{\langle S\rangle}=\bigcap_{g\in S}X^g,\qquad F_\varnothing=X.
\]
于是
\[
\boxed{
R_\infty(X)^G
\cong
\{\mathcal U\in\operatorname{Ult}(X):
F_S\in\mathcal U\text{ 对所有有限 }S\subseteq G\}.
}
\tag{11}
\]

下面给出直接从作用构造的布尔代数分类。令
\[
\mathcal I_G(X)=
\{A\subseteq X:\text{存在有限 }S\subseteq G,\ A\cap F_S=\varnothing\}.
\tag{12}
\]
这是 \(\mathcal P(X)\) 的理想：向下封闭显然，而分别避开 \(F_S,F_T\) 的两个集合之并避开 \(F_{S\cup T}\)。允许它是整个布尔代数。定义
\[
B_G(X)=\mathcal P(X)/\mathcal I_G(X).
\]
那么有典范同胚
\[
\boxed{
R_\infty(X)^G\cong\operatorname{Stone}(B_G(X)).
}
\tag{13}
\]
这里退化布尔代数 \(0=1\) 的 Stone 空间约定为空。

确实，超滤子包含所有 \(F_S\)，当且仅当它不与理想 \(\mathcal I_G(X)\) 相交；这又恰好是它能下降为商布尔代数上超滤子的条件。

为核验拓扑，写
\[
\widehat A=\{\mathcal U:A\in\mathcal U\}.
\]
在分类 (1) 下，
\[
\{r:r_n(f)=j\}=\widehat{f^{-1}(\{j\})}.
\]
反过来，每个 \(\widehat A\) 都来自二值观察。因此题设拓扑正是 \(\mathcal P(X)\) 的 Stone 拓扑，\(\widehat A\) 构成闭开基。商布尔代数的基本闭开集对应于
\[
\widehat A\cap R_\infty(X)^G,
\]
故 (13) 是同胚，而不只是集合双射。这里所用 Stone 空间定理适用于集合大小的布尔代数；所有布尔代数均由集合 \(\mathcal P(X)\) 构造。特别地，该空间是紧 Hausdorff 空间，允许为空。

由超滤子扩张定理得到精确的非空判准：
\[
\boxed{
R_\infty(X)^G\ne\varnothing
\quad\Longleftrightarrow\quad
X^H\ne\varnothing
\text{ 对每个有限生成子群 }H\le G.
}
\tag{14}
\]
必要性来自 (11)。充分性是因为
\[
F_S\cap F_T=F_{S\cup T},
\]
所以假设保证这些集合具有有限交性质，生成一个真滤子；ZFC 中的超滤子扩张定理给出延拓。该条件也覆盖 \(X=\varnothing\)：取平凡子群便知右侧不成立。

对于任意 \(A\subseteq X\)，主超滤子的闭包满足
\[
\overline{\{\mathcal U_x:x\in A\}}=\widehat A.
\tag{15}
\]
右侧是包含这些点的闭集。若 \(\mathcal U\in\widehat A\)，任一含它的基本邻域 \(\widehat B\) 都满足 \(A\cap B\in\mathcal U\)，故 \(A\cap B\ne\varnothing\)，邻域中存在某个 \(\mathcal U_x\)，证明反向包含。

所以题目要求的闭包为
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}
=\widehat{X^G}
=\{\mathcal U:X^G\in\mathcal U\}.
}
\tag{16}
\]
并且
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\quad\Longleftrightarrow\quad
\exists\text{有限 }S\subseteq G,\quad X^{\langle S\rangle}=X^G.
}
\tag{17}
\]
若这样的 \(S\) 存在，结论直接来自 (11)。若不存在，则每个
\(F_S\setminus X^G\) 都非空；这些集合有有限交性质，故可扩张为超滤子。所得超滤子不动，却包含 \(X\setminus X^G\)，不属于 (16)，矛盾。这也处理了不动记录空间为空的情形。

因此，对每个 \(G\) 集合都满足该闭包等式的群，恰好是
\[
\boxed{\text{有限生成群。}}
\tag{18}
\]
有限生成时，在 (17) 中取一组有限生成元即可。

反之，若 \(G\) 非有限生成，取
\[
X=\coprod_{\substack{H\le G\\H\text{ 有限生成}}}G/H
\]
并赋予左乘作用。这是集合大小的作用，因为所有子群组成 \(\mathcal P(G)\) 的子集。每个这样的 \(H\) 都是真子群，故所有分量均无 \(G\)-不动点。然而，每个有限生成子群 \(K\) 都固定 \(G/K\) 分量中的陪集 \(K\)。由 (14)，完整不动记录非空，闭包等式失败。

一个更具体的可数例子是
\[
G=\bigoplus_{n\in\mathbb N}C_2,\qquad
X=\mathbb N\times\{0,1\},
\]
作用为
\[
\varepsilon\cdot(n,b)=(n,b+\varepsilon_n\pmod2).
\tag{19}
\]
群元素是有限支撑的二进制序列，因此 \(G,X\) 都可数。每个点都被翻转其所在二点块的生成元移动，故 \(X^G=\varnothing\)。

每个群元素只移动有限多个点。因此每个自由超滤子都包含其固定点集，从而不动。反过来，不动超滤子不能是主超滤子，否则其主点必须固定。于是本例的全部不动记录为
\[
\boxed{
R_\infty(X)^G=\{\text{\(X\) 上所有自由超滤子}\}
\cong\operatorname{Stone}(\mathcal P(X)/\mathrm{Fin}).
}
\tag{20}
\]
它非空，因为无限集上的余有限滤子是真滤子，可以扩张为超滤子。每个记录都按式 (2) 从其自由超滤子恢复。式 (20) 同时描述了全部记录及其拓扑。

现在也可给出任意 \(G\) 集合上有限层不动记录的准确延拓范围：

- 第 \(1\) 层：非空 \(X\) 上的唯一记录可完整不动延拓，当且仅当 (14) 成立；所有延拓正是 (11)。
- 第 \(2\) 层：一个不动互补选择族可延拓，当且仅当它是超滤子，等价于对每个三块分割恰选一块；延拓唯一。
- 至少第 \(3\) 层：每个不动记录都唯一延拓。唯一性和 (4) 保证延拓仍不动。

**3. 乘积比较。**

每个坐标投影 \(p_i\) 都是 \(G\)-等变映射，所以由函子性，
\[
R_\infty(p_i)(g\cdot r)=g\cdot R_\infty(p_i)(r).
\]
因此 \(\Pi_{(X_i)}\) 良定义。其第 \(i\) 个坐标映射满足
\[
R_\infty(p_i)^{-1}(\widehat A)=\widehat{p_i^{-1}(A)},
\]
故连续；按乘积拓扑的定义，\(\Pi_{(X_i)}\) 连续。

事实上，
\[
\boxed{\Pi_{(X_i)}\text{ 对任意 }G\text{ 和任意集合指标族总是满射。}}
\tag{21}
\]
若目标为空，满射断言自然成立。否则给定目标中的一族不动超滤子
\((\mathcal U_i)_{i\in I}\)，令 \(P=\prod_iX_i\)，在 \(P\) 上考虑以下集合族：
\[
p_i^{-1}(A)\quad(i\in I,\ A\in\mathcal U_i),
\qquad
P^{\langle S\rangle}=\prod_{i\in I}X_i^{\langle S\rangle}
\quad(S\subseteq G\text{ 有限}).
\tag{22}
\]
它具有有限交性质。事实上，合并有限多个条件后，只需考虑有限多个坐标约束 \(A_i\in\mathcal U_i\) 和一个有限集合 \(S\)。由不动性，
\[
X_i^{\langle S\rangle}\in\mathcal U_i.
\]
在受约束的坐标，\(A_i\cap X_i^{\langle S\rangle}\ne\varnothing\)；在其余坐标，\(X_i^{\langle S\rangle}\ne\varnothing\)。ZFC 的选择公理保证可以同时选择坐标，得到交集中的一点。

将 (22) 扩张为超滤子 \(\mathcal W\)。它的每个边缘超滤子是指定的 \(\mathcal U_i\)，又包含所有 \(P^{\langle S\rangle}\)，故由 (11) 不动。这证明满射。若 \(I=\varnothing\)，源和目标都是单点集，比较映射是唯一双射，与上述结论一致。

对于平凡群，两集合的比较映射满足
\[
\boxed{
\operatorname{Ult}(X\times Y)\longrightarrow
\operatorname{Ult}(X)\times\operatorname{Ult}(Y)
\text{ 单射}
\iff
X,Y\text{ 至少一个有限}.
}
\tag{23}
\]

先证有限一侧的结论，而且直接允许任意群作用。假设 \(X\) 有限。若 \(X=\varnothing\)，源、目标都为空。否则任一目标元素都形如
\[
(\mathcal U_x,\mathcal V),\qquad x\in X^G,\quad
\mathcal V\in\operatorname{Ult}(Y)^G.
\]
边缘为 \(\mathcal U_x\) 的超滤子必须包含切片 \(\{x\}\times Y\)，因此被另一个边缘唯一确定，具体为
\[
A\in\mathcal W
\quad\Longleftrightarrow\quad
\{y:(x,y)\in A\}\in\mathcal V.
\tag{24}
\]
这是由等变映射 \(y\mapsto(x,y)\) 推前得到的不动超滤子。因此比较映射双射。\(Y\) 有限时同理。这证明了题目中第一个全称命题为真。

再假设 \(X,Y\) 都无限。ZFC 保证存在互异点列
\((x_n)_{n\in\mathbb N}\)、\((y_n)_{n\in\mathbb N}\)。取 \(\mathbb N\) 上自由超滤子 \(\mathcal U\)，沿两点列推前，得到 \(\mathcal U_X,\mathcal U_Y\)。令
\[
D=\{(x_n,y_n):n\in\mathbb N\}.
\]
沿 \(n\mapsto(x_n,y_n)\) 推前得到超滤子 \(\mathcal W_D\)，其边缘是
\((\mathcal U_X,\mathcal U_Y)\)，并且 \(D\in\mathcal W_D\)。

另一方面，集合族
\[
\{A\times B:A\in\mathcal U_X,\ B\in\mathcal U_Y\}
\ \cup\ \{(X\times Y)\setminus D\}
\tag{25}
\]
具有有限交性质。对于任意这样的 \(A,B\)，集合
\[
\{n:x_n\in A\}\cap\{n:y_n\in B\}
\]
属于自由超滤子 \(\mathcal U\)，因而无限。取其中不同的 \(n,m\)，则
\((x_n,y_m)\in(A\times B)\setminus D\)。有限多个矩形的交仍是同类矩形，故证明了有限交性质。

将 (25) 扩张为超滤子 \(\mathcal W_{\mathrm{off}}\)，它具有相同边缘，却不包含 \(D\)。于是比较映射不单射，完成 (23) 的证明。

最后，题目中的第二个全称命题为假：
\[
X^G=Y^G=\varnothing
\quad\text{并不保证比较映射单射。}
\]
取 (19) 的可数作用，并令 \(Y=X\)。任选一个自由超滤子 \(\mathcal U\)，它由 (20) 知道是不动的。

沿对角映射 \(x\mapsto(x,x)\) 推前，得到不动超滤子
\(\mathcal W_\Delta\)，边缘为 \((\mathcal U,\mathcal U)\)，且包含对角线 \(\Delta\)。

同时，
\[
\{A\times B:A,B\in\mathcal U\}\cup\{(X\times X)\setminus\Delta\}
\tag{26}
\]
具有有限交性质：\(A\cap B\) 属于自由超滤子，故无限，可以选择不同的两个点。将其扩张为 \(\mathcal W_{\mathrm{off}}\)，则边缘仍为
\((\mathcal U,\mathcal U)\)。

这个延拓也必定不动。对每个 \(g\in G\)，有 \(X^g\in\mathcal U\)，所以 (26) 中包含矩形
\[
X^g\times X^g=(X\times X)^g.
\]
由 (9)，\(\mathcal W_{\mathrm{off}}\) 被每个 \(g\) 固定。两个不动记录有相同边缘，却分别包含和排除对角线，因而不同；同时两因子都没有任何原集合不动点。