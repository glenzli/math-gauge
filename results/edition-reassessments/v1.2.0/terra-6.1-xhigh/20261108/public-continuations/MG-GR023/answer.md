# 有限测试记录与群作用

记
\[
\operatorname{Fix}_X(F)=\{x\in X:gx=x\text{ 对所有 }g\in F\},
\qquad F\subseteq G.
\]
特别地，\(\operatorname{Fix}_X(\varnothing)=X\)，而 \(\operatorname{Fix}_X(G)=X^G\)。下文的超滤子均指真超滤子；空集上没有真超滤子。

主要分类是：非空集合上的二元记录是互补子集的一致选择；从三元测试开始，记录恰是超滤子。完整不动记录恰是包含每个有限共同不动点集合的超滤子。

除原题要求外，下面还给出任意群、任意指标族的乘积比较映射的**全部纤维分类**，以及一个直接用作用和集合分解表述的**单射充要条件**。

## 1. 截断、相容性与有限作用

### 1.1 所有记录

若 \(X=\varnothing\)，则对每个允许的 \(m\)，
\[
R_m(X)=\varnothing.
\]
因为 \(\operatorname{Map}(\varnothing,[0])\) 是单点集，不存在从它到 \([0]=\varnothing\) 的函数。

以下先设 \(X\ne\varnothing\)。对 \(A\subseteq X\)，令 \(1_A:X\to[2]\) 为示性函数，并对二元记录定义
\[
\mathcal C_r=\{A\subseteq X:r_2(1_A)=1\}.
\]
各层分类如下：

- \(R_1(X)\) 是单点集。
- \(R_2(X)\) 等同于满足
  \[
  X\in\mathcal C,\qquad
  A\in\mathcal C\ \Longleftrightarrow\ X\setminus A\notin\mathcal C
  \quad(A\subseteq X)
  \tag{1}
  \]
  的所有子集族 \(\mathcal C\)。
- 对 \(3\le m\le\infty\)，\(R_m(X)\) 等同于 \(X\) 上的真超滤子集合 \(\operatorname{Ult}(X)\)。超滤子 \(U\) 对应的记录为
  \[
  r_n(f)=\text{使 }f^{-1}(\{j\})\in U\text{ 的唯一 }j\in[n].
  \tag{2}
  \]

**证明。** 第一层唯一非空测试的值只能是 \(0\)。第二层中，把常值映射和交换 \([2]\) 两点的映射代入自然性，得到 (1)。反过来，(1) 确定每个二元测试的值；\([1]\) 与 \([2]\) 之间以及各自的映射只有常值映射、恒等映射和二元交换等情形，逐一验证即得自然性。

设 \(m\ge3\)。若 \(A,B\in\mathcal C_r\)，考虑三部分分割
\[
A\cap B,\qquad A\setminus B,\qquad X\setminus A.
\]
将该三元测试分别合并为 \(1_A\) 和 \(1_B\)。自然性迫使被选中的部分同时位于 \(A\) 和 \(B\) 中，因而只能是 \(A\cap B\)。故 \(\mathcal C_r\) 对有限交封闭；结合 (1)，它是真超滤子。

反之，超滤子在每个有限分割中恰选中一个部分，因此 (2) 定义所有测试的值；合并分割时，被选中的部分合并到新分割中被选中的部分，所以自然性成立。两种构造互逆。由于三元记录已确定超滤子，它也唯一确定全部更大测试。\(X\ne\varnothing\) 时不存在 \(X\to[0]\)，故零元测试没有额外要求。

### 1.2 遗忘映射与集合映射

在上述识别下，\(X\ne\varnothing\) 时：

- \(q_{m,1}\) 是到单点集的唯一映射，其唯一纤维是整个 \(R_m(X)\)。
- \(q_{2,2}\) 及所有 \(q_{m,k}\)（\(m,k\ge3\)）是相应集合上的恒等映射。
- \(m\ge3\) 时，\(q_{m,2}\) 把超滤子视为满足 (1) 的子集族。它是单射；其像恰为还对有限交封闭的 \(\mathcal C\)。所以每个像点的纤维是单点，其他纤维为空。

若 \(X=\varnothing\)，相关记录集合及像均为空。

对 \(h:X\to Y\)，二元选择和超滤子按逆像推送：
\[
h_*\mathcal C=\{B\subseteq Y:h^{-1}(B)\in\mathcal C\}.
\tag{3}
\]
在超滤子情形，这仍是真超滤子。直接由定义，
\[
q_{m,k}R_m(h)=R_k(h)q_{m,k},
\qquad
R_m(h)\eta_{m,X}=\eta_{m,Y}h.
\]
当 \(m\ge3\) 时，点值记录 \(\eta_{m,X}(x)\) 对应主超滤子
\[
\delta_x=\{A\subseteq X:x\in A\}.
\]

### 1.3 有限 \(G\) 集合

设 \(X\) 有限，\(G\) 无须有限。若 \(X=\varnothing\)，所有 \(R_m(X)^G\) 均为空。以下设 \(X\ne\varnothing\)。

第一层的不动记录集合是单点集。有限集合上的超滤子都是主超滤子，所以
\[
R_m(X)^G=\{\delta_x:x\in X^G\},\qquad
|R_m(X)^G|=|X^G|
\quad(m\ge3).
\tag{4}
\]

对第二层，让 \(G\) 作用于互补对子
\[
\{A,X\setminus A\}\qquad(A\subseteq X).
\]
若存在 \(g\in G\) 和 \(A\subseteq X\) 使
\[
gA=X\setminus A,
\tag{5}
\]
则不存在不动的二元选择。若不存在这样的 \(g,A\)，令 \(c\) 为除去对子 \(\{\varnothing,X\}\) 后的互补对子的 \(G\)-轨道数，则
\[
|R_2(X)^G|=2^c.
\tag{6}
\]

的确，二元记录必须从每个互补对子中选一边，且不动性要求选择沿轨道传递。(5) 恰好是沿一个轨道传递选择时发生矛盾的条件。若没有矛盾，每个非平凡轨道有两个独立选择，而 \(\{\varnothing,X\}\) 被迫选 \(X\)。

限制到不动记录后的映射也随之确定：第三层及以上互相限制是 \(X^G\) 上的恒等映射；向第一层的映射是到单点的唯一映射；从第三层及以上到第二层的像恰为
\[
\{\mathcal C_{\delta_x}:x\in X^G\},
\]
各像点的纤维为单点。

因此，有限层不动记录延拓为完整不动记录的准确范围为：第一层的唯一记录当且仅当 \(X^G\ne\varnothing\) 时可延拓；第二层记录当且仅当它是某个 \(x\in X^G\) 的主超滤子时可延拓；第三层及以上的每个不动记录均唯一延拓。

## 2. 完整不动记录的空间

### 2.1 内在分类与非空条件

在记录与超滤子的识别下，
\[
\boxed{\quad
R_\infty(X)^G
=
\left\{U\in\operatorname{Ult}(X):
\operatorname{Fix}_X(F)\in U
\text{ 对每个有限 }F\subseteq G\right\}.
\quad}
\tag{7}
\]

为证明它，先固定 \(g\in G\)。若超滤子 \(U\) 包含 \(\operatorname{Fix}_X(g)\)，则任意 \(A\) 与 \(gA\) 在该集合上的交相同，故 \(A\in U\) 当且仅当 \(gA\in U\)；因此 \(U\) 受 \(g\) 固定。

反过来，把 \(X\setminus\operatorname{Fix}_X(g)\) 按循环群 \(\langle g\rangle\) 的轨道分解。每个非平凡有限循环可用至多三色使相邻点异色，无限轨道也可以。由选择公理合并各轨道的染色，得到三个集合 \(C_1,C_2,C_3\)，覆盖非不动点，并满足
\[
C_j\cap gC_j=\varnothing.
\]
若 \(g\)-不变超滤子包含非不动点集合，它就包含某个 \(C_j\)，也包含 \(gC_j\)，矛盾。因此它包含 \(\operatorname{Fix}_X(g)\)。对有限多个群元素取交，即得 (7)。

有限共同不动点集合满足
\[
\operatorname{Fix}_X(F_1)\cap\operatorname{Fix}_X(F_2)
=\operatorname{Fix}_X(F_1\cup F_2).
\]
由 ZFC 中的超滤子扩张定理，
\[
\boxed{\quad
R_\infty(X)^G\ne\varnothing
\ \Longleftrightarrow\
\operatorname{Fix}_X(F)\ne\varnothing
\text{ 对每个有限 }F\subseteq G.
\quad}
\tag{8}
\]
这也覆盖 \(X=\varnothing\)：取 \(F=\varnothing\) 即可。

对 \(A\subseteq X\)，记
\[
\widehat A=\{U\in\operatorname{Ult}(X):A\in U\}.
\]
这些集合构成 Stone 拓扑的开闭基。示性函数观察给出每个 \(\widehat A\)，任意有限测试的观察纤维也具有此形式，因此 Stone 拓扑就是题设拓扑。于是 (7) 同时给出拓扑分类：
\[
R_\infty(X)^G
=\bigcap_{\substack{F\subseteq G\\F\text{ 有限}}}
\widehat{\operatorname{Fix}_X(F)}
\subseteq\operatorname{Ult}(X).
\tag{9}
\]

### 2.2 真正不动点的闭包

对任意 \(S\subseteq X\)，有
\[
\overline{\{\delta_x:x\in S\}}=\widehat S.
\tag{10}
\]
若 \(S\notin U\)，则 \(\widehat{X\setminus S}\) 是 \(U\) 的一个邻域，不含上述主超滤子。若 \(S\in U\)，任意基本邻域 \(\widehat A\ni U\) 都满足 \(A\cap S\ne\varnothing\)，所以包含某个 \(\delta_x\)，其中 \(x\in S\)。

因此
\[
\boxed{\quad
\overline{\eta_{\infty,X}(X^G)}
=\{U\in\operatorname{Ult}(X):X^G\in U\}.
\quad}
\tag{11}
\]
该闭包总包含于 \(R_\infty(X)^G\)，而两者相等当且仅当
\[
\boxed{\quad
\exists\text{ 有限 }F\subseteq G,\qquad
\operatorname{Fix}_X(F)=X^G.
\quad}
\tag{12}
\]
充分性由 (7) 直接得到。若不存在这样的 \(F\)，则所有 \(\operatorname{Fix}_X(F)\) 与 \(X\setminus X^G\) 共同具有有限交性质；把它们扩张成超滤子，便得到一个属于 (7) 而不属于 (11) 的记录。

对**每个** \(G\) 集合都满足该闭包等式的群，恰为有限生成群。有限生成时，在 (12) 中取有限生成集即可。反过来，若 \(G\) 非有限生成，令 \(H\) 遍历其有限生成子群，取
\[
X=\coprod_H G/H
\]
及其左平移作用。每个这样的 \(H\) 都是 \(G\) 的真子群，因此 \(X^G=\varnothing\)。但任意有限 \(F\subseteq G\) 固定分量 \(G/\langle F\rangle\) 中的陪集 \(\langle F\rangle\)。由 (8)，\(R_\infty(X)^G\ne\varnothing\)，所以闭包等式失败。

### 2.3 一个可数例子

取 \(X=\mathbb N\)，\(G\) 为 \(\mathbb N\) 的有限支撑置换群，以通常方式作用。二者均可数，且 \(X^G=\varnothing\)。

每个 \(g\in G\) 的不动点集合余有限，所以每个非主超滤子都包含它，因而是不动记录。反之，若不动超滤子包含单点 \(\{n\}\)，它就是 \(\delta_n\)，但交换 \(n\) 与另一点的置换不固定它。因此全部不动记录恰为
\[
\boxed{\quad
R_\infty(\mathbb N)^G
=\{\mathbb N\text{ 上的非主超滤子}\}.
\quad}
\]
由超滤子扩张定理，余有限滤子可扩张为非主超滤子，故该集合非空。

## 3. 乘积比较

### 3.1 良定义、连续性与满射

投影 \(p_i:P=\prod_iX_i\to X_i\) 是等变映射，故超滤子的推送把不动记录送到不动记录。目标的观察复合 \(\Pi_{(X_i)}\) 后是源上的观察
\[
r\longmapsto r_n(f\circ p_i),
\]
所以比较映射良定义且连续。

它对任意 \(G\) 和任意集合指标族都是**满射**。给定目标中的不动超滤子 \(U_i\)，考虑 \(P\) 上的集合族
\[
p_i^{-1}(A)\quad(A\in U_i),\qquad
\operatorname{Fix}_P(F)
=\prod_i\operatorname{Fix}_{X_i}(F)
\quad(F\subseteq G\text{ 有限}).
\tag{13}
\]
它具有有限交性质。事实上，合并有限多个 \(F\) 后，每个被有限多个柱集约束的坐标，都有一个属于 \(U_i\) 的集合再与 \(\operatorname{Fix}_{X_i}(F)\) 相交；该交仍属于 \(U_i\)，故非空。其余坐标的 \(\operatorname{Fix}_{X_i}(F)\) 也非空。选择公理给出乘积中的点。

将 (13) 扩张为超滤子 \(U\)。由 (7)，\(U\) 不动；其第 \(i\) 个边缘包含 \(U_i\)，因两者均为超滤子，故相等。若目标为空，满射性自动成立。指标族为空时，源、目标均为单点，比较映射为双射。

### 3.2 平凡群的两因子单射判准

对平凡群，
\[
\boxed{\quad
\Pi_{X,Y}\text{ 为单射}
\ \Longleftrightarrow\
X\text{ 或 }Y\text{ 有限}.
\quad}
\tag{14}
\]
这里有限包括空集。

若 \(Y\) 是非空有限集，\(X\times Y\) 上的每个超滤子集中于唯一切片 \(X\times\{y\}\)，并由其在 \(X\) 上的边缘唯一确定。若 \(Y=\varnothing\)，源为空。交换两因子同理。

若 \(X,Y\) 均无限，选取互异点列 \((x_n)\)、\((y_n)\)，以及 \(\mathbb N\) 上的非主超滤子 \(U,V\)。定义 \(\mathbb N^2\) 上的超滤子
\[
\begin{aligned}
A\in W
&\Longleftrightarrow
\{n:\{m:(n,m)\in A\}\in V\}\in U,\\
A\in W'
&\Longleftrightarrow
\{m:\{n:(n,m)\in A\}\in U\}\in V.
\end{aligned}
\tag{15}
\]
它们的两个边缘分别都是 \(U,V\)，但集合 \(\{(n,m):n<m\}\) 属于 \(W\) 而不属于 \(W'\)：其每一行余有限、每一列有限。沿 \((n,m)\mapsto(x_n,y_m)\) 推送，得到两个不同而边缘相同的超滤子，所以比较映射不单射。

### 3.3 原题中的两个全称命题

**若 \(X,Y\) 至少一个有限，比较映射为双射。** 满射性由 3.1 得到；单射性由 3.2 的切片论证在全部超滤子层面成立，限制到不动记录后仍成立。

**\(X^G=Y^G=\varnothing\) 不保证比较映射单射。** 取 2.3 的有限支撑置换群，令 \(X=Y=\mathbb N\)，并取 (15) 中的 \(W,W'\)。对每个 \(g\in G\)，
\[
\operatorname{Fix}_{\mathbb N^2}(g)
=\operatorname{Fix}_{\mathbb N}(g)^2
\]
属于这两个超滤子，因为两个边缘均为非主超滤子。由 (7)，\(W,W'\) 都是不动记录；它们不同却具有相同边缘。

## 4. 进一步结果：任意乘积的纤维与单射性

以下结果适用于任意群、任意集合指标族，并包含空底集和空指标族。它把联合不动记录的重建问题化为明确的布尔代数问题。

令
\[
P=\prod_{i\in I}X_i,\qquad
D_F=\operatorname{Fix}_P(F)
=\prod_{i\in I}\operatorname{Fix}_{X_i}(F)
\quad(F\subseteq G\text{ 有限}).
\]
定义 \(\mathcal P(P)\) 的理想
\[
J=\{A\subseteq P:\exists\text{ 有限 }F\subseteq G,\ A\cap D_F=\varnothing\}.
\tag{16}
\]
它确是理想：向下封闭；若 \(A\cap D_F=B\cap D_H=\varnothing\)，则
\[
(A\cup B)\cap D_{F\cup H}=\varnothing.
\]
允许 \(J=\mathcal P(P)\)，此时商布尔代数是平凡的。

令 \(\mathcal B\) 是由全部柱集 \(p_i^{-1}(A)\)，\(A\subseteq X_i\)，生成的 \(\mathcal P(P)\) 的布尔子代数。其元素恰是只依赖有限多个坐标的集合：它们是有限多个柱集的布尔组合。

### 定理：精确单射判准

\[
\boxed{\quad
\Pi_{(X_i)}\text{ 为单射}
\ \Longleftrightarrow\
\forall A\subseteq P\ \exists B\in\mathcal B\
\exists\text{ 有限 }F\subseteq G,\quad
A\cap D_F=B\cap D_F.
\quad}
\tag{17}
\]

换言之，单射性等价于自然映射
\[
\mathcal B\longrightarrow\mathcal P(P)/J
\tag{18}
\]
满射。

对两个因子，\(\mathcal B\) 的元素恰为有限个矩形 \(A_j\times B_j\) 的并。因此 (17) 可完全展开为：对每个 \(E\subseteq X\times Y\)，存在有限 \(F\subseteq G\) 和有限多个矩形，使得它们的并与 \(E\) 在
\[
\operatorname{Fix}_X(F)\times\operatorname{Fix}_Y(F)
\]
上相等。

**证明。** 写 \(K_X=R_\infty(X)^G\)。由 (9)，它是 \(\operatorname{Ult}(X)\) 的闭子空间。Stone 空间 \(\operatorname{Ult}(X)\) 是紧 Hausdorff 空间：Hausdorff 性由集合及其补的开闭邻域分离；紧性由具有有限交性质的集合族可扩张为超滤子得到。因此 \(K_X\) 也是紧 Hausdorff 空间，空集情形同样成立。

先证明，对任意 \(A\subseteq P\)，
\[
K_P\cap\widehat A=\varnothing
\quad\Longleftrightarrow\quad A\in J.
\tag{19}
\]
若 \(A\cap D_F=\varnothing\)，包含 \(D_F\) 的超滤子不能包含 \(A\)。反之，若每个 \(A\cap D_F\) 非空，则 \(\{A\}\cup\{D_F:F\text{ 有限}\}\) 具有有限交性质；扩张为超滤子后，由 (7) 得到 \(K_P\cap\widehat A\) 中的点。

因此，两个集合 \(A,B\subseteq P\) 在 \(K_P\) 上给出相同开闭集，当且仅当
\[
A\triangle B\in J.
\tag{20}
\]
并且 \(K_P\) 的每个开闭集都形如 \(K_P\cap\widehat A\)：对其每个点取一个包含在该开集中的基本开闭邻域，再由紧性取有限子覆盖。

同理，每个 \(K_{X_i}\) 的开闭集都由某个 \(A\subseteq X_i\) 给出。紧性进一步表明，乘积 \(\prod_iK_{X_i}\) 的每个开闭集都是有限多个有限坐标基本开闭柱集的并；即使乘积为空，这一结论也成立。

若 (17) 成立，任意 \(K_P\) 中的不同超滤子可由某个 \(A\subseteq P\) 分离。由 (17) 和 (20)，它们也由某个 \(B\in\mathcal B\) 分离；而 \(B\) 只由有限多个坐标观察决定，所以它们的边缘不同。这证明单射性。

反过来，若 \(\Pi_{(X_i)}\) 单射，它由 3.1 也是连续满射，故是紧空间到 Hausdorff 空间的同胚。任意 \(K_P\cap\widehat A\) 的像是目标中的开闭集，因而由有限多个坐标开闭柱集构成；将该表示拉回 \(K_P\)，得到某个 \(B\in\mathcal B\) 与 \(A\) 在 \(K_P\) 上给出相同开闭集。由 (20) 和 (16)，得到 (17)。

### 定理：每个纤维的重建

给定目标中的一族不动超滤子 \((U_i)_{i\in I}\)，定义理想
\[
J_{(U_i)}
=
\left\{A\subseteq P:
\begin{array}{l}
\text{存在有限 }F\subseteq G,\ \text{有限 }E\subseteq I,\\
\text{以及 }A_i\in U_i\ (i\in E),\text{ 使}\\
A\cap D_F\cap\displaystyle\bigcap_{i\in E}p_i^{-1}(A_i)=\varnothing
\end{array}
\right\}.
\tag{21}
\]
则对应纤维与商布尔代数上的真超滤子空间自然同胚：
\[
\boxed{\quad
\Pi_{(X_i)}^{-1}\bigl((U_i)_i\bigr)
\cong
\operatorname{Ult}\bigl(\mathcal P(P)/J_{(U_i)}\bigr).
\quad}
\tag{22}
\]

**证明。** (21) 是理想：两个见证可分别合并有限群元素集与有限坐标集，并在重复坐标上把相应的 \(U_i\)-集合取交。3.1 的有限交论证说明 \(P\notin J_{(U_i)}\)，所以该商是非平凡布尔代数。

纤维中的超滤子恰包含所有 \(D_F\) 及所有 \(p_i^{-1}(A_i)\)，其中 \(A_i\in U_i\)。等价地，它避开理想 \(J_{(U_i)}\)：若避开该理想，则包含上述每个集合，因为它们各自的补属于理想；反向也由有限交封闭成立。避开一个理想的超滤子恰对应其商布尔代数上的超滤子。这个对应把由 \(A\subseteq P\) 给出的基本开闭集送到商类 \([A]\) 给出的基本开闭集，故是同胚。

作为具体推论，若 \(G\) 有限生成，则
\[
R_\infty(X)^G\cong\operatorname{Ult}(X^G).
\tag{23}
\]
确实，取有限生成集 \(F\)，(7) 要求超滤子包含 \(\operatorname{Fix}_X(F)=X^G\)，而这样的超滤子与 \(X^G\) 上的超滤子自然对应。由于 \((X\times Y)^G=X^G\times Y^G\)，由 (14) 得到更具体的判准：
\[
\boxed{\quad
G\text{ 有限生成时，}\Pi_{X,Y}\text{ 单射}
\ \Longleftrightarrow\
X^G\text{ 或 }Y^G\text{ 有限}.
\quad}
\tag{24}
\]
这包括某个不动点集合为空的情形。

## 保留、修正与自评

保留了原稿中三层记录分类、不动超滤子分类、闭包判准、可数例子及原题乘积结论；上述证明重新完整给出，并核对了空集和空指标族。新增了任意指标族的单射判准 (17)、每个乘积纤维的布尔代数重建 (22)，以及有限生成群的具体判准 (24)。没有发现需要撤回的原稿结论。

自评为 **B2/R3**：原题三个目标均已覆盖；新增结果对任意群作用和任意集合指标族，完整决定单射性并分类所有纤维，且给出了从集合与作用到商布尔代数、再到纤维拓扑的证明。没有已知未完成部分；这里不声称上述结果的文献原创性。