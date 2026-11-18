## 1. 截断记录及限制映射

若 \(X=\varnothing\)，则 \(\operatorname{Map}(X,[0])\) 是单点集，因而不存在 \(r_0\)。所以每个 \(R_m(\varnothing)\) 都为空，所有遗忘映射的像也为空，没有目标点需要取纤维。以下先设 \(X\ne\varnothing\)。此时没有到 \([0]\) 的测试，而 \(r_1\) 唯一，因此 \(R_1(X)\) 是单点集。

### 二值和三值测试

对 \(A\subseteq X\)，记 \(\chi_A:X\to[2]\) 为取值 \(1\) 于 \(A\) 的指示函数。对任意 \(m\ge2\) 的记录，定义
\[
\mathcal C_r=\{A\subseteq X\mid r_2(\chi_A)=1\}.
\]
由 \([1]\to[2]\) 的两个常值映射可知，\(X\in\mathcal C_r\) 且 \(\varnothing\notin\mathcal C_r\)。由 \([2]\) 上的交换映射可知，每对 \(A,X\setminus A\) 中恰有一个属于 \(\mathcal C_r\)。

当 \(m=2\) 时，这些条件已经充分。每个二值测试都是某个 \(\chi_A\)，所以 \(\mathcal C_r\) 确定 \(r_2\)。而 \([1],[2]\) 之间允许的映射只有恒等、交换和常值映射，上述条件保证了相容性。因此，\(R_2(X)\) 恰由所有互补对子上的选择给出，其中 \(\{\varnothing,X\}\) 必须选择 \(X\)。

当 \(m\ge3\) 时，\(\mathcal C_r\) 必为 \(X\) 上的**超滤子**。为此，对任一允许的 \(f:X\to[n]\) 和 \(i\in[n]\)，用 \(\{i\}\) 的指示函数 \([n]\to[2]\) 后复合，得到
\[
r_n(f)=i\quad\Longleftrightarrow\quad f^{-1}(\{i\})\in\mathcal C_r. \tag{1}
\]
特别地，三格划分中恰有一格属于 \(\mathcal C_r\)，允许其中一些格为空。若 \(A,B\) 不交，对划分 \(A,B,X\setminus(A\cup B)\) 应用这一事实，得到
\[
A\cup B\in\mathcal C_r
\quad\Longleftrightarrow\quad A\in\mathcal C_r\ \text{或}\ B\in\mathcal C_r.
\]
将较大的集合写成较小的集合与差集的不交并，可知 \(\mathcal C_r\) 向上封闭。若 \(A,B\in\mathcal C_r\) 而 \(A\cap B\notin\mathcal C_r\)，把 \(A\) 写成 \((A\cap B)\sqcup(A\setminus B)\) 就得到 \(A\setminus B\in\mathcal C_r\)，进而 \(X\setminus B\in\mathcal C_r\)，矛盾。因此 \(\mathcal C_r\) 是真滤子，又恰含每对互补集合中的一个，所以是超滤子。

反过来，给定超滤子 \(\mathcal U\)，每个有限划分恰有一格属于 \(\mathcal U\)。两格同时属于它会使空集属于它，各格均不属于它则会使各格补集的交即空集属于它。用 (1) 定义记录。若所选格是 \(f^{-1}(\{i\})\)，它包含于 \((a\circ f)^{-1}(\{a(i)\})\)，故后一个测试选 \(a(i)\)。这证明了相容性，并给出对每个 \(m\ge3\)（包括 \(\infty\)）的同一分类。点值记录对应于主超滤子
\[
\mathcal U_x=\{A\subseteq X\mid x\in A\}.
\]
在二值层，它对应于同一个子集族。

### 像、纤维与自然性

对非空 \(X\)，所有 \(q_{m,k}\) 如下。

- \(k=1\) 时，像是唯一的目标点，其纤维是整个 \(R_m(X)\)。定义域含有点值记录。
- \(m=k=2\) 时，映射为恒等。
- \(m\ge3,\ k=2\) 时，像恰由构成超滤子的二值选择族组成。像内各点有一个原像，其余各点的纤维为空。
- \(m\ge k\ge3\) 时，在超滤子分类下映射为恒等。

对 \(h:X\to Y\)，预复合保留记录的相容方程。在二值选择族和超滤子的分类下，\(R_m(h)\) 都由同一公式给出
\[
h_*\mathcal C=\{B\subseteq Y\mid h^{-1}(B)\in\mathcal C\}.
\]
这是因为 \(\chi_B\circ h=\chi_{h^{-1}(B)}\)。逆像保留补集、交和包含关系，因此公式也直接保留相应的分类条件。在一值层，有记录时就是单点之间的映射。由预复合的定义，\(R_m\) 保持恒等和复合，且
\[
q^Y_{m,k}R_m(h)=R_k(h)q^X_{m,k},
\qquad
R_m(h)\eta_{m,X}=\eta_{m,Y}h,
\qquad
q^X_{m,k}\eta_{m,X}=\eta_{k,X}.
\]
特别地，\(R_m(h)\) 将一个遗忘纤维送入相应目标记录的遗忘纤维。这些等式也适用于空集。

### 有限 \(G\) 集合

设 \(X\) 有限非空，记 \(d=|X^G|\)，令 \(H\) 为 \(G\) 在 \(\operatorname{Sym}(X)\) 中的像。则：

- \(R_1(X)^G\) 恒为单点集。
- \(R_2(X)^G\) 非空当且仅当 \(H\) 的每个元素在 \(X\) 上至少有一个奇长度循环。条件成立时，令 \(N=|\mathcal P(X)/H|\)，则
  \[
  |R_2(X)^G|=2^{N/2-1},
  \qquad
  N=\frac1{|H|}\sum_{\sigma\in H}2^{c(\sigma)},
  \]
  其中 \(c(\sigma)\) 是 \(\sigma\) 的循环数。条件失败时基数为 \(0\)。
- 对 \(m\ge3\)，\(R_m(X)^G\) 与 \(X^G\) 一一对应，基数为 \(d\)，故非空当且仅当 \(d>0\)。

二值层的不动条件是所选子集族为 \(H\)-轨道的并。补集在 \(\mathcal P(X)/H\) 上诱导对合。若它有不动轨道，就存在 \(\sigma A=X\setminus A\)，而轨道内的集合必须同时被选或同时被舍，无法满足互补选择。若对合没有不动轨道，每一对互补轨道中任选一个即可，其中 \(\varnothing\) 与 \(X\) 所在的一对必须选择 \(X\) 的轨道。这给出 \(2^{N/2-1}\)。等式 \(\sigma A=X\setminus A\) 要求沿每个循环交替进出 \(A\)，所以它有解恰当所有循环长度均为偶数。公式中的 Burnside 引理适用于有限群 \(H\) 对有限集 \(\mathcal P(X)\) 的作用，而 \(\sigma\) 固定的子集恰是它的循环的并。

对 \(m\ge3\)，有限集上的超滤子必在单点划分中选择一个单点，因而是主超滤子。又有 \(g_*\mathcal U_x=\mathcal U_{gx}\)，且不同点给出不同主超滤子，故不动条件正是 \(x\in X^G\)。

这些不动集合之间的限制映射由此完全确定。目标层为 \(1\) 时，纤维是整个定义域，像在定义域非空时为单点。两层均至少为 \(3\) 时，映射在 \(X^G\) 的标识下为恒等。由 \(m\ge3\) 到 \(2\) 时，映射把 \(x\in X^G\) 送到选择所有含 \(x\) 子集的记录，每个这样的记录有唯一原像，其余没有原像。二值层到自身是恒等。若 \(X=\varnothing\)，各不动集合均为空。

因此在有限非空 \(X\) 上，一层记录有且仅有 \(d\) 个完整不动延拓。二层不动记录恰在由某个 \(x\in X^G\) 给出时可延拓，且延拓唯一。从三层开始，每个不动记录都有唯一完整不动延拓。事实上，对任意 \(X\)，二层不动记录的延拓条件都是其选择族构成超滤子。延拓一旦存在，就由唯一性和 \(q_{\infty,2}\) 的等变性自动不动。若 \(|X|\le2\)，每个二层记录都满足这个条件。若 \(|X|\ge3\) 且存在二层不动记录，可以在所有单点集所在的互补对子上改为选择单点集。不同单点集属于不同对子，且 \(G\) 保持这项修改。所得不动记录含两个不交的单点集，无法延拓。三值门槛也适用于延拓的存在性保证：三阶循环群在自身上的正则作用有一层和二层不动记录，但没有完整不动记录。

## 2. 完整不动记录的空间

记 \(\operatorname{Ult}(X)\) 为 \(X\) 上的超滤子集合，并写
\[
\widehat A=\{\mathcal U\in\operatorname{Ult}(X)\mid A\in\mathcal U\}.
\]
由 (1)，观察 \(r\mapsto r_n(f)\) 取值 \(i\) 的集合恰为 \(\widehat{f^{-1}(\{i\})}\)。反过来，每个 \(\widehat A\) 都由二值测试 \(\chi_A\) 给出。这些集合对有限交封闭，且 \(\widehat A\) 的补集是 \(\widehat{X\setminus A}\)，所以构成一组开闭基。第一部分的分类因而是 \(R_\infty(X)\) 与这个超滤子空间之间的同胚。

### 不动性的判据与内在构造

对单个 \(g\in G\)，写 \(\operatorname{Fix}_X(g)=\{x\in X\mid gx=x\}\)。有
\[
g_*\mathcal U=\mathcal U
\quad\Longleftrightarrow\quad
\operatorname{Fix}_X(g)\in\mathcal U. \tag{2}
\]
若固定点集属于 \(\mathcal U\)，则 \(A\) 与 \(g_X^{-1}(A)\) 在该集上相同，故二者是否属于 \(\mathcal U\) 相同。这里用到 \(B\in\mathcal U\) 时，\(A\in\mathcal U\) 等价于 \(A\cap B\in\mathcal U\)。

反过来，将非固定点按 \(g\) 的轨道分解，并用选择公理在各轨道选取代表。无限轨道可用整数编号，沿整数奇偶交替使用两种颜色。偶长度循环也交替使用两色。奇长度循环的长度至少为三，先将前面偶数个点交替染色，再给最后一点第三种颜色。这样得到非固定点的一组三格划分 \(C_0,C_1,C_2\)，满足 \(C_j\cap gC_j=\varnothing\)。若 \(\mathcal U\) 由 \(g\) 保持而不含固定点集，则必含一个 \(C_j\)，也就含 \(gC_j\)，与真滤子性质矛盾。这证明了 (2)。

对有限 \(F\subseteq G\)，记
\[
X^F=\bigcap_{g\in F}\operatorname{Fix}_X(g),\qquad X^\varnothing=X.
\]
于是完整不动记录对应于
\[
\bigcap_{F\subseteq G\ \mathrm{有限}}\widehat{X^F}. \tag{3}
\]
这些记录**非空当且仅当每个有限 \(F\subseteq G\) 都有 \(X^F\ne\varnothing\)**。必要性来自真滤子的定义。充分性来自有限交性质，因为有限多个 \(X^F\) 的交等于指标并集对应的固定点集。在 ZFC 中，具有有限交性质的子集族生成一个真滤子，并由 Zorn 引理延拓为超滤子。这里链的并仍是真滤子，而极大真滤子若不含 \(A\)，就必有某个成员与 \(A\) 不交，否则还可加入 \(A\) 并生成更大的真滤子。因此极大真滤子恰含每对互补集合中的一个。该非空判据也就是每个有限生成子群都有共同固定点，因为固定一组生成元等价于固定它生成的子群。对非空 \(X\)，这也给出唯一一层不动记录可延拓的准确条件。

还可以直接从作用构造一个布尔代数，其超滤子空间就是 (3)。定义
\[
A\sim B\quad\Longleftrightarrow\quad
\exists F\subseteq G\ \mathrm{有限},\quad A\cap X^F=B\cap X^F,
\qquad
\mathfrak B_{G,X}=\mathcal P(X)/{\sim}.
\]
合并有限指标集即可同时保持多项等式，因此这是等价关系，且并、交、补在等价类上良定义。商映射把每个 \(X^F\) 送到单位元，所以商代数上的超滤子拉回后属于 (3)。反之，属于 (3) 的超滤子对 \(A\) 的取舍仅依赖于 \([A]\)，因为可在判定 \(A\sim B\) 的 \(X^F\) 上取交。由此得到的等价类族是真滤子且恰选每对互补元素中的一个。例如若 \([A]\le[B]\) 且 \([A]\) 被选，则 \([A\cap B]=[A]\) 被选，从而 \(A\cap B\in\mathcal U\)，进而 \(B\in\mathcal U\)。这两个构造互逆，并把商代数超滤子空间中由 \([A]\) 给出的基开集对应到 (3) 与 \(\widehat A\) 的交，故给出同胚。若商代数的零元等于单位元，它没有真超滤子。这包括 \(X=\varnothing\) 的情形。

### 不动点记录的闭包

对任意 \(S\subseteq X\)，主超滤子 \(\{\mathcal U_x\mid x\in S\}\) 的闭包是 \(\widehat S\)。若 \(\mathcal U\in\widehat S\)，其每个基本邻域 \(\widehat A\) 都满足 \(A\cap S\in\mathcal U\)，故包含某个来自 \(S\) 的主超滤子。若 \(\mathcal U\notin\widehat S\)，则 \(\widehat{X\setminus S}\) 是与这些主超滤子全不相交的邻域。因此
\[
\overline{\eta_{\infty,X}(X^G)}=\widehat{X^G},
\qquad
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\quad\Longleftrightarrow\quad
\exists F\subseteq G\ \mathrm{有限},\quad X^F=X^G.
\]
如果有这样的 \(F\)，(3) 中每个超滤子都含 \(X^G\)。如果没有，则每个 \(X^F\) 都与 \(X\setminus X^G\) 相交。由 \(X^{F_1}\cap X^{F_2}=X^{F_1\cup F_2}\)，所有 \(X^F\) 连同 \(X\setminus X^G\) 具有有限交性质，因而给出一个在 (3) 中但不在闭包中的超滤子。

**对每个 \(G\) 集合都满足闭包等式的群，恰是有限生成群。** 若 \(G\) 有有限生成集，取该生成集为 \(F\) 即可。若 \(G\) 不是有限生成的，取 \(X\) 为所有有限生成子群 \(H\le G\) 的左陪集空间 \(G/H\) 的不交并，作用为左乘。这些子群构成集合，且每个都是真子群。陪集 \(aH\) 的稳定子是 \(aHa^{-1}\)，仍是真子群，故 \(X^G=\varnothing\)。每个有限 \(F\subseteq G\) 都固定 \(\langle F\rangle\) 对应分支中的单位陪集，故 (3) 非空，闭包等式失败。

### 可数例子

取
\[
G=\bigoplus_{n\in\mathbb N}\mathbb Z/2,\qquad
X=\mathbb N\times\mathbb Z/2,\qquad
g(n,e)=(n,e+g_n).
\]
群元素是有限支撑的二值序列，所以 \(G\) 与 \(X\) 都可数。每个点都被只翻转其所在坐标的群元素移动，故 \(X^G=\varnothing\)。而每个 \(g\) 只移动有限多个点，所以它的固定点集是余有限集。

这个例子的全部不动记录恰对应于 \(X\) 上的非主超滤子。每个非主超滤子都含所有余有限集，故由 (2) 得到不动记录。主超滤子若不动，其对应点就必须不动。非主超滤子确实存在，因为无限集上所有余有限集具有有限交性质，而包含它们的超滤子不能含单点集。更明确地，每个不动记录由唯一的一对 \((e,\mathcal D)\) 给出，其中 \(e\in\mathbb Z/2\)，\(\mathcal D\) 是 \(\mathbb N\) 上的非主超滤子，公式为
\[
A\in\mathcal U_{e,\mathcal D}
\quad\Longleftrightarrow\quad
\{n\in\mathbb N\mid (n,e)\in A\}\in\mathcal D .
\]
因为超滤子恰含 \(\mathbb N\times\{0\}\) 与 \(\mathbb N\times\{1\}\) 中的一边，限制在所选一边就确定了 \(\mathcal D\)。

## 3. 乘积比较

记 \(P=\prod_{i\in I}X_i\)。投影 \(p_i\) 等变，所以 \(R_\infty(p_i)\) 把不动记录送到不动记录。目标因子上观察 \(f:X_i\to[n]\) 的拉回是对 \(f\circ p_i\) 的观察，故各坐标连续，从而 \(\Pi_{(X_i)}\) 对乘积拓扑连续。若 \(I=\varnothing\)，两端都是单点，映射为双射。若某个 \(X_i=\varnothing\)，两端都为空。

**\(\Pi_{(X_i)}\) 总是满射。** 给定一族不动超滤子 \((\mathcal U_i)_{i\in I}\)，在 \(P\) 上考虑下列集合
\[
p_i^{-1}(A)\quad(i\in I,\ A\in\mathcal U_i),
\qquad
P^F=\prod_{i\in I}X_i^F\quad(F\subseteq G\text{ 有限}).
\]
它们具有有限交性质。对任一有限子族，将其中的固定点条件合并为一个有限 \(F\)，并在每个坐标 \(i\) 将选中的集合与 \(X_i^F\) 取交。所得集合属于 \(\mathcal U_i\)，故非空。选择公理给出这些坐标集合的乘积中的一点，即所取有限子族的公共点。因此有超滤子 \(\mathcal W\) 包含上述各集。由 (3)，\(\mathcal W\) 不动。其第 \(i\) 个投影包含 \(\mathcal U_i\) 的所有成员，因而等于 \(\mathcal U_i\)。这就构造了给定目标点的原像。

### 有限因子与平凡群的单射判据

**对任意群作用，只要两因子至少一个有限，比较映射就是双射。** 设 \(X\) 有限。若给定一对不动投影超滤子，第一个必为某个 \(x\in X^G\) 的主超滤子。因此任何原像 \(\mathcal W\) 都含 \(\{x\}\times Y\)。对任意 \(C\subseteq X\times Y\)，若第二个投影超滤子为 \(\mathcal V\)，则
\[
C\in\mathcal W
\quad\Longleftrightarrow\quad
\{y\in Y\mid (x,y)\in C\}\in\mathcal V.
\]
这是因为 \(C\) 与右侧集合在 \(p_Y\) 下的逆像，在 \(\{x\}\times Y\) 上相同。故原像唯一，也可直接用等变映射 \(y\mapsto(x,y)\) 推送 \(\mathcal V\) 得到。若没有目标点，良定义性保证定义域也为空。

对平凡群，**两因子的比较映射为单射，当且仅当至少一个因子有限。** 有限因子的方向已证。若 \(X,Y\) 均无限，在 ZFC 中可取单射 \(n\mapsto x_n\in X\)、\(n\mapsto y_n\in Y\)。取 \(\mathbb N\) 上的非主超滤子 \(\mathcal D\)，沿这两个单射推送得到 \(\mathcal U,\mathcal V\)。沿 \(n\mapsto(x_n,y_n)\) 推送得到一个以它们为投影的超滤子 \(\mathcal W_0\)，其中含
\[
E=\{(x_n,y_n)\mid n\in\mathbb N\}.
\]
另一个原像可由所有 \(A\times B\)（\(A\in\mathcal U,\ B\in\mathcal V\)）连同 \((X\times Y)\setminus E\) 延拓得到。事实上，有限多个这样的矩形相交后仍是这样的矩形，而 \(\{n\mid x_n\in A\}\) 和 \(\{m\mid y_m\in B\}\) 都属于 \(\mathcal D\)，故都是无限集。可选 \(n\ne m\) 使 \((x_n,y_m)\in A\times B\)，由单射性该点不在 \(E\) 中。这证明了有限交性质。所得 \(\mathcal W_1\) 含 \(E\) 的补集，两个投影仍为 \(\mathcal U,\mathcal V\)，故与 \(\mathcal W_0\) 不同。

### 两因子都没有不动点的情形

命题“若 \(X^G=Y^G=\varnothing\)，则比较映射为单射”是**假的**。先注意，在两因子的情形，只要一个超滤子的两个投影都不动，它本身就不动。对每个 \(g\)，两个投影分别含 \(\operatorname{Fix}_X(g)\) 和 \(\operatorname{Fix}_Y(g)\)，所以原超滤子含两个逆像的交，即 \(\operatorname{Fix}_{X\times Y}(g)\)。由 (2) 即得不动性。

现在取第二部分的可数作用，令 \(Y=X=\mathbb N\times\mathbb Z/2\)，两边取同一作用。两边都没有不动点。用 \(x_n=y_n=(n,0)\) 进行上面的两个原像构造，两投影都是由 \(e=0\) 和 \(\mathcal D\) 给出的同一个不动超滤子。因此 \(\mathcal W_0,\mathcal W_1\) 都是不动记录，且仍由是否包含 \(E\) 区分。这给出了所需的非单射反例。