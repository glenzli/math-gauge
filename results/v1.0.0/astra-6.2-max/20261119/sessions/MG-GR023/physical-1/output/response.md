## 1. 截断记录与限制映射

若 \(X=\varnothing\)，则 \(\operatorname{Map}(X,[0])\) 是单点集，不存在从它到 \([0]\) 的映射。因此所有 \(R_m(\varnothing)\) 及其不动集合都为空，层间的限制映射都是空映射。

先设 \(X\ne\varnothing\)。记 \(A^c=X\setminus A\)，用 \(\mathcal C(X)\) 表示满足下列条件的子集族 \(\mathcal S\subseteq\mathcal P(X)\)：\(X\in\mathcal S\)，且对每个 \(A\subseteq X\)，\(A,A^c\) 中恰有一个属于 \(\mathcal S\)。记 \(\operatorname{Ult}(X)\) 为 \(X\) 上所有真超滤子的集合。则有典范对应
\[
R_m(X)\cong
\begin{cases}
\{*\},&m=1,\\
\mathcal C(X),&m=2,\\
\operatorname{Ult}(X),&3\le m\le\infty.
\end{cases}
\tag{1}
\]

事实上，\(r_0\) 是唯一的空映射，\(r_1\) 也唯一。从第二层起，令
\[
\mathcal S_r=\{A\subseteq X:r_2(\mathbf 1_A)=1\}.
\]
从 \([1]\) 到 \([2]\) 的两个映射迫使记录在常值测试上取该常值，而交换 \(0,1\) 的置换迫使 \(A,A^c\) 中恰有一个被选中。反之，每个二元测试都是某个 \(\mathbf 1_A\)，且 \([2]\) 的自映射只有恒等、交换和两个常值映射。因此每个 \(\mathcal S\in\mathcal C(X)\) 恰好定义一个第二层记录。

当 \(m\ge3\) 时，取有标号的分划 \(X=A_0\sqcup A_1\sqcup A_2\)，允许空块。将对应的三元测试与三个映射 \(\mathbf 1_{\{j\}}:[3]\to[2]\) 分别复合，可知三个块中恰有一个被选中。令 \(\mu(A)=\mathbf 1_{\{A\in\mathcal S_r\}}\)。对不交的 \(A,B\)，取第三块为 \((A\cup B)^c\)，得到
\[
\mu(A\cup B)=\mu(A)+\mu(B).
\]
这给出向上封闭性，也说明两个不交集合不能同时被选中。若 \(A,B\) 都被选中而 \(A\cap B\) 未被选中，则分解 \(A=(A\cap B)\sqcup(A\setminus B)\) 迫使 \(A\setminus B\) 被选中，与 \(B\) 被选中矛盾。因此 \(\mathcal S_r\) 是真滤子，再由补集条件知它是超滤子。

反之，真超滤子 \(\mathcal U\) 在每个有限分划中恰含一个块。至多一个来自块的不交性，至少一个来自所有块的补集交为空。因此可以定义
\[
r_n(f)=j\quad\Longleftrightarrow\quad f^{-1}(\{j\})\in\mathcal U.
\tag{2}
\]
选中的纤维包含于复合测试中标号为 \(a(j)\) 的纤维，故此规则满足相容条件。对任意已有记录，用 \(\mathbf 1_{\{j\}}:[n]\to[2]\) 检验又可知其取值必须满足 (2)。这证明了 (1)，也证明第三层已唯一决定全部更高层。

**限制映射。** 对非空 \(X\)，其像与纤维如下。

- 若 \(m=k\) 或 \(m\ge k\ge3\)，在 (1) 的对应下是恒等映射，像为全体，每个纤维都是单点。
- 若 \(m\ge3,\ k=2\)，映射是 \(\operatorname{Ult}(X)\hookrightarrow\mathcal C(X)\)。一个二元记录的纤维是单点，当且仅当它的选择族是超滤子，等价地，它在每个三块分划中恰选一块。其余纤维为空。
- 若 \(m>1,\ k=1\)，像是唯一的第一层记录，因为任意 \(x\in X\) 都给出点值记录。其纤维在 \(m\ge3\) 时为 \(\operatorname{Ult}(X)\)，在 \(m=2\) 时可明确写为 \(\prod_{P\in\mathcal D(X)}P\)，其中
  \[
  \mathcal D(X)=\bigl\{\{A,A^c\}:\varnothing\ne A\subsetneq X\bigr\}.
  \]
  这是因为每个非平凡的无序二分划可独立选择一侧。

对 \(h:X\to Y\)，由 \(\mathbf 1_B\circ h=\mathbf 1_{h^{-1}(B)}\)，第二层及以上的映射统一写为
\[
h_*\mathcal S=\{B\subseteq Y:h^{-1}(B)\in\mathcal S\}.
\tag{3}
\]
对超滤子，(2) 也直接给出此式。第一层的映射由唯一性确定。逆像保持恒等与复合所要求的关系，故这些映射给出函子。由逐层定义还有
\[
q_{m,k}R_m(h)=R_k(h)q_{m,k},\qquad
q_{k,\ell}q_{m,k}=q_{m,\ell},\qquad
R_m(h)\eta_{m,X}=\eta_{m,Y}\circ h.
\]
点值记录从第二层起对应于 \(\delta_x=\{A\subseteq X:x\in A\}\)，遗忘测试仍给出同一点的点值记录。这些等式也覆盖空定义域。

### 有限 \(G\) 集合

设 \(X\) 有限且非空，\(H\) 是 \(G\) 在 \(\operatorname{Sym}(X)\) 中的像，\(b\) 是 \(H\) 在 \(\mathcal D(X)\) 上的轨道数。令 \(E\) 表示每个 \(\sigma\in H\) 都至少有一个奇长度循环，长度 \(1\) 也计入。则
\[
|R_m(X)^G|=
\begin{cases}
1,&m=1,\\
2^b,&m=2\text{ 且 }E\text{ 成立},\\
0,&m=2\text{ 且 }E\text{ 不成立},\\
|X^G|,&3\le m\le\infty.
\end{cases}
\tag{4}
\]

第二层的不动记录须在每个二分划上等变地选择一侧。若某个 \(\sigma\) 将 \(A\) 送到 \(A^c\)，它交换该二分划的两侧，选择就不可能。若无这样的 \(\sigma,A\)，则每个轨道代表的稳定子都保持其两侧，任选一侧后即可通过群作用唯一地传到整个轨道。这给出 \(2^b\) 个选择。对有限非空 \(X\)，等式 \(\sigma A=A^c\) 要求沿每个循环交替归入两侧，故每个循环长度都必须是偶数。反过来，若每个循环都是偶长度，逐循环交替选择就构造出这样的 \(A\)。这证明了判准 \(E\)。

当 \(E\) 成立时，也可从循环数 \(c(\sigma)\) 直接计算
\[
b=\frac{1}{2|H|}\sum_{\sigma\in H}\bigl(2^{c(\sigma)}-2\bigr).
\]
事实上，\(\sigma\) 保持的子集都是它的循环的并。去掉空集与全集后，每两个互补的稳定子集给出一个稳定二分划，且 \(E\) 排除了交换两侧的情形。对有限群 \(H\) 作用的有限集合 \(\mathcal D(X)\) 使用轨道计数公式即得上式。

有限非空集上的超滤子在单点分划中选中唯一的 \(\{x\}\)，故等于 \(\delta_x\)。由 \(g_*\delta_x=\delta_{gx}\)，它不动恰当 \(x\in X^G\)。这证明了 (4) 的最后一行。

因此在有限 \(X\) 上，各层不动集合的限制映射也完全确定。第三层及以上之间是 \(X^G\) 上的恒等映射。从这些层限制到第二层是 \(x\mapsto\delta_x\)，每个像点有唯一原像，其余点的纤维为空。限制到第一层时，唯一目标点的纤维是整个源不动集合，源为空时像为空。同层限制都是恒等映射。

更一般地，对任意 \(X\)，**第三层及以上的每个不动记录都唯一延拓为完整不动记录。第二层不动记录可延拓当且仅当它的选择族是超滤子，此时延拓也唯一**，因为 (3) 保持这个超滤子。非空 \(X\) 上第一层记录的全部延拓就是 \(R_\infty(X)^G\)，其一般存在判准如下节所示。在有限 \(X\) 上，这些延拓恰由 \(X^G\) 参数化。层数界是锐利的。例如 \(S_3\) 自然作用在三点集上，选择含至少两点的一侧给出第二层不动记录，而 \(X^G=\varnothing\)，所以第一层和第二层都有不动记录，却都没有完整不动记录可供延拓。

## 2. 完整不动记录的空间

把 \(R_\infty(X)\) 按 (2) 识别为 \(\operatorname{Ult}(X)\)，空集上两者也都为空。对 \(A\subseteq X\) 记
\[
\widehat A=\{\mathcal U:A\in\mathcal U\}.
\]
由 (2)，观察 \(r_n(f)=j\) 的原像是 \(\widehat{f^{-1}(\{j\})}\)，而每个 \(\widehat A\) 都能由二元测试得到。这些集合对有限交封闭，且 \(\widehat A\) 的补集是 \(\widehat{A^c}\)，所以它们恰给出观察拓扑的一组开闭基。

对有限的 \(F\subseteq G\)，记
\[
D_X(F)=\{x\in X:gx=x\text{ 对每个 }g\in F\},\qquad D_X(\varnothing)=X.
\]
完整不动记录的描述为
\[
\boxed{\displaystyle R_\infty(X)^G=\bigcap_{F\subseteq G\ {\rm 有限}}\widehat{D_X(F)}.}
\tag{5}
\]

为证此式，先固定 \(g\in G\)，令 \(D=D_X(\{g\})\)。若 \(D\in\mathcal U\)，则 \(A\) 与 \(g^{-1}A\) 在 \(D\) 上一致，故二者同时属于或同时不属于 \(\mathcal U\)。由 (3) 得 \(g_*\mathcal U=\mathcal U\)。

反过来，\(X\setminus D\) 可以分成至多三个颜色类，使每个颜色类 \(C\) 都满足 \(C\cap gC=\varnothing\)。为此，在 \(g\) 的每条非单点轨道上选一个起点。无限轨道按 \(\mathbb Z\) 编号后交替着两色，有限偶循环也交替着两色。在有限奇循环上，前面偶数个点交替着两色，最后一点用第三色。若 \(D\notin\mathcal U\)，则 \(X\setminus D\in\mathcal U\)，其中必有一个颜色类 \(C\) 属于 \(\mathcal U\)。若此时 \(g_*\mathcal U=\mathcal U\)，则 \(gC\) 也属于 \(\mathcal U\)，与二者不交矛盾。于是 \(g_*\mathcal U=\mathcal U\) 当且仅当 \(D\in\mathcal U\)。对所有 \(g\) 应用该结论并取有限交，即得 (5)。

特别地，
\[
R_\infty(X)^G\ne\varnothing
\quad\Longleftrightarrow\quad
D_X(F)\ne\varnothing\quad\text{对每个有限 }F\subseteq G.
\tag{6}
\]
必要性来自超滤子的真性。充分性来自 \(D_X(F)\cap D_X(K)=D_X(F\cup K)\)，故右侧条件使这些集合具有有限交性质。在 ZFC 中，它们生成的真滤子可由超滤子引理延拓为超滤子，再应用 (5)。取 \(F=\varnothing\) 已覆盖空底集。这也是第一层不动记录在非空 \(X\) 上可延拓的准确条件。

还可以直接从作用构造一个布尔代数，得到不依赖于环境空间的拓扑分类。在 \(\mathcal P(X)\) 上令
\[
A\sim B
\quad\Longleftrightarrow\quad
A\cap D_X(F)=B\cap D_X(F)\quad\text{对某个有限 }F\subseteq G.
\]
把有限见证取并即可验证传递性以及与布尔运算的相容性。令 \(\mathfrak A_G(X)=\mathcal P(X)/{\sim}\)。则有典范同胚
\[
R_\infty(X)^G\ \cong\ \operatorname{Stone}(\mathfrak A_G(X)),
\tag{7}
\]
其中右端是该布尔代数的真超滤子空间。事实上，由 (5)，在不动超滤子中，\(A\) 的成员资格只依赖于 \([A]\)，所以它给出商代数上的超滤子。反之，将商代数上的超滤子沿商映射取逆像就得到 \(X\) 上的超滤子，且它包含每个 \(D_X(F)\)，因为 \([D_X(F)]=[X]\)。两构造互逆，商代数中由 \([A]\) 给出的基本开集恰对应于 \(\widehat A\cap R_\infty(X)^G\)，故为同胚。若某个 \(D_X(F)\) 为空，则商代数中 \(0=1\)，其真超滤子空间也为空。

### 点值记录的闭包与群的分类

对任何 \(S\subseteq X\)，都有 \(\overline{\eta_{\infty,X}(S)}=\widehat S\)。一方面，\(\widehat S\) 是包含这些点值记录的闭集。另一方面，若 \(\mathcal U\in\widehat S\)，则对每个包含它的基本邻域 \(\widehat A\)，都有 \(A\cap S\in\mathcal U\)。取 \(x\in A\cap S\)，即得邻域中的点值记录 \(\delta_x\)。

因此所求闭包是 \(\widehat{X^G}\)，并且
\[
\boxed{\displaystyle
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\quad\Longleftrightarrow\quad
D_X(F)=X^G\ \text{对某个有限 }F\subseteq G.}
\tag{8}
\]
因为 \(X^G\subseteq D_X(F)\) 对所有 \(F\) 成立，右侧若成立，结论立即来自 (5)。若右侧不成立，则每个 \(D_X(F)\setminus X^G\) 都非空，这些集合有有限交性质。延拓所得超滤子包含所有 \(D_X(F)\) 以及 \(X\setminus X^G\)，从而给出闭包之外的不动记录。

**对每个 \(G\) 集合都满足该闭包等式的群，恰是有限生成群。** 若 \(F\) 是有限生成集，固定 \(F\) 中每个元素的点就被整个群固定，故 (8) 适用。若 \(G\) 非有限生成，取
\[
X=\coprod_{H\le G,\ H\ {\rm 有限生成}}G/H
\]
并赋予左平移作用。指标是 \(\mathcal P(G)\) 的一个子集。每个这样的 \(H\) 都是真子群，而陪集 \(aH\) 的稳定子为 \(aHa^{-1}\)，故 \(X^G=\varnothing\)。但每个有限 \(F\subseteq G\) 都固定分量 \(G/\langle F\rangle\) 中的基准陪集 \(\langle F\rangle\)。由 (6)，该作用有完整不动记录。

**可数例子**可取 \(X=\mathbb N\)，让所有有限支撑置换组成的群 \(G\) 自然作用。这个群是各有限对称群 \(\operatorname{Sym}([n])\) 延拓为恒等后所得的并，因此可数。每个点都能被某个对换移动，故 \(X^G=\varnothing\)。每个 \(g\) 的不动点集都是余有限集，所以每个非主超滤子都由 (5) 给出不动记录。这里用到，含有有限集的超滤子必含其中一个单点，因而非主超滤子包含一切余有限集。主超滤子则因没有全局不动点而全部排除。因此该例的**全部不动记录恰为由 (2) 给出的所有非主超滤子**，它们存在，因为 \(\mathbb N\) 上的余有限滤子是真滤子。其空间即 \(\operatorname{Stone}(\mathcal P(\mathbb N)/\mathrm{Fin})\)。事实上，每个 \(D_X(F)\) 都余有限，而任意有限个点都能由有限多个对换的支撑覆盖，故 (7) 中的等价关系恰是对称差有限。

## 3. 乘积比较

令 \(Z=\prod_{i\in I}X_i\)。投影 \(p_i\) 等变，由函子性，\(p_{i*}\) 将不动记录送到不动记录。又由 (3)，对任意 \(B\subseteq X_i\) 有
\[
(p_{i*})^{-1}(\widehat B)=\widehat{p_i^{-1}(B)}.
\]
故每个坐标映射在不动子空间上连续，\(\Pi_{(X_i)}\) 良定义且对乘积拓扑连续。

**比较映射对任意群和任意集合指标族都是满射。** 给定目标中的一族 \((\mathcal U_i)_{i\in I}\)，在 \(Z\) 上取以下集合族
\[
\bigl\{p_i^{-1}(A):i\in I,\ A\in\mathcal U_i\bigr\}
\ \cup\
\bigl\{D_Z(F):F\subseteq G\text{ 有限}\bigr\},
\qquad
D_Z(F)=\prod_{i\in I}D_{X_i}(F).
\]
它具有有限交性质。具体地，将一次有限交中出现的所有 \(F\) 取并为 \(F_0\)。对每个坐标 \(i\)，将 \(D_{X_i}(F_0)\) 与该坐标上指定的有限多个 \(A\) 相交。由 (5)，参与相交的集合都属于 \(\mathcal U_i\)，故所得集合非空。用选择公理在所有坐标上各取一点，即得所需有限交中的元素。

将此族延拓为超滤子 \(\mathcal W\)。它包含所有 \(D_Z(F)\)，故由 (5) 不动。每个 \(p_{i*}\mathcal W\) 包含 \(\mathcal U_i\)，两者均为真超滤子，故相等。这证明了满射性。若目标为空，良定义性已推出源也为空，特别涵盖有空因子的情形。若 \(I=\varnothing\)，则 \(Z\) 是单点集，两端均为单点，比较映射为双射。

### 两个因子

**对任意群，至少一个因子有限时，比较映射为双射。** 空因子的情形已处理。交换因子后可设 \(X\) 有限且非空。给定目标中的一对记录，第一坐标必为某个 \(x\in X^G\) 的 \(\delta_x\)，记第二坐标为 \(\mathcal V\)。任何具有这两个边缘超滤子的 \(\mathcal W\) 都包含 \(\{x\}\times Y\)。因此对任意 \(A\subseteq X\times Y\)，记 \(A_x=\{y:(x,y)\in A\}\)，便有
\[
A\in\mathcal W\quad\Longleftrightarrow\quad A_x\in\mathcal V.
\]
这是因为 \(A\) 与 \(p_Y^{-1}(A_x)\) 在 \(\{x\}\times Y\) 上一致。这证明唯一性，也给出显式逆像，即将 \(\mathcal V\) 沿等变映射 \(y\mapsto(x,y)\) 推前。

**对平凡群，比较映射为单射当且仅当 \(X,Y\) 至少一个有限。** 为证必要性，先在 \(\mathbb N\) 上取非主超滤子 \(\mathcal U\)。在 \(\mathbb N^2\) 上构造两个边缘都为 \((\mathcal U,\mathcal U)\) 的超滤子。

- 令 \(\mathcal W_0\) 为 \(\mathcal U\) 沿 \(n\mapsto(n,n)\) 的推前。它包含对角线 \(\Delta\)。
- 令 \(\mathcal W_1\) 延拓所有 \(A\times B\)（\(A,B\in\mathcal U\)）和 \(\mathbb N^2\setminus\Delta\) 组成的族。有限多个这样的矩形相交后，两边仍是 \(\mathcal U\) 中的无限集，故能从两边取到不同的数。这验证了有限交性质。由矩形 \(A\times\mathbb N\) 和 \(\mathbb N\times B\) 可知两个边缘都是 \(\mathcal U\)。

两者对 \(\Delta\) 的选择不同。若 \(X,Y\) 均无限，在 ZFC 中可取单射 \(u:\mathbb N\hookrightarrow X\)、\(v:\mathbb N\hookrightarrow Y\)。将两个超滤子沿 \(u\times v\) 推前，它们仍由集合 \((u\times v)(\Delta)\) 区分，因为该集合的逆像恰为 \(\Delta\)。它们却有相同的边缘 \((u_*\mathcal U,v_*\mathcal U)\)，故比较映射不是单射。

最后，**\(X^G=Y^G=\varnothing\) 不能推出单射性。** 取上一节的有限支撑置换群，并令 \(X=Y=\mathbb N\) 都带自然作用。上面构造的 \(\mathcal W_0,\mathcal W_1\) 在对角作用下都不动。事实上，对每个 \(g\)，其在 \(\mathbb N\) 上的不动点集 \(D\) 余有限，故属于共同边缘 \(\mathcal U\)。于是 \(D\times\mathbb N\) 和 \(\mathbb N\times D\) 都属于这两个超滤子，其交 \(D\times D\) 正是 \(g\) 在乘积上的不动点集。由 (5) 即得所言。这样，两个因子均无全局不动点，而两个不同的完整不动记录具有相同的像。