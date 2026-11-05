记 \(\operatorname{Ult}(X)\) 为 \(X\) 上的所有**真超滤子**；特别地，\(\operatorname{Ult}(\varnothing)=\varnothing\)。下文的有限生成子群包括平凡子群，有限集合也允许为空。

## 1. 截断记录、限制映射及有限作用

### 1.1 任意底集上的分类

首先，若 \(X=\varnothing\)，则 \(\operatorname{Map}(X,[0])\) 是单点集，故所要求的 \(r_0:\operatorname{Map}(X,[0])\to[0]\) 不存在。因此
\[
R_m(\varnothing)=\varnothing\qquad\text{对每个 }m.
\]

以下先设 \(X\ne\varnothing\)。令
\[
\mathcal Q(X)=
\left\{\mathcal F\subseteq\mathcal P(X):
X\in\mathcal F,\quad
\text{对每个 }A\subseteq X,\ 
A,A^c\text{ 恰有一个属于 }\mathcal F
\right\}.
\]
其中补集均相对于 \(X\)。有自然双射
\[
\boxed{
R_1(X)\cong\{*\},\qquad
R_2(X)\cong\mathcal Q(X),\qquad
R_m(X)\cong\operatorname{Ult}(X)\quad(m\ge3).
}
\]
这里 \(m\ge3\) 包括 \(m=\infty\)。

这些双射的构造如下。对 \(A\subseteq X\)，写 \(\chi_A:X\to[2]\) 为其示性函数。二元记录 \(r\) 对应
\[
\mathcal F_r=\{A\subseteq X:r_2(\chi_A)=1\}.
\]
反之，\(\mathcal F\in\mathcal Q(X)\) 决定 \(r_2(\chi_A)\) 是否为 \(1\)，而 \(r_1\) 唯一。

对于超滤子 \(\mathcal U\)，对应的完整记录由下式给出：对 \(n\ge1\) 和 \(f:X\to[n]\)，
\[
r_n(f)=\text{唯一满足 }f^{-1}\{j\}\in\mathcal U\text{ 的 }j\in[n].
\]
这样的 \(j\) 存在且唯一，因为有限分割中恰有一个部分属于超滤子。由于 \(X\ne\varnothing\)，没有 \(X\to[0]\) 的映射，所以 \(r_0\) 唯一。

**证明分类。** 对 \(m=1\)，唯一的 \(1\)-值测试只能输出 \(0\)。对 \(m=2\)，由 \([2]\) 上的交换映射得到
\[
A\in\mathcal F_r\iff A^c\notin\mathcal F_r,
\]
由常值测试得到 \(X\in\mathcal F_r\)。反过来，\([2]\to[2]\) 只有恒等、交换和两个常值映射，故 \(\mathcal Q(X)\) 的每个成员都给出合法二元记录。

现在设 \(m\ge3\)。任意三部分分割对应一个 \(f:X\to[3]\)；通过把某一部分合并为 \(1\)、其他部分合并为 \(0\)，可知记录选中的那一部分恰属于 \(\mathcal F_r\)。特别地，两个不交集合不能都属于 \(\mathcal F_r\)。

若 \(A,B\in\mathcal F_r\)，考虑分割
\[
A\cap B,\qquad A\setminus B,\qquad X\setminus A.
\]
由于 \(A\in\mathcal F_r\)，三元记录选中的必是前两部分之一；若选中 \(A\setminus B\)，它便与 \(B\in\mathcal F_r\) 不交，矛盾。因此 \(A\cap B\in\mathcal F_r\)。由交封闭性和互补二选一性质还得向上封闭：若 \(A\in\mathcal F_r\)、\(A\subseteq B\) 而 \(B\notin\mathcal F_r\)，则 \(B^c\in\mathcal F_r\)，从而 \(\varnothing\in\mathcal F_r\)，矛盾。所以 \(\mathcal F_r\) 是真超滤子。

最后，对任意允许的 \(n\ge1\)，将 \(f:X\to[n]\) 与“只在 \(j\) 处取值 \(1\)”的映射 \([n]\to[2]\) 复合，得到
\[
r_n(f)=j\iff f^{-1}\{j\}\in\mathcal F_r.
\]
因此所有较高测试都被二元数据唯一决定。反过来，上述超滤子构造满足所有后处理相容性：若选中的 \(f\)-纤维是 \(j\)，它包含于 \(a\circ f\) 的 \(a(j)\)-纤维，后者因而属于超滤子。证毕。

### 1.2 所有遗忘映射及自然性

在上述标识下，对 \(X\ne\varnothing\)：

- \(q_{m,1}\) 的目标是单点，其唯一纤维是整个 \(R_m(X)\)。
- 若 \(m\ge3\)，则
  \[
  q_{m,2}:\operatorname{Ult}(X)\hookrightarrow\mathcal Q(X)
  \]
  是包含映射。其像恰为对有限交封闭的 \(\mathcal F\in\mathcal Q(X)\)；像中各点的纤维为单点，其余纤维为空。
- 若 \(m\ge k\ge3\)，则 \(q_{m,k}\) 在超滤子标识下为恒等双射。
- \(q_{m,m}\) 为恒等映射。

对于空 \(X\)，所有相关集合及映射均为空。

对任意 \(h:X\to Y\)，在二元族或超滤子的标识下，
\[
h_*\mathcal F
=\{B\subseteq Y:h^{-1}(B)\in\mathcal F\}.
\]
这是 \(\mathcal Q\) 中的成员；若 \(\mathcal F\) 是超滤子，它也是超滤子。这个公式直接由示性函数得到，并说明
\[
q_{m,k,Y}\,R_m(h)=R_k(h)\,q_{m,k,X}.
\]
点值记录在 \(m\ge2\) 时对应主超滤子
\[
\mathcal U_x=\{A\subseteq X:x\in A\},
\]
而 \(m=1\) 时所有点给出同一记录。并且
\[
R_m(h)\eta_{m,X}=\eta_{m,Y}h.
\]
若 \(X=\varnothing\)，这些等式在空定义域上成立。

### 1.3 不动二元记录：一般描述与有限计数

先给出对任意非空 \(G\)-集合 \(X\) 的描述。\(G\) 作用于 \(\mathcal P(X)\)，补集在轨道集
\[
O=\mathcal P(X)/G
\]
上诱导一个对合。二元记录不动，当且仅当其对应的 \(\mathcal F\) 在每个 \(G\)-轨道上取相同的成员资格。因此：

- 如果该补集对合有不动轨道，则 \(R_2(X)^G=\varnothing\)。
- 否则，每对互补轨道中必须选择一个；包含 \(X\) 的轨道与包含 \(\varnothing\) 的轨道所成的那一对，必须选择前者。若 \(D\) 是所有互补轨道对之集，\(d_0\) 是这一指定对，则
  \[
  |R_2(X)^G|=2^{|D\setminus\{d_0\}|}.
  \]

补集对合有不动轨道，当且仅当存在 \(g\in G\) 和 \(A\subseteq X\) 使 \(gA=A^c\)。这又当且仅当该置换 \(g_X\) 的每个轨道都是无限轨道或偶数长度的有限轨道。必要性来自沿轨道交替属于 \(A,A^c\)；充分性则是在每个这样的轨道上交替着色，使用选择公理选取轨道代表。因此
\[
\boxed{
R_2(X)^G\ne\varnothing
\iff
\text{每个 }g\in G\text{ 在 }X\text{ 上至少有一个奇数长度的有限轨道}.
}
\]

现在设 \(X\) 是有限 \(G\)-集合。若 \(X=\varnothing\)，每个 \(R_m(X)^G\) 都为空。若 \(X\ne\varnothing\)，令 \(H\) 为 \(G\) 在 \(X\) 上的有限置换像，并记
\[
c(h)=h\text{ 在 }X\text{ 上的循环个数},\qquad
b=\frac1{|H|}\sum_{h\in H}2^{c(h)}.
\]
Burnside 引理适用于有限群 \(H\) 作用于有限集 \(\mathcal P(X)\)；因为被 \(h\) 固定的子集恰是 \(h\)-循环的并，所以 \(b=|\mathcal P(X)/H|\)。于是精确基数为
\[
\boxed{
|R_m(X)^G|=
\begin{cases}
1,&m=1,\\[1mm]
0,&m=2\text{ 且某个 }h\in H\text{ 的循环全为偶数长度},\\[1mm]
2^{b/2-1},&m=2\text{ 且每个 }h\in H\text{ 有奇数长度循环},\\[1mm]
|X^G|,&m\ge3.
\end{cases}}
\]
在第三行中，补集对合无不动轨道，故 \(b\) 为偶数；减去的 \(1\) 对应必须选取 \(X\) 而非 \(\varnothing\) 的那一对。

最后一行成立是因为有限集上的每个超滤子都是主超滤子：有限的单点分割中必有一个单点属于超滤子。主超滤子 \(\mathcal U_x\) 不动当且仅当 \(x\in X^G\)。

这些不动集合上的限制映射完全如下：

- 在 \(m\ge k\ge3\) 时，它们均标识为 \(X^G\) 上的恒等映射。
- 在 \(m\ge3,k=2\) 时，映射把 \(x\in X^G\) 送到
  \[
  \{A\subseteq X:x\in A\}\in R_2(X)^G.
  \]
  这是单射；其像外的二元不动记录没有不动的较高延拓。
- 到 \(R_1(X)^G=\{*\}\) 的限制是常值映射，其唯一纤维就是整个定义域，定义域允许为空。
- 同层限制为恒等映射。

因此，对有限非空 \(X\)，唯一的一元不动记录可延拓为完整不动记录，当且仅当 \(X^G\ne\varnothing\)；二元不动记录可延拓，当且仅当它是某个 \(x\in X^G\) 的主记录；三元及以上记录都有唯一完整延拓。

更一般地，任意 \(X\) 上，二元不动记录可延拓为完整不动记录，当且仅当其 \(\mathcal Q(X)\)-族对有限交封闭；延拓唯一。一元不动记录的完整延拓范围由下一节的非空判准精确给出。

---

## 2. 完整不动记录及其空间

写
\[
\beta X=\operatorname{Ult}(X),\qquad
\widehat A=\{\mathcal U\in\beta X:A\in\mathcal U\}.
\]
第一部分的分类是拓扑同胚：原拓扑中的观察满足
\[
\{\mathcal U:r_n(f)=j\}=\widehat{f^{-1}\{j\}},
\]
反过来，每个 \(\widehat A\) 由二元观察 \(\chi_A\) 给出。这正是布尔代数 \(\mathcal P(X)\) 的 Stone 空间拓扑；包括 \(X=\varnothing\) 时的空空间。

### 2.1 置换引理

若 \(T:X\to X\) 是置换，则
\[
\boxed{
T_*\mathcal U=\mathcal U
\iff
\operatorname{Fix}(T)\in\mathcal U.
}
\]

证明右推左：\(A\) 与 \(T^{-1}A\) 在 \(\operatorname{Fix}(T)\) 上相同，故它们是否属于 \(\mathcal U\) 相同。

证明左推右：使用选择公理，可将非不动点集分成 \(C_0,C_1,C_2\)，使
\[
T(C_j)\cap C_j=\varnothing\quad(j=0,1,2).
\]
具体地，在无限循环和偶数有限循环上交替用两色；在奇数有限循环上，除最后一个点外交替用两色，最后一个点用第三色。若非不动点集属于 \(T\)-不变超滤子，则有限并中的某个 \(C_j\) 属于它，继而 \(T(C_j)\) 也属于它，与二者不交矛盾。

对有限 \(F\subseteq G\) 写
\[
X^F=\{x\in X:gx=x\text{ 对每个 }g\in F\}.
\]
置换引理因此给出
\[
\boxed{
R_\infty(X)^G
\cong
\{\mathcal U\in\beta X:X^F\in\mathcal U
\text{ 对每个有限 }F\subseteq G\}.
}\tag{1}
\]

这也是由作用直接构造的 Stone 空间。具体定义理想
\[
\mathcal I_G=
\{A\subseteq X:\text{存在有限 }F\subseteq G,\ A\cap X^F=\varnothing\}.
\]
它对取子集及有限并封闭，因为 \(X^{F\cup E}=X^F\cap X^E\)。式 (1) 中的超滤子恰是避开 \(\mathcal I_G\) 的超滤子，所以
\[
\boxed{
R_\infty(X)^G\cong
\operatorname{Stone}\bigl(\mathcal P(X)/\mathcal I_G\bigr).
}
\]
若理想不真，则商是退化布尔代数，其 Stone 空间为空。该同胚由商映射的超滤子逆像给出，并保留基本开闭集。

### 2.2 非空判准和有限层延拓

式 (1) 中的集合族满足
\[
X^{F_1}\cap\cdots\cap X^{F_s}=X^{F_1\cup\cdots\cup F_s}.
\]
由 ZFC 中的超滤子延拓定理，它包含于某个超滤子当且仅当所有这些集合非空。因此
\[
\boxed{
R_\infty(X)^G\ne\varnothing
\iff
X^F\ne\varnothing\quad\text{对每个有限 }F\subseteq G.
}\tag{2}
\]
等价地，\(G\) 的每个有限生成子群都在 \(X\) 上有不动点。取 \(F=\varnothing\) 也核验了空底集：此时要求 \(X\ne\varnothing\)。

所以对任意非空 \(X\)，唯一的一元不动记录可延拓为完整不动记录，当且仅当 (2) 成立；它的所有完整延拓恰是式 (1) 中的超滤子。二元及以上层的延拓范围已在第一部分给出。

### 2.3 不动点记录的闭包

在 \(\beta X\) 中，
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}
=
\{\mathcal U\in\beta X:X^G\in\mathcal U\}
=\widehat{X^G}.
}\tag{3}
\]
事实上，若 \(X^G\in\mathcal U\)，则包含 \(\mathcal U\) 的每个基本邻域 \(\widehat A\) 都满足 \(A\cap X^G\ne\varnothing\)，因而包含一个不动点的主超滤子。反之，若 \(X^G\notin\mathcal U\)，基本邻域 \(\widehat{X\setminus X^G}\) 与所有这些主超滤子不交。式 (3) 也适用于 \(X^G=\varnothing\)。

式 (3) 总包含于 \(R_\infty(X)^G\)。二者相等的充要条件是
\[
\boxed{
\exists\text{ 有限 }F\subseteq G\quad X^F=X^G.
}\tag{4}
\]
若 (4) 成立，式 (1) 中每个超滤子都包含 \(X^G\)。反之，若所有 \(X^F\setminus X^G\) 非空，它们构成具有有限交性质的族；将其延拓为超滤子，得到满足 (1) 而不包含 \(X^G\) 的记录。

哪些群对**每个** \(G\)-集合都满足所问闭包等式？答案恰是**有限生成群**。若 \(G\) 由有限 \(F\) 生成，则对每个作用有 \(X^F=X^G\)。

反之，若 \(G\) 非有限生成，令 \(\mathcal H\) 为其所有有限生成子群之集，取
\[
X=\coprod_{H\in\mathcal H}G/H
\]
并令 \(G\) 左乘。每个 \(H\in\mathcal H\) 都是 \(G\) 的真子群，故 \(X^G=\varnothing\)。但对每个有限 \(F\subseteq G\)，在 \(H=\langle F\rangle\) 所对应分量中，陪集 \(H\) 被 \(F\) 固定。由 (2)，\(R_\infty(X)^G\ne\varnothing\)，而所求闭包为空。

### 2.4 群和底集均可数的具体例子

令
\[
G=\bigoplus_{j\in\mathbb N}C_2,\qquad
G_n=\bigoplus_{j<n}C_2,\qquad
X=\coprod_{n\in\mathbb N}X_n,\quad X_n=G/G_n,
\]
\(G\) 在每个分量上作平移。\(G\) 和 \(X\) 都可数。由于每个 \(G_n\ne G\)，没有全局不动点。

记 \(\pi:X\to\mathbb N\) 为分量指标。对 \(g\in G\)，令 \(d(g)\) 为满足 \(g\in G_{d(g)}\) 的最小整数，则
\[
\operatorname{Fix}(g)=\coprod_{n\ge d(g)}X_n.
\]
而所有正整数 \(N\) 均由某个基元的 \(d(g)=N\) 实现。故这个例子的**全部**不动记录恰对应于
\[
\boxed{
\{\mathcal U\in\operatorname{Ult}(X):
\pi_*\mathcal U\text{ 是 }\mathbb N\text{ 上的非主超滤子}\}.
}\tag{5}
\]
对其中每个 \(\mathcal U\)，记录在有限测试 \(f:X\to[n]\) 上的输出，是唯一使 \(f^{-1}\{j\}\in\mathcal U\) 的 \(j\)。

例如，取 \(\mathbb N\) 上任意非主超滤子 \(\mathcal V\)，令
\[
s(n)=(n,G_n)\in X_n.
\]
则 \(s_*\mathcal V\) 满足 (5)。非主超滤子存在，是因为余有限滤子可在 ZFC 中延拓为超滤子。

还可不通过 \(X\) 上的超滤子来参数化 (5)。对每个非主 \(\mathcal V\)，令
\[
\mathcal B_{\mathcal V}
=\prod_n\mathcal P(X_n)\big/\!\sim_{\mathcal V},
\quad
(A_n)\sim_{\mathcal V}(B_n)
\iff\{n:A_n=B_n\}\in\mathcal V.
\]
所有不动记录与所有对
\[
\bigl(\mathcal V,\mathcal W\bigr),
\quad
\mathcal V\text{ 为 }\mathbb N\text{ 上非主超滤子},\quad
\mathcal W\in\operatorname{Ult}(\mathcal B_{\mathcal V})
\]
一一对应：对应的 \(\mathcal U\) 由
\[
A\in\mathcal U
\iff [(A\cap X_n)_n]_{\mathcal V}\in\mathcal W
\]
定义。确实，该 \(\mathcal U\) 投影为 \(\mathcal V\)；反过来，若 \(\pi_*\mathcal U=\mathcal V\)，在一个 \(\mathcal V\)-大的指标集上相同的两个子集在 \(\mathcal U\) 中具有相同成员资格，故 \(\mathcal U\) 唯一地下降为这样的 \(\mathcal W\)。

---

## 3. 乘积比较

### 3.1 良定义、连续和满射

每个投影 \(p_i:\prod_jX_j\to X_i\) 都是 \(G\)-等变的，所以它把不动记录送到不动记录，故 \(\Pi_{(X_i)}\) 良定义。对观察 \(f:X_i\to[n]\)，对应坐标观察的复合是
\[
r\longmapsto r_n(f\circ p_i),
\]
因此每个坐标映射连续，\(\Pi_{(X_i)}\) 连续。

**该比较映射总是满射，包括任意集合指标族。** 证明：给定目标中的一族不动超滤子 \((\mathcal U_i)_{i\in I}\)，在
\[
P=\prod_{i\in I}X_i
\]
上考虑以下子集族：
\[
p_i^{-1}(A)\quad(A\in\mathcal U_i),\qquad
P^F=\prod_{i\in I}X_i^F\quad(F\subseteq G\text{ 有限}).
\]
它具有有限交性质。事实上，有限多个柱面条件只限制有限多个指标；对每个被限制的 \(i\)，相关的有限交与 \(X_i^F\) 都属于 \(\mathcal U_i\)，故非空。未被限制的 \(i\) 也有 \(X_i^F\in\mathcal U_i\)，故非空。选择公理提供所有坐标的选择。

把该族延拓为 \(P\) 上的超滤子 \(\mathcal U\)。由包含每个 \(P^F\)，式 (1) 表明它不动；而它的第 \(i\) 个投影超滤子包含 \(\mathcal U_i\)，故等于 \(\mathcal U_i\)。若目标为空，满射性当然成立。若 \(I=\varnothing\)，源是单点集上的唯一记录，目标也是单点，故比较映射是单点间双射。

### 3.2 一个有限因子时

若 \(X\) 有限，则任意 \(X\times Y\) 上的超滤子必选择有限分割中的唯一一个纤维 \(\{x\}\times Y\)。因此它唯一形如
\[
(j_x)_*\mathcal V,\qquad j_x(y)=(x,y),\quad
x\in X,\quad\mathcal V\in\operatorname{Ult}(Y).
\]
其两个投影分别是 \(\mathcal U_x,\mathcal V\)。该超滤子对对角作用不动，当且仅当 \(x\in X^G\) 且 \(\mathcal V\) 不动：必要性由投影等变性得到；充分性由此时 \(j_x\) 等变得到。

所以，对任意群作用，**若 \(X,Y\) 至少一个有限，两因子的比较映射为双射**。这也覆盖有限因子为空时两边均为空的情况。

### 3.3 平凡群时的单射判准

平凡群时，两因子的比较映射单射的充要条件是
\[
\boxed{X\text{ 或 }Y\text{ 有限}.}
\]
充分性已证。为证必要性，设两者均无限。由 ZFC，可选单射
\(e_X:\mathbb N\to X\)、\(e_Y:\mathbb N\to Y\)，再取 \(\mathbb N\) 上非主超滤子 \(\mathcal V\)。令
\[
\mathcal U=(e_X)_*\mathcal V,\qquad
\mathcal W=(e_Y)_*\mathcal V,\qquad
\mathcal D=(e_X,e_Y)_*\mathcal V.
\]

对任意超滤子 \(\mathcal U,\mathcal W\)，定义其张量超滤子
\[
A\in\mathcal U\otimes\mathcal W
\iff
\{x\in X:\{y\in Y:(x,y)\in A\}\in\mathcal W\}\in\mathcal U.
\]
这是超滤子：截面运算保持有限交，而对补集，内层超滤子恰好将成员资格取反。其两个投影分别为 \(\mathcal U,\mathcal W\)，与 \(\mathcal D\) 相同。

但是，图集
\[
L=\{(e_X(n),e_Y(n)):n\in\mathbb N\}
\]
属于 \(\mathcal D\)，不属于 \(\mathcal U\otimes\mathcal W\)，因为 \(L\) 的每个纵截面至多是单点，而 \(\mathcal W\) 非主。所以比较映射不单射。

### 3.4 两边均无不动点时不一定单射

命题“若 \(X^G=Y^G=\varnothing\)，则两因子的比较映射单射”是**假的**。

使用 2.4 节的可数作用，令 \(Y=X\)，取其中一个不动超滤子 \(\mathcal U\)。由于 \(X^G=\varnothing\)，\(\mathcal U\) 不可能是主超滤子。令
\[
\mathcal D=d_*\mathcal U,\quad d(x)=(x,x),
\qquad
\mathcal T=\mathcal U\otimes\mathcal U.
\]
二者都对对角作用不动：对每个 \(g\)，置换引理给出 \(\operatorname{Fix}(g)\in\mathcal U\)，故
\(\operatorname{Fix}(g)\times\operatorname{Fix}(g)\) 同时属于 \(\mathcal D\) 和 \(\mathcal T\)；再应用置换引理即可。二者的两个投影都为 \(\mathcal U\)。

然而对角线 \(\Delta_X\) 属于 \(\mathcal D\)，却不属于 \(\mathcal T\)，因为其每个纵截面是单点，而 \(\mathcal U\) 非主。因此这两个不同的不动记录有相同的两个投影，比较映射不单射。