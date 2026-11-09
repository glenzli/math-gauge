以下超滤子均指不含空集的真超滤子。记 \(\operatorname{Ult}(X)\) 为 \(X\) 上所有超滤子的集合。

首先，所有 \(m\) 都有
\[
R_m(\varnothing)=\varnothing,
\]
因为 \(r_0\) 必须是从单点集 \(\operatorname{Map}(\varnothing,\varnothing)\) 到空集的映射。以下分类先假设 \(X\ne\varnothing\)。

对 \(A\subseteq X\)，写 \(A^c=X\setminus A\)。令 \(\mathscr D(X)\) 为所有满足下列条件的族 \(\mathcal A\subseteq\mathcal P(X)\)：
\[
X\in\mathcal A,\qquad \varnothing\notin\mathcal A,\qquad
A\in\mathcal A\Longleftrightarrow A^c\notin\mathcal A.
\]
这里不要求向上封闭或有限交封闭。则有规范分类
\[
\boxed{
R_m(X)\cong
\begin{cases}
\{*\},&m=1,\\
\mathscr D(X),&m=2,\\
\operatorname{Ult}(X),&3\le m\le\infty.
\end{cases}}
\tag{1}
\]

具体地，\(\mathscr D(X)\) 的一个元素，就是在每对非平凡补集
\[
\{A,A^c\},\qquad \varnothing\ne A\ne X,
\]
中独立选择一边，另将 \(X\) 选入。因此这是一个明确的二元选择乘积分类。

证明如下。\(m=1\) 时，\(r_0\) 是唯一的空映射，\(r_1\) 也被唯一确定。若 \(m\ge2\)，记 \(\chi_A:X\to[2]\) 为示性函数，定义
\[
A\in\mathcal A_r\Longleftrightarrow r_2(\chi_A)=1.
\]
由常值映射及交换 \(0,1\) 的映射可知，\(\mathcal A_r\in\mathscr D(X)\)。对任意允许的 \(n\ge1\)、\(f:X\to[n]\) 及 \(j\in[n]\)，将自然性用于 \(\{j\}\) 的示性函数，得到
\[
\boxed{r_n(f)=j\Longleftrightarrow f^{-1}(\{j\})\in\mathcal A_r.}
\tag{2}
\]
所以二色测试已经确定所有可能的高层值。

当 \(m=2\) 时，任意 \(\mathcal A\in\mathscr D(X)\) 都通过此式定义一个记录：二元集合之间的映射只有常值映射和双射，相容性恰由补集二择一保证。

当 \(m\ge3\) 时，每个三块分割恰有一块属于 \(\mathcal A_r\)。令
\(\mu(A)=1\) 当且仅当 \(A\in\mathcal A_r\)。对不交的 \(A,B\)，考察分割
\[
A,\quad B,\quad (A\cup B)^c,
\]
得到
\[
\mu(A\cup B)=\mu(A)+\mu(B).
\]
于是 \(\mu\) 单调。若 \(A,B\in\mathcal A_r\) 而 \(A\cap B\notin\mathcal A_r\)，上述可加性迫使 \(A\setminus B\in\mathcal A_r\)，这与它和 \(B\) 不交矛盾。因此 \(\mathcal A_r\) 是超滤子。

反过来，超滤子在每个有限分割中恰选一块，故式 (2) 定义所有有限测试的值。若所选细块映入某个粗块，粗块也属于超滤子，因而满足全部自然性条件。这证明了 (1)。

在这些识别下，所有遗忘映射的像和纤维如下：

- \(q_{m,1}\) 的像是唯一的一层记录，其唯一纤维是整个 \(R_m(X)\)。
- \(q_{2,2}\) 是恒等映射。
- \(m\ge3\) 时，\(q_{m,2}\) 是
  \[
  \operatorname{Ult}(X)\hookrightarrow\mathscr D(X).
  \]
  目标族若是超滤子，其纤维为单点；否则纤维为空。
- \(m\ge k\ge3\) 时，\(q_{m,k}\) 在超滤子分类下是恒等映射。

当 \(X=\varnothing\) 时，这些都是空集之间的映射。

对集合映射 \(h:X\to Y\)，后两类对象上的映射均为
\[
h_*\mathcal A=\{B\subseteq Y:h^{-1}(B)\in\mathcal A\}.
\tag{3}
\]
事实上，对示性函数直接计算即可得到此式。逆像保持补集和有限交，所以它分别保持补集选择族和超滤子。一层记录之间则是唯一可能的映射。由复合计算还得到
\[
R_m(h'h)=R_m(h')R_m(h),\qquad
q_{m,k}R_m(h)=R_k(h)q_{m,k}.
\]
点记录对应主超滤子
\[
\mathcal U_x=\{A\subseteq X:x\in A\},
\]
并且
\[
R_m(h)\eta_{m,X}(x)=\eta_{m,Y}(h(x)),\qquad
q_{m,k}\eta_{m,X}(x)=\eta_{k,X}(x).
\]
不同点由二色测试分开。式 (3) 也表明，群的不动记录就是相应的 \(G\)-不变族；所有遗忘映射均为 \(G\)-等变映射。

现在设 \(X\) 是有限 \(G\)-集合。空集情形已经处理。令
\[
N=|X|>0,\qquad H=\operatorname{im}(G\to\operatorname{Sym}(X)),\qquad
t=|X^G|.
\]
这里 \(H\) 是有限群。对 \(h\in H\)，令 \(c(h)\) 为其在 \(X\) 上的循环数，包括长度为 \(1\) 的循环。

二层不动记录存在，当且仅当
\[
\boxed{\text{不存在 }h\in H\text{，使 }h\text{ 的所有循环长度均为偶数。}}
\tag{4}
\]
在此条件成立时，令
\[
b=\frac12\left(\frac1{|H|}\sum_{h\in H}2^{c(h)}-2\right).
\]
则精确基数为
\[
\boxed{
|R_m(X)^G|=
\begin{cases}
1,&m=1,\\
0,&m=2\text{ 且 (4) 不成立},\\
2^b,&m=2\text{ 且 (4) 成立},\\
t,&3\le m\le\infty.
\end{cases}}
\tag{5}
\]

为证明二层结论，令
\[
\Omega=(\mathcal P(X)\setminus\{\varnothing,X\})/H.
\]
补集在 \(\Omega\) 上诱导一个对合。不变补集选择族必须在每对互补的 \(H\)-轨道中选一个；若对合有不动轨道，则无法选择。这个障碍等价于存在 \(h,A\) 满足 \(hA=A^c\)。沿 \(h\) 的每个循环交替检查成员关系可知，这又等价于 \(h\) 的所有循环均为偶长。

无障碍时，\(\Omega\) 分为 \(b\) 对互补轨道，给出 \(2^b\) 个选择。Burnside 引理适用于有限群 \(H\) 在有限集 \(\mathcal P(X)\) 上的作用；一个 \(h\)-不变子集恰是循环的并，故共有 \(2^{c(h)}\) 个。这就给出上述 \(b\) 的公式。最后，有限非空集合上的每个超滤子都包含且只包含一个单点集，所以都是主超滤子，证明了最后一行。

有限 \(X\) 上的不动限制映射也完全确定：

- 三层及以上均识别为 \(X^G\)，它们之间的映射是恒等映射。
- 从三层及以上到二层，是 \(x\mapsto\mathcal U_x\)。像恰为固定点对应的主选择族；这些点的纤维为单点，其余纤维为空。
- 到一层的映射是常值映射，唯一目标点的纤维就是定义域；定义域为空时，像也为空。

因此，有限 \(X\) 上唯一的一层不动记录恰在 \(t>0\) 时能延拓，且有 \(t\) 个完整不动延拓；二层可延拓的不动记录恰为那 \(t\) 个主记录，每个延拓唯一；三层及以上全部唯一延拓。

下面处理任意 \(G\)-集合的完整记录。将 \(\operatorname{Ult}(X)\) 记为 \(\beta X\)，并写
\[
\widehat A=\{\mathcal U\in\beta X:A\in\mathcal U\}.
\]
由 (2)，观察 \(r_n(f)=j\) 对应的集合恰为
\[
\widehat{f^{-1}(\{j\})}.
\]
反过来，每个 \(\widehat A\) 都来自二色观察。因此题设拓扑恰是以 \(\widehat A\) 为开闭基的超滤子拓扑。

这个空间也是 \(\{0,1\}^{\mathcal P(X)}\) 中满足布尔同态等式的闭子空间：常元、补集、有限交的等式都只涉及有限个坐标。由于 \(\mathcal P(X)\) 是集合，Tychonoff 定理适用，故它是紧、零维、Hausdorff 空间，允许为空。

关键是不动超滤子满足
\[
\boxed{
\mathcal U\in(\beta X)^G
\Longleftrightarrow
\operatorname{Fix}_X(g)\in\mathcal U\quad\text{对每个 }g\in G.
}
\tag{6}
\]
先证明必要性。固定 \(g\)，将其移动点集分成三个集合 \(C_0,C_1,C_2\)，使
\[
C_j\cap gC_j=\varnothing.
\]
这样的分割存在：在每个非平凡循环上作适当三染色；偶环和双向无限轨道可交替二染色，奇环另用第三色。轨道代表的选择由 ZFC 保证。若 \(\mathcal U\) 不动，任何 \(C_j\) 属于它都会迫使不交的 \(gC_j\) 也属于它，矛盾。因此移动点集不属于它，固定点集属于它。

反之，若 \(\operatorname{Fix}_X(g)\in\mathcal U\)，则 \(A\) 与 \(g^{-1}A\) 在该固定点集上相同，所以二者同时属于或不属于 \(\mathcal U\)。这正是 \(g\mathcal U=\mathcal U\)。

这给出一个直接由作用构造的内在分类。对有限 \(F\subseteq G\)，记
\[
X^F=\bigcap_{g\in F}\operatorname{Fix}_X(g),\qquad X^\varnothing=X,
\]
并定义布尔理想
\[
\mathcal I_G(X)=
\{A\subseteq X:\exists F\subseteq G\text{ 有限},\ A\cap X^F=\varnothing\}.
\]
它向下封闭；有限并的条件可通过合并有限集 \(F\) 验证。令
\[
\mathcal B_G(X)=\mathcal P(X)/\mathcal I_G(X).
\]
也就是说，两个子集等价，当且仅当它们在某个 \(X^F\) 上相同。

由 (6)，不动超滤子恰为避开 \(\mathcal I_G(X)\) 的超滤子。因此有规范同胚
\[
\boxed{
R_\infty(X)^G
\cong \operatorname{Ult}(\mathcal B_G(X))
\cong\operatorname{Hom}_{\mathrm{BA}}(\mathcal B_G(X),\{0,1\}).
}
\tag{7}
\]
相应记录的明确公式为
\[
r_n(f)=j
\Longleftrightarrow
\phi\bigl([f^{-1}(\{j\})]\bigr)=1.
\]
拓扑相容性由开闭集 \(\{\phi:\phi([A])=1\}\) 与 \(\widehat A\) 的对应直接得到。若理想包含 \(X\)，商布尔代数满足 \(0=1\)，其超滤子空间为空。

非空判准是
\[
\boxed{
R_\infty(X)^G\ne\varnothing
\Longleftrightarrow
\forall F\subseteq G\text{ 有限},\ X^F\ne\varnothing.
}
\tag{8}
\]
等价地，每个有限生成子群在 \(X\) 上都有固定点。必要性来自 (6)。充分性方面，集合族 \(\{\operatorname{Fix}_X(g):g\in G\}\) 有有限交性质，故生成真滤子；由 Zorn 引理的超滤子扩张定理，可将其延拓为超滤子，再用 (6)。这里底集和生成族都是集合，扩张定理的条件均满足。特别地，\(X=\varnothing\) 时，取 \(F=\varnothing\) 即使条件失败。

这也确定了任意底集上的有限层不动延拓范围：若 \(X\ne\varnothing\)，唯一的一层记录能延拓，当且仅当 (8) 成立，其延拓集合就是 \(R_\infty(X)^G\)；二层不动记录能延拓，当且仅当其选择族本身是超滤子，且延拓唯一；三层及以上的不动记录全部唯一延拓。

对任意 \(S\subseteq X\)，有
\[
\overline{\eta_{\infty,X}(S)}=\widehat S.
\tag{9}
\]
若 \(S\notin\mathcal U\)，开闭邻域 \(\widehat{S^c}\) 将其与该像分开。若 \(S\in\mathcal U\)，则任何基本邻域 \(\widehat A\ni\mathcal U\) 都满足 \(A\cap S\ne\varnothing\)，从而包含某个来自 \(S\) 的主超滤子。

所以题设闭包为
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}
=\widehat{X^G}
\subseteq R_\infty(X)^G
=\bigcap_{g\in G}\widehat{\operatorname{Fix}_X(g)}.
}
\tag{10}
\]
其中等号的准确判准为
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\Longleftrightarrow
\exists F\subseteq G\text{ 有限},\ X^F=X^G.
}
\tag{11}
\]
若这样的 \(F\) 存在，任一不动超滤子都包含 \(X^F=X^G\)。反之，若不存在，则
\[
X^F\setminus X^G\ne\varnothing
\]
对所有有限 \(F\) 成立。这些集合具有有限交性质，可延拓出一个包含所有 \(\operatorname{Fix}_X(g)\) 及 \(X\setminus X^G\) 的超滤子。它不动，却不在 (10) 的闭包中。此证明也覆盖 \(X=\varnothing\)：此时取 \(F=\varnothing\)，两边均为空。

对每个 \(G\)-集合都满足该闭包等式的群，**恰为有限生成群**。有限生成时，取有限生成集 \(F\) 即可应用 (11)。若 \(G\) 不是有限生成群，取
\[
Z=\coprod_{\substack{F\subseteq G\\F\text{ 有限}}}G/\langle F\rangle
\]
及左平移作用。这是集合指标的集合并。每个 \(\langle F\rangle\) 都是真子群，所以 \(Z^G=\varnothing\)；但任意有限 \(K\subseteq G\) 都固定 \(G/\langle K\rangle\) 分量中的单位陪集。由 (8)，\(R_\infty(Z)^G\ne\varnothing\)，故闭包等式失败。

一个群和底集均可数的具体例子是
\[
G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N),\qquad X=\mathbb N,
\]
其中 \(G\) 为有限支撑置换群，取自然作用。有限支撑集合只有可数多个，每个支撑上的置换只有有限多个，故 \(G\) 可数。每个自然数都被某个换位移动，所以 \(X^G=\varnothing\)。

该例的全部不动记录恰由 \(\mathbb N\) 上的自由超滤子给出：
\[
R_\infty(\mathbb N)^G
=\{\mathcal U:\mathcal U\text{ 是 }\mathbb N\text{ 上的非主超滤子}\}.
\tag{12}
\]
事实上，每个 \(g\) 的固定点集余有限，而自由超滤子包含所有余有限集，故由 (6) 不动；主超滤子不动则要求其支点为全群固定点，这里不存在。余有限滤子是真滤子，其超滤子延拓必为自由超滤子，所以该空间非空。

所有记录均由
\[
r_n(f)=j\Longleftrightarrow f^{-1}(\{j\})\in\mathcal U
\]
给出，拓扑就是
\[
\mathbb N^*=\beta\mathbb N\setminus\mathbb N
\cong\operatorname{Ult}\bigl(\mathcal P(\mathbb N)/\mathrm{Fin}\bigr).
\]
最后一个商中，有限集理想正是 \(\mathcal I_G(\mathbb N)\)：每个移动点集有限，而每个有限集都被有限多个换位的移动点集覆盖。

最后讨论乘积比较。令 \(P=\prod_{i\in I}X_i\)。投影 \(p_i\) 是 \(G\)-等变映射，故其推前保持不动记录，证明了 \(\Pi_{(X_i)}\) 的良定义。又有
\[
\bigl(R_\infty(p_i)r\bigr)_n(f)=r_n(f\circ p_i),
\]
所以每个坐标观察的拉回仍是观察开集。因而各坐标映射连续，\(\Pi_{(X_i)}\) 对通常的乘积拓扑连续。

它对任意群和任意集合指标族都满射。给定目标点 \((\mathcal U_i)_{i\in I}\)，在 \(P\) 上考虑集合族
\[
\{p_i^{-1}(A):i\in I,\ A\in\mathcal U_i\}
\ \cup\
\{P^F:F\subseteq G\text{ 有限}\}.
\]
其中
\[
P^F=\prod_{i\in I}X_i^F.
\]
这族具有有限交性质。事实上，将有限多个约束合并后，其交为
\[
\prod_{i\in I}B_i,\qquad
B_i=
\begin{cases}
A_i\cap X_i^F,&i\text{ 受到柱集约束},\\
X_i^F,&\text{否则},
\end{cases}
\]
其中每个受约束的 \(A_i\in\mathcal U_i\)。由 (6)，\(X_i^F\in\mathcal U_i\)，所以各 \(B_i\) 非空。指标 \(I\) 是集合，ZFC 的选择公理保证该乘积非空。

将此真滤子延拓为超滤子 \(\mathcal W\)。它的各边缘恰为 \(\mathcal U_i\)，且包含每个 \(\operatorname{Fix}_P(g)\)，故由 (6) 不动，给出所需原像。

若某个 \(X_i=\varnothing\)，源和目标均为空。若 \(I=\varnothing\)，底集乘积是单点，其完整记录也是单点，目标空乘积同样是单点，比较映射为双射。

对于平凡群，两集合比较映射的单射判准是
\[
\boxed{
\beta(X\times Y)\longrightarrow\beta X\times\beta Y
\text{ 单射}
\Longleftrightarrow
X,Y\text{ 至少一个有限。}
}
\tag{13}
\]
空集已包含在有限情形中，此时两端均为空。若 \(X\) 有限非空，任一 \(\mathcal W\in\beta(X\times Y)\) 必选择唯一的切片 \(\{x\}\times Y\)。若其 \(Y\)-边缘为 \(\mathcal V\)，则
\[
A\in\mathcal W
\Longleftrightarrow
\{y:(x,y)\in A\}\in\mathcal V.
\]
所以两个边缘唯一确定 \(\mathcal W\)。

反之，若 \(X,Y\) 都无限，ZFC 保证存在互异点列 \((x_s)\)、\((y_s)\)。取 \(\mathbb N\) 上一个自由超滤子 \(\mathcal U\)，定义
\[
A\in\mathcal W_\Delta
\Longleftrightarrow
\{s:(x_s,y_s)\in A\}\in\mathcal U,
\]
以及
\[
A\in\mathcal W_\otimes
\Longleftrightarrow
\{s:\{t:(x_s,y_t)\in A\}\in\mathcal U\}\in\mathcal U.
\]
第一者是超滤子的推前；第二者逐行取超滤子值再取一次，保持常元、补集和有限交，因此也是超滤子。直接计算可知，它们的两个边缘相同，分别为
\[
(x_s)_*\mathcal U,\qquad (y_s)_*\mathcal U.
\]
但对
\[
D=\{(x_s,y_s):s\in\mathbb N\},
\]
有 \(D\in\mathcal W_\Delta\)，而 \(D\notin\mathcal W_\otimes\)，因为后一计算中的每一行都是单点集。这证明了非单射。

题末两个全称命题依次为真、假。

若至少一个因子有限，普通比较映射由 (13) 及已经证明的满射性是双射。它是 \(G\)-等变的，故其逆也等变；限制到不动点集仍是双射。这证明第一个命题，包含空因子的情形。

第二个命题可用 (12) 的同一个可数作用反驳。取
\[
G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N),\qquad X=Y=\mathbb N,
\]
并在上述构造中令 \(x_s=y_s=s\)。两个边缘都是不动的自由超滤子 \(\mathcal U\)。

这里 \(\mathcal W_\Delta,\mathcal W_\otimes\) 也都不动。更一般地，对两因子，若一个超滤子的两个边缘不动，则对每个 \(g\)，它都包含
\[
p_X^{-1}(\operatorname{Fix}_X(g))
\cap p_Y^{-1}(\operatorname{Fix}_Y(g))
=\operatorname{Fix}_{X\times Y}(g),
\]
因而由 (6) 不动。因此这两个超滤子属于比较映射的定义域，具有相同像，却在对角集的二色测试上分别取 \(1\) 和 \(0\)。同时 \(X^G=Y^G=\varnothing\)，所要求的单射性失败。