分界出现在三值测试：\(m=1\) 只检测底集是否非空，\(m=2\) 对互补子集作选择，而 \(m\ge3\) 已经完全等价于超滤。下面给出分类及各项证明。

记 \(\operatorname{Ult}(X)\) 为 \(X\) 上的超滤集合，约定超滤不含空集。使用的超滤延拓定理是：集合上的任意具有有限交性质的子集族都包含于某个超滤；这在 ZFC 中成立。

**先分类截断记录。** 若 \(X=\varnothing\)，则
\[
\operatorname{Map}(\varnothing,[0])=\{\varnothing\},
\]
不存在从它到 \([0]=\varnothing\) 的函数。因此，对所有允许的 \(m\)，
\[
R_m(\varnothing)=\varnothing.
\tag{1}
\]

以下暂设 \(X\ne\varnothing\)。定义
\[
\mathscr S(X)=
\left\{
\mathcal U\subseteq\mathcal P(X):
\varnothing\notin\mathcal U,\quad
\text{每对 }A,X\setminus A\text{ 恰有一个属于 }\mathcal U
\right\}.
\]
这里不要求向上封闭或交封闭。分类为
\[
\boxed{
R_m(X)\cong
\begin{cases}
\{\ast\},&m=1,\\
\mathscr S(X),&m=2,\\
\operatorname{Ult}(X),&3\le m\le\infty.
\end{cases}}
\tag{2}
\]

对应关系如下。对 \(m\ge2\)，令
\[
\mathcal U_r=\{A\subseteq X:r_2(\mathbf1_A)=1\}.
\tag{3}
\]
反过来，二值记录由
\[
r_2(f)=1\iff f^{-1}(1)\in\mathcal U
\]
确定；若 \(\mathcal U\) 是超滤，则完整记录由
\[
r_n(f)=\text{唯一满足 }f^{-1}(j)\in\mathcal U\text{ 的 }j\in[n]
\qquad(n\ge1)
\tag{4}
\]
确定。非空 \(X\) 的零值测试没有输入，故其 \(r_0\) 唯一。

证明分类时，一值测试显然唯一。二值测试之间的映射只有恒等、交换和常值映射；相容性恰好要求常值测试取其常值，并要求互补子集选择相反的值。因此恰好得到 \(\mathscr S(X)\)。

若允许三值测试，对任意允许空块的划分
\[
X=A_0\sqcup A_1\sqcup A_2,
\]
取对应的 \(f:X\to[3]\)，再与三个单点指示映射 \([3]\to[2]\) 复合，可知三个 \(A_j\) 中恰有一个属于 \(\mathcal U_r\)。这强制 \(\mathcal U_r\) 为超滤：

- 若 \(A\subseteq B\) 且 \(A\in\mathcal U_r\)，考察划分 \(A,B\setminus A,X\setminus B\)，得到 \(X\setminus B\notin\mathcal U_r\)，所以 \(B\in\mathcal U_r\)。
- 若 \(A,B\in\mathcal U_r\)，考察划分 \(A\cap B,A\setminus B,X\setminus A\)。第三块不被选；第二块若被选，向上封闭性会推出 \(X\setminus B\in\mathcal U_r\)，矛盾。因此 \(A\cap B\in\mathcal U_r\)。

此外，对任意允许的 \(n\)，与各单点指示映射 \([n]\to[2]\) 的相容性强制给出公式 (4)。反之，超滤在每个有限划分中恰好包含一个块；被选块在任何合并划分中仍落入被选块，故 (4) 满足全部相容条件。这证明了 (2)。

更具体地，令
\[
\mathscr C(X)=
\bigl\{\{A,X\setminus A\}:\varnothing\ne A\ne X\bigr\}.
\]
则
\[
\mathscr S(X)\cong\prod_{P\in\mathscr C(X)}P:
\]
每个互补对任选一边，再加入 \(X\)。特别地，
\[
|\mathscr S(X)|=2^{|\mathscr C(X)|}.
\tag{5}
\]

遗忘映射的像和纤维现在完全明确。对非空 \(X\)：

| 遗忘映射 | 像 | 纤维 |
|---|---|---|
| \(q_{2,1}\) | 唯一的一值记录 | \(\mathscr S(X)\) |
| \(q_{m,1}\)，\(m\ge3\) | 唯一的一值记录 | \(\operatorname{Ult}(X)\) |
| \(q_{m,2}\)，\(m\ge3\) | \(\mathscr S(X)\) 中恰好为超滤的选择族 | 像内为单点，像外为空 |
| \(q_{m,k}\)，\(m\ge k\ge3\) | 全部目标 | 每个纤维为单点 |

\(q_{m,m}\) 为恒等；空底集上的映射均为 \(\varnothing\to\varnothing\)。上述到一值层的映射总是满射，因为非空集合有主超滤。到二值层的 \(q_{m,2}\)（\(m\ge3\)）满射当且仅当 \(|X|\le2\)：至多两点时所有选择族都是主超滤；若有三个不同点，以“包含其中至少两点”为选择规则，便得到不交封闭的二值记录。

对任意 \(h:X\to Y\)，在选择族及超滤模型中，\(R_m(h)\) 都由同一公式表示：
\[
h_*\mathcal U=\{B\subseteq Y:h^{-1}(B)\in\mathcal U\}.
\tag{6}
\]
这是因为 \(\mathbf1_B\circ h=\mathbf1_{h^{-1}(B)}\)。原像保持补集和有限交，故分别保持选择族和超滤。公式也直接给出
\[
R_m(k\circ h)=R_m(k)\circ R_m(h),\qquad
q_{m,k,Y}\circ R_m(h)=R_k(h)\circ q_{m,k,X}.
\tag{7}
\]
点值记录对应主超滤
\[
\mathcal U_x=\{A\subseteq X:x\in A\},
\tag{8}
\]
且 \(h_*\mathcal U_x=\mathcal U_{h(x)}\)。这些结论在空底集情形同样成立。

现在设 \(X\) 是有限 \(G\) 集合。若 \(X=\varnothing\)，所有不动记录集合均为空。设 \(X\ne\varnothing\)，令
\[
H=\operatorname{im}(G\to\operatorname{Sym}(X)),\qquad
\Omega=H\backslash\mathcal P(X).
\]
\(H\) 是有限群，补集运算在有限集合 \(\Omega\) 上诱导一个对合。

二值记录不动，当且仅当其选择族是 \(H\)-轨道的并。因此，其存在的充要条件是
\[
\boxed{\text{不存在 }A\subseteq X,\ h\in H\text{ 使 }hA=X\setminus A.}
\tag{9}
\]
等价地：
\[
\boxed{\text{每个 }h\in H\text{ 的循环分解都至少有一个奇长度循环。}}
\tag{10}
\]
事实上，\(hA=A^c\) 要求沿每个循环交替归属 \(A,A^c\)，这恰好在所有循环长度都为偶数时可行。

若 (9) 成立，补集对合把 \(\Omega\) 分成两两配对的轨道；其中 \(\{\{\varnothing\},\{X\}\}\) 的选择被强制为 \(X\)，其他每对均可自由选择。所以精确基数为
\[
\boxed{
|R_m(X)^G|=
\begin{cases}
1,&m=1,\\[2mm]
2^{|\Omega|/2-1},&m=2\text{ 且 (9) 成立},\\
0,&m=2\text{ 且 (9) 不成立},\\
|X^G|,&m\ge3.
\end{cases}}
\tag{11}
\]
这里的轨道数也可直接计算：
\[
|\Omega|=\frac1{|H|}\sum_{h\in H}2^{c(h)},
\tag{12}
\]
其中 \(c(h)\) 是 \(h\) 在 \(X\) 上的循环数。因为一个子集被 \(h\) 固定当且仅当它是若干循环的并，固定子集有 \(2^{c(h)}\) 个；再对有限群作用于有限集合 \(\mathcal P(X)\) 使用 Burnside 引理即得 (12)。

式 (11) 最后一行来自：有限集合的每个超滤均主于唯一一点，其不动性恰好等价于该点属于 \(X^G\)。

这些有限不动集合之间的限制映射为：

- 在 \(m\ge k\ge3\) 时，识别为 \(X^G\) 后是恒等映射。
- 从 \(m\ge3\) 到二值层，是单射 \(x\mapsto\mathcal U_x\)；纤维在这些主选择族处为单点，其他处为空。
- 到一值层是唯一映射，其唯一纤维就是整个源不动集合，可能为空。

因此，对有限非空 \(X\)，唯一的一值不动记录有 \(|X^G|\) 个完整不动延拓；二值不动记录可延拓当且仅当它主于某个 \(x\in X^G\)，此时延拓唯一；三值及以上的不动记录全部唯一延拓。

**再处理完整不动记录的空间。** 在超滤模型中，对 \(A\subseteq X\) 记
\[
\widehat A=\{\mathcal U\in\operatorname{Ult}(X):A\in\mathcal U\}.
\]
观察集合满足
\[
\{r:r_n(f)=j\}=\widehat{f^{-1}(j)},
\]
而每个 \(\widehat A\) 都来自二值观察。因此题设拓扑恰好是超滤的 Stone 拓扑。它以 \(\widehat A\) 为开闭基，是紧 Hausdorff、零维空间；这里使用标准 Stone 空间定理，适用于集合布尔代数 \(\mathcal P(X)\)，零布尔代数的 Stone 空间约定为空。

关键是如下事实。若 \(s:X\to X\) 是置换，则
\[
\boxed{s_*\mathcal U=\mathcal U
\iff \operatorname{Fix}(s)\in\mathcal U.}
\tag{13}
\]

证明必要性：将移动点集 \(M=X\setminus\operatorname{Fix}(s)\) 分为三个集合 \(C_0,C_1,C_2\)，使
\[
C_j\cap sC_j=\varnothing.
\]
这种划分总能构造：用选择公理在各 \(s\)-轨道选代表；偶长度循环及双向无限轨道交替用两色，奇长度循环在前偶数个点交替用两色、末点用第三色。若 \(M\in\mathcal U\)，则某个 \(C_j\in\mathcal U\)；不动性又给出 \(sC_j\in\mathcal U\)，与交集为空矛盾。

反之，若 \(D=\operatorname{Fix}(s)\in\mathcal U\)，则
\[
A\cap D=s^{-1}(A)\cap D.
\]
故 \(A\in\mathcal U\iff s^{-1}(A)\in\mathcal U\)，即 \(\mathcal U\) 不动。这证明 (13)。

对有限 \(F\subseteq G\)，定义
\[
D_F=\{x\in X:gx=x\text{ 对所有 }g\in F\}
    =X^{\langle F\rangle},
\qquad D_\varnothing=X.
\]
于是
\[
R_\infty(X)^G
\cong
\{\mathcal U\in\operatorname{Ult}(X):D_F\in\mathcal U
\text{ 对每个有限 }F\subseteq G\}.
\tag{14}
\]

这给出一个直接由作用构造的布尔代数模型。令
\[
\mathcal J_{G,X}=
\{A\subseteq X:\text{存在有限 }F\subseteq G,\ A\cap D_F=\varnothing\},
\qquad
B_{G,X}=\mathcal P(X)/\mathcal J_{G,X}.
\tag{15}
\]
\(\mathcal J_{G,X}\) 是理想：向下封闭显然成立，两个见证 \(F,E\) 的有限并由 \(F\cup E\) 见证。超滤包含所有 \(D_F\)，恰好等价于它与这个理想不交。因此，布尔代数商的超滤对应给出
\[
\boxed{R_\infty(X)^G\cong\operatorname{Stone}(B_{G,X}).}
\tag{16}
\]
具体映射把 \(\mathcal U\) 送到 \(\{[A]:A\in\mathcal U\}\)。商上的基本开闭集对应于
\(\widehat A\cap R_\infty(X)^G\)，所以这是题设拓扑下的同胚。若理想包含 \(X\)，商为零布尔代数，两边都为空。

由超滤延拓定理及
\(D_F\cap D_E=D_{F\cup E}\)，得到准确的存在判准：
\[
\boxed{
R_\infty(X)^G\ne\varnothing
\iff
D_F\ne\varnothing\quad\text{对每个有限 }F\subseteq G.
}
\tag{17}
\]
亦即，每个有限生成子群都在 \(X\) 中有不动点。取 \(F=\varnothing\) 已覆盖空底集。

这也补全了任意 \(G\) 集合上的有限层延拓判准：非空 \(X\) 的一值不动记录可延拓当且仅当 (17) 成立，其延拓集合就是 (16)；二值不动记录可延拓当且仅当其选择族是超滤，此时唯一；三值及以上全部唯一延拓。

令 \(A=X^G\)。其点值记录的闭包为
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}
=\widehat{X^G}.
}
\tag{18}
\]
事实上，若 \(A\notin\mathcal U\)，则开邻域 \(\widehat{X\setminus A}\) 避开所有来自 \(A\) 的主超滤；若 \(A\in\mathcal U\)，则任一基本邻域 \(\widehat B\ni\mathcal U\) 都满足 \(A\cap B\ne\varnothing\)，因而包含某个来自 \(A\) 的主超滤。这个闭包也自然同胚于 \(\operatorname{Ult}(X^G)\)。

由 (14) 可知该闭包总包含于不动空间，而且
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G
\iff
\text{存在有限 }F\subseteq G,\quad D_F=X^G.
}
\tag{19}
\]
充分性直接来自每个不动超滤都包含 \(D_F\)。证明必要性时，若不存在这样的 \(F\)，则每个
\(D_F\setminus X^G\) 都非空。因此
\[
\{D_F:F\subseteq G\text{ 有限}\}\cup\{X\setminus X^G\}
\]
具有有限交性质；其超滤延拓是不动超滤，却不属于 \(\widehat{X^G}\)，与等式矛盾。这个论证也覆盖两边为空的情形。

对于群本身，完整分类是
\[
\boxed{
\text{对每个 }G\text{ 集合都满足 (19) 左侧等式}
\iff G\text{ 有限生成}.
}
\tag{20}
\]
若 \(F\) 是有限生成集，则对每个作用都有 \(D_F=X^G\)。

反之，设 \(G\) 非有限生成，令 \(\mathcal H\) 为其所有有限生成子群组成的集合，并取
\[
X=\coprod_{H\in\mathcal H}G/H
\]
及左平移作用。每个 \(H\) 都是 proper 子群，所以各点的稳定子是某个 proper 子群的共轭，故 \(X^G=\varnothing\)。但对每个有限 \(F\subseteq G\)，分量
\(G/\langle F\rangle\) 中的单位陪集被 \(F\) 固定，所以 \(D_F\ne\varnothing\)。由 (17) 存在完整不动记录，等式失败。该余积是集合，因而满足题设的大小条件。

所需的可数具体例子可取
\[
G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N),
\qquad X=\mathbb N,
\tag{21}
\]
即所有有限支撑置换的群，以自然方式作用。它是有限群
\(\operatorname{Sym}([n])\) 的可数递增并，因此群和底集都可数。每个自然数都被某个换位移动，故 \(X^G=\varnothing\)。

此例的全部不动记录恰好对应 \(\mathbb N\) 上的全部自由超滤：

- 每个群元素的固定点集都是余有限集，因此每个自由超滤由 (13) 给出不动记录。
- 主超滤若不动，其所主之点必须全局不动，所以不存在主的不动超滤。

自由超滤存在，因为余有限滤子是 proper 滤子，可在 ZFC 中延拓。全部记录的取值由 (4) 给出，其整个拓扑空间为
\[
R_\infty(\mathbb N)^G
\cong\operatorname{Stone}\bigl(\mathcal P(\mathbb N)/\mathrm{Fin}\bigr).
\tag{22}
\]
这里 \(\mathrm{Fin}\) 是有限子集理想；与它不交的超滤正是自由超滤。

**最后考察乘积比较。** 每个投影 \(p_i\) 都是等变映射，所以 (7) 表明它把不动记录送到不动记录，\(\Pi_{(X_i)}\) 良定义。又由
\[
(R_\infty(h))^{-1}(\widehat B)=\widehat{h^{-1}(B)}
\tag{23}
\]
可知每个 \(R_\infty(h)\) 连续。故限制到不动空间后，各坐标仍连续，\(\Pi_{(X_i)}\) 连续。

对任意群和任意集合指标族，
\[
\boxed{\Pi_{(X_i)}\text{ 总是满射。}}
\tag{24}
\]
证明时，若目标为空，满射性无须再证。否则固定目标中的一个元组
\((\mathcal U_i)_{i\in I}\)，令 \(P=\prod_iX_i\)。在 \(P\) 上考虑：

\[
p_i^{-1}(A)\quad(A\in\mathcal U_i),
\qquad
P^F=\prod_{i\in I}D_{i,F}\quad(F\subseteq G\text{ 有限}),
\]
其中 \(D_{i,F}=X_i^{\langle F\rangle}\)。

这些集合具有有限交性质。任一有限交可写成
\[
P^F\cap\bigcap_{j\in J}p_j^{-1}(A_j)
=
\prod_{i\in I}B_i,
\qquad
B_i=
\begin{cases}
D_{i,F}\cap A_i,&i\in J,\\
D_{i,F},&i\notin J,
\end{cases}
\tag{25}
\]
其中 \(J\) 有限。由不动性及 (14)，每个 \(B_i\in\mathcal U_i\)，所以非空；ZFC 的选择公理保证该乘积非空。

将此族延拓为超滤 \(\mathcal W\)。它包含每个 \(P^{\{g\}}\)，故由 (13) 是不动超滤；它在第 \(i\) 个坐标的边缘超滤包含 \(\mathcal U_i\)，因此等于 \(\mathcal U_i\)。这给出所求原像。

当 \(I=\varnothing\) 时，源底集和目标空乘积均为单点，比较映射是单点间的双射。若非空指标族含空底集因子，则源与目标均为空。这些情况都与上述结论一致。

先证明有限因子的结论。若 \(X\) 有限非空，\(X\times Y\) 上每个超滤 \(\mathcal W\) 都包含唯一一条纤维 \(\{x\}\times Y\)。令
\(\mathcal V=(p_Y)_*\mathcal W\)，则对每个 \(A\subseteq X\times Y\)，
\[
A\in\mathcal W
\iff
\{y:(x,y)\in A\}\in\mathcal V.
\tag{26}
\]
所以 \(\mathcal W\) 由 \(x,\mathcal V\) 唯一确定。

若 \(\mathcal W\) 不动，则其第一边缘 \(\mathcal U_x\) 不动，故 \(x\in X^G\)，第二边缘也不动。反之，若 \(x\in X^G\) 且 \(\mathcal V\) 不动，则等变映射
\(y\mapsto(x,y)\) 将 \(\mathcal V\) 推成所需的不动超滤。因此
\[
R_\infty(X\times Y)^G
\cong X^G\times R_\infty(Y)^G,
\]
且这一对应正是比较映射。交换因子同理；空因子时两边都为空。故第一个全称命题为真：
\[
\boxed{\text{至少一个因子有限时，两因子的比较映射为双射。}}
\tag{27}
\]

对于平凡群，准确的单射判准是
\[
\boxed{
\operatorname{Ult}(X\times Y)\longrightarrow
\operatorname{Ult}(X)\times\operatorname{Ult}(Y)
\text{ 单射}
\iff X\text{ 或 }Y\text{ 有限}.
}
\tag{28}
\]
充分性已经证明。若两者均无限，在 ZFC 中可选单射
\(a:\mathbb N\to X\)、\(b:\mathbb N\to Y\)。取自由超滤 \(\mathcal U\)，令
\[
\mathcal U_X=a_*\mathcal U,\qquad
\mathcal U_Y=b_*\mathcal U,\qquad
D=\{(a(n),b(n)):n\in\mathbb N\}.
\]
超滤
\[
\mathcal W_0=(n\mapsto(a(n),b(n)))_*\mathcal U
\]
具有边缘 \((\mathcal U_X,\mathcal U_Y)\)，并包含 \(D\)。

另一方面，所有矩形 \(A\times B\)，其中
\(A\in\mathcal U_X,B\in\mathcal U_Y\)，连同 \(D^c\)，具有有限交性质：合并有限多个矩形条件后，\(a^{-1}(A),b^{-1}(B)\) 都属于自由超滤，因而无限；可选不同的
\(n\in a^{-1}(A)\)、\(m\in b^{-1}(B)\)，得到
\((a(n),b(m))\in(A\times B)\setminus D\)。
延拓得到 \(\mathcal W_1\)，其边缘相同，但包含 \(D^c\)。因此 \(\mathcal W_0\ne\mathcal W_1\)，证明非单射。

第二个全称命题为假，且可沿用可数作用 (21)。令
\[
X=Y=\mathbb N,\qquad
G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb N),
\]
则 \(X^G=Y^G=\varnothing\)。固定自由超滤 \(\mathcal U\)，将上一构造中的 \(a,b\) 都取为恒等，得到具有相同边缘
\((\mathcal U,\mathcal U)\) 的两个不同超滤：一个包含对角线，另一个包含其补集。

它们都是不动的。事实上，对每个 \(g\in G\)，
\(E_g=\operatorname{Fix}_{\mathbb N}(g)\) 余有限，故 \(E_g\in\mathcal U\)。两个乘积超滤都包含
\[
E_g\times E_g
=\operatorname{Fix}_{\mathbb N\times\mathbb N}(g),
\]
于是由 (13) 不动。因此
\[
\boxed{
X^G=Y^G=\varnothing
\ \text{并不能保证两因子的比较映射单射。}
}
\]