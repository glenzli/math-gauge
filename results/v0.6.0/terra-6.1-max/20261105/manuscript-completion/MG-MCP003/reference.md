# 一条已观察的 AI 参考路线

以下正文逐字保留已观察的 Terra A1 答卷。它已获本次 AI 数学审核满分并由用户选择接纳；人工数学审核仍为 pending。它是完整参考路线之一，正确替代定义、比较口径及论证同样可接受，不要求采用 OET 专属记号或路线。

原文见 [reference-terra-answer.md](reference-terra-answer.md)，9441 UTF-8 字节，SHA-256 `aef71d1eb6ff1c231ac777ede509694a29544264dc567deba245c5a7ca4f61cf`。分隔线之后保留其原字节。

---

下面给出一套自然的定义。矩阵的**行表示输出分量，列表示输入分量**；上、下界使用扩展非负数上的矩阵乘法，“不可区分”则用输入类别上的零距离来表达。

需要先固定比较口径。对每个算子 \(\phi\)，可以选用

\[
P_\phi=
\begin{cases}
\operatorname{dom}(\phi)\times\operatorname{dom}(\phi),
&\text{有效域口径},\\[2mm]
\mathcal X\times\mathcal X,
&\text{全局口径}.
\end{cases}
\]

前者比较 \(\phi\) 在两点都有效时的行为；后者还比较输出为 \(\bot\) 的情形。以下各式在统一采用任一种口径时都成立。有效域为空时，有效域口径下的全称断言都是空真，因而不能据此推断算子的非平凡行为。

记距离向量为

\[
D(x,y):=(d_j(x,y))_{j\in I},\qquad
D_\phi(x,y):=D(\phi(x),\phi(y)).
\]

**矩阵上界与下界。** 给定 \(L,A\in\bar{\mathbb R}_+^{I\times I}\)，称 \(L\) 是 \(\phi\) 的一个**矩阵 Lipschitz 上界**，称 \(A\) 是一个**矩阵下界**，如果对每个 \((x,y)\in P_\phi\)，

\[
\boxed{\quad A D(x,y)\ \leq\ D_\phi(x,y)\ \leq\ L D(x,y).\quad} \tag{1}
\]

这里向量不等式逐分量理解，矩阵乘法使用题目给定的扩展非负数算术。例如上界的第 \(i\) 行是

\[
d_i(\phi x,\phi y)
\leq \sum_{j\in I}L_{ij}d_j(x,y).
\]

上界和下界可以分别存在；定义并不要求预先找到同时满足两边的某一对矩阵。零矩阵总是下界。若 \(L\) 是上界，逐项增大它仍是上界；若 \(A\) 是下界，逐项减小它仍是下界。

允许无穷系数的含义由原算术约定决定：当 \(L_{ij}=\infty\) 而 \(d_j(x,y)=0\) 时，该项仍为零；当 \(A_{ij}=\infty\) 而 \(d_j(x,y)>0\) 时，下界要求输出第 \(i\) 分量的距离为 \(\infty\)。

加和是对矩阵下界的一种选择。若只想分别记录各输入分量给出的下界，也可以改用

\[
\max_j A_{ij}d_j(x,y)\leq d_i(\phi x,\phi y).
\]

这是较弱的条件；它的复合使用 \((B\otimes A)_{ij}=\max_k B_{ik}A_{kj}\)，而不是普通矩阵乘法。

对于式 (1) 的加和形式，若 \(\phi\) 分别有上、下界 \(L,A\)，而 \(\psi\) 分别有上、下界 \(M,B\)，则

\[
\boxed{\quad ML\text{ 是 }\psi\circ\phi\text{ 的上界},\qquad
BA\text{ 是其下界}.\quad} \tag{2}
\]

例如，上界由

\[
D_{\psi\circ\phi}\leq M D_\phi\leq ML D
\]

得到，下界同理。有效域口径下，这里使用了

\[
\operatorname{dom}(\psi\circ\phi)
=\{x\in\operatorname{dom}(\phi):\phi(x)\in\operatorname{dom}(\psi)\}.
\]

恒等算子以上下界矩阵 \(I\) 取到等号。

两种比较口径对下界的影响尤其大：如果存在 \(x\neq\bot\) 使 \(\phi(x)=\bot\)，那么全局口径下任何矩阵下界都只能是零矩阵。事实上，比较 \(x\) 与 \(\bot\) 时，所有输入分量距离均为 \(\infty\)，而输出距离均为零。这也是有效域口径对研究部分算子的定量下界有用的原因。

**无穷上界能覆盖什么。** 定义全分量零距离关系

\[
x\sim y\quad\Longleftrightarrow\quad d_j(x,y)=0\quad(\forall j\in I).
\]

它是等价关系，但根据题设不必推出 \(x=y\)。在选定的口径下，以下两件事等价：

1. \(\phi\) 存在一个矩阵 Lipschitz 上界；
2. 对每个 \((x,y)\in P_\phi\)，若 \(x\sim y\)，则 \(\phi(x)\sim\phi(y)\)。

必要性来自 \(L\cdot 0=0\)。反过来，若条件 2 成立，取所有元素都为 \(\infty\) 的矩阵即可：输入距离向量全零时输出也全零；只要有一个输入分量为正，矩阵乘积的每一行都是 \(\infty\)。

因此，\(\infty\) 可以表示没有有限 Lipschitz 常数的情形，但它不能消除零距离处的不相容。例如，令 \(d(a,b)=0\)、\(d(a,c)=d(b,c)=1\)，各非吸收点到 \(\bot\) 的距离均为 \(\infty\)，再令 \(\phi(a)=a,\ \phi(b)=c\)。则输入 \(a,b\) 距离为零、输出距离为一，所以连系数 \(\infty\) 也不能给出上界。

另一方面，在 \([0,1]\cup\{\bot\}\) 上取通常距离并令 \(\phi(t)=\sqrt t\)、\(\phi(\bot)=\bot\)，则不存在有限的标量 Lipschitz 常数，但系数 \(\infty\) 是上界。

在全局口径下，上述零距离相容性还要求有效域按 \(\sim\) **饱和**：若 \(x\sim y\) 且 \(x\in\operatorname{dom}(\phi)\)，则 \(y\in\operatorname{dom}(\phi)\)。否则一个输出为非吸收点、另一个为 \(\bot\)，它们的距离为 \(\infty\)。

若希望**每个算子**都有统一的估计，可以加入一个偏移项。定义零距离缺陷

\[
e_i(\phi):=
\sup\{d_i(\phi x,\phi y):(x,y)\in P_\phi,\ x\sim y\},
\qquad \sup\varnothing:=0.
\]

令 \(J_\infty\) 为全 \(\infty\) 矩阵，则总有

\[
\boxed{\quad D_\phi(x,y)\leq e(\phi)+J_\infty D(x,y),
\qquad (x,y)\in P_\phi.\quad} \tag{3}
\]

输入距离向量为零时，式 (3) 由 \(e(\phi)\) 的定义成立；否则右侧为 \(\infty\)。而且，在任何形如 \(D_\phi\leq b+LD\) 的估计中，比较全零输入距离的点对可知 \(b_i\geq e_i(\phi)\)。所以 \(e(\phi)\) 精确记录了零距离处不可由齐次矩阵项吸收的缺陷。

**一般不存在逐项最优矩阵。** 即使上下界存在，也不一定有一个逐项最小的上界或逐项最大的下界。例如取两个相同的分量 \(d_1=d_2=d\)，并令 \(\phi\) 为恒等算子。只要存在有限正距离的点对，矩阵

\[
\begin{pmatrix}1&0\\1&0\end{pmatrix},
\qquad
\begin{pmatrix}0&1\\0&1\end{pmatrix}
\]

都同时给出精确上、下界。它们的逐项最小值零矩阵不是上界，逐项最大值全一矩阵不是下界。

此外，无穷距离会使系数的下确界不再是可取上界：若单个伪度量在不同点之间均取 \(\infty\)，恒等算子的所有 \(c>0\)，包括 \(c=\infty\)，都是上界，而 \(c=0\) 不是。因此不能不加论证地把逐项下确界称为“最优 Lipschitz 矩阵”。

**不可区分矩阵。** “输入属于某个范畴”可以先用点对关系表达。给定关系 \(R_j\subseteq\mathcal X\times\mathcal X\)，定义布尔矩阵

\[
K^\phi_{ij}(R)=1
\quad\Longleftrightarrow\quad
\forall(x,y)\in P_\phi\cap R_j,\quad
d_i(\phi x,\phi y)=0. \tag{4}
\]

例如，若输入类别是集合 \(S_j\subseteq\mathcal X\)，取 \(R_j=S_j\times S_j\)，则 \(K^\phi_{ij}=1\) 表示该类别内任意两个有效输入的输出，在第 \(i\) 个伪度量下不可区分。若某一列的所有行均为 \(1\)，则该类别内输出在**所有分量**下距离均为零；这仍不必意味着输出是同一个点。

一个特别有用的选择是距离阈值。对 \(r\in\bar{\mathbb R}_+\)，令

\[
C_\phi(r)_{ij}=1
\quad\Longleftrightarrow\quad
\forall(x,y)\in P_\phi,\quad
d_j(x,y)\leq r\ \Longrightarrow\ d_i(\phi x,\phi y)=0. \tag{5}
\]

于是 \(C_\phi(0)\) 描述输入第 \(j\) 分量的零距离是否足以使输出第 \(i\) 分量不可区分。阈值 \(r>0\) 则描述一个更强的“局部折叠”性质；\(r=\infty\) 包含输入距离为 \(\infty\) 的点对。

若希望每个矩阵位置有自己的阈值，可定义其**容许阈值集**

\[
\Lambda_{ij}(\phi):=
\{r\in\bar{\mathbb R}_+:C_\phi(r)_{ij}=1\}.
\]

它总是向下封闭，但可能为空，也可能没有最大元素。它可以由一个扩展实数和一个端点标记完整表示：令

\[
\begin{aligned}
E_{ij}&:=\{d_j(x,y):(x,y)\in P_\phi,\ d_i(\phi x,\phi y)>0\},\\
\rho_{ij}&:=\inf E_{ij},\qquad \inf\varnothing:=\infty,\\
\eta_{ij}&:={\bf1}_{\{\rho_{ij}\in E_{ij}\}}.
\end{aligned}
\]

则恰有

\[
\boxed{\quad
r\in\Lambda_{ij}(\phi)
\iff
r<\rho_{ij}\ \text{或}\ \bigl(r=\rho_{ij}\text{ 且 }\eta_{ij}=0\bigr).
\quad} \tag{6}
\]

这是因为阈值 \(r\) 有效，恰当于不存在输出可区分、同时输入第 \(j\) 分量距离不超过 \(r\) 的点对。

端点标记不能省略。例如 \(E_{ij}=\{1\}\) 时，容许阈值为 \([0,1)\)。而 \(E_{ij}=\varnothing\) 与 \(E_{ij}=\{\infty\}\) 都有 \(\rho_{ij}=\infty\)，但前者容许阈值 \(\infty\)，后者只容许有限阈值。若某位置不需要提出折叠要求，可另用符号 \(\star\) 表示“不启用”；不能把 \(0\) 一律当成不启用，因为零阈值本身可能不成立。

**复合与上下界的联系。** 布尔矩阵采用通常的“或—且”乘法 \(\odot\)。对任意 \(r,s\in\bar{\mathbb R}_+\)，有

\[
\boxed{\quad C_{\psi\circ\phi}(r)
\ \geq\ C_\psi(s)\odot C_\phi(r).\quad} \tag{7}
\]

确实，若输入的第 \(j\) 分量距离不超过 \(r\)，且 \(C_\phi(r)_{kj}=1\)，则中间输出的第 \(k\) 分量距离为零；零不超过 \(s\)，于是 \(C_\psi(s)_{ik}=1\) 又给出最终输出第 \(i\) 分量距离为零。复合可能产生更多折叠，所以式 (7) 一般只是包含关系。

最后，上、下界分别给出两种相反方向的零距离蕴含。若 \(L\) 是上界，记 \(S_i=\{j:L_{ij}>0\}\)，则

\[
\bigl[d_j(x,y)=0\ \text{对所有 }j\in S_i\bigr]
\quad\Longrightarrow\quad
d_i(\phi x,\phi y)=0. \tag{8}
\]

这里通常需要 \(S_i\) 中的条件**同时**成立。若 \(A\) 是下界且 \(A_{ij}>0\)，则

\[
d_i(\phi x,\phi y)=0
\quad\Longrightarrow\quad d_j(x,y)=0. \tag{9}
\]

因此，若存在上界，且下界 \(A\) 的每一列至少有一个正元素，那么在所选比较口径内，输入全分量零距离当且仅当输出全分量零距离。该结论描述的是零距离等价类；除非另加族分离性，不能把它直接解释成普通意义下的单射。