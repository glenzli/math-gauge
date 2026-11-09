可以将这一想法严格化为三类对象：**上距离控制矩阵、下距离控制矩阵，以及不可分辨阈值矩阵**。其中有两个必须保留的区别：

- 允许系数为 \(\infty\)，仍不一定能得到 Lipschitz 型上界，因为 \(0\cdot\infty=0\)。
- “输出不可分辨”应指输出的相应伪度量为零；在没有族分离性时，这不等于输出点相同。

下面给出一套定义及其基本性质。

先将有限指标集写成 \(I=\{1,\ldots,n\}\)，记距离向量为
\[
\mathbf d(x,y):=(d_1(x,y),\ldots,d_n(x,y))^{\mathsf T},
\qquad
x\sim y\iff \mathbf d(x,y)=\mathbf0.
\]
向量不等式均按分量理解。非负扩展矩阵的乘法采用题设算术：
\[
(A\mathbf v)_i=\sum_{j=1}^n a_{ij}v_j.
\]
这些运算满足结合律、分配律和单调性，因而通常的矩阵复合论证仍然成立。

还应固定一个**比较范围** \(Y\subseteq\mathcal X\)。取 \(Y=\mathcal X\) 得到全局性质；取 \(Y=\operatorname{dom}(\phi)\)，则只比较有效输入。这一区别对于下界尤其重要。

称 \(A\in[0,\infty]^{n\times n}\) 为 \(\phi\) 在 \(Y\) 上的一个**上控制矩阵**，若
\[
\boxed{\quad
\mathbf d(\phi(x),\phi(y))
\le A\mathbf d(x,y)
\qquad(x,y\in Y).
\quad} \tag{1}
\]
称 \(B\in[0,\infty]^{n\times n}\) 为一个**下控制矩阵**，若
\[
\boxed{\quad
B\mathbf d(x,y)
\le \mathbf d(\phi(x),\phi(y))
\qquad(x,y\in Y).
\quad} \tag{2}
\]
分别记所有这样的矩阵组成的集合为
\[
\mathsf U_Y(\phi),\qquad \mathsf L_Y(\phi).
\]

这里的行求和允许一个输出分量同时依赖多个输入分量。例如
\[
d_i(\phi(x),\phi(y))
\le a_{i1}d_1(x,y)+a_{i2}d_2(x,y).
\]
它不同于逐对要求 \(d_i(\phi(x),\phi(y))\le a_{ij}d_j(x,y)\)。若采用逐对比较，多个上界应合成为最小值，多个下界应合成为最大值；**独立成立的下界不能直接相加**。

这些定义有以下基本性质。

- **上界存在的准确条件。**
  \[
  \boxed{\quad
  \mathsf U_Y(\phi)\ne\varnothing
  \iff
  \bigl[x,y\in Y,\ x\sim y\Longrightarrow \phi(x)\sim\phi(y)\bigr].
  \quad} \tag{3}
  \]
  必要性来自 \(A\mathbf0=\mathbf0\)，即使 \(A\) 含有无穷条目也如此。

  反过来，若右侧成立，取所有条目均为 \(\infty\) 的矩阵：输入距离向量为零时，输出距离向量也为零；否则输入至少有一个严格正的分量，每一行的上界便都是 \(\infty\)。因此它是合法上界。

  所以，扩展系数能够容纳“没有有限 Lipschitz 界”的情形，却不能容纳“把零距离输入分开”的情形。

- **下界总是存在，但可能只有零矩阵。**

  总有 \(0\in\mathsf L_Y(\phi)\)。并且，上控制矩阵的集合向上封闭，下控制矩阵的集合向下封闭：
  \[
  A'\ge A\in\mathsf U_Y(\phi)\Longrightarrow A'\in\mathsf U_Y(\phi),
  \]
  \[
  0\le B'\le B\in\mathsf L_Y(\phi)\Longrightarrow B'\in\mathsf L_Y(\phi).
  \]

  对全局比较，有一个由吸收元引起的限制：
  \[
  \boxed{\quad
  \operatorname{dom}(\phi)\ne\mathcal X\setminus\{\bot\}
  \Longrightarrow
  \mathsf L_{\mathcal X}(\phi)=\{0\}.
  \quad} \tag{4}
  \]
  事实上，取 \(x\ne\bot\) 使 \(\phi(x)=\bot\)，并比较 \(x,\bot\)。输入每个距离都是 \(\infty\)，输出每个距离都是零；任何严格正的矩阵条目都会使相应下界成为 \(\infty\)，导致矛盾。

  这说明：若要研究部分算子的非平凡下界，通常应在有效定义域或其他指定区域内比较。

- **复合律。**

  若
  \[
  A\in\mathsf U_Y(\phi),\qquad
  C\in\mathsf U_{\phi(Y)}(\psi),
  \]
  则
  \[
  CA\in\mathsf U_Y(\psi\circ\phi).
  \]
  同样，
  \[
  B\in\mathsf L_Y(\phi),\qquad
  D\in\mathsf L_{\phi(Y)}(\psi)
  \Longrightarrow
  DB\in\mathsf L_Y(\psi\circ\phi).
  \]
  证明就是单调性，例如
  \[
  \mathbf d(\psi\phi(x),\psi\phi(y))
  \le C\mathbf d(\phi(x),\phi(y))
  \le CA\mathbf d(x,y).
  \]

  若各算子的界原本只在各自有效定义域上成立，将比较范围限制到 \(\operatorname{dom}(\psi\circ\phi)\)，同样可以应用此结论。

- **非退化下界控制信息丢失。**

  若 \(B\in\mathsf L_Y(\phi)\)，且每一列至少含有一个严格正的条目，则
  \[
  \phi(x)\sim\phi(y)\Longrightarrow x\sim y.
  \]
  因为输出距离全为零时，\(b_{ij}d_j(x,y)\le0\)；只要 \(b_{ij}>0\)，就必须有 \(d_j(x,y)=0\)。

  若同时存在上控制矩阵，则 \(\phi\) 在零距离商空间上诱导单射。没有族分离性时，不能将此直接称为原集合上的单射。

**一般应保留“所有合法控制矩阵”的集合，而不要预设存在唯一的最佳矩阵。**

例如，令 \(d_1=d_2=d\)，且存在一对距离为 \(1\) 的点。对恒等算子，矩阵
\[
E=\begin{pmatrix}1&0\\0&1\end{pmatrix},
\qquad
P=\begin{pmatrix}0&1\\1&0\end{pmatrix}
\]
都同时是上、下控制矩阵。

若存在按分量排序的最小上控制矩阵，它必须同时不超过 \(E,P\)，于是只能为零矩阵，矛盾。若存在最大下控制矩阵，它必须同时不小于 \(E,P\)，于是每个条目至少为 \(1\)；作用于距离向量 \((1,1)^{\mathsf T}\) 时，下界至少为 \((2,2)^{\mathsf T}\)，也产生矛盾。

甚至在单分量情形，上界系数的下确界也未必可取。令
\[
\mathcal X=\{\bot,a\},\qquad d(a,\bot)=\infty,\qquad \phi=\mathrm{id}.
\]
每个 \(c>0\)，包括 \(c=\infty\)，都满足
\[
d(\phi(x),\phi(y))\le c\,d(x,y),
\]
但 \(c=0\) 不满足。因此合法系数集合是 \((0,\infty]\)，其下确界 \(0\) 并不是合法上界。

接下来严格化“输入落入一定范围后，输出不再可区分”。

最完整的对象首先是关系
\[
K_i(\phi;Y)
:=
\{(x,y)\in Y^2:d_i(\phi(x),\phi(y))=0\}.
\]
它是 \(Y\) 上的等价关系：反身性、对称性直接成立；传递性由三角不等式得到。所有分量都不可分辨对应
\[
K(\phi;Y):=\bigcap_i K_i(\phi;Y).
\]
例如，“区域 \(S\subseteq Y\) 内的输入经算子后都不可分辨”，准确地说就是
\[
S\times S\subseteq K(\phi;Y).
\]

如果希望用输入距离阈值概括这种性质，可以定义**逐分量消隐半径矩阵**
\[
\boxed{\quad
R_{ij}^Y(\phi)
:=
\inf\{d_j(x,y):x,y\in Y,\ d_i(\phi(x),\phi(y))>0\},
\quad} \tag{5}
\]
约定 \(\inf\varnothing=\infty\)。

它具有准确的阈值解释：对任意 \(r\in[0,\infty]\)，
\[
\boxed{
\begin{aligned}
&r\le R_{ij}^Y(\phi)\\
&\iff
\forall x,y\in Y,\quad
d_j(x,y)<r
\Longrightarrow
d_i(\phi(x),\phi(y))=0.
\end{aligned}
} \tag{6}
\]
证明很直接：右侧恰好说明，所有输出第 \(i\) 分量仍可区分的输入对，其第 \(j\) 分量距离都至少为 \(r\)，也就是 \(r\) 是式 (5) 中集合的下界。

因此 \(R_{ij}\) 是一个真正的、唯一确定的**最大开阈值**。这里有三个端点细节：

- 一般只能保证 \(d_j<R_{ij}\)，不能自动改成 \(d_j\le R_{ij}\)。例如恒等算子在两个距离为 \(1\) 的非吸收点上有消隐半径 \(1\)，但距离恰为 \(1\) 时并不消隐。
- \(R_{ij}=0\) 不提供任何消隐保证，甚至不保证零距离输入被保持。
- \(R_{ij}=\infty\) 表示所有有限 \(d_j\)-距离的输入对均被消隐；它不涵盖 \(d_j=\infty\) 的输入对。例如上述 \(\{\bot,a\}\) 上的恒等算子，其消隐半径就是 \(\infty\)。

若希望使用闭阈值“\(\le r\)”，必须另外检查端点是否成立。单独一个数 \(R_{ij}\) 不能记录这项信息。

上下控制矩阵与消隐关系之间还有直接联系。对 \(A\in\mathsf U_Y(\phi)\)、\(B\in\mathsf L_Y(\phi)\)，有
\[
\boxed{
\bigcap_{j:a_{ij}>0}\{(x,y)\in Y^2:d_j(x,y)=0\}
\ \subseteq\ K_i(\phi;Y)
\ \subseteq\
\bigcap_{j:b_{ij}>0}\{(x,y)\in Y^2:d_j(x,y)=0\}.
} \tag{7}
\]
左侧来自上界右端为零，右侧来自下界各项都必须为零；空交集理解为 \(Y^2\)。

这也说明三类量的不同作用：上界限制输出能够分开多少，下界限制哪些输入差异能够被消除，消隐半径则直接保证某个范围内的输出距离恰为零。

不过，逐分量半径表达的是“**某一个**输入分量足够小就足够”。有些算子需要**多个分量同时受限**。为此，可以进一步定义**联合闭阈值矩阵** \(T=(t_{ij})\)：
\[
\boxed{\quad
\forall i,\ \forall x,y\in Y,\qquad
\bigl[\forall j,\ d_j(x,y)\le t_{ij}\bigr]
\Longrightarrow d_i(\phi(x),\phi(y))=0.
\quad} \tag{8}
\]
每一行指定一个输入距离范围，用来保证一个输出分量不可分辨。

例如在非吸收部分 \(\{0,1\}^2\) 上取
\[
d_j(x,y)=|x_j-y_j|,
\qquad
\phi(x_1,x_2)=(x_1\mathbin{\oplus}x_2,0),
\]
并按 CH1 加入吸收元。对输出第一分量，单独令任一输入分量距离为零都不足以保证消隐，所以 \(R_{11}=R_{12}=0\)；但两个输入距离同时不超过 \(1/2\) 时，输出第一分量必然不可分辨。因此联合阈值可以记录逐分量半径遗漏的性质。

若希望**对所有算子都有统一的定量表达**，可以用非线性控制函数作为基础，再把上述矩阵视为特殊形式。对 \(\mathbf r\in[0,\infty]^n\)，定义
\[
\Omega_i^{\phi,Y}(\mathbf r)
:=
\sup\left\{
d_i(\phi(x),\phi(y)):
x,y\in Y,\ \mathbf d(x,y)\le\mathbf r
\right\},
\]
\[
\Lambda_i^{\phi,Y}(\mathbf r)
:=
\inf\left\{
d_i(\phi(x),\phi(y)):
x,y\in Y,\ \mathbf d(x,y)\ge\mathbf r
\right\},
\]
其中 \(\sup\varnothing=0\)、\(\inf\varnothing=\infty\)。

这两个函数始终有定义，且都随 \(\mathbf r\) 单调不减。因为输入对本身参与对应的上、下确界，所以
\[
\Lambda_i^{\phi,Y}(\mathbf d(x,y))
\le d_i(\phi(x),\phi(y))
\le\Omega_i^{\phi,Y}(\mathbf d(x,y)).
\]

它们准确统一了前面的定义：
\[
\boxed{
A\in\mathsf U_Y(\phi)
\iff
\forall\mathbf r,\quad
\boldsymbol\Omega^{\phi,Y}(\mathbf r)\le A\mathbf r,
} \tag{9}
\]
\[
\boxed{
B\in\mathsf L_Y(\phi)
\iff
\forall\mathbf r,\quad
B\mathbf r\le\boldsymbol\Lambda^{\phi,Y}(\mathbf r).
} \tag{10}
\]
例如，若 (1) 成立且 \(\mathbf d(x,y)\le\mathbf r\)，则输出距离至多为 \(A\mathbf r\)，取上确界得到 (9)；反方向取 \(\mathbf r=\mathbf d(x,y)\) 即可。(10) 同理。

联合闭阈值矩阵则恰好满足
\[
\boxed{\quad
\Omega_i^{\phi,Y}(t_{i1},\ldots,t_{in})=0
\qquad(\forall i).
\quad} \tag{11}
\]
因此，矩阵上界是对 \(\boldsymbol\Omega\) 的线性控制，矩阵下界是对 \(\boldsymbol\Lambda\) 的线性控制，而不可分辨范围由 \(\Omega_i\) 的零值区域描述。即使算子将零距离输入分开，\(\Omega_i(\mathbf0)>0\) 仍能如实记录它，而不需要改变 \(0\cdot\infty=0\) 的约定。

联合阈值还可以与上控制矩阵一起传递。若 \(A\) 是 \(\phi\) 在 \(Y\) 上的上控制矩阵，\(T\) 是 \(\psi\) 在 \(\phi(Y)\) 上的联合闭阈值矩阵，那么任何满足
\[
\boxed{\quad SA^{\mathsf T}\le T\quad} \tag{12}
\]
的矩阵 \(S\)，都是 \(\psi\circ\phi\) 在 \(Y\) 上的联合闭阈值矩阵。事实上，当原输入距离不超过 \(S\) 的第 \(i\) 行时，中间输出距离的第 \(j\) 分量至多为
\[
\sum_k a_{jk}s_{ik}=(SA^{\mathsf T})_{ij}\le t_{ij},
\]
于是由 \(T\) 的定义，最终输出的第 \(i\) 分量距离为零。这个传递条件对零和无穷条目同样有效，无须引入含糊的无穷除法。