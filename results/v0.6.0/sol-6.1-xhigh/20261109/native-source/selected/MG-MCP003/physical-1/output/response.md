可以把这一想法严格化为三类对象：**上控制矩阵、下控制矩阵、塌缩阈值矩阵**。它们分别描述各规范分量之间的距离上界、距离下界，以及哪些输入距离条件足以使输出不可区分。一般应把矩阵视为“控制证书”，不预设存在唯一的最优矩阵。

首先需要明确比较范围。对算子 \(\phi\)，指定一个比较集 \(S\subseteq\mathcal X\)：

- \(S=\operatorname{dom}(\phi)\)：描述算子在有效定义域上的行为；
- \(S=\mathcal X\)：描述包括吸收行为在内的全局性质。

下面的定义同时适用于这两种选择。有效域为空时，相应条件真空成立。

记距离向量为
\[
D(x,y):=\bigl(d_i(x,y)\bigr)_{i\in I}\in\bar{\mathbb R}_+^I.
\]
向量、矩阵都采用逐分量偏序；矩阵运算采用题设的扩展算术：
\[
(At)_i=\sum_{j\in I}A_{ij}t_j,
\qquad
(AB)_{ik}=\sum_{j\in I}A_{ij}B_{jk}.
\]
由于 \(I\) 有限，这些运算满足通常的结合律、分配律和单调性，包括含有 \(0,\infty\) 的情形。

称 \(A\in\bar{\mathbb R}_+^{I\times I}\) 为 \(\phi\) 在 \(S\) 上的一个**上控制矩阵**，若
\[
\boxed{\quad D(\phi x,\phi y)\le A D(x,y)
\qquad(x,y\in S).\quad}
\]
也就是
\[
d_i(\phi x,\phi y)
\le \sum_{j\in I}A_{ij}d_j(x,y).
\]
这里第 \(i\) 行共同控制第 \(i\) 个输出距离；不要求每一项单独控制它。只有一个规范时，这就回到通常的 Lipschitz 上界，但允许系数取 \(\infty\)。

类似地，称 \(B\in\bar{\mathbb R}_+^{I\times I}\) 为一个**下控制矩阵**，若
\[
\boxed{\quad B D(x,y)\le D(\phi x,\phi y)
\qquad(x,y\in S).\quad}
\]
同时具有这两种控制时，
\[
B D(x,y)\le D(\phi x,\phi y)\le A D(x,y).
\]
零矩阵总是下控制矩阵，因此有意义的下界来自其中的正系数。

这些定义直接给出以下性质：

- 若 \(A\) 是上控制矩阵且 \(A'\ge A\)，则 \(A'\) 也是；
- 若 \(B\) 是下控制矩阵且 \(0\le B'\le B\)，则 \(B'\) 也是；
- 恒等算子的上、下控制矩阵都可以取单位矩阵；
- 若 \(\phi,\psi\) 分别有控制矩阵 \(A_\phi,B_\phi\) 和 \(A_\psi,B_\psi\)，则
  \[
  A_{\psi\circ\phi}=A_\psi A_\phi,
  \qquad
  B_{\psi\circ\phi}=B_\psi B_\phi
  \]
  分别是复合算子的上、下控制矩阵。

最后一条在全局版本中直接成立；在有效域版本中，比较点取自
\[
\operatorname{dom}(\psi\circ\phi)
=\{x\in\operatorname{dom}(\phi):\phi(x)\in\operatorname{dom}(\psi)\}.
\]
例如上界的证明就是
\[
D(\psi\phi x,\psi\phi y)
\le A_\psi D(\phi x,\phi y)
\le A_\psi A_\phi D(x,y),
\]
下界同理由矩阵乘法的单调性得到。

下控制矩阵还能表达“不允许塌缩”的方向。若 \(B_{ij}>0\)，则
\[
d_i(\phi x,\phi y)=0
\quad\Longrightarrow\quad d_j(x,y)=0.
\]
因此，如果 \(B\) 的每一列都含有正元素，那么
\[
D(\phi x,\phi y)=0\quad\Longrightarrow\quad D(x,y)=0.
\]
这表示算子保持输入的可区分性。在不预设族分离性的背景下，它尚不能推出 \(x=y\)。

这里全局版本与有效域版本确有区别：若存在 \(a\ne\bot\) 满足 \(\phi(a)=\bot\)，则任何全局下控制矩阵都只能是零矩阵。因为
\[
D(a,\bot)=(\infty,\ldots,\infty),
\qquad
D(\phi a,\phi\bot)=0;
\]
只要 \(B\) 有一个正元素，相应分量的下界就会是 \(\infty\)。这也是讨论部分算子的定量下界时，通常应采用有效域版本的原因。

允许上控制矩阵取 \(\infty\)，仍有一个必须保留的限制。定义
\[
x\sim_{\mathcal G}y
\quad\Longleftrightarrow\quad D(x,y)=0.
\]
则有精确结论：
\[
\boxed{\quad
\phi\text{ 在 }S\text{ 上存在上控制矩阵}
\iff
\bigl[x\sim_{\mathcal G}y\Rightarrow
\phi x\sim_{\mathcal G}\phi y\bigr]\quad(x,y\in S).
\quad}
\]

必要性来自 \(A0=0\)。反过来，若上述零距离保持条件成立，取所有元素均为 \(\infty\) 的矩阵即可：输入距离向量为零时输出也为零；否则矩阵作用后的每个分量均为 \(\infty\)。

所以，\(\infty\) 系数可以容纳没有有限 Lipschitz 界的算子，但不能容纳把零距离点对变成正距离点对的算子。这正是约定 \(0\cdot\infty=0\) 的结果。

即使上控制矩阵存在，也不宜直接定义“唯一最优矩阵”。

一方面，扩展距离可能造成下确界不再有效。例如，在两个非吸收点之间距离为 \(\infty\) 的单规范空间上，恒等算子的每个系数 \(a>0\) 都是上控制系数，\(a=0\) 却不是。因此其上控制系数集合为
\[
(0,\infty],
\]
下确界 \(0\) 并非可用的控制系数。

另一方面，不同输入分量之间可以相互补偿。若 \(d_1=d_2\)，单位矩阵与交换矩阵都能精确控制恒等算子；只要存在有限正距离点对，它们的逐项最小值——零矩阵——就不是上控制矩阵，逐项最大值——全 \(1\) 矩阵——也不是下控制矩阵。因此，保留全部可用矩阵，或另行指定优化准则，更为准确。

对于“某类输入使输出不可区分”，可以先记录精确关系
\[
K_i^\phi
:=\{(x,y)\in S^2:d_i(\phi x,\phi y)=0\}.
\]
每个 \(K_i^\phi\) 都是等价关系：自反性、对称性直接成立，传递性来自三角不等式。全部输出规范下的不可区分关系是
\[
K^\phi=\bigcap_{i\in I}K_i^\phi.
\]
这里的不可区分始终指距离全为零，未必指输出是同一个点。

把“某类输入”具体化为各分量距离的阈值条件，就得到相应矩阵。称
\[
R\in\bar{\mathbb R}_+^{I\times I}
\]
为 \(\phi\) 在 \(S\) 上的一个**塌缩阈值矩阵**，若
\[
\boxed{\quad
\left[\forall j\in I,\ d_j(x,y)\le R_{ij}\right]
\Longrightarrow d_i(\phi x,\phi y)=0
\qquad(i\in I,\ x,y\in S).
\quad}
\]
每一行给出一个输入距离的矩形范围；落入这一范围，就足以使相应输出分量归零。各行条件均满足时，输出在全部规范下不可区分。

这一矩阵具有如下性质：

- 若 \(R\) 可用且 \(0\le R'\le R\)，则 \(R'\) 也可用；
- 零矩阵可用，当且仅当 \(\phi\) 保持全分量零距离关系；
- 全 \(\infty\) 矩阵可用，当且仅当
  \[
  D(\phi x,\phi y)=0\qquad(x,y\in S).
  \]
  此时像集中的所有点不可区分。

上控制矩阵可以提供塌缩证书：若对每个 \(i\)，
\[
\sum_j A_{ij}R_{ij}=0,
\]
则 \(R\) 是塌缩阈值矩阵。因为在第 \(i\) 行的阈值条件下，
\[
d_i(\phi x,\phi y)
\le\sum_jA_{ij}d_j(x,y)
\le\sum_jA_{ij}R_{ij}=0.
\]
特别地，可以取
\[
R_{ij}=
\begin{cases}
\infty,&A_{ij}=0,\\
0,&A_{ij}>0.
\end{cases}
\]
正的塌缩阈值还可以记录上控制矩阵之外的额外信息。

塌缩阈值也能沿复合传递。设 \(A_\phi\) 是 \(\phi\) 的上控制矩阵，\(R_\psi\) 是 \(\psi\) 的塌缩阈值矩阵。若矩阵 \(T\) 满足
\[
\sum_j(A_\phi)_{kj}T_{ij}\le(R_\psi)_{ik}
\qquad(i,k\in I),
\]
则 \(T\) 是 \(\psi\circ\phi\) 的塌缩阈值矩阵。事实上，输入满足第 \(i\) 行的 \(T\) 阈值后，中间距离满足 \(R_\psi\) 的第 \(i\) 行阈值，故最终第 \(i\) 个输出距离为零。

阈值的端点需要单独留意。即使只有一个规范，也可能不存在最大的闭阈值。例如有效域只有两个距离为 \(1\) 的点，算子为恒等算子，则
\[
d(x,y)\le r\Longrightarrow d(\phi x,\phi y)=0
\]
恰在 \(0\le r<1\) 时成立。可用阈值的上确界是 \(1\)，但阈值 \(1\) 本身无效。因此，“塌缩半径”若只记录一个上确界，还必须注明临界端点是否包含。

若希望统一描述**所有**算子，包括不保持零距离关系的算子，可以进一步采用距离模函数。对 \(t\in\bar{\mathbb R}_+^I\)，定义
\[
\overline\omega_i^\phi(t)
:=
\sup_{\substack{x,y\in S\\D(x,y)\le t}}
d_i(\phi x,\phi y),
\]
\[
\underline\omega_i^\phi(t)
:=
\inf_{\substack{x,y\in S\\D(x,y)\ge t}}
d_i(\phi x,\phi y),
\]
约定 \(\sup\varnothing=0\)、\(\inf\varnothing=\infty\)。它们总是存在，并满足
\[
\underline\omega^\phi(D(x,y))
\le D(\phi x,\phi y)
\le\overline\omega^\phi(D(x,y)).
\]

上述三类矩阵与它们有精确对应：
\[
\begin{aligned}
A\text{ 是上控制矩阵}
&\iff
\overline\omega^\phi(t)\le At
&&(\forall t),\\
B\text{ 是下控制矩阵}
&\iff
Bt\le\underline\omega^\phi(t)
&&(\forall t),\\
R\text{ 是塌缩阈值矩阵}
&\iff
\overline\omega_i^\phi(R_{i\bullet})=0
&&(\forall i).
\end{aligned}
\]
前两条由矩阵作用的单调性及取 \(t=D(x,y)\) 得到；第三条直接来自上确界的定义。若 \(\overline\omega^\phi(0)\ne0\)，它就明确记录了纯乘法上控制矩阵无法表达的零距离分裂现象。