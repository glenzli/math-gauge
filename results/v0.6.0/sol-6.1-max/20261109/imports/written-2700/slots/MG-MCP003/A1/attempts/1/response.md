可以把这一想法整理为三类对象：**上距离比较矩阵、下距离比较矩阵，以及使输出不可区分的阈值矩阵**。其中有一个必须保留的限制：在不假设族分离性的伪度量空间中，即使允许系数为 \(\infty\)，也不能保证每个算子都有线性上界。

下面以**有效定义域内的比较**为主；最后说明把未定义行为纳入比较时有什么变化。

记
\[
E=[0,\infty],\qquad
\Delta(x,y):=(d_i(x,y))_{i\in I}\in E^I,\qquad
S_\phi:=\operatorname{dom}(\phi).
\]
向量不等式均按分量理解。矩阵运算采用题设的扩展非负实数算术：
\[
(Av)_i=\sum_{j\in I}a_{ij}v_j,\qquad
(AB)_{ik}=\sum_{j\in I}a_{ij}b_{jk}.
\]
由于 \(I\) 有限，且约定 \(0\cdot\infty=0\)，这些运算有定义，并满足非负矩阵运算所需的结合律、分配律和单调性。

称 \(U\in E^{I\times I}\) 为 \(\phi\) 的一个**上距离比较矩阵**，若
\[
\Delta(\phi x,\phi y)\le U\Delta(x,y)
\qquad(x,y\in S_\phi).
\tag{1}
\]
称 \(L\in E^{I\times I}\) 为一个**下距离比较矩阵**，若
\[
L\Delta(x,y)\le \Delta(\phi x,\phi y)
\qquad(x,y\in S_\phi).
\tag{2}
\]
因此，双边估计写成
\[
\boxed{\quad
L\Delta(x,y)\le \Delta(\phi x,\phi y)
\le U\Delta(x,y),\qquad x,y\in S_\phi.
\quad}
\tag{3}
\]

当 \(I\) 只有一个元素时，这就是扩展值的上下 Lipschitz 估计。多个分量时，例如
\[
d_1(\phi x,\phi y)
\le 2d_1(x,y)+3d_2(x,y),
\]
便允许第一输出分量同时受多个输入分量控制。

这里应讨论“可容许矩阵的全体”，而不预设存在唯一的最优矩阵。上界矩阵向上封闭，下界矩阵向下封闭；零矩阵总是下界矩阵。系数 \(\infty\) 的含义尤其需要明确：

- 在上界中，\(\infty\cdot t\) 对 \(t>0\) 给出无信息的上界，但在 \(t=0\) 时仍为 \(0\)。
- 在下界中，系数 \(l_{ij}=\infty\) 要求：只要相应输入距离 \(d_j(x,y)>0\)，第 \(i\) 个输出距离就必须为 \(\infty\)。

这些定义与算子复合相容。事实上，
\[
\operatorname{dom}(\psi\circ\phi)
=\{x\in S_\phi:\phi x\in S_\psi\}.
\]
若 \((L_\phi,U_\phi)\)、\((L_\psi,U_\psi)\) 分别给出双边估计，则
\[
\boxed{\quad
(L_\psi L_\phi,\;U_\psi U_\phi)
\text{ 是 }\psi\circ\phi\text{ 的一对可容许矩阵。}
\quad}
\tag{4}
\]
证明只需对复合的有效域内点对使用单调性：
\[
\begin{aligned}
L_\psi L_\phi\Delta(x,y)
&\le L_\psi\Delta(\phi x,\phi y)\\
&\le\Delta(\psi\phi x,\psi\phi y)\\
&\le U_\psi\Delta(\phi x,\phi y)\\
&\le U_\psi U_\phi\Delta(x,y).
\end{aligned}
\]

下界还刻画了哪些输入差异不允许消失。由 (2)，
\[
d_i(\phi x,\phi y)=0,\quad l_{ij}>0
\quad\Longrightarrow\quad d_j(x,y)=0.
\tag{5}
\]
因此，若 \(L\) 的每一列都至少有一个正元素，则
\[
\Delta(\phi x,\phi y)=0\Longrightarrow\Delta(x,y)=0.
\tag{6}
\]
若同时存在上界矩阵，\(\phi\) 就在有效域的零距离商空间上诱导单射；若规范族还具有分离性，则 \(\phi|_{S_\phi}\) 本身是单射。

允许 \(\infty\) 能扩大上界矩阵的适用范围，但不能消除零距离障碍。定义
\[
x\sim_{\mathcal G}y
\iff \Delta(x,y)=0.
\]
这是等价关系。存在上界矩阵的准确条件是
\[
\boxed{\quad
\phi\text{ 存在上界矩阵}
\iff
\forall x,y\in S_\phi,\quad
x\sim_{\mathcal G}y
\Longrightarrow
\phi x\sim_{\mathcal G}\phi y.
\quad}
\tag{7}
\]

必要性来自 \(U0=0\)。反之，若右侧成立，取所有元素均为 \(\infty\) 的矩阵 \(U\)：输入距离向量为零时，输出也为零；输入向量非零时，每个上界分量均为 \(\infty\)，所以 (1) 成立。

例如，在三个非吸收点 \(a,b,c\) 上取
\[
d(a,b)=0,\qquad d(a,c)=d(b,c)=1,
\]
并按 CH1 加入隔离的吸收元。令
\[
\phi(a)=a,\qquad \phi(b)=\phi(c)=c,\qquad \phi(\bot)=\bot.
\]
则有效域内有
\[
d(a,b)=0,\qquad d(\phi a,\phi b)=1.
\]
任何系数，包括 \(\infty\)，都无法满足上界，因为 \(\infty\cdot0=0\)。

所以，在 CH1 的一般性下，合理做法是允许上界矩阵族为空，或者把“尊重全分量零距离”作为所研究算子的附加条件。若规范族分离，则所有算子自动满足这一条件。

此外，不宜把“所有可容许系数的下确界”直接当成可用系数。例如，单分量空间中，若有效域由两个互距 \(\infty\) 的点组成，则恒等算子的所有 \(u>0\) 都是上界系数，\(u=0\) 却不是。多分量下还存在权重之间的补偿：当 \(d_1=d_2=d\)、\(\phi=\mathrm{id}\) 时，每个上界行只需系数和至少为 \(1\)，每个下界行只需系数和至多为 \(1\)，通常不存在逐项最小的上界矩阵或逐项最大的下界矩阵。

对于“输入落入某个范围后，输出不再可区分”，首先可以给出不依赖阈值选取的精确定义：
\[
K_i^\phi
:=\{(x,y)\in S_\phi^2:
d_i(\phi x,\phi y)=0\}.
\tag{8}
\]
每个 \(K_i^\phi\) 都是 \(S_\phi\) 上的等价关系；传递性来自
\[
d_i(\phi x,\phi z)
\le d_i(\phi x,\phi y)+d_i(\phi y,\phi z)=0.
\]
交集 \(\bigcap_iK_i^\phi\) 表示输出在全部规范分量上不可区分。由于没有族分离性，这不必意味着 \(\phi x=\phi y\)。

阈值矩阵可以概括这些关系，但必须明确矩阵的读法。一种适合表达多个输入分量联合作用的定义是：称 \(R=(r_{ij})\in E^{I\times I}\) 为**联合零化阈值矩阵**，若对所有 \(i\in I\)、\(x,y\in S_\phi\)，
\[
\boxed{\quad
\bigl[\forall j\in I,\ d_j(x,y)<r_{ij}\bigr]
\Longrightarrow d_i(\phi x,\phi y)=0.
\quad}
\tag{9}
\]
即：第 \(i\) 行规定一个输入距离范围；所有输入分量同时进入该范围，就保证第 \(i\) 个输出分量不可区分。

这类矩阵向下封闭：若 \(R\) 可容许且 \(0\le R'\le R\)，则 \(R'\) 也可容许。零矩阵总可容许，其条件为空泛条件。这里使用严格不等式是有意的：阈值处是否仍然零化，需要额外信息；而 \(r_{ij}=\infty\) 只测试 \(d_j(x,y)<\infty\) 的情形。

它也能与复合估计配合。例如，若 \(R^\phi\) 是 \(\phi\) 的联合阈值矩阵，\(U^\psi\) 是 \(\psi\) 的上界矩阵，则
\[
T_{kj}:=
\min_{\{i:\,u^\psi_{ki}>0\}}r^\phi_{ij},
\qquad \min\varnothing:=\infty,
\tag{10}
\]
是 \(\psi\circ\phi\) 的一个联合阈值矩阵。因为输入满足第 \(k\) 行的条件时，所有实际参与第 \(k\) 个上界的中间输出距离均为零，从而
\[
d_k(\psi\phi x,\psi\phi y)
\le\sum_i u^\psi_{ki}d_i(\phi x,\phi y)=0.
\]

另一种读法是：**单独一个输入分量达到阈值就足以保证零化**。这种读法有逐项最大的、完全规范的矩阵：
\[
\boxed{\quad
c_{ij}(\phi):=
\inf\{d_j(x,y):
x,y\in S_\phi,\ d_i(\phi x,\phi y)>0\},
\qquad \inf\varnothing:=\infty.
\quad}
\tag{11}
\]
其准确含义为：对任意 \(r\in E\)，
\[
\boxed{\quad
\bigl[\forall x,y\in S_\phi,\ 
d_j(x,y)<r\Longrightarrow d_i(\phi x,\phi y)=0\bigr]
\iff r\le c_{ij}(\phi).
\quad}
\tag{12}
\]
证明是：该蕴含成立，当且仅当所有使第 \(i\) 个输出可区分的点对，其第 \(j\) 个输入距离均至少为 \(r\)；这恰好等价于 \(r\) 不超过 (11) 的下确界。

因此 \(C(\phi)=(c_{ij}(\phi))\) 可称为**逐分量零化阈值矩阵**。注意 \(c_{ij}=\infty\) 只说明有限的第 \(j\) 个输入距离必使相应输出零化；它不保证输入距离为 \(\infty\) 时也零化。

联合阈值与逐分量阈值并不等价。例如，在非吸收部分 \(\mathbb Z^2\) 上取
\[
d_1((m,n),(m',n'))=|m-m'|,\qquad
d_2((m,n),(m',n'))=|n-n'|,
\]
令
\[
\phi(m,n)=(m+n,0).
\]
在有效域内，一个上界矩阵为
\[
U=\begin{pmatrix}1&1\\0&0\end{pmatrix}.
\]
条件 \(d_1<1,\ d_2<1\) 联合保证输出不可区分，所以联合阈值的第一行可取 \((1,1)\)。但任意一个输入分量单独为零，都不能保证第一输出分量为零，故
\[
c_{11}=c_{12}=0.
\]
这说明联合阈值能表达逐分量阈值遗漏的信息。阈值也不能照搬普通矩阵乘法：例如 \(2\mathbb Z\) 上恒等算子的单分量阈值为 \(2\)，复合后仍为 \(2\)，而非 \(4\)。

如果“统一表达”要求**每个算子都具有一个上界对象**，可以进一步采用非线性距离模量：
\[
\Omega_{\phi,i}(r)
:=
\sup\{d_i(\phi x,\phi y):
x,y\in S_\phi,\ \Delta(x,y)\le r\},
\qquad r\in E^I,
\tag{13}
\]
约定 \(\sup\varnothing=0\)。它对所有算子都有定义、按分量单调，并且
\[
\Delta(\phi x,\phi y)
\le\Omega_\phi(\Delta(x,y)).
\tag{14}
\]
上界矩阵正好对应它的线性控制：
\[
U\text{ 满足 (1)}
\iff
\Omega_\phi(r)\le Ur\quad(\forall r\in E^I).
\tag{15}
\]
这里允许 \(\Omega_\phi(0)\ne0\)，因此也能描述破坏零距离相容性的算子。

最后，若希望连未定义行为也纳入估计，可以把上述量词范围从 \(S_\phi^2\) 改为 \(\mathcal X^2\)。但这会显著加强条件：只要存在 \(x\ne\bot\) 满足 \(\phi x=\bot\)，点对 \((x,\bot)\) 就满足
\[
\Delta(x,\bot)=(\infty,\ldots,\infty),
\qquad
\Delta(\phi x,\phi\bot)=0.
\]
任何非零下界矩阵都会因此产生矛盾，所以全空间版本的下界矩阵只能是零矩阵。有效域版本估计已定义部分的距离行为；全空间版本还对算子的定义与未定义结构施加约束，二者应明确区分。