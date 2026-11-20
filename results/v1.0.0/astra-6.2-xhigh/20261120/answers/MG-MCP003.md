取 \(D=\mathrm{dom}(\phi)\)，先比较有效定义域中的点对。对 \(x,y\in D\)，记
\[
a_j(x,y)=d_j(x,y),\qquad b_i(x,y)=d_i(\phi x,\phi y).
\]
矩阵的**行 \(i\) 表示输出分量，列 \(j\) 表示输入分量**。若要把算子失效也纳入估计，可以在以下定义中统一取 \(D=\mathcal X\)。此时，一个输出有效、另一个输出为 \(\bot\) 的点对，在每个输出分量上的距离都是 \(\infty\)。

## 一、上、下 Lipschitz 系数矩阵

对每个 \(i,j\in I\)，定义两个可用系数集
\[
\begin{aligned}
\mathcal U^\phi_{ij}
&=\{u\in[0,\infty]:\ \forall x,y\in D,\ b_i(x,y)\le u\,a_j(x,y)\},\\
\mathcal L^\phi_{ij}
&=\{\ell\in[0,\infty]:\ \forall x,y\in D,\ \ell\,a_j(x,y)\le b_i(x,y)\}.
\end{aligned}
\]
由此定义**上系数矩阵** \(U^\phi\) 和**下系数矩阵** \(L^\phi\)：
\[
U^\phi_{ij}=\inf\mathcal U^\phi_{ij},
\qquad
L^\phi_{ij}=\sup\mathcal L^\phi_{ij},
\qquad \inf\varnothing=\infty .
\]
对于 \(0<a_j(x,y)<\infty\) 的点对，这就是从上、下两侧估计比值 \(b_i(x,y)/a_j(x,y)\)。直接用不等式定义，也涵盖了输入距离为零或无穷的情形。

**下系数总能取到。** \(0\) 总是可用，而且在 CH1 的算术下，对固定的 \(a\in[0,\infty]\)，乘以 \(a\) 保持上确界。因此对所有可用的 \(\ell\) 取上确界，仍有 \(L^\phi_{ij}a_j(x,y)\le b_i(x,y)\)。

**上系数要区分下确界与可用性。** 当 \(0<U^\phi_{ij}<\infty\) 时，令可用上系数从上方趋于 \(U^\phi_{ij}\)，即可得到该值本身可用。两个端点则有各自的含义。

- \(U^\phi_{ij}=\infty\) 表示没有有限上系数。\(\infty\) 本身可用的充要条件是 \(a_j(x,y)=0\Rightarrow b_i(x,y)=0\)。若某个零距离点对经 \(\phi\) 后在第 \(i\) 个分量可区分，则由 \(\infty\cdot0=0\)，连 \(\infty\) 也不能使上估计成立。
- \(U^\phi_{ij}=0\) 时，\(0\) 本身可用的充要条件是 \(b_i\) 在 \(D^2\) 上恒为零。例如，若距离数据只有 \((a_j,b_i)=(0,0)\) 和 \((\infty,1)\)，则每个正上系数都可用，其下确界 \(0\) 却不可用。

这样，每个算子都有扩展值矩阵 \(U^\phi,L^\phi\)。需要把某个上系数代回不等式时，其精确判据是属于 \(\mathcal U^\phi_{ij}\)。

## 二、不可区分半径矩阵

把“落入一定范畴”具体化为“输入的第 \(j\) 个距离小于某一阈值”。定义**不可区分半径矩阵**
\[
\boxed{\displaystyle
R^\phi_{ij}
=\inf\{\,d_j(x,y):x,y\in D,\ d_i(\phi x,\phi y)>0\,\}.}
\]
它从所有**输出仍可区分**的点对中，取输入距离的下确界。因而对每个 \(r\in[0,\infty]\)，都有精确等价式
\[
r\le R^\phi_{ij}
\quad\Longleftrightarrow\quad
\forall x,y\in D,\quad
d_j(x,y)<r\ \Longrightarrow\ d_i(\phi x,\phi y)=0 .
\]
证明直接来自下确界的定义。若 \(r\le R^\phi_{ij}\)，所有可区分点对的输入距离都至少为 \(r\)。若 \(r>R^\phi_{ij}\)，就存在输入距离小于 \(r\) 的可区分点对。

严格不等号保留了临界点的信息。若需要判断**闭半径** \(r\) 是否可用，可定义
\[
\omega^\phi_{ij}(r)
=\sup\{\,d_i(\phi x,\phi y): x,y\in D,\ d_j(x,y)\le r\,\},
\qquad \sup\varnothing=0 .
\]
闭半径 \(r\) 可用当且仅当 \(\omega^\phi_{ij}(r)=0\)。特别地，\(R^\phi_{ij}=\infty\) 保证所有有限输入距离上的输出均不可区分，输入距离恰为 \(\infty\) 的情形则由 \(\omega^\phi_{ij}(\infty)\) 判断。

若“不可区分”要求**所有输出分量**都为零，则对输入分量 \(j\)，精确的严格半径为
\[
R^\phi_{\mathrm{all},j}=\min_{i\in I}R^\phi_{ij}.
\]
其结论是 \(\phi x\sim\phi y\)，其中 \(u\sim v\) 表示对每个 \(i\) 都有 \(d_i(u,v)=0\)。CH1 允许这样的 \(u,v\) 是不同的点。若所说的“范畴”是指定集合 \(S\subseteq D\)，也可直接使用判据 \(\sup_{x,y\in S}d_i(\phi x,\phi y)=0\)，逐个输出分量判断。

**下系数与不可区分半径记录不同的信息。** 例如，在普通距离空间 \(D=\{0,1,4\}\) 上，令 \(\phi(0)=\phi(1)=0,\ \phi(4)=4\)，再按 CH1 添入孤立的 \(\bot\)。三个不同点对的输入、输出距离分别为 \((1,0),(3,4),(4,4)\)，故
\[
U^\phi=\tfrac43,\qquad L^\phi=0,\qquad R^\phi=3.
\]
距离小于 \(3\) 时输出不可区分，恰为 \(3\) 时已经可区分。作为对照，\([0,1]\) 上的 \(x\mapsto x^2\) 也有下系数 \(0\)，但它严格单调，且有任意接近的不同输入，所以其不可区分半径为 \(0\)。

## 三、复合与多个输入分量的联合估计

对复合 \(\psi\circ\phi\)，其有效定义域中的点都经 \(\phi\) 落入 \(\mathrm{dom}(\psi)\)。因此，经由任一中间分量 \(k\)，两个**可用**上系数可以相乘，两个可用下系数也可以相乘。这只需连续应用两次相应的不等式。对不可区分性，更直接的复合规则是
\[
\omega^{\psi\circ\phi}_{ij}(r)
\le \min_{k\in I}\omega^\psi_{ik}\!\left(\omega^\phi_{kj}(r)\right).
\]
事实上，若 \(d_j(x,y)\le r\)，则中间距离至多为 \(\omega^\phi_{kj}(r)\)，再应用 \(\psi\) 的估计即得。右侧只要有一项为零，复合算子就在该闭半径内使第 \(i\) 个输出分量不可区分。

最后，若想表达的是**多个输入分量共同控制一个输出分量**，可令 \(\mathbf d(x,y)=(d_j(x,y))_{j\in I}\)，另行定义可用的联合上、下估计矩阵 \(A,B\) 满足逐分量不等式
\[
B\,\mathbf d(x,y)\ \le\ \mathbf d(\phi x,\phi y)\
\le\ A\,\mathbf d(x,y)\qquad(x,y\in D).
\]
这里使用通常的非负矩阵乘法及 CH1 的无穷算术。这种估计能表达真正的分量叠加。例如，在 \(\mathbb R^2\) 上取两个坐标伪度量，令 \(\phi(s,t)=(s+t,0)\)。由三角不等式，
\[
A=\begin{pmatrix}1&1\\0&0\end{pmatrix}
\]
是可用的联合上矩阵，而单独固定任一输入坐标，第一输出坐标仍可改变，所以 \(\mathcal U^\phi_{11}\) 和 \(\mathcal U^\phi_{12}\) 都为空。联合矩阵也能沿复合传递，因为非负矩阵乘法保持逐分量次序，故 \(A_\psi A_\phi\) 和 \(B_\psi B_\phi\) 分别给出复合的联合上、下估计。