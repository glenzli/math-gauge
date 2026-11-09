可以将这一想法严格化为三类数据：**上控制矩阵、下控制矩阵，以及塌缩阈值矩阵**。下面给出一种便于复合、允许 \(+\infty\)，且不预设族分离性的定义。

先记
\[
E=[0,\infty],\qquad
\mathbf d(x,y):=(d_i(x,y))_{i\in I}\in E^I.
\]
向量不等式均按分量理解，矩阵乘法采用 CH1 的扩展非负实数算术：
\[
(Av)_i=\sum_{j\in I}a_{ij}v_j,\qquad
(AB)_{ij}=\sum_{k\in I}a_{ik}b_{kj}.
\]
特别地，始终保留 \(0\cdot\infty=0\)。

定义
\[
x\sim y\quad\Longleftrightarrow\quad \mathbf d(x,y)=\mathbf0.
\]
由伪度量公理，\(\sim\) 是等价关系。这里“不可区分”指 \(\sim\)，不必意味着两点相等。

还需明确一个**考察域** \(S\subseteq\mathcal X\)：研究整个算子时取 \(S=\mathcal X\)；只研究有效作用时取 \(S=\operatorname{dom}\phi\)；研究某个输入区域时也可以取更小的 \(S\)。以下定义均对 \(x,y\in S\) 作要求。

**定义（上下控制矩阵）。** 对算子 \(\phi\)，若 \(U,L\in E^{I\times I}\) 满足
\[
\boxed{\quad
L\mathbf d(x,y)
\ \le\
\mathbf d(\phi(x),\phi(y))
\ \le\
U\mathbf d(x,y)
\qquad(x,y\in S),
\quad}
\]
则分别称 \(U\) 为上控制矩阵、\(L\) 为下控制矩阵。

展开后，上界为
\[
d_i(\phi(x),\phi(y))
\le \sum_j U_{ij}d_j(x,y),
\]
下界为
\[
\sum_j L_{ij}d_j(x,y)
\le d_i(\phi(x),\phi(y)).
\]
因此，行 \(i\) 对应输出分量，列 \(j\) 对应输入分量。这里采用的是加和型控制：多个输入分量共同控制一个输出分量。

当 \(I\) 只有一个元素时，就得到通常的双边距离估计
\[
\ell\,d(x,y)\le d(\phi(x),\phi(y))\le u\,d(x,y).
\]
一般情况下，取 \(U=u\,\mathrm{Id}\)、\(L=\ell\,\mathrm{Id}\)，则得到各分量使用相同标量的估计。

分别记全部可行矩阵为
\[
\mathsf U_\phi(S),\qquad \mathsf L_\phi(S).
\]
零矩阵总属于 \(\mathsf L_\phi(S)\)；上控制矩阵的存在性则需要下面说明的条件。

**定义（塌缩阈值矩阵）。** 将“输入落入一定范围后，输出不可区分”具体解释为：某个输入分量的距离足够小，就使某个输出分量的距离变为零。

称 \(C\in E^{I\times I}\) 为 \(\phi\) 在 \(S\) 上的严格塌缩阈值矩阵，如果
\[
\boxed{\quad
d_j(x,y)<C_{ij}
\quad\Longrightarrow\quad
d_i(\phi(x),\phi(y))=0
\qquad(x,y\in S).
\quad}
\]

这类矩阵有一个天然的、总是存在的最大值：
\[
\boxed{\quad
\Gamma^\phi_{ij}(S)
:=
\inf\bigl\{
d_j(x,y):
x,y\in S,\ 
d_i(\phi(x),\phi(y))>0
\bigr\},
\quad}
\]
其中约定 \(\inf\varnothing=\infty\)。

确切地说，
\[
C\text{ 是塌缩阈值矩阵}
\quad\Longleftrightarrow\quad
C\le\Gamma^\phi(S).
\]

证明如下：若 \(d_j(x,y)<\Gamma^\phi_{ij}(S)\)，该点对就不可能属于定义中的“输出仍可区分”集合。反过来，若 \(C_{ij}>\Gamma^\phi_{ij}(S)\)，由下确界的定义，存在输出仍可区分、但输入距离小于 \(C_{ij}\) 的点对。因此 \(\Gamma^\phi(S)\) 本身有效，并且最大。

这里采用严格小于号有实质作用：

- \(\Gamma^\phi_{ij}=0\) 表示没有正的统一阈值；它本身不判断零输入距离能否被保持。
- \(\Gamma^\phi_{ij}=\infty\) 保证所有**有限**的第 \(j\) 分量输入距离都使第 \(i\) 分量输出距离为零，不包含输入距离等于 \(\infty\) 的情形。
- 若希望改用 \(d_j(x,y)\le C_{ij}\)，还需要记录临界距离处是否也发生塌缩；单取一个上确界，未必得到有效阈值。

固定输入分量 \(j\) 时，有
\[
d_j(x,y)<\min_{i\in I}\Gamma^\phi_{ij}(S)
\quad\Longrightarrow\quad
\phi(x)\sim\phi(y).
\]
因此，矩阵中的单个元素描述一个输出分量的塌缩，而这一列的最小值控制全部输出分量的不可区分。

这些定义具有以下基本性质。

1. **允许 \(\infty\) 后，上控制矩阵存在，当且仅当算子保持全分量零距离。**

   即
   \[
   \boxed{\quad
   \mathsf U_\phi(S)\ne\varnothing
   \quad\Longleftrightarrow\quad
   \bigl[x\sim y\Longrightarrow\phi(x)\sim\phi(y)\bigr]
   \quad(x,y\in S).
   \quad}
   \]

   必要性来自
   \[
   \mathbf d(x,y)=\mathbf0
   \Longrightarrow
   U\mathbf d(x,y)=\mathbf0,
   \]
   即使 \(U\) 含有 \(\infty\)，这个结论仍成立。

   反之，假设 \(\phi\) 保持零距离，取所有元素均为 \(\infty\) 的矩阵 \(U\)。输入距离向量为零时，上界由假设成立；否则至少一个输入分量为正，因而 \(U\mathbf d(x,y)\) 的每个分量都是 \(\infty\)，上界也成立。

   所以，**把系数扩展到 \(\infty\)，仍不能涵盖会拆开零距离等价类的任意算子。** 例如，取三个非吸收点满足
   \[
   d(a,b)=0,\qquad d(a,c)=d(b,c)=1,
   \]
   并令
   \[
   \phi(a)=a,\qquad\phi(b)=\phi(c)=c.
   \]
   则输入点对 \((a,b)\) 的距离为零，输出距离却为 \(1\)，没有任何扩展上界系数能够控制它。

   若规范族具有分离性，零距离保持条件自动成立；在 CH1 的一般情形下，它是对算子的额外要求，而无需强化空间本身。

2. **上下界具有自然的单调性，并可按通常矩阵乘法复合。**

   若 \(U\) 有效，则任何 \(U'\ge U\) 都有效；若 \(L\) 有效，则任何 \(0\le L'\le L\) 都有效。缩小考察域也会保留这些估计。

   设 \(\phi(S)\subseteq T\)，并且 \(\phi\) 在 \(S\) 上、\(\psi\) 在 \(T\) 上分别具有上下控制矩阵。则
   \[
   U_{\psi\circ\phi}=U_\psi U_\phi,\qquad
   L_{\psi\circ\phi}=L_\psi L_\phi
   \]
   是复合算子的可行控制矩阵。

   这是因为扩展非负矩阵乘法保持序，从而
   \[
   \begin{aligned}
   L_\psi L_\phi\mathbf d(x,y)
   &\le L_\psi\mathbf d(\phi(x),\phi(y))\\
   &\le \mathbf d(\psi\phi(x),\psi\phi(y))\\
   &\le U_\psi\mathbf d(\phi(x),\phi(y))\\
   &\le U_\psi U_\phi\mathbf d(x,y).
   \end{aligned}
   \]
   该证明允许矩阵元素和距离取 \(\infty\)。

   有效域版本也成立：只需在
   \[
   \operatorname{dom}(\psi\circ\phi)
   =
   \{x\in\operatorname{dom}\phi:\phi(x)\in\operatorname{dom}\psi\}
   \]
   上应用上述估计。

3. **正下界阻止相应输入差异被消除。**

   若下控制矩阵 \(L\) 的每一列都至少有一个正元素，则
   \[
   \phi(x)\sim\phi(y)\quad\Longrightarrow\quad x\sim y.
   \]
   事实上，输出距离全为零时，对每个 \(j\)，选取 \(L_{ij}>0\)，便有
   \[
   0\ge L_{ij}d_j(x,y),
   \]
   从而 \(d_j(x,y)=0\)。

   若同时存在上控制矩阵，\(\phi\) 就在零距离商空间上诱导单射。只有进一步具有族分离性时，才能由此推出通常意义的单射。

   下界与塌缩阈值之间还满足
   \[
   L_{ij}>0
   \quad\Longrightarrow\quad
   \{d_j(x,y):x,y\in S\}
   \cap(0,\Gamma^\phi_{ij}(S))
   =\varnothing.
   \]
   否则某个点对一方面由下界得到正输出距离，另一方面由阈值得到零输出距离，产生矛盾。特别地，若第 \(j\) 分量存在任意小的正输入距离，则 \(L_{ij}>0\) 必然推出 \(\Gamma^\phi_{ij}(S)=0\)。

4. **塌缩阈值可以沿复合传播，但不使用通常的矩阵乘法。**

   在第 2 条的考察域条件下，若 \(\psi\) 有上控制矩阵 \(U_\psi\)，则
   \[
   \boxed{\quad
   \Gamma^{\psi\circ\phi}_{ij}(S)
   \ge
   \min_{k:(U_\psi)_{ik}>0}
   \Gamma^\phi_{kj}(S),
   \quad}
   \]
   约定空集的最小值为 \(\infty\)。

   证明：若第 \(j\) 分量输入距离小于右侧，那么对所有参与控制第 \(i\) 个最终输出的中间分量 \(k\)，都有
   \[
   d_k(\phi(x),\phi(y))=0.
   \]
   因而
   \[
   d_i(\psi\phi(x),\psi\phi(y))
   \le
   \sum_k(U_\psi)_{ik}d_k(\phi(x),\phi(y))
   =0.
   \]

   阈值本身不能直接相乘。例如，在两点距离为 \(2\) 的考察域上，恒等映射的最大塌缩阈值是 \(2\)，复合后仍是 \(2\)，而不是 \(4\)。

5. **上、下控制矩阵一般没有唯一的逐项最优值。**

   假设 \(d_1=d_2=d\)，且考察域中存在有限正距离。对恒等算子，
   \[
   A=
   \begin{pmatrix}1&0\\1&0\end{pmatrix},
   \qquad
   B=
   \begin{pmatrix}0&1\\0&1\end{pmatrix}
   \]
   都同时是上、下控制矩阵，因为它们作用于 \((d,d)^{\mathsf T}\) 后仍得到 \((d,d)^{\mathsf T}\)。

   若存在最小上控制矩阵，它必须逐项不大于 \(A,B\)，因此只能是零矩阵，但零矩阵无效。若存在最大下控制矩阵，它必须逐项不小于 \(A,B\)，每一行就至少给出 \(2d\) 的下界，同样无效。

   即使只有一个分量，扩展距离也会导致最优上界不取到。例如
   \[
   S=\mathcal X=\{\bot,a\},\qquad d(\bot,a)=\infty,
   \qquad\phi=\mathrm{id}.
   \]
   每个 \(u>0\) 都是上界系数，但 \(u=0\) 不是；可行系数的下确界为 \(0\)，却不是可行系数。

   因此，以可行矩阵族 \(\mathsf U_\phi(S),\mathsf L_\phi(S)\) 作为定义更稳妥；塌缩矩阵 \(\Gamma^\phi(S)\) 则确实有上述天然最大值。

6. **吸收元使全空间下界与有效域下界产生实质差别。**

   若存在 \(x\ne\bot\) 满足 \(\phi(x)=\bot\)，那么在 \(S=\mathcal X\) 上，唯一的下控制矩阵是零矩阵。

   对点对 \((x,\bot)\)，输入的每个距离都是 \(\infty\)，输出距离却全为零。因此任何正元素 \(L_{ij}>0\) 都会要求
   \[
   \infty=L_{ij}\cdot\infty
   \le d_i(\phi(x),\phi(\bot))=0,
   \]
   不可能成立。

   所以，若希望研究部分算子在有效输入上的扩张或非退化性质，应使用 \(S=\operatorname{dom}\phi\)。全空间版本则同时约束有效与失效的行为。

最后给出一个说明塌缩阈值具有独立信息的例子。取一个分量，
\[
\mathcal X=\{\bot,a,b,c\},\qquad
d(a,b)=1,\quad d(a,c)=d(b,c)=2,
\]
并按 CH1 将 \(\bot\) 与其余点的距离设为 \(\infty\)。定义两个固定 \(\bot\) 的算子：
\[
\phi(a)=\phi(b)=a,\qquad\phi(c)=c,
\]
\[
\eta(a)=\eta(c)=a,\qquad\eta(b)=b.
\]
直接检查各点对可知，两者的最优标量上界均为 \(1\)，最优标量下界均为 \(0\)，但是
\[
\Gamma^\phi(\mathcal X)=2,\qquad
\Gamma^\eta(\mathcal X)=1.
\]
因此，上下 Lipschitz 界相同，并不决定塌缩阈值。对 \(\phi\)，距离小于 \(2\) 的输入点对都被合并为不可区分的输出，但距离恰为 \(2\) 的点对仍可区分，也说明严格不等号为何必要。

还应注意，正的统一塌缩阈值是一项较强性质：沿着步长均小于该阈值的有限点链，输出零距离会由三角不等式传递。于是，在通常距离的实数区间上，正的统一阈值会迫使整个考察域的输出不可区分。若想描述局部区域内的塌缩，便应明确选取相应的 \(S\)。

可以据此将
\[
\boxed{\quad
\bigl(\mathsf U_\phi(S),\ \mathsf L_\phi(S),\
\Gamma^\phi(S)\bigr)
\quad}
\]
作为任意算子的统一控制数据，允许 \(\mathsf U_\phi(S)=\varnothing\)。若进一步要求每个算子都拥有某个扩展上控制矩阵，则应将适用的算子类限定为保持全分量零距离的算子。