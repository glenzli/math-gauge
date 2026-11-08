## S1　原始记录

对每个有限维 \(F\subset E'\)，\(g_F\) 非负，因为它是 \(f\) 在纤维上的下确界，而空纤维的下确界规定为 \(+\infty\)。若 \(f(x_0)<\infty\)，则
\[
g_F(q_Fx_0)\le f(x_0)<\infty.
\]

证明凸性。若 \(g_F(y_0),g_F(y_1)<\infty\)，对任意 \(\varepsilon>0\)，可取 \(x_i\) 使
\[
q_Fx_i=y_i,\qquad f(x_i)\le g_F(y_i)+\varepsilon
\quad(i=0,1).
\]
于是对 \(0\le\lambda\le1\)，
\[
g_F((1-\lambda)y_0+\lambda y_1)
\le (1-\lambda)g_F(y_0)+\lambda g_F(y_1)+\varepsilon.
\]
令 \(\varepsilon\downarrow0\)，得到凸性；涉及 \(+\infty\) 的情形由上图定义直接处理。

若 \(F\subset K\)，则 \(q_F=r_{KF}\circ q_K\)。因此，对每个 \(y\in F^*\)，
\[
\begin{aligned}
\inf_{r_{KF}z=y}g_K(z)
&=\inf_{r_{KF}z=y}\ \inf_{q_Kx=z}f(x)\\
&=\inf_{q_Fx=y}f(x)
=g_F(y).
\end{aligned}
\]
这里允许空集下确界为 \(+\infty\)。上述证明**不需要**任何纤维下确界取到。

## S2　紧次水平集

固定 \(F\) 和满足 \(g_F(y)<\infty\) 的 \(y\)，记 \(a=g_F(y)\)。对每个正整数 \(n\)，集合
\[
C_n=\{x:q_Fx=y,\ f(x)\le a+1/n\}
\]
非空：这是下确界的定义。映射 \(q_F\) 连续，故纤维闭；按假设，\(f\) 的有限实数次水平集紧。因此每个 \(C_n\) 都是紧集，且这些集合递减。它们在紧集 \(C_1\) 中具有有限交性质，所以
\[
\bigcap_{n\ge1}C_n\ne\varnothing.
\]
任取其中的 \(x\)，便有 \(q_Fx=y\) 且 \(f(x)\le a\)。由 \(a\) 的定义，\(f(x)=a\)，即纤维下确界取到。

现在对任意实数 \(c\)，
\[
\{y:g_F(y)\le c\}=q_F(\{x:f(x)\le c\}).
\]
从左到右使用刚证明的取到性；反向包含显然成立。右边是紧集的连续像，因 \(F^*\) 为有限维 Hausdorff 空间，故闭。因此 \(g_F\) 的所有实次水平集闭，也就是 \(g_F\) 下半连续。

## S3　兼容成本记录的实现

令
\[
C=\{x\in E:f(x)\le c\}.
\]
该集合紧。对每个有限维 \(F\subset E'\)，令
\[
C_F=C\cap\{x:q_Fx=y_F\}.
\]
它是 \(C\) 的闭子集。由于 \(g_F(y_F)\le c<\infty\)，S2 的取到性给出 \(C_F\ne\varnothing\)。

这些闭集具有有限交性质。事实上，对有限多个 \(F_1,\ldots,F_n\)，令
\[
K=F_1+\cdots+F_n.
\]
任取 \(x\in C_K\)。兼容性给出
\[
q_{F_i}x=r_{KF_i}q_Kx=r_{KF_i}y_K=y_{F_i},
\]
故 \(x\in\bigcap_i C_{F_i}\)。由 \(C\) 的紧性，存在
\[
x\in\bigcap_F C_F.
\]
这个 \(x\) 满足全部 \(q_Fx=y_F\)，并且 \(f(x)\le c\)。

它也是唯一的：若 \(x,x'\) 满足相同记录，则对每个 \(\phi\in E'\)，取 \(F=\operatorname{span}\{\phi\}\) 可得 \(\phi(x-x')=0\)。Hausdorff 局部凸空间的连续对偶分离点，因此 \(x=x'\)。

## S4　一般成本的恢复

**结论：可以。** 对每个 \(F\)，令 \(\overline{g_F}\) 的实上图为 \(g_F\) 的实上图在 \(F^*\times\mathbb R\) 中的闭包，并定义
\[
\boxed{\displaystyle G(x)=\sup_{F\subset E',\ \dim F<\infty}
\overline{g_F}(q_Fx).}
\]

这个定义有效：\(g_F\ge0\)，所以其上图闭包仍位于 \(F^*\times[0,\infty)\) 中。该闭包是闭凸且向上封闭的集合，其每个非空竖直截面都是闭射线；因此它恰是某个 \([0,\infty]\) 值闭凸函数的上图。于是 \(\overline{g_F}\) 是 \(g_F\) 的最大下半连续凸下界。

每个 \(x\mapsto\overline{g_F}(q_Fx)\) 下半连续且凸，并满足
\[
\overline{g_F}(q_Fx)\le g_F(q_Fx)\le f(x).
\]
故 \(G\) 下半连续、凸，且 \(G\le f\)。

下面证明包括允许取 \(-\infty\) 的竞争函数在内的最大性。记
\[
A=\operatorname{epi}_{\mathbb R}(f),\qquad
Q_F=q_F\times\operatorname{id}_{\mathbb R}.
\]
首先，
\[
\overline{Q_F(A)}
=\overline{\operatorname{epi}_{\mathbb R}(g_F)}.
\tag{1}
\]
一侧包含显然；另一侧成立是因为若 \(g_F(y)\le t<\infty\)，则对每个 \(\varepsilon>0\)，存在 \(q_Fx=y\) 且 \(f(x)<t+\varepsilon\)，所以 \((y,t+\varepsilon)\in Q_F(A)\)。

赋予 \(E\) 弱拓扑 \(\sigma(E,E')\)。其有限坐标邻域由各种 \(q_F\) 给出，因而
\[
\operatorname{cl}_{\sigma(E,E')\times\mathbb R}A
=\bigcap_F Q_F^{-1}\bigl(\overline{Q_F(A)}\bigr).
\tag{2}
\]
\(A\) 是凸集。由局部凸空间的 Hahn–Banach 分离定理，凸集在原拓扑与 \(\sigma(E,E')\) 下的闭包相同：两种拓扑有相同连续对偶，而 \(E\times\mathbb R\) 的连续线性泛函均形如 \((x,t)\mapsto\phi(x)+at\)。结合 (1)、(2)，得到
\[
\operatorname{cl}_{E\times\mathbb R}A
=\bigcap_F\operatorname{epi}_{\mathbb R}
\bigl(\overline{g_F}\circ q_F\bigr)
=\operatorname{epi}_{\mathbb R}(G).
\tag{3}
\]

若 \(h:E\to[-\infty,\infty]\) 下半连续、凸且 \(h\le f\)，则其闭上图包含 \(A\)，因此也包含式 (3) 左边的闭包。于是
\[
\operatorname{epi}_{\mathbb R}(G)\subset
\operatorname{epi}_{\mathbb R}(h),
\]
即 \(h\le G\)。这也覆盖 \(h\) 取 \(-\infty\) 或 \(+\infty\) 的情形。

扩大观测空间时，若 \(F\subset K\)，则
\[
\boxed{\quad
\overline{g_F}(r_{KF}z)\le \overline{g_K}(z),
\qquad
\overline{g_F}(q_Fx)\le\overline{g_K}(q_Kx).
\quad}
\]
这是因为 S1 给出 \(g_F(r_{KF}z)\le g_K(z)\)，对相应上图取闭包即可。故有限观测给出的闭成本下界随观测空间扩大而递增，\(G\) 是它们的上确界。

## S5　闭成本的有限投影

**结论：不一定下半连续。**

在 \(E=\mathbb R^2\) 中取
\[
C=\{(x,y):x>0,\ y\ge 1/x\}
 =\{(x,y):x\ge0,\ xy\ge1\}.
\]
第二个表示式说明 \(C\) 闭；第一个表示式说明 \(C\) 是凸函数 \(x\mapsto1/x\) 在 \((0,\infty)\) 上的上图，故凸。

令 \(f\) 为 \(C\) 的指标函数：在 \(C\) 上为 \(0\)，在 \(C\) 外为 \(+\infty\)。它非负、下半连续、凸，且至少一点有限。

令 \(F\) 由第一坐标泛函生成，并将 \(F^*\) 识别为 \(\mathbb R\)。则
\[
g_F(x)=
\begin{cases}
0,&x>0,\\
+\infty,&x\le0.
\end{cases}
\]
它的零次水平集是非闭集 \((0,\infty)\)，所以 \(g_F\) 不下半连续。

## S6　恢复与投影的精确关系

由 S4，\(G\le f\) 且 \(G\) 下半连续。若 \(G=f\)，则 \(f\) 下半连续。反之，若 \(f\) 下半连续，则 \(f\) 本身是 S4 中允许的竞争函数，故 \(f\le G\)。因此
\[
\boxed{\quad G=f\ \Longleftrightarrow\ f\text{ 下半连续}.\quad}
\]

现设 \(F\subset K\)，令
\[
v(y)=\inf_{r_{KF}z=y}\overline{g_K}(z),
\qquad T=r_{KF}\times\operatorname{id}_{\mathbb R}.
\]
\(v\) 非负、凸且至少一点有限；凸性与 S1 中的近似下确界论证相同。与式 (1) 相同的论证给出
\[
\overline{\operatorname{epi}_{\mathbb R}(v)}
=\overline{T(\operatorname{epi}_{\mathbb R}(\overline{g_K}))}.
\]
又因 \(T\) 连续，且
\(\operatorname{epi}_{\mathbb R}(\overline{g_K})
=\overline{\operatorname{epi}_{\mathbb R}(g_K)}\)，有
\[
\overline{T(\operatorname{epi}_{\mathbb R}(\overline{g_K}))}
=\overline{T(\operatorname{epi}_{\mathbb R}(g_K))}.
\]
S1 的原始记录关系及式 (1) 型论证说明，右边正是
\(\overline{\operatorname{epi}_{\mathbb R}(g_F)}\)。因此两边的闭上图相同，得到
\[
\boxed{\displaystyle
\overline{g_F}
=
\overline{\left(y\mapsto
\inf_{r_{KF}z=y}\overline{g_K}(z)\right)}.}
\]

右式最外层的闭包操作**不能总省去**。沿用 S5 的例子，取 \(K=E'\)。此时 \(q_K:E\to K^*\) 是有限维线性同构，所以在该识别下 \(g_K=f=\overline{g_K}\)。向第一坐标投影得到的函数是 S5 中的 \(g_F\)，它不是下半连续的；而 \(\overline{g_F}\) 下半连续。因此去掉最外层横线后，等式在这个例子中不成立。