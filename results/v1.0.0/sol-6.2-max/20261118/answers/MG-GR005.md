## S1　原始记录

取 \(x_0\in E\) 使 \(f(x_0)<+\infty\)。由 \(f\ge 0\) 得 \(g_F\ge 0\)，且 \(g_F(q_Fx_0)\le f(x_0)<+\infty\)。

任取 \((y_i,t_i)\in\operatorname{epi}_{\mathbb R}(g_F)\)（\(i=1,2\)）和 \(\varepsilon>0\)。由下确界的定义，可取 \(x_i\) 使 \(q_Fx_i=y_i\) 且 \(f(x_i)<t_i+\varepsilon\)。对 \(0\le\lambda\le 1\)，由 \(q_F\) 的线性和 \(f\) 的凸性，
\[
g_F\bigl(\lambda y_1+(1-\lambda)y_2\bigr)
\le f\bigl(\lambda x_1+(1-\lambda)x_2\bigr)
\le \lambda t_1+(1-\lambda)t_2+\varepsilon .
\]
令 \(\varepsilon\downarrow 0\)，即得 \(g_F\) 的实高度上图为凸集。

若 \(F\subset K\)，则 \(q_F=r_{KF}q_K\)。按 \(q_Kx\) 对 \(q_F\) 的纤维分组，得到
\[
g_F(y)=\inf_{r_{KF}z=y}\ \inf_{q_Kx=z} f(x)
      =\inf_{r_{KF}z=y}g_K(z).
\]
空纤维按 \(+\infty\) 处理。凸性证明只用到对有限下确界的逼近，分组公式也无需下确界取到。

## S2　紧次水平集

记 \(C_a=\{x\in E:f(x)\le a\}\)。对实数 \(a\)，由 \(x\mapsto(x,a)\) 的连续性和 \(f\) 的闭上图可知 \(C_a\) 闭。\(q_F\) 也连续，因为在 \(F\) 的一组基下，它的坐标就是有限个连续线性泛函。

固定 \(y\) 使 \(\alpha=g_F(y)<+\infty\)。对每个 \(n\ge 1\)，集合
\[
q_F^{-1}(\{y\})\cap C_{\alpha+1/n}
\]
由下确界的定义非空。这些集合是紧集 \(C_{\alpha+1}\) 中递减的闭子集，所以交集非空。交集中任一点 \(x\) 都满足 \(q_Fx=y\) 且 \(f(x)\le\alpha\)，而下确界的定义给出 \(f(x)\ge\alpha\)。故纤维下确界取到。

因此，对每个实数 \(c\)，
\[
\{y:g_F(y)\le c\}=q_F(C_c).
\]
右侧是紧集在连续映射下的像，在 Hausdorff 空间 \(F^*\) 中闭。若 \(t<g_F(y)\)，可选实数 \(c\) 使 \(t<c<g_F(y)\)。此时 \((F^*\setminus q_F(C_c))\times(-\infty,c)\) 是 \((y,t)\) 的开邻域，且与 \(g_F\) 的上图不交。故 \(g_F\) 下半连续。

## S3　兼容成本记录的实现

在紧集 \(C_c\) 中，对每个有限维 \(F\) 取闭子集
\[
A_F=C_c\cap q_F^{-1}(\{y_F\}).
\]
由 \(g_F(y_F)\le c<+\infty\) 和 S2 的取到性，\(A_F\) 非空。对任意有限多个 \(F_1,\ldots,F_m\)，令 \(K=F_1+\cdots+F_m\)。兼容条件和 \(q_{F_i}=r_{KF_i}q_K\) 给出
\[
\varnothing\ne A_K\subseteq \bigcap_{i=1}^m A_{F_i}.
\]
由紧性和有限交性质，可在 \(\bigcap_F A_F\) 中取 \(x\)。按定义，\(q_Fx=y_F\) 对所有 \(F\) 成立，且 \(f(x)\le c\)。

若 \(x'\) 也实现全部记录，则取 \(F=\operatorname{span}\{\phi\}\) 可知 \(\phi(x-x')=0\) 对每个 \(\phi\in E'\) 成立。实 Hausdorff 局部凸空间的连续对偶由 Hahn–Banach 定理分离点，故 \(x=x'\)。

## S4　一般成本的恢复

可以恢复。先说明闭上图如何给出所需的下界。对非负凸函数 \(u\)，令
\[
D=\overline{\operatorname{epi}_{\mathbb R}(u)}.
\]
\(D\) 闭且凸，仍包含于非负高度区域，并且在向上平移后仍包含于自身。最后一条由原上图的同一性质和高度平移的连续性得到。因此，\(D\) 在每个底点的竖直截面或者为空，或者为某个闭射线 \([a,+\infty)\)，其中 \(a\ge 0\)。分别赋值 \(+\infty\) 和 \(a\)，得到非负下半连续凸函数 \(\bar u\)，其上图恰为 \(D\)。

函数的逐点序与实高度上图的包含关系反向。这个关系也适用于取 \(-\infty\) 或 \(+\infty\) 的函数，因为这两个值对应的竖直截面分别是 \(\mathbb R\) 和空集。因此 \(\bar u\le u\)，而任何下半连续凸下界的上图都包含 \(D\)，从而该下界逐点小于等于 \(\bar u\)。

用全部有限维记录构造
\[
G(x)=\sup_{\substack{F\subseteq E'\\ \dim F<\infty}}\bar g_F(q_Fx).
\]
若 \(F\subset K\)，由 S1 可知 \(\bar g_F\circ r_{KF}\le g_K\)。由于 \(r_{KF}\) 连续且线性，\(\bar g_F\circ r_{KF}\) 的上图是闭凸上图在连续线性映射下的原像。于是由 \(\bar g_K\) 的最大性，
\[
\bar g_F\circ r_{KF}\le\bar g_K,\qquad
\bar g_F\circ q_F\le\bar g_K\circ q_K .
\tag{1}
\]
所以扩大观测空间时，拉回到 \(E\) 的下界逐点递增。

为证明 \(G\) 的最大性，记 \(A=\operatorname{epi}_{\mathbb R}(f)\)，并令 \(P_F(x,t)=(q_Fx,t)\)。有
\[
\overline{P_F(A)}=\overline{\operatorname{epi}_{\mathbb R}(g_F)}.
\tag{2}
\]
一方面，\(P_F(A)\subseteq\operatorname{epi}_{\mathbb R}(g_F)\)。另一方面，若 \(g_F(y)\le t\) 且 \(t\in\mathbb R\)，则对每个 \(\varepsilon>0\)，可在纤维中选到 \(x\) 使 \(f(x)<t+\varepsilon\)，从而 \((y,t+\varepsilon)\in P_F(A)\)。令 \(\varepsilon\downarrow0\) 即得反向的闭包包含。

由 \(G\) 的定义和 (2)，
\[
\operatorname{epi}_{\mathbb R}(G)=\bigcap_F P_F^{-1}\bigl(\overline{P_F(A)}\bigr).
\tag{3}
\]
各 \(P_F\) 连续，故右侧包含 \(\overline A\)。反过来，若 \((x,t)\notin\overline A\)，则 \(E\times\mathbb R\) 是实 Hausdorff 局部凸空间，且 \(\overline A\) 非空、闭、凸，可用 Hahn–Banach 分离定理严格分离该点与 \(\overline A\)。于是存在 \(\phi\in E'\) 及实数 \(a,b\)，使
\[
\phi(x)+at>b,\qquad \phi(u)+as\le b\quad ((u,s)\in\overline A).
\]
取 \(F=\operatorname{span}\{\phi\}\)。闭半空间 \(\{(y,s):y(\phi)+as\le b\}\) 包含 \(\overline{P_F(A)}\)，而 \(P_F(x,t)\) 落在该半空间之外。因此 \((x,t)\) 也在 (3) 右侧之外，证明了
\[
\operatorname{epi}_{\mathbb R}(G)=\overline{\operatorname{epi}_{\mathbb R}(f)}.
\]
故 \(G\) 下半连续、凸，且 \(G\le f\)。若题设中的 \(h\le f\)，则 \(h\) 的闭上图包含 \(A\)，也包含 \(\overline A\)，所以 \(h\le G\)。

## S5　闭成本的有限投影

**不一定。** 取
\[
C=\{(a,b)\in\mathbb R^2:a\ge 0,\ b\ge 0,\ ab\ge 1\}.
\]
\(C\) 由连续函数的闭不等式定义，因此闭。它也可写成 \(\{(a,b):a>0,\ b\ge 1/a\}\)。由于 \(a\mapsto 1/a\) 在 \((0,+\infty)\) 上的二阶导数为 \(2/a^3>0\)，\(C\) 凸。令 \(f\) 在 \(C\) 上取 \(0\)，其余处取 \(+\infty\)。其上图为闭凸集 \(C\times[0,+\infty)\)，且 \(f(1,1)=0\)。

取 \(\phi(a,b)=a\) 和 \(F=\operatorname{span}\{\phi\}\)，用 \(y(\phi)\) 将 \(F^*\) 识别为 \(\mathbb R\)。当 \(y>0\) 时，纤维含 \((y,1/y)\in C\)。当 \(y\le 0\) 时，纤维与 \(C\) 不交。因此
\[
g_F(y)=
\begin{cases}
0,&y>0,\\
+\infty,&y\le 0.
\end{cases}
\]
上图中的 \((1/n,0)\) 收敛到上图之外的 \((0,0)\)，故 \(g_F\) 不下半连续。

## S6　恢复与投影的精确关系

由 S4，\(G\) 的上图是 \(f\) 的上图的闭包。实高度上图唯一确定函数，所以 \(G=f\) 当且仅当 \(f\) 的上图闭，也就是 \(f\) 下半连续。

对 \(F\subset K\)，令 \(p(y)=\inf_{r_{KF}z=y}\bar g_K(z)\)。因 \(r_{KF}\) 线性，S1 的纤维逼近论证给出 \(p\) 非负且凸。取一个使 \(g_K\) 有限的 \(z\)，则 \(p(r_{KF}z)\le\bar g_K(z)\le g_K(z)<+\infty\)。由 \(\bar g_K\le g_K\) 和 S1 得 \(p\le g_F\)。另一方面，对 (1) 在纤维上取下确界，得 \(\bar g_F\le p\)。由最大下半连续凸下界的定义，
\[
\bar g_F\le\bar p\le\bar g_F.
\]
这就证明了所求等式。

**最外层的上横线不能总省去。** 沿用 S5 的例子，取 \(K=E'\)。在两个坐标泛函给出的坐标下，\(q_K\) 是 \(E\) 到 \(K^*\) 的线性同胚，\(r_{KF}\) 是第一坐标投影。于是 \(g_K\) 对应于 \(f\)，已经下半连续，故 \(\bar g_K=g_K\)。此时 \(p=g_F\)，所以 \(p(0)=+\infty\)，而由 S5 的上图极限点及非负性得 \(\bar g_F(0)=0\)。