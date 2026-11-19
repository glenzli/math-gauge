## S1　原始记录

由于 \(f\ge 0\)，有 \(g_F\ge 0\)。取一点 \(x_0\) 使 \(f(x_0)<+\infty\)，则 \(g_F(q_Fx_0)\le f(x_0)<+\infty\)。

为证明凸性，取 \((y_i,t_i)\in\operatorname{epi}_{\mathbb R}(g_F)\)，其中 \(i=1,2\)。对任意 \(\varepsilon>0\)，由下确界的定义可取 \(x_i\) 满足 \(q_Fx_i=y_i\) 且 \(f(x_i)<t_i+\varepsilon\)。对任意 \(\lambda\in[0,1]\)，由 \(q_F\) 线性和 \(f\) 凸，
\[
g_F\bigl(\lambda y_1+(1-\lambda)y_2\bigr)
\le f\bigl(\lambda x_1+(1-\lambda)x_2\bigr)
\le \lambda t_1+(1-\lambda)t_2+\varepsilon.
\]
令 \(\varepsilon\downarrow 0\)，得到实高度上图的凸性。

若 \(F\subset K\)，则 \(q_F=r_{KF}q_K\)。因此 \(q_F^{-1}(y)\) 是满足 \(r_{KF}z=y\) 的各个纤维 \(q_K^{-1}(z)\) 的并。在这些纤维上分别取下确界，再取总下确界，得到
\[
g_F(y)=\inf_{\{z\in K^*:r_{KF}z=y\}}g_K(z).
\]
空纤维按约定贡献 \(+\infty\)。上述论证均无需纤维下确界取到。

## S2　紧次水平集

\(q_F\) 连续，因为选定 \(F\) 的一组基后，\(q_F\) 的坐标正是这些基元素所给出的连续线性泛函。由 \(f\) 的实高度上图闭，通过映射 \(x\mapsto(x,c)\) 取原像可知，每个实数 \(c\) 对应的次水平集 \(\{f\le c\}\) 都闭。

固定 \(y\in F^*\) 使 \(m=g_F(y)<+\infty\)。对 \(n\ge1\)，令
\[
A_n=\{x:q_Fx=y,\ f(x)\le m+1/n\}.
\]
由下确界的定义，每个 \(A_n\) 都非空。它们递减，且都是紧集 \(\{f\le m+1\}\) 的闭子集，因此由紧性，\(\bigcap_n A_n\ne\varnothing\)。其中任一点 \(x\) 都满足 \(q_Fx=y\) 和 \(f(x)\le m\)，再由 \(m\) 的定义得到 \(f(x)=m\)。

所以对每个有限实数 \(c\)，
\[
\{y:g_F(y)\le c\}=q_F(\{x:f(x)\le c\}).
\]
右侧是紧集在连续映射下的像，在 Hausdorff 空间 \(F^*\) 中闭。若 \((y,t)\) 不在 \(g_F\) 的实高度上图中，取实数 \(c\) 使 \(t<c<g_F(y)\)，则 \(\{g_F>c\}\times(-\infty,c)\) 是包含 \((y,t)\) 且与上图不相交的开集。因此 \(g_F\) 下半连续。

## S3　兼容成本记录的实现

在紧集 \(L=\{x:f(x)\le c\}\) 中，对每个 \(F\) 定义
\[
B_F=\{x\in L:q_Fx=y_F\}.
\]
由 \(q_F\) 连续，\(B_F\) 在 \(L\) 中闭。由 \(g_F(y_F)\le c<+\infty\) 和 S2 的取到性，\(B_F\) 非空。

对任意有限多个 \(F_1,\ldots,F_n\)，令 \(K=F_1+\cdots+F_n\)。兼容条件给出 \(B_K\subseteq\bigcap_{i=1}^n B_{F_i}\)。故这些闭集具有有限交性质，由 \(L\) 的紧性，
\[
\bigcap_F B_F\ne\varnothing.
\]
取交集中的一点 \(x\)，它满足全部观测条件和 \(f(x)\le c\)。

若 \(x'\) 也满足全部观测条件，对每个 \(\phi\in E'\) 取 \(F=\operatorname{span}\{\phi\}\)，便有 \(\phi(x-x')=0\)。因 \(E\) 是实 Hausdorff 局部凸空间，Hahn–Banach 定理保证 \(E'\) 分离点，故 \(x=x'\)。

## S4　一般成本的恢复

**可以恢复。** 先说明如何从上图得到下半连续凸下界。对任意非负凸函数 \(u\)，其实高度上图的闭包仍然凸，位于非负高度，且对任意非负的竖直平移封闭。因此，它在每个底点处的高度纤维或者为空，或者是某个闭射线 \([a,+\infty)\)。把这两种纤维分别赋值为 \(+\infty\) 和 \(a\)，得到函数 \(\bar u\)，满足
\[
\operatorname{epi}_{\mathbb R}(\bar u)
=\overline{\operatorname{epi}_{\mathbb R}(u)}.
\]
它下半连续、凸，并且 \(\bar u\le u\)。若 \(h\le u\) 且 \(h\) 下半连续，则 \(h\) 的闭上图包含 \(u\) 的上图，也就包含其闭包，故 \(h\le\bar u\)。这里上图包含关系反转函数的点态次序，因为函数值等于实高度纤维的下确界，空纤维和整条实轴分别对应 \(+\infty\) 和 \(-\infty\)。

令 \(C=\operatorname{epi}_{\mathbb R}(f)\)，并记 \(T_F(x,t)=(q_Fx,t)\)。由下确界的定义，
\[
T_F(C)\subseteq \operatorname{epi}_{\mathbb R}(g_F)
\subseteq\overline{T_F(C)}.
\]
第二个包含关系成立，是因为若 \(g_F(y)\le t\in\mathbb R\)，则对每个 \(\varepsilon>0\)，可取 \(q_Fx=y\) 且 \(f(x)<t+\varepsilon\)，从而 \((y,t+\varepsilon)\in T_F(C)\)。因此
\[
\operatorname{epi}_{\mathbb R}(\bar g_F)=\overline{T_F(C)}.
\]
由全部记录定义
\[
G(x)=\sup_F \bar g_F(q_Fx).
\]
它的实高度上图为
\[
\operatorname{epi}_{\mathbb R}(G)
=\bigcap_F T_F^{-1}\bigl(\overline{T_F(C)}\bigr)
=\overline C.
\]
为证明最后一个等号，连续性给出 \(\overline C\) 包含于右侧各原像。反过来，若 \(p\notin\overline C\)，则 \(\overline C\) 是实 Hausdorff 局部凸空间 \(E\times\mathbb R\) 中的非空闭凸集。由 Hahn–Banach 严格分离定理，存在连续线性泛函 \(\ell(x,t)=\phi(x)+at\)，其中 \(\phi\in E'\)、\(a\in\mathbb R\)，使 \(\ell(p)>\sup_C\ell\)。取 \(F=\operatorname{span}\{\phi\}\)，则 \(\ell(x,t)=\lambda(T_F(x,t))\)，其中 \(\lambda(y,t)=y(\phi)+at\) 连续。于是 \(\lambda(T_Fp)>\sup_{T_F(C)}\lambda\)，故 \(T_Fp\notin\overline{T_F(C)}\)。

由上图等式，\(G=\bar f\)，所以 \(G\) 非负、下半连续、凸且 \(G\le f\)。按上述上图包含关系，题设允许取 \(-\infty\) 或 \(+\infty\) 的每个竞争函数 \(h\) 都满足 \(h\le G\)。

扩大观测空间时，若 \(F\subset K\)，连续映射 \((z,t)\mapsto(r_{KF}z,t)\) 把 \(T_K(C)\) 映到 \(T_F(C)\)，故把 \(\overline{T_K(C)}\) 映入 \(\overline{T_F(C)}\)。因此
\[
\bar g_F\circ r_{KF}\le\bar g_K,
\qquad
\bar g_F\circ q_F\le\bar g_K\circ q_K.
\]
所以构成 \(G\) 的各项随观测空间增大而单调上升。

## S5　闭成本的有限投影

**未必下半连续。** 在 \(\mathbb R^2\) 中取
\[
D=\{(a,b):b\ge e^a\},\qquad
f(a,b)=
\begin{cases}
0,&(a,b)\in D,\\
+\infty,&(a,b)\notin D.
\end{cases}
\]
指数函数连续且凸，故其上图 \(D\) 闭且凸。因此 \(\operatorname{epi}_{\mathbb R}(f)=D\times[0,+\infty)\) 闭且凸，且 \(f(0,1)=0\)。

令 \(F\) 由第二坐标泛函 \(\pi_2(a,b)=b\) 张成，用 \(y\mapsto y(\pi_2)\) 将 \(F^*\) 识别为 \(\mathbb R\)。固定第二坐标 \(b\) 的纤维与 \(D\) 相交当且仅当 \(b>0\)。确实，\(e^a>0\)，而对 \(b>0\) 可取 \(a=\log b\)。因此 \(g_F\) 在 \((0,+\infty)\) 上等于 \(0\)，在其余点等于 \(+\infty\)。其实高度上图包含 \((1/n,0)\) 却不包含极限 \((0,0)\)，故 \(g_F\) 不下半连续。

## S6　恢复与投影的精确关系

由 S4，\(G=f\) 当且仅当 \(\operatorname{epi}_{\mathbb R}(f)\) 等于其闭包，也就是 \(f\) 下半连续。

对 \(F\subset K\)，令
\[
v(y)=\inf_{\{z:r_{KF}z=y\}}\bar g_K(z).
\]
\(\bar g_K\) 非负、凸且至少一点有限。由于 \(r_{KF}\) 线性，S1 中用近似最小值证明凸性的论证同样适用，故 \(v\) 也非负、凸且至少一点有限。由 S4 的单调关系，\(\bar g_F(y)\le v(y)\)。再由 \(\bar g_K\le g_K\) 和 S1 的投影公式，\(v(y)\le g_F(y)\)。于是
\[
\bar g_F\le v\le g_F.
\]
由于 \(\bar g_F\) 是 \(v\) 的下半连续凸下界，有 \(\bar g_F\le\bar v\)。由于 \(\bar v\le v\le g_F\)，又有 \(\bar v\le\bar g_F\)。这就证明了
\[
\bar g_F
=\overline{\left(y\mapsto\inf_{\{z:r_{KF}z=y\}}\bar g_K(z)\right)}.
\]

**最外层的闭化不能总省去。** 沿用 S5 的例子，取 \(K=E'\)。此时 \(q_K\) 是有限维线性同构，每个 \(q_K\) 纤维恰有一点，故 \(g_K=f\circ q_K^{-1}\) 下半连续，\(\bar g_K=g_K\)。由 S1，上式中的 \(v\) 就是 \(g_F\)，所以 \(v(0)=+\infty\)。而 \(\operatorname{epi}_{\mathbb R}(g_F)=(0,+\infty)\times[0,+\infty)\) 的闭包包含 \((0,0)\)，故 \(\bar g_F(0)=0\)。