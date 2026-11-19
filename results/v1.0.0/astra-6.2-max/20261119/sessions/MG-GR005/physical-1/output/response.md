## S1　原始记录

由 \(f\ge 0\) 和空纤维的约定，\(g_F\ge 0\)。取 \(x_0\in E\) 使 \(f(x_0)<+\infty\)，则 \(g_F(q_Fx_0)\le f(x_0)<+\infty\)。

为证凸性，取 \(g_F\) 的实高度上图中的两点 \((y_0,t_0),(y_1,t_1)\)。对任意 \(\varepsilon>0\)，可取 \(u_i\in E\) 使 \(q_Fu_i=y_i\) 且 \(f(u_i)<t_i+\varepsilon\)。对 \(0\le\lambda\le1\)，由 \(q_F\) 的线性和 \(f\) 的凸性，
\[
g_F((1-\lambda)y_0+\lambda y_1)
\le f((1-\lambda)u_0+\lambda u_1)
\le (1-\lambda)t_0+\lambda t_1+\varepsilon .
\]
令 \(\varepsilon\downarrow0\)，即得上图凸。

若 \(F\subset K\)，则 \(q_F=r_{KF}\circ q_K\)，从而
\[
q_F^{-1}(\{y\})
=\bigcup_{z\in K^*,\,r_{KF}z=y}q_K^{-1}(\{z\}).
\]
在此并集上取下确界即得
\[
g_F(y)=\inf_{r_{KF}z=y}g_K(z).
\]
上述证明均不需要纤维下确界取到。

## S2　紧次水平集

记 \(C_b=\{x\in E\mid f(x)\le b\}\)。对每个有限实数 \(b\)，\(C_b\) 由下半连续性为闭集，并由本阶段假设为紧集。取 \(F\) 的一组基后，\(q_F\) 的各坐标都是连续线性泛函，故 \(q_F\) 连续。

设 \(a=g_F(y)<+\infty\)。由下确界的定义，
\[
C_{a+1/n}\cap q_F^{-1}(\{y\}),\qquad n\ge1,
\]
是紧集 \(C_{a+1}\) 中递减的非空闭集。因此其交中有一点 \(x\)。此点满足 \(q_Fx=y\) 且 \(f(x)\le a\)，而下确界的定义又给出 \(a\le f(x)\)。故 \(f(x)=a\)。

由取到性，对每个有限实数 \(b\) 都有
\[
\{y\in F^*\mid g_F(y)\le b\}=q_F(C_b).
\]
右侧是 Hausdorff 空间 \(F^*\) 中的紧集，因而闭。若 \(g_F(y)>t\)，取实数 \(b\) 使 \(t<b<g_F(y)\)，则 \(\{g_F>b\}\times(-\infty,b)\) 是 \((y,t)\) 的开邻域，且与实高度上图不交。故 \(g_F\) 下半连续。

## S3　兼容成本记录的实现

在紧集 \(C_c\) 中，对每个 \(F\) 定义闭集
\[
D_F=C_c\cap q_F^{-1}(\{y_F\}).
\]
由于 \(g_F(y_F)\le c<+\infty\)，S2 的取到性保证 \(D_F\ne\varnothing\)。对任意有限多个 \(F_1,\ldots,F_m\)，取 \(K=F_1+\cdots+F_m\)。由记录的兼容性，\(D_K\subseteq\bigcap_{i=1}^m D_{F_i}\)。因此这些闭集具有有限交性质，紧性给出
\[
\bigcap_F D_F\ne\varnothing .
\]
取交中一点 \(x\)，即有 \(f(x)\le c\) 且对所有 \(F\) 均有 \(q_Fx=y_F\)。

为证唯一性，若 \(x'\ne x\)，令 \(v=x-x'\)。Hausdorff 局部凸性给出连续半范数 \(p\) 使 \(p(v)>0\)。由 Hahn–Banach 定理，\(\mathbb Rv\) 上的泛函 \(av\mapsto a p(v)\) 可延拓为满足 \(|\varphi|\le p\) 的 \(\varphi\in E'\)。于是 \(\varphi(x)-\varphi(x')=p(v)>0\)，两点在 \(F=\mathbb R\varphi\) 上的记录不同。故所构造的 \(x\) 唯一。

## S4　一般成本的恢复

**可以。** 以下用 \(\operatorname{epi}u\) 表示实高度上图。对于非负凸函数 \(u\)，闭集 \(\overline{\operatorname{epi}u}\) 凸，且其中任一点向上平移任意非负高度后仍在其中。由于所有高度均非负，每个底点上的竖直截面或为空，或为闭射线 \([a,+\infty)\)。分别赋值 \(+\infty\) 或 \(a\)，就得到非负下半连续凸函数 \(\bar u\)，满足
\[
\operatorname{epi}\bar u=\overline{\operatorname{epi}u},\qquad \bar u\le u.
\]
对任意下半连续凸函数 \(h\le u\)，即使它同时取两种无穷值，其上图仍是包含 \(\operatorname{epi}u\) 的闭集，因而包含 \(\operatorname{epi}\bar u\)。这给出 \(h\le\bar u\)，证明了最大性。

仅用有限维记录即可构造
\[
\boxed{\displaystyle G(x)=\sup_{\substack{F\subset E'\\ \dim F<\infty}}\bar g_F(q_Fx).}
\]
为验证此式，记 \(P_F(x,t)=(q_Fx,t)\)。由下确界的定义，\(P_F(\operatorname{epi}f)\subseteq\operatorname{epi}g_F\)。对每个 \((y,t)\in\operatorname{epi}g_F\) 和 \(n\ge1\)，又可取 \(q_Fu=y\) 且 \(f(u)<t+1/n\)，故 \((y,t+1/n)\in P_F(\operatorname{epi}f)\)。于是
\[
\overline{P_F(\operatorname{epi}f)}=\operatorname{epi}\bar g_F.
\]

令 \(C=\overline{\operatorname{epi}f}\)。由 \(G\) 的定义，
\[
\operatorname{epi}G
=\bigcap_F P_F^{-1}\!\left(\overline{P_F(\operatorname{epi}f)}\right)
\supseteq C,
\]
其中每个逆像都是包含 \(\operatorname{epi}f\) 的闭集。为证反向包含，取 \((x,t)\notin C\)。空间 \(E\times\mathbb R\) 实 Hausdorff 局部凸，且 \(C\) 是非空闭凸集，故 Hahn–Banach 点与闭凸集的严格分离定理适用。乘积空间上的连续线性泛函形如 \((u,s)\mapsto\varphi(u)+bs\)，因此存在 \(\varphi\in E'\) 和 \(b,\alpha\in\mathbb R\) 使
\[
\varphi(x)+bt<\alpha\le\varphi(u)+bs
\qquad\bigl((u,s)\in C\bigr).
\]
取 \(F=\operatorname{span}\{\varphi\}\)。连续泛函 \((y,s)\mapsto y(\varphi)+bs\) 在 \(P_F(\operatorname{epi}f)\) 及其闭包上均至少为 \(\alpha\)，在 \(P_F(x,t)\) 处却小于 \(\alpha\)。故 \((x,t)\notin\operatorname{epi}G\)。这就证明了 \(\operatorname{epi}G=C\)，即 \(G=\bar f\)，从而 \(G\) 具有题设的全部性质。

扩大观测空间时，S1 给出 \(\bar g_F\circ r_{KF}\le g_F\circ r_{KF}\le g_K\)。由于 \(r_{KF}\) 连续线性，左端是下半连续凸函数。由 \(\bar g_K\) 的最大性，
\[
\boxed{\bar g_F(r_{KF}z)\le\bar g_K(z)\qquad(z\in K^*).}
\]
取 \(z=q_Kx\)，可见定义 \(G(x)\) 的各项随 \(F\) 扩大而单调不减。

## S5　闭成本的有限投影

**不一定。** 在 \(\mathbb R^2\) 中取
\[
C=\{(a,b)\mid a>0,\ b\ge1/a\},\qquad
f(a,b)=
\begin{cases}
0,&(a,b)\in C,\\
+\infty,&(a,b)\notin C.
\end{cases}
\]
函数 \(a\mapsto 1/a\) 在 \((0,\infty)\) 上凸，故 \(C\) 凸。又有
\[
C=\{(a,b)\mid a\ge0,\ b\ge0,\ ab\ge1\},
\]
故 \(C\) 闭。因此 \(\operatorname{epi} f=C\times[0,\infty)\) 闭且凸，并且 \(f(1,1)=0\)。

令 \(\pi_1(a,b)=a\)，取 \(F=\mathbb R\pi_1\)，用 \(y(\pi_1)\) 将 \(F^*\) 与 \(\mathbb R\) 等同。对 \(a>0\)，纤维中有 \((a,1/a)\in C\)。对 \(a\le0\)，纤维与 \(C\) 不交。故
\[
g_F(a)=
\begin{cases}
0,&a>0,\\
+\infty,&a\le0.
\end{cases}
\]
其上图含有每个 \((1/n,0)\)，却不含极限点 \((0,0)\)，所以 \(g_F\) 不下半连续。

## S6　恢复与投影的精确关系

若 \(f\) 下半连续，由共同设定它已凸，故 \(f\) 本身可作为 S4 的竞争函数，得到 \(f\le G\le f\)。反过来，若 \(G=f\)，则由 \(G\) 下半连续可知 \(f\) 下半连续。故 \(G=f\) 当且仅当 \(f\) 下半连续。

对 \(F\subset K\)，记
\[
p(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
由 S1 对线性映射纤维的同一逼近论证，\(p\) 非负且凸。因 \(\bar g_K\le g_K\) 且 \(g_K\) 至少一点有限，\(p\) 也至少一点有限。由 S4 的观测空间扩大关系和 S1 的下确界等式，
\[
\bar g_F(y)\le p(y)\le\inf_{r_{KF}z=y}g_K(z)=g_F(y).
\]
于是 \(\bar g_F\) 是 \(p\) 的下半连续凸下界，故 \(\bar g_F\le\bar p\)。同样，\(\bar p\le p\le g_F\) 给出 \(\bar p\le\bar g_F\)。因此
\[
\boxed{\displaystyle
\bar g_F=\overline{\left(y\longmapsto\inf_{r_{KF}z=y}\bar g_K(z)\right)}.}
\]

**最外层的 \(\bar{\cdot}\) 一般不能省去。** 在 S5 的例子中取 \(K=E'\)。由有限维双对偶的自然识别，\(q_K\) 是同构，故 \(g_K=f=\bar g_K\)。此时 \(p=g_F\)，在 \(0\) 处取值 \(+\infty\)。而 \(\operatorname{epi}g_F=(0,\infty)\times[0,\infty)\) 的闭包为 \([0,\infty)\times[0,\infty)\)，故 \(\bar g_F(0)=0\)。