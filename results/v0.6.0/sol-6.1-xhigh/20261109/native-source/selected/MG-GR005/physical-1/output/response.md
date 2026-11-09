以下 \(\operatorname{epi}\) 均指题设的实高度上图。选取 \(F\) 的基即可将 \(F^*\) 识别为有限维欧氏空间，因而 \(q_F\) 是连续线性映射；\(r_{KF}\) 也连续，且
\[
q_F=r_{KF}\circ q_K.
\]

**S1.**

由 \(f\ge0\)，立即有 \(g_F\ge0\)。取 \(f(x_0)<\infty\)，则
\[
g_F(q_Fx_0)\le f(x_0)<\infty.
\]

证明凸性。设 \(g_F(y_i)<\infty\)，\(0<\lambda<1\)。给定 \(\varepsilon>0\)，可取
\[
q_Fx_i=y_i,\qquad f(x_i)\le g_F(y_i)+\varepsilon.
\]
由 \(f\) 的凸性，
\[
g_F(\lambda y_1+(1-\lambda)y_2)
\le f(\lambda x_1+(1-\lambda)x_2)
\le\lambda g_F(y_1)+(1-\lambda)g_F(y_2)+\varepsilon.
\]
令 \(\varepsilon\downarrow0\)。若右侧有 \(+\infty\)，凸性不等式自动成立；端点情形也显然。因此 \(\operatorname{epi}g_F\) 凸。

对 \(F\subset K\)，有纤维分解
\[
\{x:q_Fx=y\}
=\bigcup_{r_{KF}z=y}\{x:q_Kx=z\}.
\]
对这个并集取下确界，得到
\[
\boxed{\quad g_F(y)=\inf_{r_{KF}z=y}g_K(z).\quad}
\]
这也涵盖空纤维及成本全为 \(+\infty\) 的情形。以上论证均不需要纤维下确界取到。

**S2.**

记 \(C_c=\{x:f(x)\le c\}\)。由下半连续性，\(C_c\) 闭；本阶段还假设其在有限 \(c\) 时紧。

先证明取到性。若 \(a=g_F(y)<\infty\)，则
\[
D_n=C_{a+1/n}\cap q_F^{-1}(\{y\})
\]
非空。这些集合是紧集 \(C_{a+1}\) 中递减的非空闭子集，故由紧性
\[
\bigcap_{n\ge1}D_n\ne\varnothing.
\]
取其中的 \(x\)，便有 \(q_Fx=y\) 且 \(f(x)\le a\)。结合下确界定义，得到 \(f(x)=a\)。

因此，对每个有限实数 \(c\)，
\[
\{y:g_F(y)\le c\}=q_F(C_c).
\]
右侧是紧集的连续像，在 Hausdorff 空间 \(F^*\) 中闭。故 \(g_F\) 的所有实次水平集均闭，等价地，其实高度上图闭，即 \(g_F\) 下半连续。

**S3.**

在紧集 \(C_c\) 中定义
\[
A_F=C_c\cap q_F^{-1}(\{y_F\}).
\]
由 \(g_F(y_F)\le c\) 及 S2 的取到性，每个 \(A_F\) 非空；由 \(q_F\) 连续，每个 \(A_F\) 在 \(C_c\) 中闭。

给定有限多个 \(F_1,\dots,F_m\)，令 \(K=F_1+\cdots+F_m\)。兼容性给出
\[
A_K\subseteq\bigcap_{j=1}^m A_{F_j}.
\]
因此 \((A_F)_F\) 有有限交性质。由 \(C_c\) 紧，
\[
\bigcap_F A_F\ne\varnothing.
\]
取其中的 \(x\)，则 \(f(x)\le c\)，且所有 \(q_Fx=y_F\)。

若 \(x,x'\) 都满足要求，对任意 \(\varphi\in E'\) 取 \(F=\operatorname{span}\{\varphi\}\)，得到
\[
\varphi(x-x')=0.
\]
Hausdorff 局部凸空间的连续对偶分离点：非零向量可被某个连续半范数检测，再用 Hahn–Banach 定理得到检测它的连续线性泛函。因此 \(x=x'\)。

所求构造就是上述交集中的唯一点。

**S4.**

结论成立，只需共同设定。

先说明闭化操作。对非负、凸且至少一点有限的函数 \(u\)，令
\[
C_u=\overline{\operatorname{epi}u},\qquad
\bar u(v)=\inf\{t\in\mathbb R:(v,t)\in C_u\}.
\]
这里空集下确界取 \(+\infty\)。因为 \(C_u\) 闭、凸、向上封闭，且包含于 \(\{t\ge0\}\)，其竖直截面为空或形如 \([a,\infty)\)。故
\[
\operatorname{epi}\bar u=C_u.
\]
于是 \(\bar u\ge0\)，下半连续、凸，且 \(\bar u\le u\)。

若 \(h\) 下半连续、凸且 \(h\le u\)，则
\[
\operatorname{epi}u\subseteq\operatorname{epi}h
\quad\Longrightarrow\quad
\overline{\operatorname{epi}u}\subseteq\operatorname{epi}h,
\]
所以 \(h\le\bar u\)。这直接涵盖 \(h\) 同时取两种无穷值的情形。因此该操作正是 S6 所说的最大下半连续凸下界。

由全部记录定义
\[
\boxed{\qquad G(x)=\sup_{\dim F<\infty}\bar g_F(q_Fx).\qquad}
\]
每个被取上确界的函数均非负、下半连续、凸，且不超过 \(f\)，所以 \(G\) 也有这些性质，并在 \(x_0\) 处有限。

扩大观测空间时，由 S1，
\[
g_F\circ r_{KF}\le g_K.
\]
而 \(\bar g_F\circ r_{KF}\) 下半连续、凸，且不超过 \(g_K\)，故
\[
\boxed{\quad
\bar g_F\circ r_{KF}\le\bar g_K,\qquad
\bar g_F\circ q_F\le\bar g_K\circ q_K.
\quad}
\]
因此恢复公式是随观测空间扩大而递增的上确界。

下面证明其最大性，具体证明
\[
\operatorname{epi}G=\overline{\operatorname{epi}f}. \tag{1}
\]
记 \(A=\operatorname{epi}f\)，\(P_F=q_F\times\mathrm{id}_{\mathbb R}\)。首先，
\[
\overline{P_F(A)}=\overline{\operatorname{epi}g_F}
=\operatorname{epi}\bar g_F. \tag{2}
\]
确实，\(P_F(A)\subseteq\operatorname{epi}g_F\)。反过来，若 \(g_F(y)\le t\)，则对任意 \(\varepsilon>0\)，存在 \(q_Fx=y\) 且 \(f(x)<t+\varepsilon\)，故
\((y,t+\varepsilon)\in P_F(A)\)，证明了另一方向的闭包包含关系。

由 (2)，
\[
\operatorname{epi}G
=\bigcap_F P_F^{-1}\bigl(\overline{P_F(A)}\bigr).
\]
这个交集闭且包含 \(A\)，所以包含 \(\overline A\)。

反过来，若 \((x,t)\notin\overline A\)，则可应用点与非空闭凸集的严格分离定理：\(E\times\mathbb R\) 是 Hausdorff 局部凸空间，而 \(\overline A\) 非空、闭、凸。因此存在 \(\varphi\in E'\)、\(a,\alpha\in\mathbb R\)，使
\[
\varphi(x)+at<\alpha
\le\varphi(v)+as
\qquad((v,s)\in\overline A).
\]
取 \(F=\operatorname{span}\{\varphi\}\)。连续函数
\[
(y,s)\longmapsto y(\varphi)+as
\]
在 \(\overline{P_F(A)}\) 上至少为 \(\alpha\)，但在 \(P_F(x,t)\) 处小于 \(\alpha\)。故 \((x,t)\notin\operatorname{epi}G\)，完成 (1)。

由 (1)，\(G=\bar f\)。特别地，任何题设允许的下半连续凸函数 \(h\le f\) 都满足
\[
\operatorname{epi}G=\overline{\operatorname{epi}f}
\subseteq\operatorname{epi}h,
\]
即 \(h\le G\)。

**S5.**

结论不成立。

取
\[
C=\{(a,b):a>0,\ b\ge1/a\}
=\{(a,b):a\ge0,\ b\ge0,\ ab\ge1\},
\qquad
f=\delta_C,
\]
其中 \(\delta_C\) 在 \(C\) 上为 \(0\)，其余处为 \(+\infty\)。

第二个表示说明 \(C\) 闭；由于 \(a\mapsto1/a\) 在 \((0,\infty)\) 上凸，第一个表示说明 \(C\) 凸。此外 \((1,1)\in C\)。因而
\[
\operatorname{epi}f=C\times[0,\infty)
\]
非空、闭、凸，满足本阶段所有条件。

令 \(F=\operatorname{span}\{\pi_1\}\)，将 \(F^*\) 识别为第一坐标空间。则
\[
g_F(a)=
\begin{cases}
0,&a>0,\\
+\infty,&a\le0.
\end{cases}
\]
于是 \((1/n,0)\in\operatorname{epi}g_F\)，而其极限 \((0,0)\) 不在该上图中。因此 \(g_F\) 不下半连续。

**S6.**

首先，由 S4，\(G=\bar f\) 且 \(G\) 下半连续。因此
\[
\boxed{\quad G=f\iff f\text{ 下半连续}.\quad}
\]
其中反向是因为：若 \(f\) 下半连续，则 \(\operatorname{epi}f\) 已闭，S4 的公式直接给出 \(G=f\)。

固定 \(F\subset K\)，记
\[
p(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
函数 \(\bar g_K\) 非负、凸，并在 \(q_Kx_0\) 处有限，故 S1 的纤维下确界论证同样说明：\(p\) 非负、凸且至少一点有限，可以对它作闭化。

由 S4 的单调关系，
\[
\bar g_F(y)\le p(y).
\]
另一方面，由 \(\bar g_K\le g_K\) 及 S1，
\[
p(y)\le\inf_{r_{KF}z=y}g_K(z)=g_F(y).
\]
所以
\[
\bar g_F\le p\le g_F.
\]
闭化操作保持次序，且对已经下半连续、凸的函数不作改变，因此
\[
\bar g_F=\overline{\bar g_F}
\le\bar p\le\bar g_F.
\]
这就证明
\[
\boxed{\quad
\bar g_F
=\overline{\left(y\longmapsto
\inf_{r_{KF}z=y}\bar g_K(z)\right)}.
\quad}
\]

最外层的闭化**不能总省去**。沿用 S5 的例子，取 \(K=E'\)。通过自然识别 \(K^*\cong\mathbb R^2\)，有
\[
g_K=f,\qquad \bar g_K=f.
\]
所以这里的 \(p=g_F\)，而
\[
\bar g_F(a)=
\begin{cases}
0,&a\ge0,\\
+\infty,&a<0.
\end{cases}
\]
特别地，
\[
\bar g_F(0)=0,\qquad
\inf_{r_{KF}z=0}\bar g_K(z)=+\infty.
\]
两者不同，证明最外层闭化确有必要。