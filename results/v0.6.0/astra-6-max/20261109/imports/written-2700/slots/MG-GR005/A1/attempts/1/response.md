**S1.** 取 \(x_0\in E\) 使 \(f(x_0)<\infty\)。由定义，
\[
g_F\ge0,\qquad g_F(q_Fx_0)\le f(x_0)<\infty.
\]
若 \(g_F(y_1),g_F(y_2)<\infty\)，则对任意 \(\varepsilon>0\)，可选取 \(x_i\) 满足
\[
q_Fx_i=y_i,\qquad f(x_i)\le g_F(y_i)+\varepsilon.
\]
对 \(0<\lambda<1\)，由 \(f\) 的凸性，
\[
\begin{aligned}
g_F(\lambda y_1+(1-\lambda)y_2)
&\le f(\lambda x_1+(1-\lambda)x_2)\\
&\le\lambda g_F(y_1)+(1-\lambda)g_F(y_2)+\varepsilon.
\end{aligned}
\]
令 \(\varepsilon\downarrow0\)。若右侧有 \(+\infty\)，凸性不等式自动成立；端点情形也成立。因此 \(g_F\) 凸。

因为 \(q_F=r_{KF}q_K\)，对应纤维满足
\[
\{x:q_Fx=y\}
=\bigcup_{r_{KF}z=y}\{x:q_Kx=z\}.
\]
于是，包括空集情形，
\[
\boxed{\quad g_F(y)=\inf_{r_{KF}z=y}g_K(z).\quad}
\]
上述证明均不需要纤维下确界取到。

**S2.** 记 \(C_c=\{x:f(x)\le c\}\)。取 \(F\) 的一组基后，\(q_F\) 的坐标就是有限个连续线性泛函，因此 \(q_F\) 连续。

设 \(a=g_F(y)<\infty\)。对每个 \(n\ge1\)，集合
\[
A_n=C_{a+1/n}\cap q_F^{-1}(\{y\})
\]
由下确界定义非空，并且是一列递减闭集，均包含在紧集 \(C_{a+1}\) 中。这里闭性来自 \(f\) 下半连续和 \(q_F\) 连续。由紧空间中闭集的有限交性质，存在
\[
x\in\bigcap_{n\ge1}A_n.
\]
于是 \(q_Fx=y\)、\(f(x)\le a\)，而下确界定义又给出 \(f(x)\ge a\)。故
\[
f(x)=g_F(y),
\]
即有限的纤维下确界取到。

因此，对每个有限实数 \(c\)，
\[
\{y:g_F(y)\le c\}=q_F(C_c).
\]
右侧是紧集，因 \(F^*\) 为 Hausdorff 空间而闭。因此 \(g_F\) 下半连续。具体地，若 \(t<g_F(y)\)，选取实数 \(a\) 满足 \(t<a<g_F(y)\)，则
\[
\{v:g_F(v)>a\}\times(-\infty,a)
\]
是包含 \((y,t)\) 且与上图不交的开集，故实高度上图闭。

**S3.** 在紧集 \(C_c\) 中定义
\[
A_F=C_c\cap q_F^{-1}(\{y_F\}).
\]
由 S2 的取到性及 \(g_F(y_F)\le c\)，每个 \(A_F\) 都非空且闭；特别地，\(C_c\) 非空。

对任意有限多个 \(F_1,\ldots,F_m\)，令
\[
K=F_1+\cdots+F_m.
\]
兼容性给出
\[
A_K\subseteq\bigcap_{i=1}^m A_{F_i}.
\]
所以这族闭集具有有限交性质。由 \(C_c\) 紧，
\[
\bigcap_F A_F\ne\varnothing.
\]
取交集中的 \(x\)，即有 \(f(x)\le c\) 且 \(q_Fx=y_F\) 对所有 \(F\) 成立。

若 \(x'\) 也满足全部观测条件，则取 \(F=\operatorname{span}\{\varphi\}\)，可得
\[
\varphi(x-x')=0\qquad(\varphi\in E').
\]
Hausdorff 局部凸空间的连续对偶由 Hahn–Banach 定理分离点，故 \(x=x'\)。因此构造可写为
\[
\boxed{\quad \{x\}=\bigcap_F
\bigl(C_c\cap q_F^{-1}(\{y_F\})\bigr).\quad}
\]

**S4.** 结论成立。先说明闭上图包络的构造。

对非负凸函数 \(u:V\to[0,\infty]\)，令
\[
C_u=\overline{\operatorname{epi}_{\mathbb R}(u)}
\]
（取所在空间 \(V\times\mathbb R\) 的闭包）。该集合闭、凸、沿高度方向向上封闭，并包含于 \(V\times[0,\infty)\)。故每个竖直截面或者为空，或者为某个 \([a,\infty)\)，其中 \(a\ge0\)。于是唯一确定函数 \(\bar u\)，使
\[
\operatorname{epi}_{\mathbb R}(\bar u)=C_u.
\]
它非负、下半连续、凸，且 \(\bar u\le u\)。

若 \(v\le u\) 且 \(v\) 的上图闭，则
\[
\operatorname{epi}_{\mathbb R}(u)
\subseteq\operatorname{epi}_{\mathbb R}(v)
\quad\Longrightarrow\quad
C_u\subseteq\operatorname{epi}_{\mathbb R}(v),
\]
故 \(v\le\bar u\)。这个论证允许 \(v\) 同时取 \(-\infty\) 和 \(+\infty\)。

现在仅用全部记录定义
\[
\boxed{\qquad
G(x)=\sup_{\dim F<\infty}\bar g_F(q_Fx).
\qquad}
\]
每一项下半连续、凸且非负，其上确界也有这些性质，并且
\[
0\le G(x)\le f(x).
\]
特别地，\(G(x_0)<\infty\)。

扩大观测空间时，有
\[
\boxed{\quad
\bar g_F(r_{KF}z)\le\bar g_K(z),\qquad F\subseteq K.
\quad}
\]
事实上，\(r_{KF}\) 连续线性，故 \(\bar g_F\circ r_{KF}\) 下半连续且凸；S1 给出
\[
\bar g_F(r_{KF}z)\le g_F(r_{KF}z)\le g_K(z),
\]
再用 \(\bar g_K\) 的最大性即可。特别地，
\[
\bar g_F(q_Fx)\le\bar g_K(q_Kx),
\]
所以恢复公式中的函数随观测空间扩大而单调增加。

下面证明最大性，核心是
\[
\boxed{\quad
\operatorname{epi}_{\mathbb R}(G)
=\overline{\operatorname{epi}_{\mathbb R}(f)}.
\quad} \tag{1}
\]
令 \(P_F=q_F\times\mathrm{id}_{\mathbb R}\)。首先，
\[
\overline{P_F(\operatorname{epi}_{\mathbb R}(f))}
=\operatorname{epi}_{\mathbb R}(\bar g_F). \tag{2}
\]
确实，投影上图包含于 \(g_F\) 的上图；反过来，若 \(g_F(y)\le t\)，则对每个 \(\varepsilon>0\) 可选 \(x\) 使
\[
q_Fx=y,\qquad f(x)<t+\varepsilon.
\]
因此 \((y,t+\varepsilon)\) 属于投影上图，得到其闭包包含 \(g_F\) 的上图，从而证明 (2)。

记 \(C=\overline{\operatorname{epi}_{\mathbb R}(f)}\)。由 (2) 和 \(P_F\) 连续，
\[
C\subseteq\bigcap_F P_F^{-1}
\bigl(\operatorname{epi}_{\mathbb R}(\bar g_F)\bigr)
=\operatorname{epi}_{\mathbb R}(G).
\]
反之，若 \((x,t)\notin C\)，由于 \(C\) 是 Hausdorff 局部凸空间 \(E\times\mathbb R\) 中的非空闭凸集，几何 Hahn–Banach 分离定理给出
\(\varphi\in E'\)、\(b,a\in\mathbb R\)，使
\[
\varphi(x)+bt<a\le\varphi(z)+bs
\qquad((z,s)\in C).
\]
取 \(F=\operatorname{span}\{\varphi\}\)。投影上图及其闭包均包含于闭半空间
\[
\{(y,s):y(\varphi)+bs\ge a\},
\]
而 \((q_Fx,t)\) 不在其中。由 (2)，
\[
(q_Fx,t)\notin\operatorname{epi}_{\mathbb R}(\bar g_F),
\]
故 \((x,t)\notin\operatorname{epi}_{\mathbb R}(G)\)。这证明 (1)。

于是 \(G=\bar f\)。对题设任何竞争函数 \(h\)，由 \(h\le f\) 及其上图闭，
\[
\operatorname{epi}_{\mathbb R}(G)
=\overline{\operatorname{epi}_{\mathbb R}(f)}
\subseteq\operatorname{epi}_{\mathbb R}(h),
\]
即 \(h\le G\)，包括允许同时取两种无穷值的情形。

**S5.** 不一定。令
\[
C=\{(s,t)\in\mathbb R^2:s\ge0,\ t\ge0,\ st\ge1\}
=\{(s,t):s>0,\ t\ge1/s\},
\]
并定义
\[
f(s,t)=
\begin{cases}
0,&(s,t)\in C,\\
+\infty,&(s,t)\notin C.
\end{cases}
\]
集合 \(C\) 由连续不等式定义，因而闭；由于 \(s\mapsto1/s\) 在 \((0,\infty)\) 上凸，\(C\) 也凸。又 \((1,1)\in C\)，而
\[
\operatorname{epi}_{\mathbb R}(f)=C\times[0,\infty),
\]
所以 \(f\) 满足本阶段全部条件。

取 \(F\) 为第一坐标泛函张成的空间，将 \(F^*\) 识别为 \(\mathbb R\)，则
\[
g_F(s)=
\begin{cases}
0,&s>0,\\
+\infty,&s\le0.
\end{cases}
\]
其上图包含 \((1/n,0)\)，却不包含极限点 \((0,0)\)，故 \(g_F\) 不下半连续。

**S6.** 由 S4 的公式 (1)，
\[
G=f
\iff \operatorname{epi}_{\mathbb R}(f)
=\overline{\operatorname{epi}_{\mathbb R}(f)}
\iff f\text{ 下半连续}.
\]

对 \(F\subseteq K\)，记
\[
p(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
S1 的同一近似取值论证适用于凸函数 \(\bar g_K\) 和线性映射 \(r_{KF}\)，故 \(p\) 非负且凸。它也至少一点有限：取此前的 \(x_0\)，则
\[
p(q_Fx_0)\le\bar g_K(q_Kx_0)\le f(x_0)<\infty.
\]
由 S4 的扩大观测关系、\(\bar g_K\le g_K\) 及 S1，
\[
\bar g_F(y)\le p(y)\le g_F(y).
\]
因此，\(\bar g_F\) 是 \(p\) 的下半连续凸下界，给出
\(\bar g_F\le\bar p\)；而 \(\bar p\le p\le g_F\)，又给出
\(\bar p\le\bar g_F\)。所以
\[
\boxed{\quad
\bar g_F
=\overline{\left(y\longmapsto
\inf_{r_{KF}z=y}\bar g_K(z)\right)}.
\quad}
\]

最外层包络不能总省去。沿用 S5 的例子，取 \(K=E'\)，通过自然坐标识别 \(K^*=\mathbb R^2\)。此时
\[
g_K=f,\qquad \bar g_K=f,
\]
所以
\[
p(s)=g_F(s)=
\begin{cases}
0,&s>0,\\
+\infty,&s\le0,
\end{cases}
\qquad
\bar g_F(s)=
\begin{cases}
0,&s\ge0,\\
+\infty,&s<0.
\end{cases}
\]
特别地，\(p(0)=+\infty\)，而 \(\bar g_F(0)=0\)，两者确实不同。