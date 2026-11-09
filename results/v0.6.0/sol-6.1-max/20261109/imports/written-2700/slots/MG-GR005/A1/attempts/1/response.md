**S1　原始记录**

选定 \(x_0\in E\) 使 \(f(x_0)<\infty\)。显然
\[
g_F\ge0,\qquad g_F(q_Fx_0)\le f(x_0)<\infty.
\]

证明凸性。设 \(g_F(y_i)<\infty\)，\(0<\lambda<1\)。对任意 \(\varepsilon>0\)，可选 \(x_i\) 满足
\[
q_Fx_i=y_i,\qquad f(x_i)<g_F(y_i)+\varepsilon.
\]
由 \(q_F\) 的线性及 \(f\) 的凸性，
\[
g_F(\lambda y_1+(1-\lambda)y_2)
\le \lambda g_F(y_1)+(1-\lambda)g_F(y_2)+\varepsilon.
\]
令 \(\varepsilon\downarrow0\)。若某个端点成本为 \(+\infty\)，相应凸性不等式自动成立；端点权重情形也显然。因此 \(g_F\) 的实高度上图凸。

当 \(F\subset K\) 时，\(q_F=r_{KF}q_K\)，所以
\[
\{x:q_Fx=y\}
=\bigcup_{r_{KF}z=y}\{x:q_Kx=z\}.
\]
对这个并集取下确界，得到
\[
\boxed{\quad g_F(y)=\inf_{r_{KF}z=y}g_K(z).\quad}
\]
这也涵盖空纤维的情形。以上证明均不需要下确界取到，只使用了下确界的逼近性质。

以下会用到：选取 \(F\) 的一组基后，\(q_F\) 就是有限个连续线性泛函组成的映射，故连续；\(r_{KF}\) 也连续，因为它是有限维空间之间的线性映射。

**S2　紧次水平集**

先证明取到。固定 \(y\)，设 \(a=g_F(y)<\infty\)。令
\[
B_n=\{x:q_Fx=y,\ f(x)\le a+1/n\},\qquad n\ge1.
\]
下确界的逼近性质保证每个 \(B_n\) 非空。由于纤维闭、\(f\) 下半连续，且相应次水平集紧，\(B_n\) 是紧集，也是 \(B_1\) 中的闭集。这些集合递减，故由紧集的有限交性质，
\[
\bigcap_{n\ge1}B_n\ne\varnothing.
\]
其中任意 \(x\) 都满足 \(q_Fx=y\) 及 \(f(x)\le a\)，从而
\[
f(x)=a=g_F(y).
\]

因此对每个有限实数 \(c\)，
\[
\{y:g_F(y)\le c\}=q_F(\{x:f(x)\le c\}).
\]
当 \(c<0\) 时两边均为空；其他情形使用刚证明的取到性质。右边是紧集的连续像，因 \(F^*\) 为 Hausdorff 空间而闭。因此 \(g_F\) 的每个有限实数次水平集均闭，故其实高度上图闭，即 \(g_F\) 下半连续。

这里使用有限交性质，并未假定 \(E\) 中的紧性等同于序列紧性。

**S3　兼容成本记录的实现**

令
\[
C=\{x:f(x)\le c\},\qquad
C_F=C\cap q_F^{-1}(\{y_F\}).
\]
由 S2 及 \(g_F(y_F)\le c<\infty\)，每个 \(C_F\) 非空；它也是紧集 \(C\) 中的闭集。

给定有限多个观测空间 \(F_1,\dots,F_n\)，令
\[
K=F_1+\cdots+F_n.
\]
兼容性及 \(q_{F_i}=r_{KF_i}q_K\) 给出
\[
C_K\subseteq\bigcap_{i=1}^n C_{F_i}.
\]
故这些闭集具有有限交性质。由 \(C\) 紧，
\[
\bigcap_F C_F\ne\varnothing.
\]
取其中的 \(x\)，便有
\[
f(x)\le c,\qquad q_Fx=y_F\quad\text{对所有 }F.
\]

若 \(x,x'\) 都实现这些记录，则对任意 \(\varphi\in E'\)，取 \(F=\operatorname{span}\{\varphi\}\)，得到
\[
\varphi(x)=\varphi(x').
\]
实 Hausdorff 局部凸空间的连续对偶由 Hahn–Banach 定理分离点，故 \(x=x'\)。这证明了存在性与唯一性。

**S4　一般成本的恢复**

结论成立。

先给出闭化的具体含义。对非负、凸且至少一点有限的函数 \(u\)，令
\[
C_u=\overline{\operatorname{epi}_{\mathbb R}(u)}.
\]
此集合非空、闭、凸、向上封闭，并包含于 \(X\times[0,\infty)\)。因此它在每一点上方的竖直截面，或者为空，或者是某个 \([a,\infty)\)，其中 \(a\ge0\)。于是它唯一确定一个非负函数 \(\bar u\)，满足
\[
\operatorname{epi}_{\mathbb R}(\bar u)=C_u.
\]
这个函数下半连续、凸，且 \(\bar u\le u\)。

若 \(h\le u\) 且 \(h\) 下半连续、凸，则
\[
\operatorname{epi}_{\mathbb R}(u)
\subseteq\operatorname{epi}_{\mathbb R}(h),
\]
故
\[
C_u\subseteq\operatorname{epi}_{\mathbb R}(h),
\qquad h\le\bar u.
\]
这一论证允许 \(h\) 同时取 \(-\infty\) 和 \(+\infty\)。因此 \(\bar u\) 正是题目要求的最大下半连续凸下界。

由全部记录构造
\[
\boxed{\qquad
G(x)=\sup_{\substack{F\subset E'\\ \dim F<\infty}}
       \bar g_F(q_Fx).
\qquad} \tag{1}
\]
下面证明它等于 \(\bar f\)。

记
\[
A=\operatorname{epi}_{\mathbb R}(f),\qquad
p_F(x,t)=(q_Fx,t),\qquad B_F=p_F(A).
\]
有
\[
B_F\subseteq\operatorname{epi}_{\mathbb R}(g_F)
\subseteq\overline{B_F}.
\]
第二个包含关系是因为：若 \(g_F(y)\le t\)，则对每个 \(\varepsilon>0\)，存在 \(x\) 满足
\[
q_Fx=y,\qquad f(x)<t+\varepsilon,
\]
所以 \((y,t+\varepsilon)\in B_F\)。因此
\[
\overline{B_F}=\operatorname{epi}_{\mathbb R}(\bar g_F). \tag{2}
\]

我们断言
\[
\overline A=\bigcap_F p_F^{-1}(\overline{B_F}). \tag{3}
\]
“\(\subseteq\)”由 \(p_F\) 连续立即得到。

反之，设 \(w=(x,t)\notin\overline A\)。空间 \(E\times\mathbb R\) 仍为实 Hausdorff 局部凸空间，而 \(\overline A\) 非空、闭、凸，故点与闭凸集的严格分离定理适用：存在 \(\varphi\in E'\)、\(b,a\in\mathbb R\)，使
\[
\varphi(x)+bt<a\le\varphi(v)+bs
\quad\text{对所有 }(v,s)\in\overline A.
\]
取 \(F=\operatorname{span}\{\varphi\}\)，允许 \(F=\{0\}\)。连续线性函数
\[
(y,s)\longmapsto y(\varphi)+bs
\]
在 \(B_F\) 及其闭包上均至少为 \(a\)，但在 \(p_F(w)\) 处小于 \(a\)。故 \(p_F(w)\notin\overline{B_F}\)，证明了 (3)。这里无需假定 \(b\ne0\)。

结合 (1)–(3)，
\[
\operatorname{epi}_{\mathbb R}(G)
=\bigcap_Fp_F^{-1}\!\left(\operatorname{epi}_{\mathbb R}(\bar g_F)\right)
=\overline{\operatorname{epi}_{\mathbb R}(f)}.
\]
所以 \(G=\bar f\)，具有所要求的全部性质。

扩大观测空间时，S1 给出
\[
\bar g_F(r_{KF}z)\le g_F(r_{KF}z)\le g_K(z).
\]
左端作为 \(z\) 的函数下半连续、凸，故由 \(\bar g_K\) 的最大性，
\[
\boxed{\quad \bar g_F\circ r_{KF}\le\bar g_K.\quad} \tag{4}
\]
特别地，
\[
0\le\bar g_F(q_Fx)\le\bar g_K(q_Kx)\le f(x).
\]
因此 (1) 是随观测空间扩大而单调增加的上确界。

**S5　闭成本的有限投影**

结论：**不一定下半连续。**

取
\[
C=\{(a,b)\in\mathbb R^2:a\ge0,\ b\ge0,\ ab\ge1\},
\]
并定义
\[
f(a,b)=
\begin{cases}
0,&(a,b)\in C,\\
+\infty,&(a,b)\notin C.
\end{cases}
\]
连续不等式表明 \(C\) 闭。又
\[
C=\{(a,b):a>0,\ b\ge1/a\},
\]
而 \(a\mapsto1/a\) 在 \((0,\infty)\) 上凸，所以 \(C\) 凸。于是
\[
\operatorname{epi}_{\mathbb R}(f)=C\times[0,\infty)
\]
闭且凸；此外 \(f\ge0\)，且 \(f(1,1)=0\)。

令 \(F\) 由第一坐标泛函生成，并将 \(F^*\) 识别为 \(\mathbb R\)。则
\[
g_F(a)=
\begin{cases}
0,&a>0,\\
+\infty,&a\le0.
\end{cases}
\]
因为 \(a>0\) 时可取 \(b=1/a\)，而 \(a\le0\) 时纤维不与 \(C\) 相交。

现在 \((1/n,0)\in\operatorname{epi}_{\mathbb R}(g_F)\)，但其极限 \((0,0)\) 不在上图中。因此 \(g_F\) 不下半连续。

**S6　恢复与投影的精确关系**

由 S4，\(G=\bar f\)，故
\[
\boxed{\quad G=f\quad\Longleftrightarrow\quad f\text{ 下半连续}.\quad}
\]
确实，若 \(G=f\)，则 \(f\) 继承 \(G\) 的下半连续性；若 \(f\) 下半连续，则它已经是自身的下半连续凸下界，所以最大性及 \(G\le f\) 给出 \(G=f\)。

固定有限维 \(F\subset K\)，令
\[
m(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
由 S1 同样的纤维逼近论证，\(m\) 非负、凸；选取 \(f(x_0)<\infty\)，还有
\[
m(q_Fx_0)\le\bar g_K(q_Kx_0)\le f(x_0)<\infty.
\]
所以其闭化 \(\bar m\) 适用上述构造。

一方面，由 \(\bar g_K\le g_K\) 及 S1，
\[
m\le g_F.
\]
因此 \(\bar m\) 是 \(g_F\) 的下半连续凸下界，从而
\[
\bar m\le\bar g_F.
\]
另一方面，由 (4)，对每个满足 \(r_{KF}z=y\) 的 \(z\)，
\[
\bar g_F(y)\le\bar g_K(z).
\]
取下确界得到 \(\bar g_F\le m\)。再由 \(\bar m\) 的最大性，
\[
\bar g_F\le\bar m.
\]
两式合并即得
\[
\boxed{\quad
\bar g_F
=\overline{\left(y\longmapsto
       \inf_{r_{KF}z=y}\bar g_K(z)\right)}.
\quad}
\]

右式最外层的闭化**不能总省去**。沿用 S5，取 \(K=E'=(\mathbb R^2)'\)。在自然识别下，
\[
g_K=f=\bar g_K,
\]
因而
\[
m(a)=g_F(a)=
\begin{cases}
0,&a>0,\\
+\infty,&a\le0.
\end{cases}
\]
但由其上图的闭包，
\[
\bar g_F(a)=
\begin{cases}
0,&a\ge0,\\
+\infty,&a<0.
\end{cases}
\]
特别地，\(\bar g_F(0)=0\)，而 \(m(0)=+\infty\)。所以即使 \(f\) 本身下半连续，最外层闭化仍不可普遍省去。