令 \(\mathcal N_{F^*}(y)\) 表示 \(F^*\) 中 \(y\) 的邻域族，定义每条记录的下半连续包

\[
\bar g_F(y)
=\sup_{U\in\mathcal N_{F^*}(y)}\inf_{v\in U}g_F(v).
\]

所求函数是

\[
\boxed{\displaystyle
G(x)=\sup_{\substack{F\subset E'\\ \dim F<\infty}}
\bar g_F\bigl(q_F(x)\bigr).}
\]

它满足 \(0\le G\le f\)，是下半连续凸函数，并且

\[
\boxed{\displaystyle
\operatorname{epi}_{\mathbb R}(G)
=\overline{\operatorname{epi}_{\mathbb R}(f)}^{\,E\times\mathbb R}.}
\]

因此，对题目中允许取 \(-\infty\) 的任意下半连续凸函数 \(h\le f\)，都有 \(h\le G\)。事实上，这里的比较甚至不需要 \(h\) 凸。

记录之间的精确关系是：当 \(F\subset K\) 时，

\[
\boxed{\displaystyle
g_F(y)=\inf_{\substack{z\in K^*\\r_{KF}(z)=y}}g_K(z).}
\]

取下半连续包后，通常必须再次取包，才能维持这一关系：

\[
\boxed{\displaystyle
\bar g_F
=\operatorname{lsc}\!\left(
y\longmapsto\inf_{\substack{z\in K^*\\r_{KF}(z)=y}}\bar g_K(z)
\right),}
\]

其中 \(\operatorname{lsc}\) 表示由上面的邻域公式定义的下半连续包。

更进一步，一维观测已经足够：

\[
\boxed{\displaystyle
G(x)=
\sup_{\varphi\in E'}\ \sup_{\varepsilon>0}
\inf\{f(z):|\varphi(z)-\varphi(x)|<\varepsilon\}.}
\]

下面证明这些结论。

首先，\(q_F\) 连续且满射。连续性由 \(F\) 的有限维基给出。若 \(q_F(E)\) 是 \(F^*\) 的真子空间，则存在非零 \(\varphi\in F=(F^*)^*\)，使得
\(q_F(x)(\varphi)=\varphi(x)=0\) 对所有 \(x\in E\) 成立，这与 \(\varphi\ne0\) 矛盾。同样，限制映射 \(r_{KF}\) 满射，且

\[
q_F=r_{KF}\circ q_K.
\]

于是按纤维分组取下确界，便得到上面的 \(g_F\) 与 \(g_K\) 的精确关系。每个 \(g_F\) 非负，并至少在 \(q_F(x_0)\) 处有限，其中 \(f(x_0)<\infty\)。通过在两个纤维中分别取近似极小点，再使用 \(f\) 的凸性，可知 \(g_F\) 凸。

对任意这样的非负函数，邻域公式给出的下半连续包满足

\[
\operatorname{epi}_{\mathbb R}(\bar g_F)
=\overline{\operatorname{epi}_{\mathbb R}(g_F)}
\quad\text{于 }F^*\times\mathbb R.
\]

所以 \(\bar g_F\) 非负、下半连续、凸，并至少在一点有限。它还是 \(g_F\) 的最大下半连续次函数：若 \(v\le g_F\) 且 \(v\) 下半连续，则
\(\operatorname{epi}_{\mathbb R}(g_F)\subset\operatorname{epi}_{\mathbb R}(v)\)，取闭包即得 \(v\le\bar g_F\)。

当 \(F\subset K\) 时，由原始记录的关系，

\[
\bar g_F(r_{KF}z)\le g_F(r_{KF}z)\le g_K(z).
\]

左边是 \(K^*\) 上的下半连续函数，故由 \(\bar g_K\) 的最大性，

\[
\bar g_F(r_{KF}z)\le\bar g_K(z).
\]

因此，若写

\[
p(y)=\inf_{r_{KF}z=y}\bar g_K(z),
\]

则 \(\bar g_F\le p\le g_F\)，取下半连续包就得到 \(\operatorname{lsc}p=\bar g_F\)。特别地，对每个 \(x\)，
\(\bar g_F(q_F(x))\) 随有限维空间 \(F\) 扩大而递增；有限维子空间按包含关系构成有向集。

由 \(\bar g_F\le g_F\) 和 \(g_F(q_F(x))\le f(x)\)，上述构造满足 \(G\le f\)。每个 \(\bar g_F\circ q_F\) 都下半连续且凸，故其上确界 \(G\) 也下半连续且凸。并且 \(G(x_0)\le f(x_0)<\infty\)。

为证明其最大性，记

\[
P_F:E\times\mathbb R\to F^*\times\mathbb R,\qquad
P_F(x,t)=(q_F(x),t).
\]

投影可能丢失下确界处的端点，但不会影响闭包：

\[
\overline{P_F(\operatorname{epi}_{\mathbb R}(f))}
=\overline{\operatorname{epi}_{\mathbb R}(g_F)}
=\operatorname{epi}_{\mathbb R}(\bar g_F).
\]

确实，左侧投影包含于 \(\operatorname{epi}_{\mathbb R}(g_F)\)；反过来，若 \(g_F(y)\le t\)，则对每个 \(\delta>0\)，可选 \(x\) 使 \(q_F(x)=y\) 且 \(f(x)<t+\delta\)，故 \((y,t+\delta)\) 属于该投影。

因此

\[
\operatorname{epi}_{\mathbb R}(G)
=\bigcap_F P_F^{-1}
\left(\overline{P_F(\operatorname{epi}_{\mathbb R}(f))}\right).
\]

令 \(C=\overline{\operatorname{epi}_{\mathbb R}(f)}\)。它是 \(E\times\mathbb R\) 中非空的闭凸集，显然包含于上式右边。反过来，若 \((x,t)\notin C\)，局部凸空间中的严格分离定理给出 \(\varphi\in E'\)、\(a,c\in\mathbb R\)，使得

\[
\varphi(x)+at<c\le \varphi(z)+as
\qquad ((z,s)\in C).
\]

取 \(F=\operatorname{span}\{\varphi\}\)。连续线性函数
\((y,s)\mapsto y(\varphi)+as\) 在
\(P_F(\operatorname{epi}_{\mathbb R}(f))\) 上至少为 \(c\)，因而在其闭包上也至少为 \(c\)；但它在 \(P_F(x,t)\) 处小于 \(c\)。因此 \((x,t)\) 不属于上述交集，证明了

\[
\operatorname{epi}_{\mathbb R}(G)=C.
\]

这个论证每次只用了至多一维的 \(F\)，故上确界可以只取这些 \(F\)。将 \(\bar g_F\) 的邻域公式代入，便得到前述单个 \(\varphi\) 与 \(\varepsilon\) 的公式。这里所用的单个函数约束一般不构成 \(E\) 原拓扑的邻域基；能用它们恢复闭包，依靠的是上图的凸性和分离定理。

现在若 \(h\le f\) 且 \(h\) 下半连续，即使 \(h\) 取 \(-\infty\)，仍有

\[
\operatorname{epi}_{\mathbb R}(f)
\subset\operatorname{epi}_{\mathbb R}(h).
\]

右侧闭，故 \(\operatorname{epi}_{\mathbb R}(G)\subset
\operatorname{epi}_{\mathbb R}(h)\)，也就是 \(h\le G\)。

恢复出的 \(G\) 与各条记录还满足

\[
\bar g_F(y)\le
\inf_{q_F(x)=y}G(x)\le g_F(y).
\]

因此，\(G\) 在每个观测空间上的纤维成本，其下半连续包恰好是 \(\bar g_F\)。

最后，记录投影后确实可能失去下半连续性。例如在 \(E=\mathbb R^2\) 上，令 \(f\) 在闭凸集
\(\{(u,v):u\ge e^v\}\) 上为 \(0\)，在其余处为 \(+\infty\)，并只观测 \(u\)。这时

\[
g_F(u)=
\begin{cases}0,&u>0,\\+\infty,&u\le0,\end{cases}
\qquad
\bar g_F(u)=
\begin{cases}0,&u\ge0,\\+\infty,&u<0.\end{cases}
\]

所以即使原函数已经下半连续，投影后的记录仍可能需要取闭包；这也说明闭包后的记录之间一般不能省去上述的 \(\operatorname{lsc}\) 操作。