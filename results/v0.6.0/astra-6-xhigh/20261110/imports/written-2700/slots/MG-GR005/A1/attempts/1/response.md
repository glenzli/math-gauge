**S1．结论成立，且不需要纤维下确界取到。**

显然 \(g_F\ge0\)。取 \(x_0\in E\) 使 \(f(x_0)<\infty\)，则
\[
g_F(q_Fx_0)\le f(x_0)<\infty.
\]

为证明凸性，取 \((y_i,t_i)\in\operatorname{epi}_{\mathbb R}(g_F)\)，\(i=1,2\)。对任意 \(\varepsilon>0\)，可取 \(x_i\) 满足
\[
q_Fx_i=y_i,\qquad f(x_i)<t_i+\varepsilon.
\]
由 \(f\) 的凸性，对 \(0<\lambda<1\)，
\[
g_F(\lambda y_1+(1-\lambda)y_2)
\le f(\lambda x_1+(1-\lambda)x_2)
\le\lambda t_1+(1-\lambda)t_2+\varepsilon.
\]
令 \(\varepsilon\downarrow0\)，即得实高度上图的凸性。

若 \(F\subset K\)，则 \(q_F=r_{KF}q_K\)，从而有纤维分解
\[
\{x:q_Fx=y\}
=\bigcup_{\substack{z\in K^*\\r_{KF}z=y}}\{x:q_Kx=z\}.
\]
对集合并逐次取下确界，得到
\[
\boxed{g_F(y)=\inf_{r_{KF}z=y}g_K(z).}
\]
这些论证均只使用下确界的定义，不要求下确界取到。

**S2．各 \(g_F\) 下半连续，有限值处的纤维下确界取到。**

选取 \(F\) 的一组基，\(q_F\) 的坐标就是有限多个连续线性泛函，故 \(q_F:E\to F^*\) 连续。

固定 \(g_F(y)=\alpha<\infty\)。令
\[
B_n=\{x:q_Fx=y,\ f(x)\le\alpha+1/n\},\qquad n\ge1.
\]
由下确界定义，每个 \(B_n\) 非空。由于 \(f\) 下半连续、纤维闭，这些集合是紧集 \(\{f\le\alpha+1\}\) 中的闭集，且递减。因此由紧性，
\[
\bigcap_{n\ge1}B_n\ne\varnothing.
\]
任取其中的 \(x\)，便有 \(q_Fx=y\) 及 \(f(x)\le\alpha\)。结合下确界定义，得到 \(f(x)=\alpha\)。

于是，对每个有限实数 \(c\)，
\[
\{y:g_F(y)\le c\}=q_F(\{x:f(x)\le c\}).
\]
右侧是紧集的连续像；有限维空间 \(F^*\) 为 Hausdorff 空间，故该像闭。因此 \(g_F\) 的所有有限实数次水平集均闭，等价地，其实高度上图闭。

**S3．所求 \(x\) 存在且唯一。**

记紧集 \(C_c=\{x:f(x)\le c\}\)，并令
\[
A_F=C_c\cap q_F^{-1}(\{y_F\}).
\]
由 \(g_F(y_F)\le c<\infty\) 及 S2 的取到结论，每个 \(A_F\) 非空；它也是 \(C_c\) 中的闭集。

对有限多个观测空间 \(F_1,\ldots,F_m\)，取
\[
K=F_1+\cdots+F_m.
\]
兼容性给出
\[
A_K\subseteq\bigcap_{i=1}^m A_{F_i}.
\]
所以 \((A_F)_F\) 具有有限交性质。由 \(C_c\) 的紧性，
\[
\bigcap_F A_F\ne\varnothing.
\]
取交集中的 \(x\)，即有全部所需记录及 \(f(x)\le c\)。

若 \(x,x'\) 都实现这些记录，对任意 \(\varphi\in E'\)，使用 \(F=\operatorname{span}\{\varphi\}\) 即得
\[
\varphi(x)=\varphi(x').
\]
\(E\) 为 Hausdorff 局部凸空间，Hahn–Banach 定理保证 \(E'\) 分离点，故 \(x=x'\)。因此上述交集恰为单点，给出了所求构造。

**S4．成立；无需 S2 的附加条件。**

先说明闭上图恢复的一般事实。对非负凸函数 \(u\)，令
\[
C_u=\overline{\operatorname{epi}_{\mathbb R}(u)}.
\]
它是闭凸集，向上封闭，且包含于“高度非负”的半空间。故每个垂直截面为空集或某个闭射线 \([a,\infty)\)，其中 \(a\ge0\)。因此存在非负下半连续凸函数 \(\bar u\)，使
\[
\operatorname{epi}_{\mathbb R}(\bar u)=C_u.
\]
具体地，
\[
\bar u(v)=\inf\{t\in\mathbb R:(v,t)\in C_u\},
\]
空截面时取 \(+\infty\)。

上图包含关系给出 \(\bar u\le u\)。若 \(h\le u\) 且 \(h\) 下半连续、凸，则
\[
\operatorname{epi}_{\mathbb R}(u)
\subseteq\operatorname{epi}_{\mathbb R}(h),
\]
而后者闭，所以
\[
C_u\subseteq\operatorname{epi}_{\mathbb R}(h),
\qquad h\le\bar u.
\]
这一论证也适用于同时允许取 \(-\infty\)、\(+\infty\) 的 \(h\)。

现在仅用记录 \(g_F\) 构造
\[
\boxed{G(x)=\sup_{\substack{F\subset E'\\ \dim F<\infty}}
                 \bar g_F(q_Fx).}
\]
各项均非负、下半连续、凸，故其上确界也具有这些性质。并且
\[
\bar g_F(q_Fx)\le g_F(q_Fx)\le f(x),
\]
所以 \(G\le f\)，且 \(G(x_0)<\infty\)。

扩大观测空间时，由 S1，
\[
\bar g_F(r_{KF}z)\le g_F(r_{KF}z)\le g_K(z).
\]
函数 \(\bar g_F\circ r_{KF}\) 下半连续且凸，因为 \(r_{KF}\) 连续线性。由 \(\bar g_K\) 的最大性，
\[
\boxed{\bar g_F(r_{KF}z)\le\bar g_K(z).}
\]
特别地，
\[
\bar g_F(q_Fx)\le\bar g_K(q_Kx).
\]
这些拉回到 \(E\) 的函数随观测空间扩大而单调上升，\(G\) 是它们的有向上确界。

下面证明关键等式
\[
\boxed{\operatorname{epi}_{\mathbb R}(G)
       =\overline{\operatorname{epi}_{\mathbb R}(f)}.}
\]
令 \(P_F(x,t)=(q_Fx,t)\)。首先，
\[
\overline{P_F(\operatorname{epi}_{\mathbb R}(f))}
=\overline{\operatorname{epi}_{\mathbb R}(g_F)}
=\operatorname{epi}_{\mathbb R}(\bar g_F). \tag{1}
\]
事实上，投影上图包含于 \(g_F\) 的上图；反过来，若 \(g_F(y)\le t\)，则对每个 \(\varepsilon>0\)，存在 \(x\) 满足
\[
q_Fx=y,\qquad f(x)<t+\varepsilon,
\]
所以 \((y,t+\varepsilon)\) 属于投影上图，令 \(\varepsilon\downarrow0\) 即得另一方向的闭包包含。

记 \(C=\overline{\operatorname{epi}_{\mathbb R}(f)}\)。由于 \(G\le f\) 且 \(G\) 下半连续，已有 \(C\subseteq\operatorname{epi}_{\mathbb R}(G)\)。

若 \((x,t)\notin C\)，则 \(C\) 是 Hausdorff 局部凸空间 \(E\times\mathbb R\) 中的非空闭凸集，可以应用点与闭凸集的严格分离定理。存在 \(\varphi\in E'\)、\(a,\beta\in\mathbb R\)，使
\[
\varphi(x)+at<\beta
\le\varphi(w)+as\qquad((w,s)\in C).
\]
取 \(F=\operatorname{span}\{\varphi\}\)，允许 \(F=\{0\}\)。投影上图包含于闭半空间
\[
\{(y,s):y(\varphi)+as\ge\beta\}.
\]
由 (1)，\(\operatorname{epi}_{\mathbb R}(\bar g_F)\) 也包含于该半空间，而 \((q_Fx,t)\) 不在其中。因此
\[
\bar g_F(q_Fx)>t,\qquad G(x)>t.
\]
这证明了所需上图等式，即 \(G=\bar f\)。

最后，任何题设允许的竞争函数 \(h\) 都满足
\[
\operatorname{epi}_{\mathbb R}(G)
=\overline{\operatorname{epi}_{\mathbb R}(f)}
\subseteq\operatorname{epi}_{\mathbb R}(h),
\]
故 \(h\le G\)。这里没有对 \(h\) 的无穷值另作限制。

**S5．不成立。**

在 \(\mathbb R^2\) 中令
\[
C=\{(a,b):a\ge0,\ b\ge0,\ ab\ge1\}
 =\{(a,b):a>0,\ b\ge1/a\},
\]
并定义
\[
f(a,b)=
\begin{cases}
0,&(a,b)\in C,\\
+\infty,&(a,b)\notin C.
\end{cases}
\]
第一个表达式说明 \(C\) 闭；第二个表达式及 \(a\mapsto1/a\) 在 \((0,\infty)\) 上的凸性说明 \(C\) 凸。于是
\[
\operatorname{epi}_{\mathbb R}(f)=C\times[0,\infty)
\]
闭且凸，而且 \(f(1,1)=0\)。

取 \(F=\operatorname{span}\{\varphi\}\)，其中 \(\varphi(a,b)=a\)，将 \(F^*\) 识别为 \(\mathbb R\)。则
\[
g_F(a)=
\begin{cases}
0,&a>0,\\
+\infty,&a\le0.
\end{cases}
\]
因为 \(g_F(1/n)=0\)，但 \(g_F(0)=+\infty\)，所以 \(g_F\) 不下半连续。

**S6．所述等价与恒等式成立，但最外层下半连续化不能总省去。**

由 S4，\(G\) 下半连续。因此 \(G=f\) 蕴含 \(f\) 下半连续。反过来，若 \(f\) 下半连续，则共同设定中的凸性使 \(f\) 本身成为合法竞争函数，故
\[
f\le G\le f.
\]
所以
\[
\boxed{G=f\quad\Longleftrightarrow\quad f\text{ 下半连续}.}
\]

固定 \(F\subset K\)，令
\[
v(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
由与 S1 相同的近似下确界论证，\(v\) 非负、凸且至少一点有限。由 \(\bar g_K\le g_K\) 及 S1，
\[
v\le g_F.
\]
另一方面，S4 的扩大观测空间关系给出
\[
\bar g_F(r_{KF}z)\le\bar g_K(z),
\]
对纤维取下确界，得到
\[
\bar g_F\le v\le g_F.
\]
由于 \(\bar g_F\) 下半连续、凸，左不等式及最大性给出 \(\bar g_F\le\bar v\)；右不等式及最大性给出 \(\bar v\le\bar g_F\)。因此
\[
\boxed{
\bar g_F
=\overline{\left(y\longmapsto
       \inf_{r_{KF}z=y}\bar g_K(z)\right)}.
}
\]

最外层的横线不能总省去。使用 S5 的例子，并取 \(K=E'=(\mathbb R^2)'\)。在自然识别下，\(g_K=f\)，故 \(\bar g_K=f\)。于是
\[
\inf_{r_{KF}z=a}\bar g_K(z)=g_F(a),
\]
而
\[
\bar g_F(a)=
\begin{cases}
0,&a\ge0,\\
+\infty,&a<0.
\end{cases}
\]
在 \(a=0\) 处，左侧 \(\bar g_F(0)=0\)，未经最外层下半连续化的右侧为 \(+\infty\)，故不能省去。