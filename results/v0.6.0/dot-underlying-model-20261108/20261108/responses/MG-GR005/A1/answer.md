## S1　原始记录

对每个有限维 (F\subset E')，显然 (g_F\geq0)。取 (x_0\in E) 使 (f(x_0)<\infty)，则
\[
g_F(q_Fx_0)\leq f(x_0)<\infty.
\]

证明凸性时，设 (0<\lambda<1)。若 (g_F(y_1),g_F(y_2)) 均有限，则对任意 (\varepsilon>0)，可取 (x_i\in E) 满足
\[
q_Fx_i=y_i,\qquad f(x_i)<g_F(y_i)+\varepsilon.
\]
由 (q_F) 的线性和 (f) 的凸性，
\[
g_F(\lambda y_1+(1-\lambda)y_2)
\leq\lambda g_F(y_1)+(1-\lambda)g_F(y_2)+\varepsilon.
\]
令 (\varepsilon\downarrow0) 即得凸性不等式；若右侧某项为 (+\infty)，不等式自动成立，端点情形亦显然。因此实高度上图凸。

若 (F\subset K)，则 (q_F=r_{KF}\circ q_K)，并且纤维有分解
\[
\{x:q_Fx=y\}
=\bigcup_{r_{KF}z=y}\{x:q_Kx=z\}.
\]
对该并集取下确界，得到
\[
\boxed{g_F(y)=\inf_{r_{KF}z=y}g_K(z).}
\]
此等式也涵盖空集和仅有无限成本的情形。上述所有证明均不需要纤维下确界取到，只使用下确界的近似性质。

## S2　紧次水平集

记 (L_c=\{x:f(x)\leq c\})。此阶段假设保证每个有限 (c) 的 (L_c) 都是紧集；由下半连续性，它们也都是闭集。映射 (q_F:E\to F^*) 连续，因为选取 (F) 的一组基后，它的坐标是有限个连续线性泛函。

固定 (y)，设 (a=g_F(y)<\infty)。对每个正整数 (n)，令
\[
A_n=L_{a+1/n}\cap q_F^{-1}\{y\}.
\]
由下确界定义，(A_n\ne\varnothing)。它们是紧集 (L_{a+1}) 中的闭子集，且单调递减。因此紧性的有限交性质给出
\[
\bigcap_{n\geq1}A_n\ne\varnothing.
\]
任取其中的 (x)，便有 (q_Fx=y) 及 (f(x)\leq a)，而下确界定义又给出 (f(x)\geq a)。故纤维最小值取到。

由此，对每个有限实数 (c)，
\[
\{y:g_F(y)\leq c\}=q_F(L_c).
\]
当 (c<0) 时两边都是空集；其他情形使用刚证明的最小值取到。右边是紧集的连续像，因有限维空间 (F^*) 是 Hausdorff 空间而为闭集。因此 (g_F) 的所有有限次水平集闭，等价地，其实高度上图闭，即 (g_F) 下半连续。

## S3　兼容成本记录的实现

继续使用 S2 的条件。对每个有限维 (F\subset E')，定义
\[
B_F=L_c\cap q_F^{-1}\{y_F\}.
\]
由 (g_F(y_F)\leq c<\infty) 以及 S2 的取到性，(B_F\ne\varnothing)。每个 (B_F) 都是紧集 (L_c) 中的闭子集。

任给有限多个 (F_1,\ldots,F_m)，令 (K=F_1+\cdots+F_m)。它仍是有限维子空间，且兼容性保证
\[
B_K\subset\bigcap_{i=1}^m B_{F_i}.
\]
于是这族闭集有有限交性质。由 (L_c) 的紧性，可取
\[
x\in\bigcap_F B_F.
\]
这就是所需构造：它满足 (f(x)\leq c) 和全部记录 (q_Fx=y_F)。

若 (x,x') 均实现这些记录，对任意 (\varphi\in E')，取 (F=\operatorname{span}\{\varphi\})，便得 (\varphi(x-x')=0)。Hausdorff 局部凸空间的连续对偶分离点，这是 Hahn–Banach 定理的标准推论；其 Hausdorff 性和局部凸性正是共同设定中的条件。因此 (x=x')。

## S4　一般成本的恢复

结论成立，且不需要紧性或预先假设 (f) 下半连续。

先说明闭上图操作。若 (u:V\to[0,+\infty]) 凸且至少一点有限，其中 (V) 是 Hausdorff 局部凸空间，令
\[
C_u=\overline{\operatorname{epi}_{\mathbb R}(u)}\subset V\times\mathbb R.
\]
这是非空闭凸集，位于高度 (t\geq0) 中，并且向上封闭。其每个竖直截面或为空，或为某个闭射线 ([a,+\infty))，其中 (a\geq0)。故存在唯一函数 (\bar u:V\to[0,+\infty])，使
\[
\operatorname{epi}_{\mathbb R}(\bar u)=C_u.
\]
它下半连续、凸、至少一点有限，且 (\bar u\leq u)。若任意允许取 (\pm\infty) 的函数 (h) 下半连续、凸且 (h\leq u)，则
\[
\operatorname{epi}_{\mathbb R}(u)
\subset\operatorname{epi}_{\mathbb R}(h).
\]
后者闭，因而包含 (C_u)，从而 (h\leq\bar u)。这也证明该构造对题目允许的全部竞争函数具有最大性。

现在仅从全部记录构造
\[
\boxed{G(x)=\sup_{F\subset E',\ \dim F<\infty}\bar g_F(q_Fx).}
\]
S1 保证上述闭上图操作适用于每个 (g_F)。每项都是非负下半连续凸函数，故它们的上确界也是如此。此外，
\[
\bar g_F(q_Fx)\leq g_F(q_Fx)\leq f(x),
\]
所以 (G\leq f)，且 (G) 在 (f) 的某个有限点有限。

下面证明最大性，特别说明有限维记录足以恢复闭上图。令
\[
A=\operatorname{epi}_{\mathbb R}(f),\quad C=\overline A,
\quad Q_F(x,t)=(q_Fx,t).
\]
由下确界定义，
\[
Q_F(A)\subset\operatorname{epi}_{\mathbb R}(g_F)
\subset\overline{Q_F(A)}.
\]
第二个包含的理由是：若 (g_F(y)\leq t\in\mathbb R)，则对每个 (\varepsilon>0)，存在同纤维的 (x) 使 (f(x)<t+\varepsilon)，所以 ((y,t+\varepsilon)\in Q_F(A))。于是
\[
\overline{Q_F(A)}=\operatorname{epi}_{\mathbb R}(\bar g_F).
\]
我们断言
\[
C=\bigcap_F Q_F^{-1}\!\left(\overline{Q_F(A)}\right).
\]
由连续性，左边包含于右边。反过来，若 (p=(x,t)\notin C)，则 (C) 是非空闭凸集，而 (E\times\mathbb R) 是 Hausdorff 局部凸空间，故点与闭凸集的严格分离定理适用。存在 (\varphi\in E')、(a\in\mathbb R) 及 (b\in\mathbb R)，使
\[
\varphi(x)+at<b\leq\varphi(v)+as\qquad((v,s)\in C).
\]
取 (F=\operatorname{span}\{\varphi\})，其中 (\varphi=0) 时允许 (F=\{0\})。有限维空间上的连续线性函数
\[
(y,s)\longmapsto y(\varphi)+as
\]
在 (Q_F(A)) 以及其闭包上都至少为 (b)，却在 (Q_F(p)) 上小于 (b)。所以 (p) 不属于右边，断言得证。

另一方面，上确界的实高度上图是各项上图之交。因此
\[
\boxed{\operatorname{epi}_{\mathbb R}(G)
=\overline{\operatorname{epi}_{\mathbb R}(f)}.}
\]
若 (h\leq f) 是题目所允许的下半连续凸函数，其闭上图包含 (A)，也就包含上述闭包，故 (h\leq G)。即使 (h) 同时取 (+\infty) 和 (-\infty)，这个上图包含论证仍完全适用。

扩大观测空间时，若 (F\subset K)，S1 给出原始记录的精确兼容关系，并有
\[
g_F(r_{KF}z)\leq g_K(z).
\]
函数 (z\mapsto\bar g_F(r_{KF}z)) 是 (g_K) 的下半连续凸下界，因此
\[
\boxed{\bar g_F(r_{KF}z)\leq\bar g_K(z).}
\]
特别地，恢复中的观测下界随观测空间扩大而单调增加：
\[
\bar g_F(q_Fx)\leq\bar g_K(q_Kx)\leq G(x).
\]
有限维子空间按包含关系构成有向集，所以构造式也就是这些单调观测下界的有向上确界。与投影相联系的更精确等式见 S6。

## S5　闭成本的有限投影

不一定下半连续。令
\[
D=\{(s,t)\in\mathbb R^2:s>0,\ t\geq1/s\},
\qquad f=\delta_D,
\]
其中 (\delta_D) 在 (D) 上为 (0)，在其外为 (+\infty)。

函数 (s\mapsto1/s) 在 ((0,+\infty)) 上凸，所以 (D) 凸。又有
\[
D=\{(s,t):s\geq0,\ t\geq0,\ st\geq1\},
\]
故 (D) 闭；且 ((1,1)\in D)，所以非空。因此 (f) 非负、凸、至少一点有限，且其实高度上图为 (D\times[0,+\infty))，是闭集。

取 (F) 为第一坐标泛函所张成的一维空间，将 (F^*) 识别为 (\mathbb R)。则
\[
g_F(s)=
\begin{cases}
0,&s>0,\\
+\infty,&s\leq0.
\end{cases}
\]
这是因为 (D) 的第一坐标投影恰好是 ((0,+\infty))。例如 ((1/n,0)\in\operatorname{epi}_{\mathbb R}(g_F)) 收敛到不在该上图中的 ((0,0))，故 (g_F) 不下半连续。

## S6　恢复与投影的精确关系

首先，S4 已证明 (G) 下半连续，并且是所有下半连续凸下界中最大的。因此：

- 若 (G=f)，则 (f) 下半连续。
- 若 (f) 下半连续，则共同设定中的凸性保证 (f) 自身就是一个允许的竞争函数，故 (f\leq G\leq f)。

所以
\[
\boxed{G=f\quad\Longleftrightarrow\quad f\text{ 下半连续}.}
\]

现在固定 (F\subset K)，记 (r=r_{KF})，并令
\[
v(y)=\inf_{rz=y}\bar g_K(z),\qquad
T:K^*\times\mathbb R\to F^*\times\mathbb R,
\quad T(z,t)=(rz,t).
\]
由 S4 的闭上图构造，(\bar g_K) 非负、凸且至少一点有限。对其作线性投影下确界，使用 S1 同样的近似最小值论证，便知 (v) 也具有这三个性质，故 (\bar v) 有定义。

对任意非负凸函数 (u)，上述投影下确界的上图与投影上图具有相同闭包：这正是 S4 中用高度 (t+\varepsilon) 逼近的论证。因此
\[
\begin{aligned}
\operatorname{epi}_{\mathbb R}(\bar v)
&=\overline{T\bigl(\operatorname{epi}_{\mathbb R}(\bar g_K)\bigr)}\\
&=\overline{T\bigl(\overline{\operatorname{epi}_{\mathbb R}(g_K)}\bigr)}\\
&=\overline{T\bigl(\operatorname{epi}_{\mathbb R}(g_K)\bigr)}\\
&=\overline{\operatorname{epi}_{\mathbb R}(g_F)}\\
&=\operatorname{epi}_{\mathbb R}(\bar g_F).
\end{aligned}
\]
其中第三个等号使用连续性给出的通用事实
\[
\overline{T(\overline B)}=\overline{T(B)}:
\]
一边来自 (B\subset\overline B)，另一边来自 (T(\overline B)\subset\overline{T(B)})。第四个等号使用 S1 的恒等式 (g_F(y)=\inf_{rz=y}g_K(z))，以及同一个投影上图闭包论证。所有闭包都取在相应的有限维空间与实高度的乘积中。

由上图相等，得到所求精确关系
\[
\boxed{\bar g_F
=\overline{\left(y\longmapsto\inf_{r_{KF}z=y}\bar g_K(z)\right)}.}
\]
这里右侧的横线表示函数的最大下半连续凸下界。

最外层横线不能总省去。使用 S5 的例子，取 (K=(\mathbb R^2)') 为全对偶，并保持 (F) 为第一坐标观测。在自然识别下，(q_K) 是恒等映射，故
\[
g_K=f=\bar g_K.
\]
于是
\[
\inf_{r_{KF}z=s}\bar g_K(z)=g_F(s)=\delta_{(0,+\infty)}(s),
\]
而
\[
\bar g_F(s)=\delta_{[0,+\infty)}(s).
\]
两者在 (s=0) 分别取 (+\infty) 和 (0)。所以即使大观测空间的成本已经闭，投影下确界仍可能不闭，最外层闭化确实必要。
