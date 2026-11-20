## S1　原始记录

由 \(f\ge 0\) 得 \(g_F\ge 0\)。取 \(x_0\in E\) 使 \(f(x_0)<\infty\)，则 \(g_F(q_Fx_0)\le f(x_0)<\infty\)。

为证凸性，取 \((y_i,t_i)\in\operatorname{epi}_{\mathbb R}(g_F)\)，\(i=1,2\)。对每个 \(\varepsilon>0\)，可取 \(x_i\) 使 \(q_Fx_i=y_i\) 且 \(f(x_i)\le t_i+\varepsilon\)。于是对 \(0\le\lambda\le1\)，由 \(q_F\) 的线性和 \(f\) 的凸性，
\[
g_F\bigl(\lambda y_1+(1-\lambda)y_2\bigr)
\le f\bigl(\lambda x_1+(1-\lambda)x_2\bigr)
\le \lambda t_1+(1-\lambda)t_2+\varepsilon.
\]
令 \(\varepsilon\downarrow0\)，即得实高度上图凸。

当 \(F\subset K\) 时，\(q_F=r_{KF}q_K\)，故按 \(q_Kx\) 的值分组取下确界，得到
\[
g_F(y)
=\inf_{r_{KF}z=y}\ \inf_{q_Kx=z} f(x)
=\inf_{r_{KF}z=y}g_K(z).
\]
空纤维也符合此式。本阶段的证明均不需要下确界取到。

## S2　紧次水平集

记 \(L_c=\{x:f(x)\le c\}\)。设 \(a=g_F(y)<\infty\)。对每个 \(n\ge1\)，集合
\[
A_n=L_{a+1/n}\cap q_F^{-1}(\{y\})
\]
由下确界的定义非空。由于 \(f\) 下半连续，\(L_{a+1/n}\) 闭。由于 \(F\) 有限维，\(q_F\) 在选定基后的各坐标都是连续线性泛函，故 \(q_F\) 连续。于是 \(A_n\) 是紧集 \(L_{a+1}\) 中递减的非空闭集，其交非空。取 \(x\in\bigcap_n A_n\)，则 \(q_Fx=y\) 且 \(f(x)\le a\)。由 \(a\) 的定义，\(f(x)=a\)。

因此对每个有限实数 \(c\)，有
\[
\{y:g_F(y)\le c\}=q_F(L_c).
\]
右端是紧集在连续映射下的像，在 Hausdorff 空间 \(F^*\) 中闭。所有有限实数次水平集均闭，故 \(g_F\) 下半连续。

## S3　兼容成本记录的实现

在紧集 \(L_c\) 中，对每个有限维 \(F\subset E'\) 取闭集
\[
B_F=L_c\cap q_F^{-1}(\{y_F\}).
\]
由 \(g_F(y_F)\le c\) 和 S2 的取到性，\(B_F\) 非空。给定有限多个 \(F_1,\ldots,F_m\)，令 \(K=F_1+\cdots+F_m\)。兼容性给出
\[
\varnothing\ne B_K\subseteq\bigcap_{i=1}^m B_{F_i}.
\]
故这族闭集具有有限交性质。由紧性，可取 \(x\in\bigcap_F B_F\)，它满足全部记录且 \(f(x)\le c\)。

若 \(x'\) 也满足全部记录，对每个 \(\varphi\in E'\) 取 \(F=\operatorname{span}\{\varphi\}\)，得 \(\varphi(x')=\varphi(x)\)。Hausdorff 局部凸空间的连续对偶由 Hahn–Banach 定理分离点，故 \(x'=x\)。

## S4　一般成本的恢复

对非负凸函数 \(u\)，用上图闭包定义 \(\bar u\)：
\[
\operatorname{epi}_{\mathbb R}(\bar u)
=\overline{\operatorname{epi}_{\mathbb R}(u)}.
\]
这个定义成立，因为闭包仍向上封闭，且包含在 \(t\ge0\) 中。每条垂直截面因而为空或形如 \([a,\infty)\)，分别对应函数值 \(+\infty\) 或 \(a\)。上图闭包是闭凸集，故 \(\bar u\) 下半连续且凸。由上图包含关系，\(\bar u\le u\)，且任何下半连续凸下界的闭上图都包含该闭包，所以 \(\bar u\) 是最大的下半连续凸下界。

由全部记录构造
\[
\boxed{\displaystyle G(x)=\sup_{\substack{F\subset E'\\ \dim F<\infty}}\bar g_F(q_Fx).}
\]
扩大观测空间时，对 \(F\subset K\)，S1 给出
\(\bar g_F(r_{KF}z)\le g_F(r_{KF}z)\le g_K(z)\)。由于 \(r_{KF}\) 是有限维空间之间的连续线性映射，\(\bar g_F\circ r_{KF}\) 是 \(g_K\) 的下半连续凸下界。因此
\[
\bar g_F\circ r_{KF}\le\bar g_K.
\]
特别地，定义 \(G(x)\) 的各项随 \(F\) 扩大而单调不减，并且都介于 \(0\) 和 \(f(x)\) 之间。

为证最大性，记 \(D=\operatorname{epi}_{\mathbb R}(f)\)，\(T_F(x,t)=(q_Fx,t)\)。有
\[
\overline{T_F(D)}=\overline{\operatorname{epi}_{\mathbb R}(g_F)}.
\]
事实上，\(T_F(D)\subseteq\operatorname{epi}_{\mathbb R}(g_F)\)。反过来，若 \(g_F(y)\le t\)，则对每个 \(\varepsilon>0\) 都有 \((y,t+\varepsilon)\in T_F(D)\)。

由 \(G\) 的定义和上述等式，
\[
\operatorname{epi}_{\mathbb R}(G)
=\bigcap_F T_F^{-1}\bigl(\overline{T_F(D)}\bigr)
=\overline D.
\]
最后一个等号可由分离定理证明。交集中的每个集合都是包含 \(D\) 的闭集，故包含 \(\overline D\)。反过来，若 \(p\notin\overline D\)，由于 \(E\times\mathbb R\) 是 Hausdorff 局部凸空间，而 \(\overline D\) 是非空闭凸集，点与闭凸集的严格分离定理给出连续线性泛函 \(L\) 和实数 \(b\)，使 \(L(p)<b\le L(d)\) 对所有 \(d\in D\) 成立。写成
\[
L(x,t)=\varphi(x)+\alpha t,\qquad \varphi\in E',\ \alpha\in\mathbb R.
\]
取 \(F=\operatorname{span}\{\varphi\}\)，则 \(L(x,t)=(q_Fx)(\varphi)+\alpha t\)。因此闭半空间 \(\{(y,s):y(\varphi)+\alpha s\ge b\}\) 包含 \(\overline{T_F(D)}\)，而 \(T_F(p)\) 在其外。故 \(p\) 不属于上述交集。

于是 \(G\) 下半连续、凸且 \(G\le f\)。若 \(h\le f\) 下半连续且凸，则其闭上图包含 \(D\)，从而包含 \(\overline D=\operatorname{epi}_{\mathbb R}(G)\)，即 \(h\le G\)。这个包含关系也涵盖 \(h\) 同时取 \(-\infty\) 与 \(+\infty\) 的情形，此时相应的垂直截面分别为整条实线与空集。

## S5　闭成本的有限投影

**不一定下半连续。** 取
\[
C=\{(s,v)\in[0,\infty)^2:sv\ge1\},\qquad
f(s,v)=
\begin{cases}
0,&(s,v)\in C,\\
+\infty,&(s,v)\notin C.
\end{cases}
\]
由乘法的连续性，\(C\) 闭。它也可写成 \(\{(s,v):s>0,\ v\ge1/s\}\)，由 \(s\mapsto1/s\) 在 \((0,\infty)\) 上的凸性可知 \(C\) 凸。因此 \(f\) 的实高度上图 \(C\times[0,\infty)\) 闭且凸，并且 \(f(1,1)=0\)。

取 \(F\) 为第一坐标泛函张成的空间，将 \(F^*\) 识别为 \(\mathbb R\)。由于 \(C\) 在第一坐标上的投影为 \((0,\infty)\)，有
\[
g_F(s)=
\begin{cases}
0,&s>0,\\
+\infty,&s\le0.
\end{cases}
\]
其零次水平集 \((0,\infty)\) 不闭。

## S6　恢复与投影的精确关系

由 S4 的恒等式 \(\operatorname{epi}_{\mathbb R}(G)=\overline{\operatorname{epi}_{\mathbb R}(f)}\)，\(G=f\) 当且仅当 \(f\) 的实高度上图闭，即当且仅当 \(f\) 下半连续。

对 \(F\subset K\)，记
\[
u(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
这是非负凸函数，凸性可沿用 S1 的近似取点论证。由 S4 的 \(\bar g_F\circ r_{KF}\le\bar g_K\)，以及 \(\bar g_K\le g_K\) 和 S1 的分组公式，得
\[
\bar g_F(y)\le u(y)\le g_F(y).
\]
左边说明 \(\bar g_F\) 是 \(u\) 的下半连续凸下界，故 \(\bar g_F\le\bar u\)。右边说明 \(\bar u\) 是 \(g_F\) 的下半连续凸下界，故 \(\bar u\le\bar g_F\)。因此
\[
\boxed{\displaystyle
\bar g_F=\overline{\left(y\longmapsto\inf_{r_{KF}z=y}\bar g_K(z)\right)}.}
\]

**最外层的闭化不能总省去。** 在 S5 的例子中取 \(K=E'\)。因 \(E=\mathbb R^2\)，\(q_K:E\to K^*\) 是线性同胚，在此识别下 \(g_K=f=\bar g_K\)。于是 \(u=g_F\)，在 \(0\) 处取 \(+\infty\)。但 \((1/n,0)\in\operatorname{epi}_{\mathbb R}(g_F)\) 趋于 \((0,0)\)，故 \(\bar g_F(0)=0\)。这给出了省去最外层闭化后等式失效的具体点。