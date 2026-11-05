记实高度上图为 \(\operatorname{epi}_{\mathbb R}(u)\)，集合的拓扑闭包记为 \(\operatorname{cl}\)。

### S1　原始记录

取 \(x_0\in E\) 使 \(f(x_0)<\infty\)。由定义，
\[
g_F(y)\ge 0,\qquad g_F(q_Fx_0)\le f(x_0)<\infty.
\]

证明凸性。设 \((y_i,t_i)\in\operatorname{epi}_{\mathbb R}(g_F)\)，\(i=1,2\)。对任意 \(\varepsilon>0\)，可选 \(x_i\) 使
\[
q_Fx_i=y_i,\qquad f(x_i)<t_i+\varepsilon.
\]
对 \(0\le\lambda\le1\)，由 \(f\) 的凸性，
\[
g_F(\lambda y_1+(1-\lambda)y_2)
\le \lambda t_1+(1-\lambda)t_2+\varepsilon.
\]
令 \(\varepsilon\downarrow0\)，即得 \(\operatorname{epi}_{\mathbb R}(g_F)\) 凸。

若 \(F\subset K\)，则 \(q_F=r_{KF}q_K\)，所以
\[
\{x:q_Fx=y\}
=\bigcup_{r_{KF}z=y}\{x:q_Kx=z\}.
\]
对该并集取下确界，包括空集下确界为 \(+\infty\) 的情形，得到
\[
\boxed{\displaystyle
g_F(y)=\inf_{r_{KF}z=y}g_K(z).}
\]
上述证明只使用下确界的逼近性质及并集下确界公式，**不需要任何纤维下确界取到**。

### S2　紧次水平集

固定 \(F\) 和满足 \(m:=g_F(y)<\infty\) 的 \(y\)。有限维性使 \(q_F\) 连续：选 \(F\) 的一组基后，\(q_F\) 的坐标都是 \(E'\) 中的连续线性泛函。

对 \(n\ge1\)，令
\[
A_n=\{x:q_Fx=y,\ f(x)\le m+1/n\}.
\]
由下确界定义，\(A_n\) 非空；由 \(f\) 的下半连续性及 \(q_F\) 的连续性，\(A_n\) 闭。并且 \(A_1\) 是紧集 \(\{f\le m+1\}\) 的闭子集，故紧；各 \(A_n\) 递减且包含于 \(A_1\)。由紧集的有限交性质，
\[
\bigcap_{n\ge1}A_n\ne\varnothing.
\]
若 \(x_*\) 属于该交集，则 \(q_Fx_*=y\) 且 \(f(x_*)\le m\)。反向不等式由 \(m\) 的定义成立，因此
\[
f(x_*)=g_F(y).
\]
这里没有使用紧空间的序列紧性，因而适用于一般的 \(E\)。

对任意有限实数 \(c\)，所得取到性给出
\[
\{y:g_F(y)\le c\}=q_F(\{x:f(x)\le c\}).
\]
右侧是紧集的连续像；\(F^*\) 为有限维 Hausdorff 空间，所以它是闭集。故 \(g_F\) 的每个有限实次水平集均闭，从而其实高度上图闭，即 \(g_F\) 下半连续。最后一步也可直接验证：若 \(g_F(y)>t\)，取有限实数 \(a\) 满足 \(t<a<g_F(y)\)，则
\[
\bigl(F^*\setminus\{g_F\le a\}\bigr)\times(-\infty,a)
\]
是 \((y,t)\) 的开邻域，且不交上图。

### S3　兼容成本记录的实现

令
\[
C_c=\{x:f(x)\le c\},\qquad
A_F=C_c\cap q_F^{-1}(\{y_F\}).
\]
由 S2，\(g_F(y_F)\le c<\infty\) 的下确界取到，所以每个 \(A_F\) 非空。每个 \(A_F\) 都是紧集 \(C_c\) 的闭子集。

对有限多个 \(F_1,\ldots,F_n\)，令 \(K=F_1+\cdots+F_n\)。兼容性和 \(q_{F_i}=r_{KF_i}q_K\) 给出
\[
A_K\subseteq\bigcap_{i=1}^n A_{F_i}.
\]
因此 \(\{A_F\}\) 在紧集 \(C_c\) 中具有有限交性质。取
\[
x\in\bigcap_F A_F,
\]
便有 \(f(x)\le c\) 且所有 \(q_Fx=y_F\)。

此 \(x\) 唯一。确实，若 \(x'\) 也实现所有记录，则对任意 \(\varphi\in E'\)，取 \(F=\operatorname{span}\{\varphi\}\) 可得 \(\varphi(x)=\varphi(x')\)。Hausdorff 局部凸空间的连续对偶分离点：例如，对非零 \(d\) 可取连续半范数 \(p\) 使 \(p(d)>0\)，再由实 Hahn–Banach 定理得到不在 \(d\) 上为零的连续线性泛函。故 \(x=x'\)。

### S4　一般成本的恢复

**结论：成立。** 先说明所用的下半连续化。若 \(u:X\to[0,+\infty]\) 是局部凸空间上的凸函数，则
\[
D:=\operatorname{cl}\operatorname{epi}_{\mathbb R}(u)
\]
仍凸，包含于 \(X\times[0,\infty)\)，且对实高度向上封闭。因此每条非空竖直截面都是形如 \([a,\infty)\) 的闭集。令相应截面的最小值为 \(\bar u(x)\)，空截面则令 \(\bar u(x)=+\infty\)，便有
\[
\operatorname{epi}_{\mathbb R}(\bar u)=D.
\]
所以 \(\bar u\) 非负、下半连续、凸且 \(\bar u\le u\)。若 \(h\le u\) 且 \(h\) 下半连续、凸，即使 \(h\) 同时允许取 \(-\infty\) 和 \(+\infty\)，仍有
\[
\operatorname{epi}_{\mathbb R}(u)
\subseteq\operatorname{epi}_{\mathbb R}(h),
\]
故 \(D\subseteq\operatorname{epi}_{\mathbb R}(h)\)，即 \(h\le\bar u\)。这证明了 \(\bar u\) 的最大性。

仅用给定记录定义
\[
\boxed{\displaystyle
G(x)=\sup_{F\subset E',\,\dim F<\infty}
       \bar g_F(q_Fx),\qquad
\operatorname{epi}_{\mathbb R}(\bar g_F)
=\operatorname{cl}\operatorname{epi}_{\mathbb R}(g_F).}
\]
每个 \(q_F\) 连续，所以各 \(\bar g_F\circ q_F\) 下半连续且凸；其上确界 \(G\) 也下半连续且凸，因为其上图是相应上图的交。并且
\[
0\le \bar g_F(q_Fx)\le g_F(q_Fx)\le f(x),
\]
故 \(G:E\to[0,\infty]\) 且 \(G\le f\)。

**扩大观测空间的关系。** 若 \(F\subset K\)，S1 给出
\[
g_F(r_{KF}z)\le g_K(z).
\]
函数 \(\bar g_F\circ r_{KF}\) 是 \(K^*\) 上下半连续凸的 \(g_K\) 下界：限制映射 \(r_{KF}\) 是有限维空间间的连续线性映射。因此由最大性，
\[
\boxed{\bar g_F(r_{KF}z)\le\bar g_K(z).}
\]
特别地，\(\bar g_F(q_Fx)\le\bar g_K(q_Kx)\)；这些成本随观测空间按包含关系增大而递增。还有逐点夹逼
\[
\boxed{\displaystyle
\bar g_F(y)\le
\inf_{r_{KF}z=y}\bar g_K(z)
\le g_F(y).}
\tag{1}
\]
第一式来自刚证的不等式，第二式来自 \(\bar g_K\le g_K\) 和 S1。

下面证明 \(G\) 的最大性。写
\[
T_F:E\times\mathbb R\to F^*\times\mathbb R,\qquad
T_F(x,t)=(q_Fx,t).
\]
有
\[
T_F(\operatorname{epi}_{\mathbb R}f)
\subseteq\operatorname{epi}_{\mathbb R}(g_F)
\subseteq\operatorname{cl}T_F(\operatorname{epi}_{\mathbb R}f).
\]
第二个包含关系是因为，若 \(g_F(y)\le t\)，可取 \(q_Fx_n=y\) 且
\(f(x_n)<g_F(y)+1/n\le t+1/n\)。因此
\[
\operatorname{epi}_{\mathbb R}(\bar g_F)
=\operatorname{cl}T_F(\operatorname{epi}_{\mathbb R}f)
\]
及
\[
\operatorname{epi}_{\mathbb R}(G)
=\bigcap_F T_F^{-1}
 \!\left(\operatorname{cl}T_F(\operatorname{epi}_{\mathbb R}f)\right).
\tag{2}
\]

实际上，右侧恰为 \(\operatorname{cl}\operatorname{epi}_{\mathbb R}f\)。一个包含关系由各 \(T_F\) 的连续性立即得到。反过来，令
\[
C=\operatorname{cl}\operatorname{epi}_{\mathbb R}f,
\qquad (x,t)\notin C.
\]
集合 \(C\) 非空、闭且凸；\(E\times\mathbb R\) 是实 Hausdorff 局部凸空间。因此几何 Hahn–Banach 分离定理适用，存在 \(\varphi\in E'\)、\(a,\alpha\in\mathbb R\)，使
\[
\varphi(x)+at>\alpha
\ge \varphi(u)+as\quad\text{对所有 }(u,s)\in C.
\]
取 \(F=\operatorname{span}\{\varphi\}\)，包括 \(\varphi=0\) 时的零维情形。连续线性函数
\[
L_F(y,s)=y(\varphi)+as
\]
在 \(T_F(\operatorname{epi}_{\mathbb R}f)\) 上不超过 \(\alpha\)，在其闭包上亦然；但
\(L_F(T_F(x,t))>\alpha\)。所以 \(T_F(x,t)\) 不属于 (2) 中该项的闭集。由此
\[
\boxed{\operatorname{epi}_{\mathbb R}(G)
=\operatorname{cl}\operatorname{epi}_{\mathbb R}f.}
\tag{3}
\]

若竞争函数 \(h:E\to[-\infty,+\infty]\) 下半连续、凸且 \(h\le f\)，则其闭上图包含 \(f\) 的上图，故由 (3)
\[
\operatorname{epi}_{\mathbb R}(G)
\subseteq\operatorname{epi}_{\mathbb R}(h).
\]
于是 \(h\le G\)。因此 \(G\) 正是所求最大下界，也即 \(G=\bar f\)。

### S5　闭成本的有限投影

**结论：不一定下半连续。** 在 \(E=\mathbb R^2\) 中令
\[
C=\{(a,b):a>0,\ b\ge 1/a\},\qquad
f(a,b)=
\begin{cases}
0,&(a,b)\in C,\\
+\infty,&(a,b)\notin C.
\end{cases}
\]
集合 \(C\) 非空且凸，因为 \(a\mapsto1/a\) 在 \((0,\infty)\) 上凸。它也闭：等价地，
\[
C=\{(a,b):a\ge0,\ b\ge0,\ ab\ge1\}.
\]
故
\[
\operatorname{epi}_{\mathbb R}(f)=C\times[0,\infty)
\]
闭且凸，\(f\) 满足本阶段假设。

取 \(\varphi_1(a,b)=a\)、\(F=\operatorname{span}\{\varphi_1\}\)，并用 \(y(\varphi_1)\) 将 \(F^*\) 识别为 \(\mathbb R\)。直接投影得
\[
g_F(s)=
\begin{cases}
0,&s>0,\\
+\infty,&s\le0.
\end{cases}
\]
其上图包含 \((1/n,0)\) 却不包含极限 \((0,0)\)，故 \(g_F\) 不下半连续。这不与 S2 矛盾：此例的零次水平集 \(C\) 不紧。

### S6　恢复与投影的精确关系

由 S4，\(G\) 下半连续且 \(G\le f\)。若 \(f\) 下半连续，则 \(f\) 自身是 S4 中的竞争函数，故 \(f\le G\)，从而 \(G=f\)。反之，若 \(G=f\)，则 \(f\) 下半连续。因此
\[
\boxed{G=f\quad\Longleftrightarrow\quad f\text{ 下半连续}.}
\]

设 \(F\subset K\)，令
\[
v(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
\(v\) 非负；它凸，因为 S1 中的 \(\varepsilon\)-逼近凸性证明对线性映射 \(r_{KF}:K^*\to F^*\) 和非负凸函数 \(\bar g_K\) 同样适用。并且 \(g_K\) 至少一点有限，故 \(\bar g_K\) 及 \(v\) 也至少一点有限。

由 (1)，
\[
\bar g_F\le v\le g_F.
\]
由于 \(\bar g_F\) 是 \(v\) 的下半连续凸下界，且 \(\bar v\) 是 \(g_F\) 的下半连续凸下界，最大性给出
\[
\boxed{\displaystyle
\bar g_F
=\bar v
=\overline{\left(y\mapsto
 \inf_{r_{KF}z=y}\bar g_K(z)\right)}.}
\]

**最外层的横线不能总省去。** 沿用 S5 的例子，取 \(K=E'\)，以两坐标识别 \(K^*=\mathbb R^2\)。此时 \(q_K\) 是坐标恒等映射，
\[
g_K=f=\bar g_K,\qquad r_{KF}(a,b)=a.
\]
所以
\[
v(0)=\inf_{b\in\mathbb R}\bar g_K(0,b)=+\infty.
\]
另一方面，S5 中 \(g_F\) 的上图闭包为 \([0,\infty)\times[0,\infty)\)，因此
\[
\bar g_F(s)=
\begin{cases}
0,&s\ge0,\\
+\infty,&s<0,
\end{cases}
\qquad\text{特别地 }\bar g_F(0)=0.
\]
故此处 \(v\ne\bar g_F\)，外层下半连续化不可省去。