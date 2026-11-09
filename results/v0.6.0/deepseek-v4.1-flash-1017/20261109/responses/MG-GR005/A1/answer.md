以下 \(F,K\) 均表示 \(E'\) 的有限维子空间；记
\[
r_{KF}:K^*\to F^*,\qquad r_{KF}z=z|_F,
\]
并注意
\[
q_F=r_{KF}\circ q_K\qquad(F\subset K).
\]

---

## S1　原始记录

**结论：成立。**

### 1. \(g_F\) 非负、凸且至少一点有限

因 \(f\ge 0\)，由下确界定义立得 \(g_F\ge 0\)。

取 \(x_0\in E\) 使 \(f(x_0)<+\infty\)，令 \(y_0=q_Fx_0\)。则
\[
g_F(y_0)=\inf_{q_Fx=y_0}f(x)\le f(x_0)<+\infty,
\]
故 \(g_F\) 至少一点有限。

证明凸性。取 \(y_1,y_2\in F^*\)，\(\lambda\in[0,1]\)。若
\[
\lambda g_F(y_1)+(1-\lambda)g_F(y_2)=+\infty,
\]
则凸性不等式显然。否则两端有限。任取 \(\varepsilon>0\)，由下确界定义可取 \(x_1,x_2\in E\) 使
\[
q_Fx_i=y_i,\qquad f(x_i)\le g_F(y_i)+\varepsilon\quad(i=1,2).
\]
令 \(x_\lambda=\lambda x_1+(1-\lambda)x_2\)。由 \(q_F\) 线性，
\[
q_Fx_\lambda=\lambda y_1+(1-\lambda)y_2.
\]
于是由 \(f\) 的凸性，
\[
\begin{aligned}
g_F(\lambda y_1+(1-\lambda)y_2)
&\le f(x_\lambda)\\
&\le \lambda f(x_1)+(1-\lambda)f(x_2)\\
&\le \lambda g_F(y_1)+(1-\lambda)g_F(y_2)+\varepsilon.
\end{aligned}
\]
令 \(\varepsilon\downarrow0\)，得凸性。

### 2. \(g_F(y)=\inf_{r_{KF}z=y}g_K(z)\)

设 \(F\subset K\)，\(r=r_{KF}\)。有
\[
q_F^{-1}(y)
=\bigcup_{\substack{z\in K^*\\ rz=y}}q_K^{-1}(z),
\]
因为 \(q_F=r\circ q_K\)。因此
\[
\begin{aligned}
g_F(y)
&=\inf_{x:q_Fx=y}f(x)\\
&=\inf_{\substack{z:rz=y}}\ \inf_{x:q_Kx=z}f(x)\\
&=\inf_{\substack{z:rz=y}}g_K(z).
\end{aligned}
\]
此式只是把外层下确界按纤维分解，**不需要任何纤维下确界取到**。凸性证明中也只用了近似极小点，不需要取到。

---

## S2　紧次水平集

**结论：成立。**

固定有限维 \(F\)。

### 1. \(g_F(y)<+\infty\) 时纤维下确界取到

设 \(g_F(y)=L<+\infty\)。取序列 \(x_n\in E\) 使
\[
q_Fx_n=y,\qquad f(x_n)\le L+\frac1n.
\]
特别地，当 \(n\) 充分大时 \(f(x_n)\le L+1<+\infty\)。由假设，集合
\[
\{f\le L+1\}
\]
紧。故序列 \((x_n)\) 有收敛子网 \(x_\nu\to x\)。由 \(q_F\) 连续，
\[
q_Fx=\lim q_Fx_\nu=y.
\]
又因 \(f\) 下半连续，
\[
f(x)\le\liminf_\nu f(x_\nu)\le L.
\]
而由 \(g_F\) 的定义 \(g_F(y)\le f(x)\)，故 \(f(x)=L=g_F(y)\)，下确界取到。

### 2. \(g_F\) 下半连续

设 \(y_n\to y\) 于 \(F^*\)，令
\[
L=\liminf_{n\to\infty}g_F(y_n).
\]
若 \(L=+\infty\)，结论显然。设 \(L<+\infty\)。取子列仍记为 \(y_n\)，使 \(g_F(y_n)\to L\)。

任取 \(\delta>0\)。当 \(n\) 充分大时
\[
g_F(y_n)\le L+\delta.
\]
由下确界定义，取 \(x_n\) 使
\[
q_Fx_n=y_n,\qquad f(x_n)\le g_F(y_n)+\delta\le L+2\delta.
\]
于是 \(x_n\in\{f\le L+2\delta\}\)。该集合紧，故有子网 \(x_\nu\to x\)。由 \(q_F\) 连续，
\[
q_Fx=y.
\]
由 \(f\) 下半连续，
\[
g_F(y)\le f(x)\le\liminf_\nu f(x_\nu)
\le\limsup_\nu f(x_\nu)
\le L+\delta.
\]
令 \(\delta\downarrow0\)，得
\[
g_F(y)\le L=\liminf g_F(y_n).
\]
故 \(g_F\) 下半连续。

---

## S3　兼容成本记录的实现

**结论：存在且唯一。**

对每个有限维 \(F\subset E'\)，令
\[
C_F:=q_F^{-1}(y_F)\cap\{f\le c\}.
\]
由于 \(q_F\) 连续、\(\{f\le c\}\) 紧，且 \(\{f\le c\}\) 闭，故 \(C_F\) 是紧集。

由 S2，\(g_F(y_F)<+\infty\) 时下确界取到；已知 \(g_F(y_F)\le c<+\infty\)，故存在 \(x_F\in E\) 使
\[
q_Fx_F=y_F,\qquad f(x_F)=g_F(y_F)\le c.
\]
所以 \(C_F\neq\varnothing\)。

证明有限交性质。取有限个 \(F_1,\dots,F_m\)，令
\[
K=\operatorname{span}(F_1\cup\cdots\cup F_m),
\]
则 \(K\) 有限维。对每个 \(i\)，由兼容性
\[
r_{KF_i}y_K=y_{F_i}.
\]
若 \(x\in C_K\)，则 \(q_Kx=y_K\)，从而
\[
q_{F_i}x=r_{KF_i}q_Kx=r_{KF_i}y_K=y_{F_i},
\]
且 \(f(x)\le c\)。所以
\[
C_K\subset\bigcap_{i=1}^m C_{F_i}.
\]
而 \(C_K\neq\varnothing\)，故有限交非空。

所有 \(C_F\) 都是紧集 \(C_{\{0\}}=\{f\le c\}\) 的闭子集，且具有有限交性质。由紧集有限交性质，
\[
\bigcap_F C_F\neq\varnothing.
\]
取其中一点 \(x\)，则
\[
q_Fx=y_F\quad(\forall F),\qquad f(x)\le c.
\]

唯一性：若 \(x\neq x'\)，因 \(E\) 是 Hausdorff 局部凸空间，\(E'\) 分离点，故存在 \(\varphi\in E'\) 使
\[
\varphi(x)\neq\varphi(x').
\]
取 \(F=\operatorname{span}\varphi\)，则
\[
q_Fx\neq q_Fx',
\]
与二者都等于记录 \(y_F\) 矛盾。故 \(x=x'\)。

---

## S4　一般成本的恢复

**结论：能。**

记 \(\overline{u}\) 为 \(u\) 的最大下半连续凸下界。定义
\[
G(x):=\sup_{F}\overline{g_F}(q_Fx),\qquad x\in E. \tag{4.1}
\]
这里 \(F\) 取遍 \(E'\) 的全部有限维子空间。

### 1. \(G\) 下半连续、凸、非负且 \(G\le f\)

由 S1，每个 \(g_F\) 非负凸，故 \(\overline{g_F}\) 存在、非负、下半连续凸，并且
\[
\overline{g_F}\le g_F.
\]
于是每个 \(\overline{g_F}\circ q_F\) 下半连续凸。任意多个下半连续函数的逐点上确界仍下半连续；凸函数的上确界仍凸。因此 \(G\) 下半连续、凸、非负。

对任意 \(x\) 和任意有限维 \(F\)，
\[
\overline{g_F}(q_Fx)\le g_F(q_Fx)\le f(x),
\]
因为 \(x\) 本身满足 \(q_Fx=q_Fx\)。故
\[
G(x)\le f(x).
\]

### 2. 泛性质：任意下半连续凸的 \(h\le f\) 都满足 \(h\le G\)

设 \(h:E\to[-\infty,+\infty]\) 下半连续凸，且 \(h\le f\)。若 \(h(x)=-\infty\)，显然 \(h(x)\le G(x)\)。

下面设 \(h(x)>-\infty\)。若 \(h\) 在某点取 \(-\infty\) 而不恒等于 \(-\infty\)，则因 \(h\) 下半连续凸，它不能再取有限值；于是 \(h(x)=+\infty\) 时必有 \(x\notin\overline{\operatorname{dom}h}\)，归入下面的第二种情形。因此其余情形可把 \(h\) 看作 proper。

**情形一：\(h(x)=+\infty\) 且 \(x\notin\overline{\operatorname{dom}h}\)。**

令
\[
C=\overline{\operatorname{dom}h},
\]
这是闭凸集。由严格分离定理，存在 \(\varphi\in E'\) 使
\[
\varphi(x)>a:=\sup_{z\in C}\varphi(z).
\]
若 \(\varphi(z)>a\)，则 \(z\notin C\)，从而 \(z\notin\operatorname{dom}h\)，即 \(h(z)=+\infty\)。由 \(h\le f\)，得 \(f(z)=+\infty\)。取
\[
F=\operatorname{span}\varphi.
\]
在 \(F^*\) 的自然坐标下，\(q_Fz=\varphi(z)\)。于是对任意 \(t>a\)，
\[
g_F(t)=\inf_{\varphi(z)=t}f(z)=+\infty.
\]
因此
\[
\operatorname{epi}g_F\subset\{t\le a\}\times\mathbb R.
\]
右端闭，故
\[
\operatorname{epi}\overline{g_F}
=\overline{\operatorname{epi}g_F}
\subset\{t\le a\}\times\mathbb R.
\]
而 \(\varphi(x)>a\)，所以
\[
\overline{g_F}(q_Fx)=+\infty.
\]
于是 \(G(x)=+\infty=h(x)\)。

**情形二：\(x\in\overline{\operatorname{dom}h}\)。**

若 \(h(x)\) 有限，取任意 \(t<h(x)\)；若 \(h(x)=+\infty\)，取任意实数 \(t\)。此时
\[
(x,t)\notin\operatorname{epi}h.
\]
由于 \(\operatorname{epi}h\) 闭凸，且 \(x\in\overline{\operatorname{dom}h}\)，由严格分离可把值变量系数取负并归一化，得到连续仿射函数
\[
\ell(z)=\varphi(z)+a
\]
满足
\[
\ell\le h,\qquad \ell(x)>t.
\]
具体地，分离超平面中值变量系数为负；若为零，则会在 \(E\) 中把 \(x\) 与 \(\overline{\operatorname{dom}h}\) 严格分开，与 \(x\in\overline{\operatorname{dom}h}\) 矛盾。

取 \(F=\operatorname{span}\varphi\)，在 \(F^*\) 上定义
\[
\ell_F(y):=y(\varphi)+a.
\]
则对任意 \(z\in E\)，
\[
\ell_F(q_Fz)=\varphi(z)+a=\ell(z)\le h(z)\le f(z).
\]
因此 \(\ell_F\le g_F\)。由于 \(\ell_F\) 是连续仿射函数，也有
\[
\ell_F\le\overline{g_F}.
\]
于是
\[
\overline{g_F}(q_Fx)\ge\ell_F(q_Fx)=\ell(x)>t.
\]
故
\[
G(x)>t.
\]
若 \(h(x)\) 有限，令 \(t\uparrow h(x)\)，得 \(G(x)\ge h(x)\)；若 \(h(x)=+\infty\)，令 \(t\to+\infty\)，得 \(G(x)=+\infty=h(x)\)。

综上，任意下半连续凸的 \(h\le f\) 都满足 \(h\le G\)。因此 \(G\) 是所有下半连续凸的 \(f\)-minorant 的最大者。

### 3. \(G=\overline f\) 及与原始上确界的关系

由 \(G\le f\) 且 \(G\) 下半连续凸，得
\[
G\le\overline f.
\]
另一方面，\(\overline f\) 下半连续凸且 \(\overline f\le f\)，由泛性质
\[
\overline f\le G.
\]
所以
\[
\boxed{G=\overline f.} \tag{4.2}
\]

令
\[
H(x):=\sup_F g_F(q_Fx).
\]
显然 \(H\) 非负凸且 \(H\le f\)，并且
\[
G\le H.
\]
由于 \(G\) 下半连续凸，故 \(G\le\overline H\)。反过来，\(\overline H\) 下半连续凸且 \(\overline H\le H\le f\)，由泛性质 \(\overline H\le G\)。因此
\[
\boxed{G=\overline{\left(\sup_F g_F\circ q_F\right)}.} \tag{4.3}
\]
这说明 \(G\) 确实只由全部 \(g_F\) 构造出来。

### 4. 扩大观测空间时的关系

若 \(F\subset K\)，由 S1，
\[
g_F(y)=\inf_{r_{KF}z=y}g_K(z).
\]
也就是说，把观测空间从 \(F\) 扩大到 \(K\) 后，\(F\)-记录是 \(K\)-记录沿限制映射的纤维下确界。对于固定点 \(x\)，还有
\[
g_F(q_Fx)=\inf_{r_{KF}z=q_Fx}g_K(z)\le g_K(q_Kx).
\]
因此原始记录在扩大观测时会下降。

但最终的 \(G\) 已对全部有限维 \(F\) 取上确界，所以单纯扩大观测空间不会改变最终恢复出来的 \(G\)。更精细地，S6 将证明正则化记录满足
\[
\overline{g_F}
=\overline{\inf_{r_{KF}z=\,\cdot\,}\overline{g_K}(z)}.
\]
因此若改用共尾的有限维观测族，最终得到的仍是同一个 \(G=\overline f\)。

---

## S5　闭成本的有限投影

**结论：不一定。**

反例。取 \(E=\mathbb R^2\)，坐标记为 \((x,y)\)。定义
\[
f(x,y)=
\begin{cases}
\displaystyle \max\left\{\frac1x-y,\,0\right\},&x>0,\\[1ex]
+\infty,&x\le 0.
\end{cases}
\]

### 1. 验证 \(f\) 下半连续凸且非负

在 \(x>0\) 上，\(\frac1x-y\) 是凸函数，因为 \(\frac1x\) 在 \((0,+\infty)\) 上凸、\(-y\) 是仿射函数；与 \(0\) 取最大值仍凸。将 \(f\) 在 \(x\le0\) 上定义为 \(+\infty\)，仍是凸的：若凸组合中有一个点不在 \(x>0\) 内，则右端为 \(+\infty\)，凸性不等式自动成立；若两点都在 \(x>0\) 内，则由原函数凸性成立。

\(f\ge0\) 显然，且 \(f(1,1)=0<+\infty\)。

下半连续性：在 \(x>0\) 上连续。考察边界 \(x=0\)。若 \((x_n,y_n)\to(0,y_0)\) 且 \(x_n>0\)，则 \(y_n\to y_0\) 有限，于是
\[
\frac1{x_n}-y_n\to+\infty,
\]
故
\[
f(x_n,y_n)=\max\left\{\frac1{x_n}-y_n,0\right\}\to+\infty=f(0,y_0).
\]
所以 \(f\) 在 \(x=0\) 的各点也下半连续；\(x<0\) 时同理。故 \(f\) 下半连续。

### 2. 取一维投影

取
\[
F=\operatorname{span}\varphi,\qquad \varphi(x,y)=x.
\]
则 \(F^*\cong\mathbb R\)，且 \(q_F(x,y)=x\)。于是
\[
g_F(t)=\inf_{y\in\mathbb R}f(t,y).
\]
当 \(t>0\) 时，取 \(y\ge1/t\) 可使 \(f(t,y)=0\)，故
\[
g_F(t)=0\qquad(t>0).
\]
当 \(t\le0\) 时，\(f(t,y)=+\infty\) 对所有 \(y\) 成立，故
\[
g_F(t)=+\infty\qquad(t\le0).
\]
因此
\[
g_F(t)=
\begin{cases}
0,&t>0,\\
+\infty,&t\le0.
\end{cases}
\]
但
\[
g_F(0)=+\infty,\qquad
\lim_{n\to\infty}g_F(1/n)=0,
\]
故 \(g_F\) 在 \(0\) 处不下半连续。

所以即使 \(f\) 本身下半连续凸且非负，其某个有限维投影 \(g_F\) 也未必下半连续。

---

## S6　恢复与投影的精确关系

### 1. \(G=f\) 当且仅当 \(f\) 下半连续

若 \(f\) 下半连续，则由 S4 的泛性质取 \(h=f\)，得 \(f\le G\)；而 S4 已有 \(G\le f\)，故 \(G=f\)。

反之，若 \(G=f\)，由 S4 的构造 \(G\) 下半连续，故 \(f\) 下半连续。

等价地，由 (4.2)，
\[
G=\overline f,
\]
所以 \(G=f\) 当且仅当 \(\overline f=f\)，即 \(f\) 下半连续。

### 2. 证明
\[
\overline{g_F}
=
\overline{\left(y\mapsto \inf_{r_{KF}z=y}\overline{g_K}(z)\right)}.
\]

记
\[
P_{KF}h(y):=\inf_{r_{KF}z=y}h(z).
\]
要证
\[
\overline{g_F}=\overline{P_{KF}\overline{g_K}}. \tag{6.1}
\]

令
\[
C:=\operatorname{epi}_{\mathbb R}g_K
=\{(z,t)\in K^*\times\mathbb R:g_K(z)\le t\}.
\]
定义连续线性映射
\[
L:K^*\times\mathbb R\to F^*\times\mathbb R,\qquad
L(z,t)=(r_{KF}z,t).
\]
由 S1 中 \(g_F=P_{KF}g_K\)，有
\[
L(C)=\operatorname{epi} g_F.
\]
又因为 \(g_K\) 凸，故
\[
\overline C=\operatorname{epi}\overline{g_K}.
\]
于是
\[
L(\overline C)=\operatorname{epi}\bigl(P_{KF}\overline{g_K}\bigr).
\]
对任意连续线性映射 \(L\) 和任意集合 \(C\)，成立
\[
\overline{L(C)}=\overline{L(\overline C)}.
\]
事实上，若 \(w\in\overline C\)，取网 \(c_\alpha\in C\) 使 \(c_\alpha\to w\)，由连续性 \(L(c_\alpha)\to L(w)\)，故 \(L(\overline C)\subset\overline{L(C)}\)；再取闭包即得等式。

因此
\[
\overline{\operatorname{epi}g_F}
=
\overline{L(C)}
=
\overline{L(\overline C)}
=
\overline{\operatorname{epi}\bigl(P_{KF}\overline{g_K}\bigr)}.
\]
由于 \(g_F\) 凸，左端等于
\[
\operatorname{epi}\overline{g_F}.
\]
由于 \(P_{KF}\overline{g_K}\) 也凸，右端等于
\[
\operatorname{epi}\overline{P_{KF}\overline{g_K}}.
\]
故两函数相等，即
\[
\boxed{
\overline{g_F}
=
\overline{\left(y\mapsto \inf_{r_{KF}z=y}\overline{g_K}(z)\right)}
}.
\]
这就证明了所需公式。

### 3. 最外层 \(\overline{\phantom{x}}\) 不能总省去

不能。仍取 S5 中的反例：
\[
E=\mathbb R^2,\qquad
f(x,y)=
\begin{cases}
\max\{1/x-y,0\},&x>0,\\
+\infty,&x\le0.
\end{cases}
\]
已知 \(f\) 下半连续凸且非负。

取
\[
K=E',
\]
这是有限维子空间，且 \(K^*\) 与 \(E\) 在自然意义下同构。取
\[
F=\operatorname{span}\varphi,\qquad \varphi(x,y)=x.
\]
由于 \(K=E'\) 且 \(E\) 有限维，
\[
g_K(y)=f(q_K^{-1}y),
\]
而 \(f\) 下半连续，故 \(g_K\) 下半连续，从而
\[
\overline{g_K}=g_K.
\]
限制映射 \(r_{KF}\) 在坐标下就是把 \((x,y)\) 送到 \(x\)。因此
\[
h(t):=\inf_{r_{KF}z=t}\overline{g_K}(z)
=\inf_{y\in\mathbb R}f(t,y)
=g_F(t).
\]
由 S5，
\[
h(t)=g_F(t)=
\begin{cases}
0,&t>0,\\
+\infty,&t\le0.
\end{cases}
\]
所以 \(h=g_F\) 在 \(0\) 处不下半连续：
\[
h(0)=+\infty,\qquad
\lim_{n\to\infty}h(1/n)=0.
\]
但
\[
\overline{g_F}(0)=0,
\]
因为 \(\overline{g_F}\) 是 \(h\) 的下半连续凸闭包，且 \((1/n,0)\to(0,0)\)。

于是
\[
\overline{g_F}(0)=0
\neq
+\infty
=h(0)
=
\inf_{r_{KF}z=0}\overline{g_K}(z).
\]
故右式若不取最外层的 \(\overline{\phantom{x}}\)，等于 \(h=g_F\)，一般不等于左端的 \(\overline{g_F}\)。因此外层的下半连续凸闭包不能总省去。

补充：若额外假设 S2 中的紧次水平集条件，则 S2 已保证所有 \(g_F\) 下半连续，于是
\[
\overline{g_F}=g_F,\qquad
\overline{g_K}=g_K,\qquad
P_{KF}\overline{g_K}=P_{KF}g_K=g_F,
\]
此时外层 \(\overline{\phantom{x}}\) 可以省去；但在 S6 的共同设定下不能总省去。