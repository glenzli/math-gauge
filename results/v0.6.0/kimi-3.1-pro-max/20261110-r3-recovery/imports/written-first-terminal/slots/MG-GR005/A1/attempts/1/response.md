## S1　原始记录

固定有限维 \(F\subset E'\)。

### 1. 非负性与至少一点有限

因为 \(f\ge 0\)，任意纤维上的下确界也非负；空纤维的下确界为 \(+\infty\)，故
\[
g_F:F^*\longrightarrow[0,+\infty].
\]
取 \(x_0\in E\) 使 \(f(x_0)<+\infty\)，则
\[
g_F(q_Fx_0)\le f(x_0)<+\infty,
\]
所以 \(g_F\) 至少一点有限。

### 2. 凸性

设 \(y_0,y_1\in F^*\)，\(0<\lambda<1\)，令
\[
y_\lambda=(1-\lambda)y_0+\lambda y_1.
\]
若 \(g_F(y_0)=+\infty\) 或 \(g_F(y_1)=+\infty\)，凸不等式显然成立。否则，对任意 \(\varepsilon>0\)，取 \(x_i\) 满足
\[
q_Fx_i=y_i,\qquad f(x_i)\le g_F(y_i)+\varepsilon .
\]
令 \(x_\lambda=(1-\lambda)x_0+\lambda x_1\)。由 \(q_F\) 的线性和 \(f\) 的凸性，
\[
q_Fx_\lambda=y_\lambda,\qquad
f(x_\lambda)\le (1-\lambda)f(x_0)+\lambda f(x_1).
\]
因此
\[
g_F(y_\lambda)
\le (1-\lambda)g_F(y_0)+\lambda g_F(y_1)+\varepsilon .
\]
令 \(\varepsilon\downarrow0\) 即得凸性。端点 \(\lambda=0,1\) 是显然的。

### 3. 扩大观测空间时的原始记录公式

设 \(F\subset K\)，记 \(r=r_{KF}\)。对固定的 \(y\in F^*\)，有纤维分解
\[
\{x\in E:q_Fx=y\}
=
\bigcup_{\substack{z\in K^*\\rz=y}}
\{x\in E:q_Kx=z\}.
\]
事实上，若 \(q_Fx=y\)，则 \(z=q_Kx\) 满足 \(rz=y\)；反向包含也直接由 \(q_F=r\circ q_K\) 得到。

对不相交纤维的并取下确界，可以先分别在每个纤维上取下确界，再对 \(z\) 取下确界，故
\[
\boxed{\;
g_F(y)=\inf_{\substack{z\in K^*\\r_{KF}z=y}}g_K(z).
\;}
\]
空纤维对应 \(+\infty\)，不影响该等式。

**以上证明完全不需要纤维下确界取到。** 凸性证明只使用近似极小化点，兼容公式只使用纤维分解和下确界的结合律。

---

## S2　紧次水平集

现在另设 \(f\) 下半连续，且对任意有限实数 \(c\)，
\[
C_c:=\{x\in E:f(x)\le c\}
\]
为紧集。

先证明一个阈值存在性结论：若 \(c\ge0\) 且 \(g_F(y)\le c\)，则存在 \(x\) 使
\[
q_Fx=y,\qquad f(x)\le c.
\]
为此，对每个 \(n\ge1\)，由 \(g_F(y)\le c<c+1/n\)，集合
\[
A_n:=\left\{x\in C_{c+1}:q_Fx=y,\ f(x)\le c+\frac1n\right\}
\]
非空。由于 \(f\) 下半连续、\(q_F\) 连续，\(A_n\) 是紧集 \(C_{c+1}\) 的闭子集，因而紧；并且 \(A_1\supset A_2\supset\cdots\)。由有限交性质，
\[
\bigcap_{n\ge1}A_n\ne\varnothing .
\]
任取交集中的 \(x\)，便有 \(q_Fx=y\)，且
\[
f(x)\le c+\frac1n\qquad(n\ge1),
\]
所以 \(f(x)\le c\)。

由此得到，对任意 \(c\ge0\)，
\[
\{y\in F^*:g_F(y)\le c\}=q_F(C_c).
\]
右端是紧集的连续像，故为 \(F^*\) 中的紧集；有限维空间 \(F^*\) 是 Hausdorff 空间，所以它是闭集。对 \(c<0\)，两端均为空集。因此 \(g_F\) 的所有实数次水平集均闭，即
\[
\boxed{g_F\text{ 下半连续}.}
\]

若 \(m:=g_F(y)<+\infty\)，则 \(m\ge0\)。把上述结论用于 \(c=m\)，得到 \(x\) 满足 \(q_Fx=y\) 且 \(f(x)\le m\)。另一方面，由下确界定义 \(m\le f(x)\)，故
\[
\boxed{f(x)=g_F(y),\qquad q_Fx=y,}
\]
即纤维下确界取到。

---

## S3　兼容成本记录的实现

沿用 S2 的条件。令
\[
C:=\{x\in E:f(x)\le c\},
\]
它是紧集。对每个有限维 \(F\subset E'\)，定义
\[
A_F:=\{x\in C:q_Fx=y_F\}.
\]

因为 \(g_F(y_F)\le c<+\infty\)，S2 给出纤维中的极小化点，所以 \(A_F\ne\varnothing\)。又因为 \(q_F\) 连续而单点 \(\{y_F\}\) 闭，\(A_F\) 是 \(C\) 的闭子集，因而紧。

下面验证有限交性质。任取有限多个 \(F_1,\dots,F_n\)，令
\[
K:=F_1+\cdots+F_n,
\]
这是有限维子空间。取 \(x\in A_K\)。对每个 \(i\)，由 \(F_i\subset K\) 及兼容性，
\[
q_{F_i}x
=r_{KF_i}(q_Kx)
=r_{KF_i}y_K
=y_{F_i}.
\]
同时 \(f(x)\le c\)，所以
\[
x\in\bigcap_{i=1}^n A_{F_i}.
\]
故 \(\{A_F\}\) 具有有限交性质。由 \(C\) 的紧性，
\[
\bigcap_F A_F\ne\varnothing .
\]
任取其中的 \(x\)，即得
\[
q_Fx=y_F\quad\text{对所有有限维 }F\subset E',
\qquad f(x)\le c.
\]

最后证明唯一性。若 \(x'\) 也满足同样的记录条件，则对任意 \(\varphi\in E'\)，取 \(F=\operatorname{span}\{\varphi\}\)，便有
\[
\varphi(x)=\varphi(x').
\]
因此所有连续线性泛函在 \(x-x'\) 上均为零。Hausdorff 局部凸空间的连续对偶分离点，故 \(x=x'\)。

所以所要求的 \(x\) 存在且唯一。

---

## S4　一般成本的恢复

结论：**可以构造。**

### 1. 下半连续凸包络

若 \(u:X\to[0,+\infty]\) 是至少一点有限的凸函数，记其最大下半连续凸下界为 \(\bar u\)。它可由
\[
\operatorname{epi}_{\mathbb R}(\bar u)
=\overline{\operatorname{epi}_{\mathbb R}u}
\]
得到。非负性保证 \(\bar u\ge0\)，至少一点有限保证 \(\bar u\) 不恒为 \(+\infty\)。若 \(v\) 下半连续、凸且 \(v\le u\)，则 \(\operatorname{epi}_{\mathbb R}v\) 是包含 \(\operatorname{epi}_{\mathbb R}u\) 的闭凸集，故也包含其闭包，从而 \(v\le\bar u\)。这正是最大性。

### 2. 构造

对所有有限维 \(F\subset E'\)，定义
\[
H_F:=\bar g_F\circ q_F,
\qquad
\boxed{\;
G(x):=\sup_{F\subset E',\ \dim F<\infty}\bar g_F(q_Fx).
\;}
\]

每个 \(q_F\) 连续线性，每个 \(\bar g_F\) 在有限维空间 \(F^*\) 上下半连续、凸，所以 \(H_F\) 下半连续、凸。任意族下半连续凸函数的上确界仍下半连续、凸，因此 \(G\) 下半连续、凸且非负。

又因为 \(x\) 自身属于纤维 \(\{w:q_Fw=q_Fx\}\)，
\[
\bar g_F(q_Fx)\le g_F(q_Fx)\le f(x).
\]
取上确界得 \(G\le f\)。在 \(f(x_0)<+\infty\) 的点也有 \(G(x_0)<+\infty\)。

### 3. 最大性

设 \(h:E\to[-\infty,+\infty]\) 下半连续、凸且 \(h\le f\)。先处理不当凸函数：令
\[
h_+:=\max\{h,0\}.
\]
其实高度上图为两个闭凸上图的交，所以 \(h_+\) 仍下半连续、凸；并且
\[
h\le h_+\le f,
\]
其中第二个不等式使用了 \(h\le f\) 和 \(0\le f\)。在 \(f\) 有限的点，\(h_+\) 也有限，因此 \(h_+\) 是 proper 的非负下半连续凸函数。

在 Hausdorff 局部凸空间上，proper 下半连续凸函数是其所有连续仿射下包的逐点上确界；这是 Hahn–Banach 分离定理的标准结论，proper 性保证所需的仿射下包存在。

固定 \(x\)，任取实数 \(t<h_+(x)\)。于是存在 \(\varphi\in E'\)、\(a\in\mathbb R\)，使仿射函数
\[
\ell(w):=a+\varphi(w)
\]
满足
\[
\ell\le h_+,\qquad \ell(x)>t.
\]
取有限维 \(F:=\operatorname{span}\{\varphi\}\)。对 \(y\in F^*\)，定义
\[
\ell_F(y):=a+y(\varphi).
\]
若 \(q_Fw=y\)，则
\[
\ell(w)=a+\varphi(w)=a+y(\varphi)=\ell_F(y).
\]
由于 \(\ell\le h_+\le f\)，对该纤维中的所有 \(w\) 都有 \(\ell_F(y)\le f(w)\)，取下确界得
\[
\ell_F(y)\le g_F(y).
\]
\(\ell_F\) 是 \(F^*\) 上的连续仿射函数，因而是下半连续凸下包；由 \(\bar g_F\) 的最大性，
\[
\ell_F\le\bar g_F.
\]
特别地，
\[
t<\ell(x)=\ell_F(q_Fx)
\le\bar g_F(q_Fx)\le G(x).
\]
对所有 \(t<h_+(x)\) 取极限，得到 \(h_+(x)\le G(x)\)；当 \(h_+(x)=+\infty\) 时，这迫使 \(G(x)=+\infty\)。故
\[
h\le h_+\le G.
\]
所以 \(G\) 正是 \(f\) 的最大下半连续凸下界。

### 4. 扩大观测空间时的关系

设 \(F\subset K\)，\(r=r_{KF}\)，并定义
\[
v_{KF}(y):=\inf_{rz=y}\bar g_K(z).
\]
由 S1 及 \(\bar g_K\le g_K\)，先有 \(v_{KF}\le g_F\)。

另一方面，任取 \(F^*\) 上满足 \(\ell\le g_F\) 的连续仿射函数 \(\ell\)。对任意 \(z\in K^*\)，S1 给出
\[
\ell(rz)\le g_F(rz)
=\inf_{rz'=rz}g_K(z')
\le g_K(z).
\]
因此 \(\ell\circ r\) 是 \(g_K\) 的连续仿射下包，从而
\[
\ell\circ r\le\bar g_K.
\]
固定 \(y\)，对所有 \(rz=y\) 的 \(z\) 取下确界，得到 \(\ell(y)\le v_{KF}(y)\)。再对所有这样的 \(\ell\) 取上确界，由有限维空间上的仿射下包表示，
\[
\bar g_F\le v_{KF}.
\]
于是有基本夹逼关系
\[
\boxed{\;
\bar g_F(y)\le
\inf_{r_{KF}z=y}\bar g_K(z)
\le g_F(y).
\;}
\]
特别地，对任意 \(z\in K^*\)，
\[
\boxed{\bar g_F(r_{KF}z)\le\bar g_K(z).}
\]
因而 \(F\subset K\) 时 \(H_F\le H_K\)。有限维子空间按包含构成有向集，有限多个 \(F_i\) 总可包含在 \(K=\sum_iF_i\) 中，所以 \(G\) 也是单调有向族 \(\{H_F\}\) 的上确界（或极限）。

---

## S5　闭成本的有限投影

**不必下半连续。**

在 \(E=\mathbb R^2\) 上考虑
\[
C:=\{(a,b):a>0,\ b>0,\ ab\ge1\},
\qquad
f(a,b):=
\begin{cases}
0,&(a,b)\in C,\\
+\infty,&(a,b)\notin C.
\end{cases}
\]
在正象限内，\(C\) 可写成
\[
\log a+\log b\ge0,
\]
而 \(\log\) 是凹函数，所以 \(C\) 凸。它也是闭集：若 \(C\) 中点列收敛，则极限满足 \(ab\ge1\)、\(a,b\ge0\)，从而必有 \(a,b>0\)。因此
\[
\operatorname{epi}_{\mathbb R}f=C\times[0,+\infty)
\]
闭且凸，且 \(f(1,1)=0\)，故 \(f\) 满足本阶段全部假设。

取 \(F\) 为第二个坐标泛函张成的一维空间，并识别 \(F^*\simeq\mathbb R\)，则 \(q_F(a,b)=b\)。于是
\[
g_F(b)=\inf_{a\in\mathbb R}f(a,b)
=
\begin{cases}
0,&b>0,\\
+\infty,&b\le0.
\end{cases}
\]
这里 \(b>0\) 时可取 \(a=1/b\)；\(b\le0\) 时纤维与 \(C\) 无交。

取 \(b_n=1/n\downarrow0\)，则 \(g_F(b_n)=0\)，但 \(g_F(0)=+\infty\)。所以 \(g_F\) 在 \(0\) 处不下半连续。

---

## S6　恢复与投影的精确关系

### 1. \(G=f\) 的充要条件

若 \(G=f\)，由于 \(G\) 下半连续，立即得到 \(f\) 下半连续。

反之，若 \(f\) 下半连续，则 \(f\) 本身就是一个下半连续、凸且满足 \(f\le f\) 的竞争函数。由 S4 中 \(G\) 的最大性，\(f\le G\)；又始终有 \(G\le f\)，故
\[
\boxed{G=f\iff f\text{ 下半连续}.}
\]

### 2. 闭包投影公式

设 \(F\subset K\)，仍记
\[
v_{KF}(y)=\inf_{r_{KF}z=y}\bar g_K(z).
\]
它与 S1 中的下确界投影具有同样的非负性、凸性和至少一点有限性，因此可以取 \(\bar v_{KF}\)。

S4 已证明
\[
\bar g_F\le v_{KF}\le g_F.
\]
由 \(v_{KF}\le g_F\) 及 \(\bar g_F\) 的最大性，得到
\[
\bar v_{KF}\le\bar g_F.
\]
另一方面，\(\bar g_F\) 是 \(v_{KF}\) 的下半连续凸下界，而 \(\bar v_{KF}\) 是最大的这样的下界，所以
\[
\bar g_F\le\bar v_{KF}.
\]
故
\[
\boxed{\;
\bar g_F
=
\overline{\left(
y\longmapsto
\inf_{r_{KF}z=y}\bar g_K(z)
\right)}.
\;}
\]

### 3. 最外层闭包不能总省去

沿用 S5 的 \(E=\mathbb R^2\) 和 \(f\)，并取 \(K=E'\)。在标准识别下 \(K^*\simeq\mathbb R^2\)，\(q_K\) 为恒同映射，因此
\[
g_K=f,\qquad \bar g_K=f,
\]
最后一个等式因为 \(f\) 下半连续。

仍取 \(F\) 为第二个坐标方向，则 \(r_{KF}(a,b)=b\)，且
\[
v_{KF}(b)=\inf_a f(a,b)
=
\begin{cases}
0,&b>0,\\
+\infty,&b\le0.
\end{cases}
\]
而
\[
\operatorname{epi}_{\mathbb R}g_F
=\{(b,t):b>0,\ t\ge0\},
\]
其闭包为 \(\{(b,t):b\ge0,\ t\ge0\}\)，所以
\[
\bar g_F(b)=
\begin{cases}
0,&b\ge0,\\
+\infty,&b<0.
\end{cases}
\]
在 \(b=0\) 处，
\[
v_{KF}(0)=+\infty,\qquad \bar g_F(0)=0.
\]
因此不带最外层闭包时等式一般不成立；最外层的 \(\bar{\phantom{u}}\) **不能省去**。