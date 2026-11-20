复核后，整体结论成立。原论证中的主要问题在 S6：由 \(g_F=P_{KF}g_K\) 不能直接推出
\[
L(\operatorname{epi}g_K)=\operatorname{epi}g_F
\]
；当纤维下确界不取到时，右端可能缺少极限高度。以下改用上图的闭包关系完成论证，并相应补强 S4 的分离论证。

以下 \(\mathcal F\) 表示 \(E'\) 的全部有限维子空间。对 \(F\in\mathcal F\)、\(F\subset K\)，记
\[
r_{KF}:K^*\to F^*,\qquad r_{KF}z=z|_F,
\]
故
\[
q_F=r_{KF}\circ q_K.
\]

对有限维空间上的非负凸函数 \(u\)，令
\[
\operatorname{epi}_{\mathbb R}(\bar u)
:=\overline{\operatorname{epi}_{\mathbb R}(u)}.
\]
由于 \(u\ge0\)，这个闭包的实高度纤维仍确定一个非负、下半连续、凸的扩展实值函数；它就是 \(u\) 的最大下半连续凸下界。特别地，任何连续仿射函数 \(\ell\le u\) 也满足 \(\ell\le\bar u\)。

## S1　原始记录

### 非负、有限性和凸性

因为 \(f\ge0\)，所以对每个 \(y\in F^*\)，
\[
g_F(y)=\inf_{q_Fx=y}f(x)\ge0.
\]

取 \(x_0\in E\) 使 \(f(x_0)<+\infty\)，并令 \(y_0=q_Fx_0\)。则
\[
g_F(y_0)\le f(x_0)<+\infty,
\]
故 \(g_F\) 至少一点有限。

证明凸性。取 \(y_1,y_2\in F^*\) 和 \(\lambda\in[0,1]\)。端点情形显然，设 \(0<\lambda<1\)。若
\[
\lambda g_F(y_1)+(1-\lambda)g_F(y_2)=+\infty,
\]
则凸性不等式显然成立。否则由下确界定义，对任意 \(\varepsilon>0\)，可取 \(x_1,x_2\in E\)，使
\[
q_Fx_i=y_i,\qquad
f(x_i)\le g_F(y_i)+\varepsilon
\quad(i=1,2).
\]
令 \(x_\lambda=\lambda x_1+(1-\lambda)x_2\)。由线性和 \(f\) 的凸性，
\[
\begin{aligned}
g_F(\lambda y_1+(1-\lambda)y_2)
&\le f(x_\lambda)\\
&\le \lambda f(x_1)+(1-\lambda)f(x_2)\\
&\le \lambda g_F(y_1)+(1-\lambda)g_F(y_2)+\varepsilon.
\end{aligned}
\]
令 \(\varepsilon\downarrow0\)，得到凸性。

### 扩大观测空间

由于
\[
q_F^{-1}(y)
=\bigcup_{\substack{z\in K^*\\r_{KF}z=y}}q_K^{-1}(z),
\]
得到
\[
\begin{aligned}
g_F(y)
&=\inf_{x:q_Fx=y}f(x)\\
&=\inf_{\substack{z\in K^*\\r_{KF}z=y}}
  \inf_{x:q_Kx=z}f(x)\\
&=\inf_{\substack{z\in K^*\\r_{KF}z=y}}g_K(z).
\end{aligned}
\tag{1.1}
\]
这里只对空纤维使用通常约定 \(\inf\varnothing=+\infty\)。该等式及凸性证明都不需要纤维下确界取到；凸性证明用的只是近似极小点。

## S2　紧次水平集

固定有限维 \(F\)。

### 有限纤维下确界取到

设 \(g_F(y)=L<+\infty\)。取 \(x_n\in E\)，使
\[
q_Fx_n=y,\qquad f(x_n)\le L+\frac1n.
\]
当 \(n\) 足够大时，\(x_n\in\{f\le L+1\}\)。由假设，该集合紧，故序列 \((x_n)\) 有收敛子列，仍记为 \(x_n\to x\)。由 \(q_F\) 连续，
\[
q_Fx=y.
\]
由 \(f\) 下半连续，
\[
f(x)\le\liminf_{n\to\infty}f(x_n)\le L.
\]
另一方面，\(g_F(y)\le f(x)\)，故
\[
f(x)=L=g_F(y).
\]
所以纤维下确界确实取到。

### \(g_F\) 下半连续

设 \(y_n\to y\) 于 \(F^*\)，并令
\[
L=\liminf_{n\to\infty}g_F(y_n).
\]
若 \(L=+\infty\)，结论显然。以下设 \(L<+\infty\)，取子列使 \(g_F(y_n)\to L\)。

任取 \(\delta>0\)。当 \(n\) 足够大时，
\[
g_F(y_n)\le L+\delta.
\]
由下确界定义，取 \(x_n\) 使
\[
q_Fx_n=y_n,\qquad
f(x_n)\le g_F(y_n)+\delta\le L+2\delta.
\]
故 \(x_n\in\{f\le L+2\delta\}\)。这是紧集，所以存在收敛子网 \(x_\nu\to x\)。由连续性 \(q_Fx=y\)，再由下半连续性，
\[
g_F(y)\le f(x)
\le\liminf_\nu f(x_\nu)
\le L+2\delta.
\]
令 \(\delta\downarrow0\)，得到
\[
g_F(y)\le L=\liminf_{n\to\infty}g_F(y_n).
\]
因此 \(g_F\) 下半连续。

## S3　兼容成本记录的实现

对每个有限维 \(F\)，令
\[
C_F:=q_F^{-1}(y_F)\cap\{f\le c\}.
\]

由 S2，因为 \(g_F(y_F)\le c<+\infty\)，存在 \(x_F\in E\) 使
\[
q_Fx_F=y_F,\qquad f(x_F)=g_F(y_F)\le c.
\]
所以 \(C_F\ne\varnothing\)。同时，\(q_F^{-1}(y_F)\) 闭，且由 \(f\) 下半连续，\(\{f\le c\}\) 闭；故 \(C_F\) 是紧集 \(\{f\le c\}\) 的闭子集，从而是紧集。特别地，
\[
C_{\{0\}}=\{f\le c\}.
\]

证明有限交性质。取有限个有限维空间 \(F_1,\dots,F_m\)，令
\[
K=\operatorname{span}(F_1\cup\cdots\cup F_m).
\]
则 \(K\) 有限维。由兼容性，
\[
r_{KF_i}y_K=y_{F_i}.
\]
若 \(x\in C_K\)，则 \(q_Kx=y_K\)，故
\[
q_{F_i}x=r_{KF_i}q_Kx=r_{KF_i}y_K=y_{F_i},
\]
并且 \(f(x)\le c\)。因此
\[
C_K\subset\bigcap_{i=1}^m C_{F_i}.
\]
由于 \(C_K\ne\varnothing\)，这些紧集具有有限交性质，故
\[
\bigcap_F C_F\ne\varnothing.
\]
取其中一点 \(x\)，即得
\[
q_Fx=y_F\quad(\forall F\in\mathcal F),\qquad f(x)\le c.
\]

再证唯一性。若 \(x\ne x'\)，因 \(E\) 是 Hausdorff 局部凸空间，连续对偶 \(E'\) 分离点，故存在 \(\varphi\in E'\) 使
\[
\varphi(x)\ne\varphi(x').
\]
取 \(F=\operatorname{span}\varphi\)，与 \(q_Fx=y_F=q_Fx'\) 矛盾。因此实现点唯一。

## S4　一般成本的恢复

结论：可以恢复。恢复值为 \(f\) 的最大下半连续凸下界。

定义
\[
G(x):=\sup_{F\in\mathcal F}\bar g_F(q_Fx),
\qquad x\in E.
\tag{4.1}
\]
这里 \(\bar g_F\) 是 \(g_F\) 的最大下半连续凸下界，等价地，\(\operatorname{epi}\bar g_F=\overline{\operatorname{epi}g_F}\)。

### \(G\) 的可行性

每个 \(\bar g_F\) 非负、下半连续、凸，并且
\[
\bar g_F\le g_F.
\]
由 \(q_F\) 连续、线性，\(\bar g_F\circ q_F\) 也非负、下半连续、凸。它们的逐点上确界仍非负、下半连续、凸，所以 \(G\) 非负、下半连续、凸。

对任意 \(x\) 和任意 \(F\)，
\[
\bar g_F(q_Fx)\le g_F(q_Fx)\le f(x),
\]
其中最后一步是因为 \(x\) 本身是纤维 \(q_F^{-1}(q_Fx)\) 中的一点。故
\[
G\le f.
\tag{4.2}
\]

### 最大性

设 \(h:E\to[-\infty,+\infty]\) 下半连续、凸且 \(h\le f\)。若 \(h(x)=-\infty\)，显然 \(h(x)\le G(x)\)。固定 \(x\)，以下设 \(h(x)>-\infty\)。

令
\[
D=\operatorname{dom}h=\{z:h(z)<+\infty\},\qquad
C=\overline D.
\]
由 \(h\le f\) 且 \(f\) 至少一点有限，知 \(D\ne\varnothing\)。

若 \(x\notin C\)，由闭凸集与点的强分离定理，存在 \(\varphi\in E'\) 和实数 \(a\)，使
\[
\varphi(x)>a,\qquad
\sup_{z\in C}\varphi(z)\le a.
\]
于是当 \(\varphi(z)>a\) 时，\(z\notin C\)，从而 \(h(z)=+\infty\)；由 \(h\le f\)，也有 \(f(z)=+\infty\)。

取 \(F=\operatorname{span}\varphi\)，并用 \(y(\varphi)\) 作为 \(F^*\) 的坐标。对任意实数 \(s>a\)，只要 \(q_Fz=s\varphi\)，便有 \(f(z)=+\infty\)，所以
\[
g_F(s\varphi)=+\infty.
\]
因此
\[
\operatorname{epi}g_F
\subset\{(s\varphi,t):s\le a,\ t\in\mathbb R\},
\]
右端闭，所以
\[
\operatorname{epi}\bar g_F
\subset\{(s\varphi,t):s\le a,\ t\in\mathbb R\}.
\]
而 \(\varphi(x)>a\)，故
\[
\bar g_F(q_Fx)=+\infty.
\]
所以 \(G(x)=+\infty=h(x)\)。

若 \(x\in C\)，任取实数 \(t<h(x)\)。则 \((x,t)\notin\operatorname{epi}h\)。这里 \(\operatorname{epi}h\) 是非空闭凸集，点与它可严格分离。具体地，存在连续线性泛函 \((\varphi,\alpha)\) 和实数 \(\rho\)，使
\[
\varphi(z)+\alpha s<\rho<\varphi(x)+\alpha t
\quad((z,s)\in\operatorname{epi}h).
\]
这里 \(\alpha\le0\)，因为当 \(s\to+\infty\) 时上图向上无界。又因 \(x\in\overline D\)，不能有 \(\alpha=0\)；否则 \(\varphi\) 会在 \(x\) 处严格大于其在 \(\overline D\) 上的上确界。因此 \(\alpha<0\)。

归一化后可写成连续仿射形式
\[
\ell(z)=\varphi(z)+b,
\qquad
\ell\le h,\qquad
\ell(x)>t.
\tag{4.3}
\]
取 \(F=\operatorname{span}\varphi\)，并在 \(F^*\) 上定义
\[
\ell_F(y):=y(\varphi)+b.
\]
则对任意 \(z\in E\)，
\[
\ell_F(q_Fz)=\varphi(z)+b=\ell(z)
\le h(z)\le f(z).
\]
所以 \(\ell_F\le g_F\)。由于 \(\ell_F\) 连续仿射，也有 \(\ell_F\le\bar g_F\)。因此
\[
G(x)\ge\bar g_F(q_Fx)
\ge\ell_F(q_Fx)
=\ell(x)>t.
\]
若 \(h(x)<+\infty\)，令 \(t\uparrow h(x)\)，得到 \(G(x)\ge h(x)\)；若 \(h(x)=+\infty\)，因 \(t\) 可任意大，得到 \(G(x)=+\infty=h(x)\)。

于是任意下半连续凸的 \(h\le f\) 都满足
\[
h\le G.
\tag{4.4}
\]

令 \(\bar f\) 表示 \(f\) 的最大下半连续凸下界。由 \(G\le f\) 且 \(G\) 下半连续、凸，得
\[
G\le\bar f.
\]
反过来，\(\bar f\) 下半连续、凸且 \(\bar f\le f\)，由 (4.4) 得 \(\bar f\le G\)。所以
\[
\boxed{G=\bar f.}
\tag{4.5}
\]

### 由原始 \(g_F\) 直接表示的公式

令
\[
H(x):=\sup_{F\in\mathcal F}g_F(q_Fx).
\]
每个 \(g_F\) 凸，故 \(H\) 凸；且由 \(0\le g_F(q_Fx)\le f(x)\)，知 \(H\) 非负且
\[
G\le H\le f.
\]
由于 \(G\) 下半连续、凸，它是 \(H\) 的一个下半连续凸下界，故
\[
G\le\bar H.
\]
另一方面，\(\bar H\) 下半连续、凸且 \(\bar H\le H\le f\)，由 (4.4) 得 \(\bar H\le G\)。因此
\[
\boxed{
G=\overline{\sup_{F\in\mathcal F}g_F\circ q_F}.
}
\tag{4.6}
\]

### 扩大观测空间

若 \(F\subset K\)，S1 给出
\[
g_F(y)=\inf_{r_{KF}z=y}g_K(z).
\tag{4.7}
\]

正则化后的记录仍随观测空间扩大而单调。设
\[
P_{KF}h(y):=\inf_{r_{KF}z=y}h(z).
\]
记
\[
L_{KF}:K^*\times\mathbb R\to F^*\times\mathbb R,\qquad
L_{KF}(z,t)=(r_{KF}z,t).
\]
对任意函数 \(h\)，有
\[
\overline{L_{KF}(\operatorname{epi}h)}
=
\overline{\operatorname{epi}(P_{KF}h)}.
\tag{4.8}
\]
事实上，\(L_{KF}(\operatorname{epi}h)\subset\operatorname{epi}(P_{KF}h)\)；反过来，若 \(P_{KF}h(y)\le t\)，可由下确界定义取 \(z_n\) 使 \(h(z_n)\le t+1/n\)，于是
\[
(y,t+1/n)=L_{KF}(z_n,t+1/n)
\]
趋于 \((y,t)\)，从而得到反向包含的闭包形式。

由 \(\operatorname{epi}\bar g_K=\overline{\operatorname{epi}g_K}\) 得
\[
\overline{L_{KF}(\operatorname{epi}g_K)}
=
\overline{L_{KF}(\operatorname{epi}\bar g_K)}.
\]
结合 (4.7)、(4.8)，若 \(\bar g_K(q_Kx)\le t\)，则
\[
(q_Kx,t)\in\operatorname{epi}\bar g_K
\]
映射后属于
\[
\overline{\operatorname{epi}g_F}
=\operatorname{epi}\bar g_F.
\]
所以
\[
\bar g_F(q_Fx)\le\bar g_K(q_Kx).
\tag{4.9}
\]
因此，若采用一个在包含关系下共尾的有限维观测族，任意较小记录都有某个更大记录支配它，最终的
\[
G=\bar f
\]
不变。对题设从全部有限维 \(F\) 同时取记录的情形，扩大一个观测空间更是只会把原空间重新包含在同一个上确界中。

## S5　闭成本的有限投影

结论：不一定。下面给出反例。

设 \(E=\mathbb R^2\)，坐标记为 \((x,y)\)，定义
\[
f(x,y)=
\begin{cases}
\displaystyle\max\left\{\frac1x-y,0\right\},&x>0,\\[1ex]
+\infty,&x\le0.
\end{cases}
\]

在 \(x>0\) 上，\(1/x-y\) 是凸函数，与 \(0\) 取最大值后仍凸；把 \(x\le0\) 定义为 \(+\infty\) 不破坏凸性。显然 \(f\ge0\)，且 \(f(1,1)=0<+\infty\)。

再验证下半连续性。在 \(x>0\) 上连续；若 \((x_n,y_n)\in\operatorname{dom}f\) 且 \((x_n,y_n)\to(0,y_0)\)，则 \(x_n\to0^+\)，故
\[
\frac1{x_n}-y_n\to+\infty,
\]
从而在边界 \(x=0\) 满足下半连续性。\(x<0\) 处同理。因此 \(f\) 下半连续、凸、非负且至少一点有限。

取
\[
F=\operatorname{span}\varphi,\qquad \varphi(x,y)=x.
\]
则 \(q_F(x,y)=x\)，并且
\[
g_F(s)=\inf_{y\in\mathbb R}f(s,y).
\]
当 \(s>0\) 时，取 \(y\ge1/s\) 可得 \(g_F(s)=0\)；当 \(s\le0\) 时，纤维中每一点的 \(f\) 都是 \(+\infty\)。因此
\[
g_F(s)=
\begin{cases}
0,&s>0,\\
+\infty,&s\le0.
\end{cases}
\]
于是
\[
g_F(0)=+\infty,
\qquad
\lim_{n\to\infty}g_F(1/n)=0,
\]
故 \(g_F\) 在 \(0\) 处不下半连续。

## S6　恢复与投影的精确关系

### \(G=f\) 当且仅当 \(f\) 下半连续

若 \(f\) 下半连续，则由 S4 的最大性，\(f\le G\)；而 (4.2) 给出 \(G\le f\)，故 \(G=f\)。反过来，若 \(G=f\)，由 S4 的构造，\(G\) 下半连续，故 \(f\) 下半连续。结合 (4.5)，这也等价于
\[
G=f\iff \bar f=f.
\]

### 投影记录及其正则化的精确关系

设 \(F\subset K\)，并记
\[
P_{KF}h(y)=\inf_{r_{KF}z=y}h(z).
\]
要证明
\[
\operatorname{epi}\bar g_F
=
\operatorname{epi}\overline{P_{KF}\bar g_K},
\]
从而
\[
\boxed{
\bar g_F
=
\overline{
y\mapsto\inf_{r_{KF}z=y}\bar g_K(z)
}.
}
\tag{6.1}
\]

令
\[
C=\operatorname{epi}g_K,\qquad
L_{KF}(z,t)=(r_{KF}z,t).
\]
由 (4.8)，
\[
\overline{L_{KF}(C)}
=
\overline{\operatorname{epi}(P_{KF}g_K)}
=
\overline{\operatorname{epi}g_F}
=
\operatorname{epi}\bar g_F.
\tag{6.2}
\]

另一方面，对任意集合 \(C\) 和连续线性映射 \(L_{KF}\)，有
\[
\overline{L_{KF}(C)}
=
\overline{L_{KF}(\overline C)}.
\]
其中包含“\(\subset\)”成立是因为闭包中的点可由 \(C\) 中的网逼近，且 \(L_{KF}\) 连续；另一方向显然。

而
\[
\overline C=\operatorname{epi}\bar g_K.
\]
所以由 (4.8) 和 (6.2)，
\[
\begin{aligned}
\operatorname{epi}\bar g_F
&=\overline{L_{KF}(\operatorname{epi}\bar g_K)}\\
&=\overline{\operatorname{epi}(P_{KF}\bar g_K)}.
\end{aligned}
\]
函数 \(P_{KF}\bar g_K\) 是凸函数，且至少一点有限；它还是非负的，因为 \(\bar g_K\ge0\)。因此
\[
\overline{\operatorname{epi}(P_{KF}\bar g_K)}
=
\operatorname{epi}\overline{P_{KF}\bar g_K}.
\]
这正是 (6.1)。

### 最外层的 bar 不能总省去

仍取 S5 的反例
\[
f(x,y)=
\begin{cases}
\max\{1/x-y,0\},&x>0,\\
+\infty,&x\le0.
\end{cases}
\]

取 \(K=E'\)，则在自然等同 \(K^*\simeq E\) 下，
\[
g_K(y)=f(q_K^{-1}y).
\]
由于 \(f\) 下半连续，\(g_K\) 也下半连续，因此
\[
\bar g_K=g_K.
\]
再取 \(F=\operatorname{span}\varphi\)，其中 \(\varphi(x,y)=x\)。限制映射在坐标下就是
\[
r_{KF}(x,y)=x.
\]
于是
\[
\inf_{r_{KF}z=t}\bar g_K(z)
=
\inf_{y\in\mathbb R}f(t,y)
=g_F(t)
=
\begin{cases}
0,&t>0,\\
+\infty,&t\le0.
\end{cases}
\]
这个函数在 \(0\) 处仍为 \(+\infty\)，而在 \(1/n\) 处为 \(0\)，所以它在 \(0\) 处不下半连续。

另一方面，\((1/n,0)\) 属于 \(\operatorname{epi}g_F\) 并收敛到 \((0,0)\)，且 \(g_F\ge0\)，故
\[
\bar g_F(0)=0.
\]
因此
\[
\bar g_F(0)=0
\ne
+\infty
=
\inf_{r_{KF}z=0}\bar g_K(z).
\]
所以在共同设定下，最外层的下半连续凸闭包不能总省去。

---

### 保留、修正和自评

- **保留：** S1、S2、S3、S5 的证明均成立；S4 的恢复构造 \(G=\sup_F\bar g_F\circ q_F\) 和 S6 的公式及反例结论也成立。
- **修正：** S6 改为使用
  \[
  \overline{L(C)}=\overline{L(\bar C)}
  \]
  和投影上图的闭包关系。不能直接断言 \(L(\operatorname{epi}g_K)=\operatorname{epi}g_F\)，因为纤维下确界可能不取到。S4 中也显式给出了严格分离及仿射下界到 \(F^*\) 的传递过程。
- **仍未完成或不确定：** 没有。题面 S1 至 S6 的全部要求均已在所述范围内证明或构造完成。

按题给研究档位自评：**B2，R3**。理由是 S4 在任意实 Hausdorff 局部凸空间、任意非负 proper 凸成本上完整给出了恢复算子，释放了 S2 的紧次水平集条件；S6 进一步建立了投影记录闭包与恢复之间的精确关系，并用反例证明最外层闭包不可省略。这构成了一个完整的一般重建机制及其锐度边界。因此在无额外交付阻断时，MC 与 RMC 均对应最高有效档，SMC 达标。