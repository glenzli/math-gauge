记 \(\overline p\) 为函数 \(p\) 的下半连续包络。对每个 \(F\)，令

\[
h_F:=\overline{g_F},\qquad
h_F(y)=\sup_{\varepsilon>0}
       \inf_{\|z-y\|<\varepsilon}g_F(z),
\]

其中 \(F^*\) 上可任选一个范数。所求函数是

\[
\boxed{\displaystyle
G(x)=\sup_{\substack{F\subset E'\\ \dim F<\infty}}
h_F(q_F(x)).}
\]

它是下半连续凸函数，满足 \(0\le G\le f\)，并且是所有不超过 \(f\) 的下半连续凸函数中最大的。事实上，\(G\) 连所有不超过 \(f\) 的下半连续函数都支配。

记录及其下半连续包络满足以下关系。若 \(F\subset K\)，则

\[
\boxed{\displaystyle
g_F(y)=\inf_{\substack{z\in K^*\\r_{KF}(z)=y}}g_K(z)}
\tag{1}
\]

以及

\[
\boxed{\displaystyle
h_F=
\overline{\left(y\longmapsto
\inf_{\substack{z\in K^*\\r_{KF}(z)=y}}h_K(z)\right)}.}
\tag{2}
\]

因此 \(h_F(q_Fx)\le h_K(q_Kx)\)：构造 \(G\) 时得到的是一个随观测空间扩大而递增的族。

定义连续对偶上的共轭函数

\[
f^*(\varphi)=\sup_{x\in E}\{\varphi(x)-f(x)\}.
\]

整个记录族确定 \(f^*\)，进而确定 \(G\)。更具体地，对任意 \(\varphi\in F\),

\[
f^*(\varphi)
=\sup_{y\in F^*}\{y(\varphi)-g_F(y)\},
\qquad
h_F(y)=\sup_{\varphi\in F}\{y(\varphi)-f^*(\varphi)\},
\tag{3}
\]

所以

\[
\boxed{\displaystyle
G(x)=\sup_{\varphi\in E'}\{\varphi(x)-f^*(\varphi)\}.}
\tag{4}
\]

事实上，所有一维及零维记录已经足够：

\[
G(x)=
\sup_{\varphi\in E'}
h_{\operatorname{span}\{\varphi\}}
\bigl(q_{\operatorname{span}\{\varphi\}}(x)\bigr).
\tag{5}
\]

用有限观测邻域也可直接写成

\[
G(x)=
\sup_{\substack{n\ge 0,\ \varphi_1,\ldots,\varphi_n\in E'\\
                 \varepsilon>0}}
\inf\left\{
f(z):|\varphi_i(z-x)|<\varepsilon,\ 1\le i\le n
\right\},
\tag{6}
\]

其中 \(n=0\) 时没有约束，内层下确界为 \(\inf_E f\)。

**证明。** 先说明一个下半连续包络事实。设 \(X\) 是实 Hausdorff 局部凸空间，\(p:X\to[0,+\infty]\) 凸且至少在一点有限。令

\[
C=\overline{\operatorname{epi}p}\subset X\times\mathbb R.
\]

\(C\) 是非空闭凸集，包含于 \(X\times[0,+\infty)\)，且对第二坐标向上封闭。因此每个非空竖直截面都是形如 \([a,+\infty)\) 的集合，故 \(C=\operatorname{epi}\overline p\)，其中 \(\overline p\) 是非负、下半连续、凸且至少在一点有限的函数。由于任何满足 \(v\le p\) 的下半连续函数 \(v\) 都有

\[
\operatorname{epi}p\subset\operatorname{epi}v,
\]

闭性给出 \(C\subset\operatorname{epi}v\)，即 \(v\le\overline p\)。所以 \(\overline p\) 是 \(p\) 的最大下半连续次函数；邻域公式

\[
\overline p(x)=\sup_{U\ni x}\inf_{z\in U}p(z)
\tag{7}
\]

也由此成立。

还有共轭表示

\[
\overline p(x)
=\sup_{\ell\in X'}\{\ell(x)-p^*(\ell)\},
\qquad
p^*(\ell)=\sup_{z\in X}\{\ell(z)-p(z)\}.
\tag{8}
\]

为证明它，取实数 \(t<\overline p(x)\)。点 \((x,t)\) 不属于闭凸集 \(C\)，由局部凸空间中的分离定理，存在 \(\ell\in X'\)、\(a,c\in\mathbb R\)，使

\[
\ell(x)+at<c\le \ell(z)+as
\quad\text{对所有 }(z,s)\in C.
\]

由于 \(C\) 向上无界，必有 \(a\ge0\)。若 \(a>0\)，则连续仿射函数
\(z\mapsto(c-\ell(z))/a\) 不超过 \(p\)，且在 \(x\) 处大于 \(t\)。若 \(a=0\)，则对所有 \(p(z)<+\infty\) 有 \(\ell(z)\ge c>\ell(x)\)；于是

\[
z\longmapsto n(c-\ell(z))
\]

对每个 \(n>0\) 都不超过 \(p\)，而在 \(x\) 处趋于 \(+\infty\)。因此每个 \(t<\overline p(x)\) 都能被某个不超过 \(p\) 的连续仿射函数在 \(x\) 处超过。反过来，每个这样的仿射函数都不超过 \(\overline p\)。按斜率取这些仿射次函数的上确界，就得到 (8)。同一论证还给出

\[
(\overline p)^*=p^*.
\tag{9}
\]

现在回到题设。\(q_F\) 是满射：否则它的像是 \(F^*\) 的真子空间，从而存在非零的 \(\varphi\in(F^*)^*=F\) 消去其像，即 \(\varphi(x)=0\) 对所有 \(x\in E\) 成立，矛盾。特别地，每个 \(g_F\) 都是非负、凸且至少在一点有限的函数。

若 \(F\subset K\)，则 \(q_F=r_{KF}\circ q_K\)。按 \(q_K(x)\) 的值分组取下确界，立即得到 (1)。

对 \(F^*\) 的连续对偶作自然识别 \((F^*)'=F\)。利用 \(g_F\) 的定义，对 \(\varphi\in F\) 有

\[
\sup_{y\in F^*}\{y(\varphi)-g_F(y)\}
=\sup_{x\in E}\{\varphi(x)-f(x)\}
=f^*(\varphi).
\]

将 (8) 应用于 \(p=g_F\)，即得到 (3)。

为证明 (2)，记其右边括号内的函数为 \(p\)。它是非负、凸且至少在一点有限。对 \(\varphi\in F\)，将 \(\varphi\) 视为 \(K\) 的元素，由 (9) 和上面的共轭计算，

\[
p^*(\varphi)
=h_K^*(\varphi)
=g_K^*(\varphi)
=f^*(\varphi)
=g_F^*(\varphi).
\]

对 \(p\) 和 \(g_F\) 分别使用 (8)，得到 \(\overline p=h_F\)，即 (2)。由于下半连续包络不超过原函数，还得到

\[
h_F(y)\le
\inf_{r_{KF}(z)=y}h_K(z),
\]

代入 \(y=q_F(x)\)、\(z=q_K(x)\) 即得所述单调性。

由 (3) 和每个 \(\varphi\in E'\) 都属于有限维空间 \(\operatorname{span}\{\varphi\}\)，可将构造式中的两个上确界合并为 (4)。再将 (8) 应用于原函数 \(f\)，便知 \(G=\overline f\)。因此 \(G\) 具有所要求的最大性。式 (5) 同样由 (3) 得出，而 (6) 是对各 \(h_F\) 使用邻域公式 (7) 后的展开。

特别地，(4) 表明 \(G\) 对弱拓扑 \(\sigma(E,E')\) 也下半连续。于是

\[
\operatorname{epi}G
=\overline{\operatorname{epi}f}^{\,E\times\mathbb R}
=\overline{\operatorname{epi}f}^{\,\sigma(E,E')\times\mathbb R}.
\]

式 (2) 中的下半连续包络一般不能省略。例如在 \(E=\mathbb R^2\) 上，令 \(f\) 为集合

\[
C=\{(u,v):u>0,\ v\ge 1/u\}
\]

的凸指示函数：在 \(C\) 上为 \(0\)，在其外为 \(+\infty\)。集合 \(C\) 闭且凸，所以对于 \(K=E'\) 有 \(h_K=g_K=f\)。若 \(F\) 只观测第一坐标，则 \(g_F\) 是 \((0,+\infty)\) 的指示函数，而 \(h_F\) 是 \([0,+\infty)\) 的指示函数。于是

\[
h_F(0)=0
\quad\text{但}\quad
\inf_{r_{KF}(z)=0}h_K(z)=+\infty.
\]

这也说明，即使原成本已下半连续，投影记录仍可能失去下半连续性。