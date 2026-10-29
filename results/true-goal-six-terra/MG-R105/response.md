令
\[
F=\overline{A(E)}\subseteq H,
\qquad
\overline A:Q\longrightarrow H,\quad \overline A(q(x))=Ax.
\]
若 \(q(x)=q(x')\)，则 \(x-x'\in\ker A\)，所以 \(\overline A\) 定义良好。它是线性的，且
\[
\|\overline A(q(x))\|_H=\|q(x)\|_A.
\]
因此 \(\|\cdot\|_A\) 是 \(Q\) 上的范数，\(\overline A\) 是到 \(A(E)\) 的线性等距同构。

构造完备化时，取 \(Q\) 中所有 Cauchy 序列，规定
\[
(u_n)\sim(v_n)\quad\Longleftrightarrow\quad
\|u_n-v_n\|_A\longrightarrow0.
\]
令 \(\widehat Q\) 为这些等价类构成的空间，逐项定义线性运算，并定义
\[
\|[(u_n)]\|_{\widehat Q}=\lim_{n\to\infty}\|u_n\|_A,
\qquad
\iota(u)=[(u,u,\ldots)].
\]
上述极限存在，且不依赖代表序列。定义
\[
J:\widehat Q\longrightarrow H,\qquad
J([(u_n)])=\lim_{n\to\infty}\overline A(u_n).
\]
因为 \(\overline A\) 是等距映射且 \(H\) 完备，这个极限存在并且不依赖代表序列。由范数的连续性，
\[
\|J([(u_n)])\|_H
=\lim_{n\to\infty}\|\overline A(u_n)\|_H
=\|[(u_n)]\|_{\widehat Q},
\]
所以 \(J\) 是线性等距映射，并满足 \(J\iota q=A\)。

其像恰为 **\(F=\overline{A(E)}\)**：一方面，定义中的极限都属于 \(F\)；另一方面，任取 \(h\in F\)，可选 \(u_n\in Q\) 使 \(\overline A(u_n)\to h\)。由于 \(\overline A\) 等距，\((u_n)\) 是 Cauchy 序列，且 \(J([(u_n)])=h\)。闭子空间 \(F\) 完备，故由 \(J\) 的满射等距性知 \(\widehat Q\) 完备。同时，
\[
\iota(u_n)\longrightarrow [(u_n)],
\]
所以 \(\iota(Q)\) 在 \(\widehat Q\) 中稠密。这就得到所求完备化。

对于任意固定的完备化 \((\widehat Q,\iota)\)，满足 \(J\iota q=A\) 的线性等距映射也必然唯一：若 \(J_1,J_2\) 都满足该条件，则它们在稠密集 \(\iota(q(E))=\iota(Q)\) 上相等；两者连续，因而处处相等。其存在性同样可由
\[
J(u)=\lim_{n\to\infty}\overline A(u_n)
\quad\text{其中 }\iota(u_n)\to u
\]
得到，且其像仍为 \(F\)。

现在固定 \(y\in H\)，令
\[
d=\inf_{v\in F}\|y-v\|_H.
\]
取 \(v_n\in F\) 使 \(\|y-v_n\|\to d\)。平行四边形恒等式给出
\[
\|v_n-v_m\|^2
\le 2\|y-v_n\|^2+2\|y-v_m\|^2-4d^2\longrightarrow0.
\]
故 \((v_n)\) 在闭子空间 \(F\) 中收敛到某个 \(p\)，并有 \(\|y-p\|=d\)。对任意 \(v\in F\) 和 \(t\in\mathbb R\)，极小性说明
\[
0\le \|y-p-tv\|^2-\|y-p\|^2
=t^2\|v\|^2-2t\langle y-p,v\rangle.
\]
由此 \(\langle y-p,v\rangle=0\)，即 \(y-p\in F^\perp\)。反过来，这个正交条件唯一确定 \(p\)：若 \(p'\in F\) 也满足 \(y-p'\in F^\perp\)，则 \(p-p'\in F\cap F^\perp=\{0\}\)。

记这个点为 \(P_Fy\)，并定义
\[
\boxed{R(y)=J^{-1}(P_Fy).}
\]
这里 \(J^{-1}\) 定义在 \(F\) 上。对任意 \(u\in\widehat Q\)，正交分解给出
\[
\|y-Ju\|^2
=\|y-P_Fy\|^2+\|P_Fy-Ju\|^2.
\]
因此 \(R(y)\) 是所求的唯一极小点。

由正交分解的唯一性，\(P_F\) 线性，故 \(R\) 线性；又因为
\[
\|P_Fy\|\le\|y\|,
\]
对任意 \(y,z\in H\) 有
\[
\|R(y)-R(z)\|_{\widehat Q}
=\|P_F(y-z)\|_H
\le\|y-z\|_H.
\]
所以 \(R\) 是 \(1\)-Lipschitz 的。由于 \(A(E)\) 在 \(F\) 中稠密，
\[
\boxed{\min_{u\in\widehat Q}\|y-Ju\|_H
=\|y-P_Fy\|_H
=\inf_{x\in E}\|y-Ax\|_H.}
\]

最后，上面的平方和公式表明，原空间中的最小点存在当且仅当
\[
\boxed{P_Fy\in A(E).}
\]
这也等价于 \(R(y)\in\iota(Q)\)，或 \(y\in A(E)+F^\perp\)。无论集合是否为空，都有
\[
M_y
=\{x\in E:Ax=P_Fy\}
=\{x\in E:\langle y-Ax,Az\rangle=0\ \text{对所有 }z\in E\}.
\]
若 \(M_y\ne\varnothing\)，任选 \(x_0\in E\) 满足 \(Ax_0=P_Fy\)，则其完整描述为
\[
\boxed{M_y=x_0+\ker A.}
\]

特别地，所有 \(y\in H\) 都有原空间中的最小点，当且仅当 \(A(E)\) 在 \(H\) 中闭。