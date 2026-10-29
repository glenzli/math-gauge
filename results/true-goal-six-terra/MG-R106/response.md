这些观测确实唯一确定所求的映射 \(F\)。而且，延拓族在每个紧集上一致收敛，所述同步改变输入的结论也成立。

先对每个 \(d\in D\) 构造观测极限。Cauchy 滤子条件表明，对每个正整数 \(n\)，存在 \(A_n\in\mathcal F\)，使得
\[
d_Y(f_i(d),f_j(d))<\frac1n
\qquad(i,j\in A_n).
\]
由于 \(\mathcal F\) 是真滤子，每个有限交集非空；在 ZFC 中可取
\[
i_n\in\bigcap_{k=1}^n A_k.
\]
于是 \((f_{i_n}(d))\) 是 Cauchy 列。由 \(Y\) 的完备性，它收敛到某个 \(g(d)\in Y\)。若 \(i\in A_n\)，令 \(m\to\infty\) 可得
\[
d_Y(f_i(d),g(d))\leq \frac1n.
\]
因此 \(f_i(d)\to g(d)\) 沿 \(\mathcal F\)。真滤子在度量空间中的极限唯一，所以 \(g(d)\) 由观测唯一确定。

对任意 \(d,e\in D\) 和 \(\eta>0\)，下列两个集合都属于 \(\mathcal F\)：
\[
\{i:d_Y(f_i(d),g(d))<\eta\},\qquad
\{i:d_Y(f_i(e),g(e))<\eta\}.
\]
它们的交集非空。取其中一个 \(i\)，便有
\[
d_Y(g(d),g(e))
<2\eta+K d_X(d,e).
\]
令 \(\eta\downarrow0\)，得到
\[
d_Y(g(d),g(e))\leq Kd_X(d,e).
\]
所以 \(g:D\to Y\) 是 \(K\)-Lipschitz 映射。

接下来使用标准的稠密集延拓构造：若 \(E\) 稠密于度量空间 \(Z\)，且 \(h:E\to Y\) 为 \(K\)-Lipschitz，则对 \(z\in Z\) 取任意满足 \(e_n\to z\) 的 \(E\) 中序列，定义
\[
\overline h(z)=\lim_{n\to\infty}h(e_n).
\]
Lipschitz 条件和 \(Y\) 的完备性保证极限存在；同一条件也保证它与序列的选取无关。逐点取极限可知 \(\overline h\) 仍为 \(K\)-Lipschitz。由于 Lipschitz 映射连续，这样的延拓由稠密性唯一确定。

这里 \(\iota(D)\) 稠密于 \(\widehat X\)。将上述构造用于
\[
\iota(d)\longmapsto g(d)
\]
便得到唯一的 \(K\)-Lipschitz 映射 \(F:\widehat X\to Y\)，满足
\[
F(\iota d)=g(d),\qquad d\in D.
\]
因而它满足题设中的观测收敛。任何其他满足该收敛条件的 \(K\)-Lipschitz 映射，都必须在 \(\iota(D)\) 上与 \(F\) 相同，故处处相同。

同样，对每个 \(i\in I\)，将 \(\iota(x)\mapsto f_i(x)\) 从稠密集 \(\iota(X)\) 延拓，得到唯一的 \(K\)-Lipschitz 映射
\[
\widehat f_i:\widehat X\to Y,
\qquad
\widehat f_i(\iota x)=f_i(x).
\]

现在证明紧集上一致收敛。设 \(C\subset\widehat X\) 紧，给定 \(\varepsilon>0\)，取
\[
\delta=\frac{\varepsilon}{3(1+K)}.
\]
由 \(\iota(D)\) 的稠密性和 \(C\) 的紧性，可取有限多个 \(d_1,\ldots,d_m\in D\)，使得
\[
C\subset\bigcup_{j=1}^m B(\iota d_j,\delta).
\]
对每个 \(j\)，观测收敛给出
\[
A_j=\left\{i:
d_Y\bigl(f_i(d_j),F(\iota d_j)\bigr)<\frac{\varepsilon}{3}
\right\}\in\mathcal F.
\]
于是 \(A=\bigcap_{j=1}^m A_j\in\mathcal F\)。对 \(i\in A\) 和任意 \(z\in C\)，选择满足 \(d_{\widehat X}(z,\iota d_j)<\delta\) 的 \(j\)，有
\[
\begin{aligned}
d_Y(\widehat f_i(z),F(z))
&\leq Kd_{\widehat X}(z,\iota d_j)
 +d_Y\bigl(f_i(d_j),F(\iota d_j)\bigr)
 +Kd_{\widehat X}(z,\iota d_j)\\
&<2K\delta+\frac{\varepsilon}{3}<\varepsilon.
\end{aligned}
\]
因此
\[
\left\{i:\forall z\in C,\ 
d_Y(\widehat f_i(z),F(z))<\varepsilon\right\}\in\mathcal F,
\]
这正是所求的一致收敛。空集的情形显然成立。特别地，取 \(C=\{a\}\)，可知对每个 \(a\in\widehat X\)，
\[
\widehat f_i(a)\longrightarrow F(a)\quad\text{沿 }\mathcal F.
\]

最后，若 \(u:I\to\widehat X\) 且 \(u\to a\) 沿 \(\mathcal F\)，则
\[
d_Y(\widehat f_i(u(i)),F(a))
\leq Kd_{\widehat X}(u(i),a)
   +d_Y(\widehat f_i(a),F(a)).
\]
右侧两项都沿 \(\mathcal F\) 趋于零，故
\[
\boxed{\ \widehat f_i(u(i))\longrightarrow F(a)
\quad\text{沿 }\mathcal F.\ }
\]

实际上，上述有限覆盖证明也适用于任意全有界子集。不过，一般不能要求在整个 \(\widehat X\) 上一致收敛：例如取 \(X=Y=\mathbb R\)、\(D=\mathbb Q\)、余有限滤子及 \(f_n(x)=x/n\)，所得 \(F\equiv0\)，但收敛不在 \(\mathbb R\) 上一致。