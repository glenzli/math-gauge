# 证明

命题成立。先说明所用集合与商都是良定义的。由于每个算子都把 $\bot$ 映到 $\bot$，从 $x\in U_0\subseteq\operatorname{dom}(c)$ 可知，在 $x$ 上的每一个中间像都不是 $\bot$；否则其后的像以及 $c(x)$ 都会是 $\bot$。因此各 $U_m$ 非空，且对 $m=2,\ldots,k$ 有 $U_{m-1}\subseteq\operatorname{dom}(\varphi_m)$。题设的各上界证书确实可用于相应的中间像。

关系 $E_r$ 是 $U_0$ 上的等价关系：长度为零的序列给出自反性；利用 $d_i$ 的对称性反转序列得到对称性；连接两个有限序列得到传递性。关系 $\approx_J$ 是 $U_k$ 上的等价关系：自反性与对称性直接来自各 $d_j$，而若 $z\approx_J z'$、$z'\approx_J z''$，对每个 $j\in J$，三角不等式给出
\[
d_j(z,z'')\le d_j(z,z')+d_j(z',z'')=0,
\]
故 $z\approx_J z''$。所以两个商集及其商映射均良定义。

下面证明 $c$ 把每个 $E_r$ 类送入一个 $\approx_J$ 类。先考虑满足 $d_i(x,y)<r$ 的 $x,y\in U_0$。若 $l\in S$，则由 $r\le\rho\le n_l\le r_l(y)$，以及 $d_i(x,y)<r$，可从 $r_l(y)$ 的上确界定义找到一个有限正数 $t>d_i(x,y)$，它属于定义该上确界的集合。这里即使 $r_l(y)=+\infty$，同样可以找到这样的有限 $t$。于是
\[
d_l\bigl(\varphi_1(x),\varphi_1(y)\bigr)=0
\qquad(l\in S).
\tag{1}
\]
当 $S=\varnothing$ 时，此结论按空集约定自然成立。

记
\[
a_l=d_l\bigl(\varphi_1(x),\varphi_1(y)\bigr).
\]
逐次应用上界证书，得到对每个 $j\in I$，
\[
d_j(c(x),c(y))\le\sum_{l\in I}P_{jl}a_l.
\tag{2}
\]
具体而言，$k\ge2$ 时，对 $m=2,\ldots,k$ 依次使用证书，并利用扩展非负数乘法的单调性和对有限和的分配律，即得到矩阵乘积 $L^{(m)}\cdots L^{(2)}$；题设约定 $0\cdot\infty=0$ 也适用于这些运算。$k=1$ 时 $P$ 为单位矩阵，(2) 事实上为等式，包括距离为无穷的情况。

固定 $j\in J$。若 $P_{jl}>0$，由 $S$ 的定义有 $l\in S$，因此由 (1) 得 $a_l=0$，从而 $P_{jl}a_l=0$，即使 $P_{jl}=+\infty$ 也如此。若 $P_{jl}=0$，则按题设约定同样有 $P_{jl}a_l=0$，即使 $a_l=+\infty$ 也如此。故 (2) 的右端为零，因而
\[
d_j(c(x),c(y))=0\qquad(j\in J).
\]
这也涵盖 $S=\varnothing$ 的情况：此时每个 $j\in J$、$l\in I$ 都有 $P_{jl}=0$。

若 $xE_ry$，取定义中的有限序列 $x=x_0,\ldots,x_n=y$。上述结论适用于序列中的每一对相邻元素；再逐次使用 $d_j$ 的三角不等式，得到对每个 $j\in J$ 都有 $d_j(c(x),c(y))=0$。$n=0$ 时这由自距为零直接成立。因此
\[
xE_ry\quad\Longrightarrow\quad c(x)\approx_J c(y).
\tag{3}
\]

由 (3)，可定义
\[
F_r([x]_{E_r})=[c(x)]_{\approx_J}\qquad(x\in U_0),
\]
且该定义与代表元的选取无关。它满足 $F_r\circ q_r=q_J\circ c$。每个 $z\in U_k$ 都有 $z=c(x)$ 对某个 $x\in U_0$ 成立，所以 $F_r$ 是满射。若另一映射满足同一复合式，则它在每个 $[x]_{E_r}=q_r(x)$ 上的值都必须是 $q_J(c(x))$，因而与 $F_r$ 相同。这证明了存在性、满射性和唯一性。

最后证明覆盖数界。若 $H_r=\infty$，则 $N_J(U_k,\varepsilon)\le\infty=H_r$ 直接成立。若 $H_r<\infty$，对每个 $E_r$ 类选一个代表元 $x_a$，并令中心 $v_a=c(x_a)\in U_k$。任取 $z\in U_k$，写为 $z=c(x)$，取 $x$ 所在类的代表元 $x_a$；由 (3)，
\[
d_j(z,v_a)=0\qquad(j\in J).
\]
因为 $J$ 是有限非空集，$\max_{j\in J}d_j(z,v_a)=0<\varepsilon$。这 $H_r$ 个中心因而覆盖 $U_k$，故对每个有限 $\varepsilon>0$，
\[
N_J(U_k,\varepsilon)\le H_r.
\]
证毕。
