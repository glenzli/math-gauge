令 \(C_f=\limsup_{n\to\infty}f(n)/n\)。则 \(P_f\) 能诱导 \(X\) 上的映射当且仅当 \(C_f<\infty\)。此时 \(T_f\) 连续且满射，最小 Lipschitz 常数为 \(C_f\)，并且 \(T_f\) 是单射当且仅当 \(C_f=1\)。

第 2 问中全部可能的有序对为
\[
\boxed{\bigl\{(C,r)\in\mathbb R^2:1\le r\le C<\infty\bigr\}.}
\]

## 1. 取样映射何时能下降到商空间

记
\[
p(x)=\limsup_{M\to\infty}\frac1M\sum_{m=1}^M|x_m|.
\]
这是 \(E\) 上的半范数，且 \(\bar d([x],[y])=p(x-y)\)。由于 \(P_f\) 线性，它能诱导商空间上的映射当且仅当 \(p(x)=0\) 蕴含 \(p(P_fx)=0\)。

若 \(C_f<\infty\)，由 \(f\) 严格递增可得
\[
\frac1n\sum_{j=1}^n|x_{f(j)}|
\le
\frac{f(n)}n\cdot\frac1{f(n)}\sum_{m=1}^{f(n)}|x_m|.
\]
取上极限，得到 \(p(P_fx)\le C_f p(x)\)。因此 \(T_f\) 良定义且连续，其最小 Lipschitz 常数至多为 \(C_f\)。

下面用同一个构造证明这个上界最优，并排除 \(C_f=\infty\) 的情形。固定 \(0<\varepsilon\le1\)，选取趋于无穷的整数 \(n_i\)，令 \(\ell_i=\lfloor\varepsilon n_i\rfloor\)，使得
\[
\frac{f(n_i)}{n_i}\longrightarrow C_f,\qquad
n_{i+1}>n_i+\ell_i,\qquad
\frac{\sum_{h<i}\ell_h}{n_i}\longrightarrow0.
\]
这样的选取总是可行，因为可从实现上极限的子列中，每次选取足够大的 \(n_i\)。令 \(x\) 为集合
\[
\bigcup_{i\ge1}\{f(n_i+1),\ldots,f(n_i+\ell_i)\}
\]
的示性数列。在取样后的第 \(n_i+\ell_i\) 项处，前缀中至少有 \(\ell_i\) 个 \(1\)，所以
\[
p(P_fx)\ge \lim_{i\to\infty}\frac{\ell_i}{n_i+\ell_i}
=\frac{\varepsilon}{1+\varepsilon}.
\]
另一方面，若 \(f(n_i)\le M<f(n_{i+1})\)，则
\[
\frac1M\sum_{m=1}^M x_m
\le \frac{\sum_{h\le i}\ell_h}{f(n_i)}.
\]
右端趋于 \(\varepsilon/C_f\)，其中 \(C_f=\infty\) 时该值为 \(0\)。因此 \(p(x)\le \varepsilon/C_f\)。若 \(C_f=\infty\)，就有 \(p(x)=0\) 而 \(p(P_fx)>0\)，故映射不能下降到商空间。若 \(C_f<\infty\)，任何 Lipschitz 常数 \(K\) 都满足
\[
\frac{\varepsilon}{1+\varepsilon}\le Kp(x)\le K\frac{\varepsilon}{C_f}.
\]
令 \(\varepsilon\downarrow0\)，得到 \(K\ge C_f\)。

对每个允许的 \(f\)，任给 \(y\in E\)，令 \(x_{f(j)}=y_j\)，并在 \(f(\mathbb N)\) 之外令 \(x_m=0\)。则 \(x\in E\) 且 \(P_fx=y\)，所以 \(T_f\) 满射。

再令 \(S=f(\mathbb N)\)。若 \(C_f>1\)，则 \(S^c=\mathbb N\setminus S\) 的示性数列满足
\[
p(\mathbf 1_{S^c})\ge
\limsup_{n\to\infty}\frac{f(n)-n}{f(n)}
=1-\frac1{C_f}>0,
\qquad P_f\mathbf 1_{S^c}=0.
\]
故 \(T_f\) 不是单射。若 \(C_f=1\)，由于 \(f(n)\ge n\)，有 \(f(n)/n\to1\)。记 \(m=m(M)=\#(S\cap\{1,\ldots,M\})\)。对充分大的 \(M\)，有 \(f(m)\le M<f(m+1)\)，从而 \(m/M\to1\)。若 \(p(P_fx)=0\)，则
\[
\frac1M\sum_{i=1}^M|x_i|
\le
\frac{m}{M}\cdot\frac1m\sum_{j=1}^m |x_{f(j)}|
+\left(1-\frac mM\right)\|x\|_\infty
\longrightarrow0.
\]
因此 \(p(x)=0\)。这说明线性映射 \(T_f\) 的核为零，故它是单射。

## 2. 迭代的增长率与构造

用 \(f^{\circ k}\) 表示 \(f\) 的 \(k\) 次复合。由 \(T_f^k=T_{f^{\circ k}}\) 和第 1 问，
\[
L_k=\limsup_{n\to\infty}\frac{f^{\circ k}(n)}n.
\]
复合映射的 Lipschitz 常数满足 \(L_{k+h}\le L_kL_h\)，且 \(1\le L_k\le L_1^k\)。令 \(L_0=1\)。固定 \(m\ge1\)，写 \(k=qm+s\)，其中 \(0\le s<m\)。由 \(L_k\le L_m^q L_s\) 得
\[
\limsup_{k\to\infty} L_k^{1/k}\le L_m^{1/m}.
\]
对 \(m\) 取下确界，并注意每个 \(L_k^{1/k}\) 都至少为这个下确界，可得
\[
R_f=\lim_{k\to\infty}L_k^{1/k}=\inf_{m\ge1}L_m^{1/m}.
\]
特别地，\(1\le R_f\le L_1\)。

现在任取 \(1\le r\le C<\infty\)。令 \(a=C-1\)，取 \(N_i=2^{i^2}\)（\(i\ge0\)），并令 \(N(n)=\max\{N_i:N_i\le n\}\)。定义
\[
f(n)=\max\bigl\{\lfloor rn\rfloor,\ n+\lfloor aN(n)\rfloor\bigr\}.
\]
两个取最大值的项每步都至少增加 \(1\)，所以 \(f\) 严格递增。又有 \(n\le f(n)\le Cn\)，且 \(f(N_i)=\lfloor C N_i\rfloor\)，故 \(L_1=C\)。

由 \(f(n)\ge rn-1\)，对每个固定的 \(k\) 迭代可得
\[
f^{\circ k}(n)\ge r^k n-\sum_{j=0}^{k-1}r^j.
\]
因此 \(L_k\ge r^k\)。

为证明反向的增长率上界，固定 \(k\)。由于 \(N_{i+1}/N_i\to\infty\)，当 \(n\) 充分大时，区间 \([n,C^kn]\) 至多包含一个 \(N_i\)。而从 \(n\) 开始的前 \(k\) 步迭代都落在这个区间内，轨道单调不减。因此这 \(k\) 步可以分成至多两段，每段各步的输入具有相同的 \(N(\cdot)\) 值。

考虑其中一段，设起点为 \(u\)，共 \(t\) 步，共同的 \(N(\cdot)\) 值为 \(N\le u\)。对于该段每一步的输入 \(v\)，有
\[
f(v)\le rv+au.
\]
所以该段的终点至多为
\[
\left(r^t+a\sum_{j=0}^{t-1}r^j\right)u
\le (1+at)r^t u.
\]
将至多两段的放大倍数相乘，得到
\[
f^{\circ k}(n)\le (1+ak)^2 r^k n
\]
对充分大的 \(n\) 成立。故 \(r^k\le L_k\le (1+ak)^2r^k\)。取 \(k\) 次方根再令 \(k\to\infty\)，得到 \(R_f=r\)，从而实现了所给的每一对 \((C,r)\)。