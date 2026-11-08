记
\[
D(A)=\limsup_{N\to\infty}\frac{|A\cap[1,N]|}{N},
\qquad
C_f=\limsup_{n\to\infty}\frac{f(n)}n\in[1,+\infty].
\]

结论是：

- \(P_f\) 能诱导 \(X\) 上的映射，当且仅当 \(C_f<\infty\)，也就是 \(f(n)=O(n)\)。
- 对每个这样的 \(f\)，\(T_f\) 连续、满射，且最小 Lipschitz 常数为
  \[
  L_1=C_f.
  \]
  它单射当且仅当 \(D(\mathbb N\setminus f(\mathbb N))=0\)，等价于 \(f(n)/n\to1\)，也等价于 \(L_1=1\)。
- 第二问中全部可能的有序对恰为
  \[
  \boxed{\{(L,R):1\le R\le L<\infty\}.}
  \]

下面证明这些结论并给出构造。

## 一、下降到商空间及映射的性质

对有界数列 \(x\)，写
\[
\|[x]\|=\limsup_{N\to\infty}\frac1N\sum_{j=1}^N|x_j|.
\]
这是商空间 \(X\) 上的范数，且 \(\bar d([x],[y])=\|[x-y]\|\)。

### 下降条件

先设 \(C_f<\infty\)。对每个 \(n\)，由于 \(f\) 严格递增，
\[
\frac1n\sum_{j=1}^n|x_{f(j)}|
\le
\frac{f(n)}n
\left(\frac1{f(n)}\sum_{m=1}^{f(n)}|x_m|\right).
\]
取上极限得到
\[
\|[P_fx]\|\le C_f\|[x]\|. \tag{1}
\]
因此零范数数列经 \(P_f\) 后仍为零范数，\(T_f\) 良定义并连续，其 Lipschitz 常数至多为 \(C_f\)。

反之，设 \(C_f=\infty\)。递归选取趋于无穷的整数 \(n_i\)，使
\[
\frac{f(n_i)}{n_i}\ge i,\qquad
n_i>2n_{i-1},\qquad
\sum_{h<i}n_h\le n_i.
\]
这样的选择是可能的，因为 \(f(n)/n\) 无上界。令
\[
A=\bigcup_{i\ge1}\{f(j):n_i<j\le 2n_i\}.
\]
若第 \(i\) 块是 \(A\) 中与 \([1,N]\) 相交的最后一块，则 \(N\ge f(n_i)\)，故
\[
|A\cap[1,N]|
\le \sum_{h\le i}n_h
\le 2n_i
\le \frac{2N}{i}.
\]
当 \(N\to\infty\) 时，相应的 \(i\to\infty\)，所以 \(D(A)=0\)。但对每个 \(i\)，
\[
\frac1{2n_i}\sum_{j=1}^{2n_i}\mathbf 1_A(f(j))
\ge\frac12.
\]
于是 \(\mathbf1_A\sim0\)，但 \(P_f\mathbf1_A\not\sim0\)。因此 \(P_f\) 不能下降到商空间。这证明了所述下降条件。

### 最小 Lipschitz 常数

下面设 \(C=C_f<\infty\)。式 (1) 已给出上界。为证明这个上界最优，任取 \(0<\delta<C\) 和 \(\varepsilon>0\)，选取整数 \(n_i\to\infty\)，使
\[
\frac{f(n_i)}{n_i}\ge C-\delta,
\]
并使区间
\[
(n_i,n_i+\lceil\varepsilon n_i\rceil]
\]
两两不交，同时满足
\[
\frac{\sum_{h<i}\lceil\varepsilon n_h\rceil}{f(n_i)}\longrightarrow0.
\]
这可逐次选取，因为满足第一条不等式的 \(n\) 有无穷多个。

令
\[
A=\bigcup_i
\{f(j):n_i<j\le n_i+\lceil\varepsilon n_i\rceil\}.
\]
在第 \(i\) 块开始之后、下一块开始之前，分母至少为 \(f(n_i)\)，而已选元素数至多为
\[
\sum_{h<i}\lceil\varepsilon n_h\rceil+
\lceil\varepsilon n_i\rceil.
\]
因此
\[
D(A)\le \frac{\varepsilon}{C-\delta}.
\]
另一方面，在取样长度 \(n_i+\lceil\varepsilon n_i\rceil\) 处，
\[
\|[P_f\mathbf1_A]\|
\ge \frac{\varepsilon}{1+\varepsilon}.
\]
于是任何 Lipschitz 常数都至少为
\[
\frac{\varepsilon/(1+\varepsilon)}
     {\varepsilon/(C-\delta)}
=\frac{C-\delta}{1+\varepsilon}.
\]
先令 \(\delta\downarrow0\)，再令 \(\varepsilon\downarrow0\)，得到下界 \(C\)。所以
\[
\boxed{L_1=C_f.} \tag{2}
\]

### 满射和单射

满射性对任意严格递增的 \(f\) 都成立：给定有界数列 \(y\)，令
\[
x_{f(j)}=y_j,\qquad
x_m=0\quad(m\notin f(\mathbb N)).
\]
则 \(P_fx=y\)。

令 \(B=\mathbb N\setminus f(\mathbb N)\)。若 \(D(B)>0\)，则 \([\mathbf1_B]\ne0\)，但 \(T_f[\mathbf1_B]=0\)，所以 \(T_f\) 非单射。

若 \(D(B)=0\) 且 \(T_f[x]=0\)，则
\[
\frac1N\sum_{m=1}^N|x_m|
\le
\frac1N\sum_{j=1}^N|x_{f(j)}|
+\|x\|_\infty\frac{|B\cap[1,N]|}{N}.
\]
取上极限可得 \([x]=0\)，所以 \(T_f\) 单射。

最后，\(D(B)=0\) 等价于 \(f(n)/n\to1\)。确实，前者意味着
\[
\frac{n}{f(n)}
=\frac{|f(\mathbb N)\cap[1,f(n)]|}{f(n)}
\longrightarrow1.
\]
反之，若 \(f(n)/n\to1\)，对 \(f(n)\le N<f(n+1)\) 有
\[
1\ge\frac{|f(\mathbb N)\cap[1,N]|}{N}
=\frac nN
\ge\frac{n}{f(n+1)}\longrightarrow1.
\]
又因为 \(f(n)\ge n\)，这也等价于 \(C_f=1\)。结合 (2)，单射恰在 \(L_1=1\) 时成立。

## 二、迭代增长率与全部可能的有序对

对允许的 \(f\)，由第一问应用于 \(f^k\)，
\[
L_k=\limsup_{n\to\infty}\frac{f^k(n)}n.
\]
每个 \(L_k\) 有限且至少为 \(1\)。算子范数的次乘性给出
\[
L_{k+\ell}\le L_kL_\ell.
\]
因此 \(\log L_k\) 是次可加数列。由次可加引理，
\[
\lim_{k\to\infty}\frac{\log L_k}{k}
=\inf_{k\ge1}\frac{\log L_k}{k}.
\]
从而 \(R_f=\lim_kL_k^{1/k}\) 存在，并且
\[
1\le R_f\le L_1<\infty. \tag{3}
\]

下面构造所有满足 (3) 的有序对。

任取实数
\[
1\le r\le L<\infty.
\]
取严格递增整数列 \(N_i\)，使 \(N_{i-1}/N_i\to0\)，例如 \(N_i=2^{2^i}\)。定义
\[
b(n)=\max\bigl(\{0\}\cup
\{\lceil(L-1)N_i\rceil:N_i\le n\}\bigr),
\]
并令
\[
f(n)=\max\{\lceil rn\rceil,\ n+b(n)\}. \tag{4}
\]
两个取最大值的项均严格递增，故 \(f\) 严格递增。对 \(N_i\le n<N_{i+1}\)，
\[
b(n)=\lceil(L-1)N_i\rceil,
\]
因此
\[
\frac{f(n)}n\le L+\frac1n.
\]
而在 \(n=N_i\) 时，
\[
\frac{f(N_i)}{N_i}\ge
1+\frac{\lceil(L-1)N_i\rceil}{N_i}\longrightarrow L.
\]
故 \(L_1=L\)。

接下来证明这个构造满足 \(R_f=r\)。由 \(f(n)\ge rn\)，
\[
L_k\ge r^k. \tag{5}
\]
另一方面，我们证明对每个固定的 \(k\)，
\[
L_k\le r^k+k(L-1)r^{k-1}. \tag{6}
\]

为此，固定 \(k\)，写 \(u_j=f^j(n)\)。由 (4)，对某个与 \(n\) 无关的常数 \(C\)，有 \(f(m)\le Cm\)，所以 \(u_j\le C^kn\)（\(0\le j\le k\)）。

令 \(H=N_i\) 为不超过 \(u_{k-1}\) 的最大构造点，并分两种情况：

- 若 \(H\le n\)，令 \(s=0\)。此后各步都有
  \[
  b(u_j)\le (L-1)n+1.
  \]
- 若 \(H>n\)，令 \(s\le k-1\) 为首次满足 \(u_s\ge H\) 的指标。在此之前，\(b(u_j)\le (L-1)N_{i-1}+1=o(n)\)：这是因为
  \[
  \frac{N_{i-1}}n
  \le C^k\frac{N_{i-1}}{N_i}\longrightarrow0.
  \]
  利用 \(f(m)\le rm+b(m)+1\) 递推，得到
  \[
  u_s\le r^s n+o(n).
  \]
  从第 \(s\) 步起，\(b(u_j)\le(L-1)H+1\le(L-1)u_s+1\)。

两种情况下都可取相应的 \(s\)，使越过 \(H\) 之前的附加项为 \(o(n)\)，而之后的附加项至多为
\[
(L-1)r^s n+o(n).
\]
展开递推 \(u_{j+1}\le ru_j+b(u_j)+1\)，便有
\[
\frac{u_k}{n}
\le r^k+(L-1)r^s\sum_{j=s}^{k-1}r^{k-1-j}+o(1)
\le r^k+k(L-1)r^{k-1}+o(1).
\]
取上极限即得 (6)。

由 (5)、(6)，
\[
r\le R_f
\le\lim_{k\to\infty}
\left(r^k+k(L-1)r^{k-1}\right)^{1/k}
=r.
\]
所以 \(R_f=r\)。这就对每个 \(1\le r\le L<\infty\) 构造出了所需的严格递增函数，完成证明。