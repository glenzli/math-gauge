记
\[
a_f=\limsup_{n\to\infty}\frac{f(n)}n.
\]
由于 \(f\) 严格递增，恒有 \(f(n)\ge n\)。第 1 问中允许的函数恰为 \(a_f<\infty\) 的函数。对每个这样的 \(f\)，\(T_f\) 都连续且满射，最小 Lipschitz 常数为 \(a_f\)，并且 \(T_f\) 单射当且仅当 \(a_f=1\)。

第 2 问中全部可能的有序对为
\[
\boxed{\{(a,b)\in\mathbb R^2:1\le b\le a<\infty\}}.
\]

## 1. 商空间上的取样映射

对任意 \(z\in E\)，由 \(f(1),\ldots,f(n)\) 互不相同可得
\[
\frac1n\sum_{j=1}^n |z_{f(j)}|
\le \frac{f(n)}n\cdot\frac1{f(n)}\sum_{i=1}^{f(n)}|z_i|.
\]
当 \(a_f<\infty\) 时，取上极限并令 \(z=x-y\)，得到
\[
d(P_fx,P_fy)\le a_f\,d(x,y).
\]
所以 \(P_f\) 保持等价关系，诱导的 \(T_f\) 是 Lipschitz 映射，且其最小 Lipschitz 常数至多为 \(a_f\)。

为证明必要性与常数的最优性，记集合 \(A\subseteq\mathbb N\) 的上密度为
\[
D^*(A)=\limsup_{N\to\infty}\frac{|A\cap[1,N]|}{N}
      =d(\mathbf 1_A,0).
\]
固定 \(0<\delta<1\)。选取递增数列 \(n_i\)，使得
\[
\frac{f(n_i)}{n_i}\longrightarrow a_f,\qquad
\sum_{h<i}n_h=o(n_i).
\]
当 \(a_f=\infty\) 时，第一个极限取 \(+\infty\)。这样的数列可从实现上极限的子列中递归选取，每次取 \(n_i>i\sum_{h<i}n_h\) 即可。令
\[
m_i=n_i+\lfloor\delta n_i\rfloor,\qquad
A=\bigcup_{i\ge1}\{f(j):n_i<j\le m_i\}.
\]
由于 \(f^{-1}(A)\) 包含每一段 \((n_i,m_i]\) 中的整数，在 \(N=m_i\) 处计算得
\[
D^*(f^{-1}(A))\ge\frac{\delta}{1+\delta}.
\]
另一方面，当 \(f(n_i)\le N<f(n_{i+1})\) 时，只有前 \(i\) 段可能对 \(A\cap[1,N]\) 有贡献，故
\[
\frac{|A\cap[1,N]|}{N}
\le \frac{\delta\sum_{h\le i}n_h}{f(n_i)}.
\]
因此 \(D^*(A)\le\delta/a_f\)，其中 \(\delta/\infty=0\)。

若 \(a_f=\infty\)，则 \(\mathbf1_A\sim0\)，而 \(P_f\mathbf1_A=\mathbf1_{f^{-1}(A)}\) 与 \(0\) 的距离为正，故 \(P_f\) 不能诱导商空间上的映射。若 \(a_f<\infty\)，对 \(T_f\) 的任何 Lipschitz 常数 \(L\)，都有
\[
\frac{\delta}{1+\delta}
\le D^*(f^{-1}(A))
\le L D^*(A)
\le L\frac{\delta}{a_f}.
\]
令 \(\delta\downarrow0\) 得 \(L\ge a_f\)，从而最小常数恰为 \(a_f\)。

**满射性。** 给定 \(y\in E\)，令 \(x_{f(j)}=y_j\)，其余位置取 \(0\)。则 \(x\in E\) 且 \(P_fx=y\)，所以 \(T_f\) 满射。

**单射性。** 令 \(C=\mathbb N\setminus f(\mathbb N)\)。若 \(a_f>1\)，则
\[
D^*(C)\ge \limsup_{n\to\infty}\frac{f(n)-n}{f(n)}
=1-\frac1{a_f}>0.
\]
于是 \([\mathbf1_C]\ne[0]\)，而 \(P_f\mathbf1_C=0\)，故 \(T_f\) 不单射。

若 \(a_f=1\)，则 \(f(n)/n\to1\)。令 \(m=|f(\mathbb N)\cap[1,N]|\)。对充分大的 \(N\)，由 \(f(m)\le N<f(m+1)\) 得 \(m/N\to1\)。对任意 \(x\in E\)，有
\[
\frac1N\sum_{j=1}^N|x_j|
\le \frac1m\sum_{j=1}^m|x_{f(j)}|
+\|x\|_\infty\left(1-\frac mN\right).
\]
所以 \(P_fx\sim0\) 蕴含 \(x\sim0\)。由线性，\(T_f\) 单射。

## 2. 迭代常数与全部可能的有序对

记 \(f^{\circ k}\) 为 \(f\) 的 \(k\) 次复合。由于 \(P_f^k=P_{f^{\circ k}}\)，第 1 问给出
\[
L_k=\limsup_{n\to\infty}\frac{f^{\circ k}(n)}n.
\]
这些常数满足 \(L_{k+\ell}\le L_kL_\ell\)，并且 \(1\le L_k\le L_1^k\)。令 \(L_0=1\)。固定 \(m\ge1\)，写 \(k=qm+s\)，其中 \(0\le s<m\)，则
\[
L_k\le L_m^q\max_{0\le s<m}L_s.
\]
取 \(k\) 次方根并令 \(k\to\infty\)，得到 \(\limsup_k L_k^{1/k}\le L_m^{1/m}\)。再对 \(m\) 取下确界，便有
\[
R_f=\lim_{k\to\infty}L_k^{1/k}
=\inf_{m\ge1}L_m^{1/m}.
\]
特别地，\(1\le R_f\le L_1<\infty\)。

现在给定任意 \(1\le b\le a<\infty\)。取分界点 \(s_i=i!\)（\(i\ge1\)），令
\[
s(n)=\max\{s_i:s_i\le n\},\qquad
f(n)=\big\lfloor bn+(a-b)s(n)\big\rfloor .
\]
因为 \(b\ge1\) 且 \((a-b)s(n)\) 单调不减，\(f\) 严格递增。又有 \(f(n)\le an\) 且 \(f(s_i)=\lfloor as_i\rfloor\)，所以 \(L_1=a\)。

为计算 \(R_f\)，先由 \(f(u)\ge bu-1\) 迭代得到
\[
f^{\circ k}(n)\ge b^k n-\sum_{j=0}^{k-1}b^j.
\]
对固定的 \(k\) 令 \(n\to\infty\)，可知 \(L_k\ge b^k\)。

对于上界，固定 \(k\)。从 \(n\) 出发的前 \(k\) 次迭代都落在 \([n,a^kn]\) 内。由于 \(s_{i+1}/s_i=i+1\to\infty\)，当 \(n\) 充分大时，这一区间至多含一个分界点。因此，\(k\) 次迭代可分成至多两段，每段内各次迭代的输入 \(u\) 都具有相同的 \(s(u)\)。

设其中一段从 \(v\) 开始，共迭代 \(t\) 次。段内 \(s(u)=s(v)\le v\)，故每一步都有 \(f(u)\le bu+(a-b)v\)。逐次代入得到
\[
f^{\circ t}(v)
\le b^t v+(a-b)v\sum_{j=0}^{t-1}b^j
\le b^t\bigl(1+(a-b)t\bigr)v.
\]
将至多两段的估计相乘，再对 \(n\) 取上极限，得到
\[
b^k\le L_k\le b^k\bigl(1+(a-b)k\bigr)^2.
\]
取 \(k\) 次方根并令 \(k\to\infty\)，即得 \(R_f=b\)。这一构造也覆盖 \(b=1\) 和 \(b=a\) 两个边界情形。