记 \(f^{\circ k}\) 为 \(f\) 的 \(k\) 次迭代。全部结论为：

- \(P_f\) 能下降到 \(X\) 上，当且仅当
  \[
  C_f:=\limsup_{n\to\infty}\frac{f(n)}n<\infty.
  \]
- 对每个这样的 \(f\)，\(T_f\) 都连续、满射，最小 Lipschitz 常数为 \(C_f\)；它单射当且仅当 \(C_f=1\)，此时还是等距双射。
- 对所有 \(k\ge1\)，
  \[
  L_k=\limsup_{n\to\infty}\frac{f^{\circ k}(n)}n,\qquad
  R_f=\lim_{k\to\infty}L_k^{1/k}=\inf_{k\ge1}L_k^{1/k}.
  \]
  全部可能的有序对恰好是
  \[
  \boxed{\{(c,r):1\le r\le c<\infty\}}.
  \]

下面给出证明和构造。

**1. 下降条件与映射性质。**

对集合 \(B\subseteq\mathbb N\)，记其上密度为
\[
\overline\rho(B)=\limsup_{N\to\infty}\frac{|B\cap[1,N]|}{N}.
\]
于是 \(d(\mathbf1_B,0)=\overline\rho(B)\)。

先记录一个取样块的估计。设
\[
I_i=\{n_i,\ldots,n_i+m_i-1\},\qquad n_i+m_i\le n_{i+1},
\]
并令 \(B=\bigcup_i f(I_i)\)。当 \(f(n_i)\le N<f(n_{i+1})\) 时，
\[
|B\cap[1,N]|\le\sum_{h\le i}m_h.
\]
另一方面，\(f^{-1}(B)=\bigcup_i I_i\)。因此
\[
\overline\rho(B)\le
\limsup_i\frac{\sum_{h\le i}m_h}{f(n_i)},\qquad
\overline\rho(f^{-1}(B))\ge
\limsup_i\frac{m_i}{n_i+m_i-1}.
\tag{1}
\]

若 \(C_f=\infty\)，可依次选取 \(n_i\)，使得
\[
\frac{f(n_i)}{n_i}\longrightarrow\infty,\qquad
\frac{\sum_{h<i}n_h}{n_i}\longrightarrow0,\qquad
2n_i\le n_{i+1}.
\]
在 (1) 中取 \(m_i=n_i\)，便得
\[
\overline\rho(B)=0,\qquad
\overline\rho(f^{-1}(B))\ge\frac12.
\]
故 \(\mathbf1_B\sim0\)，但 \(P_f\mathbf1_B\not\sim0\)，不能下降到商空间。

反过来，设 \(C_f=C<\infty\)。对任意 \(x,y\in E\)，
\[
\frac1n\sum_{j=1}^n|x_{f(j)}-y_{f(j)}|
\le
\frac{f(n)}n\,
\frac1{f(n)}\sum_{m=1}^{f(n)}|x_m-y_m|.
\]
取上极限得
\[
d(P_fx,P_fy)\le C\,d(x,y).
\tag{2}
\]
这既证明了下降的良定义性，也证明了连续性以及 Lipschitz 常数至多为 \(C\)。

证明这个常数最优。固定 \(\varepsilon>0\)，选取充分稀疏的子列 \(n_i\)，使
\[
\frac{f(n_i)}{n_i}\longrightarrow C,\qquad
\frac{\sum_{h<i}n_h}{n_i}\longrightarrow0.
\]
取 \(m_i=\lfloor\varepsilon n_i\rfloor\)，并使相应块互不相交。由 (1)，
\[
d(\mathbf1_B,0)\le\frac{\varepsilon}{C},\qquad
d(P_f\mathbf1_B,0)\ge\frac{\varepsilon}{1+\varepsilon}.
\]
所以任何 Lipschitz 常数 \(K\) 都满足
\[
\frac{\varepsilon}{1+\varepsilon}
\le K\frac{\varepsilon}{C},
\]
即 \(K\ge C/(1+\varepsilon)\)。令 \(\varepsilon\downarrow0\)，结合 (2)，最小常数恰为 \(C\)。

满射性直接成立：给定 \(y\in E\)，定义
\[
x_{f(j)}=y_j,\qquad x_m=0\quad(m\notin f(\mathbb N)),
\]
则 \(x\in E\) 且 \(P_fx=y\)。

最后考察单射性。令 \(A=f(\mathbb N)\)。若 \(C>1\)，则
\[
\overline\rho(A^c)
\ge\limsup_{n\to\infty}\frac{f(n)-n}{f(n)}
=1-\frac1C>0.
\]
因此 \([\mathbf1_{A^c}]\ne[0]\)，而 \(T_f([\mathbf1_{A^c}])=[0]\)，故不单射。

若 \(C=1\)，由 \(f(n)\ge n\) 得 \(f(n)/n\to1\)。记
\[
a(N)=|A\cap[1,N]|.
\]
由 \(f(a(N))\le N<f(a(N)+1)\) 可知 \(a(N)/N\to1\)。对任意有界非负数列 \(b\)，集合
\(\{f(1),\ldots,f(N)\}\) 与 \(\{1,\ldots,N\}\) 的交集恰有 \(a(N)\) 个元素，故
\[
\left|\sum_{j=1}^N b_{f(j)}-\sum_{j=1}^N b_j\right|
\le2\|b\|_\infty\bigl(N-a(N)\bigr)=o(N).
\]
取 \(b_j=|x_j-y_j|\)，得到
\[
d(P_fx,P_fy)=d(x,y).
\]
所以此时 \(T_f\) 是等距双射。

**2. 迭代增长率及全部有序对的构造。**

对允许的 \(f\)，其每次迭代仍严格递增且满足 \(f^{\circ k}(n)=O(n)\)。又
\[
T_f^k=T_{f^{\circ k}},
\]
因此第 1 问给出
\[
L_k=\limsup_{n\to\infty}\frac{f^{\circ k}(n)}n.
\tag{3}
\]
Lipschitz 常数在复合下满足
\[
1\le L_{k+\ell}\le L_kL_\ell,\qquad L_k\le L_1^k.
\tag{4}
\]

为证明极限存在，令 \(L_0=1\)，固定 \(m\ge1\)，写 \(k=qm+s\)，其中 \(0\le s<m\)。由 (4)，
\[
L_k\le L_m^qL_s.
\]
取 \(k\) 次方根并令 \(k\to\infty\)，可得
\[
\limsup_{k\to\infty}L_k^{1/k}\le L_m^{1/m}.
\]
对 \(m\) 取下确界，再结合每个 \(L_k^{1/k}\) 都不小于该下确界，便得
\[
R_f=\lim_{k\to\infty}L_k^{1/k}
=\inf_{k\ge1}L_k^{1/k}.
\]
特别地，必有 \(1\le R_f\le L_1<\infty\)。

现在给定任意
\[
1\le r\le c<\infty,
\]
构造满足 \((L_1,R_f)=(c,r)\) 的 \(f\)。

取
\[
N_i=2^{2^i}\quad(i\ge1),\qquad
H(n)=\max\bigl(\{0\}\cup\{N_i:N_i\le n\}\bigr),
\]
并定义
\[
\boxed{\quad
f(n)=n+\left\lfloor
\max\{(r-1)n,\ (c-1)H(n)\}
\right\rfloor .
\quad}
\tag{5}
\]
取整号内的函数非减，所以 \(f\) 严格递增。令 \(\Delta=c-r\ge0\)。由于 \(H(n)\le n\)，
\[
\max\{(r-1)n,(c-1)H(n)\}
\le(r-1)n+\Delta H(n).
\]
从而
\[
rn-1\le f(n)\le rn+\Delta H(n)\le cn.
\tag{6}
\]
在 \(n=N_i\) 处，
\[
f(N_i)=N_i+\lfloor(c-1)N_i\rfloor.
\]
故 \(\limsup f(n)/n=c\)，由第 1 问，\(L_1=c\)。

剩下证明 \(R_f=r\)。记
\[
S_j=\sum_{t=0}^{j-1}r^t,\qquad S_0=0.
\]
由 (6) 的下界迭代可得
\[
f^{\circ k}(n)\ge r^k n-S_k,
\]
所以
\[
L_k\ge r^k.
\tag{7}
\]

我们再证明
\[
L_k\le r^k+\Delta S_k.
\tag{8}
\]
固定 \(k\)，令 \(z_t=f^{\circ t}(n)\)。取 \(N_i\) 为不超过 \(z_{k-1}\) 的最大构造点，并记 \(p=N_{i-1}\)；以下只考虑充分大的 \(n\)，使 \(i\ge2\)。由 (6)，
\[
N_i\le z_{k-1}\le c^{k-1}n,
\]
因此
\[
0\le\frac pn\le c^{k-1}\frac{N_{i-1}}{N_i}\longrightarrow0.
\tag{9}
\]

设 \(j\in\{0,\ldots,k-1\}\) 是首次满足 \(z_j\ge N_i\) 的时刻。在此前 \(H(z_t)\le p\)；从此直到 \(t=k-1\)，都有 \(H(z_t)\le N_i\)。应用 (6) 的上界，分别迭代得到
\[
z_j\le r^j n+\Delta pS_j,
\]
以及
\[
z_k\le r^{k-j}z_j+\Delta N_iS_{k-j}
\le\bigl(r^{k-j}+\Delta S_{k-j}\bigr)z_j,
\]
最后一步用了 \(N_i\le z_j\)。故
\[
\frac{z_k}{n}\le
\bigl(r^{k-j}+\Delta S_{k-j}\bigr)
\left(r^j+\Delta S_j\frac pn\right).
\]
结合 (9)，且 \(j\) 只有有限种取值，
\[
L_k\le
\max_{0\le j<k}\bigl(r^k+\Delta r^jS_{k-j}\bigr)
\le r^k+\Delta S_k,
\]
这里用了 \(S_k=S_j+r^jS_{k-j}\)。这证明了 (8)。

若 \(r>1\)，由 (7)—(8)，
\[
r^k\le L_k
\le r^k+(c-r)\frac{r^k-1}{r-1}
\le\left(1+\frac{c-r}{r-1}\right)r^k,
\]
取 \(k\) 次方根便得 \(R_f=r\)。

若 \(r=1\)，同样得到
\[
1\le L_k\le1+(c-1)k,
\]
故 \(R_f=1=r\)。于是 (5) 实现了每一个所需的有序对。 \(\square\)