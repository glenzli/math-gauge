# 解答

记
\[
C_f:=\limsup_{n\to\infty}\frac{f(n)}n.
\]
由于 \(f\) 严格递增且取正整数值，恒有 \(f(n)\ge n\)，所以 \(C_f\in[1,+\infty]\)。

全部结论如下：

1. \(P_f\) 能在 \(X\) 上诱导映射，当且仅当 \(C_f<\infty\)。此时 \(T_f\) 总是连续、满射，其最小 Lipschitz 常数恰为 \(C_f\)；它是单射，当且仅当 \(C_f=1\)。
2. 对每个这样的 \(f\)，都有
   \[
   L_k=\limsup_{n\to\infty}\frac{f^{\circ k}(n)}n,
   \qquad
   R_f=\lim_{k\to\infty}L_k^{1/k}
       =\inf_{k\ge1}L_k^{1/k}.
   \]
   全部可能的有序对是
   \[
   \boxed{\{(c,r):1\le r\le c<\infty\}}.
   \]

以下证明这些结论并给出构造。

## 一、一个稀疏分块观察

对严格递增的 \(f\)，取正整数 \(a_\ell,m_\ell\)，使得
\(a_{\ell+1}>a_\ell+m_\ell-1\)，并设
\[
B=\bigcup_{\ell\ge1}
\{f(a_\ell),f(a_\ell+1),\ldots,f(a_\ell+m_\ell-1)\},
\qquad
S_{\ell-1}=\sum_{i<\ell}m_i.
\]
假设 \(S_{\ell-1}/f(a_\ell)\to0\)。那么
\[
\limsup_{N\to\infty}\frac{|B\cap[1,N]|}{N}
\le \limsup_{\ell\to\infty}\frac{m_\ell}{f(a_\ell)}.       \tag{1}
\]
事实上，当
\(f(a_\ell)\le N<f(a_{\ell+1})\) 时，分子至多为
\(S_{\ell-1}+m_\ell\)，分母至少为 \(f(a_\ell)\)。这直接给出 (1)。另一方面，令 \(x=\mathbf1_B\)，则
\[
\frac1{a_\ell+m_\ell-1}
\sum_{j=1}^{a_\ell+m_\ell-1}x_{f(j)}
\ge\frac{m_\ell}{a_\ell+m_\ell-1}.                       \tag{2}
\]

## 二、何时能诱导映射，以及最小 Lipschitz 常数

首先，题中的 \(d\) 是平移不变的伪距离：三角不等式来自绝对值的三角不等式以及 \(\limsup\) 的次可加性。因此零距离关系确为等价关系，且商上的 \(\bar d\) 定义良好并为距离。

### 充分性及 Lipschitz 上界

设 \(C_f=c<\infty\)。对任意 \(x,y\in E\)，有
\[
\frac1n\sum_{j=1}^n|x_{f(j)}-y_{f(j)}|
\le \frac{f(n)}n\,
\frac1{f(n)}\sum_{i=1}^{f(n)}|x_i-y_i|.
\]
取上极限得到
\[
d(P_fx,P_fy)\le c\,d(x,y).                              \tag{3}
\]
故 \(P_f\) 保持零距离关系，诱导 \(T_f\)，且 \(T_f\) 是 \(c\)-Lipschitz 的，特别地连续。

### 必要性

若 \(C_f=+\infty\)，可递归选取 \(a_\ell\to\infty\)，使
\[
\frac{f(a_\ell)}{a_\ell}\to\infty,\qquad
 a_{\ell+1}>2a_\ell,\qquad
\frac{\sum_{i<\ell}a_i}{f(a_\ell)}\to0.
\]
这是可能的，因为比值 \(f(n)/n\) 在任意尾部都无界，且 \(f(n)\to\infty\)。在上述分块观察中取 \(m_\ell=a_\ell\)。由 (1)，相应的 \(x=\mathbf1_B\) 满足 \(d(x,0)=0\)；但由 (2)，
\[
d(P_fx,0)\ge\lim_{\ell\to\infty}\frac{a_\ell}{2a_\ell-1}
=\frac12.
\]
因此 \(P_f\) 不能诱导商上的映射。

### Lipschitz 上界的最优性

仍设 \(C_f=c<\infty\)。固定任意 \(\delta>0\)，选择一个足够稀疏的子列 \(a_\ell\)，使
\[
\frac{f(a_\ell)}{a_\ell}\to c,
\qquad m_\ell=\lfloor\delta f(a_\ell)\rfloor,
\qquad a_{\ell+1}>a_\ell+m_\ell,
\qquad\frac{S_{\ell-1}}{f(a_\ell)}\to0.
\]
递归地从实现上极限的子列中取充分大的下一项，即可满足这些条件。对相应的 \(x=\mathbf1_B\)，(1)、(2) 给出
\[
d(x,0)\le\delta,
\qquad
d(P_fx,0)\ge\frac{\delta c}{1+\delta c}.
\]
若 \(K\) 是任一 Lipschitz 常数，则
\[
K\delta\ge\frac{\delta c}{1+\delta c},
\qquad K\ge\frac c{1+\delta c}.
\]
令 \(\delta\downarrow0\)，得 \(K\ge c\)。结合 (3)，最小常数正好为 \(c\)。

## 三、单射性与满射性

记 \(A=f(\mathbb N)\)。对任意 \(y\in E\)，定义
\[
x_{f(j)}=y_j,\qquad x_i=0\quad(i\notin A).
\]
则 \(x\in E\) 且 \(P_fx=y\)。因而每个允许的 \(T_f\) 都是满射。

若 \(c>1\)，取 \(x=\mathbf1_{\mathbb N\setminus A}\)。显然 \(P_fx=0\)，而
\[
d(x,0)\ge\limsup_{n\to\infty}
\frac{f(n)-n}{f(n)}=1-\frac1c>0.
\]
所以 \(T_f\) 不是单射。

若 \(c=1\)，则 \(f(n)/n\to1\)。令
\(a(N)=|A\cap[1,N]|\)。由
\(f(a(N))\le N<f(a(N)+1)\) 可得 \(a(N)/N\to1\)，即 \(A\) 的补集密度为零。
若 \(d(P_fx,0)=0\)，设 \(|x_i|\le M\)，则
\[
\frac1N\sum_{i=1}^N|x_i|
\le \frac1N\sum_{j=1}^{a(N)}|x_{f(j)}|
   +M\frac{N-a(N)}N\longrightarrow0.
\]
因此 \([P_fx]=0\) 蕴含 \([x]=0\)。由于 \(T_f\) 是线性的，它是单射。这完成第 1 问。

## 四、迭代常数及极限的存在性

有 \(P_f^k=P_{f^{\circ k}}\)，从而
\(T_f^k=T_{f^{\circ k}}\)。迭代 (3) 可知这些映射都有有限 Lipschitz 常数；也可由
\(\limsup f^{\circ k}(n)/n\le c^k\) 直接看出它们均属于第 1 问允许的情形。因此
\[
L_k=\limsup_{n\to\infty}\frac{f^{\circ k}(n)}n,
\qquad 1\le L_k\le c^k.
\]
复合映射的 Lipschitz 常数满足
\[
L_{k+\ell}\le L_kL_\ell.
\]
令 \(b_k=\log L_k\)，并令 \(b_0=0\)，则 \(b_k\) 次可加。为完整起见，固定 \(m\ge1\)，写 \(k=qm+s\)，其中 \(0\le s<m\)，有
\[
\frac{b_k}{k}\le\frac{qb_m+b_s}{k}.
\]
所以 \(\limsup b_k/k\le b_m/m\)。对 \(m\) 取下确界，并结合
\(b_k/k\ge\inf_m b_m/m\)，可知
\[
\lim_{k\to\infty}\frac{b_k}{k}=\inf_{k\ge1}\frac{b_k}{k}.
\]
指数化得到所述极限及下确界公式，且必有
\[
1\le R_f\le L_1=c<\infty.                              \tag{4}
\]

## 五、构造所有可能的有序对

给定 \(1\le r\le c<\infty\)。若 \(c=1\)，只能有 \(r=1\)，取 \(f(n)=n\) 即可。以下设 \(c>1\)。

取整数序列
\[
t_m=2^{2^m}\quad(m\ge1),
\qquad \frac{t_{m+1}}{t_m}\longrightarrow\infty.
\]
定义
\[
H(n)=\max\bigl(\{0\}\cup
       \{\lfloor(c-1)t_m\rfloor:t_m\le n\}\bigr),
\]
以及
\[
\boxed{\quad f(n)=n+\max\{\lfloor(r-1)n\rfloor,H(n)\}.\quad}       \tag{5}
\]
两个参与取最大值的函数都不减，所以 \(f\) 严格递增。此外
\[
n\le f(n)\le cn,
\qquad
\frac{f(t_m)}{t_m}\ge1+\frac{\lfloor(c-1)t_m\rfloor}{t_m}
\longrightarrow c.
\]
因此 \(C_f=c\)，并且 \(L_1=c\)。下面证明 \(R_f=r\)。

### 情形 A：\(r>1\)

由 \(f(n)\ge rn-1\)，归纳得
\[
f^{\circ k}(n)\ge r^k n-\frac{r^k-1}{r-1}.
\]
所以 \(L_k\ge r^k\)。我们再证明存在与 \(k\) 无关的常数
\[
D=1+\frac{c-1}{r-1}
\]
使得对每个 \(k\ge1\)，都有 \(L_k\le Dr^k\)。

固定 \(k\)，置 \(\alpha=(r-1)/(c-1)>0\)。由于相邻 \(t_m\) 的比值趋向无穷，当 \(n\) 充分大时，区间
\[
[\alpha n,c^k n]
\]
中至多包含一个 \(t_m\)。记 \(x_j=f^{\circ j}(n)\)，则
\(n\le x_j\le c^k n\)（\(0\le j\le k\)）。凡 \(t_m<\alpha n\)，都有
\[
\lfloor(c-1)t_m\rfloor\le\lfloor(r-1)x_j\rfloor,
\]
所以这些旧项不会超过基线项。

若上述区间没有 \(t_m\)，每一步都有 \(x_{j+1}\le rx_j\)，故 \(x_k\le r^k n\)。若区间中有唯一的 \(t=t_m\)，记 \(H_* =\lfloor(c-1)t\rfloor\)。若它直到最后都未被取样点 \(x_0,\ldots,x_{k-1}\) 越过，结论仍然相同。否则令 \(j\) 为首次满足 \(x_j\ge t\) 的指标。之前只有基线起作用，因而
\[
x_j\le r^j n,\qquad H_*\le(c-1)x_j\le(c-1)r^j n.
\]
此后没有另一个有效的新项，并且
\[
x_{i+1}\le\max\{rx_i,x_i+H_*\}\le rx_i+H_*.
\]
迭代这个不等式得
\[
\begin{aligned}
x_k
&\le r^{k-j}x_j+H_*\frac{r^{k-j}-1}{r-1}\\
&\le \left(1+\frac{c-1}{r-1}\right)r^k n
=Dr^k n.
\end{aligned}
\]
故 \(r^k\le L_k\le Dr^k\)。取 \(k\) 次方根并令 \(k\to\infty\)，得到 \(R_f=r\)。

### 情形 B：\(r=1\)

此时 (5) 化为 \(f(n)=n+H(n)\)。我们证明更精确的公式
\[
L_k=1+k(c-1)\qquad(k\ge1).                              \tag{6}
\]

先证下界。固定 \(k\)，令 \(n=t_m\)。当 \(m\) 足够大时，
\[
t_m+k\lfloor(c-1)t_m\rfloor<t_{m+1}.
\]
这 \(k\) 次迭代都停留在同一段常值区间内，所以
\[
f^{\circ k}(t_m)=t_m+k\lfloor(c-1)t_m\rfloor.
\]
令 \(m\to\infty\) 得到 \(L_k\ge1+k(c-1)\)。

再证上界。固定 \(k\)，对充分大的 \(n\)，区间 \((n,c^k n]\) 至多含一个跳点 \(t_m\)。仍记 \(x_j=f^{\circ j}(n)\)。若迭代所使用的点 \(x_0,\ldots,x_{k-1}\) 没有越过新的跳点，则每次增量为 \(H(n)\le(c-1)n\)，故
\[
x_k\le[1+k(c-1)]n.
\]
否则，设被越过的唯一新跳点为 \(t_m>n\)，首次越过时为 \(x_j\ge t_m\)，其中 \(1\le j\le k-1\)。越过之前每次增量至多为 \((c-1)t_{m-1}\)，从而
\[
t_m\le x_j\le n+k(c-1)t_{m-1}.
\]
又因 \(t_m\le c^k n\)，有
\[
0\le\frac{t_{m-1}}n\le c^k\frac{t_{m-1}}{t_m}\longrightarrow0
\]
（在这类 \(n\to\infty\) 的情形下必有 \(m\to\infty\)）。于是 \(t_m/n\le1+o(1)\)。所有 \(k\) 次增量均至多为 \((c-1)t_m\)，故
\[
\frac{x_k}{n}\le1+k(c-1)\frac{t_m}{n}
\le1+k(c-1)+o(1).
\]
这给出 (6) 的上界。因此
\[
R_f=\lim_{k\to\infty}[1+k(c-1)]^{1/k}=1=r.
\]

构造 (5) 因而实现了每一对 \(1\le r\le c<\infty\)。结合必要条件 (4)，所列有序对恰好是全部可能情形。\(\square\)
