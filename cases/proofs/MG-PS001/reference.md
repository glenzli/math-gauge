# 序列空间上的取样映射：参考证明

这是一份非形式化数学证明，不声称已有人工或 Lean 验证。题面中的空间不假设完备。以下所有极限、集合与构造均在题面给定的有界实数列空间内。

## 结论

记
\[
C(f)=\limsup_{n\to\infty}\frac{f(n)}n\in[1,+\infty].
\]

取样映射能够下降到零距商，当且仅当 \(C(f)<\infty\)。此时它是满射的线性 Lipschitz 映射，最小 Lipschitz 常数恰为 \(C(f)\)。它是单射当且仅当 \(C(f)=1\)；在这一情形它是满射等距映射。

对允许的 \(f\)，
\[
L_k=C(f^{\circ k}),\qquad R_f=\inf_{k\ge1}L_k^{1/k}.
\]
全部可能的有序对恰为
\[
\{(C,r):1\le r\le C<\infty\}.
\]

## 1. 伪度量及商

令
\[
p(x)=\limsup_{N\to\infty}\frac1N\sum_{j=1}^{N}|x_j|.
\]
它有限、绝对齐次，逐点三角不等式及 limsup 的次可加性给出 \(p(x+y)\le p(x)+p(y)\)。因此 \(d(x,y)=p(x-y)\) 是伪度量，零集 \(Z=\{x:p(x)=0\}\) 是线性子空间。若两代表相差零半范数，则反三角不等式保证它们具有相同半范数，故 \(p\) 在 \(E/Z\) 上给出范数，诱导距离正是 \(\bar d\)。

对集合 \(A\subseteq\mathbb N\)，记其上密度为
\[
\overline\delta(A)=\limsup_{M\to\infty}\frac{|A\cap\{1,\ldots,M\}|}{M}.
\]
于是 \(p(\mathbf1_A)=\overline\delta(A)\)。严格递增性给出 \(f(n)\ge n\)，特别地 \(C(f)\ge1\)。

## 2. 有限增长率足以下降，并给出上界

若 \(C=C(f)<\infty\)，则对任意有界数列 \(x\)，
\[
\frac1n\sum_{j=1}^{n}|x_{f(j)}|
\le\frac{f(n)}n\frac1{f(n)}\sum_{i=1}^{f(n)}|x_i|.
\]
因 \(f(n)\to\infty\)，取 limsup 得
\[
p(P_fx)\le C p(x).
\]
这既证明 \(P_f(Z)\subseteq Z\)，也证明诱导线性映射的 Lipschitz 常数至多 \(C\)。

## 3. 无界增长率不允许下降

设 \(C(f)=\infty\)。递归选取整数 \(n_j\to\infty\)，使
\[
f(n_j)\ge j n_j,\qquad n_j>2n_{j-1},\qquad
\sum_{i<j}(n_i+1)\le n_j/j.
\]
无界 limsup 保证在任意大的位置仍能选择满足第一式的整数，故全部条件可同时满足。

置
\[
A_j=\{f(n_j),f(n_j+1),\ldots,f(2n_j)\},\qquad A=\bigcup_j A_j.
\]
若 \(f(n_j)\le M<f(n_{j+1})\)，则
\[
|A\cap[1,M]|\le\sum_{i<j}(n_i+1)+(n_j+1),
\]
从而
\[
\frac{|A\cap[1,M]|}{M}
\le\frac{n_j/j+n_j+1}{j n_j}\longrightarrow0.
\]
这覆盖所有充分大的 \(M\)，故 \(p(\mathbf1_A)=0\)。另一方面，\(P_f\mathbf1_A\) 在全部指标 \(n_j,\ldots,2n_j\) 上取值 1，因此
\[
p(P_f\mathbf1_A)\ge\limsup_j\frac{n_j+1}{2n_j}=\frac12.
\]
零数列与 \(\mathbf1_A\) 属于同一零距类，而它们的取样结果不属于同一零距类。因此取样不能下降。

## 4. Lipschitz 上界是最优的

若 \(C(f)=1\)，常数数列 \(\mathbf1\) 满足 \(p(P_f\mathbf1)=p(\mathbf1)=1\)，结合上界即得最优常数为 1。

设 \(1<C=C(f)<\infty\)。固定 \(0<c<C\) 及 \(\varepsilon>0\)。可取越来越稀疏的整数 \(n_j\)，满足 \(f(n_j)\ge c n_j\)，各指标段
\[
J_j=\{n_j,\ldots,n_j+\lfloor\varepsilon n_j\rfloor\}
\]
互不相交，并且 \(\sum_{i<j}|J_i|/n_j\to0\)。定义 \(A=\bigcup_j f(J_j)\)。

对 \(f(n_j)\le M<f(n_{j+1})\)，同样估计得
\[
\frac{|A\cap[1,M]|}{M}
\le\frac{\sum_{i<j}|J_i|+|J_j|}{c n_j}.
\]
所以 \(p(\mathbf1_A)\le\varepsilon/c\)。在 \(m_j=n_j+\lfloor\varepsilon n_j\rfloor\) 处则有
\[
\frac1{m_j}\sum_{i=1}^{m_j}(P_f\mathbf1_A)_i
\ge\frac{\lfloor\varepsilon n_j\rfloor+1}{n_j+\lfloor\varepsilon n_j\rfloor}
\longrightarrow\frac\varepsilon{1+\varepsilon}.
\]
设 \(L\) 是任何有效 Lipschitz 常数，便有
\[
\frac\varepsilon{1+\varepsilon}\le L\frac\varepsilon c,
\qquad L\ge\frac c{1+\varepsilon}.
\]
令 \(c\uparrow C\)、\(\varepsilon\downarrow0\)，得到 \(L\ge C\)。结合第 2 节，最优常数恰为 \(C\)。

## 5. 满射性、单射性与等距性

给定任意有界数列 \(y\)，定义 \(x_{f(j)}=y_j\)，在其余位置令 \(x_i=0\)。严格递增性使定义无冲突，且 \(x\) 有界、\(P_fx=y\)。故每个允许的 \(T_f\) 都满射。

令 \(B=\mathbb N\setminus f(\mathbb N)\)。若 \(C(f)>1\)，沿 \(f(n)/n\to C(f)\) 的子列，
\[
\frac{|B\cap[1,f(n)]|}{f(n)}=1-\frac n{f(n)}\longrightarrow1-\frac1{C(f)}>0.
\]
所以 \([\mathbf1_B]\ne[0]\)，但 \(P_f\mathbf1_B=0\)，诱导映射不是单射。

若 \(C(f)=1\)，由 \(f(n)\ge n\) 得 \(f(n)/n\to1\)。对
\[
k(M)=|f(\mathbb N)\cap[1,M]|,
\]
有 \(f(k(M))\le M<f(k(M)+1)\)，从而 \(k(M)/M\to1\)，故 \(B\) 的密度为零。对任意 \(x\)，
\[
\frac1M\sum_{i=1}^{M}|x_i|
\le\frac1M\sum_{j=1}^{k(M)}|x_{f(j)}|+\|x\|_\infty\frac{|B\cap[1,M]|}{M}.
\]
取 limsup 得 \(p(x)\le p(P_fx)\)。第 2 节给出反向不等式，因此 \(p(P_fx)=p(x)\)。于是 \(T_f\) 是等距映射，特别地单射。

## 6. 迭代率存在及其必要范围

直接计算可得 \(P_f^k=P_{f^{\circ k}}\)。由 Lipschitz 复合界，所有这些取样都允许下降，且
\[
L_k=C(f^{\circ k}),\qquad 1\le L_{k+\ell}\le L_kL_\ell.
\]
对 \(a_k=\log L_k\ge0\) 使用次可加数列引理，得到
\[
\lim_{k\to\infty}\frac{a_k}k=\inf_{k\ge1}\frac{a_k}k.
\]
此引理可由 \(k=qm+s\)、\(0\le s<m\) 时 \(a_k\le qa_m+a_s\) 直接证明，再对 \(m\) 取下确界。因此
\[
R_f=\inf_{k\ge1}L_k^{1/k},\qquad 1\le R_f\le L_1<\infty.
\]
不需要假设商空间完备，也没有使用 Banach 空间谱理论。

## 7. 每个可能的有序对都可实现

给定任意实数 \(1\le r\le C<\infty\)。取整数列
\[
N_j=2^{2^j}\quad(j\ge1),
\]
并定义
\[
a(n)=
\begin{cases}
0,&1\le n<N_1,\\
\lfloor(C-r)N_j\rfloor,&N_j\le n<N_{j+1},
\end{cases}
\qquad f(n)=\lfloor rn\rfloor+a(n).
\]
函数 \(a\) 非减，而 \(r\ge1\) 保证 \(\lfloor r(n+1)\rfloor-\lfloor rn\rfloor\ge1\)，因此 \(f\) 严格递增。又有
\[
n\le f(n)\le Cn,
\qquad \frac{f(N_j)}{N_j}\longrightarrow C,
\]
故 \(C(f)=C\)。

下面实际上证明对每个固定 \(k\ge1\)，
\[
L_k=A_k:=r^k+(C-r)\sum_{i=0}^{k-1}r^i.\tag{*}
\]

### 下界

因 \(N_{j+1}/N_j\to\infty\)，固定 \(k\) 后，对充分大的 \(j\)，\(C^kN_j<N_{j+1}\)。从 \(N_j\) 出发的前 \(k\) 次迭代都留在同一指标段内，且每一步只是 \(v\mapsto\lfloor rv\rfloor+\lfloor(C-r)N_j\rfloor\)。有限次取整误差为 \(O_k(1)\)，故
\[
\frac{f^{\circ k}(N_j)}{N_j}\longrightarrow r^k+(C-r)\sum_{i=0}^{k-1}r^i=A_k.
\]
这给出 \(L_k\ge A_k\)。

### 上界

固定 \(k\)。因为 \(f(v)\le Cv\)，从大整数 \(n\) 开始的前 \(k\) 次迭代都落在 \([n,C^kn]\) 内。相邻 \(N_j\) 的比值趋于无穷，故对充分大的 \(n\)，此区间至多包含一个分段边界。

若没有跨越分段边界，所有迭代使用同一个常量 \(a\le(C-r)n\)，从而
\[
f^{\circ k}(n)=r^kn+a\sum_{i=0}^{k-1}r^i+O_k(1)\le A_kn+O_k(1).
\]

若跨越边界 \(N=N_{j+1}\)，令 \(\ell\in\{1,\ldots,k\}\) 为第一次达到或超过 \(N\) 的迭代次数。因为 \(N\le C^kn\) 且 \(N_j/N\to0\)，跨越前所用常量为 \(O(N_j)=o(n)\)。因此
\[
v_\ell:=f^{\circ\ell}(n)=r^\ell n+o(n),\qquad N\le v_\ell.
\]
跨越后所用常量 \(a'=\lfloor(C-r)N\rfloor\le(C-r)v_\ell\)。此后不再跨越边界，所以
\[
\begin{aligned}
f^{\circ k}(n)
&=r^{k-\ell}v_\ell+a'\sum_{i=0}^{k-\ell-1}r^i+O_k(1)\\
&\le\left(r^k+(C-r)\sum_{i=\ell}^{k-1}r^i\right)n+o(n)\\
&\le A_kn+o(n).
\end{aligned}
\]
空和按零处理。这也覆盖最后一步恰好跨越的情形。有限个 \(\ell\) 的误差可以统一，故取 limsup 得 \(L_k\le A_k\)，证明了 (*)。

若 \(r=1\)，则 \(A_k=1+k(C-1)\)，所以 \(A_k^{1/k}\to1\)。若 \(r>1\)，则
\[
A_k=r^k+(C-r)\frac{r^k-1}{r-1},
\]
其 \(k\) 次方根趋于 \(r\)。因此构造满足 \((L_1,R_f)=(C,r)\)。所有允许有序对均已实现，包含 \(C=r=1\)、\(r=1<C\) 和 \(r=C\) 的边界。
