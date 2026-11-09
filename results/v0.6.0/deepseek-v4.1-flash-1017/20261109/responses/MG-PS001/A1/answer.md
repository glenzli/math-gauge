令 \(\|x\|_\infty=\sup_{j\ge1}|x_j|\)。先指出
\[
d(x,y)=0\iff \frac1N\sum_{j=1}^N|x_j-y_j|\xrightarrow[N\to\infty]{}0.
\]
这是因为被求和的项非负。

---

## 一、\(P_f\) 何时诱导 \(X\) 上的映射

### 引理 1
\(P_f\) 诱导出良定义的映射 \(T_f([x])=[P_fx]\) 当且仅当
\[
f(n)=O(n)\qquad(n\to\infty).
\]
由于 \(f\) 严格递增，自动有 \(f(n)\ge n\)。

#### 必要性
假设 \(\limsup_{n\to\infty}f(n)/n=+\infty\)。选取严格递增的整数 \(n_k\)，使得
\[
n_k>2n_{k-1},\qquad 
n_k>k\sum_{j<k}(n_j+1),\qquad 
\frac{f(n_k)}{n_k}>k.
\]
令
\[
B=\bigcup_{k=1}^\infty [n_k,2n_k]\cap\mathbb N,
\qquad A=f(B).
\]
在 \(N=2n_k\) 处，
\[
|B\cap[1,N]|\ge n_k+1,
\]
故 \(B\) 有正的上密度，例如 \(\overline d(B)\ge1/2>0\)。

另一方面，若
\[
f(n_k)\le m<f(n_{k+1}),
\]
则所有满足 \(f(j)\le m\) 的 \(j\) 必满足 \(j<n_{k+1}\)。由于 \(n_{k+1}>2n_k\)，这些 \(j\) 至多落在 \(B\) 的前 \(k\) 个区间中。因此
\[
|A\cap[1,m]|
\le \sum_{j=1}^k(n_j+1)
\le 2n_k.
\]
又 \(m\ge f(n_k)>kn_k\)，所以
\[
\frac{|A\cap[1,m]|}{m}\le \frac2k\to0.
\]
于是 \(A\) 有上密度 \(0\)，即 \(\overline d(A)=0\)。

取 \(z={\bf1}_A\)。则 \(d(z,0)=0\)，即 \(z\sim0\)。但
\[
P_fz={\bf1}_{f^{-1}(A)}={\bf1}_B,
\]
而 \(d(P_fz,0)=\overline d(B)>0\)。故 \(P_f\) 不保持等价关系，不能诱导 \(X\) 上的映射。

#### 充分性
设存在 \(C>0\) 使 \(f(n)\le Cn\)。若 \(z\sim0\)，令 \(a_j=|z_j|\)，\(M=\|z\|_\infty\)。对任意 \(\varepsilon>0\)，集合
\[
E_\varepsilon=\{j:a_j>\varepsilon\}
\]
有密度 \(0\)，因为
\[
|E_\varepsilon\cap[1,N]|
\le \frac1\varepsilon\sum_{j=1}^N a_j=o(N).
\]
于是
\[
\begin{aligned}
\frac1N\sum_{k=1}^N a_{f(k)}
&\le \varepsilon+
M\frac{|E_\varepsilon\cap[1,f(N)]|}{N}\\
&\le \varepsilon+
M\frac{|E_\varepsilon\cap[1,CN]|}{N}
\to\varepsilon.
\end{aligned}
\]
令 \(\varepsilon\downarrow0\)，得 \(d(P_fz,0)=0\)。故 \(P_f\) 保持等价关系，诱导映射良定义。

因此第 1 问允许的全部 \(f\) 正是满足 \(f(n)=O(n)\) 的严格递增函数。

---

## 二、连续性、单射性、满射性与最小 Lipschitz 常数

从本节起设 \(f\) 严格递增且 \(f(n)\le Cn\)。记
\[
\Lambda(f):=\limsup_{n\to\infty}\frac{f(n)}n\in[1,\infty).
\]

### 1. 连续性及最小 Lipschitz 常数

#### 上界
取 \(z\in E\)，令 \(a_j=|z_j|\)，\(M=\|z\|_\infty\)，并令
\[
\delta=d(z,0)=\limsup_{m\to\infty}\frac1m\sum_{j=1}^m a_j.
\]
任给 \(\varepsilon>0\)。当 \(m\) 足够大时，
\[
\sum_{j=1}^m a_j\le(\delta+\varepsilon)m.
\]
又当 \(N\) 足够大时 \(f(N)\le(\Lambda(f)+\varepsilon)N\)。于是
\[
\sum_{k=1}^N a_{f(k)}
\le \sum_{j=1}^{f(N)}a_j
\le(\delta+\varepsilon)f(N)
\le(\delta+\varepsilon)(\Lambda(f)+\varepsilon)N.
\]
故
\[
d(P_fz,0)\le \Lambda(f)\,d(z,0).
\]
所以 \(T_f\) 是 Lipschitz 连续的，且
\[
\operatorname{Lip}(T_f)\le \Lambda(f).
\]

#### 下界
任取 \(0<\lambda'<\Lambda(f)\) 和 \(0<\delta<1\)。因为
\[
\limsup_{n\to\infty}\frac{f(n)}n=\Lambda(f),
\]
可以递归选取整数 \(n_j\to\infty\)，满足
\[
\frac{f(n_j)}{n_j}\ge\lambda',\qquad
n_{j+1}>(1+\delta)n_j,
\]
并且
\[
\sum_{i<j}\bigl(\lfloor\delta n_i\rfloor+1\bigr)\le \delta^2n_j.
\]
令
\[
h_j=\lfloor\delta n_j\rfloor,\qquad
B=\bigcup_{j=1}^\infty [n_j,n_j+h_j]\cap\mathbb N,
\qquad A=f(B).
\]
在 \(N_j=(1+\delta)n_j\) 处，
\[
|B\cap[1,N_j]|\ge h_j+1,
\]
故
\[
\overline d(B)
\ge \frac{\delta}{1+\delta}.
\]
另一方面，若 \(f(n_j)\le m<f(n_{j+1})\)，则
\[
|A\cap[1,m]|
\le\sum_{i\le j}(h_i+1)
\le(\delta+\delta^2)n_j+1.
\]
由于 \(m\ge f(n_j)\ge\lambda'n_j\)，得到
\[
\overline d(A)
\le \frac{\delta(1+\delta)}{\lambda'}.
\]
又因 \(f(n_j+h_j)\le C(n_j+h_j)\)，在
\[
m=f(n_j+h_j)
\]
处，\(A\cap[1,m]\) 至少含有 \(h_j+1\) 个点，所以 \(\overline d(A)>0\)。

取 \(z={\bf1}_A\)，则 \(P_fz={\bf1}_B\)，从而
\[
\frac{d(P_fz,0)}{d(z,0)}
=
\frac{\overline d(B)}{\overline d(A)}
\ge
\frac{\lambda'}{(1+\delta)^2}.
\]
先令 \(\delta\downarrow0\)，再令 \(\lambda'\uparrow\Lambda(f)\)，得到
\[
\operatorname{Lip}(T_f)\ge\Lambda(f).
\]
因此
\[
\boxed{\operatorname{Lip}(T_f)=\Lambda(f)
=\limsup_{n\to\infty}\frac{f(n)}n.}
\]
特别地，所有允许的 \(f\) 对应的 \(T_f\) 都连续。

---

### 2. 满射性

对任意 \(y\in E\)，因为 \(f\) 是单射，可以定义
\[
x_{f(j)}=y_j\quad(j\ge1),
\]
而在 \(n\notin f(\mathbb N)\) 处令 \(x_n=0\)。则 \(x\in E\) 且
\[
P_fx=y.
\]
故
\[
\boxed{T_f\text{ 总是满射}.}
\]

---

### 3. 单射性

断言
\[
\boxed{T_f\text{ 是单射}\iff \lim_{n\to\infty}\frac{f(n)}n=1
\iff \Lambda(f)=1.}
\]

若 \(\Lambda(f)>1\)，取 \(\varepsilon>0\) 及 \(n_j\to\infty\) 使
\[
\frac{f(n_j)}{n_j}\ge1+\varepsilon.
\]
令
\[
A=\mathbb N\setminus f(\mathbb N).
\]
在 \(m=f(n_j)\) 处，\(f(1),\dots,f(n_j)\) 都 \(\le m\)，所以
\[
|A\cap[1,m]|\ge m-n_j.
\]
于是
\[
\overline d(A)
\ge1-\frac{n_j}{f(n_j)}
\ge \frac{\varepsilon}{1+\varepsilon}>0.
\]
取 \(z={\bf1}_A\)。则 \(P_fz=0\)，但 \(z\not\sim0\)。故 \(T_f\) 不单射。

反之，若 \(f(n)/n\to1\)，对任意有界序列 \(z\)，令 \(a_j=|z_j|\)，并令
\[
S_N=\sum_{k=1}^N a_{f(k)},\qquad
D_m=\frac1m\sum_{j=1}^m a_j.
\]
前 \(N\) 个采样点 \(f(1),\dots,f(N)\) 是 \([1,f(N)]\) 中的 \(N\) 个不同点，故其中缺失的点数至多 \(f(N)-N\)。于是
\[
\bigl|S_N-f(N)D_{f(N)}\bigr|
\le \|z\|_\infty (f(N)-N).
\]
又 \(f(N)/N\to1\)，且 \(f(N+1)-f(N)=o(N)\)，所以
\[
\limsup_{N\to\infty}D_{f(N)}=\limsup_{m\to\infty}D_m=d(z,0).
\]
故
\[
d(P_fz,0)=d(z,0).
\]
于是 \(T_f\) 保持距离，当然单射。证毕。

---

## 三、迭代的 Lipschitz 常数与可能的 \((L_1,R_f)\)

记 \(f^k=f\circ\cdots\circ f\)（\(k\) 次）。显然
\[
P_f^k=P_{f^k},
\]
因此
\[
T_f^k=T_{f^k}.
\]
由第一部分的公式，
\[
\boxed{L_k:=\operatorname{Lip}(T_f^k)
=\limsup_{n\to\infty}\frac{f^k(n)}n.}
\]

### 1. \(R_f\) 的存在性

记 \(a_k=L_k\)。任取 \(\varepsilon>0\)。因为
\[
a_k=\limsup_{n\to\infty}\frac{f^k(n)}n,
\]
当 \(n\) 足够大时
\[
\frac{f^k(n)}n\le a_k+\varepsilon.
\]
同理，当 \(m\) 足够大时
\[
\frac{f^j(m)}m\le a_j+\varepsilon.
\]
而 \(f^k(n)\to\infty\)，故
\[
\begin{aligned}
\frac{f^{j+k}(n)}n
&=
\frac{f^j(f^k(n))}{f^k(n)}
\frac{f^k(n)}n\\
&\le(a_j+\varepsilon)(a_k+\varepsilon)
\end{aligned}
\]
对足够大的 \(n\) 成立。令 \(n\to\infty\)，再令 \(\varepsilon\downarrow0\)，得到
\[
a_{j+k}\le a_ja_k.
\]
于是 \(\log a_k\) 是次可加序列：
\[
\log a_{j+k}\le\log a_j+\log a_k.
\]
由 Fekete 次可加引理，
\[
\lim_{k\to\infty}\frac{\log a_k}{k}
\]
存在，从而
\[
\boxed{R_f:=\lim_{k\to\infty}L_k^{1/k}\text{ 存在}.}
\]

此外，因 \(f^k(n)\ge n\)，有 \(L_k\ge1\)，故 \(R_f\ge1\)。又由 \(a_{j+k}\le a_ja_k\) 可归纳得
\[
L_k=a_k\le a_1^k=L_1^k,
\]
于是
\[
R_f\le L_1.
\]
所以必有
\[
\boxed{1\le R_f\le L_1<\infty.}
\]

下面证明反过来每个这样的有序对都能实现。

---

## 四、全部可能的 \((L_1,R_f)\)

结论为
\[
\boxed{\{(L_1,R_f):f\text{ 允许}\}
=\{(L,R):1\le R\le L<\infty\}.}
\]
下面逐类构造。

---

### 情形 A：\(R=L\)

若 \(L=1\)，取 \(f(n)=n\)。

若 \(L>1\)，取
\[
f(n)=\lfloor Ln\rfloor.
\]
由于 \(L>1\)，\(f\) 严格递增，且 \(f(n)\le Ln\)，故允许。并且
\[
\frac{f(n)}n\to L,
\]
所以 \(L_1=L\)。又
\[
f(n)=Ln+O(1),
\]
逐步迭代得
\[
f^k(n)=L^kn+O_k(1).
\]
于是
\[
L_k=\limsup_{n\to\infty}\frac{f^k(n)}n=L^k,
\qquad
R_f=\lim_{k\to\infty}(L^k)^{1/k}=L.
\]
故 \((L_1,R_f)=(L,L)\) 可实现。

---

### 情形 B：\(1<R<L\)

记
\[
r=R,\qquad \ell=L,\qquad 1<r<\ell.
\]
令
\[
\alpha=\frac{\ell-1}{r-1}>1.
\]
选取严格递增的整数 \(N_k\)，并令
\[
d_k=\lfloor(\ell-1)N_k\rfloor,\qquad
M_k=\left\lceil\frac{d_k+1}{r-1}\right\rceil,
\]
使得
\[
N_{k+1}>M_k+1,\qquad
N_{k+1}>r^{k+3}(M_k+1)
\]
对所有 \(k\) 成立，且 \(N_1\) 足够大。注意
\[
\frac{d_k}{N_k}\to\ell-1,\qquad
\frac{M_k}{N_k}\to\alpha.
\]

定义
\[
f(n)=
\begin{cases}
n+d_k,&N_k\le n\le M_k,\\[2mm]
\lfloor rn\rfloor,& n\notin\bigcup_{j=1}^\infty[N_j,M_j].
\end{cases}
\]
可以检查 \(f\) 严格递增：在区间 \([N_k,M_k]\) 内斜率为 \(1\)；在外部 \(\lfloor rn\rfloor\) 严格递增；在端点处，因为 \(N_k\) 很大且
\[
\frac{d_k}{N_k}\to\ell-1>r-1,
\]
有
\[
N_k+d_k>\lfloor r(N_k-1)\rfloor.
\]
又由 \(M_k\ge (d_k+1)/(r-1)\)，
\[
\lfloor r(M_k+1)\rfloor
\ge r(M_k+1)-1
>M_k+d_k,
\]
所以右端点也严格递增。

再者，若 \(N_k\le n\le M_k\)，则
\[
\frac{f(n)}n=1+\frac{d_k}{n}
\le1+\frac{d_k}{N_k}\to\ell,
\]
且在 \(n=N_k\) 时该比值趋于 \(\ell\)。在区间外
\[
\frac{f(n)}n\to r.
\]
故
\[
L_1=\limsup_{n\to\infty}\frac{f(n)}n=\ell.
\]
又 \(d_k\le(\ell-1)N_k\le(\ell-1)n\)，故 \(f(n)\le\ell n\)，所以 \(f\) 是允许的。

另一方面，由 \(M_k\) 的定义，
\[
(r-1)M_k<d_k+r.
\]
于是对 \(N_k\le n\le M_k\)，
\[
d_k>(r-1)n-r,
\]
从而
\[
f(n)=n+d_k\ge rn-r.
\]
在区间外也有
\[
f(n)=\lfloor rn\rfloor\ge rn-1.
\]
故存在常数 \(C\) 使
\[
f(n)\ge rn-C\qquad(n\ge1).
\]
迭代可得，对每个固定的 \(k\)，
\[
f^k(n)\ge r^kn-C_k.
\]
因此
\[
L_k=\limsup_{n\to\infty}\frac{f^k(n)}n\ge r^k,
\]
从而
\[
R_f\ge r.
\]

下面证明 \(R_f\le r\)。考虑任一轨道
\[
x_{i+1}=f(x_i).
\]
把轨道的一段极大连续项落在 \(\bigcup_j[N_j,M_j]\) 中者称为一个 “episode”。

若一个 episode 发生在 \([N_j,M_j]\)，其进入值 \(y\ge N_j\)，在离开时的值不超过
\[
r(M_j+1).
\]
由 \(M_j/N_j\to\alpha\)，存在常数 \(K\)，使每个 episode 至多把当前值乘以 \(K\)。而在区间外，
\[
f(x)=\lfloor rx\rfloor\le rx,
\]
所以每一步至多乘以 \(r\)。

设一个 episode 在第 \(j\) 个区间结束。此后在进入下一个区间之前，每一步至多乘以 \(r\)。由
\[
N_{j+1}>r^{j+3}(M_j+1)
\]
可知，在 \(j+1\) 步内不可能到达 \(N_{j+1}\)，故两次 episode 之间至少有 \(j+2\) 个区间外步骤。于是若在 \(k\) 步内发生了 \(E\) 个 episode，则
\[
1+2+\cdots+E\lesssim k,
\]
从而 \(E=O(\sqrt k)\)。因此存在常数 \(C\)，使得对一切 \(x_0\)，
\[
f^k(x_0)\le K^{O(\sqrt k)}r^kx_0.
\]
于是
\[
L_k\le r^kK^{C\sqrt k},
\qquad
R_f=\lim_{k\to\infty}L_k^{1/k}\le r.
\]
结合 \(R_f\ge r\)，得到
\[
R_f=r=R.
\]
故 \((L_1,R_f)=(L,R)\) 可实现。

---

### 情形 C：\(R=1<L\)

记 \(\ell=L>1\)。选取整数 \(N_k\to\infty\)，满足
\[
N_{k+1}>\max\{N_k^3,kN_k^2\}.
\]
令
\[
d_k=\lfloor(\ell-1)N_k\rfloor,
\]
并定义
\[
f(n)=
\begin{cases}
n,&n<N_1,\\
n+d_k,&N_k\le n<N_{k+1}.
\end{cases}
\]
因为
\[
f(N_{k+1})-f(N_{k+1}-1)
=1+d_{k+1}-d_k>0,
\]
且在每一块内 \(f(n+1)-f(n)=1\)，所以 \(f\) 严格递增。

又对 \(N_k\le n<N_{k+1}\)，
\[
\frac{f(n)}n
=1+\frac{d_k}{n}
\le1+\frac{d_k}{N_k}
\to\ell,
\]
且在 \(n=N_k\) 时该比值趋于 \(\ell\)。故
\[
L_1=\limsup_{n\to\infty}\frac{f(n)}n=\ell.
\]
同时 \(f(n)\le\ell n\)，所以 \(f\) 是允许的。

显然 \(f(n)\ge n\)，故 \(f^k(n)\ge n\)，从而 \(L_k\ge1\)，\(R_f\ge1\)。

下面证明 \(R_f\le1\)。固定 \(k\)。当 \(n\) 足够大时，\(n\) 落在某个块 \([N_j,N_{j+1})\) 中。在未离开该块时，
\[
f^t(n)=n+td_j
\le n(1+k(\ell-1))
\]
对 \(t\le k\) 成立。

若在 \(k\) 步内进入下一块，则进入时的值至多为
\[
C_kn:=n(1+k(\ell-1)).
\]
进入下一块后，新的位移为
\[
d_{j+1}\le(\ell-1)N_{j+1}\le(\ell-1)C_kn.
\]
由于 \(N_{j+2}>N_{j+1}^3\)，当 \(n\) 足够大时，在剩余的 \(k\) 步内不可能再进入下一个块。故至多跨过一个块边界。于是
\[
f^k(n)\le C'_kn,
\]
其中 \(C'_k=O(k^2)\)。因此
\[
L_k\le C'_k=O(k^2),
\qquad
R_f=\lim_{k\to\infty}L_k^{1/k}\le1.
\]
结合 \(R_f\ge1\)，得到
\[
R_f=1.
\]
故 \((L_1,R_f)=(\ell,1)=(L,1)\) 可实现。

---

综上，\(\boxed{(L_1,R_f)\text{ 的全部可能值正是 }1\le R_f\le L_1<\infty}\)。

---

## 五、最终答案摘要

1. \(P_f\) 诱导 \(X\) 上映射当且仅当
   \[
   \boxed{f(n)=O(n).}
   \]
   对这样的 \(f\)：
   \[
   \boxed{T_f\text{ 连续，且 }
   \operatorname{Lip}(T_f)=\limsup_{n\to\infty}\frac{f(n)}n;}
   \]
   \[
   \boxed{T_f\text{ 总是满射};}
   \]
   \[
   \boxed{T_f\text{ 单射}\iff \lim_{n\to\infty}\frac{f(n)}n=1
   \iff \operatorname{Lip}(T_f)=1.}
   \]

2. 对允许的 \(f\)，令
   \[
   L_k=\operatorname{Lip}(T_f^k)
   =\limsup_{n\to\infty}\frac{f^k(n)}n.
   \]
   则
   \[
   \boxed{R_f:=\lim_{k\to\infty}L_k^{1/k}\text{ 存在，且 }1\le R_f\le L_1<\infty.}
   \]
   反过来，对任意实数 \(L,R\) 满足
   \[
   \boxed{1\le R\le L<\infty,}
   \]
   均存在严格递增的允许函数 \(f\)，使得
   \[
   L_1=L,\qquad R_f=R.
   \]
   构造方法为：
   - 若 \(R=L\)，取 \(f(n)=\lfloor Ln\rfloor\)（\(L=1\) 时取 \(f(n)=n\)）；
   - 若 \(1<R<L\)，使用上文情形 B 的稀疏“斜坡”构造；
   - 若 \(1=R<L\)，使用上文情形 C 的分块平移构造。