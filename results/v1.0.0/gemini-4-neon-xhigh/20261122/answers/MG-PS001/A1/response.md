下面给出两问的完整解答与证明。

---

### 预备说明

对任意 $x=(x_j)_{j=1}^\infty\in E$，因 $x$ 有界，记 $\|x\|_\infty=\sup_{j\ge 1}|x_j|<+\infty$，并记
$$
\|x\|:=d(x,0)=\limsup_{N\to\infty}\frac{1}{N}\sum_{j=1}^{N}|x_j|\in [0,\|x\|_\infty].
$$
直接由上极限的性质可见：
1. 对任意 $x,y\in E$，有 $d(x,y)=\|x-y\|$；
2. $\|\cdot\|$ 是 $E$ 上的半范数（非负、绝对齐次且满足三角不等式），从而 $d$ 是 $E$ 上的伪度量，$\sim$ 是等价关系；
3. 商空间 $X=E/\!\sim$ 按 $\|[x]\|:=\|x\|$ 成为赋范实线性空间，其诱导距离为 $\bar d([x],[y])=d(x,y)=\|[x]-[y]\|$。

由于 $P_f:E\to E$ 是线性映射，$P_f$ 能诱导 $X$ 上的良定义映射 $T_f([x])=[P_fx]$ 当且仅当
$$
\forall x,y\in E,\quad d(x,y)=0\implies d(P_fx,P_fy)=0,
$$
由线性性即等价于
$$
\forall x\in E,\quad d(x,0)=0\implies d(P_fx,0)=0.
$$
当 $T_f$ 良定义时，$T_f$ 也是线性映射；又 $X$ 非平凡（例如常数列 $\mathbf 1=(1,1,\ldots)$ 满足 $d(\mathbf 1,0)=1>0$），故 $T_f$ 的最小 Lipschitz 常数（若不存在有限常数则约定为 $+\infty$）为
$$
L(T_f)=\sup_{\substack{u,v\in X\\ u\neq v}}\frac{\bar d(T_fu,T_fv)}{\bar d(u,v)}=\sup_{\substack{x\in E\\ d(x,0)>0}}\frac{d(P_fx,0)}{d(x,0)}.
$$

另外，对任意严格递增函数 $f:\mathbb N\to\mathbb N$，容易由数学归纳法得 $f(n)\ge n$（$\forall n\in\mathbb N$）：$f(1)\ge 1$，且若 $f(n)\ge n$，则 $f(n+1)>f(n)\ge n$，故 $f(n+1)\ge n+1$。因此 $\frac{f(n)}{n}\ge 1$ 对一切 $n\in\mathbb N$ 成立，记
$$
C_f:=\limsup_{n\to\infty}\frac{f(n)}{n}\in [1,+\infty].
$$

---

## 第 1 问

### 结论汇总

1. **允许的函数 $f$**：严格递增函数 $f:\mathbb N\to\mathbb N$ 使 $P_f$ 诱导良定义映射 $T_f:X\to X$，**当且仅当**
   $$
   C_f=\limsup_{n\to\infty}\frac{f(n)}{n}<+\infty
   $$
   （等价地，$\sup_{n\in\mathbb N}\frac{f(n)}{n}<+\infty$，即 $f(n)=O(n)$）。
2. 对每一个允许的 $f$：
   - **最小 Lipschitz 常数**：$L(T_f)=C_f=\limsup_{n\to\infty}\frac{f(n)}{n}\in [1,+\infty)$；
   - **连续性**：$T_f$ 恒为连续映射（事实上是 Lipschitz 连续映射）；
   - **满射性**：$T_f$ 恒为满射；
   - **单射性**：$T_f$ 为单射**当且仅当** $\lim_{n\to\infty}\frac{f(n)}{n}=1$（等价地，$C_f=\limsup_{n\to\infty}\frac{f(n)}{n}=1$，此时 $T_f$ 实为双射等距）。

---

### 完整证明

#### 1.1 $T_f$ 良定义的充要条件

**充分性（$C_f<+\infty\implies T_f$ 良定义且 $L(T_f)\le C_f$）：**

设 $C_f<+\infty$。任取 $x,y\in E$，记 $z_m=|x_m-y_m|\ge 0$，则 $z=(z_m)_{m=1}^\infty\in E$。对任意 $n\in\mathbb N$，因 $1\le f(1)<f(2)<\cdots<f(n)$ 是 $\{1,2,\ldots,f(n)\}$ 中互异的正整数且 $z_m\ge 0$，有
$$
\frac{1}{n}\sum_{j=1}^{n}|x_{f(j)}-y_{f(j)}|=\frac{1}{n}\sum_{j=1}^{n}z_{f(j)}\le \frac{1}{n}\sum_{m=1}^{f(n)}z_m=\frac{f(n)}{n}\cdot\frac{1}{f(n)}\sum_{m=1}^{f(n)}z_m.
$$
令 $a_n=\frac{f(n)}{n}\ge 0$，$b_n=\frac{1}{f(n)}\sum_{m=1}^{f(n)}z_m\ge 0$。因 $f$ 严格递增，$(b_n)$ 是有界数列 $\left(\frac{1}{N}\sum_{m=1}^{N}z_m\right)_{N=1}^\infty$ 的子列，故
$$
\limsup_{n\to\infty} b_n\le \limsup_{N\to\infty}\frac{1}{N}\sum_{m=1}^{N}z_m=d(x,y)<+\infty.
$$
对任意 $\varepsilon>0$，存在 $N_0\in\mathbb N$，使对一切 $n\ge N_0$ 有 $a_n\le C_f+\varepsilon$ 且 $b_n\le d(x,y)+\varepsilon$，从而 $a_nb_n\le (C_f+\varepsilon)(d(x,y)+\varepsilon)$。令 $n\to\infty$ 取上极限，再令 $\varepsilon\to 0^+$，得
$$
d(P_fx,P_fy)\le C_f\, d(x,y). \tag{1}
$$
由 $(1)$ 立即得出：若 $d(x,y)=0$，则 $d(P_fx,P_fy)=0$，故 $T_f$ 良定义；进一步对所有 $[x],[y]\in X$ 有
$$
\bar d(T_f([x]),T_f([y]))\le C_f\,\bar d([x],[y]),
$$
即 $T_f$ 是 Lipschitz 连续映射，且 $L(T_f)\le C_f<+\infty$。

**必要性（$C_f=+\infty\implies T_f$ 不良定义）：**

设 $\limsup_{n\to\infty}\frac{f(n)}{n}=+\infty$。下面归纳构造严格递增正整数列 $(n_k)_{k=1}^\infty$：
- 取 $n_1=1$（则 $\frac{f(n_1)}{n_1}\ge 1$）；
- 若已取定 $n_1,\ldots,n_{k-1}$（$k\ge 2$），令
  $$
  M_k:=\max\left\{2n_{k-1},\; k\sum_{i=1}^{k-1}(n_i+1)\right\}.
  $$
  由于 $\limsup_{n\to\infty}\frac{f(n)}{n}=+\infty$，集合 $\{n\in\mathbb N:\frac{f(n)}{n}\ge k\}$ 无穷，故可选取 $n_k>M_k$ 满足 $\frac{f(n_k)}{n_k}\ge k$。

由此序列满足：
1. 对一切 $k\ge 2$，$n_k>2n_{k-1}$，故 $f(2n_{k-1})<f(n_k)$；
2. 对一切 $k\ge 2$，$f(n_k)\ge n_k>k\sum_{i=1}^{k-1}(n_i+1)$；
3. 对一切 $k\ge 1$，$\frac{n_k+1}{f(n_k)}\le\frac{2n_k}{f(n_k)}\le\frac{2}{k}$。

对每个 $k\ge 1$，记
$$
S_k:=\{f(j): n_k\le j\le 2n_k\},\qquad S:=\bigcup_{k=1}^{\infty}S_k,
$$
并定义 $x=\mathbf 1_S\in E$（即 $m\in S$ 时 $x_m=1$，$m\notin S$ 时 $x_m=0$）。因 $f$ 单射，有 $|S_k|=n_k+1$。

先证 $d(x,0)=0$。对任意整数 $N\ge f(n_2)$，由于 $f(n_1)<f(n_2)<\cdots$ 且 $f(n_k)\ge n_k\to+\infty$，存在唯一整数 $k\ge 2$ 使 $f(n_k)\le N<f(n_{k+1})$。对任意 $r\ge k+1$ 及任意 $m\in S_r$，皆有 $m\ge f(n_r)\ge f(n_{k+1})>N$，故 $S\cap\{1,\ldots,N\}\subseteq\bigcup_{i=1}^{k}S_i$。于是
$$
0\le \frac{1}{N}\sum_{m=1}^{N}|x_m|=\frac{|S\cap\{1,\ldots,N\}|}{N}\le\frac{1}{f(n_k)}\sum_{i=1}^{k}|S_i|=\frac{\sum_{i=1}^{k-1}(n_i+1)}{f(n_k)}+\frac{n_k+1}{f(n_k)}<\frac{1}{k}+\frac{2}{k}=\frac{3}{k}.
$$
对任意 $K\ge 2$，当 $N\ge f(n_K)$ 时必有 $k\ge K$，故 $\frac{1}{N}\sum_{m=1}^{N}|x_m|<\frac{3}{K}$。从而 $\lim_{N\to\infty}\frac{1}{N}\sum_{m=1}^{N}|x_m|=0$，即 $d(x,0)=0$，$x\sim 0$。

再证 $d(P_fx,0)>0$。对每个 $k\ge 1$ 及 $j\in\{n_k,\ldots,2n_k\}$，有 $f(j)\in S_k\subseteq S$，故 $(P_fx)_j=x_{f(j)}=1$。于是
$$
\frac{1}{2n_k}\sum_{j=1}^{2n_k}|(P_fx)_j|\ge\frac{1}{2n_k}\sum_{j=n_k}^{2n_k}1=\frac{n_k+1}{2n_k}>\frac{1}{2}.
$$
因 $2n_k\to+\infty$，故 $d(P_fx,0)\ge\frac{1}{2}>0$，即 $P_fx\not\sim 0=P_f0$。因此 $P_f$ 不能诱导 $X$ 上的映射。

综上，$T_f$ 良定义当且仅当 $C_f=\limsup_{n\to\infty}\frac{f(n)}{n}<+\infty$。

---

#### 1.2 最小 Lipschitz 常数与连续性

设 $f$ 允许，即 $C_f\in [1,+\infty)$。由 1.1 节已得 $L(T_f)\le C_f$，且由此即知 $T_f$ 是 Lipschitz 连续映射，从而连续。

下证 $L(T_f)\ge C_f$。任取 $\delta>0$。由 $\limsup_{n\to\infty}\frac{f(n)}{n}=C_f$，存在严格递增正整数列 $(r_\ell)_{\ell=1}^\infty$ 使得 $\lim_{\ell\to\infty}\frac{f(r_\ell)}{r_\ell}=C_f$。从中归纳抽取子列 $(n_k)_{k=1}^\infty$，并记 $m_k:=\lfloor(1+\delta)n_k\rfloor$：
- 选取 $n_1\in\{r_\ell\}$ 满足 $n_1\ge 1/\delta$（于是 $m_1\ge n_1+1>n_1$）；
- 若已取定 $n_1,\ldots,n_{k-1}$（$k\ge 2$），选取 $n_k\in\{r_\ell\}$ 满足
  $$
  n_k>\max\left\{m_{k-1},\; k\sum_{i=1}^{k-1}(m_i-n_i+1)\right\}.
  $$

则对一切 $k\ge 1$ 有 $m_k\ge n_k$，$\lim_{k\to\infty}\frac{f(n_k)}{n_k}=C_f$，对一切 $k\ge 2$ 有 $n_k>m_{k-1}$（从而 $f(n_1)<f(n_2)<\cdots\to+\infty$）以及 $f(n_k)\ge n_k>k\sum_{i=1}^{k-1}(m_i-n_i+1)$。

令 $S_k:=\{f(j): n_k\le j\le m_k\}$，$S:=\bigcup_{k=1}^{\infty}S_k$，并取 $x=\mathbf 1_S\in E$。则 $|S_k|=m_k-n_k+1$。

一方面，对每个 $k\ge 1$，
$$
\frac{1}{m_k}\sum_{j=1}^{m_k}|(P_fx)_j|\ge\frac{1}{m_k}\sum_{j=n_k}^{m_k}1=\frac{m_k-n_k+1}{m_k}.
$$
因为 $(1+\delta)n_k-1<m_k\le(1+\delta)n_k$ 且 $n_k\to+\infty$，有 $\lim_{k\to\infty}\frac{m_k}{n_k}=1+\delta$，故
$$
\lim_{k\to\infty}\frac{m_k-n_k+1}{m_k}=\frac{\delta}{1+\delta},
$$
从而 $d(P_fx,0)\ge\frac{\delta}{1+\delta}>0$。

另一方面，对任意整数 $N\ge f(n_2)$，存在唯一整数 $k=k(N)\ge 2$ 满足 $f(n_k)\le N<f(n_{k+1})$。同前可得 $S\cap\{1,\ldots,N\}\subseteq\bigcup_{i=1}^{k}S_i$，于是
$$
\frac{1}{N}\sum_{m=1}^{N}|x_m|\le\frac{\sum_{i=1}^{k-1}(m_i-n_i+1)}{f(n_k)}+\frac{m_k-n_k+1}{f(n_k)}<\frac{1}{k}+\frac{m_k-n_k+1}{n_k}\cdot\frac{n_k}{f(n_k)}=:u_k.
$$
由于 $\lim_{k\to\infty}u_k=0+\delta\cdot\frac{1}{C_f}=\frac{\delta}{C_f}$，且 $N\to+\infty$ 时 $k(N)\to+\infty$，故
$$
d(x,0)=\limsup_{N\to\infty}\frac{1}{N}\sum_{m=1}^{N}|x_m|\le\frac{\delta}{C_f}.
$$
又由 $0<\frac{\delta}{1+\delta}\le d(P_fx,0)\le C_f\,d(x,0)$ 可知 $d(x,0)>0$，即 $[x]\neq [0]$。因此
$$
L(T_f)\ge\frac{\bar d(T_f([x]),T_f([0]))}{\bar d([x],[0])}=\frac{d(P_fx,0)}{d(x,0)}\ge\frac{\delta/(1+\delta)}{\delta/C_f}=\frac{C_f}{1+\delta}.
$$
由 $\delta>0$ 的任意性，令 $\delta\to 0^+$ 得 $L(T_f)\ge C_f$。结合 $L(T_f)\le C_f$，即证
$$
L(T_f)=C_f=\limsup_{n\to\infty}\frac{f(n)}{n}.
$$

---

#### 1.3 满射性与单射性

设 $f$ 允许。

**满射性：** 对任意 $[y]\in X$（其中 $y=(y_j)_{j=1}^\infty\in E$），因 $f$ 严格递增故单射，可良定义数列 $x=(x_m)_{m=1}^\infty$：
$$
x_m=\begin{cases}
y_j, & \text{若存在 } j\in\mathbb N \text{ 使 } m=f(j),\\
0, & \text{若 } m\notin f(\mathbb N).
\end{cases}
$$
显然 $\|x\|_\infty=\|y\|_\infty<+\infty$，故 $x\in E$；且对所有 $j\in\mathbb N$ 有 $(P_fx)_j=x_{f(j)}=y_j$，即 $P_fx=y$，从而 $T_f([x])=[y]$。因此 $T_f$ 恒为满射。

**单射性：** 记 $A=f(\mathbb N)$，$A^c=\mathbb N\setminus A$。因 $\frac{f(n)}{n}\ge 1$ 恒成立，条件 $\lim_{n\to\infty}\frac{f(n)}{n}=1$ 与 $C_f=\limsup_{n\to\infty}\frac{f(n)}{n}=1$ 等价。下面证明 $T_f$ 单射当且仅当 $\lim_{n\to\infty}\frac{f(n)}{n}=1$。

- **（必要性）** 设 $T_f$ 单射。取 $x=\mathbf 1_{A^c}\in E$。对任意 $j\in\mathbb N$，因 $f(j)\in A$，故 $(P_fx)_j=x_{f(j)}=0$，于是 $T_f([x])=[0]=T_f([0])$。由 $T_f$ 单射得 $[x]=[0]$，即
  $$
  \lim_{N\to\infty}\frac{|A^c\cap\{1,\ldots,N\}|}{N}=0.
  $$
  特别地，取 $N=f(n)\to+\infty$。因 $f$ 严格递增，$A\cap\{1,\ldots,f(n)\}=\{f(1),\ldots,f(n)\}$，故 $|A^c\cap\{1,\ldots,f(n)\}|=f(n)-n$。于是
  $$
  \lim_{n\to\infty}\left(1-\frac{n}{f(n)}\right)=\lim_{n\to\infty}\frac{f(n)-n}{f(n)}=0,
  $$
  从而 $\lim_{n\to\infty}\frac{f(n)}{n}=1$。

- **（充分性）** 设 $\lim_{n\to\infty}\frac{f(n)}{n}=1$。对任意 $N\in\mathbb N$，记 $\pi(N):=|A\cap\{1,\ldots,N\}|$。当 $N\ge f(1)$ 时，$\pi(N)\ge 1$ 且 $f(\pi(N))\le N<f(\pi(N)+1)$，由此
  $$
  \frac{\pi(N)}{f(\pi(N)+1)}<\frac{\pi(N)}{N}\le\frac{\pi(N)}{f(\pi(N))}\le 1.
  $$
  由于对任意 $m\in\mathbb N$，$N\ge f(m)$ 蕴含 $\pi(N)\ge m$，故 $N\to+\infty$ 时 $\pi(N)\to+\infty$。又
  $$
  \lim_{n\to\infty}\frac{n}{f(n+1)}=\lim_{n\to\infty}\frac{n}{n+1}\cdot\frac{n+1}{f(n+1)}=1,
  $$
  由夹逼定理得 $\lim_{N\to\infty}\frac{\pi(N)}{N}=1$，从而
  $$
  \lim_{N\to\infty}\frac{|A^c\cap\{1,\ldots,N\}|}{N}=\lim_{N\to\infty}\left(1-\frac{\pi(N)}{N}\right)=0.
  $$
  现设 $T_f([x])=T_f([y])$，记 $z=x-y\in E$，则 $d(P_fz,0)=0$，亦即 $\lim_{n\to\infty}\frac{1}{n}\sum_{j=1}^{n}|(P_fz)_j|=0$。对任意 $N\ge f(1)$，记 $n=\pi(N)$，则 $A\cap\{1,\ldots,N\}=\{f(1),\ldots,f(n)\}$ 且 $N\ge f(n)\ge n$，于是
  $$
  \frac{1}{N}\sum_{m=1}^{N}|z_m|=\frac{1}{N}\sum_{j=1}^{n}|z_{f(j)}|+\frac{1}{N}\sum_{\substack{1\le m\le N\\ m\in A^c}}|z_m|\le\frac{1}{n}\sum_{j=1}^{n}|(P_fz)_j|+\|z\|_\infty\cdot\frac{|A^c\cap\{1,\ldots,N\}|}{N}.
  $$
  当 $N\to+\infty$ 时，$n=\pi(N)\to+\infty$，故右端两项均趋于 $0$。于是 $d(x,y)=d(z,0)=0$，即 $[x]=[y]$。因此 $T_f$ 单射。

第 1 问全部证明完毕。

---

## 第 2 问

### 结论汇总

1. 对任意第 1 问中允许的 $f$，极限 $R_f=\lim_{k\to\infty}L_k^{1/k}$ 存在，且 $R_f=\inf_{k\ge 1}L_k^{1/k}$。
2. 全部可能的有序对 $(L_1,R_f)$ 组成的集合为
   $$
   \Omega=\{(L,R)\in\mathbb R^2: 1\le R\le L<+\infty\}.
   $$
3. 对每个 $(L,R)\in\Omega$，取 $a_m=m!$（$m\in\mathbb N$），对任意 $n\in\mathbb N$，令 $m$ 为满足 $a_m\le n<a_{m+1}$ 的唯一正整数，定义
   $$
   f(n)=\lfloor Rn+(L-R)a_m\rfloor,
   $$
   则 $f:\mathbb N\to\mathbb N$ 严格递增、在第 1 问中允许，且满足 $(L_1,R_f)=(L,R)$。

---

### 完整证明

#### 2.1 $R_f=\lim_{k\to\infty}L_k^{1/k}$ 的存在性与必要条件

设 $f:\mathbb N\to\mathbb N$ 在第 1 问中允许。对任意 $k\in\mathbb N$，用归纳法易知：
- $f^k=\underbrace{f\circ\cdots\circ f}_{k\text{ 次}}:\mathbb N\to\mathbb N$ 严格递增；
- 对任意 $x\in E$ 与 $j\in\mathbb N$，$(P_f^kx)_j=x_{f^k(j)}$（即 $P_f^k=P_{f^k}$），归纳步为 $(P_f^{k+1}x)_j=(P_f(P_f^kx))_j=(P_f^kx)_{f(j)}=x_{f^k(f(j))}=x_{f^{k+1}(j)}$；
- 从而 $T_f^k([x])=[P_f^kx]=[P_{f^k}x]$，即 $T_f^k=T_{f^k}$。

故 $f^k$ 在第 1 问中也允许，由第 1 问结论得
$$
L_k=L(T_{f^k})=\limsup_{n\to\infty}\frac{f^k(n)}{n}\in [1,+\infty)\qquad (\forall k\in\mathbb N).
$$

对任意 $j,k\in\mathbb N$ 及任意 $u,v\in X$，有
$$
\bar d(T_f^{j+k}(u),T_f^{j+k}(v))=\bar d\big(T_f^j(T_f^k(u)),T_f^j(T_f^k(v))\big)\le L_j\,\bar d(T_f^k(u),T_f^k(v))\le L_jL_k\,\bar d(u,v).
$$
由最小 Lipschitz 常数的定义得次可乘性：
$$
L_{j+k}\le L_jL_k\qquad (\forall j,k\in\mathbb N).
$$

令 $a_0:=0$，对 $k\ge 1$ 令 $a_k:=\ln L_k\ge 0$。则对一切非负整数 $j,k$ 均有次可加性 $a_{j+k}\le a_j+a_k$。记
$$
\alpha:=\inf_{k\ge 1}\frac{a_k}{k}\in [0,a_1].
$$
显然 $\liminf_{k\to\infty}\frac{a_k}{k}\ge\alpha$。另一方面，任取固定的 $m\in\mathbb N$。对任意 $k\ge m$，作带余除法写 $k=qm+r$，其中 $q\in\mathbb N$，$0\le r<m$。由次可加性归纳可得 $a_{qm}\le qa_m$，故
$$
a_k=a_{qm+r}\le qa_m+a_r.
$$
两边除以 $k$，并利用 $qm\le k$ 与 $a_m\ge 0$，得
$$
\frac{a_k}{k}\le\frac{qm}{k}\cdot\frac{a_m}{m}+\frac{a_r}{k}\le\frac{a_m}{m}+\frac{\max_{0\le r<m}a_r}{k}.
$$
令 $k\to\infty$ 取上极限，得 $\limsup_{k\to\infty}\frac{a_k}{k}\le\frac{a_m}{m}$。对 $m\in\mathbb N$ 取下确界，得
$$
\limsup_{k\to\infty}\frac{a_k}{k}\le\inf_{m\ge 1}\frac{a_m}{m}=\alpha\le\liminf_{k\to\infty}\frac{a_k}{k}.
$$
因此 $\lim_{k\to\infty}\frac{a_k}{k}=\alpha$ 存在。由指数函数的连续性，极限
$$
R_f:=\lim_{k\to\infty}L_k^{1/k}=\lim_{k\to\infty}e^{a_k/k}=e^\alpha=\inf_{k\ge 1}L_k^{1/k}
$$
存在。此外，因 $0\le\alpha\le a_1=\ln L_1<+\infty$，必有
$$
1\le R_f\le L_1<+\infty,
$$
即 $(L_1,R_f)\in\Omega=\{(L,R)\in\mathbb R^2: 1\le R\le L<+\infty\}$。

---

#### 2.2 对每个 $(L,R)\in\Omega$ 构造严格递增函数 $f$

任取实数 $L,R$ 满足 $1\le R\le L<+\infty$。令 $a_m:=m!$（$m\in\mathbb N$），则 $1=a_1<a_2<a_3<\cdots$ 严格递增且 $\frac{a_{m+1}}{a_m}=m+1\to+\infty$。从而每个 $n\in\mathbb N$ 属于唯一的区间 $[a_m,a_{m+1})$，据此定义
$$
f(n):=\lfloor Rn+(L-R)a_m\rfloor\qquad (a_m\le n<a_{m+1}).
$$

下面分步验证 $f$ 满足全部要求。

**步骤 1：$f$ 映 $\mathbb N$ 到 $\mathbb N$ 且严格递增。**

对任意 $n\in [a_m,a_{m+1})$，因 $R\ge 1$，$L-R\ge 0$，$n\ge a_m\ge 1$，有 $Rn+(L-R)a_m\ge n\ge 1$，故 $f(n)\ge n\ge 1$，$f(n)\in\mathbb N$。

再证 $f(n+1)>f(n)$。分两种情形：
- 若 $n+1<a_{m+1}$，则 $n+1\in [a_m,a_{m+1})$，取整号内两表达式之差为
  $$
  \big(R(n+1)+(L-R)a_m\big)-\big(Rn+(L-R)a_m\big)=R\ge 1.
  $$
- 若 $n+1=a_{m+1}$，则 $n+1\in [a_{m+1},a_{m+2})$，取整号内两表达式之差为
  $$
  \big(R(n+1)+(L-R)a_{m+1}\big)-\big(Rn+(L-R)a_m\big)=R+(L-R)(a_{m+1}-a_m)\ge R\ge 1.
  $$

因实数 $y\ge x+1$ 总推出 $\lfloor y\rfloor\ge\lfloor x+1\rfloor=\lfloor x\rfloor+1>\lfloor x\rfloor$，故在两种情形下均有 $f(n+1)\ge f(n)+1>f(n)$。所以 $f$ 严格递增。

**步骤 2：全局界与允许性。**

对任意 $n\in [a_m,a_{m+1})$，因 $a_m\le n$ 且 $L-R\ge 0$，有
$$
f(n)\le Rn+(L-R)a_m\le Rn+(L-R)n=Ln.
$$
因此 $L_1=\limsup_{n\to\infty}\frac{f(n)}{n}\le L<+\infty$，$f$ 在第 1 问中允许；并且由数学归纳法得，对一切整数 $j\ge 0$ 与 $n\in\mathbb N$ 均有
$$
n\le f^j(n)\le L^j n \qquad (\text{约定 } f^0(n)=n).
$$

**步骤 3：精确计算 $L_k$。**

对整数 $j\ge 0$，定义 $S_j:=\sum_{i=0}^{j-1}R^i$（约定 $S_0=0$），则 $S_1=1$ 且对所有 $j\ge 0$ 有 $S_{j+1}=RS_j+1$。注意对任意 $j\ge 1$，因 $L\ge R\ge 1$，有
$$
(L-R)S_j=(L-R)\sum_{i=0}^{j-1}R^i\le(L-R)\sum_{i=0}^{j-1}L^{j-1-i}R^i=L^j-R^j,
$$
从而
$$
R^j+(L-R)S_j\le L^j,\qquad (L-R)S_j\le L^j-R^j<L^j. \tag{2}
$$

现固定 $k\in\mathbb N$，令 $M_k:=\lceil L^k\rceil\in\mathbb N$。对一切 $m\ge M_k$，由 $(2)$ 有
$$
\frac{a_{m+1}}{a_m}=m+1>L^k>(L-R)S_k,
$$
特别地，$L^k a_m<a_{m+1}$ 且 $L^k a_{m+1}<a_{m+2}$。

1. **下界 $L_k\ge R^k+(L-R)S_k$：**
   对任意 $m\ge M_k$ 及 $0\le j\le k-1$，有
   $$
   a_m\le f^j(a_m)\le L^j a_m\le L^k a_m<a_{m+1},
   $$
   故 $f^j(a_m)\in [a_m,a_{m+1})$，从而
   $$
   f^{j+1}(a_m)=\lfloor Rf^j(a_m)+(L-R)a_m\rfloor>Rf^j(a_m)+(L-R)a_m-1.
   $$
   对 $j=0,1,\ldots,k$ 归纳证明
   $$
   f^j(a_m)\ge R^j a_m+(L-R)S_j a_m-S_j.
   $$
   事实上，$j=0$ 时两边均等于 $a_m$；若对 $j$（$0\le j\le k-1$）成立，则
   $$
   \begin{aligned}
   f^{j+1}(a_m)&>R\big(R^j a_m+(L-R)S_j a_m-S_j\big)+(L-R)a_m-1\\
   &=R^{j+1}a_m+(L-R)(RS_j+1)a_m-(RS_j+1)\\
   &=R^{j+1}a_m+(L-R)S_{j+1}a_m-S_{j+1}.
   \end{aligned}
   $$
   取 $j=k$ 并除以 $a_m$，得
   $$
   \frac{f^k(a_m)}{a_m}\ge R^k+(L-R)S_k-\frac{S_k}{a_m}.
   $$
   因 $a_m=m!\to+\infty$，令 $m\to\infty$ 即得
   $$
   L_k=\limsup_{n\to\infty}\frac{f^k(n)}{n}\ge\limsup_{m\to\infty}\frac{f^k(a_m)}{a_m}\ge R^k+(L-R)S_k.
   $$

2. **上界 $L_k\le R^k+(L-R)S_k$：**
   任取整数 $n\ge a_{M_k}$，令 $m=m(n)\ge M_k$ 为满足 $n\in [a_m,a_{m+1})$ 的唯一正整数。对一切 $0\le j\le k$，序列 $(f^j(n))_{j=0}^k$ 单调不减，且
   $$
   a_m\le n\le f^j(n)\le L^k n<L^k a_{m+1}<a_{m+2}.
   $$
   分两种情形讨论：

   - **情形 A：$f^{k-1}(n)<a_{m+1}$。**
     此时对所有 $0\le j\le k-1$ 均有 $f^j(n)\in [a_m,a_{m+1})$，故 $f^{j+1}(n)\le Rf^j(n)+(L-R)a_m$。与上面同样归纳可得对所有 $0\le j\le k$ 有
     $$
     f^j(n)\le R^j n+(L-R)S_j a_m.
     $$
     取 $j=k$ 并利用 $a_m\le n$，得
     $$
     \frac{f^k(n)}{n}\le R^k+(L-R)S_k\frac{a_m}{n}\le R^k+(L-R)S_k.
     $$

   - **情形 B：$f^{k-1}(n)\ge a_{m+1}$**（仅当 $k\ge 2$ 时可能发生，因 $f^0(n)=n<a_{m+1}$）。
     由 $(f^j(n))_{j=0}^k$ 单调不减，存在唯一整数 $r\in\{1,\ldots,k-1\}$，使得
     $$
     f^j(n)\in [a_m,a_{m+1})\quad (0\le j\le r-1),\qquad f^j(n)\in [a_{m+1},a_{m+2})\quad (r\le j\le k-1).
     $$
     在前 $r$ 步应用 $[a_m,a_{m+1})$ 上的递推不等式，归纳得
     $$
     a_{m+1}\le f^r(n)\le R^r n+(L-R)S_r a_m. \tag{3}
     $$
     在后 $k-r$ 步应用 $[a_{m+1},a_{m+2})$ 上的递推不等式 $f^{r+t+1}(n)\le Rf^{r+t}(n)+(L-R)a_{m+1}$（$0\le t\le k-r-1$），对 $t=0,1,\ldots,k-r$ 归纳得
     $$
     f^{r+t}(n)\le R^t f^r(n)+(L-R)S_t a_{m+1}.
     $$
     取 $t=k-r$，并先后利用 $a_{m+1}\le f^r(n)$ 与 $(3)$，得
     $$
     f^k(n)\le \big(R^{k-r}+(L-R)S_{k-r}\big)f^r(n)\le \big(R^{k-r}+(L-R)S_{k-r}\big)\big(R^r n+(L-R)S_r a_m\big).
     $$
     注意：
     - $R^r S_{k-r}=\sum_{i=r}^{k-1}R^i\le\sum_{i=0}^{k-1}R^i=S_k$，故 $\big(R^{k-r}+(L-R)S_{k-r}\big)R^r\le R^k+(L-R)S_k$；
     - 由 $(2)$ 有 $R^{k-r}+(L-R)S_{k-r}\le L^{k-r}\le L^k$，且 $S_r\le S_k$；
     - 由 $(3)$ 以及 $R^r\le R^k$、$S_r\le S_k$，得
       $$
       (m+1)a_m=a_{m+1}\le R^k n+(L-R)S_k a_m \implies \frac{a_m}{n}\le\frac{R^k}{m+1-(L-R)S_k}
       $$
       （因 $m\ge M_k$ 时分母 $m+1-(L-R)S_k>0$）。

     综合以上三点，两边除以 $n$ 即得
     $$
     \frac{f^k(n)}{n}\le R^k+(L-R)S_k+\frac{L^k R^k(L-R)S_k}{m+1-(L-R)S_k}.
     $$

   合并情形 A 与情形 B，对一切 $n\ge a_{M_k}$ 皆有
   $$
   \frac{f^k(n)}{n}\le R^k+(L-R)S_k+\frac{L^k R^k(L-R)S_k}{m(n)+1-(L-R)S_k}.
   $$
   当 $n\to+\infty$ 时，$m(n)\to+\infty$，故最后一项趋于 $0$，从而
   $$
   L_k=\limsup_{n\to\infty}\frac{f^k(n)}{n}\le R^k+(L-R)S_k.
   $$

综合上下界，对一切 $k\in\mathbb N$ 有精确公式
$$
L_k=R^k+(L-R)S_k.
$$

**步骤 4：验证 $(L_1,R_f)=(L,R)$。**

- 取 $k=1$，因 $S_1=1$，得 $L_1=R+(L-R)\cdot 1=L$。
- 对任意 $k\in\mathbb N$，因 $R\ge 1$，有 $0\le S_k=\sum_{i=0}^{k-1}R^i\le kR^k$，又 $L-R\ge 0$，故
  $$
  R^k\le L_k=R^k+(L-R)S_k\le \big(1+(L-R)k\big)R^k.
  $$
  开 $k$ 次方得
  $$
  R\le L_k^{1/k}\le \big(1+(L-R)k\big)^{1/k}R.
  $$
  记 $c=L-R\ge 0$。当 $c=0$ 时 $(1+ck)^{1/k}\equiv 1$；当 $c>0$ 时 $1\le (1+ck)^{1/k}\le (1+c)^{1/k}k^{1/k}\to 1$（$k\to\infty$）。故由夹逼定理得
  $$
  R_f=\lim_{k\to\infty}L_k^{1/k}=R.
  $$

因此对每个 $(L,R)\in\Omega$，所构造的严格递增函数 $f$ 均满足 $(L_1,R_f)=(L,R)$。第 2 问全部证明完毕。