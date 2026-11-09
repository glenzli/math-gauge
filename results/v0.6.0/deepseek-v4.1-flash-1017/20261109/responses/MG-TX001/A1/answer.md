下面给出一个证明。关键是把“三条单位根同时为零点”化成 Fourier 矩阵的一个三阶子式为零，再证明在题设条件下该子式不可能为零。

---

记 \(\mu_N=\{z\in\mathbb C:z^N=1\}\)。

## 1. 一个单射性引理

**引理.** 设 \(p\) 为奇素数，\(N=p^r\)，整数 \(t\) 满足
\[
1\le t<N,\qquad p\nmid t,\qquad t\not\equiv 1\pmod p.
\]
定义
\[
G_t(x)=
\begin{cases}
\dfrac{x^t-1}{x-1},&x\ne1,\\[1ex]
t,&x=1.
\end{cases}
\]
则 \(G_t\) 在 \(\mu_N\) 上是单射。

**证明.** 令 \(K=\mathbb Q(\zeta_N)\)，取 \(K\) 中唯一的素理想 \(\mathfrak P\mid p\)，并把 \(\mathfrak P\)-进赋值 \(v\) 正规化为 \(v(\mathfrak P)=1\)。

熟知：若 \(z\in\mu_N\setminus\{1\}\) 的阶为 \(p^s\)（\(1\le s\le r\)），则
\[
v(z-1)=p^{r-s}>0.
\]
因此所有 \(N\) 次单位根都满足 \(z\equiv1\pmod{\mathfrak P}\)。

反设 \(G_t(x)=G_t(y)\)，其中 \(x,y\in\mu_N\)。

若 \(x=1,y\ne1\)，则
\[
0=G_t(y)-G_t(1)
=\sum_{k=1}^{t-1}y^k
=\frac{y(1-y^{t-1})}{1-y}.
\]
于是 \(y^{t-1}=1\)。但 \(p\nmid(t-1)\)，而 \(y\) 的阶是 \(p\) 的幂，故只能有 \(y=1\)，矛盾。所以不妨 \(x,y\ne1\)。

### 情形一：\(x,y\) 的阶相同

设其公共阶为 \(p^s\)。因为二者同阶且不同，\(x/y\) 的阶仍为 \(p^s\)，所以
\[
v(x-y)=v(x-1)=v(y-1)>0.
\]
对 \(1\le k\le t-1\)，置
\[
S_k=\frac{x^k-y^k}{x-y}
=\sum_{j=0}^{k-1}x^{k-1-j}y^j.
\]
由于 \(x\equiv y\equiv1\pmod{\mathfrak P}\)，有
\[
S_k\equiv k\pmod{\mathfrak P}.
\]
于是
\[
G_t(x)-G_t(y)
=\sum_{k=1}^{t-1}(x^k-y^k)
=(x-y)\sum_{k=1}^{t-1}S_k.
\]
而
\[
\sum_{k=1}^{t-1}S_k
\equiv \sum_{k=1}^{t-1}k
=\frac{t(t-1)}2
\not\equiv0\pmod{\mathfrak P},
\]
因为 \(p\) 为奇素数且 \(p\nmid t(t-1)\)。又 \(x-y\ne0\)，故 \(G_t(x)-G_t(y)\ne0\)，矛盾。

### 情形二：\(x,y\) 的阶不同

不妨设 \(x\) 的阶大于 \(y\) 的阶。由上面的赋值公式，
\[
v(x-1)<v(y-1).
\]
对 \(p\nmid k\)，\(x^k,y^k\) 分别与 \(x,y\) 同阶，因此
\[
v(x^k-1)=v(x-1),\qquad v(y^k-1)=v(y-1).
\]
于是
\[
\frac{x^k-y^k}{x-1}
\equiv k\pmod{\mathfrak P}.
\]
若 \(p\mid k\)，则 \(x^k,y^k\) 的阶都严格小于原来的阶（或 \(x^k=1\)，\(y^k=1\)），故
\[
v(x^k-1)>v(x-1),\qquad v(y^k-1)>v(x-1),
\]
从而该项除以 \(x-1\) 后仍被 \(\mathfrak P\) 整除。

因此
\[
\frac{G_t(x)-G_t(y)}{x-1}
=\sum_{k=1}^{t-1}\frac{x^k-y^k}{x-1}
\equiv
\sum_{\substack{1\le k\le t-1\\ p\nmid k}}k
\pmod{\mathfrak P}.
\]
写 \(t=qp+\rho\)，其中 \(0\le\rho<p\)。因 \(p\nmid t\)，有 \(\rho\ne0\)；又 \(t\not\equiv1\pmod p\)，有 \(\rho\ne1\)。每满一个模 \(p\) 的完整周期，和为零，故
\[
\sum_{\substack{1\le k\le t-1\\ p\nmid k}}k
\equiv 1+2+\cdots+(\rho-1)
=\frac{\rho(\rho-1)}2
\not\equiv0\pmod p.
\]
所以 \(G_t(x)-G_t(y)\ne0\)，仍矛盾。

引理得证。\(\square\)

---

## 2. 证明原命题

反设存在三个互不相同的 \(N\) 次单位根
\[
\xi_1,\xi_2,\xi_3
\]
都满足 \(P(\xi_i)=0\)。

由于 \(c_1,c_2,c_3\) 不全为零，线性方程组
\[
c_1\xi_i^{a_1}+c_2\xi_i^{a_2}+c_3\xi_i^{a_3}=0
\qquad(i=1,2,3)
\]
有非零解，所以三阶矩阵
\[
\bigl(\xi_i^{a_j}\bigr)_{1\le i,j\le3}
\]
奇异，即
\[
\det\bigl(\xi_i^{a_j}\bigr)=0.
\]

令
\[
b=a_2-a_1,\qquad d=a_3-a_1.
\]
因为 \(a_1,a_2,a_3\) 模 \(p\) 两两不同，所以
\[
p\nmid b,\qquad p\nmid d,\qquad p\nmid(d-b).
\]
因此 \(b,d\) 都同 \(N=p^r\) 互素。从矩阵的每一行提出因子 \(\xi_i^{a_1}\)，并令
\[
X=\frac{\xi_2}{\xi_1},\qquad Y=\frac{\xi_3}{\xi_1},
\]
得到
\[
0=
\begin{vmatrix}
1&\xi_1^b&\xi_1^d\\
1&\xi_2^b&\xi_2^d\\
1&\xi_3^b&\xi_3^d
\end{vmatrix}.
\]
用第一行消去后两行的第一列，得
\[
0=\xi_1^{b+d}
\Bigl((X^b-1)(Y^d-1)-(X^d-1)(Y^b-1)\Bigr).
\]
所以
\[
(X^b-1)(Y^d-1)=(X^d-1)(Y^b-1). \tag{1}
\]

由于 \(b\) 与 \(N\) 互素，存在整数 \(t\)，\(1\le t<N\)，使得
\[
d\equiv bt\pmod N.
\]
并且
\[
p\nmid t,\qquad t\not\equiv1\pmod p,
\]
因为 \(p\nmid d\)，且
\[
t-1\equiv b^{-1}(d-b)\not\equiv0\pmod p.
\]

置
\[
U=X^b,\qquad V=Y^b.
\]
它们都是 \(N\) 次单位根。又因为 \(X,Y\ne1\)，且 \(b\) 与 \(N\) 互素，故
\[
U\ne1,\qquad V\ne1.
\]
若 \(U=V\)，则 \(X^b=Y^b\)，从而 \(X=Y\)，即 \(\xi_2=\xi_3\)，矛盾。因此
\[
U\ne V.
\]

将 \(d\equiv bt\pmod N\) 代入 (1)，并注意 \(X^d=(X^b)^t=U^t\)，\(Y^d=(Y^b)^t=V^t\)，得到
\[
(U-1)(V^t-1)=(U^t-1)(V-1).
\]
由于 \(U,V\ne1\)，可除以 \((U-1)(V-1)\)，得
\[
\frac{V^t-1}{V-1}
=
\frac{U^t-1}{U-1},
\]
即
\[
G_t(V)=G_t(U).
\]
但引理说明 \(G_t\) 在 \(\mu_N\) 上单射，故 \(U=V\)，与前面所得矛盾。

因此不存在三个不同的 \(N\) 次单位根同时为 \(P\) 的零点。故在全部 \(N\) 次单位根中，满足 \(P(z)=0\) 的不同根至多有两个。\(\blacksquare\)