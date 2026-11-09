以下均采用题中 Fourier 系数约定。记  
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad d_\alpha(k)=\alpha k_1+k_2 .
\]
于是对光滑函数 \(u\)，
\[
\widehat{\partial_j u}(k)=2\pi i k_j\widehat u(k),\qquad
\widehat{N_\alpha u}(k)=2\pi i\,d_\alpha(k)\widehat u(k).
\]

---

## S1

设
\[
H_N=\operatorname{span}_{\mathbb C}\{e_k:\ 0<|k|\le N\}.
\]
因为 \(\alpha\) 无理，所以 \(d_\alpha(k)\neq0\) 对所有 \(k\neq0\) 成立。定义
\[
N_\alpha^{-1}F
=
\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}\,e_k,
\qquad F\in H_N.
\]
直接求导得 \(N_\alpha N_\alpha^{-1}F=F\)，故这是 \(N_\alpha|_{H_N}\) 的逆。

对任意 \(r\in\mathbb R\)，
\[
\|N_\alpha^{-1}\|_{\mathcal L(H_N,\|\cdot\|_{H^r})}
=
\max_{0<|k|\le N}
\frac{1}{2\pi |d_\alpha(k)|}
=
\frac1{2\pi}
\max_{0<|k|\le N}\frac1{|\alpha k_1+k_2|}.
\]
事实上，
\[
\|N_\alpha^{-1}F\|_{H^r}^2
=
\sum_{0<|k|\le N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{(2\pi)^2|d_\alpha(k)|^2},
\]
故酉对角化后算子范数就是对角元绝对值的最大值；取使最大值达到的频率对应的单项式 \(F=e_k\) 即可取等号。

---

## S2

记 \(F_N=P_NF\) 为投影到 \(0<|k|\le N\) 的频带截断。定义全频率形式解
\[
u=\sum_{k\neq0}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k,
\qquad
u_N=P_Nu.
\]
因为 \(F\) 光滑且零均值，\(\widehat F(k)\) 速降；又由
\[
|d_\alpha(k)|\ge c\langle k\rangle^{-s},
\]
可得
\[
|\widehat u(k)|
\le \frac1{2\pi c}\langle k\rangle^s|\widehat F(k)|.
\]
由于 \(\widehat F(k)\) 对每个多项式阶都速降，故 \(u\in C^\infty_0(\mathbb T^2)\)，且 \(N_\alpha u=F\)。

现在
\[
u-u_N
=
\sum_{|k|>N}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
对 \(|k|>N\)，有
\[
\langle k\rangle^{-q}\le (1+N^2)^{-q/2}.
\]
因此
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=
\sum_{|k|>N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{(2\pi)^2|d_\alpha(k)|^2}\\
&\le
\frac1{(2\pi c)^2}
\sum_{|k|>N}
\langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&=
\frac1{(2\pi c)^2}
\sum_{|k|>N}
\langle k\rangle^{-2q}
\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le
\frac{(1+N^2)^{-q}}{(2\pi c)^2}
\|F\|_{H^{r+s+q}}^2 .
\end{aligned}
\]
开平方即得
\[
\boxed{
\|u-u_N\|_{H^r}
\le
\frac1{2\pi c}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}},
\qquad q\ge0.
}
\]

---

## S3

设 \(u_\alpha,u_\beta\in H_N\) 分别为
\[
N_\alpha u_\alpha=F,\qquad N_\beta u_\beta=F.
\]
则对每个 \(0<|k|\le N\)，
\[
\widehat{u_\alpha-u_\beta}(k)
=
\frac{\widehat F(k)}{2\pi i}
\left(
\frac1{d_\alpha(k)}
-\frac1{d_\beta(k)}
\right).
\]
注意
\[
\frac1{d_\alpha(k)}-\frac1{d_\beta(k)}
=
\frac{(\beta-\alpha)k_1}{d_\alpha(k)d_\beta(k)}.
\]
由 \(|d_\alpha(k)|,|d_\beta(k)|\ge\delta\)，以及 \(|k_1|\le |k|\le N\)，得到
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
|\widehat F(k)|.
\]
乘以 \(\langle k\rangle^r\) 并取 \(\ell^2\) 范数即得
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
\|F\|_{H^r}.
}
\]

---

## S4

### 4.1 Fourier 判据

对 \(s\ge0\) 定义
\[
D_s(\alpha)
:=
\inf_{0\ne k\in\mathbb Z^2}
|d_\alpha(k)|\langle k\rangle^s
=
\inf_{0\ne k\in\mathbb Z^2}
|\alpha k_1+k_2|\langle k\rangle^s\in[0,+\infty].
\]

**命题 4.1.** 对固定 \(s\ge0\)，下列两件事等价：

1. 对每个 \(r\in\mathbb R\)，存在有限常数 \(C_{\alpha,r,s}\)，使得
   \[
   \|u\|_{H^r}
   \le
   C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}
   \qquad
   \forall\,u\in C^\infty_0(\mathbb T^2).
   \]
2. \(D_s(\alpha)>0\)。

并且当 \(D_s(\alpha)>0\) 时，可取
\[
C_{\alpha,r,s}
=
\frac1{2\pi D_s(\alpha)},
\]
它与 \(r\) 无关，而且是最好的常数。

**证明.** 对光滑零均值 \(u\)，
\[
\|N_\alpha u\|_{H^{r+s}}^2
=
(2\pi)^2
\sum_{k\ne0}
|d_\alpha(k)|^2
\langle k\rangle^{2(r+s)}
|\widehat u(k)|^2.
\]
若 \(D_s(\alpha)\ge d_0>0\)，则
\[
|d_\alpha(k)|\langle k\rangle^s\ge d_0
\]
对一切 \(k\ne0\) 成立，于是
\[
\|N_\alpha u\|_{H^{r+s}}
\ge
2\pi d_0\|u\|_{H^r}.
\]
所以不等式成立，且常数至多 \(1/(2\pi d_0)\)。取 \(d_0=D_s(\alpha)\) 得上界。

反之，若 \(D_s(\alpha)=0\)，取 \(k_j\ne0\) 使
\[
|d_\alpha(k_j)|\langle k_j\rangle^s\to0.
\]
令 \(u_j=e_{k_j}\)，则
\[
\frac{\|u_j\|_{H^r}}
{\|N_\alpha u_j\|_{H^{r+s}}}
=
\frac1{2\pi|d_\alpha(k_j)|\langle k_j\rangle^s}
\to\infty,
\]
故不存在有限常数。最后，取使上确界达到或趋近的频率单项式，可见常数 \(1/(2\pi D_s(\alpha))\) 是最优的。\(\square\)

因此，对固定的 \(\alpha\)，全部允许的损失指数精确地为
\[
\boxed{
\mathcal S(\alpha)
=
\{s\ge0:\ D_s(\alpha)>0\}.
}
\]

### 4.2 可逆性：完整分类

记
\[
\|q\alpha\|
=
\min_{m\in\mathbb Z}|q\alpha-m|,
\qquad q=1,2,\dots
\]
并定义算术指数
\[
\lambda(\alpha)
:=
\limsup_{q\to\infty}
\frac{-\log\|q\alpha\|}{\log q}
\in[1,\infty].
\]
若用通常的无理逼近指数
\[
\mu(\alpha)
=
\sup\{\beta:\ |\alpha-p/q|<q^{-\beta}
\text{ 对无穷多个 }p/q\},
\]
则对无理 \(\alpha\) 有
\[
\lambda(\alpha)=\mu(\alpha)-1.
\]
特别地，\(\lambda(\alpha)=\infty\) 正是 Liouville 数；\(\lambda(\alpha)<\infty\) 等价于 \(\alpha\) 非 Liouville。

**命题 4.2.**  
\[
N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)
\]
是双射，当且仅当存在 \(s\ge0\) 使 \(D_s(\alpha)>0\)。等价地，当且仅当 \(\alpha\) 无理且非 Liouville，即 \(\lambda(\alpha)<\infty\)。

更具体地：

- 若 \(\alpha\in\mathbb Q\)，则 \(N_\alpha\) 既非单射也非满射；全部 \(D_s(\alpha)=0\)。
- 若 \(\alpha\) 无理且 \(\lambda(\alpha)=\infty\)（Liouville），则 \(N_\alpha\) 在 \(C^\infty_0\) 上为单射，但不是满射。
- 若 \(\alpha\) 无理且 \(\lambda(\alpha)<\infty\)，则 \(N_\alpha\) 是 \(C^\infty_0\) 到自身的双射。

**证明.**

**（i）有理情形.**  
设 \(\alpha=p/q\)，\((p,q)=1\)，取
\[
k_0=(q,-p)\ne0.
\]
则 \(d_\alpha(k_0)=0\)。令
\[
\varphi(y)=e^{2\pi i k_0\cdot y}.
\]
则 \(\varphi\in C^\infty_0\) 且 \(N_\alpha\varphi=0\)，所以 \(N_\alpha\) 不是单射。另一方面，若方程
\[
N_\alpha u=\varphi
\]
有光滑解，则比较 \(k_0\) 处 Fourier 系数得
\[
0=\widehat{N_\alpha u}(k_0)=\widehat\varphi(k_0)=1,
\]
矛盾。故也不是满射。

**（ii）\(\alpha\) 无理且存在 \(s\) 使 \(D_s(\alpha)>0\).**  
此时对任意 \(F\in C^\infty_0\)，定义
\[
u=\sum_{k\ne0}
\frac{\widehat F(k)}{2\pi i d_\alpha(k)}e_k.
\]
由 \(D_s(\alpha)>0\)，存在 \(c>0\) 使
\[
|d_\alpha(k)|\ge c\langle k\rangle^{-s}.
\]
于是
\[
|\widehat u(k)|
\le
\frac1{2\pi c}
\langle k\rangle^s|\widehat F(k)|.
\]
因为 \(F\) 光滑，\(\widehat F(k)\) 速降，故 \(\widehat u(k)\) 也速降，从而 \(u\in C^\infty_0\)。并且 \(N_\alpha u=F\)。唯一性：若 \(N_\alpha v=0\)，则对所有 \(k\ne0\)，\(d_\alpha(k)\widehat v(k)=0\)，故 \(\widehat v(k)=0\)；零均值又迫使 \(\widehat v(0)=0\)。因此 \(v=0\)。

**（iii）\(\alpha\) 无理且对一切 \(s\ge0\)，\(D_s(\alpha)=0\).**  
需构造一个光滑零均值 \(F\)，使得 \(N_\alpha u=F\) 无光滑零均值解。

因为 \(D_n(\alpha)=0\)，可取非零整数频率 \(k_n\)，使 \(|k_n|\) 严格递增，且
\[
0<|d_\alpha(k_n)|<|k_n|^{-n}.
\]
令
\[
c_n=|d_\alpha(k_n)|\,|k_n|,
\qquad
F(y)=\sum_{n=1}^\infty c_n e^{2\pi i k_n\cdot y}.
\]
对任意多重指标 \(\gamma\)，\(|\gamma|=M\)，有
\[
|\partial^\gamma F(y)|
\le
\sum_n c_n(2\pi|k_n|)^M
\le
(2\pi)^M
\sum_n |k_n|^{-n+M+1}.
\]
当 \(n>M+1\) 时，通项按 \(n\) 超指数速降；有限个初始项也有限。因此 \(F\in C^\infty(\mathbb T^2)\)。又 \(F\) 无零频项，故 \(\int_{\mathbb T^2}F=0\)。

若 \(u\in C^\infty_0\) 解 \(N_\alpha u=F\)，比较 \(k_n\) 处 Fourier 系数：
\[
2\pi i d_\alpha(k_n)\widehat u(k_n)
=
c_n
=
|d_\alpha(k_n)|\,|k_n|.
\]
因此
\[
|\widehat u(k_n)|
=
\frac{|k_n|}{2\pi}\longrightarrow\infty.
\]
于是
\[
\sum_{k\in\mathbb Z^2}|\widehat u(k)|^2=+\infty,
\]
与 \(u\in L^2\) 矛盾。故不存在光滑解。\(\square\)

### 4.3 全部允许损失 \(s\) 的算术描述

由命题 4.1 及上面的算术指数 \(\lambda(\alpha)\)，对无理 \(\alpha\) 有：

\[
D_s(\alpha)>0
\quad\Longrightarrow\quad
\lambda(\alpha)\le s,
\]
并且若 \(\lambda(\alpha)<\infty\)，则
\[
s>\lambda(\alpha)
\quad\Longrightarrow\quad
D_s(\alpha)>0.
\]
因此
\[
\boxed{
(\lambda(\alpha),\infty)
\subseteq
\mathcal S(\alpha)
\subseteq
[\lambda(\alpha),\infty).
}
\]
也就是说：

- 所有 \(s>\lambda(\alpha)\) 都允许；
- 所有 \(s<\lambda(\alpha)\) 都不允许；
- 临界值 \(s=\lambda(\alpha)\) 是否允许，由 \(D_{\lambda(\alpha)}(\alpha)>0\) 是否成立决定。

若 \(\lambda(\alpha)=\infty\)（Liouville 数），则
\[
\boxed{\mathcal S(\alpha)=\varnothing.}
\]
若 \(\alpha\in\mathbb Q\)，同样
\[
\boxed{\mathcal S(\alpha)=\varnothing.}
\]

下面证明上述 \(\lambda\) 判据。若 \(D_s(\alpha)>0\)，取 \(q\) 很大，令 \(p\) 为使 \(|q\alpha-p|=\|q\alpha\|\) 的整数，置 \(k=(q,-p)\)。则 \(|k|\le Cq\)，从而
\[
\|q\alpha\|
=
|d_\alpha(k)|
\ge
D_s(\alpha)\langle k\rangle^{-s}
\ge
c q^{-s}.
\]
故
\[
\frac{-\log\|q\alpha\|}{\log q}
\le s+o(1),
\]
从而 \(\lambda(\alpha)\le s\)。

反之，若 \(\lambda(\alpha)<\infty\)，取 \(s>\lambda(\alpha)\)，令 \(\varepsilon>0\) 满足
\[
\lambda(\alpha)+\varepsilon<s.
\]
由 \(\lambda\) 的定义，对充分大的 \(q\)，
\[
\|q\alpha\|\ge q^{-(\lambda(\alpha)+\varepsilon)}>q^{-s}.
\]
对 \(k=(q,p)\)，若 \(|p|\le Cq\)，则
\[
|d_\alpha(k)|
=
|q\alpha+p|
\ge
\|q\alpha\|
>
q^{-s}
\ge
c_s\langle k\rangle^{-s};
\]
若 \(|p|\) 远大于 \(q\)，则 \(|d_\alpha(k)|\sim |p|\)，下界更加显然。有限多个小 \(q\) 可再缩小常数。于是 \(D_s(\alpha)>0\)。证毕。

### 4.4 特殊方向 \(\alpha_*=\sqrt2-1\)

**命题 4.3.** 对 \(\alpha_*=\sqrt2-1\)，有
\[
\boxed{
\mathcal S(\alpha_*)=[1,\infty).
}
\]
因此最小允许损失为
\[
\boxed{s_{\min}=1,}
\]
并且 \(s=1\) 确实可取到。

**证明.** 先证 \(D_1(\alpha_*)>0\)。写
\[
d_{\alpha_*}(k)
=
(\sqrt2-1)k_1+k_2
=
\sqrt2\,k_1+(k_2-k_1).
\]
令 \(l=k_2-k_1\)。若 \(k_1\ne0\)，则
\[
(\sqrt2 k_1+l)(-\sqrt2 k_1+l)
=
l^2-2k_1^2
\in\mathbb Z\setminus\{0\}.
\]
于是
\[
|\sqrt2 k_1+l|
=
\frac{|l^2-2k_1^2|}
{|-\sqrt2 k_1+l|}
\ge
\frac1{\sqrt2|k_1|+|l|}.
\]
又 \(|l|\le |k_2|+|k_1|\le2|k|\)，故
\[
|d_{\alpha_*}(k)|
\ge
\frac1{(2+\sqrt2)|k|}
\ge
\frac{c_0}{\langle k\rangle},
\qquad
c_0=\frac1{2+\sqrt2}>0.
\]
若 \(k_1=0\)，则 \(d_{\alpha_*}(k)=k_2\)，且 \(|k_2|\ge1\)，同样有
\[
|d_{\alpha_*}(k)|\ge \frac{c_0}{\langle k\rangle}.
\]
因此
\[
D_1(\alpha_*)\ge c_0>0,
\]
并且对一切 \(s\ge1\)，
\[
D_s(\alpha_*)\ge c_0>0.
\]
所以
\[
[1,\infty)\subseteq\mathcal S(\alpha_*).
\]

另一方面，对任意无理 \(\alpha\) 和任意 \(0\le s<1\)，由 Dirichlet 逼近定理，存在无穷多 \(p/q\) 使
\[
\left|\alpha-\frac pq\right|<\frac1{q^2}.
\]
取 \(k=(q,-p)\)，则
\[
|d_\alpha(k)|
=
|q\alpha-p|
<
\frac1q,
\]
且 \(|k|\le Cq\)。因此
\[
|d_\alpha(k)|\langle k\rangle^s
\le
C' q^{-1}q^s
=
C'q^{s-1}\longrightarrow0.
\]
于是 \(D_s(\alpha)=0\)。特别地，对 \(\alpha_*\)，所有 \(s<1\) 都不允许。故
\[
\mathcal S(\alpha_*)=[1,\infty).
\]
证毕。

### 4.5 \(C^m\) 估计

对 \(\alpha_*=\sqrt2-1\)，由上面 \(D_1(\alpha_*)\ge c_0>0\)，对一切光滑零均值 \(u\)，
\[
\|u\|_{H^r}
\le
\frac1{2\pi c_0}
\|N_{\alpha_*}u\|_{H^{r+1}}.
\]
令 \(F=N_{\alpha_*}u\)。对任意 \(m\in\mathbb N_0\)，取 \(r=m+3\)，得
\[
\|u\|_{H^{m+3}}
\le
C\|F\|_{H^{m+4}}.
\]
二维 Sobolev 嵌入给出
\[
H^{m+3}(\mathbb T^2)\subset C^{m+1}(\mathbb T^2)\subset C^m(\mathbb T^2),
\]
因为 \(m+3>m+1+1=m+2\)。另一方面，
\[
\|F\|_{H^{m+4}}\le A_m\|F\|_{C^{m+4}}
\]
对所有光滑 \(F\) 成立，因为 \(H^{m+4}\) 只涉及有限多个阶数不超过 \(m+4\) 的连续导数。

因此存在常数 \(C_m<\infty\)，使得
\[
\boxed{
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le
C_m\|F\|_{C^{m+4}}
\qquad
\forall F\in C^\infty_0(\mathbb T^2).
}
\]
所以题目所问的结论成立。

---

## S5

**结论：不存在这样的开区间 \(J\)、有限 \(s\ge0\) 和有限 \(C\)。**

事实上，任何开区间内都含有 Liouville 型数，而 Liouville 型方向连一个有限损失 \(s\) 的 \(L^2\) 下界都没有。

下面给出直接构造。令
\[
L=\sum_{n=1}^\infty 10^{-n!}.
\]
它是无理数（证明见 S6）。设 \(J\ni\alpha_*\) 为任意开区间，\(s\ge0\) 有限。取有理数
\[
\frac pr\in J.
\]
取足够大的 \(M\)，使得
\[
\alpha:=\frac pr+10^{-M}L\in J.
\]
则 \(\alpha\) 无理。

令
\[
q_n=r10^{M+n!},
\qquad
m_n
=
p10^{M+n!}
+
r\sum_{j=1}^n10^{n!-j!}\in\mathbb Z.
\]
则
\[
\alpha q_n-m_n
=
r\sum_{j=n+1}^\infty10^{n!-j!}
=
O\!\left(10^{-nn!}\right).
\]
置
\[
k_n=(q_n,-m_n).
\]
则 \(|k_n|\le Cq_n\)，并且
\[
|d_\alpha(k_n)|\langle k_n\rangle^s
\le
C_s 10^{-nn!}\bigl(10^{M+n!}\bigr)^s
=
C_s 10^{sM-(n-s)n!}\longrightarrow0
\]
因为 \(n\to\infty\) 且最终 \(n>s\)。因此
\[
D_s(\alpha)=0.
\]
取
\[
u_n(y)=e^{2\pi i k_n\cdot y}.
\]
则 \(\|u_n\|_{L^2}=1\)，而
\[
N_\alpha u_n
=
2\pi i\,d_\alpha(k_n)u_n,
\]
从而
\[
\frac{\|u_n\|_{L^2}}
{\|N_\alpha u_n\|_{H^s}}
=
\frac1{2\pi|d_\alpha(k_n)|\langle k_n\rangle^s}
\longrightarrow\infty.
\]
所以对任何有限 \(C\)，只要 \(n\) 足够大就有
\[
\|u_n\|_{L^2}>C\|N_\alpha u_n\|_{H^s}.
\]
故所要求的一致估计不存在。

---

## S6

取
\[
\alpha=\sum_{n=1}^\infty 10^{-n!}.
\]

### 6.1 \(\alpha\) 是无理数

设
\[
S_N=\sum_{n=1}^N10^{-n!}.
\]
则 \(S_N\) 的分母整除 \(10^{N!}\)，且
\[
0<\alpha-S_N
=
\sum_{n=N+1}^\infty10^{-n!}
<
2\cdot10^{-(N+1)!}.
\]
若 \(\alpha=p/q\in\mathbb Q\)，则 \(\alpha-S_N\) 是非零有理数，其分母整除 \(q10^{N!}\)，故
\[
\alpha-S_N
\ge
\frac1{q10^{N!}}.
\]
但当 \(N\) 充分大时，
\[
2\cdot10^{-(N+1)!}
<
\frac1{q10^{N!}},
\]
因为
\[
2q<10^{(N+1)!-N!}=10^{N\cdot N!}.
\]
矛盾。因此 \(\alpha\notin\mathbb Q\)。

### 6.2 构造一个光滑零均值 \(F\)，使 \(N_\alpha u=F\) 无光滑解

令
\[
q_n=10^{n!},
\qquad
P_n=\sum_{j=1}^n10^{n!-j!}\in\mathbb Z.
\]
由于
\[
\alpha q_n
=
P_n+a_n,
\qquad
a_n:=\sum_{j=n+1}^\infty10^{n!-j!},
\]
且
\[
0<a_n\le 2\cdot10^{-nn!}.
\]
令
\[
k_n=(q_n,-P_n)\ne0.
\]
注意 \(q_n\to\infty\)，\(|k_n|\le2q_n\)，并且
\[
d_\alpha(k_n)
=
\alpha q_n-P_n
=
a_n.
\]

定义
\[
\boxed{
F(y)
=
\sum_{n=1}^\infty
a_n|k_n|\cos(2\pi k_n\cdot y).
}
\]
这是零均值实函数。下面证明 \(F\in C^\infty\)。

对任意多重指标 \(\gamma\)，\(|\gamma|=M\)，有
\[
|\partial^\gamma F(y)|
\le
\sum_{n=1}^\infty
a_n|k_n|(2\pi|k_n|)^M.
\]
由 \(a_n\le2\cdot10^{-nn!}\) 和 \(|k_n|\le2q_n=2\cdot10^{n!}\)，右边第 \(n\) 项至多
\[
C_M
10^{-nn!}10^{(M+1)n!}
=
C_M10^{-(n-M-1)n!}.
\]
当 \(n>M+1\) 时，通项随 \(n\) 超指数速降；有限个初始项也有限。因此所有阶导数都一致收敛，故
\[
F\in C^\infty(\mathbb T^2).
\]
又 \(\int_{\mathbb T^2}F=0\)。

现在假设存在光滑零均值解 \(u\in C^\infty_0(\mathbb T^2)\)，使
\[
N_\alpha u=F.
\]
比较 \(k_n\) 处的 Fourier 系数。因为
\[
\widehat F(k_n)=\frac12a_n|k_n|,
\qquad
\widehat F(-k_n)=\frac12a_n|k_n|,
\]
而
\[
\widehat{N_\alpha u}(k_n)
=
2\pi i\,a_n\widehat u(k_n),
\qquad
\widehat{N_\alpha u}(-k_n)
=
-2\pi i\,a_n\widehat u(-k_n),
\]
所以
\[
|\widehat u(k_n)|
=
|\widehat u(-k_n)|
=
\frac{a_n|k_n|}{4\pi a_n}
=
\frac{|k_n|}{4\pi}.
\]
于是
\[
\sum_{k\ne0}|\widehat u(k)|^2
\ge
2\sum_{n=1}^\infty
\left(\frac{|k_n|}{4\pi}\right)^2
=
+\infty,
\]
因为 \(|k_n|\to\infty\)。这与 \(u\in L^2(\mathbb T^2)\) 矛盾。

因此，这个统一的 \(F\) 是光滑零均值函数，但方程
\[
N_\alpha u=F
\]
没有光滑零均值解。\(\boxed{}\)