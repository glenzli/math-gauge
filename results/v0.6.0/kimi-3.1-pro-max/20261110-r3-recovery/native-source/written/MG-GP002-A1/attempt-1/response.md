记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad d_k(\alpha)=\alpha k_1+k_2 .
\]
则
\[
N_\alpha e_k=2\pi i\,d_k(\alpha)e_k.
\]
由于 \(\alpha\) 无理，对 \(k\ne0\) 总有 \(d_k(\alpha)\ne0\)。

## S1 有限频带上的逆

对
\[
F=\sum_{0<|k|\le N}\widehat F(k)e_k\in H_N,
\]
定义
\[
\boxed{\;
N_\alpha^{-1}F
:=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e_k .
\;}
\]
直接计算得 \(N_\alpha N_\alpha^{-1}F=F\)，同理 \(N_\alpha^{-1}N_\alpha F=F\)，故这是 \(H_N\) 上的逆。

令
\[
\delta_{\alpha,N}:=\min_{0<|k|\le N}|\alpha k_1+k_2|>0.
\]
在 \(H^r\) 范数下，\(N_\alpha^{-1}\) 是对角乘子算子，其乘子模为
\[
\frac1{2\pi |d_k(\alpha)|}.
\]
因此对任意 \(r\in\mathbb R\)，精确的算子范数为
\[
\boxed{\;
\|N_\alpha^{-1}\|_{H^r\to H^r}
=\max_{0<|k|\le N}\frac1{2\pi |\alpha k_1+k_2|}
=\frac1{2\pi\delta_{\alpha,N}} .
\;}
\]
它特别与 \(r\) 无关。

---

## S2 有算术界的截断误差

假设
\[
|d_k(\alpha)|\ge c\langle k\rangle^{-s}
\qquad(k\ne0).
\]
对光滑零均值 \(F\)，定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i d_k(\alpha)}
\quad(k\ne0).
\]
由算术界，
\[
|\widehat u(k)|
\le (2\pi c)^{-1}\langle k\rangle^s|\widehat F(k)|.
\]
所以对每个 \(\rho\in\mathbb R\)，
\[
\|u\|_{H^\rho}\le (2\pi c)^{-1}\|F\|_{H^{\rho+s}}.
\]
因为 \(F\) 光滑，其所有 Sobolev 范数均有限，故 \(u\in\bigcap_\rho H^\rho=C^\infty\)。其 Fourier 级数给出 \(N_\alpha u=F\)，且 \(u\) 零均值。

令 \(F_N\) 为 \(F\) 在 \(0<|k|\le N\) 上的截断，则 \(u_N=N_\alpha^{-1}F_N\) 恰好是 \(u\) 的同一频带截断。因此
\[
u-u_N=\sum_{|k|>N}\widehat u(k)e_k.
\]
于是
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\frac1{4\pi^2}\sum_{|k|>N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}{|d_k(\alpha)|^2}\\
&\le \frac1{(2\pi c)^2}\sum_{|k|>N}
\langle k\rangle^{2r+2s}|\widehat F(k)|^2.
\end{aligned}
\]
当 \(|k|>N\) 时，\(\langle k\rangle^2>1+N^2\)。因 \(q\ge0\)，
\[
\langle k\rangle^{-2q}\le (1+N^2)^{-q}.
\]
代入即得
\[
\|u-u_N\|_{H^r}^2
\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}
\|F\|_{H^{r+s+q}}^2,
\]
从而
\[
\boxed{\;
\|u-u_N\|_{H^r}
\le (2\pi c)^{-1}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}} .
\;}
\]

---

## S3 固定频带内改变方向

对 \(0<|k|\le N\)，两个解的 Fourier 系数分别为
\[
\widehat u_\alpha(k)=\frac{\widehat F(k)}{2\pi i d_k(\alpha)},
\qquad
\widehat u_\beta(k)=\frac{\widehat F(k)}{2\pi i d_k(\beta)}.
\]
因此
\[
\widehat u_\alpha(k)-\widehat u_\beta(k)
=\frac{\widehat F(k)}{2\pi i}
\frac{d_k(\beta)-d_k(\alpha)}
{d_k(\alpha)d_k(\beta)}
=\frac{\widehat F(k)}{2\pi i}
\frac{(\beta-\alpha)k_1}{d_k(\alpha)d_k(\beta)}.
\]
利用 \(|d_k(\alpha)|,|d_k(\beta)|\ge\delta\) 及
\[
|k_1|\le |k|\le N,
\]
得到
\[
|\widehat u_\alpha(k)-\widehat u_\beta(k)|
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat F(k)|.
\]
两边乘以 \(\langle k\rangle^{2r}\) 并求和，即得
\[
\boxed{\;
\|u_\alpha-u_\beta\|_{H^r}
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}
\|F\|_{H^r}.
\;}
\]

---

## S4 整体对象与全部恢复目标

### 1. 一般分类

引入算术条件 \(D_{\alpha,s}\)：
\[
\exists c>0\ \text{使得}\qquad
|d_k(\alpha)|\ge c\langle k\rangle^{-s}
\quad(k\ne0). \tag{\(D_{\alpha,s}\)}
\]

**定理。** 对无理数 \(\alpha\)：

1. \(N_\alpha:C_0^\infty(\mathbb T^2)\to C_0^\infty(\mathbb T^2)\) 总是单射。
2. 它是双射，当且仅当存在某个 \(s\ge0\) 使 \(D_{\alpha,s}\) 成立。
3. 对固定的 \(s\ge0\)，估计
   \[
   \|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}
   \quad(u\in C_0^\infty)
   \]
   对每个 \(r\in\mathbb R\) 成立，当且仅当 \(D_{\alpha,s}\) 成立。
4. 若 \(D_{\alpha,s}\) 以常数 \(c\) 成立，则可以统一取
   \[
   C_{\alpha,r,s}=(2\pi c)^{-1},
   \]
   它甚至不依赖于 \(r\)。

因此，全部允许的 \(s\) 恰好是
\[
\boxed{\;
\mathcal A_\alpha:=\{s\ge0:D_{\alpha,s}\text{ 成立}\},
\;}
\]
该集合为空或向上封闭。

**证明。**

若 \(N_\alpha u=0\)，则对 \(k\ne0\)，
\[
2\pi i d_k(\alpha)\widehat u(k)=0,
\]
故 \(\widehat u(k)=0\)；零均值条件又给出 \(\widehat u(0)=0\)。所以 \(u=0\)，单射性成立。相同计算也说明：只要光滑零均值解存在，它就必然唯一。

若 \(D_{\alpha,s}\) 成立，则 S2 中的构造对任意 \(F\in C_0^\infty\) 给出光滑零均值解，故算子为双射。同时
\[
|\widehat u(k)|
\le (2\pi c)^{-1}\langle k\rangle^s
|\widehat{N_\alpha u}(k)|,
\]
从而
\[
\|u\|_{H^r}\le (2\pi c)^{-1}\|N_\alpha u\|_{H^{r+s}}.
\]

反过来，若固定 \(s\) 的 Sobolev 估计成立，取单频函数 \(u=e_k\)，其中 \(k\ne0\)。因为
\[
\|e_k\|_{H^r}=\langle k\rangle^r,\qquad
\|N_\alpha e_k\|_{H^{r+s}}
=2\pi |d_k(\alpha)|\langle k\rangle^{r+s},
\]
估计给出
\[
|d_k(\alpha)|
\ge (2\pi C_{\alpha,r,s})^{-1}\langle k\rangle^{-s}.
\]
这正是 \(D_{\alpha,s}\)。

最后证明：若所有 \(D_{\alpha,s}\) 都失败，则算子不是满射。此时对每个整数 \(n\ge1\)，取 \(c=1,s=n\)，可找到 \(\ell_n\ne0\) 使
\[
|d_{\ell_n}(\alpha)|<\langle\ell_n\rangle^{-n}.
\]
这些 \(\ell_n\) 不可能全部落在有限频率集内，因为任何有限频率集上的 \(|d_k(\alpha)|\) 有正下界，而 \(\langle\ell_n\rangle^{-n}\to0\)。故可抽取 \(n_1<n_2<\cdots\)，使
\[
k_j:=\ell_{n_j}
\]
两两不同，且 \(n_j\ge j\)。于是
\[
|d_{k_j}(\alpha)|
<\langle k_j\rangle^{-n_j}
\le \langle k_j\rangle^{-j}.
\]
现在一次性构造
\[
F:=\sum_{j=1}^\infty 2\pi i d_{k_j}(\alpha)e_{k_j}.
\]
对任意 \(r\)，当 \(j\) 足够大使 \(2n_j-2r\ge3\) 时，
\[
\langle k_j\rangle^{2r}
|2\pi i d_{k_j}(\alpha)|^2
\le4\pi^2\langle k_j\rangle^{2r-2n_j}
\le4\pi^2\langle k_j\rangle^{-3}.
\]
由于 \(k_j\) 两两不同且
\(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-3}<\infty\)，可知 \(F\in H^r\) 对每个 \(r\) 成立，故 \(F\in C_0^\infty\)。

但若 \(N_\alpha u=F\) 有光滑解，则必须有
\[
\widehat u(k_j)
=\frac{2\pi i d_{k_j}(\alpha)}
{2\pi i d_{k_j}(\alpha)}=1
\qquad(j\ge1).
\]
这给出无穷多个模为 \(1\) 的不同 Fourier 系数，与 \(u\in L^2\) 矛盾。因此该 \(F\) 没有光滑零均值解。证毕。

### 2. \(\alpha_*=\sqrt2-1\) 的最小损失

结论是
\[
\boxed{\mathcal A_{\alpha_*}=[1,\infty).}
\]
所以最小损失为 \(\boxed{s=1}\)，并且 \(\boxed{\text{可以取到}}\)。

先证明 \(s=1\) 的算术界。写 \(k=(m,n)\)，则
\[
d=(\sqrt2-1)m+n=\sqrt2m+n-m.
\]
取共轭代数数
\[
\widetilde d=-(\sqrt2+1)m+n=n-m-\sqrt2m.
\]
当 \(m\ne0\) 时，
\[
d\widetilde d=(n-m)^2-2m^2
\]
是非零整数，故 \(|d\widetilde d|\ge1\)。另一方面，
\[
|\widetilde d|
\le |n|+(1+\sqrt2)|m|
\le(2+\sqrt2)\langle k\rangle.
\]
因此
\[
|d|\ge\frac1{(2+\sqrt2)\langle k\rangle}.
\]
当 \(m=0,n\ne0\) 时，\(|d|=|n|\ge1\)，同一估计显然也成立。故
\[
\boxed{\;
|\alpha_*k_1+k_2|
\ge \frac1{2+\sqrt2}\langle k\rangle^{-1}
\qquad(k\ne0).
\;}
\]
特别地，对所有 \(r\) 可以取
\[
\|u\|_{H^r}
\le \frac{2+\sqrt2}{2\pi}\|N_{\alpha_*}u\|_{H^{r+1}}.
\]

再排除 \(s<1\)。Dirichlet 逼近定理适用于无理数，给出无穷多 \((p_j,q_j)\)，其中 \(q_j\to\infty\)，使
\[
|q_j\alpha_*-p_j|<\frac1{q_j}.
\]
取 \(k_j=(q_j,-p_j)\)。由 \(p_j/q_j\to\alpha_*\)，存在固定常数 \(A\) 使
\(\langle k_j\rangle\le Aq_j\)。若某个 \(s<1\) 的算术界以常数 \(c'\) 成立，则
\[
c'A^{-s}q_j^{-s}
\le |q_j\alpha_*-p_j|
<q_j^{-1},
\]
即
\[
q_j^{1-s}<\frac{A^s}{c'}.
\]
这与 \(q_j\to\infty\) 且 \(1-s>0\) 矛盾。因此不允许任何 \(s<1\)。

### 3. \(C^m\) 恢复估计

答案是肯定的。

维数为 \(2\) 时，Sobolev 嵌入给出
\[
\|v\|_{C^m}\le C_m\|v\|_{H^{m+2}},
\]
因为 \(m+2>m+2/2\)。用 Fourier 系数和 Cauchy–Schwarz 也可直接看到这一点，关键在于
\(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}<\infty\)。

对 \(u=N_{\alpha_*}^{-1}F\)，利用已经取到的 \(s=1\) 估计：
\[
\|u\|_{H^{m+2}}
\le C\|F\|_{H^{m+3}}.
\]
另一方面，对整数阶 Sobolev 范数，展开 \((1+|k|^2)^{m+3}\) 并使用 Parseval，可得
\[
\|F\|_{H^{m+3}}
\le C_m\|F\|_{C^{m+3}}
\le C_m\|F\|_{C^{m+4}}.
\]
合并得到
\[
\boxed{\;
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le C_m\|F\|_{C^{m+4}},
\;}
\]
其中 \(C_m\) 有限且与 \(F\) 无关。

---

## S5 邻近方向的一致估计

\[
\boxed{\text{不存在这样的 }J,s,C.}
\]

反设存在。开区间 \(J\) 内取一个有理数 \(p/q\)，其中 \(q>0\)，并固定非零频率
\[
k=(q,-p).
\]
对任意无理 \(\alpha\in J\)，将所设估计用于 \(u=e_k\)。由于
\[
\|e_k\|_{L^2}=1,\qquad
N_\alpha e_k=2\pi i(\alpha q-p)e_k,
\]
必须有
\[
1\le 2\pi C|\alpha q-p|\langle k\rangle^s
=2\pi Cq\left|\alpha-\frac pq\right|\langle k\rangle^s.
\]
但无理数在 \(J\) 内稠密，可令无理 \(\alpha\in J\) 任意接近 \(p/q\)，使右端任意小，矛盾。因此即使在 \(\alpha_*\) 本身有固定损失估计，也不存在对其整个邻域一致的 \(s,C\)。

---

## S6 一个具体方向的不可解数据

令
\[
q_n=10^{n!},\qquad
p_n=\sum_{j=1}^n10^{n!-j!}\in\mathbb Z,\qquad
A_n=\frac{p_n}{q_n}=\sum_{j=1}^n10^{-j!}.
\]
尾部满足 \(0<\alpha-A_n\)，并且
\[
\begin{aligned}
\alpha-A_n
&=\sum_{j=n+1}^\infty10^{-j!}\\
&\le10^{-(n+1)!}\sum_{\ell=0}^\infty10^{-\ell}
=\frac{10}{9}10^{-(n+1)!}
<2\cdot10^{-(n+1)!}. \tag{1}
\end{aligned}
\]

### \(\alpha\) 的无理性

若 \(\alpha=a/b\)，其中 \(a\in\mathbb Z,b\in\mathbb N\)，则因 \(\alpha\ne A_n\)，整数 \(aq_n-bp_n\) 非零，故
\[
\alpha-A_n
=\frac{|aq_n-bp_n|}{bq_n}
\ge\frac1{bq_n}.
\]
结合 (1) 得
\[
1\le bq_n(\alpha-A_n)
<2b\,10^{n!-(n+1)!}
=2b\,10^{-n\,n!}.
\]
右端随 \(n\to\infty\) 趋于 \(0\)，矛盾。因此 \(\alpha\) 无理。

### 同一个光滑数据的构造

定义
\[
d_n:=\alpha q_n-p_n=q_n(\alpha-A_n)>0.
\]
由 (1)，
\[
0<d_n<2q_n10^{-(n+1)!}
=2\cdot10^{-n\,n!}. \tag{2}
\]
取频率
\[
k_n=(q_n,-p_n).
\]
因为 \(q_n\) 严格递增，这些频率两两不同。又 \(0<A_n<1\)，故 \(0<p_n<q_n\)，从而
\[
\langle k_n\rangle
=\sqrt{1+q_n^2+p_n^2}
\le2q_n=2\cdot10^{n!}. \tag{3}
\]

现在构造单个函数
\[
\boxed{\;
F(y):=\sum_{n=1}^\infty
2\pi i d_n\,e^{2\pi i(q_ny_1-p_ny_2)} .
\;}
\]
它没有零频项，所以只要光滑便自动零均值。

验证其光滑性：对任意固定整数 \(M\ge0\)，由 (2)、(3)，
\[
\begin{aligned}
\langle k_n\rangle^M|2\pi i d_n|
&\le4\pi\,\langle k_n\rangle^M10^{-n n!}\\
&\le2^{M+2}\pi\,10^{M n!}10^{-n n!}\\
&=2^{M+2}\pi\,10^{-(n-M)n!}.
\end{aligned}
\]
对每个固定 \(M\)，
\[
\sum_n10^{-(n-M)n!}<\infty,
\]
因为 \(n<M\) 只有有限项，而 \(n\ge M+1\) 时
\((n-M)n!\ge n!\)。因此所有阶导数的形式级数都绝对且一致收敛，故 \(F\in C_0^\infty(\mathbb T^2)\)。

最后，若 \(N_\alpha u=F\) 有光滑零均值解，则 Fourier 系数必须满足
\[
2\pi i(\alpha q_n-p_n)\widehat u(k_n)
=2\pi i d_n.
\]
由于 \(d_n>0\)，这迫使
\[
\widehat u(k_n)=1\qquad\text{对所有 }n\ge1.
\]
于是 Parseval 给出
\[
\|u\|_{L^2}^2
\ge\sum_{n=1}^\infty|\widehat u(k_n)|^2
=\sum_{n=1}^\infty1=\infty,
\]
与 \(u\in L^2\) 矛盾。因此上述**同一个光滑零均值 \(F\)** 没有光滑零均值解。