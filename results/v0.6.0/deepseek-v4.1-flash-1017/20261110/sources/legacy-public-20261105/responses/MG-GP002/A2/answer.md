下面始终记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad \lambda_k=\alpha k_1+k_2,
\]
于是
\[
N_\alpha e_k=2\pi i(\alpha k_1+k_2)e_k=2\pi i\lambda_k e_k.
\]
因 \(\alpha\) 无理，\(\lambda_k\neq0\) 对所有 \(k\neq0\) 成立。

---

## S1

在 \(H_N\) 上定义
\[
N_\alpha^{-1}F
=
\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}\,e_k,
\qquad F\in H_N.
\]
逐频率计算得
\[
N_\alpha N_\alpha^{-1}F=F,\qquad 
N_\alpha^{-1}N_\alpha u=u,
\]
故这是 \(N_\alpha:H_N\to H_N\) 的逆。

对任意 \(r\in\mathbb R\)，在 \(H^r\) 范数下该逆算子是对角算子，因此其精确算子范数为
\[
\boxed{
\|N_\alpha^{-1}\|_{\mathcal L(H^r,H^r)}
=
\frac1{2\pi}
\max_{0<|k|\le N}\frac1{|\alpha k_1+k_2|}
}
\]
事实上上界由逐项估计得到；取使最大值取得的频率 \(k_*\) 及 \(F=e_{k_*}\)，则
\[
\frac{\|N_\alpha^{-1}e_{k_*}\|_{H^r}}{\|e_{k_*}\|_{H^r}}
=
\frac1{2\pi|\alpha k_{*,1}+k_{*,2}|},
\]
故等号成立。

---

## S2

令
\[
F_N=\sum_{0<|k|\le N}\widehat F(k)e_k,
\qquad
u_N=N_\alpha^{-1}F_N.
\]
构造精确解
\[
u=\sum_{k\neq0}\frac{\widehat F(k)}{2\pi i\lambda_k}e_k.
\]
由假设
\[
|\lambda_k|\ge c\langle k\rangle^{-s}
\]
及 \(F\in C^\infty_0\)，对每个 \(M\) 有
\[
|\widehat u(k)|
\le \frac1{2\pi c}\langle k\rangle^s|\widehat F(k)|
=O(\langle k\rangle^{s-M}),
\]
故 \(u\in C^\infty_0\)，且 \(N_\alpha u=F\)。

误差只含高频部分：
\[
\widehat{u-u_N}(k)
=
\begin{cases}
0,& |k|\le N,\\[2mm]
\dfrac{\widehat F(k)}{2\pi i\lambda_k},& |k|>N.
\end{cases}
\]
于是
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&\le \frac1{(2\pi c)^2}
\sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&=
\frac1{(2\pi c)^2}
\sum_{|k|>N}\langle k\rangle^{-2q}
\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2.
\end{aligned}
\]
若 \(|k|>N\)，则
\[
\langle k\rangle^2=1+|k|^2>1+N^2,
\]
故
\[
\langle k\rangle^{-2q}\le (1+N^2)^{-q}.
\]
因此
\[
\|u-u_N\|_{H^r}^2
\le
\frac{(1+N^2)^{-q}}{(2\pi c)^2}
\|F\|_{H^{r+s+q}}^2,
\]
即
\[
\boxed{
\|u-u_N\|_{H^r}
\le
\frac1{2\pi c}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}}.
}
\]

---

## S3

设 \(\lambda_{\gamma,k}=\gamma k_1+k_2\)。对 \(k\in H_N\)，
\[
\widehat{u_\alpha-u_\beta}(k)
=
\frac{\widehat F(k)}{2\pi i}
\left(
\frac1{\lambda_{\alpha,k}}-\frac1{\lambda_{\beta,k}}
\right).
\]
并且
\[
\left|
\frac1{\lambda_{\alpha,k}}-\frac1{\lambda_{\beta,k}}
\right|
=
\frac{|(\beta-\alpha)k_1|}
{|\lambda_{\alpha,k}|\,|\lambda_{\beta,k}|}
\le
\frac{|\alpha-\beta|\,|k_1|}{\delta^2}
\le
\frac{|\alpha-\beta|N}{\delta^2}.
\]
因此
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
|\widehat F(k)|.
\]
乘上 \(\langle k\rangle^{2r}\) 并求和，权重完全抵消，得到
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
\|F\|_{H^r}.
}
\]
对任意实 \(r\) 均成立。

---

## S4

### 4.1 基本引理：小除子与 Liouville 条件

记
\[
\|x\|=\operatorname{dist}(x,\mathbb Z).
\]

**引理 4.1.** 对无理 \(\alpha\) 与 \(s\ge0\)，以下两条等价：

1. 存在 \(c>0\)，使
\[
|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}
\qquad
\forall k\in\mathbb Z^2\setminus\{0\};
\]
2. 存在 \(c'>0\)，使
\[
\|n\alpha\|\ge c'n^{-s}
\qquad
\forall n\ge1.
\]

**证明.**

若 1 成立，取 \(n\ge1\)，令 \(k=(n,m)\)，其中 \(m\) 是离 \(-n\alpha\) 最近的整数。则
\[
|\alpha n+m|=\|n\alpha\|,
\qquad
\langle k\rangle\le Cn.
\]
由 1，
\[
\|n\alpha\|\ge c\langle k\rangle^{-s}\ge c(Cn)^{-s}=c'n^{-s}.
\]

反过来，若 2 成立，且 \(k_1=n\neq0\)，则
\[
|\alpha n+k_2|\ge\|n\alpha\|\ge c'n^{-s}\ge c'\langle k\rangle^{-s},
\]
因为 \(|n|\le\langle k\rangle\)。若 \(k_1=0\)，则 \(k_2\neq0\)，\(|\alpha k_1+k_2|=|k_2|\ge1\ge\langle k\rangle^{-s}\)。证毕。

采用 Liouville 数的等价刻画：
\[
\alpha\text{ 是 Liouville 数}
\iff
\forall A>0,\ \exists q\ge2,\quad \|q\alpha\|<q^{-A}.
\]
其否定恰好是：存在 \(s\ge0\)、\(c>0\)，使
\[
\|q\alpha\|\ge c q^{-s}
\qquad
\forall q\ge1.
\]
因此由引理 4.1：

\[
\boxed{
\alpha\text{ 非 Liouville}
\iff
\exists s\ge0,\ c>0,\ 
|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}
\quad\forall k\neq0.
}
\]

---

### 4.2 \(C^\infty_0\) 上的可逆性

**定理 4.2.** 对无理 \(\alpha\)，下列命题等价：

1. \(N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)\) 是双射；
2. \(\alpha\) 不是 Liouville 数；
3. 存在 \(s\ge0\)、\(c>0\)，使
\[
|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}
\qquad
\forall k\neq0.
\]

当条件成立时，唯一逆由
\[
\boxed{
N_\alpha^{-1}F
=
\sum_{k\neq0}
\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}
e_k
}
\]
给出。

**证明.**

先证单射性。若 \(u\in C^\infty_0\) 且 \(N_\alpha u=0\)，则
\[
2\pi i\lambda_k\widehat u(k)=0
\qquad
\forall k\neq0.
\]
因 \(\alpha\) 无理，\(\lambda_k\neq0\)，故 \(\widehat u(k)=0\) 对所有 \(k\neq0\)。又因 \(u\) 零均值，\(\widehat u(0)=0\)，故 \(u\equiv0\)。

若条件 3 成立，即存在 \(s,c>0\) 使
\[
|\lambda_k|\ge c\langle k\rangle^{-s}.
\]
对 \(F\in C^\infty_0\)，定义形式解
\[
u=\sum_{k\neq0}
\frac{\widehat F(k)}{2\pi i\lambda_k}e_k.
\]
因 \(F\) 光滑，对任意 \(M\) 有
\[
|\widehat F(k)|=O(\langle k\rangle^{-M}).
\]
于是
\[
|\widehat u(k)|
\le
\frac1{2\pi c}
\langle k\rangle^s|\widehat F(k)|
=
O(\langle k\rangle^{s-M}).
\]
取 \(M\) 任意大，得 \(\widehat u(k)=O(\langle k\rangle^{-M})\) 对每个 \(M\)，故 \(u\in C^\infty\)。又 \(u\) 零均值，且由 Fourier 系数逐项相等得
\[
N_\alpha u=F.
\]
所以 \(N_\alpha\) 满射。

反过来，设 \(\alpha\) 是 Liouville 数，或等价地不存在任何 \(s,c\) 满足条件 3。则对每个正整数 \(j\)，\(D_j\) 不成立，故存在 \(k_j\neq0\)，可使
\[
|k_j|\ge j,\qquad |k_j|\text{ 严格递增},\qquad
0<|\lambda_{k_j}|<|k_j|^{-j}.
\]
令
\[
a_j=\frac{|\lambda_{k_j}|}{|k_j|},
\qquad
F=\sum_{j=1}^{\infty}a_j e_{k_j}.
\]
因为
\[
a_j\le |k_j|^{-(j+1)},
\]
所以对任意多重指标 \(\beta\)，
\[
\sum_j \|a_j e_{k_j}\|_{C^{|\beta|}}
\le
(2\pi)^{|\beta|}\sum_j |k_j|^{|\beta|}a_j
<
\infty.
\]
故 \(F\in C^\infty_0\)。

若存在光滑零均值解 \(u\)，则 Fourier 系数必须满足
\[
\widehat u(k_j)
=
\frac{a_j}{2\pi i\lambda_{k_j}}.
\]
因此
\[
|\widehat u(k_j)|
=
\frac1{2\pi |k_j|}.
\]
但若 \(u\in C^\infty\)，则对每个 \(M\)，
\[
\widehat u(k_j)=O(|k_j|^{-M}),
\]
这与上式在 \(M=2\) 时矛盾：
\[
|k_j|^2|\widehat u(k_j)|
=
\frac{|k_j|}{2\pi}\to\infty.
\]
所以不存在光滑零均值解。因此 \(N_\alpha\) 不是满射。定理得证。

若把有理 \(\alpha\) 也纳入，则存在非零 \(k\) 使 \(\alpha k_1+k_2=0\)，\(N_\alpha\) 在 \(C^\infty_0\) 上既有非零核，也不可能满射。因此在题设 \(\alpha\) 无理的范围内，非 Liouville 是精确的充分必要条件。

---

### 4.3 全部 Sobolev 损失指数 \(s\)

对固定的无理 \(\alpha\)，定义
\[
\mathcal S_\alpha
=
\left\{
s\ge0:
\exists c_s>0,\ 
|\alpha k_1+k_2|\ge c_s\langle k\rangle^{-s}
\quad\forall k\neq0
\right\}.
\]

**命题 4.3.** 对给定 \(s\ge0\)，以下两条等价：

1. 对每个 \(r\in\mathbb R\)，存在 \(C_{\alpha,r,s}<\infty\)，使
\[
\|u\|_{H^r}
\le
C_{\alpha,r,s}
\|N_\alpha u\|_{H^{r+s}}
\qquad
\forall u\in C^\infty_0;
\]
2. \(s\in\mathcal S_\alpha\)。

事实上，若 \(c_s\) 如 \(\mathcal S_\alpha\) 中所示，则
\[
\|u\|_{H^r}
\le
\frac1{2\pi c_s}
\|N_\alpha u\|_{H^{r+s}}.
\]

**证明.**

由 Fourier 坐标，
\[
\|u\|_{H^r}^2
=
\sum_{k\neq0}\langle k\rangle^{2r}|\widehat u(k)|^2,
\]
\[
\|N_\alpha u\|_{H^{r+s}}^2
=
(2\pi)^2
\sum_{k\neq0}
|\lambda_k|^2
\langle k\rangle^{2(r+s)}
|\widehat u(k)|^2.
\]
故估计成立当且仅当存在常数 \(C\)，使
\[
1\le C^2(2\pi)^2|\lambda_k|^2\langle k\rangle^{2s}
\qquad
\forall k\neq0,
\]
即
\[
|\lambda_k|\ge \frac1{2\pi C}\langle k\rangle^{-s}.
\]
这正是 \(s\in\mathcal S_\alpha\)。

反过来，若估计成立，取单模 \(u=e_k\)，得
\[
1
=
\frac{\|e_k\|_{H^r}}{\langle k\rangle^r}
\le
C\cdot
2\pi|\lambda_k|\langle k\rangle^s,
\]
故 \(|\lambda_k|\ge(2\pi C)^{-1}\langle k\rangle^{-s}\)。证毕。

等价地，由引理 4.1，
\[
\boxed{
\mathcal S_\alpha
=
\left\{
s\ge0:
\exists c_s>0,\ 
\|n\alpha\|\ge c_s n^{-s}
\quad\forall n\ge1
\right\}.
}
\]
用连分数可把它计算出来。设 \(\alpha=[a_0;a_1,a_2,\dots]\)，\(p_n/q_n\) 为收敛分数，令
\[
\beta(\alpha)
=
\limsup_{n\to\infty}
\frac{\log q_{n+1}}{\log q_n}.
\]
标准最佳逼近不等式给出
\[
\frac1{q_n+q_{n+1}}
<
\|q_n\alpha\|
<
\frac1{q_{n+1}},
\]
且若 \(q_n\le m<q_{n+1}\)，则
\[
\|m\alpha\|\ge\|q_n\alpha\|.
\]
于是：

- 若 \(s>\beta(\alpha)\)，则
\[
\|m\alpha\|\ge c_s m^{-s}
\qquad
\forall m\ge1,
\]
故 \(s\in\mathcal S_\alpha\)；
- 若 \(s<\beta(\alpha)\)，沿收敛分数子列有
\[
\|q_n\alpha\|<q_n^{-s},
\]
故 \(s\notin\mathcal S_\alpha\)；
- 在 \(s=\beta(\alpha)\) 时，属于 \(\mathcal S_\alpha\) 当且仅当
\[
q_{n+1}=O(q_n^{\beta(\alpha)}).
\]

因此 \(\mathcal S_\alpha\) 恰为以 \(\beta(\alpha)\) 为下端的区间，端点是否包含由上述常数是否有界决定。若 \(\alpha\) 是 Liouville 数，则 \(\beta(\alpha)=\infty\)，\(\mathcal S_\alpha=\varnothing\)。

---

### 4.4 取 \(\alpha_*=\sqrt2-1\)

有连分数
\[
\alpha_*=\sqrt2-1=[0;\overline{2}].
\]
其收敛分数分母满足
\[
q_0=1,\qquad q_1=2,\qquad
q_{n+1}=2q_n+q_{n-1}.
\]
因此
\[
2q_n\le q_{n+1}\le3q_n.
\]
由最佳逼近性质，对所有 \(m\ge1\)，
\[
\|m\alpha_*\|\ge \frac{c}{m}
\]
其中可取 \(c=1/4\)。于是
\[
|\alpha_*k_1+k_2|
\ge
c\langle k\rangle^{-1}
\qquad
\forall k\neq0,
\]
故 \(s=1\) 时 Sobolev 估计成立：
\[
\|u\|_{H^r}
\le
C_r\|N_{\alpha_*}u\|_{H^{r+1}}.
\]

另一方面，若 \(s<1\)，取 \(m=q_n\)。由收敛分数的上界，
\[
\|q_n\alpha_*\|
<
\frac1{q_{n+1}}
\le
\frac1{2q_n}.
\]
若存在 \(c_s>0\) 使
\[
\|q_n\alpha_*\|\ge c_s q_n^{-s},
\]
则
\[
c_s q_n^{1-s}
\le
\frac12,
\]
但 \(1-s>0\)，令 \(n\to\infty\) 得矛盾。

因此
\[
\boxed{
\mathcal S_{\alpha_*}=[1,\infty),
\qquad
\text{最小允许损失 }s_{\min}=1,
\text{ 且 }s=1\text{ 取到。}
}
\]

---

### 4.5 \(C^m\) 估计

回答：**成立**。事实上对每个 \(m\in\mathbb N_0\)，存在 \(C_m<\infty\)，使
\[
\boxed{
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le
C_m\|F\|_{C^{m+4}}
\qquad
(F\in C^\infty_0(\mathbb T^2)).
}
\]

证明如下。由 \(s=1\) 的 Sobolev 估计，对任意 \(r\)，
\[
\|N_{\alpha_*}^{-1}F\|_{H^r}
\le
C_r\|F\|_{H^{r+1}}.
\]
取 \(r=m+3\)。若 \(F\in C^{m+4}\)，则 \(F\in H^{m+4}\)，且
\[
\|F\|_{H^{m+4}}\le C\|F\|_{C^{m+4}}.
\]
于是
\[
\|u\|_{H^{m+3}}
\le
C_{m+3}\|F\|_{H^{m+4}}
\le
C'_{m}\|F\|_{C^{m+4}},
\qquad u=N_{\alpha_*}^{-1}F.
\]
二维环面上的 Sobolev 嵌入
\[
H^{m+3}(\mathbb T^2)\subset C^m(\mathbb T^2)
\]
（因 \(m+3>m+1\)）给出
\[
\|u\|_{C^m}
\le
C_{\mathrm{emb}}\|u\|_{H^{m+3}}
\le
C_m\|F\|_{C^{m+4}}.
\]
证明完毕。

---

## S5

回答：**不存在**这样的开区间 \(J\)、有限 \(s\ge0\) 和常数 \(C\)。

反证思路如下。任取开区间 \(J\ni\alpha_*\)、有限 \(s\ge0\) 和 \(C<\infty\)。由于有理数在 \(J\) 中稠密，且可取分母任意大的有理数，取
\[
\frac pq\in J,\qquad q\text{ 任意大}.
\]
再取充分小的无理数 \(\varepsilon\)，使
\[
\alpha=\frac pq+\varepsilon\in J,
\]
且
\[
|\varepsilon|
<
\frac1{2\pi C\,q(1+q^2+p^2)^{s/2}}.
\]
因为 \(p/q\) 位于 \(J\) 中，而 \(J\) 开，\(\varepsilon\) 可取得足够小；同时取 \(\varepsilon\) 为无理数，则 \(\alpha\) 无理。

令
\[
u(y)=e^{2\pi i(qy_1-py_2)}.
\]
则 \(u\in C^\infty_0\)，且
\[
\|u\|_{L^2}=1.
\]
另一方面，
\[
N_\alpha u
=
2\pi i(\alpha q-p)u
=
2\pi i\varepsilon q\,u.
\]
因此
\[
\|N_\alpha u\|_{H^s}
=
2\pi|\varepsilon|q(1+q^2+p^2)^{s/2}
<
\frac1C.
\]
于是
\[
\|u\|_{L^2}=1
>
C\|N_\alpha u\|_{H^s},
\]
与所要求的一致估计矛盾。

所以任何开区间 \(J\ni\alpha_*\) 上都不可能存在一致的有限 \(s,C\)。原因是 Liouville 型方向在 \(J\) 中稠密，可产生任意小的非零 \(\alpha q-p\)。

---

## S6

取
\[
\alpha=\sum_{n=1}^{\infty}10^{-n!}.
\]

### 6.1 \(\alpha\) 无理

\(\alpha\) 的十进制展开为
\[
0.1\,1\,0\,0\,0\,1\,0\,0\,0\,0\,0\,0\,0\,0\,0\,1\cdots,
\]
其中数字 \(1\) 恰好出现在第 \(n!\) 位（\(n=1,2,\dots\)），其余位为 \(0\)。

若 \(\alpha\) 为有理数，则其十进制展开最终周期。设周期为 \(T\)。在最终周期的尾部，数字 \(1\) 出现的位置将落在有限个模 \(T\) 的等差数列中，因此相邻两个 \(1\) 之间的间隔有界。但相邻阶乘位置之间的间隔为
\[
(n+1)!-n!=n\,n!\to\infty,
\]
而 \(1\) 在任意远处仍出现，矛盾。因此 \(\alpha\) 不是最终周期小数，故
\[
\boxed{\alpha\notin\mathbb Q.}
\]

### 6.2 构造一个光滑零均值 \(F\)，使 \(N_\alpha u=F\) 无光滑零均值解

对每个 \(j\ge1\)，令
\[
q_j=10^{j!},
\qquad
p_j
=
q_j\sum_{n=1}^{j}10^{-n!}
=
\sum_{n=1}^{j}10^{j!-n!}\in\mathbb Z.
\]
则
\[
\alpha-\frac{p_j}{q_j}
=
\sum_{n=j+1}^{\infty}10^{-n!}.
\]
定义
\[
r_j
=
q_j\alpha-p_j
=
\sum_{n=j+1}^{\infty}10^{j!-n!}.
\]
首项为
\[
10^{j!-(j+1)!}
=
10^{-j\,j!}
=
q_j^{-j}.
\]
其后各项与首项之比至多为 \(10^{-4}\)，故存在绝对常数 \(C_1,C_2>0\)，使
\[
C_1q_j^{-j}
\le
r_j
\le
C_2q_j^{-j}.
\tag{6.1}
\]

令
\[
k_j=(q_j,-p_j)\in\mathbb Z^2,
\qquad
a_j=q_j^{-(j+1)}.
\]
定义
\[
\boxed{
F(y)
=
\sum_{j=1}^{\infty}
q_j^{-(j+1)}
e^{2\pi i(q_jy_1-p_jy_2)}.
}
\]
因为 \(p_j/q_j<\alpha<1\)，故 \(|k_j|\le Cq_j\)。对任意 \(M\ge0\)，
\[
\sum_{j=1}^{\infty}
\|a_je_{k_j}\|_{C^M}
\le
(2\pi)^M\sum_{j=1}^{\infty}|k_j|^M q_j^{-(j+1)}
\le
C_M\sum_{j=1}^{\infty}q_j^{M-j-1}
<\infty,
\]
因为 \(q_j=10^{j!}\) 增长得比任何多项式都快。因此
\[
F\in C^\infty(\mathbb T^2).
\]
又 \(F\) 没有零频率项，故
\[
\int_{\mathbb T^2}F=0,
\qquad
F\in C^\infty_0(\mathbb T^2).
\]

下面证明 \(F\) 不在 \(N_\alpha(C^\infty_0)\) 中。

若存在光滑零均值解 \(u\) 满足
\[
N_\alpha u=F,
\]
则比较第 \(k_j\) 个 Fourier 系数，得
\[
2\pi i r_j\,\widehat u(k_j)
=
q_j^{-(j+1)}.
\]
因此
\[
|\widehat u(k_j)|
=
\frac{q_j^{-(j+1)}}{2\pi r_j}.
\]
由 (6.1) 的下界 \(r_j\le C_2q_j^{-j}\)，得
\[
|\widehat u(k_j)|
\ge
\frac{1}{2\pi C_2\,q_j}.
\tag{6.2}
\]
但若 \(u\in C^\infty\)，则对每个 \(M\) 都有
\[
\widehat u(k_j)=O(|k_j|^{-M}).
\]
取 \(M=2\)。由于 \(|k_j|\le Cq_j\)，由 (6.2) 得
\[
|k_j|^2|\widehat u(k_j)|
\ge
\frac{|k_j|^2}{2\pi C_2q_j}
\ge
c|k_j|\to\infty,
\]
这与 \(u\in C^2\) 所要求的 \(|\widehat u(k_j)|=O(|k_j|^{-2})\) 矛盾。

因此 \(F\) 虽然属于 \(C^\infty_0\)，却不存在光滑零均值解 \(u\)。特别地，
\[
\boxed{
N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)
\text{ 不是满射。}
}
\]
这与 S4 的判别一致：\(\alpha=\sum10^{-n!}\) 是 Liouville 数，因为
\[
\left|\alpha-\frac{p_j}{q_j}\right|
=
\frac{r_j}{q_j}
\asymp
q_j^{-(j+1)},
\]
对每个 \(A\)，取 \(j>A\) 即得优于 \(q_j^{-A}\) 的有理逼近。