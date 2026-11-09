FULL

（修订说明：上一版 S2 中“\(|k|>N\Rightarrow |k|\ge N+1\)”的写法不成立，因为 \(|k|=\sqrt{k_1^2+k_2^2}\) 不一定为整数；正确论证只需用 \(|k|^2>N^2\)。结论与估计式不变。以下为覆盖全题的完整修订版。）

---

## S1：有限频带上的逆

令
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad 
\lambda_k=\alpha k_1+k_2 .
\]
则
\[
N_\alpha e_k=2\pi i(\alpha k_1+k_2)e_k=2\pi i\lambda_k e_k .
\]
因 \(\alpha\notin\mathbb Q\)，对一切 \(0\ne k\in\mathbb Z^2\) 有 \(\lambda_k\ne0\)。因此 \(N_\alpha|_{H_N}\) 在傅里叶基上可对角化，且
\[
\boxed{
(N_\alpha|_{H_N})^{-1}F
=
\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}\,e_k .
}
\]
对任意 \(r\in\mathbb R\)，\(H_N\) 上的 \(H^r\) 范数使各 \(e_k\) 正交，故逆算子范数为最大对角元模：
\[
\boxed{
\left\|(N_\alpha|_{H_N})^{-1}\right\|_{\mathcal L(H^r,H^r)}
=
\frac1{2\pi}
\max_{0<|k|\le N}\frac1{|\alpha k_1+k_2|}
=
\frac1{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.
}
\]
等号由使 \(|\alpha k_1+k_2|\) 最小的单频函数取到。

---

## S2：有算术界时的截断误差

令
\[
F_N=\sum_{0<|k|\le N}\widehat F(k)e_k .
\]
定义全解与截断解
\[
u=\sum_{k\ne0}\frac{\widehat F(k)}{2\pi i\lambda_k}e_k,
\qquad
u_N=\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i\lambda_k}e_k .
\]
由于 \(|\lambda_k|\ge c\langle k\rangle^{-s}\) 且 \(F\in C^\infty\) 的傅里叶系数速降，故 \(u\in C^\infty_0\) 且 \(N_\alpha u=F\)。并且
\[
\widehat{u_N}(k)=\widehat u(k)\quad(0<|k|\le N),
\qquad
\widehat{u_N}(k)=0\quad(|k|>N).
\]
于是 \(u-u_N\) 只含 \(|k|>N\) 的频率。对任意 \(r\in\mathbb R\)、\(q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=
\sum_{|k|>N}\langle k\rangle^{2r}
\left|\frac{\widehat F(k)}{2\pi(\alpha k_1+k_2)}\right|^2\\
&\le
\frac1{4\pi^2c^2}
\sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2 .
\end{aligned}
\]
当 \(|k|>N\) 时，
\[
\langle k\rangle^2=1+|k|^2>1+N^2,
\]
故对 \(q\ge0\)，
\[
\langle k\rangle^{-2q}\le (1+N^2)^{-q}.
\]
因此
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&\le
\frac{(1+N^2)^{-q}}{4\pi^2c^2}
\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le
\frac{(1+N^2)^{-q}}{4\pi^2c^2}
\|F\|_{H^{r+s+q}}^2 .
\end{aligned}
\]
开方得
\[
\boxed{
\|u-u_N\|_{H^r}
\le
\frac1{2\pi c}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}}.
}
\]

---

## S3：固定频带内改变方向

对 \(F\in H_N\)，由 S1，
\[
\widehat{u_\alpha}(k)=\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)},
\qquad
\widehat{u_\beta}(k)=\frac{\widehat F(k)}{2\pi i(\beta k_1+k_2)}.
\]
于是对 \(0<|k|\le N\)，
\[
\begin{aligned}
\widehat{u_\alpha-u_\beta}(k)
&=
\frac{\widehat F(k)}{2\pi i}
\left(
\frac1{\alpha k_1+k_2}
-\frac1{\beta k_1+k_2}
\right)\\
&=
\frac{\widehat F(k)}{2\pi i}
\frac{(\beta-\alpha)k_1}
{(\alpha k_1+k_2)(\beta k_1+k_2)} .
\end{aligned}
\]
由小除数下界及 \(|k_1|\le |k|\le N\)，
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
|\widehat F(k)|.
\]
乘以 \(\langle k\rangle^r\)、平方求和，得
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
\|F\|_{H^r}.
}
\]

---

## S4：整体对象、全部损失指数与 \(\alpha_*=\sqrt2-1\)

记
\[
\lambda_k=\alpha k_1+k_2,\qquad
N_\alpha e_k=2\pi i\lambda_k e_k .
\]
对无理 \(\alpha\)，\(\lambda_k\ne0\ (k\ne0)\)。若 \(N_\alpha u=F\) 且 \(u\) 零均值，则形式解必为
\[
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\lambda_k}\quad(k\ne0),
\qquad
\widehat u(0)=0.
\]
因此光滑零均值解若存在必唯一。

### 4.1 Sobolev 损失与小除数

对 \(s\ge0\)，定义
\[
d_s(\alpha)
=
\inf_{0\ne k\in\mathbb Z^2}
\langle k\rangle^s|\alpha k_1+k_2|.
\]
则对给定的 \(s\)，对所有 \(r\in\mathbb R\) 成立
\[
\exists C_{\alpha,r,s}<\infty\quad
\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}
\qquad(u\in C^\infty_0)
\]
当且仅当
\[
\boxed{d_s(\alpha)>0.}
\]
事实上，若 \(d_s>0\)，则
\[
|\widehat u(k)|
=
\frac{|\widehat F(k)|}{2\pi|\lambda_k|}
\le
\frac{\langle k\rangle^s}{2\pi d_s}|\widehat F(k)|,
\]
其中 \(F=N_\alpha u\)，从而
\[
\|u\|_{H^r}
\le
\frac1{2\pi d_s}\|F\|_{H^{r+s}}.
\]
反过来，取 \(u=e_k\)，得
\[
\frac{\|e_k\|_{H^r}}{\|N_\alpha e_k\|_{H^{r+s}}}
=
\frac1{2\pi\langle k\rangle^s|\lambda_k|},
\]
故若估计成立，则 \(d_s\ge(2\pi C_{\alpha,r,s})^{-1}\)。

记
\[
\|q\alpha\|_{\mathbb Z}
=
\min_{m\in\mathbb Z}|q\alpha-m|,
\qquad
b_s(\alpha)
=
\inf_{q\ge1}q^s\|q\alpha\|_{\mathbb Z}.
\]
则
\[
\boxed{
d_s(\alpha)>0
\iff
b_s(\alpha)>0.
}
\]
证明如下。

若 \(d_s>0\)，对每个 \(q\ge1\) 取 \(p\in\mathbb Z\) 使 \(\|q\alpha\|=|q\alpha-p|\)，令 \(k=(q,-p)\)。因为
\[
|p|\le |\alpha|q+\frac12\le (|\alpha|+1)q,
\]
存在常数 \(C_\alpha\) 使 \(\langle(q,-p)\rangle\le C_\alpha q\)。于是
\[
q^s\|q\alpha\|
=
q^s|q\alpha-p|
\ge
d_s q^s\langle(q,-p)\rangle^{-s}
\ge
d_s C_\alpha^{-s}>0.
\]
反之，若 \(b_s>0\)，对 \(k=(q,m)\)：

- 若 \(q=0\)，则 \(k\ne0\Rightarrow |m|\ge1\)，故
  \[
  \langle k\rangle^s|\alpha k_1+k_2|
  =
  \langle k\rangle^s|m|\ge1.
  \]
- 若 \(q\ne0\) 且 \(|m|\le C_\alpha|q|\)，则 \(\langle k\rangle\le C'_\alpha|q|\)，并且
  \[
  |q\alpha+m|\ge \|q\alpha\|
  \ge b_s|q|^{-s}
  \ge b_s(C'_\alpha)^{-s}\langle k\rangle^{-s}.
  \]
- 若 \(q\ne0\) 且 \(|m|>C_\alpha|q|\)（取 \(C_\alpha=2(1+|\alpha|)\)），则
  \[
  |q\alpha+m|\ge |m|-|\alpha||q|\ge \frac12|m|,
  \]
  且 \(\langle k\rangle\le C|m|\)，故
  \[
  \langle k\rangle^s|q\alpha+m|\ge c_s'>0.
  \]

于是 \(d_s>0\iff b_s>0\)。

### 4.2 可逆性定理

定义无理逼近指数
\[
\mu(\alpha)
=
\sup\left\{
\nu\ge0:
\left|\alpha-\frac pq\right|<q^{-\nu}
\text{ 对无穷多组 }(p,q),\ q\ge1,\text{ 成立}
\right\}.
\]
等价地，\(\mu(\alpha)=\infty\) 当且仅当 \(\alpha\) 为 Liouville 数。

结论为
\[
\boxed{
N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)
\text{ 为双射}
\iff
\alpha\notin\mathbb Q\ \text{且}\ \mu(\alpha)<\infty.
}
\]

证明：

1. 若 \(\alpha=p/q\in\mathbb Q\)，取 \(k=(q,-p)\ne0\)，则
   \[
   \alpha k_1+k_2=0,
   \]
   故 \(N_\alpha e_k=0\)，\(N_\alpha\) 不单射；同时任何像函数在频率 \(k\) 处的傅里叶系数恒为 \(0\)，故 \(e_k\) 不在像中，不满足满射。

2. 若 \(\alpha\notin\mathbb Q\)，则 \(N_\alpha\) 在 \(C^\infty_0\) 上单射：\(N_\alpha u=0\) 迫使 \(\widehat u(k)=0\ (k\ne0)\)，零均值又给出 \(\widehat u(0)=0\)。

3. 若 \(\mu(\alpha)<\infty\)，取 \(s>\mu(\alpha)-1\)。由定义，存在 \(\nu\) 使
   \[
   \mu(\alpha)<\nu<s+1.
   \]
   只有有限多组 \((p,q)\) 满足
   \[
   \left|\alpha-\frac pq\right|<q^{-\nu}.
   \]
   因此对充分大的 \(q\) 及所有 \(p\)，
   \[
   \left|\alpha-\frac pq\right|\ge q^{-\nu},
   \]
   从而
   \[
   q^s\|q\alpha\|
   =
   q^{s+1}\left|\alpha-\frac pq\right|
   \ge q^{s+1-\nu}\to\infty.
   \]
   有限个初始 \(q\) 上的值均为正，故 \(b_s(\alpha)>0\)，进而 \(d_s(\alpha)>0\)。于是形式解满足
   \[
   |\widehat u(k)|
   \le
   \frac1{2\pi d_s}\langle k\rangle^s|\widehat F(k)|.
   \]
   \(F\in C^\infty\) 的傅里叶系数速降，故 \(\widehat u(k)\) 也速降，\(u\in C^\infty_0\)。因此 \(N_\alpha\) 满射；结合单射性，为双射。

4. 若 \(\mu(\alpha)=\infty\)，则对任意 \(s\ge0\)，\(b_s(\alpha)=0\)。事实上取 \(\nu>s+1\)，存在无穷多组 \((p,q)\) 使
   \[
   \left|\alpha-\frac pq\right|<q^{-\nu},
   \]
   于是
   \[
   q^s\|q\alpha\|
   \le
   q^{s+1}\left|\alpha-\frac pq\right|
   <
   q^{s+1-\nu}\to0.
   \]
   故 \(d_s(\alpha)=0\) 对所有 \(s\ge0\) 成立。

   此时可构造 \(F\in C^\infty_0\) 使 \(N_\alpha u=F\) 无光滑零均值解。对每个 \(n\)，由 \(d_n(\alpha)=0\)，可取 \(k_n\ne0\)，且可归纳选取使 \(|k_n|\to\infty\)、各 \(k_n\) 互不相同，并满足
   \[
   |\alpha k_{n,1}+k_{n,2}|
   <
   2^{-n}\langle k_n\rangle^{-n}.
   \]
   令
   \[
   F
   =
   \sum_{n=1}^\infty
   2\pi i(\alpha k_{n,1}+k_{n,2})e_{k_n}.
   \]
   对任意多重指标 \(|\beta|=M\)，有
   \[
   \sum_{n=1}^\infty
   \left|
   (2\pi i k_n)^\beta
   2\pi i(\alpha k_{n,1}+k_{n,2})
   \right|
   \le
   C_M
   \sum_{n=1}^\infty
   |k_n|^M 2^{-n}\langle k_n\rangle^{-n}
   <\infty,
   \]
   因为当 \(n>M\) 时 \(|k_n|^M\langle k_n\rangle^{-n}\le1\)，而前有限项为有限和。因此 \(F\in C^\infty\)，且无常数项，\(F\in C^\infty_0\)。

   若 \(u\in C^\infty_0\) 满足 \(N_\alpha u=F\)，则在频率 \(k_n\) 处必有
   \[
   2\pi i(\alpha k_{n,1}+k_{n,2})\widehat u(k_n)
   =
   \widehat F(k_n)
   =
   2\pi i(\alpha k_{n,1}+k_{n,2}),
   \]
   故
   \[
   \widehat u(k_n)=1\qquad(n=1,2,\dots).
   \]
   但 \(|k_n|\to\infty\)，与 Riemann–Lebesgue 引理 \(\widehat u(k)\to0\) 矛盾。故该 \(F\) 无光滑零均值解，\(N_\alpha\) 不满射。

定理得证。

### 4.3 全部允许的 Sobolev 损失 \(s\)

由 4.1，对无理 \(\alpha\)，
\[
\boxed{
S(\alpha)
=
\{s\ge0:d_s(\alpha)>0\}
=
\{s\ge0:b_s(\alpha)>0\}.
}
\]
若 \(\alpha\in\mathbb Q\)，则存在 \(k\ne0\) 使 \(\lambda_k=0\)，取 \(u=e_k\) 得 \(N_\alpha u=0\) 而 \(\|u\|_{H^r}>0\)，故无任何 \(s\) 可行，即 \(S(\alpha)=\varnothing\)。

若 \(\alpha\notin\mathbb Q\)：

- 若 \(\mu(\alpha)=\infty\)，则如上 \(b_s(\alpha)=0\) 对所有 \(s\ge0\) 成立，故
  \[
  \boxed{S(\alpha)=\varnothing.}
  \]

- 若 \(\mu(\alpha)<\infty\)，令
  \[
  s_0=\mu(\alpha)-1.
  \]
  若 \(s>s_0\)，取 \(\nu\) 使 \(\mu(\alpha)<\nu<s+1\)，则只有有限多组 \((p,q)\) 满足 \(|\alpha-p/q|<q^{-\nu}\)。于是对充分大的 \(q\) 及所有 \(p\)，
  \[
  q^s\|q\alpha\|
  =
  q^{s+1}\left|\alpha-\frac pq\right|
  \ge q^{s+1-\nu},
  \]
  从而 \(b_s(\alpha)>0\)，即 \(s\in S(\alpha)\)。

  若 \(s<s_0\)，取 \(\nu\) 使
  \[
  s+1<\nu<\mu(\alpha).
  \]
  则存在无穷多组 \((p,q)\) 满足 \(|\alpha-p/q|<q^{-\nu}\)，沿此序列
  \[
  q^s\|q\alpha\|
  \le
  q^{s+1-\nu}\to0,
  \]
  故 \(b_s(\alpha)=0\)，即 \(s\notin S(\alpha)\)。

  在临界点 \(s_0=\mu(\alpha)-1\)，是否允许完全由常数下界决定：
  \[
  s_0\in S(\alpha)
  \iff
  b_{s_0}(\alpha)
  =
  \inf_{q\ge1}q^{s_0}\|q\alpha\|_{\mathbb Z}>0.
  \]
  因此
  \[
  \boxed{
  S(\alpha)
  =
  (s_0,\infty)
  \cup
  \begin{cases}
  \{s_0\},& b_{s_0}(\alpha)>0,\\
  \varnothing,& b_{s_0}(\alpha)=0.
  \end{cases}
  }
  \]
  等价地，
  \[
  S(\alpha)=[s_0,\infty)
  \quad\text{若 }b_{s_0}(\alpha)>0,
  \qquad
  S(\alpha)=(s_0,\infty)
  \quad\text{若 }b_{s_0}(\alpha)=0.
  \]
  在 \(s\in S(\alpha)\) 时，可取
  \[
  C_{\alpha,r,s}=(2\pi d_s(\alpha))^{-1},
  \]
  该常数实际上不依赖于 \(r\)。

### 4.4 \(\alpha_*=\sqrt2-1\) 时的最小损失

写 \(k=(q,m)\)，令 \(n=q-m\)。则
\[
\alpha_*k_1+k_2
=
(\sqrt2-1)q+m
=
\sqrt2 q-n .
\]
若 \(q=0\)，则 \(k\ne0\Rightarrow |m|\ge1\)。

若 \(q\ne0\)，则
\[
n^2-2q^2\in\mathbb Z\setminus\{0\},
\]
否则 \(\sqrt2=n/q\in\mathbb Q\)。故
\[
|n^2-2q^2|\ge1.
\]
于是
\[
\begin{aligned}
|\alpha_*k_1+k_2|
&=
|\sqrt2 q-n|
=
\frac{|n^2-2q^2|}{|n+\sqrt2 q|}\\
&\ge
\frac1{|n|+\sqrt2|q|}
\ge
\frac1{(2+\sqrt2)\langle k\rangle}
>
\frac1{3\sqrt2\langle k\rangle}.
\end{aligned}
\]
因此
\[
\boxed{
|\alpha_*k_1+k_2|
\ge
c_0\langle k\rangle^{-1},
\qquad
c_0=\frac1{3\sqrt2}>0,
}
\]
对所有 \(k\ne0\) 成立。故 \(s=1\) 是允许的，且
\[
\|u\|_{H^r}
\le
\frac1{2\pi c_0}\|N_{\alpha_*}u\|_{H^{r+1}}
\qquad(u\in C^\infty_0).
\]

另一方面，取 Pell 方程
\[
n_j^2-2q_j^2=\pm1
\]
的无穷多组解，使 \(q_j\to\infty\)。令
\[
k_j=(q_j,q_j-n_j).
\]
则
\[
|\alpha_*k_{j,1}+k_{j,2}|
=
|\sqrt2 q_j-n_j|
=
\frac1{n_j+\sqrt2 q_j}
\le
\frac{C}{q_j},
\]
且 \(\langle k_j\rangle\le C' q_j\)。故对任意 \(s<1\)，
\[
d_s(\alpha_*)
\le
\langle k_j\rangle^s|\alpha_*k_{j,1}+k_{j,2}|
\le
C'' q_j^{s-1}\to0.
\]
所以 \(s<1\) 均不允许。因此
\[
\boxed{
S(\alpha_*)=[1,\infty),
\qquad
s_{\min}=1,
}
\]
并且最小损失 \(s=1\) 确实取到。

### 4.5 \(\alpha_*\) 时的 \(C^m\) 估计

结论：对每个 \(m\in\mathbb N_0\)，存在与 \(F\) 无关的 \(C_m<\infty\)，使
\[
\boxed{
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le
C_m\|F\|_{C^{m+4}}
\qquad(F\in C^\infty_0(\mathbb T^2)).
}
\]

证明。由 \(s=1\) 的小除数下界，
\[
|\widehat{N_{\alpha_*}^{-1}F}(k)|
=
\frac{|\widehat F(k)|}{2\pi|\alpha_*k_1+k_2|}
\le
\frac1{2\pi c_0}\langle k\rangle|\widehat F(k)|
\qquad(k\ne0).
\]
若 \(F\in C^{m+4}\)，标准傅里叶系数估计给出
\[
|\widehat F(k)|
\le
C_{m+4}\|F\|_{C^{m+4}}(1+|k|)^{-(m+4)}
\qquad(k\ne0).
\]
于是对 \(k\ne0\)，
\[
|\widehat{N_{\alpha_*}^{-1}F}(k)|
\le
C'_m\|F\|_{C^{m+4}}|k|^{-(m+3)}.
\]
对任意多重指标 \(|\beta|\le m\)，
\[
\begin{aligned}
|\partial^\beta N_{\alpha_*}^{-1}F(y)|
&\le
(2\pi)^m
\sum_{k\ne0}|k|^m
|\widehat{N_{\alpha_*}^{-1}F}(k)|\\
&\le
C''_m\|F\|_{C^{m+4}}
\sum_{k\ne0}|k|^{-3}.
\end{aligned}
\]
二维格点满足
\[
\sum_{0\ne k\in\mathbb Z^2}|k|^{-3}<\infty.
\]
故
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le
C_m\|F\|_{C^{m+4}}.
\]
所问估计成立。

---

## S5：邻近方向的一致估计

结论：**不存在**这样的开区间 \(J\ni\alpha_*\)、有限 \(s\ge0\) 和有限 \(C<\infty\)，使得对所有无理 \(\alpha\in J\) 及所有 \(u\in C^\infty_0\) 同时有
\[
\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}.
\]
因此题中给出的肯定式断言不成立。

证明。任意固定 \(J\ni\alpha_*\)、有限 \(s\ge0\)、有限 \(C<\infty\)。取 \(\varepsilon>0\) 使
\[
(\alpha_*-\varepsilon,\alpha_*+\varepsilon)\subset J.
\]
取足够大的整数 \(Q\) 及整数 \(p\)，使
\[
\left|\frac pQ-\alpha_*\right|<\frac{\varepsilon}{4}.
\]
令 \(k=(Q,-p)\)。存在只依赖于 \(\alpha_*\) 和 \(\varepsilon\) 的常数 \(C_1\)，使
\[
\langle k\rangle\le C_1 Q.
\]
取无理数 \(\delta\)，满足
\[
0<|\delta|<
\min\left\{
\frac{\varepsilon}{4},
\frac1{4\pi C C_1^s Q^{s+1}}
\right\}.
\]
令
\[
\alpha=\frac pQ+\delta.
\]
则 \(\alpha\in J\) 且 \(\alpha\) 无理。取
\[
u=e_k.
\]
则 \(u\in C^\infty_0\)，且 \(\|u\|_{L^2}=1\)。同时
\[
N_\alpha u
=
2\pi i(\alpha Q-p)e_k
=
2\pi i\delta Q\,e_k.
\]
因此
\[
\begin{aligned}
\|N_\alpha u\|_{H^s}
&=
2\pi|\delta|Q\langle k\rangle^s\\
&\le
2\pi|\delta|Q(C_1Q)^s
<
\frac1{2C}.
\end{aligned}
\]
于是
\[
C\|N_\alpha u\|_{H^s}<\frac12<1=\|u\|_{L^2},
\]
与所要求的一致估计矛盾。故不存在这样的 \(J,s,C\)。

---

## S6：具体 Liouville 方向上的不可解数据

取
\[
\alpha=\sum_{n=1}^{\infty}10^{-n!}.
\]

### 6.1 \(\alpha\) 是无理数

令
\[
\alpha_n=\sum_{j=1}^{n}10^{-j!}.
\]
则 \(\alpha_n\) 的分母整除 \(10^{n!}\)，且
\[
0<\alpha-\alpha_n
=
\sum_{j=n+1}^{\infty}10^{-j!}
<
2\cdot10^{-(n+1)!}.
\]
若 \(\alpha=p/q\in\mathbb Q\)，则 \(\alpha-\alpha_n\) 是非零有理数，其分母整除 \(q10^{n!}\)，故
\[
|\alpha-\alpha_n|
\ge
\frac1{q10^{n!}}.
\]
但对充分大的 \(n\)，
\[
2\cdot10^{-(n+1)!}
<
\frac1{q10^{n!}},
\]
因为
\[
2q<10^{(n+1)!-n!}=10^{n\cdot n!}.
\]
矛盾。所以 \(\alpha\notin\mathbb Q\)。

### 6.2 构造同一个光滑零均值 \(F\)

令
\[
q_n=10^{n!},
\qquad
p_n=\sum_{j=1}^{n}10^{n!-j!}\in\mathbb Z.
\]
则
\[
\frac{p_n}{q_n}
=
\sum_{j=1}^{n}10^{-j!},
\]
且
\[
\lambda_n
:=
\alpha q_n-p_n
=
\sum_{j=n+1}^{\infty}10^{n!-j!}.
\]
第一项为
\[
10^{n!-(n+1)!}
=
10^{-n\cdot n!},
\]
故
\[
0<\lambda_n<2\cdot10^{-n\cdot n!}.
\]
令
\[
k_n=(q_n,-p_n)\in\mathbb Z^2.
\]
则
\[
\alpha k_{n,1}+k_{n,2}
=
\alpha q_n-p_n
=
\lambda_n.
\]
定义单一的 Fourier 级数
\[
\boxed{
F(y)
=
\sum_{n=1}^{\infty}
2\pi i\lambda_n
e^{2\pi i k_n\cdot y}.
}
\]

先证 \(F\in C^\infty_0\)。因为 \(p_n<q_n\)，故
\[
|k_n|\le2q_n.
\]
对任意多重指标 \(|\beta|=M\)，
\[
\begin{aligned}
\sum_{n=1}^{\infty}
\left|
(2\pi i k_n)^\beta
\,2\pi i\lambda_n
\right|
&\le
C_M
\sum_{n=1}^{\infty}
\lambda_n|k_n|^M\\
&\le
C_M
\sum_{n=1}^{\infty}
10^{-n\cdot n!}(2q_n)^M\\
&=
C'_M
\sum_{n=1}^{\infty}
10^{-(n-M)n!}
<\infty.
\end{aligned}
\]
故各阶导数级数绝对一致收敛，\(F\in C^\infty(\mathbb T^2)\)。又所有 \(k_n\ne0\)，常数项为零，故
\[
\int_{\mathbb T^2}F=0,
\]
即 \(F\in C^\infty_0(\mathbb T^2)\)。

最后证明 \(N_\alpha u=F\) 无光滑零均值解。若存在 \(u\in C^\infty_0\) 满足 \(N_\alpha u=F\)，则在每个频率 \(k_n\) 处，
\[
2\pi i(\alpha k_{n,1}+k_{n,2})\widehat u(k_n)
=
\widehat F(k_n)
=
2\pi i\lambda_n.
\]
由于 \(\lambda_n\ne0\)，得到
\[
\boxed{
\widehat u(k_n)=1
\qquad(n=1,2,\dots).
}
\]
但 \(|k_n|\to\infty\)，而光滑函数满足 Riemann–Lebesgue 引理 \(\widehat u(k)\to0\)，矛盾。

因此这个同一个函数 \(F\) 满足
\[
\boxed{
F\in C^\infty_0(\mathbb T^2),
\qquad
N_\alpha u=F
\text{ 不存在 }u\in C^\infty_0(\mathbb T^2)\text{ 解}.
}
\]

---

本题明确无需 Lean，原题亦未要求源码交付，故没有命名源码文件或声明对应表需要提交。