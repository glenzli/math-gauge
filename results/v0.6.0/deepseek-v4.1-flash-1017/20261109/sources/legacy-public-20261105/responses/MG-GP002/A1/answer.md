记号约定：令
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad \lambda_k=\alpha k_1+k_2,
\]
则
\[
N_\alpha e_k=2\pi i\lambda_k e_k.
\]
在 S1–S3 中也用此记号。

---

## S1：有限频带上的逆

设
\[
H_N=\left\{\sum_{0<|k|\le N}a_k e_k\right\}.
\]
因为 \(\alpha\notin\mathbb Q\)，所以对一切 \(0\ne k\in\mathbb Z^2\) 有
\[
\lambda_k=\alpha k_1+k_2\ne0.
\]
故 \(N_\alpha:H_N\to H_N\) 是对角算子。其逆为
\[
\boxed{
(N_\alpha|_{H_N})^{-1}F
=
\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}\,e_k
}
\]
其中 \(F=\sum_{0<|k|\le N}\widehat F(k)e_k\)。

对任意 \(r\in\mathbb R\)，算子 \(N_\alpha|_{H_N}\) 在傅里叶基上对角，故逆算子范数为最大对角元模：
\[
\boxed{
\left\|(N_\alpha|_{H_N})^{-1}\right\|_{\mathcal L(H^r,H^r)}
=
\frac1{2\pi}
\max_{0<|k|\le N}
\frac1{|\alpha k_1+k_2|}
=
\frac1{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.
}
\]
等号取到于使 \(|\alpha k_1+k_2|\) 最小的频率 \(k\) 所对应的单频函数。

---

## S2：有算术界时的截断误差

令 \(P_NF=F_N\) 为投影
\[
F_N=\sum_{0<|k|\le N}\widehat F(k)e_k.
\]
由假设
\[
|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}\qquad(k\ne0),
\]
可定义全解
\[
u=\sum_{k\ne0}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e_k.
\]
由于 \(F\in C^\infty\)，其傅里叶系数速降；又
\[
|\widehat u(k)|
\le \frac1{2\pi c}\langle k\rangle^s|\widehat F(k)|,
\]
故 \(\widehat u(k)\) 仍速降，\(u\in C^\infty_0(\mathbb T^2)\)，且 \(N_\alpha u=F\)。

有限频带解 \(u_N=(N_\alpha|_{H_N})^{-1}F_N\) 正好是全解在频带 \(0<|k|\le N\) 上的投影：
\[
\widehat{u_N}(k)=\widehat u(k)\quad(0<|k|\le N),\qquad
\widehat{u_N}(k)=0\quad(|k|>N).
\]
因此 \(u-u_N\) 只含 \(|k|>N\) 的频率。对任意 \(r\in\mathbb R\)、\(q\ge0\)，有
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}\langle k\rangle^{2r}
\left|\frac{\widehat F(k)}{2\pi(\alpha k_1+k_2)}\right|^2\\
&\le \frac1{(2\pi c)^2}
\sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2.
\end{aligned}
\]
当 \(|k|>N\) 时，
\[
\langle k\rangle^2=1+|k|^2\ge 1+(N+1)^2>1+N^2,
\]
故对 \(q\ge0\)，
\[
\langle k\rangle^{-2q}\le(1+N^2)^{-q}.
\]
于是
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}
\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}
\|F\|_{H^{r+s+q}}^2.
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
这正是所要求的不等式。

---

## S3：固定频带内改变方向

对 \(F\in H_N\)，由 S1，
\[
\widehat{u_\alpha}(k)=\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)},\qquad
\widehat{u_\beta}(k)=\frac{\widehat F(k)}{2\pi i(\beta k_1+k_2)}.
\]
因此对 \(0<|k|\le N\)，
\[
\begin{aligned}
\widehat{u_\alpha-u_\beta}(k)
&=\frac{\widehat F(k)}{2\pi i}
\left(
\frac1{\alpha k_1+k_2}
-\frac1{\beta k_1+k_2}
\right)\\
&=\frac{\widehat F(k)}{2\pi i}
\frac{(\beta-\alpha)k_1}
{(\alpha k_1+k_2)(\beta k_1+k_2)}.
\end{aligned}
\]
利用小除数下界与 \(|k_1|\le |k|\le N\)，
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
|\widehat F(k)|.
\]
乘以 \(\langle k\rangle^r\) 并求和：
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le
\frac{|\alpha-\beta|N}{2\pi\delta^2}
\|F\|_{H^r}.
}
\]
这正是 $S3$ 的结论。

---

## S4：整体对象、全部损失指数与 \(\alpha_*=\sqrt2-1\)

### 4.1 傅里叶对角化

对无理 \(\alpha\)，对所有 \(0\ne k\in\mathbb Z^2\)，\(\lambda_k\ne0\)。形式解必为
\[
\boxed{
\widehat u(k)=\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}
\quad(k\ne0),\qquad \widehat u(0)=0.
}
\]
因此若光滑零均值解存在，它必唯一。

### 4.2 无理逼近指数与可逆性

定义 \(\alpha\) 的无理逼近指数
\[
\mu(\alpha)
=
\sup\left\{
\nu\ge0:
|\alpha-\frac pq|<q^{-\nu}
\text{ 对无穷多个 }p/q\ (q\ge1)\text{ 成立}
\right\}.
\]
无理数满足 \(\mu(\alpha)\ge2\)。所谓 Liouville 数就是 \(\mu(\alpha)=+\infty\)。

对 \(s\ge0\)，记
\[
\|\alpha q\|_{\mathbb Z}=\min_{m\in\mathbb Z}|\alpha q-m|.
\]
有基本等价：
\[
\boxed{
\exists c_s>0,\quad
|\alpha k_1+k_2|\ge c_s\langle k\rangle^{-s}\quad\forall k\ne0
}
\]
当且仅当
\[
\boxed{
\inf_{q\ge1}q^s\|\alpha q\|_{\mathbb Z}>0.
}
\]
证明如下。

- 若小除数下界成立，取 \(k=(q,-p)\)，其中 \(p\) 使 \(|\alpha q-p|=\|\alpha q\|_{\mathbb Z}\)。此时
  \[
  \langle(q,-p)\rangle\le Cq,
  \]
  故
  \[
  q^s\|\alpha q\|_{\mathbb Z}
  =q^s|\alpha q-p|
  \ge c_s q^s\langle(q,-p)\rangle^{-s}
  \ge c_sC^{-s}>0.
  \]
- 反之，若 \(\inf_q q^s\|\alpha q\|>0\)。对 \(k=(q,m)\)：
  - \(q=0\) 时，\(|\alpha k_1+k_2|=|m|\ge1\)，自动有下界；
  - \(q\ne0\) 且 \(|m|\lesssim |q|\) 时，
    \[
    |\alpha q+m|\ge\|\alpha q\|\ge b_s|q|^{-s}
    \ge c_s'\langle k\rangle^{-s};
    \]
  - \(q\ne0\) 且 \(|m|\gg|q|\) 时，
    \(|\alpha q+m|\gtrsim |m|\gtrsim \langle k\rangle\)，
    更强。

故二者等价。

**可逆性定理。**
\[
\boxed{
N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)
\text{ 为双射}
\iff
\alpha\notin\mathbb Q
\ \text{且}\ \mu(\alpha)<\infty.
}
\]
也就是说，\(\alpha\) 是“非 Liouville 无理数”。

证明：

1. 若 \(\alpha=p/q\in\mathbb Q\)，取 \(k=(q,-p)\ne0\)，则
   \[
   \alpha k_1+k_2=0.
   \]
   因此 \(N_\alpha e_k=0\)，\(N_\alpha\) 不单射；同时 \(F=e_k\) 也不可能属于 \(N_\alpha\) 的像，因为 \(N_\alpha u\) 在频率 \(k\) 处的傅里叶系数恒为 \(0\)。

2. 若 \(\alpha\) 无理，则 \(N_\alpha\) 在 \(C^\infty_0\) 上单射：
   \(N_\alpha u=0\) 迫使
   \[
   \widehat u(k)=0\quad(k\ne0),
   \]
   而零均值又给出 \(\widehat u(0)=0\)。

3. 若 \(\mu(\alpha)<\infty\)，取任意 \(s>\mu(\alpha)-1\)。由上面等价性和 \(\mu\) 的定义，存在 \(c_s>0\) 使
   \[
   |\alpha k_1+k_2|\ge c_s\langle k\rangle^{-s}.
   \]
   于是形式解满足
   \[
   |\widehat u(k)|\le \frac1{2\pi c_s}
   \langle k\rangle^s|\widehat F(k)|.
   \]
   因 \(F\in C^\infty\)，\(\widehat F(k)\) 速降，故 \(\widehat u(k)\) 也速降；所以
   \[
   u=\sum_{k\ne0}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e_k
   \]
   定义了一个 \(C^\infty_0\) 函数，并且 \(N_\alpha u=F\)。

4. 若 \(\mu(\alpha)=\infty\)，则不存在有限 \(s\) 使小除数多项式下界成立。此时可构造 \(F\in C^\infty_0\) 使形式解不光滑：
   对每个 \(n\)，因
   \[
   \inf_{k\ne0}\langle k\rangle^n|\alpha k_1+k_2|=0,
   \]
   可取互不相同的 \(k_n\)，使 \(|k_n|\to\infty\) 且
   \[
   |\alpha k_{n,1}+k_{n,2}|<2^{-n}\langle k_n\rangle^{-n}.
   \]
   令
   \[
   F=\sum_{n=1}^\infty
   2\pi i(\alpha k_{n,1}+k_{n,2})e_{k_n}.
   \]
   对任意多重指标 \(|\beta|=M\)，
   \[
   \sum_n
   2\pi|\alpha k_{n,1}+k_{n,2}|\,|2\pi k_n|^M
   \le C_M\sum_{n>M}2^{-n}<\infty,
   \]
   故 \(F\in C^\infty_0\)。但形式解的傅里叶系数满足
   \[
   \widehat u(k_n)=1\qquad(n=1,2,\dots),
   \]
   而 \(|k_n|\to\infty\)。光滑函数的傅里叶系数必须趋于 \(0\)（Riemann–Lebesgue 引理），矛盾。因此该 \(F\) 没有光滑零均值解。

### 4.3 全部允许的 Sobolev 损失 \(s\)

由傅里叶对角化，
\[
\|u\|_{H^r}^2
=
\sum_{k\ne0}
\langle k\rangle^{2r}
\frac{|\widehat F(k)|^2}{4\pi^2|\alpha k_1+k_2|^2}.
\]
因此不等式
\[
\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}
\qquad\forall u\in C^\infty_0
\]
对所有 \(r\) 成立，当且仅当
\[
\boxed{
\exists c_s>0,\quad
|\alpha k_1+k_2|\ge c_s\langle k\rangle^{-s}\quad\forall k\ne0.
}
\]
若此条件成立，则可取
\[
C_{\alpha,r,s}=(2\pi c_s)^{-1},
\]
且这个常数与 \(r\) 无关。

于是允许的损失集合为
\[
\boxed{
\mathcal S(\alpha)
=
\left\{
s\ge0:
\inf_{k\ne0}\langle k\rangle^s|\alpha k_1+k_2|>0
\right\}.
}
\]
等价地，用 \(\|\alpha q\|_{\mathbb Z}\) 表示，
\[
\boxed{
s\in\mathcal S(\alpha)
\iff
\inf_{q\ge1}q^s\|\alpha q\|_{\mathbb Z}>0.
}
\]

将它用 \(\mu(\alpha)\) 完整写出。若 \(\mu(\alpha)=\infty\)，则
\[
\boxed{\mathcal S(\alpha)=\varnothing.}
\]
若 \(\mu(\alpha)<\infty\)，令
\[
s_0=\mu(\alpha)-1.
\]
则
\[
\boxed{
(s_0,\infty)\subseteq\mathcal S(\alpha)
\subseteq[s_0,\infty).
}
\]
更精确地，
\[
\boxed{
\mathcal S(\alpha)
=
(s_0,\infty)
\ \cup
\begin{cases}
\{s_0\},
&
\displaystyle
\inf_{q\ge1}q^{s_0}\|\alpha q\|_{\mathbb Z}>0,\\[1.2ex]
\varnothing,
&
\displaystyle
\inf_{q\ge1}q^{s_0}\|\alpha q\|_{\mathbb Z}=0.
\end{cases}
}
\]
事实上：

- 若 \(s>s_0=\mu(\alpha)-1\)，则 \(s+1>\mu(\alpha)\)。按 \(\mu(\alpha)\) 的定义，只有有限多个 \(p/q\) 满足
  \[
  |\alpha-p/q|<q^{-(s+1)}.
  \]
  因此对充分大的 \(q\) 及所有 \(p\)，
  \[
  |\alpha q-p|\ge q^{-s},
  \]
  有限个初始项再调整常数，即得 \(\inf_q q^s\|\alpha q\|>0\)。

- 若 \(s<s_0\)，可取 \(\nu\) 使
  \[
  s+1<\nu<\mu(\alpha).
  \]
  于是存在无穷多个 \(p/q\) 满足
  \[
  |\alpha-p/q|<q^{-\nu}.
  \]
  从而
  \[
  q^s\|\alpha q\|_{\mathbb Z}
  \le q^s|\alpha q-p|
  <q^{s+1-\nu}\to0,
  \]
  所以 \(s\notin\mathcal S(\alpha)\)。

- 临界指数 \(s_0\) 是否可取，正由条件
  \[
  \inf_{q\ge1}q^{s_0}\|\alpha q\|_{\mathbb Z}>0
  \]
  判定。

因此上面的公式给出了全部 \(s\)。

### 4.4 \(\alpha_*=\sqrt2-1\) 时的最小损失

先证明一个对整个 \(\mathbb Z^2\setminus\{0\}\) 成立的小除数估计。

写 \(q=k_1,\ n=q-k_2\)，则
\[
\alpha_*k_1+k_2
=(\sqrt2-1)q+k_2
=\sqrt2 q-n.
\]
若 \(q=0\)，则 \(|\alpha_*k_1+k_2|=|k_2|\ge1\)。

若 \(q\ne0\)，则
\[
n^2-2q^2\in\mathbb Z\setminus\{0\},
\]
因为否则 \(\sqrt2=n/q\in\mathbb Q\)。因此
\[
|n^2-2q^2|\ge1.
\]
于是
\[
\begin{aligned}
|\alpha_*k_1+k_2|
&=|\sqrt2 q-n|\\
&=\frac{|n^2-2q^2|}{|n+\sqrt2 q|}
\ge \frac1{|n|+\sqrt2 |q|}.
\end{aligned}
\]
又有
\[
|n|=|q-k_2|\le |q|+|k_2|\le2\langle k\rangle,
\]
故
\[
|n|+\sqrt2|q|\le 3\sqrt2\,\langle k\rangle.
\]
因此对所有 \(k\ne0\)，
\[
\boxed{
|\alpha_*k_1+k_2|
\ge
\frac1{3\sqrt2\,\langle k\rangle}
=
\frac{c_0}{\langle k\rangle},
\qquad
c_0=\frac1{3\sqrt2}.
}
\]
所以 \(s=1\) 是允许的，且
\[
\boxed{
\|u\|_{H^r}
\le
\frac1{2\pi c_0}
\|N_{\alpha_*}u\|_{H^{r+1}}
\qquad\forall r\in\mathbb R.
}
\]
特别地，\(s=1\) 确实被取到。

再证明 \(s<1\) 不允许。取 Pell 方程
\[
n_j^2-2q_j^2=\pm1
\]
的正整数解 \((n_j,q_j)\)，\(q_j\to\infty\)。令
\[
k_j=(q_j,q_j-n_j).
\]
则
\[
|\alpha_*k_{j,1}+k_{j,2}|
=|\sqrt2 q_j-n_j|
=\frac1{n_j+\sqrt2 q_j}
\le \frac1{\sqrt2 q_j},
\]
且 \(\langle k_j\rangle\asymp q_j\)。因此对任意 \(s<1\)，
\[
|\alpha_*k_{j,1}+k_{j,2}|
\langle k_j\rangle^s
\lesssim q_j^{s-1}\to0.
\]
故 \(s<1\) 时不存在 \(c_s>0\) 使小除数下界成立。等价地，取
\[
u_j=e_{k_j},
\]
则
\[
\frac{\|u_j\|_{H^r}}{\|N_{\alpha_*}u_j\|_{H^{r+s}}}
=
\frac1{2\pi|\alpha_*k_{j,1}+k_{j,2}|\langle k_j\rangle^s}
\to\infty,
\]
所以任何有限常数都不可能。

因此
\[
\boxed{
\mathcal S(\alpha_*)=[1,\infty).
}
\]
即：

- 最小允许损失为
  \[
  \boxed{s_{\min}=1};
  \]
- 这个最小值被取到，因为 \(s=1\) 时确实有上面的整体小除数估计；
- \(s<1\) 一律不允许。

顺便这也说明 \(\mu(\alpha_*)=2\)，因为上面的 \(s=1\) 小除数估计给出
\[
|\alpha_*-p/q|\ge \frac{c'}{q^2},
\]
而 Dirichlet 逼近定理又给出相反方向的无理性指数至少为 \(2\)。

### 4.5 \(\alpha_*\) 时的 \(C^m\) 估计

结论是：对每个 \(m\in\mathbb N_0\)，存在与 \(F\) 无关的 \(C_m<\infty\)，使
\[
\boxed{
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le C_m\|F\|_{C^{m+4}},
\qquad
F\in C^\infty_0(\mathbb T^2).
}
\]

证明如下。由上面的估计，
\[
|\widehat{N_{\alpha_*}^{-1}F}(k)|
=
\frac{|\widehat F(k)|}{2\pi|\alpha_*k_1+k_2|}
\le C|k|\,|\widehat F(k)|
\qquad(k\ne0).
\]
若 \(F\in C^{m+4}\)，则标准傅里叶系数估计给出
\[
|\widehat F(k)|
\le
C_m\|F\|_{C^{m+4}}(1+|k|)^{-(m+4)},
\qquad k\ne0.
\]
于是
\[
|\widehat{N_{\alpha_*}^{-1}F}(k)|
\le
C_m'\|F\|_{C^{m+4}}|k|^{-(m+3)}.
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
C_m''\|F\|_{C^{m+4}}
\sum_{k\ne0}|k|^{-3}.
\end{aligned}
\]
在二维格点中
\[
\sum_{0\ne k\in\mathbb Z^2}|k|^{-3}<\infty,
\]
故
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le C_m\|F\|_{C^{m+4}}.
\]
所以所问的 \(C^m\to C^{m+4}\) 估计成立。

---

## S5：邻近方向的一致估计

结论是：**不存在**这样的开区间 \(J\ni\alpha_*\)、有限 \(s\ge0\) 和有限 \(C\)。

证明。任取开区间 \(J\ni\alpha_*\)、任意有限 \(s\ge0\) 和任意拟定常数 \(C<\infty\)。我们要构造一个无理数 \(\alpha\in J\) 和一个光滑零均值函数 \(u\)，使
\[
\|u\|_{L^2}>C\|N_\alpha u\|_{H^s}.
\]

取 \(J\) 的内部一点 \(\alpha_0\)，令 \(\rho>0\) 使得
\[
(\alpha_0-\rho,\alpha_0+\rho)\subset J.
\]
对任意充分大的整数 \(Q\)，取整数 \(p\) 使
\[
\left|\frac pQ-\alpha_0\right|<\frac\rho2.
\]
于是 \(p/Q\in J\)。取一个足够小的无理数 \(\delta\)，满足
\[
0<|\delta|<
\min\left\{
\frac\rho2,\,
\frac1{4\pi C D_J^s Q^{s+1}}
\right\},
\]
其中 \(D_J\) 是只依赖于 \(J\) 的常数，使得
\[
\langle(Q,-p)\rangle\le D_J Q
\]
对所有充分大的 \(Q\) 成立。令
\[
\alpha=\frac pQ+\delta.
\]
则 \(\alpha\in J\) 且 \(\alpha\notin\mathbb Q\)。

取频率
\[
k=(Q,-p)\ne0,
\qquad
u=e_k.
\]
则 \(u\) 光滑、零均值且 \(\|u\|_{L^2}=1\)。同时
\[
N_\alpha e_k
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
2\pi|\delta|Q\,\langle(Q,-p)\rangle^s\\
&\le
2\pi|\delta|Q\,D_J^sQ^s\\
&<\frac1{2C}.
\end{aligned}
\]
于是
\[
C\|N_\alpha u\|_{H^s}<\frac12<1=\|u\|_{L^2},
\]
与所要求的一致估计矛盾。

所以 S5 的判定为：
\[
\boxed{\text{不存在这样的开区间 }J,\ s,\ C.}
\]

---

## S6：具体 Liouville 方向上的不可解数据

取
\[
\alpha=\sum_{n=1}^{\infty}10^{-n!}.
\]

### 6.1 \(\alpha\) 是无理数

对 \(n\ge1\) 令
\[
\alpha_n=\sum_{j=1}^{n}10^{-j!}.
\]
则
\[
0<\alpha-\alpha_n
=
\sum_{j=n+1}^{\infty}10^{-j!}
<
2\cdot10^{-(n+1)!}.
\]
而 \(\alpha_n\) 的分母整除 \(10^{n!}\)。

若 \(\alpha=p/q\in\mathbb Q\)，则 \(\alpha-\alpha_n\) 是非零有理数，其分母整除 \(q10^{n!}\)，故
\[
\alpha-\alpha_n\ge \frac1{q10^{n!}}.
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
矛盾。因此 \(\alpha\notin\mathbb Q\)。

### 6.2 构造一个光滑零均值 \(F\)，使 \(N_\alpha u=F\) 无光滑零均值解

令
\[
q_n=10^{n!},
\qquad
p_n=\sum_{j=1}^{n}10^{\,n!-j!}.
\]
于是
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
\sum_{j=n+1}^{\infty}10^{\,n!-j!}.
\]
第一项为
\[
10^{\,n!-(n+1)!}
=
10^{-n\cdot n!}.
\]
故
\[
0<\lambda_n<2\cdot10^{-n\cdot n!}.
\]
设
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

现在定义
\[
\boxed{
F(y)
=
\sum_{n=1}^{\infty}
2\pi i\lambda_n
e^{2\pi i k_n\cdot y}.
}
\]
这是一个单一的 Fourier 级数，把所有共振频率 \(k_n\) 同时包含在内。

**\(F\) 光滑且零均值。**
因为 \(q_n=10^{n!}\)，且 \(p_n<q_n\)，故
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
C_M\sum_{n=1}^{\infty}
\lambda_n|k_n|^M\\
&\le
C_M\sum_{n=1}^{\infty}
10^{-n\cdot n!}10^{M n!}\\
&=
C_M\sum_{n=1}^{\infty}
10^{-(n-M)n!}
<\infty.
\end{aligned}
\]
故导数级数绝对一致收敛，\(F\in C^\infty(\mathbb T^2)\)。又所有 \(k_n\ne0\)，所以
\[
\int_{\mathbb T^2}F=0,
\]
即 \(F\in C^\infty_0(\mathbb T^2)\)。

**形式解不光滑。**
若 \(N_\alpha u=F\)，则对每个 \(n\)，
\[
2\pi i\lambda_n\,\widehat u(k_n)
=
\widehat F(k_n)
=
2\pi i\lambda_n.
\]
而 \(\lambda_n\ne0\)，故
\[
\boxed{\widehat u(k_n)=1
\qquad(n=1,2,\dots).}
\]
如果 \(u\) 是光滑零均值解，则其傅里叶系数必须趋于 \(0\)（Riemann–Lebesgue 引理）。但
\[
|k_n|\to\infty,
\qquad
|\widehat u(k_n)|=1
\quad\forall n,
\]
矛盾。

因此这个同一的 \(F\) 满足：
\[
\boxed{
F\in C^\infty_0(\mathbb T^2),
\qquad
N_\alpha u=F
\text{ 没有 }u\in C^\infty_0(\mathbb T^2)\text{ 解}.
}
\]
这就完成了 S6 的构造与证明。