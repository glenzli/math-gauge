记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad d_\alpha(k)=\alpha k_1+k_2.
\]
归一化 Haar 测度下，\((e_k)_{k\in\mathbb Z^2}\) 是 \(L^2\) 的标准正交基，并且
\[
\widehat{N_\alpha v}(k)=2\pi i\,d_\alpha(k)\widehat v(k).
\]
若 \(\alpha\) 无理，则 \(d_\alpha(k)\ne0\) 对每个 \(k\ne0\) 成立。

下面反复使用 Fourier 系数的以下性质：一个序列是某个光滑函数的 Fourier 系数，当且仅当它快速下降，即对每个 \(M\ge0\)，
\(\sup_k\langle k\rangle^M|a_k|<\infty\)。必要性由分部积分得到；充分性由二维格点和
\(\sum_k\langle k\rangle^{-A}<\infty\)（\(A>2\)）保证 Fourier 级数及其各阶导数一致收敛。

## S1　有限频带上的逆

对 \(F\in H_N\)，定义
\[
N_\alpha^{-1}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
所有分母均非零，所以这是 \(H_N\) 上的逆。

对任意 \(r\in\mathbb R\)，其精确算子范数为
\[
\boxed{\displaystyle
\|N_\alpha^{-1}\|_{H^r\to H^r}
=\frac1{2\pi}\max_{0<|k|\le N}\frac1{|d_\alpha(k)|}.}
\]
上界由逐 Fourier 系数估计得到；取达到最大值的频率对应的单个 Fourier 模式，便取到该上界。

## S2　有算术界的截断误差

由条件，
\[
|d_\alpha(k)|^{-1}\le c^{-1}\langle k\rangle^s,\qquad k\ne0.
\]
定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}
\quad(k\ne0).
\]
由于 \(\widehat F\) 快速下降，除数的倒数至多多项式增长，故 \(\widehat u\) 也快速下降。因此 \(u\in C^\infty_0\)，且 \(N_\alpha u=F\)。其唯一性由非零频率上的分母非零得到。

S1 的 \(u_N\) 正是 \(u\) 在 \(0<|k|\le N\) 上的截断。对任意 \(r\in\mathbb R,\ q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&\le \frac1{(2\pi c)^2}
 \sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}
 \sum_{|k|>N}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2.
\end{aligned}
\]
开方即得
\[
\boxed{\displaystyle
\|u-u_N\|_{H^r}
\le (2\pi c)^{-1}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}}.}
\]

## S3　固定频带内改变方向

对 \(0<|k|\le N\)，两方向的解满足
\[
\begin{aligned}
|\widehat u_\alpha(k)-\widehat u_\beta(k)|
&=\frac{|\widehat F(k)|}{2\pi}
\left|\frac1{d_\alpha(k)}-\frac1{d_\beta(k)}\right|\\
&=\frac{|\widehat F(k)|}{2\pi}
 \frac{|\alpha-\beta|\,|k_1|}
 {|d_\alpha(k)d_\beta(k)|}\\
&\le \frac{|\alpha-\beta|N}{2\pi\delta^2}
 |\widehat F(k)|.
\end{aligned}
\]
乘以 Sobolev 权重、求和并开方，得到
\[
\boxed{\displaystyle
\|u_\alpha-u_\beta\|_{H^r}
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4　整体可逆性、全部损失及 \(\alpha_*\)

### 1. 完整分类

对无理数 \(\alpha\)，记
\[
\theta_\alpha(q)=\min_{p\in\mathbb Z}|q\alpha-p|,
\qquad
\tau(\alpha)=\limsup_{q\to\infty}
\frac{\log(1/\theta_\alpha(q))}{\log q}.
\]
这里 \(\theta_\alpha(q)>0\)，并允许 \(\tau(\alpha)=\infty\)。

**定理。**

1. \(N_\alpha:C^\infty_0\to C^\infty_0\) 是双射，当且仅当
   \(\tau(\alpha)<\infty\)，亦即 \(\alpha\) 不是 Liouville 数。此时逆由 Fourier 除法给出，并在 \(C^\infty\) 的 Fréchet 拓扑中连续。
2. 若 \(\tau(\alpha)=\infty\)，则 \(N_\alpha\) 的像是 \(C^\infty_0\) 的真稠密子空间。
3. 对 \(s\ge0\)，所要求估计的最小可能常数，与 \(r\) 无关，精确为
   \[
   \boxed{\displaystyle
   B_{\alpha,s}=\frac1{2\pi}
   \sup_{k\ne0}\frac{\langle k\rangle^{-s}}{|d_\alpha(k)|}.}
   \]
   若此上确界为无穷，则对任何 \(r\) 都不存在有限常数。
4. 全部允许损失构成的集合是
   \[
   \boxed{
   \begin{cases}
   \varnothing,&\tau(\alpha)=\infty,\\[2mm]
   [\tau(\alpha),\infty),
   &\tau(\alpha)<\infty,\
     \inf_{q\ge1}q^{\tau(\alpha)}\theta_\alpha(q)>0,\\[2mm]
   (\tau(\alpha),\infty),
   &\tau(\alpha)<\infty,\
     \inf_{q\ge1}q^{\tau(\alpha)}\theta_\alpha(q)=0.
   \end{cases}}
   \]
   总有 \(\tau(\alpha)\ge1\)。

这里也可用通常的有理逼近指数 \(\mu(\alpha)\) 表述：若 \(\mu\) 定义为使
\(|\alpha-p/q|<q^{-\mu}\) 对无界分母 \(q\) 无限次成立的指数上确界，则
\(\mu(\alpha)=1+\tau(\alpha)\)。端点是否允许，仍需上表中的一致下界判定。

### 2. 分类的证明

先证明对每个 \(s\ge0\)，以下两条件等价：
\[
\inf_{k\ne0}\langle k\rangle^s|d_\alpha(k)|>0,
\qquad
\inf_{q\ge1}q^s\theta_\alpha(q)>0. \tag{1}
\]
若第二个下确界为 \(a>0\)，对 \(k_1\ne0\) 令 \(q=|k_1|\)，便有
\[
|d_\alpha(k)|\ge\theta_\alpha(q)
\ge aq^{-s}\ge a\langle k\rangle^{-s}.
\]
若 \(k_1=0\)，则 \(|d_\alpha(k)|=|k_2|\ge1\)，所以得到第一个条件。

反过来，给定 \(q\)，取最接近 \(q\alpha\) 的整数 \(p\)。此时
\(|p|\le(|\alpha|+\tfrac12)q\)，从而
\(\langle(q,-p)\rangle\le A_\alpha q\)，其中 \(A_\alpha\) 仅依赖于 \(\alpha\)。将第一个条件用于 \((q,-p)\)，便得到第二个条件。

由逐频率比较，
\[
\|u\|_{H^r}\le B_{\alpha,s}\|N_\alpha u\|_{H^{r+s}}.
\]
反过来，将估计用于单个模式 \(u=e_k\)，得知任何可行常数至少为 \(B_{\alpha,s}\)。这证明了定理中的精确常数。

Dirichlet 鸽巢原理给出 \(\tau(\alpha)\ge1\)：对每个 \(Q\)，将 \(0,\alpha,\ldots,Q\alpha\) 的小数部分分到 \(Q\) 个等长区间，可得某个 \(1\le q\le Q\) 使 \(\theta_\alpha(q)\le1/Q\)。当 \(Q\to\infty\) 时，这些 \(q\) 必须无界，故无限多个 \(q\) 满足 \(\theta_\alpha(q)\le1/q\)。

若 \(\tau<\infty\)，由上极限的定义：

- \(s>\tau\) 时，存在 \(a_s>0\) 使 \(\theta_\alpha(q)\ge a_s q^{-s}\) 对所有 \(q\) 成立；
- \(s<\tau\) 时，\(\inf_q q^s\theta_\alpha(q)=0\)；
- \(s=\tau\) 时，是否存在一致下界正是表中所列条件。

若 \(\tau=\infty\)，对每个有限 \(s\) 都有 \(\inf_q q^s\theta_\alpha(q)=0\)。结合 (1) 即得全部损失的分类。

现在证明整体可逆性。若 \(\tau<\infty\)，取 \(s>\tau\)，由 (1) 有多项式小除数下界。S2 的 Fourier 构造便对每个 \(F\in C^\infty_0\) 给出光滑零均值解；唯一性由 \(d_\alpha(k)\ne0\) 得到。

若 \(\tau=\infty\)，则对每个正整数 \(j\)，
\[
\inf_{k\ne0}\langle k\rangle^j|d_\alpha(k)|=0.
\]
因为每个非零频率的除数都非零，可以递归选取互异的 \(k_j\)，使
\[
|k_j|\ge2^j,\qquad |d_\alpha(k_j)|<\langle k_j\rangle^{-j}.
\]
定义同一个函数
\[
F(y)=2\pi i\sum_{j=1}^\infty d_\alpha(k_j)e_{k_j}(y).
\]
对每个固定阶数 \(m\)，从 \(j\ge m+1\) 起，级数中各项的 \(m\) 阶导数由常数乘 \(2^{-j}\) 控制。因此该级数及各阶导数一致收敛，\(F\in C^\infty_0\)。若光滑 \(u\) 满足 \(N_\alpha u=F\)，则
\[
\widehat u(k_j)=1\qquad(j\ge1),
\]
这与 Parseval 定理矛盾。所以此时不满射。

对任意无理 \(\alpha\)，所有零均值三角多项式都属于其像；而光滑函数的 Fourier 截断在每个 \(C^m\) 范数中收敛，故像稠密。

最后说明逆的 Fréchet 连续性。记
\[
S=\left(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}\right)^{1/2}<\infty.
\]
Cauchy–Schwarz 给出
\[
\|v\|_{C^m}\le(2\pi)^m S\|v\|_{H^{m+2}}. \tag{2}
\]
而对整数 \(n\ge0\)，由 Parseval、二项展开及测度归一化，
\[
\|v\|_{H^n}\le3^{n/2}\|v\|_{C^n}. \tag{3}
\]
若有损失 \(s\) 的多项式下界，结合 (2)、S2 的 Fourier 估计及 (3)，对足够大的整数 \(L\) 得
\[
\|N_\alpha^{-1}F\|_{C^m}\le C_{m,L}\|F\|_{C^L},
\]
这正是所需连续性。

### 3. 端点两种情形均可出现

事实上，对每个 \(t\ge1\)，都可构造 \(\tau=t\) 且端点取到或不取到的无理数。说明这一点可表明上表的端点条件不能仅由 \(\tau\) 的数值省略。

取无限正规连分数 \(\gamma=[0;a_1,a_2,\ldots]\)，其中 \(a_n\) 均为正整数，\(a_1=2\)。其渐近分数分母满足
\[
q_{-1}=0,\quad q_0=1,\quad q_{n+1}=a_{n+1}q_n+q_{n-1}.
\]
这种无限连分数定义无理数，且 \(q_n\) 至少按 Fibonacci 速度增长。其标准渐近分数估计，在 \(q_n\le q<q_{n+1}\) 时给出
\[
\theta_\gamma(q)>\frac1{q_{n+1}+q_n},
\qquad
\theta_\gamma(q_n)<\frac1{q_{n+1}}. \tag{4}
\]
这些估计适用于这里的正整数部分商：它们由渐近分数的行列式为 \(\pm1\)、相邻误差异号，以及下一完全商位于 \((a_{n+1},a_{n+1}+1)\) 得到。

- 若递归取 \(a_{n+1}=\lceil q_n^{t-1}\rceil\)，则
  \(q_n^t\le q_{n+1}\) 且 \(q_{n+1}+q_n\le4q_n^t\)。由 (4) 得
  \(\tau(\gamma)=t\) 且 \(\inf_q q^t\theta_\gamma(q)>0\)。
- 若递归取 \(a_{n+1}=\lceil n q_n^{t-1}\rceil\)，则
  \(q_{n+1}\ge n q_n^t\) 且 \(q_{n+1}+q_n\le(n+3)q_n^t\)。
  由 (4)，\(q_n^t\theta_\gamma(q_n)\le1/n\)，故端点不取到。另一方面，对每个 \(\varepsilon>0\)，指数增长的 \(q_n\) 保证 \(n+3\le C_\varepsilon q_n^\varepsilon\)，再由 (4) 得 \(\theta_\gamma(q)\ge c_\varepsilon q^{-t-\varepsilon}\)。因此仍有 \(\tau(\gamma)=t\)。

### 4. 方向 \(\alpha_*=\sqrt2-1\)

令其代数共轭为 \(\alpha_*'=-\sqrt2-1\)。对 \(k\ne0\)，
\[
(k_2+\alpha_*k_1)(k_2+\alpha_*'k_1)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数，故绝对值至少为 \(1\)。令
\[
A=\sqrt{1+(\alpha_*')^2}=\sqrt{4+2\sqrt2}.
\]
由 Cauchy–Schwarz，
\[
|d_{\alpha_*}(k)|
\ge \frac1{A|k|}
\ge \frac1{A\langle k\rangle}.
\]
因此 \(s=1\) 允许。前述 Dirichlet 论证表明任何 \(s<1\) 都不允许，故
\[
\boxed{\text{最小允许损失为 }s=1\text{，并且该端点取到。}}
\]

对于题目的 \(C^m\) 估计，由 (2)、损失一阶的估计及 (3)，
\[
\begin{aligned}
\|N_{\alpha_*}^{-1}F\|_{C^m}
&\le (2\pi)^m S\frac{A}{2\pi}\|F\|_{H^{m+3}}\\
&\le (2\pi)^m S\frac{A}{2\pi}
   3^{(m+3)/2}\|F\|_{C^{m+3}}.
\end{aligned}
\]
所以题目要求的
\[
\boxed{\displaystyle
\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}}
\]
对每个 \(m\) 都成立；事实上右端的 \(C^{m+4}\) 可以加强为 \(C^{m+3}\)。

## S5　邻近方向的一致估计

**不存在**这样的区间和常数。设反而存在开区间 \(J\ni\alpha_*\)、有限 \(s\ge0\) 和 \(C\)。取有理数 \(p/q\in J\)，其中 \(q\ge1\)，再取 \(J\) 内无理数序列 \(\alpha_j\to p/q\)。

对固定模式 \(u=e_{(q,-p)}\)，有
\[
\|u\|_{L^2}=1,\qquad
\|N_{\alpha_j}u\|_{H^s}
=2\pi q|\alpha_j-p/q|\langle(q,-p)\rangle^s\longrightarrow0.
\]
这与假设中的一致估计矛盾。

## S6　具体方向的不可解数据

令
\[
q_n=10^{n!},\qquad
p_n=q_n\sum_{j=1}^n10^{-j!}\in\mathbb Z,\qquad
R_n=\alpha-\frac{p_n}{q_n}>0.
\]
因为余项的十进制指数至少为 \((n+1)!\)，
\[
0<R_n\le\frac{10^{-(n+1)!}}{1-10^{-1}}
<2q_n^{-(n+1)}.
\]
于是
\[
0<q_n\alpha-p_n=q_nR_n<2q_n^{-n}. \tag{5}
\]

若 \(\alpha=p/q\) 为有理数，取 \(q\ge1\)，则
\[
q q_nR_n=q_n p-qp_n
\]
是正整数；但由上述估计，它小于 \(2q q_n^{-n}\to0\)，矛盾。因此 \(\alpha\) 无理。

现在构造**同一个**数据
\[
\boxed{\displaystyle
F(y)=2\pi i\sum_{n=1}^\infty
(q_n\alpha-p_n)e^{2\pi i(q_ny_1-p_ny_2)}.}
\]
这里 \(\alpha<1\)，故 \(0<p_n<q_n\)。对任意固定 \(m\)，由 (5)，每项的任意 \(m\) 阶导数的绝对值至多为常数乘
\[
q_n^{m-n}.
\]
当 \(n\ge m+1\) 时，这不超过 \(q_n^{-1}=10^{-n!}\)，因而可求和。故级数及其各阶导数一致收敛，\(F\in C^\infty_0(\mathbb T^2)\)。

若存在光滑零均值解 \(u\)，在互异频率 \(k_n=(q_n,-p_n)\) 上比较 Fourier 系数得到
\[
2\pi i(q_n\alpha-p_n)\widehat u(k_n)
=2\pi i(q_n\alpha-p_n),
\qquad\text{即}\quad \widehat u(k_n)=1.
\]
这与 \(u\in L^2\) 的 Parseval 定理矛盾。因此该 \(F\) 没有光滑零均值解。