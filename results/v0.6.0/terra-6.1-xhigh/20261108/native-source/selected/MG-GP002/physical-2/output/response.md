以下以 \(e_k(y)=e^{2\pi i k\cdot y}\) 记 Fourier 基。因为
\[
N_\alpha e_k=2\pi i(\alpha k_1+k_2)e_k,
\]
无理性保证所有非零频率上的乘子都非零。

## S1 有限频带上的逆

对
\[
F=\sum_{0<|k|\le N}\widehat F(k)e_k\in H_N,
\]
定义
\[
N_\alpha^{-1}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e_k.
\]
逐频率计算可知，这是 \(N_\alpha:H_N\to H_N\) 的逆。

对任意 \(r\in\mathbb R\)，\(H^r\) 范数在 Fourier 基下是加权 \(\ell^2\) 范数，因此该对角乘子的精确范数为
\[
\boxed{\displaystyle
\|N_\alpha^{-1}\|_{H^r\to H^r}
=\frac1{2\pi}\max_{0<|k|\le N}\frac1{|\alpha k_1+k_2|}
=\frac1{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.}
\]
上界由逐项估计得到；取达到最大值的单一 Fourier 模式可得到等号。

## S2 有算术界的截断误差

定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}
 {2\pi i(\alpha k_1+k_2)}\quad(k\ne0).
\]
由于 \(F\) 光滑，其 Fourier 系数快速衰减。给定的小除数下界只允许除以一个至多多项式增长的因子，所以 \(\widehat u(k)\) 仍快速衰减。因此该 Fourier 级数定义光滑零均值函数，且逐频率有 \(N_\alpha u=F\)。

\(u_N\) 正是 \(u\) 在 \(0<|k|\le N\) 上的截断。于是，对任意 \(r\in\mathbb R\)、\(q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}\langle k\rangle^{2r}
 \frac{|\widehat F(k)|^2}
 {(2\pi)^2|\alpha k_1+k_2|^2}\\
&\le \frac1{(2\pi c)^2}
 \sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}
 \|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
最后一步用到 \(|k|>N\) 和 \(q\ge0\)。开方得到所要求的估计：
\[
\boxed{\displaystyle
\|u-u_N\|_{H^r}
\le \frac{(1+N^2)^{-q/2}}{2\pi c}
\|F\|_{H^{r+s+q}}.}
\]

## S3 固定频带内改变方向

对每个 \(0<|k|\le N\)，
\[
\begin{aligned}
|\widehat u_\alpha(k)-\widehat u_\beta(k)|
&=\frac{|\widehat F(k)|}{2\pi}
\left|\frac1{\alpha k_1+k_2}
-\frac1{\beta k_1+k_2}\right|\\
&=\frac{|\alpha-\beta|\,|k_1|\,|\widehat F(k)|}
 {2\pi|\alpha k_1+k_2|\,|\beta k_1+k_2|}\\
&\le \frac{|\alpha-\beta|N}{2\pi\delta^2}
 |\widehat F(k)|.
\end{aligned}
\]
乘以 \(\langle k\rangle^r\)，平方求和并开方，得到
\[
\boxed{\displaystyle
\|u_\alpha-u_\beta\|_{H^r}
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4 整体可解性、损失分类与 \(\alpha_*\)

### 一般无理方向

记
\[
\|x\|_{\mathbb Z}=\min_{p\in\mathbb Z}|x-p|,
\qquad
\mu(\alpha)=\sup\left\{\mu:
\left|\alpha-\frac pq\right|<q^{-\mu}
\text{ 对无穷多个 }(p,q)\in\mathbb Z\times\mathbb N\right\}.
\]
Dirichlet 逼近定理给出 \(\mu(\alpha)\ge2\)。允许 \(\mu(\alpha)=\infty\)，并记
\[
\tau(\alpha)=\mu(\alpha)-1\in[1,\infty].
\]

完整结论如下。

1. \(N_\alpha:C^\infty_0\to C^\infty_0\) 是双射，**当且仅当** \(\mu(\alpha)<\infty\)，即 \(\alpha\) 不是 Liouville 数。
2. 对给定 \(s\ge0\)，题中的 Sobolev 估计对每个 \(r\) 成立，当且仅当
   \[
   \boxed{\displaystyle
   \inf_{q\ge1}q^s\|q\alpha\|_{\mathbb Z}>0.}
   \tag{1}
   \]
   若 \(\tau(\alpha)<\infty\)，全部允许损失为：
   - 每个 \(s>\tau(\alpha)\)；
   - \(s=\tau(\alpha)\) 当且仅当 (1) 在该端点成立；
   - 没有 \(s<\tau(\alpha)\)。
   
   若 \(\tau(\alpha)=\infty\)，则没有有限的允许损失。

下面证明这些断言。

对固定 \(s\ge0\)，先看小除数条件
\[
|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}
\qquad(k\in\mathbb Z^2\setminus\{0\})
\tag{2}
\]
与 (1) 的等价性。若 (2) 成立，取 \(k=(q,-p)\)，其中 \(p\) 是距 \(q\alpha\) 最近的整数。此时 \(\langle k\rangle\le C_\alpha q\)，故得到 (1)。反过来，若 (1) 成立，则对 \(k_1\ne0\)，
\[
|\alpha k_1+k_2|
\ge \||k_1|\alpha\|_{\mathbb Z}
\ge d|k_1|^{-s}\ge d\langle k\rangle^{-s};
\]
而 \(k_1=0\) 时左边至少为 \(1\)。因此得到 (2)。

在 (2) 下，S2 的 Fourier 构造给出每个光滑零均值 \(F\) 的光滑解，且
\[
\|u\|_{H^r}\le \frac1{2\pi c}\|N_\alpha u\|_{H^{r+s}}
\qquad(r\in\mathbb R).
\tag{3}
\]
反之，把任何一个所要求的 Sobolev 估计用于 \(u=e_k\)，便得到 (2)。所以 (1) 精确刻画全部允许损失，且其成立与否不依赖 \(r\)。

若 \(\tau<\infty\) 且 \(s>\tau\)，取 \(\tau<t<s\)。由 \(\mu=\tau+1\) 的定义，充分大的 \(q\) 对所有整数 \(p\) 都满足
\[
\left|\alpha-\frac pq\right|\ge q^{-(t+1)}.
\]
有限多个较小的 \(q\) 也有正的最近整数距离，所以 (1) 对 \(s\) 成立。若 \(s<\tau\)，取 \(s<t<\tau\)；由上确界的定义，有无穷多个 \(q\) 满足
\[
\|q\alpha\|_{\mathbb Z}<q^{-t},
\]
从而 \(q^s\|q\alpha\|_{\mathbb Z}\to0\) 于某个子列，(1) 不成立。端点是否成立正由 (1) 判定。相同论证也表明，若 \(\tau=\infty\)，任何有限 \(s\) 都不满足 (1)。

剩下证明：没有多项式小除数下界时，不是每个光滑数据都可解。此时可选取两两不同、模长趋于无穷的 \(k_j\ne0\)，使
\[
0<|\alpha k_{j,1}+k_{j,2}|<\langle k_j\rangle^{-j}.
\]
例如逐次选择即可：任何固定有限频率集的小除数有正最小值，而相应的多项式下界不存在。令
\[
\widehat F(k_j)=\alpha k_{j,1}+k_{j,2},
\qquad
\widehat F(k)=0\quad(k\notin\{k_j:j\ge1\}).
\]
这些系数快速衰减，所以 \(F\in C^\infty_0\)。但若 \(N_\alpha u=F\)，则
\[
\widehat u(k_j)=\frac1{2\pi i}
\]
对所有 \(j\) 成立。这与光滑函数的 Fourier 系数趋于零矛盾。因此可解性恰好等价于某个有限阶的 (2)，也就等价于 \(\mu(\alpha)<\infty\)。

唯一性则对每个无理 \(\alpha\) 都成立：若 \(N_\alpha u=0\)，所有非零 Fourier 系数都为零；零均值又使常数系数为零。

### \(\alpha_*=\sqrt2-1\)

\(\alpha_*\) 满足 \(x^2+2x-1=0\)，其共轭根为
\(\alpha'=-1-\sqrt2\)。对任意 \(p\in\mathbb Z,q\ge1\)，
\[
\left|\alpha_*-\frac pq\right|
\left|\alpha'-\frac pq\right|
=\frac{|p^2+2pq-q^2|}{q^2}\ge\frac1{q^2},
\]
因为分子是非零整数。若 \(|\alpha_*-p/q|<1\)，第二个因子至多 \(2\sqrt2+1\)；若它至少为 \(1\)，同样可得
\[
\left|\alpha_*-\frac pq\right|
\ge \frac1{(2\sqrt2+1)q^2}.
\]
因此
\[
\|q\alpha_*\|_{\mathbb Z}\ge
\frac1{(2\sqrt2+1)q}.
\tag{4}
\]
这证明 \(s=1\) 允许。

另一方面，Dirichlet 定理对无理数提供无穷多个 \(q\) 满足
\(\|q\alpha_*\|_{\mathbb Z}<1/q\)。故对任意 \(s<1\)，
\(q^s\|q\alpha_*\|_{\mathbb Z}\) 沿这些 \(q\) 趋于零，不满足 (1)。所以
\[
\boxed{\text{最小允许损失为 }s=1\text{，并且端点取到。}}
\]

所问的 \(C^m\) 估计也成立。事实上可以用 \(m+3\) 阶范数。由 Cauchy–Schwarz 和二维收敛级数
\(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}<\infty\)，
\[
\|v\|_{C^m}\le A_m\|v\|_{H^{m+2}}.
\]
由 (3) 和 (4)，
\[
\|u\|_{H^{m+2}}\le B_m\|F\|_{H^{m+3}}.
\]
最后，对整数 \(d\ge0\)，Parseval 恒等式及归一化测度给出
\[
\|F\|_{H^d}\le D_d\|F\|_{C^d}.
\]
合并得到
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le A_mB_mD_{m+3}\|F\|_{C^{m+3}}
\le C_m\|F\|_{C^{m+4}},
\]
其中常数均与 \(F\) 无关。

## S5 邻近方向的一致估计

**不存在**这样的区间和常数。

假设存在。开区间 \(J\) 含有某个有理数 \(p/q\)，其中 \(q\ge1\)。取固定非零频率 \(k=(q,-p)\)，并将 \(u=e_k\) 代入假设的估计，得到对所有无理 \(\alpha\in J\)，
\[
1\le 2\pi C\,|\alpha q-p|\,\langle(q,-p)\rangle^s.
\]
在 \(J\) 内取无理数序列趋于 \(p/q\)，右边趋于零，矛盾。

## S6 一个具体方向的不可解数据

令
\[
\alpha=\sum_{n=1}^{\infty}10^{-n!},\qquad
q_n=10^{n!},\qquad
p_n=q_n\sum_{j=1}^{n}10^{-j!}\in\mathbb Z.
\]
尾项为正，而且
\[
0<q_n\alpha-p_n
=q_n\sum_{j>n}10^{-j!}
\le 2q_n10^{-(n+1)!}
=2q_n^{-n}.
\tag{5}
\]

若 \(\alpha=a/b\) 为有理数，\(b\ge1\)，则每个正数 \(q_n\alpha-p_n\) 都至少为 \(1/b\)，这与 (5) 右边趋于零矛盾。因此 \(\alpha\) 无理。

现在令 \(k_n=(q_n,-p_n)\)，定义**同一个**数据 \(F\) 的 Fourier 系数：
\[
\widehat F(k_n)=q_n\alpha-p_n,\qquad
\widehat F(k)=0\quad(k\notin\{k_n:n\ge1\}).
\]
由于 \(0<p_n<q_n\)，有 \(\langle k_n\rangle\le Cq_n\)。对每个固定 \(M\ge0\)，由 (5)
\[
\langle k_n\rangle^M|\widehat F(k_n)|
\le 2C^M q_n^{M-n},
\]
所以这些系数快速衰减。故它们定义一个 \(F\in C^\infty_0(\mathbb T^2)\)。

若存在光滑零均值解 \(N_\alpha u=F\)，则在每个 \(k_n\) 上必有
\[
\widehat u(k_n)
=\frac{q_n\alpha-p_n}{2\pi i(q_n\alpha-p_n)}
=\frac1{2\pi i}.
\]
但 \(|k_n|\to\infty\)，光滑函数的 Fourier 系数必须趋于零，矛盾。故这个 \(F\) 没有光滑零均值解。