记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad d_\alpha(k)=\alpha k_1+k_2.
\]
则
\[
N_\alpha e_k=2\pi i\,d_\alpha(k)e_k.
\]
由于 \(\alpha\) 无理，\(d_\alpha(k)\ne0\) 对所有 \(k\ne0\) 成立。零均值条件就是零频 Fourier 系数为零。

**S1. 有限频带上的逆**

对 \(F\in H_N\)，定义
\[
N_{\alpha,N}^{-1}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
逐个 Fourier 模态计算可知，这是 \(N_\alpha:H_N\to H_N\) 的双侧逆。

对任意 \(r\in\mathbb R\)，
\[
\|N_{\alpha,N}^{-1}F\|_{H^r}^2
=\sum_{0<|k|\le N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{4\pi^2|d_\alpha(k)|^2}.
\]
因此精确逆范数为
\[
\boxed{
\|N_{\alpha,N}^{-1}\|_{H^r\to H^r}
=\frac1{2\pi}\max_{0<|k|\le N}\frac1{|d_\alpha(k)|}
=\frac1{2\pi\min_{0<|k|\le N}|d_\alpha(k)|}.
}
\]
它与 \(r\) 无关；取实现最小小除数的单个 Fourier 模态，即达到该范数。

**S2. 有算术界的截断误差**

假设
\[
|d_\alpha(k)|\ge c\langle k\rangle^{-s}\qquad(k\ne0).
\]
定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}
\quad(k\ne0).
\]
光滑函数的 Fourier 系数快速衰减，而
\[
|\widehat u(k)|
\le (2\pi c)^{-1}\langle k\rangle^s|\widehat F(k)|.
\]
故 \(\widehat u(k)\) 仍快速衰减，其 Fourier 级数及所有导数级数绝对一致收敛，给出 \(u\in C^\infty_0\)，且 \(N_\alpha u=F\)。非零频乘子均非零，所以此零均值解唯一。

S1 中的 \(u_N\) 正是 \(u\) 的频带截断。对任意 \(r\in\mathbb R,\ q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{4\pi^2|d_\alpha(k)|^2}\\
&\le \frac1{4\pi^2c^2}
\sum_{|k|>N}\langle k\rangle^{-2q}
\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le \frac{(1+N^2)^{-q}}{4\pi^2c^2}
\|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
开平方即得
\[
\boxed{
\|u-u_N\|_{H^r}
\le(2\pi c)^{-1}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}}.
}
\]

**S3. 固定频带内改变方向**

对 \(0<|k|\le N\)，
\[
\widehat{u_\alpha-u_\beta}(k)
=\frac{(\beta-\alpha)k_1}
{2\pi i\,d_\alpha(k)d_\beta(k)}\widehat F(k).
\]
由两方向的小除数下界以及 \(|k_1|\le N\)，
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat F(k)|.
\]
乘以 Sobolev 权重、平方求和，得到任意 \(r\in\mathbb R\) 下的估计
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.
}
\]

**S4. 整体可逆性、全部损失及端点**

先给出精确的小除数判据。令
\[
\kappa_s(\alpha)
=\inf_{k\in\mathbb Z^2\setminus\{0\}}
\langle k\rangle^s|d_\alpha(k)|,\qquad s\ge0.
\]
则
\[
\boxed{
s\text{ 是允许损失}\iff \kappa_s(\alpha)>0.
}
\]
而且只要成立，对每个 \(r\) 的最优常数都是
\[
\boxed{C_{\alpha,r,s}^{\mathrm{opt}}
=\frac1{2\pi\kappa_s(\alpha)}.}
\]

事实上，下界 \(\kappa_s>0\) 直接给出
\[
\begin{aligned}
\|N_\alpha u\|_{H^{r+s}}^2
&=4\pi^2\sum_{k\ne0}
\langle k\rangle^{2(r+s)}|d_\alpha(k)|^2|\widehat u(k)|^2\\
&\ge 4\pi^2\kappa_s(\alpha)^2\|u\|_{H^r}^2.
\end{aligned}
\]
反过来，把估计用于 \(u=e_k\)，便得
\[
1\le 2\pi C_{\alpha,r,s}\langle k\rangle^s|d_\alpha(k)|.
\]
这也证明了最优常数公式，并说明：估计对一个 \(r\) 成立，就对所有 \(r\) 成立。

下面将此判据转化为完整的算术分类。记
\[
\|x\|_{\mathbb R/\mathbb Z}=\min_{p\in\mathbb Z}|x-p|,
\qquad
A_s(\alpha)=\inf_{q\ge1}q^s\|q\alpha\|_{\mathbb R/\mathbb Z}.
\]
则
\[
\kappa_s(\alpha)>0\iff A_s(\alpha)>0. \tag{1}
\]
证明如下：

- 若 \(A_s>0\)，当 \(k_1\ne0\) 时，令 \(q=|k_1|\)，有
  \[
  |d_\alpha(k)|\ge\|q\alpha\|_{\mathbb R/\mathbb Z}
  \ge A_s q^{-s}\ge A_s\langle k\rangle^{-s}.
  \]
  当 \(k_1=0,\ k\ne0\) 时，\(|d_\alpha(k)|=|k_2|\ge1\)。故 \(\kappa_s\ge\min(A_s,1)>0\)。
- 若 \(\kappa_s>0\)，对每个 \(q\ge1\) 取离 \(q\alpha\) 最近的整数 \(p\)。此时存在仅依赖于 \(\alpha\) 的 \(B_\alpha\)，使
  \(\langle(q,-p)\rangle\le B_\alpha q\)，从而
  \[
  \|q\alpha\|_{\mathbb R/\mathbb Z}
  \ge\kappa_s B_\alpha^{-s}q^{-s}.
  \]
  故 \(A_s>0\)。

定义无理性指数
\[
\mu(\alpha)=
\sup\left\{\nu>0:
\left|\alpha-\frac pq\right|<q^{-\nu}
\text{ 对无穷多个 }(p,q)\in\mathbb Z\times\mathbb N\text{ 成立}\right\}.
\]
对任意实无理数，Dirichlet 逼近给出无穷多个 \(q\) 满足
\[
0<\|q\alpha\|_{\mathbb R/\mathbb Z}<q^{-1},
\]
故 \(\mu(\alpha)\ge2\)。这里 Dirichlet 结论可由对
\(0,\alpha,\ldots,Q\alpha\) 的小数部分作鸽巢论证得到；所得分母必无界，因为每个固定非零分母的小除数均为正。

令 \(p_n/q_n\) 为 \(\alpha\) 的简单连分数收敛分数。全部允许损失可以精确写为
\[
\boxed{
\mathcal S_\alpha
=\left\{s\ge0:\sup_{n\ge1}\frac{q_{n+1}}{q_n^s}<\infty\right\}.
} \tag{2}
\]
等价地：

- 若 \(\mu(\alpha)=\infty\)，则 \(\mathcal S_\alpha=\varnothing\)。
- 若 \(\mu(\alpha)<\infty\)，令 \(\tau=\mu(\alpha)-1\)。则所有 \(s>\tau\) 都允许，所有 \(s<\tau\) 都不允许；端点满足
  \[
  \boxed{
  \tau\in\mathcal S_\alpha
  \iff \sup_{n\ge1}\frac{q_{n+1}}{q_n^\tau}<\infty.
  } \tag{3}
  \]

先证明非端点结论。若 \(s+1>\mu(\alpha)\)，则对充分大的 \(q\) 和所有整数 \(p\)，
\[
\left|\alpha-\frac pq\right|\ge q^{-(s+1)}.
\]
因此 \(q^s\|q\alpha\|\ge1\) 最终成立；有限个剩余分母的小除数非零，故 \(A_s>0\)。

若 \(s+1<\mu(\alpha)\)，选择
\[
s+1<\nu<\mu(\alpha).
\]
存在分母趋于无穷的逼近，使
\[
q^s\|q\alpha\|
\le q^{s+1}\left|\alpha-\frac pq\right|
<q^{s+1-\nu}\longrightarrow0.
\]
故 \(A_s=0\)。此论证也覆盖 \(\mu(\alpha)=\infty\) 时的每个有限 \(s\)。

为证明端点判据，使用简单连分数的如下标准性质：对任意实无理数及其收敛分数，\(n\ge1\) 时
\[
\frac1{q_n+q_{n+1}}
<\|q_n\alpha\|_{\mathbb R/\mathbb Z}
<\frac1{q_{n+1}},
\]
且第二类最佳逼近性质给出
\[
1\le q<q_{n+1}
\implies
\|q\alpha\|_{\mathbb R/\mathbb Z}
\ge\|q_n\alpha\|_{\mathbb R/\mathbb Z}.
\]
若 \(A_s>0\)，则
\[
A_s\le q_n^s\|q_n\alpha\|<\frac{q_n^s}{q_{n+1}},
\]
所以式 (2) 中的上确界有限。反之，若该上确界为有限的 \(M\)，对 \(q_n\le q<q_{n+1}\)，
\[
q^s\|q\alpha\|
>\frac{q^s}{q_n+q_{n+1}}
\ge\frac{q^s}{2M q_n^s}
\ge\frac1{2M}.
\]
再处理有限个 \(q<q_1\)，便得 \(A_s>0\)。这证明了 (2) 和 (3)。特别地，当 \(\mu=2\) 时，端点 \(s=1\) 取到，当且仅当连分数部分商有界。

现在证明整体光滑可逆性的分类：
\[
\boxed{
N_\alpha:C^\infty_0\to C^\infty_0
\text{ 是双射}
\iff \exists s<\infty:\kappa_s(\alpha)>0
\iff \mu(\alpha)<\infty.
} \tag{4}
\]
即：恰好非 Liouville 无理数具有对全部光滑零均值数据的光滑可解性。

充分性已经由 S2 的 Fourier 构造证明。唯一性对每个无理 \(\alpha\) 都成立，因为齐次方程在每个非零频率上的 Fourier 系数必须为零。

为证明必要性，假设没有任何有限的允许损失。于是对每个整数 \(j\ge1\)，可选取互不相同且长度严格递增的 \(k_j\)，使
\[
|k_j|\ge2^j,\qquad
0<|d_\alpha(k_j)|\le\langle k_j\rangle^{-2j}.
\]
这样的选择可以避开任意有限频率集合：在有限集合上，各个非零小除数的加权最小值为正，而 \(\kappa_{2j}=0\)。

定义同一个数据
\[
F(y)=\sum_{j=1}^\infty \langle k_j\rangle^{-j}e_{k_j}(y).
\]
对任意固定导数阶数 \(m\)，其第 \(j\) 项导数的绝对值至多为
\[
(2\pi)^m\langle k_j\rangle^{m-j}.
\]
当 \(j\ge m+1\) 时，这至多为 \((2\pi)^m2^{-j}\)。故所有导数级数绝对一致收敛，\(F\in C^\infty_0\)。

若存在光滑解，则
\[
|\widehat u(k_j)|
=\frac{\langle k_j\rangle^{-j}}{2\pi|d_\alpha(k_j)|}
\ge\frac1{2\pi}\langle k_j\rangle^j\longrightarrow\infty,
\]
与光滑函数 Fourier 系数有界矛盾。因此不是所有光滑数据都可解，证明了 (4)。

更一般地，对任意无理 \(\alpha\)，给定 \(F\) 有光滑零均值解，当且仅当
\[
\left\{\frac{\widehat F(k)}{d_\alpha(k)}:k\ne0\right\}
\]
快速衰减；解由 S2 的 Fourier 公式唯一确定。有限损失估计还保证式 (4) 中的逆在 \(C^\infty\) 的通常 Fréchet 拓扑下连续。

最后处理 \(\alpha_*=\sqrt2-1\)。令其代数共轭为
\[
\alpha_*'=-\sqrt2-1.
\]
对每个 \(k\ne0\)，
\[
(\alpha_*k_1+k_2)(\alpha_*'k_1+k_2)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数。因此
\[
\begin{aligned}
|\alpha_*k_1+k_2|
&\ge\frac1{|\alpha_*'k_1+k_2|}\\
&\ge\frac1{\sqrt{4+2\sqrt2}\,|k|}
\ge\frac1{\sqrt{4+2\sqrt2}}\langle k\rangle^{-1}.
\end{aligned}
\]
故 \(s=1\) 允许，所有 \(s\ge1\) 也允许。另一方面，前述 Dirichlet 逼近适用于无理数 \(\alpha_*\)，对 \(s<1\) 给出
\[
q^s\|q\alpha_*\|<q^{s-1}\longrightarrow0
\]
的子列，故这些 \(s\) 均不允许。于是
\[
\boxed{\mathcal S_{\alpha_*}=[1,\infty),\qquad
\text{最小损失为 }1\text{，且取到}.}
\]

题设的 \(C^m\) 估计也成立。具体地，二维环面上 Fourier 级数与 Cauchy–Schwarz 不等式给出
\[
\|v\|_{C^m}\le B_m\|v\|_{H^{m+2}},
\]
因为
\[
\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}<\infty.
\]
这是此处所需的 Sobolev 嵌入，阶数满足 \(m+2>m+2/2\)。利用已经证明的损失 \(1\) 估计，
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le B_m\frac{\sqrt{4+2\sqrt2}}{2\pi}\|F\|_{H^{m+3}}.
\]
对整数 \(L\ge0\)，Parseval 恒等式及整数阶 Sobolev 范数的导数表达给出
\[
\|F\|_{H^L}\le D_L\|F\|_{C^L};
\]
这里使用了归一化 Haar 测度下 \(\|g\|_{L^2}\le\|g\|_\infty\)。所以实际上有更强的估计
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le E_m\|F\|_{C^{m+3}}
\le E_m\|F\|_{C^{m+4}}.
\]
因此所要求的每个有限常数 \(C_m\) 都存在。

**S5. 邻近方向的一致估计**

结论为**不存在**，而且任何非空开区间都不可能满足此要求。

假设存在所述 \(J,s,C\)。取有理数 \(p/q\in J\)，其中 \(q\ge1\)，并固定
\[
k=(q,-p),\qquad u=e_k.
\]
这是光滑零均值函数，且 \(\|u\|_{L^2}=1\)。

令
\[
\alpha_j=\frac pq+\frac{\sqrt2}{j}.
\]
每个 \(\alpha_j\) 都无理，且充分大的 \(j\) 满足 \(\alpha_j\in J\)。然而
\[
\|N_{\alpha_j}u\|_{H^s}
=2\pi|q\alpha_j-p|\langle k\rangle^s
=\frac{2\pi q\sqrt2}{j}\langle k\rangle^s
\longrightarrow0.
\]
假设中的估计将给出 \(1\le C\|N_{\alpha_j}u\|_{H^s}\)，矛盾。

**S6. 一个具体方向的不可解数据**

设
\[
\alpha=\sum_{n=1}^\infty10^{-n!},\qquad
q_n=10^{n!},\qquad
p_n=\sum_{j=1}^n10^{n!-j!}.
\]
则 \(p_n\in\mathbb Z\)，且
\[
\frac{p_n}{q_n}=\sum_{j=1}^n10^{-j!}.
\]
尾项满足
\[
0<\alpha-\frac{p_n}{q_n}
=\sum_{j=n+1}^\infty10^{-j!}
<2\,10^{-(n+1)!}
=2q_n^{-(n+1)}. \tag{5}
\]
例如，将该尾和放大为从指数 \((n+1)!\) 开始的全部整数指数几何级数，便得到这个上界。

先证明无理性。若 \(\alpha=A/B\)，其中 \(A\in\mathbb Z,\ B\ge1\)，由式 (5) 中差值严格为正，
\[
\left|\frac AB-\frac{p_n}{q_n}\right|
\ge\frac1{Bq_n}.
\]
与式 (5) 合并得到
\[
q_n^n<2B,
\]
这对充分大的 \(n\) 不可能。因此 \(\alpha\) 无理。

令
\[
k_n=(q_n,-p_n),\qquad
d_n=q_n\alpha-p_n.
\]
由式 (5)，
\[
0<d_n<2q_n^{-n}. \tag{6}
\]
又因 \(0<p_n/q_n<\alpha<1\)，
\[
q_n\le |k_n|\le\sqrt2\,q_n.
\]

现在构造所要求的**同一个**数据：
\[
\boxed{
F(y)=\sum_{n=2}^\infty
q_n^{-n/2}\,e^{2\pi i(q_ny_1-p_ny_2)}.
}
\]
各频率互不相同且非零，故其均值为零。对任意固定的非负整数 \(m\)，每项的任意不超过 \(m\) 阶导数，其绝对值均不超过
\[
(2\pi\sqrt2)^m q_n^{m-n/2}.
\]
当 \(n\ge2m+2\) 时，这至多为
\[
(2\pi\sqrt2)^m q_n^{-1}.
\]
而
\[
\sum_{n=2}^\infty q_n^{-1}
=\sum_{n=2}^\infty10^{-n!}<\infty.
\]
故所有导数级数绝对一致收敛，证明 \(F\in C^\infty_0(\mathbb T^2)\)。

若存在光滑零均值解 \(u\)，在频率 \(k_n\) 上必有
\[
\widehat u(k_n)=\frac{q_n^{-n/2}}{2\pi i\,d_n}.
\]
利用式 (6)，
\[
|\widehat u(k_n)|
>\frac1{4\pi}q_n^{n/2}
\longrightarrow\infty.
\]
但任何光滑函数都满足
\[
|\widehat u(k)|\le\|u\|_{L^1}<\infty,
\]
矛盾。因此上述固定的光滑零均值 \(F\) 使 \(N_\alpha u=F\) 没有光滑零均值解。