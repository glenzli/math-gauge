记 (e_k(y)=e^{2\pi i k\cdot y})，(d_\alpha(k)=\alpha k_1+k_2)。以下 Fourier 系数、Sobolev 范数及 Haar 测度均采用题中的归一化。关键恒等式为
\[
N_\alpha e_k=2\pi i d_\alpha(k)e_k.
\]
由于 \(\alpha\) 无理，对每个 \(k\ne0\) 都有 \(d_\alpha(k)\ne0\)。

## S1 有限频带上的逆

对 \(F\in H_N\)，定义
\[
T_{\alpha,N}F=
\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i d_\alpha(k)}e_k.
\]
逐频率计算即得 \(N_\alpha T_{\alpha,N}=T_{\alpha,N}N_\alpha=I\)，因此这是 \(N_\alpha\) 在 \(H_N\) 上的逆。

对任意实数 \(r\)，其精确算子范数为
\[
\boxed{\quad
\|T_{\alpha,N}\|_{H^r\to H^r}
=\max_{0<|k|\le N}\frac1{2\pi|d_\alpha(k)|}
=\frac1{2\pi\min_{0<|k|\le N}|d_\alpha(k)|}.
\quad}
\]
确实，Sobolev 范数平方中的各项只分别乘以
\((2\pi|d_\alpha(k)|)^{-2}\)，这给出上界；取达到最小除数的一个频率 \(F=e_k\)，即达到该上界。该范数与 \(r\) 无关。

## S2 有算术界的截断误差

定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i d_\alpha(k)}\quad(k\ne0).
\]
光滑函数的 Fourier 系数快速衰减，而假设给出
\[
|\widehat u(k)|\le(2\pi c)^{-1}\langle k\rangle^s|\widehat F(k)|.
\]
所以 \(\widehat u(k)\) 仍快速衰减，其 Fourier 级数连同任意阶导数都绝对一致收敛。这构造了光滑零均值函数 \(u\)，逐项求导给出 \(N_\alpha u=F\)。无理性和零均值条件给出唯一性。

由 S1，\(u_N\) 正是 \(u\) 的频带截断。对任意 \(r\in\mathbb R\)、\(q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
 {4\pi^2|d_\alpha(k)|^2}\\
&\le(2\pi c)^{-2}\sum_{|k|>N}
 \langle k\rangle^{-2q}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le(2\pi c)^{-2}(1+N^2)^{-q}\|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
取平方根即为所要求的估计，包括 \(q=0\) 的情形。

## S3 固定频带内改变方向

对 \(0<|k|\le N\)，两解之差的 Fourier 系数为
\[
\widehat{u_\alpha-u_\beta}(k)
=\frac{(\beta-\alpha)k_1}{2\pi i d_\alpha(k)d_\beta(k)}\widehat F(k).
\]
因此相应乘子的绝对值不超过
\[
\frac{|\alpha-\beta|\,|k_1|}{2\pi\delta^2}
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}.
\]
代入 Sobolev 范数的逐项平方和，得到对任意实数 \(r\) 都成立的
\[
\boxed{\|u_\alpha-u_\beta\|_{H^r}
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4 整体可逆性与全部损失指数

### 1. 完整的算术判据

定义
\[
D_s(\alpha)=\inf_{k\in\mathbb Z^2\setminus\{0\}}
 \langle k\rangle^s|d_\alpha(k)|,\qquad s\ge0.
\]
则有如下结论：

1. 对任意无理 \(\alpha\)，\(N_\alpha\) 在光滑零均值空间上都是单射。
2. \(N_\alpha:C^\infty_0\to C^\infty_0\) 是双射，当且仅当存在有限的 \(s\ge0\) 使 \(D_s(\alpha)>0\)。在此情形，逆由 S2 的 Fourier 公式给出，并且是光滑函数 Fréchet 空间之间的连续线性算子。
3. 题目中允许的损失指数集合恰为
\[
\boxed{\mathcal S_\alpha=\{s\ge0:D_s(\alpha)>0\}.}
\]
对属于该集合的 \(s\)，每个 \(r\) 的最佳常数都是
\[
\boxed{C_{\alpha,r,s}^{\mathrm{best}}=(2\pi D_s(\alpha))^{-1}.}
\]
特别地，“对每个 \(r\) 有估计”与“对某一个 \(r\) 有估计”等价。

证明如下。单射性来自 \(2\pi i d_\alpha(k)\widehat u(k)=0\) 以及 \(\widehat u(0)=0\)。当 \(D_s>0\) 时，S2 的构造适用，且逐频率比较给出
\[
\|u\|_{H^r}\le(2\pi D_s)^{-1}\|N_\alpha u\|_{H^{r+s}}.
\]
反过来，对每个 \(k\ne0\) 将 \(u=e_k\) 代入任意一个这样的估计，便有
\[
1\le 2\pi C_{\alpha,r,s}\langle k\rangle^s|d_\alpha(k)|.
\]
这证明必要性及最佳常数公式，后者即使下确界未取到也成立。逆的连续性由上述对所有 \(r\) 的估计和环面上 Sobolev 半范数与光滑函数通常半范数所定义拓扑的等价性得到。

还须证明没有任何多项式小除数下界时确实不能满射，而不只是估计失败。设所有有限 \(s\) 都有 \(D_s=0\)。可以递归选择互异的 \(k_j\ne0\)，使
\[
|k_j|\ge2^j,\qquad
0<|d_\alpha(k_j)|<\langle k_j\rangle^{-j^2}.
\]
理由是 \(D_{j^2}=0\)，而任意有限频率集合上的
\(\langle k\rangle^{j^2}|d_\alpha(k)|\) 都有正的最小值，所以达到任意小值的频率可选在任意预定有限集合之外。

令
\[
F=\sum_{j=1}^\infty\langle k_j\rangle^{-j}e_{k_j}.
\]
对任意非负整数 \(m\)，其 \(m\) 阶以内各导数的项绝对值至多为
\((2\pi)^m\langle k_j\rangle^{m-j}\)。当 \(j\ge m+1\) 时，这不超过 \((2\pi)^m2^{-j}\)，所以各阶导数级数一致收敛。故 \(F\in C^\infty_0\)。若存在光滑解，必有
\[
|\widehat u(k_j)|
=\frac{\langle k_j\rangle^{-j}}{2\pi|d_\alpha(k_j)|}
>\frac1{2\pi}\langle k_j\rangle^{j^2-j},
\]
这与光滑函数 Fourier 系数有界矛盾。因此满射性也有上述必要条件。

### 2. 用无理性指数描述全部边界

为把这个判据写成通常的数论分类，定义
\[
\mu(\alpha)=\sup\left\{\nu\in\mathbb R:
 \left|\alpha-\frac pq\right|<q^{-\nu}
 \text{ 对无穷多个 }p\in\mathbb Z,\ q\in\mathbb N\text{ 成立}\right\}.
\]
这里不要求分数既约，不影响该定义。所有无理数都有 \(\mu(\alpha)\ge2\)。事实上，将
\(0,\alpha,\ldots,Q\alpha\) 的小数部分放入 \(Q\) 个等长区间，抽屉原理给出
\(1\le q\le Q\) 和整数 \(p\)，使
\(|q\alpha-p|<1/Q\le1/q\)。这些 \(q\) 随 \(Q\) 必须无界，否则有限多个非零的 \(\|q\alpha\|_{\mathbb R/\mathbb Z}\) 有正下界。这给出所需的无穷多个二次逼近。

对每个 \(s\ge0\)，有等价条件
\[
D_s(\alpha)>0
\quad\Longleftrightarrow\quad
\inf_{q\ge1}q^s\|q\alpha\|_{\mathbb R/\mathbb Z}>0. \tag{*}
\]
证明：从左到右，取 \(p\) 为距离 \(q\alpha\) 最近的整数，并令 \(k=(q,-p)\)。有
\(\langle k\rangle\le B_\alpha q\)，因此
\(q^s\|q\alpha\|\ge D_sB_\alpha^{-s}\)。从右到左，若 \(k_1\ne0\)，则
\[
|d_\alpha(k)|\ge\||k_1|\alpha\|
\ge c|k_1|^{-s}\ge c\langle k\rangle^{-s};
\]
若 \(k_1=0\)，则 \(|d_\alpha(k)|=|k_2|\ge1\)，同样有下界。

由此，完整的指数分类为：

- 若 \(\mu(\alpha)=\infty\)，则 \(\mathcal S_\alpha=\varnothing\)，且 \(N_\alpha\) 不满射。
- 若 \(\mu(\alpha)<\infty\)，令 \(\tau=\mu(\alpha)-1\)。则所有 \(s>\tau\) 都允许，所有 \(0\le s<\tau\) 都不允许；唯一需要进一步判定的是端点：
\[
\boxed{\tau\in\mathcal S_\alpha
\quad\Longleftrightarrow\quad
\inf_{q\ge1}q^{\mu(\alpha)-1}\|q\alpha\|_{\mathbb R/\mathbb Z}>0.}
\]
等价地，端点允许当且仅当存在 \(c>0\)，对所有整数 \(p\) 及正整数 \(q\) 都有
\(|\alpha-p/q|\ge c q^{-\mu(\alpha)}\)。

为验证这段分类，若 \(s+1<\mu(\alpha)\)，可取
\(s+1<\nu<\mu(\alpha)\)，获得无穷多个逼近，使
\(q^s|q\alpha-p|<q^{s+1-\nu}\to0\)，所以 \((*)\) 失败。若 \(s+1>\mu(\alpha)\)，取
\(\mu(\alpha)<\nu<s+1\)。只有有限多个分数满足
\(|\alpha-p/q|<q^{-\nu}\)；利用无理性处理这些有限个例外，可得统一正数 \(c\)，使所有 \(p,q\) 都满足
\(|\alpha-p/q|\ge c q^{-\nu}\ge c q^{-(s+1)}\)。于是 \((*)\) 成立。端点恰由 \((*)\) 判定。

因此，恰好是有限无理性指数的无理数（即非 Liouville 无理数），才对每个光滑零均值右端具有唯一光滑零均值解。端点是否允许不能仅由无理性指数的数值决定，必须保留上述统一下界条件。

### 3. 特殊方向 \(\alpha_* =\sqrt2-1\)

令其代数共轭为 \(\alpha_*'=-\sqrt2-1\)，并记
\(A=\sqrt{1+(\alpha_*')^2}\)。对每个 \(k\ne0\)，
\[
(\alpha_* k_1+k_2)(\alpha_*' k_1+k_2)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数。非零性可由两个根均为无理数得出；当 \(k_1=0\) 时则直接是 \(k_2^2>0\)。故
\[
|d_{\alpha_*}(k)|
\ge\frac1{|\alpha_*'k_1+k_2|}
\ge\frac1{A|k|}
\ge\frac1A\langle k\rangle^{-1}.
\]
所以 \(s=1\) 允许，而且所有 \(s\ge1\) 都允许。

另一方面，前述抽屉原理对任意无理数都给出无界的 \(q\) 以及 \(p\)，使
\(|q\alpha_*-p|<1/q\)。这些频率 \(k=(q,-p)\) 满足 \(\langle k\rangle\le Bq\)，从而对 \(0\le s<1\)，
\[
\langle k\rangle^s|d_{\alpha_*}(k)|
\le B^s q^{s-1}\longrightarrow0.
\]
因此
\[
\boxed{\mathcal S_{\alpha_*}=[1,\infty),\qquad
\text{最小损失为 }s=1\text{，且端点取到。}}
\]

最后，题中的 \(C^m\) 估计对每个 \(m\) 都成立，实际上可少用一阶右端导数。二维环面上的 Fourier 级数与 Cauchy–Schwarz 不等式给出
\[
\|v\|_{C^m}\le K_m\|v\|_{H^{m+2}},
\]
因为对 \(|\gamma|\le m\)，导数级数的绝对和由
\(K_m\|v\|_{H^{m+2}}(\sum_k\langle k\rangle^{-4})^{1/2}\)
控制，而二维中该和收敛。由刚证明的损失一阶估计，
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le K_m\frac A{2\pi}\|F\|_{H^{m+3}}.
\]
对非负整数 \(\ell\)，Parseval 恒等式以及
\((1+k_1^2+k_2^2)^\ell\) 的展开给出
\(\|F\|_{H^\ell}\le L_\ell\|F\|_{C^\ell}\)：其各项均为有限阶偏导数的 \(L^2\) 范数，而归一化测度下 \(L^2\le L^\infty\)。于是
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le C'_m\|F\|_{C^{m+3}}
\le C'_m\|F\|_{C^{m+4}}.
\]
常数只依赖于 \(m\) 及固定方向，完全不依赖于 \(F\)。

## S5 邻近方向的一致估计

所述一致估计不存在，任何有限 \(s\) 都不行。

假设存在这样的开区间 \(J\)、\(s\) 及 \(C\)。取一个有理数 \(p/q\in J\)，其中 \(q\ge1\)，并固定非零频率 \(k=(q,-p)\)。令 \(u=e_k\)，则 \(\|u\|_{L^2}=1\)，而
\[
\|N_\alpha u\|_{H^s}
=2\pi q|\alpha-p/q|\langle(q,-p)\rangle^s.
\]
可在 \(J\) 内选取无理数 \(\alpha_j\to p/q\)。假设的估计就要求
\[
1\le2\pi Cq|\alpha_j-p/q|\langle(q,-p)\rangle^s\longrightarrow0,
\]
矛盾。这里各 \(u\) 都是光滑零均值函数，各 \(\alpha_j\) 都满足题目的无理性要求。

## S6 一个具体方向的不可解数据

令
\[
\alpha=\sum_{n=1}^\infty10^{-n!},\qquad
q_j=10^{j!},\qquad
p_j=q_j\sum_{n=1}^j10^{-n!}\in\mathbb Z\quad(j\ge2).
\]
尾项满足
\[
0<\alpha-\frac{p_j}{q_j}
=\sum_{n=j+1}^\infty10^{-n!}
\le\frac{10}{9}\,10^{-(j+1)!}
<2q_j^{-(j+1)}. \tag{1}
\]
其中第一项以后的指数至少逐次增加一，故可由公比 \(1/10\) 的几何级数控制。

先证明无理性。若 \(\alpha=A/B\)，其中 \(B\ge1\)，则尾项严格为正保证 \(A/B\ne p_j/q_j\)，于是
\[
\left|\alpha-\frac{p_j}{q_j}\right|\ge\frac1{Bq_j}.
\]
这与 (1) 在充分大的 \(j\) 时矛盾，因为 \(q_j^j\to\infty\)。所以 \(\alpha\) 无理。

现在给出一个固定的不可解右端。令
\[
k_j=(q_j,-p_j),\qquad
\boxed{F(y)=\sum_{j=2}^\infty q_j^{-j/2}e^{2\pi i(q_jy_1-p_jy_2)}.}
\]
这些频率互异且非零。由于 \(0<p_j/q_j<\alpha<1\)，有
\(q_j\le|k_j|\le\sqrt2q_j\)。对每个固定非负整数 \(m\)，任意 \(m\) 阶以内偏导数的第 \(j\) 项绝对值不超过
\[
(2\pi\sqrt2)^m q_j^{m-j/2}.
\]
当 \(j\ge2m+2\) 时，该式不超过
\((2\pi\sqrt2)^m q_j^{-1}\)，而 \(\sum_{j\ge2}q_j^{-1}<\infty\)。故所有阶导数级数均绝对一致收敛，\(F\) 光滑，并且由于没有零频率，其均值为零。

由 (1)，
\[
0<d_\alpha(k_j)=q_j\alpha-p_j<2q_j^{-j}.
\]
若存在光滑零均值解 \(u\)，取方程的第 \(k_j\) 个 Fourier 系数，得到
\[
|\widehat u(k_j)|
=\frac{q_j^{-j/2}}{2\pi|q_j\alpha-p_j|}
>\frac1{4\pi}q_j^{j/2}\longrightarrow\infty.
\]
然而任何光滑函数，甚至任何可积函数，都有
\(|\widehat u(k)|\le\|u\|_{L^1}<\infty\)。矛盾。

所以这个同一个、明确给出的 \(F\in C^\infty_0(\mathbb T^2)\) 使方程没有光滑零均值解；事实上它没有任何光滑解。
