记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad
\lambda_\alpha(k)=\alpha k_1+k_2.
\]
则
\[
N_\alpha e_k=2\pi i\lambda_\alpha(k)e_k.
\]
当 \(\alpha\) 无理时，\(\lambda_\alpha(k)\ne0\) 对所有 \(k\ne0\) 成立。

下文使用 Fourier 光滑性判据：一个序列 \(a(k)\) 是光滑函数的 Fourier 系数，当且仅当它快速衰减，即对每个 \(M\ge0\)，
\[
\sup_k\langle k\rangle^M|a(k)|<\infty.
\]
必要性由分部积分得到；充分性由
\(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-p}<\infty\)（\(p>2\)）以及各阶导数级数的绝对一致收敛得到。

## S1

对
\[
F=\sum_{0<|k|\le N}\widehat F(k)e_k
\]
定义
\[
\boxed{
N_{\alpha,N}^{-1}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\lambda_\alpha(k)}e_k.
}
\]
所有分母非零，故这确实是 \(N_\alpha:H_N\to H_N\) 的双侧逆。

对任意实数 \(r\)，其精确算子范数为
\[
\boxed{
\|N_{\alpha,N}^{-1}\|_{H^r\to H^r}
=\frac1{2\pi}
\max_{0<|k|\le N}\frac1{|\alpha k_1+k_2|}
=\frac1{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.
}
\]
事实上，该算子在加权 Fourier 坐标中为对角乘子，故上式给出上界；取使小除数最小的单个 Fourier 模式，即达到此上界。特别地，范数与 \(r\) 无关。

## S2

定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\lambda_\alpha(k)}
\quad(k\ne0).
\]
由算术假设，
\[
|\widehat u(k)|
\le \frac1{2\pi c}\langle k\rangle^s|\widehat F(k)|.
\]
因为 \(F\) 光滑，右端仍快速衰减，所以该 Fourier 级数定义了光滑零均值函数 \(u\)，且逐项求导给出 \(N_\alpha u=F\)。唯一性由非零频率上的乘子不为零得到。

S1 中的 \(u_N\) 恰为 \(u\) 的频带截断。因此，对任意 \(r\in\mathbb R\)、\(q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\frac1{4\pi^2}\sum_{|k|>N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{|\lambda_\alpha(k)|^2}\\
&\le\frac1{4\pi^2c^2}
\sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&\le\frac{(1+N^2)^{-q}}{4\pi^2c^2}
\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}
|\widehat F(k)|^2.
\end{aligned}
\]
最后一步使用了 \(|k|>N\) 和 \(q\ge0\)。开方即得
\[
\boxed{
\|u-u_N\|_{H^r}
\le(2\pi c)^{-1}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}}.
}
\]

## S3

在每个 \(0<|k|\le N\) 上，
\[
\widehat{u_\alpha-u_\beta}(k)
=\frac{(\beta-\alpha)k_1}
{2\pi i\,\lambda_\alpha(k)\lambda_\beta(k)}
\widehat F(k).
\]
根据两个方向的小除数下界以及 \(|k_1|\le N\)，
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat F(k)|.
\]
乘以 Sobolev 权重并平方求和，得到对任意 \(r\in\mathbb R\)，
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.
}
\]

## S4

**完整分类如下。** 对无理数 \(\alpha\)，定义
\[
\gamma_s(\alpha)
=\inf_{k\in\mathbb Z^2\setminus\{0\}}
\langle k\rangle^s|\alpha k_1+k_2|,
\qquad s\ge0.
\]

则：

1. \(N_\alpha\) 在 \(C^\infty_0\) 上总是单射；它满射，当且仅当某个有限 \(s\ge0\) 满足 \(\gamma_s(\alpha)>0\)。
2. 题中允许的全部损失恰为
   \[
   \boxed{\mathcal S_\alpha=\{s\ge0:\gamma_s(\alpha)>0\}.}
   \]
   对每个允许的 \(s\)，每个 \(r\) 的最佳常数均为
   \[
   \boxed{C_{\alpha,r,s}^{\mathrm{best}}
   =\frac1{2\pi\gamma_s(\alpha)},}
   \]
   因而实际上不依赖于 \(r\)。
3. 以下给出的逼近指数和连分数条件，完全确定 \(\mathcal S_\alpha\)，包括端点是否取到。

**先证明 Fourier 判据和可逆性。**

若题中的估计对某个 \(r\) 成立，取 \(u=e_k\)，便有
\[
1\le2\pi C_{\alpha,r,s}
|\lambda_\alpha(k)|\langle k\rangle^s.
\]
故 \(\gamma_s(\alpha)>0\)。反过来，若 \(\gamma_s(\alpha)>0\)，则
\[
\begin{aligned}
\|u\|_{H^r}^2
&\le\frac1{4\pi^2\gamma_s(\alpha)^2}
\sum_{k\ne0}\langle k\rangle^{2(r+s)}
|2\pi i\lambda_\alpha(k)\widehat u(k)|^2\\
&=\frac1{4\pi^2\gamma_s(\alpha)^2}
\|N_\alpha u\|_{H^{r+s}}^2.
\end{aligned}
\]
单个 Fourier 模式又说明上述常数最佳。

任意光滑零均值 \(F\) 的唯一可能解为
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\lambda_\alpha(k)}.
\tag{4.1}
\]
因此，对任意无理方向，\(F\) 可光滑求解的充要条件，就是式 (4.1) 的系数快速衰减。

若某个有限 \(s\) 满足 \(\gamma_s(\alpha)>0\)，S2 适用，故每个光滑零均值 \(F\) 都有唯一光滑零均值解。所得 Sobolev 估计也说明逆在 \(C^\infty_0\) 的通常拓扑下连续。

反之，假设所有有限 \(s\) 都有 \(\gamma_s(\alpha)=0\)。可依次选取频率 \(k_j\)，使
\[
|k_j|>\max(2^j,|k_{j-1}|),\qquad
0<|\lambda_\alpha(k_j)|
\le2^{-j}\langle k_j\rangle^{-j}.
\tag{4.2}
\]
这是可行的，因为 \(\gamma_j=0\)，而任何有限频率集合上的相应最小值严格为正。

令
\[
F=\sum_{j=1}^\infty
2\pi i\lambda_\alpha(k_j)e_{k_j}.
\]
对任意固定导数阶数 \(M\)，第 \(j\) 项的导数绝对值至多为
\[
(2\pi)^{M+1}2^{-j}\langle k_j\rangle^{M-j}.
\]
当 \(j\ge M\) 时，这不超过 \((2\pi)^{M+1}2^{-j}\)。故所有导数级数绝对一致收敛，\(F\in C^\infty_0\)。但任何解都必须满足
\[
\widehat u(k_j)=1,
\]
这与光滑函数 Fourier 系数趋于零矛盾。因此并非每个光滑数据都可解。

**算术分类与端点。**

记
\[
d_\alpha(q)=\operatorname{dist}(q\alpha,\mathbb Z),
\qquad
D_s(\alpha)=\inf_{q\ge1}q^s d_\alpha(q).
\]
则
\[
\boxed{\gamma_s(\alpha)>0\iff D_s(\alpha)>0.}
\tag{4.3}
\]

证明如下。若 \(D_s>0\)，当 \(k_1\ne0\) 时，
\[
|\alpha k_1+k_2|
\ge d_\alpha(|k_1|)
\ge D_s|k_1|^{-s}
\ge D_s\langle k\rangle^{-s}.
\]
当 \(k_1=0\) 时，\(|k_2|\ge1\)，故可统一取下界常数 \(\min(D_s,1)\)。

反过来，对每个 \(q\)，选取离 \(q\alpha\) 最近的整数 \(p\)。此时
\[
\langle(q,-p)\rangle\le A_\alpha q
\]
，其中 \(A_\alpha\) 是仅依赖 \(\alpha\) 的有限常数。因此
\[
d_\alpha(q)
\ge\gamma_s(\alpha)A_\alpha^{-s}q^{-s},
\]
证明了式 (4.3)。

定义
\[
\tau(\alpha)
=\limsup_{q\to\infty}
\frac{\log(1/d_\alpha(q))}{\log q}.
\]
首先，\(\tau(\alpha)\ge1\)。事实上，Dirichlet 抽屉原理给出：对每个整数 \(Q\ge1\)，存在 \(1\le q\le Q\)，使
\[
d_\alpha(q)<Q^{-1}\le q^{-1}.
\]
这些 \(q\) 必须无界，否则与有限个正数 \(d_\alpha(q)\) 的最小值为正矛盾。这也说明所有 \(s<1\) 都不允许。

若 \(s>\tau(\alpha)\)，取 \(\tau(\alpha)<t<s\)。充分大的 \(q\) 满足 \(d_\alpha(q)\ge q^{-t}\)，而有限个剩余 \(q\) 的贡献有正下界，故 \(D_s>0\)。

若 \(s<\tau(\alpha)\)，取 \(s<t<\tau(\alpha)\)；当 \(\tau=\infty\) 时任取 \(t>s\)。有无穷多个 \(q\) 满足
\[
q^s d_\alpha(q)<q^{s-t}\longrightarrow0,
\]
故 \(D_s=0\)。因此完整分类为
\[
\boxed{
\mathcal S_\alpha=
\begin{cases}
\varnothing,&\tau(\alpha)=\infty,\\[2mm]
[\tau(\alpha),\infty),
&\tau(\alpha)<\infty,\quad D_{\tau(\alpha)}(\alpha)>0,\\[2mm]
(\tau(\alpha),\infty),
&\tau(\alpha)<\infty,\quad D_{\tau(\alpha)}(\alpha)=0.
\end{cases}}
\tag{4.4}
\]

若以通常的无理性指数
\[
\mu(\alpha)=\sup\left\{\nu:
\left|\alpha-\frac pq\right|<q^{-\nu}
\text{ 对无穷多个 }(p,q)\in\mathbb Z\times\mathbb N\text{ 成立}
\right\}
\]
表述，则
\[
\mu(\alpha)=1+\tau(\alpha),
\]
因为最接近整数的选择给出
\[
\min_{p\in\mathbb Z}\left|\alpha-\frac pq\right|
=\frac{d_\alpha(q)}q.
\]
所以
\[
\boxed{
N_\alpha:C^\infty_0\to C^\infty_0
\text{ 可逆}
\iff \mu(\alpha)<\infty.
}
\]
亦即恰好是非 Liouville 无理方向。有限无理性指数决定损失的下确界；端点仍须检查式 (4.4) 中的额外条件。

还可以用连分数直接检查端点。令 \(q_n\) 为 \(\alpha\) 的简单连分数收敛分母，则
\[
\boxed{
s\in\mathcal S_\alpha
\iff \sup_n\frac{q_{n+1}}{q_n^s}<\infty,
\qquad
\tau(\alpha)=\limsup_n\frac{\log q_{n+1}}{\log q_n}.
}
\tag{4.5}
\]
这里援引适用于任意实无理数的连分数误差公式和最佳逼近定理：忽略有限个初项后，
\[
\frac1{q_{n+1}+q_n}<d_\alpha(q_n)<\frac1{q_{n+1}},
\qquad
d_\alpha(q)\ge d_\alpha(q_n)\quad(q_n\le q<q_{n+1}).
\]
若 \(D_s>0\)，第一组不等式给出 \(q_{n+1}<D_s^{-1}q_n^s\)。反之，若 \(q_{n+1}\le Bq_n^s\)，则在上述分母区间内，
\[
q^s d_\alpha(q)
\ge\frac{q_n^s}{q_{n+1}+q_n}
\ge\frac1{2B};
\]
有限个初项不影响正下界。这证明第一个等价式。第二个公式由沿 \(q=q_n\) 的下界，以及
\[
\frac{\log(1/d_\alpha(q))}{\log q}
\le\frac{\log(q_{n+1}+q_n)}{\log q_n}
\quad(q_n\le q<q_{n+1})
\]
得到。

特别地，\(s=1\) 允许，当且仅当连分数部分商有界，因为
\[
\frac{q_{n+1}}{q_n}
=a_{n+1}+\frac{q_{n-1}}{q_n}.
\]

**现在考虑 \(\alpha_*=\sqrt2-1\)。**

取代数共轭
\[
\alpha'=-\sqrt2-1,\qquad
B=\sqrt{1+(\alpha')^2}=\sqrt{4+2\sqrt2}.
\]
对所有 \(k\ne0\)，
\[
(\alpha_*k_1+k_2)(\alpha'k_1+k_2)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数，绝对值至少为 \(1\)。又有
\[
|\alpha'k_1+k_2|\le B|k|,
\]
所以
\[
|\alpha_*k_1+k_2|
\ge\frac1{B|k|}
\ge B^{-1}\langle k\rangle^{-1}.
\tag{4.6}
\]
故 \(s=1\) 允许；前面的 Dirichlet 论证排除了所有 \(s<1\)。因此
\[
\boxed{\mathcal S_{\alpha_*}=[1,\infty),\qquad
\text{最小损失为 }1\text{，且取到。}}
\]

最后，题中的 \(C^m\) 估计成立。二维环面上的 Sobolev 嵌入给出
\[
H^{m+2}\hookrightarrow C^m,
\]
其适用条件是 \((m+2)-m=2>2/2\)。结合式 (4.6)，
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le A_m\|N_{\alpha_*}^{-1}F\|_{H^{m+2}}
\le\frac{A_mB}{2\pi}\|F\|_{H^{m+3}}.
\]
对整数阶 Sobolev 范数，Parseval 公式及
\((1+|k|^2)^{m+3}\) 的多项式展开给出
\[
\|F\|_{H^{m+3}}
\le B_m\|F\|_{C^{m+3}}
\le B_m\|F\|_{C^{m+4}}.
\]
于是对每个 \(m\in\mathbb N_0\)，存在与 \(F\) 无关的有限 \(C_m\)，使
\[
\boxed{
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le C_m\|F\|_{C^{m+4}}.
}
\]

## S5

**不存在这样的 \(J,s,C\)。**

假设存在。由有理数稠密性，选取 \(p/q\in J\)，其中 \(q\ge1\)。令
\[
\alpha_j=\frac pq+\frac{\sqrt2}{j}.
\]
每个 \(\alpha_j\) 都无理，且充分大的 \(j\) 满足 \(\alpha_j\in J\)。

固定
\[
u=e_{(q,-p)}.
\]
归一化 Haar 测度下 \(\|u\|_{L^2}=1\)，而
\[
\|N_{\alpha_j}u\|_{H^s}
=2\pi|\alpha_jq-p|\langle(q,-p)\rangle^s
=\frac{2\pi q\sqrt2}{j}\langle(q,-p)\rangle^s
\longrightarrow0.
\]
所假设的一致估计于是要求 \(1\le C\,o(1)\)，矛盾。事实上，同一论证排除了任意非空开区间上的这种一致估计。

## S6

设
\[
q_n=10^{n!},\qquad
p_n=\sum_{j=1}^n10^{\,n!-j!}\in\mathbb Z.
\]
则
\[
\frac{p_n}{q_n}=\sum_{j=1}^n10^{-j!}.
\]
尾项满足
\[
0<\alpha-\frac{p_n}{q_n}
=\sum_{j=n+1}^\infty10^{-j!}
<2\,10^{-(n+1)!}.
\]
因此
\[
\boxed{
0<\varepsilon_n:=q_n\alpha-p_n
<2\,10^{-n\,n!}=2q_n^{-n}.
}
\tag{6.1}
\]

先证明无理性。若 \(\alpha=a/b\)，其中 \(b\ge1\)，则
\[
\varepsilon_n=\frac{aq_n-bp_n}{b}>0
\]
是一个正的 \(1/b\) 的整数倍，故 \(\varepsilon_n\ge1/b\)。这与式 (6.1) 中 \(\varepsilon_n\to0\) 矛盾。

现在令
\[
k_n=(q_n,-p_n),\qquad
\boxed{
F(y)=\sum_{n=1}^\infty
q_n^{-n}e^{2\pi i(q_ny_1-p_ny_2)}.
}
\tag{6.2}
\]
这是一个固定的数据，全部频率同时包含在其中。

因为 \(0<p_n/q_n<\alpha<1\)，
\[
q_n\le |k_n|\le\sqrt2q_n.
\]
对任意固定阶数 \(M\) 的偏导，第 \(n\) 项的绝对值至多为
\[
(2\pi)^M|k_n|^Mq_n^{-n}
\le(2\pi\sqrt2)^M q_n^{M-n}.
\]
当 \(n\ge M+1\) 时，
\[
q_n^{M-n}\le q_n^{-1}=10^{-n!},
\]
而 \(\sum_n10^{-n!}<\infty\)。故式 (6.2) 的所有导数级数均绝对一致收敛，因而 \(F\) 光滑；所有频率非零，所以 \(F\) 零均值。

若存在光滑零均值解 \(u\)，在频率 \(k_n\) 上必有
\[
2\pi i\varepsilon_n\widehat u(k_n)=q_n^{-n}.
\]
由式 (6.1)，
\[
|\widehat u(k_n)|
=\frac{q_n^{-n}}{2\pi\varepsilon_n}
>\frac1{4\pi}.
\]
但 \(|k_n|\to\infty\)，而光滑函数的 Fourier 系数必须趋于零，矛盾。因此上述同一个 \(F\in C^\infty_0(\mathbb T^2)\) 满足
\[
\boxed{N_\alpha u=F\quad\text{没有光滑零均值解。}}
\]