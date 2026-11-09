记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad d_\alpha(k)=\alpha k_1+k_2.
\]
则
\[
N_\alpha e_k=2\pi i\,d_\alpha(k)e_k.
\]
当 \(\alpha\) 无理时，\(d_\alpha(k)\ne0\) 对所有 \(k\ne0\) 成立。

以下使用 Fourier 级数的标准事实：环面上的光滑函数恰好对应快速衰减的 Fourier 系数。正向由分部积分得到；反向则利用
\(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-p}<\infty\)（\(p>2\)），使各阶导数级数绝对一致收敛。

**S1．有限频带上的逆**

对 \(F\in H_N\)，定义
\[
R_{\alpha,N}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
所有分母均非零，因此这是 \(H_N\) 上的双边逆。

对任意 \(r\in\mathbb R\)，
\[
\|R_{\alpha,N}F\|_{H^r}^2
=\sum_{0<|k|\le N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{4\pi^2|d_\alpha(k)|^2}.
\]
故精确算子范数为
\[
\boxed{
\|R_{\alpha,N}\|_{H^r\to H^r}
=\frac1{2\pi}
\max_{0<|k|\le N}\frac1{|\alpha k_1+k_2|}
}.
\]
上界由逐项估计得到；取达到上述最大值的单个 Fourier 模态，就得到等号。特别地，该范数与 \(r\) 无关。

**S2．有算术界的截断误差**

假设
\[
|d_\alpha(k)|\ge c\langle k\rangle^{-s}\qquad(k\ne0).
\]
对光滑零均值 \(F\)，定义
\[
u=\sum_{k\ne0}\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
由于
\[
|\widehat u(k)|
\le \frac1{2\pi c}\langle k\rangle^s|\widehat F(k)|,
\]
除后系数仍快速衰减，故 \(u\) 光滑、零均值，并且可以逐项求导得到 \(N_\alpha u=F\)。各非零频率的系数被方程唯一确定，零频率由零均值条件确定，所以解唯一。

S1 中的解正是
\[
u_N=\sum_{0<|k|\le N}\widehat u(k)e_k.
\]
对任意 \(r\in\mathbb R,\ q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{4\pi^2|d_\alpha(k)|^2}\\
&\le \frac1{(2\pi c)^2}
\sum_{|k|>N}
\langle k\rangle^{-2q}
\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}
\|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
开平方即得
\[
\boxed{
\|u-u_N\|_{H^r}
\le(2\pi c)^{-1}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}}
}.
\]

**S3．固定频带内改变方向**

对 \(0<|k|\le N\)，
\[
\widehat{u_\alpha-u_\beta}(k)
=\frac{\widehat F(k)}{2\pi i}
\left(\frac1{d_\alpha(k)}-\frac1{d_\beta(k)}\right)
=\frac{(\beta-\alpha)k_1\,\widehat F(k)}
{2\pi i\,d_\alpha(k)d_\beta(k)}.
\]
根据假设，两分母的绝对值均至少为 \(\delta\)，且 \(|k_1|\le N\)。因此
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat F(k)|.
\]
乘以 Sobolev 权重、平方求和，得到对所有 \(r\in\mathbb R\)，
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}
}.
\]

**S4．整体可逆性、全部损失及端点**

并非每个无理方向都在 \(C^\infty_0\) 上可逆。其充要条件是小除数具有某个有限阶的多项式下界；全部允许损失还需要区分临界端点。

对 \(s\ge0\)，定义
\[
\Gamma_s(\alpha)
=\inf_{k\in\mathbb Z^2\setminus\{0\}}
\langle k\rangle^s|d_\alpha(k)|,
\qquad
\mathcal A(\alpha)=\{s\ge0:\Gamma_s(\alpha)>0\}.
\]

首先，所要求的 Sobolev 估计成立，当且仅当
\[
\boxed{s\in\mathcal A(\alpha).}
\]
事实上，若 \(\Gamma_s(\alpha)>0\)，逐项估计给出
\[
\|u\|_{H^r}
\le \frac1{2\pi\Gamma_s(\alpha)}
\|N_\alpha u\|_{H^{r+s}}
\qquad(r\in\mathbb R).
\]
反之，将任一这样的估计应用于 \(u=e_k\)，约去 \(\langle k\rangle^r\)，得到
\[
1\le 2\pi C_{\alpha,r,s}\,
|d_\alpha(k)|\langle k\rangle^s.
\]
故 \(\Gamma_s(\alpha)>0\)。这也证明最优常数为
\[
\boxed{
C_{\alpha,r,s}^{\mathrm{opt}}
=\frac1{2\pi\Gamma_s(\alpha)}
},
\]
与 \(r\) 无关。因此，对某一个 \(r\) 成立与对每个 \(r\) 成立等价。

下面给出包含端点的算术分类。记
\[
\|x\|_{\mathbb R/\mathbb Z}=\min_{p\in\mathbb Z}|x-p|,
\qquad
b_s(\alpha)=\inf_{q\ge1}q^s\|q\alpha\|_{\mathbb R/\mathbb Z}.
\]
则
\[
\Gamma_s(\alpha)>0
\quad\Longleftrightarrow\quad b_s(\alpha)>0.
\]
证明如下：

- 若 \(\Gamma_s>0\)，给每个 \(q\) 选择距 \(q\alpha\) 最近的整数 \(p\)。存在仅依赖于 \(\alpha\) 的 \(A_\alpha\)，使
  \(\langle(q,-p)\rangle\le A_\alpha q\)，故
  \[
  \|q\alpha\|_{\mathbb R/\mathbb Z}
  \ge\Gamma_s A_\alpha^{-s}q^{-s}.
  \]
- 若 \(b_s>0\)，当 \(k_1\ne0\) 时，
  \[
  |d_\alpha(k)|
  \ge\||k_1|\alpha\|_{\mathbb R/\mathbb Z}
  \ge b_s|k_1|^{-s}
  \ge b_s\langle k\rangle^{-s}.
  \]
  当 \(k_1=0,\ k\ne0\) 时，\(|d_\alpha(k)|=|k_2|\ge1\)。所以
  \(\Gamma_s\ge\min(b_s,1)>0\)。

令 \(\theta=\alpha-\lfloor\alpha\rfloor\in(0,1)\)，并设其正规连分数为
\[
\theta=[0;a_1,a_2,\ldots],
\]
收敛分数为 \(P_n/Q_n\)。对这里的无理数 \(\theta\)，连分数误差界及第二类最佳逼近定理给出：对 \(n\ge1\)，
\[
\frac1{Q_n+Q_{n+1}}
<
\|Q_n\theta\|_{\mathbb R/\mathbb Z}
<
\frac1{Q_{n+1}},
\]
并且当 \(Q_n\le q<Q_{n+1}\) 时，
\[
\|q\theta\|_{\mathbb R/\mathbb Z}
\ge\|Q_n\theta\|_{\mathbb R/\mathbb Z}.
\]
由于 \(\|q\alpha\|_{\mathbb R/\mathbb Z}=\|q\theta\|_{\mathbb R/\mathbb Z}\)，这些定理适用于当前的小除数。

由此得到精确判据
\[
\boxed{
s\in\mathcal A(\alpha)
\quad\Longleftrightarrow\quad
\sup_{n\ge1}\frac{Q_{n+1}}{Q_n^s}<\infty.
}
\]
确实，若 \(b_s>0\)，则
\[
b_sQ_n^{-s}\le\|Q_n\alpha\|_{\mathbb R/\mathbb Z}
< Q_{n+1}^{-1},
\]
所以该上确界有限。反之，若 \(Q_{n+1}\le M Q_n^s\)，则对 \(Q_n\le q<Q_{n+1}\)，
\[
\|q\alpha\|_{\mathbb R/\mathbb Z}
>\frac1{2Q_{n+1}}
\ge\frac1{2M Q_n^s}
\ge\frac1{2M q^s}.
\]
有限个遗漏的小分母也有正下界，因为 \(\alpha\) 无理。

定义
\[
\tau(\alpha)=\limsup_{n\to\infty}
\frac{\log Q_{n+1}}{\log Q_n}\in[1,\infty].
\]
那么全部允许损失为
\[
\boxed{
\begin{cases}
\mathcal A(\alpha)=\varnothing,
&\tau(\alpha)=\infty,\\[2mm]
\mathcal A(\alpha)=[\tau(\alpha),\infty),
&\tau(\alpha)<\infty,\
\displaystyle\sup_n\frac{Q_{n+1}}{Q_n^{\tau(\alpha)}}<\infty,\\[3mm]
\mathcal A(\alpha)=(\tau(\alpha),\infty),
&\tau(\alpha)<\infty,\
\displaystyle\sup_n\frac{Q_{n+1}}{Q_n^{\tau(\alpha)}}=\infty.
\end{cases}
}
\]
这是因为 \(s>\tau\) 时，上述比值最终有界；\(s<\tau\) 时，它沿一个子列趋于无穷。特别地，任何无理方向都不允许 \(s<1\)。

端点也可直接用部分商判定。由
\[
Q_{n+1}=a_{n+1}Q_n+Q_{n-1}
\]
及 \(\tau\ge1\)，可知有限端点 \(\tau\) 被允许，当且仅当
\[
a_{n+1}=O(Q_n^{\tau-1}).
\]
尤其，当 \(\tau=1\) 时，端点被允许恰好等价于部分商有界。

若采用通常的无理性指数
\[
\mu(\alpha)=\sup\left\{\nu:
\left|\alpha-\frac pq\right|<q^{-\nu}
\text{ 对无穷多个 }(p,q)\in\mathbb Z\times\mathbb N\text{ 成立}
\right\},
\]
则
\[
\mu(\alpha)=1+\tau(\alpha).
\]
为说明这一关系，由定义，
\[
\mu(\alpha)
=1+\limsup_{q\to\infty}
\frac{-\log\|q\alpha\|_{\mathbb R/\mathbb Z}}{\log q}.
\]
在 \(q=Q_n\) 上，误差上界给出该 \(\limsup\ge\tau\)；对
\(Q_n\le q<Q_{n+1}\)，最佳逼近下界给出
\[
\frac{-\log\|q\alpha\|_{\mathbb R/\mathbb Z}}{\log q}
\le\frac{\log(2Q_{n+1})}{\log Q_n},
\]
从而反向不等式也成立。因此临界损失是 \(\mu(\alpha)-1\)，但仅知道 \(\mu\) 不能判定端点是否取到。

现在证明整体光滑可逆性的结论：
\[
\boxed{
N_\alpha:C^\infty_0\longrightarrow C^\infty_0
\text{ 双射}
\iff
\mathcal A(\alpha)\ne\varnothing
\iff
\mu(\alpha)<\infty.
}
\]
亦即，在无理数中，恰好是非 Liouville 数对应整体光滑可逆方向。

单射性对每个无理 \(\alpha\) 都成立：\(N_\alpha u=0\) 使所有非零 Fourier 系数消失，零均值又使零系数消失。

若 \(\Gamma_s(\alpha)>0\) 对某个有限 \(s\) 成立，则 S2 的条件以
\(c=\Gamma_s(\alpha)\) 满足。因而对每个光滑零均值 \(F\)，唯一解是
\[
N_\alpha^{-1}F
=\sum_{k\ne0}\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
前面的 Sobolev 估计也表明，该逆在 \(C^\infty\) 的通常 Fréchet 拓扑下连续。

反之，假设所有有限阶多项式下界均失败。可以选择互异频率 \(k_j\)，使
\[
|k_j|\ge2^j,\qquad
0<|d_\alpha(k_j)|\le\langle k_j\rangle^{-j}.
\]
这样的频率可以任意大：否则，有限个非零小除数的正最小值会与其余频率上的下界合并，产生一个正的多项式下界。

定义同一个右端项
\[
F=2\pi i\sum_{j=1}^\infty d_\alpha(k_j)e_{k_j}.
\]
对任意总阶数为 \(m\) 的偏导，每项的绝对值至多为
\[
(2\pi)^{m+1}\langle k_j\rangle^{m-j}.
\]
当 \(j>m\) 时，它至多为
\((2\pi)^{m+1}2^{-j(j-m)}\)，可求和。因此 \(F\in C^\infty_0\)。

然而，任何光滑解都必须满足
\[
\widehat u(k_j)
=\frac{\widehat F(k_j)}{2\pi i\,d_\alpha(k_j)}=1.
\]
这与光滑函数的 Fourier 系数趋于零矛盾，故不满射。

更一般地，对任意固定的光滑 \(F\)，其光滑可解的充要条件，就是
\[
\left(\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}\right)_{k\ne0}
\]
快速衰减；可解时，零均值解由上述公式唯一给出。

最后处理 \(\alpha_*=\sqrt2-1\)。令其代数共轭为
\(\alpha'=-\sqrt2-1\)。对 \(k\ne0\)，
\[
d_{\alpha_*}(k)d_{\alpha'}(k)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数：若 \(k_1\ne0\)，其为零会要求
\(k_2/k_1=1\pm\sqrt2\)；若 \(k_1=0\)，则它是非零的 \(k_2^2\)。故其绝对值至少为 \(1\)。

又有
\[
|d_{\alpha'}(k)|
\le\sqrt{4+2\sqrt2}\,|k|,
\]
所以
\[
|d_{\alpha_*}(k)|
\ge\frac1{\sqrt{4+2\sqrt2}\,|k|}
\ge c_*\langle k\rangle^{-1},
\qquad
c_*=\frac1{\sqrt{4+2\sqrt2}}.
\]
因此 \(s=1\) 被允许。结合所有无理数均不允许 \(s<1\)，得到
\[
\boxed{\mathcal A(\alpha_*)=[1,\infty).}
\]
最小损失为 \(1\)，且确实取到。

题目中的 \(C^m\) 估计也成立。对 \(k\ne0\)，选择一个坐标 \(j\)，使
\(|k_j|\ge|k|/\sqrt2\)。沿该坐标分部积分 \(m+4\) 次，得到
\[
|\widehat F(k)|
\le A_m\|F\|_{C^{m+4}}\langle k\rangle^{-(m+4)}.
\]
结合小除数下界，
\[
|\widehat{N_{\alpha_*}^{-1}F}(k)|
\le \frac{A_m}{2\pi c_*}
\|F\|_{C^{m+4}}\langle k\rangle^{-(m+3)}.
\]
对任意 \(a+b\le m\)，其导数级数的绝对值总和因而至多为
\[
\frac{(2\pi)^mA_m}{2\pi c_*}
\|F\|_{C^{m+4}}
\sum_{k\ne0}\langle k\rangle^{-3}.
\]
最后的和在二维收敛，故存在与 \(F\) 无关的有限常数 \(C_m\)，使
\[
\boxed{
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le C_m\|F\|_{C^{m+4}}
\qquad(m\in\mathbb N_0).
}
\]

**S5．邻近方向的一致估计**

结论是否定的，而且任何非空开区间都不存在所要求的一致估计。

假设存在这样的 \(J,s,C\)。取一个位于 \(J\) 内的有理数 \(p/q\)，其中 \(q\ge1\)，并令
\[
k=(q,-p),\qquad u=e_k.
\]
这是光滑零均值函数，且 \(\|u\|_{L^2}=1\)。

取
\[
\alpha_\ell=\frac pq+\frac{\sqrt2}{\ell}.
\]
每个 \(\alpha_\ell\) 都无理，且充分大的 \(\ell\) 满足 \(\alpha_\ell\in J\)。但
\[
\|N_{\alpha_\ell}u\|_{H^s}
=2\pi|\alpha_\ell q-p|\langle k\rangle^s
=\frac{2\pi q\sqrt2}{\ell}\langle k\rangle^s
\longrightarrow0.
\]
假设的一致估计将给出
\[
1\le C\|N_{\alpha_\ell}u\|_{H^s}\longrightarrow0,
\]
矛盾。因此
\[
\boxed{\text{不存在这样的 }J,\ s,\ C.}
\]

**S6．具体方向的单个不可解数据**

令
\[
\alpha=\sum_{n=1}^\infty10^{-n!},\qquad
q_n=10^{n!},\qquad
p_n=\sum_{j=1}^n10^{n!-j!}\in\mathbb Z.
\]
于是
\[
\frac{p_n}{q_n}=\sum_{j=1}^n10^{-j!}.
\]
尾项满足
\[
0<\alpha-\frac{p_n}{q_n}
<2\,10^{-(n+1)!},
\]
从而令 \(\varepsilon_n=q_n\alpha-p_n\)，便有
\[
\boxed{0<\varepsilon_n<2q_n^{-n}.}
\]

若 \(\alpha=a/b\) 为有理数，其中 \(b\ge1\)，则
\[
\varepsilon_n=\frac{aq_n-bp_n}{b}>0
\]
是一个正整数除以 \(b\)，因而至少为 \(1/b\)。这与
\(\varepsilon_n<2q_n^{-n}\to0\) 矛盾。所以 \(\alpha\) 无理。

现在取
\[
k_n=(q_n,-p_n)
\]
并明确构造
\[
\boxed{
F(y)=2\pi i\sum_{n=1}^\infty
(q_n\alpha-p_n)
e^{2\pi i(q_ny_1-p_ny_2)}.
}
\]
这就是所需的同一个右端项。

验证光滑性：因为 \(0<p_n/q_n<\alpha<1\)，所以
\[
q_n\le|k_n|\le\sqrt2\,q_n.
\]
对任意总阶数为 \(m\) 的偏导，第 \(n\) 项的绝对值至多为
\[
B_m q_n^m\varepsilon_n
\le 2B_m q_n^{m-n}.
\]
当 \(n\ge m+1\) 时，上式至多为 \(2B_mq_n^{-1}\)，而
\[
\sum_nq_n^{-1}=\sum_n10^{-n!}<\infty.
\]
因此各阶导数级数均绝对一致收敛，\(F\) 光滑。所有频率均非零，故 \(F\) 零均值；它们又因第一坐标 \(q_n\) 严格递增而互异。

若存在光滑解 \(N_\alpha u=F\)，则在每个 \(k_n\) 上，
\[
2\pi i\,\varepsilon_n\widehat u(k_n)
=\widehat F(k_n)=2\pi i\,\varepsilon_n.
\]
由于 \(\varepsilon_n>0\)，必有
\[
\widehat u(k_n)=1\qquad\text{对所有 }n.
\]
而 \(|k_n|\to\infty\)，这与光滑函数 Fourier 系数的衰减矛盾。因此这个 \(F\in C^\infty_0(\mathbb T^2)\) 没有光滑零均值解。