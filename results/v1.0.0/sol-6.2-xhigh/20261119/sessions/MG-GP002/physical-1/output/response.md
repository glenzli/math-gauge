## S1 有限频带上的逆

记 \(e_k(y)=e^{2\pi i k\cdot y}\)，\(\lambda_\alpha(k)=\alpha k_1+k_2\)。则
\[
N_\alpha e_k=2\pi i\lambda_\alpha(k)e_k.
\]
当 \(k\ne0\) 时，若 \(k_1=0\)，则 \(\lambda_\alpha(k)=k_2\ne0\)。若 \(k_1\ne0\)，则由 \(\alpha\) 无理可知 \(\lambda_\alpha(k)\ne0\)。因此对 \(F\in H_N\)，唯一的 \(H_N\) 内解为
\[
N_\alpha^{-1}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\lambda_\alpha(k)}e_k.
\]

对任意 \(r\in\mathbb R\)，逆算子的精确范数为
\[
\boxed{\displaystyle
\big\|(N_\alpha|_{H_N})^{-1}\big\|_{H^r\to H^r}
=\frac{1}{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.}
\]
在 \(H^r\) 范数的加权平方和中逐项取乘子的最大绝对值，得到上界。取 \(F=e_k\)，其中 \(k\) 实现上式的最小值，即达到该上界。

## S2 有算术界的截断误差

在给定下界下，定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\lambda_\alpha(k)}
\quad(k\ne0).
\]
光滑函数的 Fourier 系数快速衰减。这可由在满足 \(|k_j|\ge |k|/\sqrt2\) 的坐标上反复分部积分得到。上述除法至多使系数增长 \((2\pi c)^{-1}\langle k\rangle^s\) 倍，所以 \(\widehat u(k)\) 仍快速衰减。由于 \(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-d}<\infty\) 对 \(d>2\) 成立，该 Fourier 级数及其任意阶逐项导数都绝对一致收敛，因而定义了光滑零均值函数 \(u\)。逐项施加 \(N_\alpha\) 得 \(N_\alpha u=F\)。这里等式由 Fourier 系数相同推出，因为 \((e_k)\) 是 \(L^2(\mathbb T^2)\) 的完备正交基。由 S1 的非零频率乘子均非零，光滑零均值解唯一。

由 S1，\(u_N\) 恰为 \(u\) 的频带截断。对任意 \(r\in\mathbb R\)、\(q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}\langle k\rangle^{2r}
   \frac{|\widehat F(k)|^2}{4\pi^2|\lambda_\alpha(k)|^2}\\
&\le (2\pi c)^{-2}\sum_{|k|>N}
   \langle k\rangle^{-2q}\langle k\rangle^{2(r+s+q)}
   |\widehat F(k)|^2\\
&\le (2\pi c)^{-2}(1+N^2)^{-q}\|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
开平方即得所求估计。

## S3 固定频带内改变方向

对 \(0<|k|\le N\)，由 S1，
\[
\widehat{u_\alpha-u_\beta}(k)
=\frac{(\beta-\alpha)k_1}
{2\pi i\lambda_\alpha(k)\lambda_\beta(k)}\widehat F(k).
\]
两个分母因子的绝对值都至少为 \(\delta\)，且 \(|k_1|\le N\)。对各频率取加权平方和，得到
\[
\boxed{\displaystyle
\|u_\alpha-u_\beta\|_{H^r}
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4 整体对象与全部恢复目标

设 \(p_n/q_n\) 为 \(\alpha\) 的简单连分数收敛分数，定义
\[
w(\alpha)=\limsup_{n\to\infty}\frac{\log q_{n+1}}{\log q_n},
\]
其中略去 \(q_n=1\) 的项。则 \(w(\alpha)\in[1,\infty]\)。算子 \(N_\alpha\) 在 \(C^\infty_0(\mathbb T^2)\) 上可逆，当且仅当 \(w(\alpha)<\infty\)，也就是当且仅当 \(\alpha\) 的无理性指数有限。

全部允许的 Sobolev 损失恰为满足
\[
\boxed{\displaystyle \sup_{n\ge1}\frac{q_{n+1}}{q_n^s}<\infty}
\]
的 \(s\ge0\)。若 \(w(\alpha)=\infty\)，则没有有限的允许损失。若 \(w(\alpha)<\infty\)，则所有 \(s>w(\alpha)\) 都允许，所有 \(s<w(\alpha)\) 都不允许。端点 \(s=w(\alpha)\) 是否允许，由上式在该端点是否有限决定。

### Fourier 判据与光滑可解性

对 \(s\ge0\)，令
\[
A_{\alpha,s}=\inf_{k\in\mathbb Z^2\setminus\{0\}}
\langle k\rangle^s|\lambda_\alpha(k)|.
\]
若 \(A_{\alpha,s}>0\)，则对任意 \(r\) 及任意光滑零均值 \(u\)，由 Fourier 范数逐项得到
\[
\|u\|_{H^r}\le \frac{1}{2\pi A_{\alpha,s}}
\|N_\alpha u\|_{H^{r+s}}.
\]
反过来，若对某个 \(r\) 存在有限常数 \(C\)，取 \(u=e_k\) 即得
\[
1\le 2\pi C\langle k\rangle^s|\lambda_\alpha(k)|\qquad(k\ne0).
\]
因此 \(A_{\alpha,s}>0\)，且每个 \(r\) 的最佳常数均为 \((2\pi A_{\alpha,s})^{-1}\)。

\(N_\alpha\) 保持光滑性，且周期导数的积分为零，所以它确实映入 \(C^\infty_0\)。由 S1 的乘子非零和 Fourier 完备性，它在该空间上是单射。若某个有限 \(s\ge0\) 满足 \(A_{\alpha,s}>0\)，则以 \(c=A_{\alpha,s}\) 应用 S2 的构造，每个 \(F\in C^\infty_0\) 都有唯一的光滑零均值解。

若对所有有限 \(s\ge0\) 都有 \(A_{\alpha,s}=0\)，则可依次选取 \(|k_j|\) 严格递增的非零整数频率，使
\[
0<|\lambda_\alpha(k_j)|\le\langle k_j\rangle^{-j}.
\]
事实上，对于 \(s=j\)，任一有限频率集合上的加权小除数都有正的最小值，故取下确界为零的频率时可以避开该集合。令
\[
F=\sum_{j=1}^\infty 2\pi i\lambda_\alpha(k_j)e_{k_j}.
\]
这些系数快速衰减，故由 S2 的 Fourier 收敛论证，\(F\) 光滑且零均值。任何光滑解都必须满足 \(\widehat u(k_j)=1\) 对所有 \(j\) 成立，与光滑函数 Fourier 系数趋于零矛盾。这证明了满射性确实要求某个有限的允许损失。

### 连分数分类及端点

记 \(\|x\|_{\mathbb Z}=\min_{p\in\mathbb Z}|x-p|\)，并令
\[
B_{\alpha,s}=\inf_{q\in\mathbb N,\ q\ge1}q^s\|q\alpha\|_{\mathbb Z}.
\]
若 \(B_{\alpha,s}>0\)，则对 \(k_1\ne0\)，
\[
|\lambda_\alpha(k)|\ge B_{\alpha,s}|k_1|^{-s}
\ge B_{\alpha,s}\langle k\rangle^{-s}.
\]
而 \(k_1=0,\ k_2\ne0\) 时，\(|\lambda_\alpha(k)|\ge1\)。反过来，取最接近 \(q\alpha\) 的整数 \(p\)，则 \(|p|\le (|\alpha|+1/2)q\)，从而
\[
\langle(q,-p)\rangle\le D_\alpha q,\qquad
D_\alpha=\sqrt{2+(|\alpha|+1/2)^2}.
\]
若 \(A_{\alpha,s}>0\)，在 \(k=(q,-p)\) 处使用其下界，就得
\(q^s\|q\alpha\|_{\mathbb Z}\ge A_{\alpha,s}D_\alpha^{-s}\)。
故 \(A_{\alpha,s}>0\) 等价于 \(B_{\alpha,s}>0\)。

为检验 \(B_{\alpha,s}\)，写 \(\alpha=[a_0;a_1,a_2,\ldots]\)，其中 \(a_0=\lfloor\alpha\rfloor\)，\(a_j\ge1\) 对 \(j\ge1\) 成立。收敛分数的递推为
\[
(p_{-1},q_{-1})=(1,0),\qquad (p_0,q_0)=(a_0,1),\qquad
(p_{n+1},q_{n+1})=a_{n+1}(p_n,q_n)+(p_{n-1},q_{n-1}).
\]
递推使相邻两向量的行列式交替为 \(\pm1\)，且 \(q_n\) 从 \(n=1\) 起严格递增并趋于无穷。设 \(t=[a_{n+1};a_{n+2},\ldots]\)。将尾项代回连分数得
\[
\alpha=\frac{p_n t+p_{n-1}}{q_n t+q_{n-1}},
\qquad a_{n+1}<t<a_{n+1}+1.
\]
因此误差 \(\varepsilon_n=q_n\alpha-p_n\) 交替变号，且
\[
\frac1{q_{n+1}+q_n}<|\varepsilon_n|
=\frac1{q_n t+q_{n-1}}<\frac1{q_{n+1}}.
\]

对 \(0<q<q_{n+1}\) 和任意整数 \(p\)，有 \(|q\alpha-p|\ge|\varepsilon_n|\)。为证明这一点，将 \((q,p)\) 写成相邻基向量 \((q_n,p_n),(q_{n+1},p_{n+1})\) 的整数线性组合，系数记为 \(a,b\)。若 \(b=0\)，则 \(a\ne0\)，误差绝对值为 \(|a||\varepsilon_n|\)。若 \(b\ne0\)，由 \(0<q<q_{n+1}\) 可知 \(a,b\) 均非零且异号。由于 \(\varepsilon_n,\varepsilon_{n+1}\) 异号，\(a\varepsilon_n\) 与 \(b\varepsilon_{n+1}\) 同号，故误差绝对值至少为 \(|a||\varepsilon_n|\ge|\varepsilon_n|\)。

若 \(B_{\alpha,s}>0\)，则
\[
B_{\alpha,s}q_n^{-s}\le\|q_n\alpha\|_{\mathbb Z}
\le|\varepsilon_n|<q_{n+1}^{-1},
\]
所以 \(q_{n+1}/q_n^s\) 有界。反之，若该比值对 \(n\ge1\) 的上界为 \(M<\infty\)，则对每个 \(q\ge q_1\) 取 \(q_n\le q<q_{n+1}\)。刚证明的误差下界给出
\[
\|q\alpha\|_{\mathbb Z}\ge|\varepsilon_n|
>\frac1{q_{n+1}+q_n}
\ge \frac1{2M q_n^s}\ge \frac1{2M q^s}.
\]
余下的 \(1\le q<q_1\) 只有有限多个，且 \(\alpha\) 无理保证各自的 \(\|q\alpha\|_{\mathbb Z}>0\)，故 \(B_{\alpha,s}>0\)。

由 \(q_{n+1}>q_n\) 得 \(w(\alpha)\ge1\)。若 \(s>w(\alpha)\)，则最终 \(q_{n+1}/q_n^s\le1\)。若 \(s<w(\alpha)\)，则存在 \(\eta>0\)，使该比值对无穷多个 \(n\) 至少为 \(q_n^\eta\)，因而无界。这就给出了上述分类和端点条件。

若将无理性指数 \(\mu(\alpha)\) 定义为使 \(0<|\alpha-p/q|<q^{-\nu}\) 有无穷多个有理近似的指数 \(\nu\) 的上确界，则 \(\mu(\alpha)=1+w(\alpha)\)。事实上，\(\nu<1+w(\alpha)\) 时，无穷多个 \(n\) 满足 \(q_{n+1}>q_n^{\nu-1}\)，相应收敛分数满足所需上界。若 \(\nu>1+w(\alpha)\)，取 \(w(\alpha)<s<\nu-1\)，则 \(B_{\alpha,s}>0\)，对所有 \(p,q\) 有 \(|\alpha-p/q|\ge B_{\alpha,s}q^{-1-s}\)，从而充分大的 \(q\) 无法满足所需上界。因此可逆的方向恰为非刘维尔无理数。

### \(\alpha_*=\sqrt2-1\) 的最小损失和 \(C^m\) 估计

令 \(\alpha'=-\sqrt2-1\) 及 \(D=\sqrt{1+(\alpha')^2}\)。对 \(k\ne0\)，
\[
(\alpha_* k_1+k_2)(\alpha' k_1+k_2)=k_2^2-2k_1k_2-k_1^2
\]
是非零整数，因为两个因子都不为零。又由 Cauchy–Schwarz 不等式，\(|\alpha' k_1+k_2|\le D|k|\)。于是
\[
|\lambda_{\alpha_*}(k)|\ge D^{-1}|k|^{-1}
\ge D^{-1}\langle k\rangle^{-1}.
\]
因此 \(s=1\) 允许。由于所有无理方向均有 \(w(\alpha)\ge1\)，故 \(\alpha_*\) 的**最小允许损失为 \(1\)，且取到**。

所问的 \(C^m\) 估计对每个 \(m\in\mathbb N_0\) 都成立。对每个 \(k\ne0\)，选择 \(|k_j|\ge |k|/\sqrt2\) 的坐标，在该坐标分部积分 \(m+4\) 次，得到
\[
|\widehat F(k)|\le
\left(\frac{\sqrt2}{2\pi}\right)^{m+4}
|k|^{-m-4}\|F\|_{C^{m+4}}.
\]
对零均值解 \(u=N_{\alpha_*}^{-1}F\)，上述小除数下界给出
\(|\widehat u(k)|\le (D/2\pi)|k|\,|\widehat F(k)|\)。
当 \(a+b\le m\) 时，导数的 Fourier 乘子绝对值至多为 \((2\pi)^m |k|^m\)。求和并取各阶导数的最大值，便得
\[
\|u\|_{C^m}\le C_m\|F\|_{C^{m+4}},\qquad
C_m=\frac{D}{2\pi}(2\pi)^m
\left(\frac{\sqrt2}{2\pi}\right)^{m+4}
\sum_{k\ne0}|k|^{-3}<\infty.
\]

## S5 邻近方向的一致估计

不存在这样的 \(J,s,C\)。任取包含 \(\alpha_*\) 的开区间 \(J\)，在其中选一个有理数 \(a/b\)，其中 \(a,b\in\mathbb Z\)、\(b\ge1\)。固定 \(k=(b,-a)\) 及光滑零均值函数 \(u=e_k\)。取 \(\alpha_j=a/b+\sqrt2/j\)，则这些方向均无理，且充分大的 \(j\) 满足 \(\alpha_j\in J\)。由测度归一化，
\[
\|u\|_{L^2}=1,\qquad
\|N_{\alpha_j}u\|_{H^s}
=2\pi b|\alpha_j-a/b|\langle k\rangle^s\longrightarrow0.
\]
对任何固定的有限 \(s\) 和 \(C\)，所求不等式都会在充分大的 \(j\) 处失败。

## S6 一个具体方向的不可解数据

令 \(Q_n=10^{n!}\)，\(P_n=Q_n\sum_{j=1}^n10^{-j!}\in\mathbb Z\)。由于尾部的阶乘指数严格递增，
\[
0<\alpha-\frac{P_n}{Q_n}
=\sum_{j>n}10^{-j!}
\le\frac{10}{9}\,10^{-(n+1)!}<2Q_n^{-(n+1)}.
\]
若 \(\alpha=A/B\) 为有理数，取整数 \(A,B\) 且 \(B\ge1\)。上式左侧为正，故它至少是 \(1/(BQ_n)\)，这与上界在 \(n\) 充分大时矛盾。因此 \(\alpha\) 无理。

取 \(k_n=(Q_n,-P_n)\)。这些频率非零且互异，并满足
\[
0<\lambda_\alpha(k_n)=Q_n\alpha-P_n<2Q_n^{-n}.
\]
又因为 \(0<P_n<Q_n\)，所以 \(\langle k_n\rangle\le\sqrt3\,Q_n\)。定义同一个右端项
\[
\boxed{\displaystyle F(y)=\sum_{n=1}^\infty
 2\pi i(Q_n\alpha-P_n)e^{2\pi i(Q_n y_1-P_n y_2)}.}
\]
对任意固定整数 \(L\ge0\)，当 \(n\ge L\) 时，
\(Q_n^{-n}\le Q_n^{-L}\le(\sqrt3)^L\langle k_n\rangle^{-L}\)。
故该级数的系数快速衰减，由 S2 的收敛论证，\(F\in C^\infty_0(\mathbb T^2)\)。若存在光滑零均值解，则在每个 \(k_n\) 上比较 Fourier 系数，得到 \(\widehat u(k_n)=1\)。由于 \(|k_n|\to\infty\)，这与 \(u\) 的光滑性矛盾。