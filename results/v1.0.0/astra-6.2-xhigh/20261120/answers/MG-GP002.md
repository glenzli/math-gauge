## S1　有限频带上的逆

记 \(e_k(y)=e^{2\pi i k\cdot y}\)，\(D_\alpha(k)=\alpha k_1+k_2\)。由于
\[
N_\alpha e_k=2\pi iD_\alpha(k)e_k,
\]
而 \(\alpha\) 无理时每个 \(k\ne0\) 都有 \(D_\alpha(k)\ne0\)，故对 \(F\in H_N\)，逆由下式给出
\[
(N_\alpha|_{H_N})^{-1}F
=\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi iD_\alpha(k)}e_k.
\]
逐项作用 \(N_\alpha\) 即得 \(F\)，且每个系数都由方程唯一确定。

对任意 \(r\in\mathbb R\)，精确逆范数为
\[
\boxed{\displaystyle
\big\|(N_\alpha|_{H_N})^{-1}\big\|_{H^r\to H^r}
=\frac{1}{2\pi\min_{0<|k|\le N}|D_\alpha(k)|}.}
\]
事实上，在 \(H^r\) 范数平方的每个求和项中，逆使该项乘以 \((2\pi|D_\alpha(k)|)^{-2}\)。取使 \(|D_\alpha(k)|\) 达到最小值的单个模式 \(F=e_k\)，即达到上述范数。

## S2　有算术界的截断误差

取 \(\widehat u(0)=0\)，并令
\[
\widehat u(k)=\frac{\widehat F(k)}{2\pi iD_\alpha(k)}
\qquad(k\ne0).
\]
光滑周期函数 \(F\) 的 Fourier 系数由反复分部积分可知按任意幂衰减。题设给出
\[
|\widehat u(k)|\le (2\pi c)^{-1}\langle k\rangle^s|\widehat F(k)|,
\]
所以 \(\widehat u(k)\) 也按任意幂衰减。其 Fourier 级数和各阶导数级数都绝对一致收敛，定义了光滑零均值函数 \(u\)。逐项求导得 \(N_\alpha u=F\)，而零均值条件和各非零模式上的方程给出唯一性。

由 S1，\(u_N\) 恰是 \(u\) 在 \(0<|k|\le N\) 上的截断。对任意实数 \(r\) 和 \(q\ge0\)，在 \(|k|>N\) 上有 \(\langle k\rangle^{-2q}\le(1+N^2)^{-q}\)，故
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&\le (2\pi c)^{-2}\sum_{|k|>N}
       \langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&\le (2\pi c)^{-2}(1+N^2)^{-q}
       \|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
开平方即得所要求的常数和截断速率。

## S3　固定频带内改变方向

由 S1，在 \(0<|k|\le N\) 上有
\[
\widehat{u_\alpha-u_\beta}(k)
=\frac{(\beta-\alpha)k_1}
       {2\pi iD_\alpha(k)D_\beta(k)}\,\widehat F(k).
\]
两个除数的绝对值均至少为 \(\delta\)，且 \(|k_1|\le N\)。将乘子的绝对值上界代入 \(H^r\) 范数，得到
\[
\boxed{\displaystyle
\|u_\alpha-u_\beta\|_{H^r}
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4　整体可逆性与全部正则性损失

**光滑零均值空间上的可逆性恰好对应于非 Liouville 无理数。** 对给定方向，允许损失的下端点可由连分数分母算出，端点是否取到还取决于这些分母在临界幂次下是否有统一上界。

### Sobolev 估计的精确判据

对 \(s\ge0\) 记
\[
\gamma_s(\alpha)=\inf_{k\in\mathbb Z^2\setminus\{0\}}
                     \langle k\rangle^s|D_\alpha(k)|.
\]
则 \(s\) 是允许损失当且仅当 \(\gamma_s(\alpha)>0\)，此时对每个 \(r\) 的最佳常数都是 \((2\pi\gamma_s(\alpha))^{-1}\)。

事实上，若题中估计对某个 \(r\) 成立，代入 \(u=e_k\) 并约去 \(\langle k\rangle^r\)，得到
\[
1\le 2\pi C_{\alpha,r,s}\langle k\rangle^s|D_\alpha(k)|
\qquad(k\ne0).
\]
反过来，若 \(\gamma_s(\alpha)>0\)，对零均值 \(u\) 的所有非零 Fourier 模式平方求和，即得
\[
\|u\|_{H^r}\le (2\pi\gamma_s(\alpha))^{-1}
                       \|N_\alpha u\|_{H^{r+s}}.
\]
两个方向也证明了常数的最优性。

### 全部允许的 \(s\)，包括端点

令 \(p_n/q_n\) 为 \(\alpha\) 的简单连分数收敛分数，取 \(q_n>0\)，定义
\[
\tau=\limsup_{n\to\infty}\frac{\log q_{n+1}}{\log q_n},
\]
其中略去开头 \(q_n=1\) 的项。由于 \(q_n\) 最终严格递增且趋于无穷，\(\tau\in[1,\infty]\)。全部允许损失构成的集合为
\[
\boxed{
\begin{cases}
\varnothing,
   &\tau=\infty,\\[2pt]
[\tau,\infty),
   &\tau<\infty,\quad \displaystyle\sup_n q_{n+1}/q_n^\tau<\infty,\\[2pt]
(\tau,\infty),
   &\tau<\infty,\quad \displaystyle\sup_n q_{n+1}/q_n^\tau=\infty.
\end{cases}}
\]

为证明此式，令 \(d(q)=\min_{p\in\mathbb Z}|q\alpha-p|\)，\(q\ge1\)。先有
\[
\gamma_s(\alpha)>0
\quad\Longleftrightarrow\quad
\inf_{q\ge1}q^s d(q)>0. \tag{1}
\]
对正向，取 \(p\) 为离 \(q\alpha\) 最近的整数，则 \(|p|\le|\alpha|q+1/2\)，故 \(\langle(q,-p)\rangle\le A_\alpha q\)。将 \(k=(q,-p)\) 代入 \(\gamma_s\) 即得。对反向，若 \(k_1\ne0\)，则 \(|D_\alpha(k)|\ge d(|k_1|)\) 且 \(\langle k\rangle\ge |k_1|\)；若 \(k_1=0\)、\(k\ne0\)，则 \(|D_\alpha(k)|=|k_2|\ge1\)。

由于 \(\alpha\) 无理，其简单连分数无限。对它的收敛分数，标准误差界和第二类最佳逼近定理给出，对充分大的 \(n\)，
\[
\frac1{q_n+q_{n+1}}<|q_n\alpha-p_n|<\frac1{q_{n+1}},
\qquad
d(q)\ge |q_n\alpha-p_n|\quad(1\le q<q_{n+1}).
\]
若 \(q^s d(q)\ge c>0\)，取 \(q=q_n\)，由误差上界得 \(q_{n+1}\le c^{-1}q_n^s\)。反过来，若 \(q_{n+1}\le Bq_n^s\)，则对 \(q_n\le q<q_{n+1}\)，
\[
d(q)>\frac1{q_n+q_{n+1}}\ge\frac1{2Bq_n^s}\ge\frac1{2Bq^s}.
\]
有限个起始分母可由调小正常数处理，因为每个 \(d(q)>0\)。因此
\[
\gamma_s(\alpha)>0
\quad\Longleftrightarrow\quad
\sup_n\frac{q_{n+1}}{q_n^s}<\infty. \tag{2}
\]
当 \(s>\tau\) 时，此比值最终至多为 \(1\)。当 \(s<\tau\) 时，取 \(s<t<\tau\)，沿一列指标有 \(q_{n+1}>q_n^t\)，比值无界。有限端点 \(s=\tau\) 直接由 (2) 判定，得到上述分类。

### 光滑解的构造与不可解数据

\(N_\alpha\) 将光滑函数映到零均值函数，因为周期函数的偏导数积分为零。在零均值空间上它总是单射，因为每个非零模式的乘子都非零。

若有某个有限的允许损失 \(s\)，则 S2 的算术假设以 \(c=\gamma_s(\alpha)>0\) 成立。S2 的 Fourier 除法便对每个光滑零均值 \(F\) 给出唯一光滑零均值解。

若没有任何有限的允许损失，则对每个整数 \(j\ge1\) 都有 \(\gamma_j(\alpha)=0\)。可依次选取模长严格递增的 \(k_j\)，使
\[
|k_j|>2^j,\qquad 0<|D_\alpha(k_j)|<\langle k_j\rangle^{-j}.
\]
这是因为每个有限频率集上的非零除数都有正的最小值。取
\[
F=\sum_{j\ge1}2\pi iD_\alpha(k_j)e_{k_j}.
\]
对固定导数阶数 \(m\)，第 \(j\) 项求导后的绝对值至多为
\((2\pi)^{m+1}\langle k_j\rangle^{m-j}\)，在 \(j\ge m+1\) 时由常数倍的 \(2^{-j}\) 控制。因此 \(F\) 光滑且零均值。若有光滑解，比较系数必得 \(\widehat u(k_j)=1\) 对所有 \(j\) 成立，这与光滑函数属于 \(L^2\)、其 Fourier 系数平方可和矛盾。

于是整体可逆当且仅当 \(\tau<\infty\)。这也给出前述 Liouville 分类。事实上，(1) 等价于存在 \(c>0\) 使所有 \(p\in\mathbb Z,\ q\ge1\) 满足
\[
|\alpha-p/q|\ge c q^{-(s+1)}.
\]
某个有限 \(s\) 有此下界，就排除了任意高次的有理逼近。若每个有限 \(s\) 的下界都失败，则每个整数 \(M\ge1\) 都有任意大的 \(q\) 使 \(0<|\alpha-p/q|<q^{-M}\)，这正是 Liouville 性质。

### 特定方向 \(\alpha_*=\sqrt2-1\)

**最小损失为 \(s=1\)，且取到。** 令 \(\alpha'=-1-\sqrt2\) 为 \(\alpha_*\) 的代数共轭。对每个 \(k\ne0\)，
\[
(\alpha_*k_1+k_2)(\alpha'k_1+k_2)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数，因为两个因子都非零。由 Cauchy–Schwarz 不等式，
\[
|D_{\alpha_*}(k)|
\ge \frac1{\sqrt{1+(\alpha')^2}\,|k|}
\ge c_*\langle k\rangle^{-1},
\qquad c_*=(1+(\alpha')^2)^{-1/2}.
\]
故 \(s=1\) 允许。上面的分类给出每个无理方向都有 \(\tau\ge1\)，故 \(s<1\) 全部排除。

题中的 **\(C^m\) 估计对每个 \(m\ge0\) 都成立**。对 \(k\ne0\)，选取满足 \(|k_j|\ge |k|/\sqrt2\) 的坐标，在该坐标分部积分 \(m+4\) 次。由 Haar 测度归一化，
\[
|\widehat F(k)|\le A_m\langle k\rangle^{-(m+4)}\|F\|_{C^{m+4}}.
\]
在解的 Fourier 级数中，除以 \(2\pi iD_{\alpha_*}(k)\) 至多带来常数倍的 \(\langle k\rangle\)，求至多 \(m\) 阶导数至多带来常数倍的 \(\langle k\rangle^m\)。于是
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le B_m\|F\|_{C^{m+4}}
       \sum_{k\ne0}\langle k\rangle^{-3}
\le C_m\|F\|_{C^{m+4}},
\]
最后的级数在二维收敛，常数与 \(F\) 无关。

## S5　邻近方向的一致估计

**不存在这样的 \(J,s,C\)。** 任取包含 \(\alpha_*\) 的开区间 \(J\)，在其中取有理数 \(p/q\)，\(q\ge1\)。令 \(\alpha_j=p/q+\sqrt2/j\)，则 \(\alpha_j\) 无理，且对充分大的 \(j\) 属于 \(J\)。固定同一个光滑零均值模式 \(u=e_{(q,-p)}\)。对任意固定的有限 \(s\)，
\[
\|u\|_{L^2}=1,\qquad
\|N_{\alpha_j}u\|_{H^s}
=2\pi\langle(q,-p)\rangle^s|q\alpha_j-p|
\longrightarrow0.
\]
因此任何有限统一常数 \(C\) 都会在这列方向上失效。

## S6　一个具体方向的不可解数据

令
\[
Q_n=10^{n!},\qquad P_n=\sum_{\ell=1}^n10^{\,n!-\ell!},
\qquad \alpha_n=P_n/Q_n.
\]
由于各阶乘指数严格递增，以从 \((n+1)!\) 开始的全部整数指数作几何级数上界，得到
\[
0<\alpha-\alpha_n
\le \frac{10}{9}10^{-(n+1)!}
<2Q_n^{-(n+1)}.
\]
若 \(\alpha=a/b\)，\(b\ge1\)，则严格正的差 \(\alpha-P_n/Q_n\) 至少为 \(1/(bQ_n)\)，与上界在充分大的 \(n\) 时矛盾。故 \(\alpha\) 无理。

现在取 \(k_n=(Q_n,-P_n)\)，\(\varepsilon_n=Q_n\alpha-P_n\)，并定义单个数据
\[
\boxed{\displaystyle
F(y)=\sum_{n=1}^{\infty}2\pi i\,\varepsilon_n
               e^{2\pi i(Q_n y_1-P_n y_2)}.}
\]
上面的尾项界给出 \(0<\varepsilon_n<2Q_n^{-n}\)，且由 \(0<P_n<\alpha Q_n\) 有 \(|k_n|\le\sqrt{1+\alpha^2}\,Q_n\)。故对每个固定阶数 \(m\)，第 \(n\) 项的任一 \(m\) 阶导数的绝对值至多为 \(C_m Q_n^{m-n}\)。在 \(n\ge m+1\) 时，\(Q_n^{m-n}\le Q_n^{-1}\le10^{-n}\)。这证明各阶导数级数均绝对一致收敛。所有模式都非零，故 \(F\in C^\infty_0(\mathbb T^2)\)。

各 \(k_n\) 互异，且 \(D_\alpha(k_n)=\varepsilon_n\)。若 \(N_\alpha u=F\) 有光滑解，则对每个 \(n\) 都必须有
\[
2\pi i\varepsilon_n\widehat u(k_n)=2\pi i\varepsilon_n,
\qquad \widehat u(k_n)=1.
\]
这违反 Fourier 系数的平方可和性，故该 \(F\) 没有光滑零均值解。