记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad d_\alpha(k)=\alpha k_1+k_2.
\]
对光滑函数分部积分可得
\[
\widehat{N_\alpha u}(k)=2\pi i\,d_\alpha(k)\widehat u(k).
\]
当 \(\alpha\) 无理且 \(k\ne0\) 时，\(d_\alpha(k)\ne0\)。

下文使用如下 Fourier 正则性事实：光滑函数的 Fourier 系数快速下降；反之，若一个系数列属于每个 \(H^t\)，则它定义光滑函数。后一断言可由 Cauchy–Schwarz 和二维中
\(\sum_k\langle k\rangle^{-4}<\infty\) 得到：每一阶导数的 Fourier 级数都绝对一致收敛。

## S1 有限频带上的逆

对 \(F\in H_N\)，定义
\[
N_\alpha^{-1}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
各分母非零，逐频率计算即得 \(N_\alpha N_\alpha^{-1}F=F\)。同理，\(N_\alpha\) 在 \(H_N\) 上无核，因此这就是其逆。

对每个 \(r\in\mathbb R\)，由于该逆是对角 Fourier 乘子，其精确范数为
\[
\boxed{\displaystyle
\|N_\alpha^{-1}\|_{H_N^r\to H_N^r}
=\frac1{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.}
\]
上界由逐项估计得到；取使最小值达到的单个 Fourier 模式，即达到该上界。

## S2 有算术界的截断误差

令 \(\widehat u(0)=0\)，并对 \(k\ne0\) 定义
\[
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}.
\]
由假设，对任意 \(t\in\mathbb R\)，
\[
\sum_k\langle k\rangle^{2t}|\widehat u(k)|^2
\le \frac1{(2\pi c)^2}
\sum_k\langle k\rangle^{2(t+s)}|\widehat F(k)|^2<\infty.
\]
因此 \(u\) 光滑且零均值，逐 Fourier 系数验证 \(N_\alpha u=F\)。无理性也保证此零均值解唯一。

S1 的 \(u_N\) 正是 \(u\) 在 \(0<|k|\le N\) 上的 Fourier 截断。因为 \(q\ge0\)，当 \(|k|>N\) 时，
\(\langle k\rangle^{-q}\le(1+N^2)^{-q/2}\)。于是
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&\le \frac1{(2\pi c)^2}
 \sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}
 \|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
取平方根便得到所求估计：
\[
\boxed{\displaystyle
\|u-u_N\|_{H^r}
\le \frac{(1+N^2)^{-q/2}}{2\pi c}
\|F\|_{H^{r+s+q}}.}
\]

## S3 固定频带内改变方向

对 \(0<|k|\le N\)，两解的系数之差为
\[
\widehat u_\alpha(k)-\widehat u_\beta(k)
=\frac{\widehat F(k)}{2\pi i}
 \left(\frac1{d_\alpha(k)}-\frac1{d_\beta(k)}\right).
\]
由小除数假设，
\[
\left|\frac1{d_\alpha(k)}-\frac1{d_\beta(k)}\right|
=\frac{|(\alpha-\beta)k_1|}
 {|d_\alpha(k)d_\beta(k)|}
\le\frac{|\alpha-\beta|N}{\delta^2}.
\]
逐项乘上 Sobolev 权重并求和，得到
\[
\boxed{\displaystyle
\|u_\alpha-u_\beta\|_{H^r}
\le\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4 整体对象与全部恢复目标

### 定理与分类

对无理 \(\alpha\)，令
\[
D_s(\alpha)=\inf_{k\in\mathbb Z^2\setminus\{0\}}
 |d_\alpha(k)|\langle k\rangle^s
 \qquad(s\ge0),
\]
并令
\[
\rho_\alpha(q)=\min_{p\in\mathbb Z}|q\alpha-p|,\qquad
\lambda_\alpha=
\limsup_{q\to\infty}\frac{\log(1/\rho_\alpha(q))}{\log q}.
\]
这里 \(\rho_\alpha(q)>0\)，且 \(\lambda_\alpha\in[1,\infty]\)。

结论如下。

1. \(N_\alpha:C^\infty_0\to C^\infty_0\) 总是单射。它满射，当且仅当存在有限 \(s\ge0\) 使 \(D_s(\alpha)>0\)，等价地，当且仅当 \(\lambda_\alpha<\infty\)。这也就是无理数 \(\alpha\) 非 Liouville。
2. 对给定 \(s\ge0\)，题中的 Sobolev 估计对每个 \(r\) 成立，当且仅当 \(D_s(\alpha)>0\)。成立时最优常数与 \(r\) 无关，精确为
   \[
   \boxed{\displaystyle C_{\alpha,r,s}^{\rm opt}
   =\frac1{2\pi D_s(\alpha)}.}
   \]
3. 若 \(\lambda_\alpha=\infty\)，没有允许的有限损失 \(s\)。若 \(\lambda_\alpha<\infty\)，全部允许损失恰为
   \[
   \boxed{\displaystyle
   (\lambda_\alpha,\infty)\ \cup\
   \begin{cases}
   \{\lambda_\alpha\},&
   \displaystyle\inf_{q\ge1}q^{\lambda_\alpha}\rho_\alpha(q)>0,\\[2mm]
   \varnothing,&
   \displaystyle\inf_{q\ge1}q^{\lambda_\alpha}\rho_\alpha(q)=0.
   \end{cases}}
   \]
   所以有限临界指数本身是否允许，须由端点条件判定，不能仅由其数值判定。

### 分类的证明

首先，对固定 \(s\ge0\) 及 \(u\in C^\infty_0\)，逐频率估计给出
\[
\|u\|_{H^r}\le \frac1{2\pi D_s(\alpha)}
 \|N_\alpha u\|_{H^{r+s}}
\]
，只要 \(D_s(\alpha)>0\)。反过来，将任何此类估计应用于 \(u=e_k\)，得到
\[
C_{\alpha,r,s}\ge
\frac1{2\pi|d_\alpha(k)|\langle k\rangle^s}.
\]
对 \(k\ne0\) 取上确界，既证明必要性，也证明上述最优常数公式。

接着说明 \(D_s\) 与一维逼近的关系。令
\[
B_\alpha=\sqrt{\,2+(|\alpha|+\tfrac12)^2\,}.
\]
若 \(p\) 是离 \(q\alpha\) 最近的整数，则
\(|p|\le(|\alpha|+\tfrac12)q\)，所以
\(\langle(q,-p)\rangle\le B_\alpha q\)。反过来，对任意
\(k_1\ne0\)，有
\(|d_\alpha(k)|\ge\rho_\alpha(|k_1|)\)；而 \(k_1=0\) 时
\(|d_\alpha(k)|=|k_2|\ge1\)。因此，对每个 \(s\ge0\)，
\[
\boxed{\quad
D_s(\alpha)>0
\quad\Longleftrightarrow\quad
\inf_{q\ge1}q^s\rho_\alpha(q)>0.
\quad}
\]

鸽巢原理表明，对每个 \(Q\ge2\)，存在 \(1\le q\le Q\) 使
\(\rho_\alpha(q)<1/Q\le1/q\)。由于 \(\alpha\) 无理，任何有限集合内的 \(\rho_\alpha(q)\) 均有正下界，故这些 \(q\) 可趋于无穷。这证明 \(\lambda_\alpha\ge1\)。

若 \(s>\lambda_\alpha\)，按上极限定义，对充分大的 \(q\) 有
\(\rho_\alpha(q)\ge q^{-(s-\varepsilon)}\)，其中某个 \(\varepsilon>0\) 固定；再考虑有限个小 \(q\)，便有
\(\inf_q q^s\rho_\alpha(q)>0\)。若 \(s<\lambda_\alpha\)，取
\(s<t<\lambda_\alpha\)，则无穷多个 \(q\) 满足
\(\rho_\alpha(q)<q^{-t}\)，故 \(\inf_q q^s\rho_\alpha(q)=0\)。
端点 \(s=\lambda_\alpha<\infty\) 则恰由上述下确界是否为正决定。这证明了全部损失的分类；\(\lambda_\alpha=\infty\) 时同理不存在有限损失。

如果 \(D_s(\alpha)>0\) 对某个有限 \(s\) 成立，则 S2 的条件以 \(c=D_s(\alpha)>0\) 成立，故每个光滑零均值 \(F\) 都有光滑零均值解。单射性则由非零频率上的
\(d_\alpha(k)\ne0\) 得到。

反之，假设不存在有限 \(s\) 使 \(D_s(\alpha)>0\)。因为每个单独的小除数非零，可依次选取互异且 \(|k_j|\to\infty\) 的非零整数频率，使
\[
|d_\alpha(k_j)|\langle k_j\rangle^j<2^{-j}.
\]
定义**同一个数据**
\[
F(y)=\sum_{j=1}^\infty 2\pi i\,d_\alpha(k_j)e_{k_j}(y).
\]
对任意固定阶导数，充分大的 \(j\) 对应的项由常数乘 \(2^{-j}\) 控制；因此所有导数级数一致收敛，\(F\in C^\infty_0\)。若 \(N_\alpha u=F\)，则必有
\(\widehat u(k_j)=1\) 对所有 \(j\) 成立。这违反 \(L^2\) Fourier 系数的 Bessel 不等式，故甚至不存在 \(L^2\) 解。由此满射性也已完全刻画。

**端点确实可能不取到。** 例如取无限简单连分数
\(\theta=[0;1,2,3,\ldots]\)，其收敛分数分母满足
\(q_{n+1}=(n+1)q_n+q_{n-1}\) 和 \(q_n\ge n!\)。无限正整数部分商的简单连分数收敛到无理数；对其收敛分数，标准最佳逼近定理适用，并给出对充分大的 \(n\)
\[
\frac1{q_{n+1}+q_n}<\rho_\theta(q_n)<\frac1{q_{n+1}},
\qquad
\rho_\theta(q)\ge\rho_\theta(q_n)
\quad(q_n\le q<q_{n+1}).
\]
于是对每个 \(\varepsilon>0\)，充分大的 \(q\) 满足
\(\rho_\theta(q)\ge q^{-1-\varepsilon}\)，所以 \(\lambda_\theta=1\)；但
\(q_n\rho_\theta(q_n)<q_n/q_{n+1}\le1/(n+1)\to0\)。
故该方向允许所有 \(s>1\)，但不允许 \(s=1\)。

### 二次无理方向 \(\alpha_*=\sqrt2-1\)

其共轭数为 \(\alpha'=-1-\sqrt2\)。对非零 \(k\in\mathbb Z^2\)，
\[
(\alpha_*k_1+k_2)(\alpha'k_1+k_2)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数，因此绝对值至少为 \(1\)。令
\[
A=\sqrt{1+(\alpha')^2},\qquad c_*=A^{-1}.
\]
由 Cauchy–Schwarz，
\[
|\alpha_*k_1+k_2|
\ge \frac1{A|k|}
\ge c_*\langle k\rangle^{-1}.
\]
所以 \(s=1\) 允许，进而所有 \(s\ge1\) 都允许；上面的 \(\lambda_\alpha\ge1\) 又排除一切 \(s<1\)。因此
\[
\boxed{\text{最小损失为 }s=1\text{，且该端点取到；允许集为 }[1,\infty).}
\]

所问的 \(C^m\) 估计也成立。事实上，令 \(n=m+4\)。对 \(k\ne0\)，选坐标 \(j\) 使
\(|k_j|\ge |k|/\sqrt2\ge\langle k\rangle/2\)，沿该坐标分部积分 \(n\) 次得
\[
|\widehat F(k)|
\le \pi^{-n}\langle k\rangle^{-n}\|F\|_{C^n}.
\]
结合上述小除数界，对 \(a+b\le m\)，解的导数级数满足
\[
\begin{aligned}
\sup_y|\partial_1^a\partial_2^b u(y)|
&\le
\frac{(2\pi)^m}{2\pi c_*}
 \sum_{k\ne0}\langle k\rangle^{m+1}|\widehat F(k)|\\
&\le
\frac{(2\pi)^{m-1}}{c_*\pi^{m+4}}
\left(\sum_{k\ne0}\langle k\rangle^{-3}\right)
\|F\|_{C^{m+4}}.
\end{aligned}
\]
二维中最后的级数收敛，故对每个 \(m\) 都存在所求的有限常数 \(C_m\)。

## S5 邻近方向的一致估计

**不存在**这样的 \(J,s,C\)。

事实上，任取包含 \(\alpha_*\) 的开区间 \(J\)，选有理数
\(p/q\in J\)，其中 \(q\ge1\)，再选 \(J\) 中无理数列
\(\alpha_j\to p/q\)。对固定频率 \(k=(q,-p)\)，取 \(u=e_k\)。则
\[
\|u\|_{L^2}=1,\qquad
\|N_{\alpha_j}u\|_{H^s}
=2\pi q|\alpha_j-p/q|\langle k\rangle^s\longrightarrow0.
\]
这与任何有限的统一常数 \(C\) 矛盾。此论证对任何有限 \(s\) 均成立。

## S6 一个具体方向的不可解数据

令
\[
Q_n=10^{n!},\qquad
P_n=Q_n\sum_{j=1}^n10^{-j!}\in\mathbb Z,\qquad
R_n=\alpha-\frac{P_n}{Q_n}.
\]
尾项严格为正，且
\[
0<R_n
\le \sum_{\ell=(n+1)!}^\infty10^{-\ell}
<2\cdot10^{-(n+1)!}
=2Q_n^{-(n+1)}.
\]

若 \(\alpha=a/b\) 为有理数，其中 \(b>0\)，则正有理数
\(\alpha-P_n/Q_n\) 至少为 \(1/(bQ_n)\)。但当 \(n\) 足够大时，
\(2Q_n^{-(n+1)}<1/(bQ_n)\)，矛盾。因此 \(\alpha\) 无理。

现在取互异频率
\[
k_n=(Q_n,-P_n)
\]
并构造单个数据
\[
\boxed{\displaystyle
F(y)=\sum_{n=1}^{\infty}Q_n^{-n}
 e^{2\pi i(Q_ny_1-P_ny_2)}.}
\]
由于 \(0<P_n<Q_n\)，任意 \(m\) 阶导数的第 \(n\) 项由
\((2\pi)^mQ_n^{m-n}\) 控制；对 \(n\ge m+2\)，它不超过常数乘
\(Q_n^{-2}\le10^{-2n}\)。因此所有导数级数一致收敛，
\(F\in C^\infty_0(\mathbb T^2)\)，且
\(\widehat F(k_n)=Q_n^{-n}\)。

另一方面，
\[
0<d_\alpha(k_n)=Q_n\alpha-P_n=Q_nR_n<2Q_n^{-n}.
\]
若存在光滑解 \(N_\alpha u=F\)，逐频率比较便有
\[
|\widehat u(k_n)|
=\frac{Q_n^{-n}}{2\pi\,d_\alpha(k_n)}
>\frac1{4\pi}\qquad\text{对所有 }n.
\]
这违反 \(u\in L^2\) 的 Bessel 不等式。因此这个固定的光滑零均值 \(F\) 没有光滑零均值解。