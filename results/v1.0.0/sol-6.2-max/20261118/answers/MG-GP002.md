## S1 有限频带上的逆

记 \(e_k(y)=e^{2\pi i k\cdot y}\) 和 \(d_\alpha(k)=\alpha k_1+k_2\)。周期积分分部给出
\[
\widehat{N_\alpha u}(k)=2\pi i\,d_\alpha(k)\widehat u(k).
\]
当 \(k\ne0\) 时，若 \(k_1=0\)，则 \(d_\alpha(k)=k_2\ne0\)。若 \(k_1\ne0\)，则由 \(\alpha\) 无理可知 \(d_\alpha(k)\ne0\)。因此 \(N_\alpha\) 在 \(H_N\) 上的逆为
\[
T_{\alpha,N}F=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]
逐频率相乘可验证两个复合都是 \(H_N\) 上的恒等算子。

对任意 \(r\in\mathbb R\)，以 \(H^r\) 范数度量 \(H_N\) 时，
\[
\boxed{\displaystyle
\|T_{\alpha,N}\|_{H^r\to H^r}
=\frac{1}{2\pi\min_{0<|k|\le N}|d_\alpha(k)|}.}
\]
上界来自对每个加权傅里叶系数应用乘子的绝对值上界。频带有限且非空，取使 \(|d_\alpha(k)|\) 最小的单频 \(F=e_k\) 即得等号。

## S2 有算术界的截断误差

令 \(\widehat u(0)=0\)，并对 \(k\ne0\) 定义
\[
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}.
\]
假设给出
\[
|\widehat u(k)|\le (2\pi c)^{-1}\langle k\rangle^s|\widehat F(k)|.
\]
光滑 \(F\) 的系数快速衰减，因为对任意整数 \(M\ge0\)，周期积分分部给出
\[
(1+4\pi^2|k|^2)^M|\widehat F(k)|
\le \|(1-\Delta)^M F\|_{L^1}.
\]
故 \(\widehat u(k)\) 也快速衰减。二维格点和 \(\sum_k\langle k\rangle^{-a}\) 在 \(a>2\) 时收敛，例如按二进环带计数可得。因此 \(u\) 的傅里叶级数及其各阶导数级数都绝对一致收敛，定义了光滑零均值函数。逐项求导给出 \(N_\alpha u=F\)，这里用到 \(e_k\) 是归一化环面 \(L^2\) 的完备正交系。零均值解的唯一性由非零频率上的乘子均非零得到。

由 S1，\(u_N\) 正是 \(u\) 在 \(0<|k|\le N\) 上的截断。对 \(|k|>N\) 和 \(q\ge0\)，有 \(\langle k\rangle^{-2q}\le(1+N^2)^{-q}\)，故
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&\le (2\pi c)^{-2}
\sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat F(k)|^2\\
&\le (2\pi c)^{-2}(1+N^2)^{-q}\|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
开平方即得所求估计，对所有实数 \(r\) 均成立。

## S3 固定频带内改变方向

由 S1，在 \(0<|k|\le N\) 上，
\[
\widehat{u_\alpha-u_\beta}(k)
=\frac{(\beta-\alpha)k_1}{2\pi i\,d_\alpha(k)d_\beta(k)}\,\widehat F(k).
\]
两个分母因子的绝对值都至少为 \(\delta\)，且 \(|k_1|\le N\)。乘以 \(H^r\) 权重后平方求和，得到
\[
\boxed{\displaystyle
\|u_\alpha-u_\beta\|_{H^r}
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4 整体可逆性与全部允许损失

对 \(s\ge0\)，定义
\[
A_s(\alpha)=\inf_{k\in\mathbb Z^2\setminus\{0\}}
\langle k\rangle^s|d_\alpha(k)|.
\]
题设的 Sobolev 估计成立当且仅当 \(A_s(\alpha)>0\)。必要性只需对任一固定 \(r\) 代入 \(u=e_k\)，约去 \(\langle k\rangle^r\) 后得到
\[
1\le 2\pi C_{\alpha,r,s}\langle k\rangle^s|d_\alpha(k)|
\qquad(k\ne0).
\]
反过来，若 \(A_s(\alpha)>0\)，由乘子公式逐频率平方求和即得估计。单频测试同时表明，对每个 \(r\)，最优常数都是 \((2\pi A_s(\alpha))^{-1}\)。

算子 \(N_\alpha:C^\infty_0\to C^\infty_0\) 总是单射，因为零均值消去了零频率，其余乘子均非零。若某个 \(s\) 满足 \(A_s(\alpha)>0\)，则 S2 以 \(c=A_s(\alpha)\) 适用，给出每个光滑零均值 \(F\) 的唯一光滑零均值解。若所有 \(A_s(\alpha)=0\)，则对每个整数 \(j\ge1\) 可选互异频率 \(k_j\ne0\)，使
\[
\langle k_j\rangle\ge 2^j,
\qquad
|d_\alpha(k_j)|<\langle k_j\rangle^{-j}.
\]
这是因为 \(A_j(\alpha)=0\)，且去掉有限多个正项后下确界仍为零。令
\[
F=\sum_{j\ge1}2\pi i\,d_\alpha(k_j)e_{k_j}.
\]
每个总阶为 \(m\) 的导数级数，其第 \(j\) 项一致范数至多为 \((2\pi)^{m+1}\langle k_j\rangle^{m-j}\)，在 \(j\ge m+1\) 时由 \((2\pi)^{m+1}2^{-j}\) 控制。因此 \(F\) 光滑且零均值。若有光滑解，乘子公式将强制 \(\widehat u(k_j)=1\) 对所有 \(j\) 成立，与光滑函数的系数衰减矛盾。这证明了可逆性恰好等价于存在有限的允许损失。

**连分数分类。** 令 \(p_n/q_n\) 是 \(\alpha\) 的简单连分数收敛分数，并定义
\[
\tau=\limsup_{n\to\infty}\frac{\log q_{n+1}}{\log q_n}\in[1,\infty].
\]
全部允许的 \(s\) 构成集合
\[
\boxed{
\begin{cases}
\varnothing,&\tau=\infty,\\[2pt]
[\tau,\infty),&
\tau<\infty\ \text{且}\ \displaystyle\sup_{n\ge1}\frac{q_{n+1}}{q_n^\tau}<\infty,\\[6pt]
(\tau,\infty),&
\tau<\infty\ \text{且}\ \displaystyle\sup_{n\ge1}\frac{q_{n+1}}{q_n^\tau}=\infty.
\end{cases}}
\]

为证明分类，记 \(\rho(q)=\min_{p\in\mathbb Z}|q\alpha-p|\)，其中 \(q\ge1\) 为整数。若 \(k_1\ne0\)，取 \(q=|k_1|\)，则 \(|d_\alpha(k)|\ge\rho(q)\) 且 \(\langle k\rangle\ge q\)。若 \(k_1=0\) 且 \(k\ne0\)，则 \(|d_\alpha(k)|\ge1\)。反向对每个 \(q\) 取距离 \(q\alpha\) 最近的整数 \(p\)，由 \(|p|\le|\alpha|q+1/2\) 可知 \(\langle(q,-p)\rangle\le K_\alpha q\)，其中 \(K_\alpha\) 与 \(q\) 无关。故
\[
A_s(\alpha)>0
\quad\Longleftrightarrow\quad
\inf_{q\ge1}q^s\rho(q)>0.
\]

由于 \(\alpha\) 无理，其简单连分数无限。设部分商为 \(a_n\)，则 \(q_0=1\)，\(q_{n+1}=a_{n+1}q_n+q_{n-1}\)，分母从 \(n=1\) 起严格递增。收敛分数的递推给出相邻整数向量 \((p_n,q_n),(p_{n+1},q_{n+1})\) 的行列式绝对值为 \(1\)。将完全商 \(x_{n+1}=[a_{n+1};a_{n+2},\ldots]\) 代回连分数，利用 \(a_{n+1}<x_{n+1}<a_{n+1}+1\)，得到
\[
q_n\alpha-p_n=\frac{(-1)^n}{q_nx_{n+1}+q_{n-1}},
\qquad
\frac1{q_{n+1}+q_n}<|q_n\alpha-p_n|<\frac1{q_{n+1}}.
\]
对 \(0<q<q_{n+1}\)，把任意 \((p,q)\) 写成上述相邻向量的整数线性组合，系数记为 \(A,B\)。若 \(B=0\)，则 \(|q\alpha-p|=|A|\,|q_n\alpha-p_n|\ge |q_n\alpha-p_n|\)。若 \(B\ne0\)，分母范围迫使 \(A,B\) 都非零且异号。相邻收敛分数的误差也异号，所以相乘后的两个误差项同号，仍有 \(|q\alpha-p|\ge|q_n\alpha-p_n|\)。

因此当 \(q_n\le q<q_{n+1}\) 时，
\[
q^s\rho(q)\ge \frac{q_n^s}{2q_{n+1}}.
\]
另一方面，\(\rho(q_n)\le |q_n\alpha-p_n|<1/q_{n+1}\)。有限个 \(q<q_1\) 的 \(\rho(q)\) 均为正，故
\[
\inf_{q\ge1}q^s\rho(q)>0
\quad\Longleftrightarrow\quad
\sup_{n\ge1}\frac{q_{n+1}}{q_n^s}<\infty.
\]
若 \(s>\tau\)，取 \(\tau<s'<s\)，则充分大的 \(n\) 满足 \(q_{n+1}\le q_n^{s'}\)，所以上确界有限。若 \(s<\tau\)，取 \(s<s'<\tau\)，则无穷多个 \(n\) 满足 \(q_{n+1}>q_n^{s'}\)，相应比值无界。有限端点 \(s=\tau\) 由上确界条件判定。

所以 \(N_\alpha\) 可逆恰好当 \(\tau<\infty\)，即 \(\alpha\) 为**非 Liouville 无理数**。具体而言，若 \(\mu(\alpha)\) 是使 \(|\alpha-p/q|<q^{-\nu}\) 对任意大分母 \(q\) 成立的指数 \(\nu\) 的上确界，则 \(\mu(\alpha)=1+\tau\)。当 \(\nu<1+\tau\) 时，沿无穷多个满足 \(q_{n+1}>q_n^{\nu-1}\) 的收敛分数，上述误差上界给出所需逼近。当 \(\nu>1+\tau\) 时，取 \(\tau<s<\nu-1\)，由 \(\inf_q q^s\rho(q)>0\) 得到 \(|\alpha-p/q|\ge c q^{-s-1}>q^{-\nu}\) 对充分大的 \(q\) 成立。这也说明临界损失是 \(\mu(\alpha)-1\)，其取到与否由上面的端点条件决定。

**方向 \(\alpha_*=\sqrt2-1\)。** 对 \(k\ne0\)，有
\[
d_{\alpha_*}(k)\bigl(k_2-(1+\sqrt2)k_1\bigr)
=(k_2-k_1)^2-2k_1^2\in\mathbb Z\setminus\{0\}.
\]
右边非零由 \(\sqrt2\) 无理得到。第二个因子的绝对值至多为 \(D|k|\)，其中 \(D=\sqrt{1+(1+\sqrt2)^2}\)。故 \(|d_{\alpha_*}(k)|\ge D^{-1}\langle k\rangle^{-1}\)。于是 \(s=1\) 允许，而分类中的 \(\tau\ge1\) 排除了所有 \(s<1\)。允许损失恰为 \([1,\infty)\)，最小值 \(1\) **取到**。

所问的 \(C^m\) 估计也成立。令 \(t=m+4\)。对每个 \(k\ne0\)，选择坐标 \(j\) 使 \(|k_j|\ge |k|/\sqrt2\)，沿该坐标积分分部 \(t\) 次，得到
\[
|\widehat F(k)|\le
\left(\frac{\sqrt2}{2\pi}\right)^t |k|^{-t}\|F\|_{C^t}.
\]
由刚证明的 \(|d_{\alpha_*}(k)|\ge(D|k|)^{-1}\)，逆乘子的绝对值至多为 \(D|k|/(2\pi)\)。对解求任意总阶不超过 \(m\) 的导数，逐项估计后得到
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le
\frac{D(2\pi)^m}{2\pi}
\left(\frac{\sqrt2}{2\pi}\right)^{m+4}
\left(\sum_{k\ne0}|k|^{-3}\right)\|F\|_{C^{m+4}}.
\]
二维格点和收敛，故右侧给出了与 \(F\) 无关的有限常数。

## S5 邻近方向的一致估计

不存在这样的 \(J,s,C\)。任取包含 \(\alpha_*\) 的开区间 \(J\)，选有理数 \(p/q\in J\)，其中 \(q\ge1\)。令
\[
\alpha_j=\frac pq+\frac{\alpha_*}{j},\qquad
k=(q,-p),\qquad u=e_k.
\]
每个 \(\alpha_j\) 都无理，且充分大的 \(j\) 满足 \(\alpha_j\in J\)。固定的 \(u\) 光滑、零均值且 \(\|u\|_{L^2}=1\)。对任意固定有限 \(s\ge0\)，
\[
\|N_{\alpha_j}u\|_{H^s}
=2\pi q\,|\alpha_j-p/q|\,\langle k\rangle^s\longrightarrow0.
\]
因此任何固定有限 \(C\) 都无法使所要求的不等式对这些方向成立。

## S6 一个具体方向的不可解数据

令
\[
q_n=10^{n!},\qquad
p_n=\sum_{j=1}^{n}10^{n!-j!},\qquad
d_n=q_n\alpha-p_n.
\]
阶乘指数严格递增，故 \(0<\alpha\le\sum_{\ell\ge1}10^{-\ell}=1/9\)，从而 \(0<p_n<q_n\)。尾项满足
\[
0<d_n
=q_n\sum_{j>n}10^{-j!}
\le \frac{10}{9}\,q_n\,10^{-(n+1)!}
=\frac{10}{9}\,q_n^{-n}.
\]
若 \(\alpha=a/b\) 且 \(b\ge1\)，则 \(bd_n=aq_n-bp_n\) 是正整数，但 \(bd_n\to0\)，矛盾。因此 \(\alpha\) 无理。

取互异频率 \(k_n=(q_n,-p_n)\)，构造同一个数据
\[
\boxed{\displaystyle
F(y)=\sum_{n=1}^{\infty} 2\pi i\,d_n\,e^{2\pi i(q_n y_1-p_n y_2)}.}
\]
总阶为 \(m\) 的任意导数，其第 \(n\) 项的一致范数至多为 \(\frac{10}{9}(2\pi)^{m+1}q_n^{m-n}\)。当 \(n\ge m+1\) 时，\(q_n^{m-n}\le q_n^{-1}\le10^{-n}\)。所以所有导数级数都绝对一致收敛，且逐项积分给出 \(F\) 的均值为零。

若 \(N_\alpha u=F\) 有光滑零均值解，则在每个 \(k_n\) 上，由 \(d_\alpha(k_n)=d_n>0\) 得
\[
2\pi i\,d_n\,\widehat u(k_n)=2\pi i\,d_n,
\qquad \widehat u(k_n)=1.
\]
由于 \(|k_n|\to\infty\)，这与光滑函数的傅里叶系数衰减矛盾。因此该 \(F\) 没有光滑零均值解。