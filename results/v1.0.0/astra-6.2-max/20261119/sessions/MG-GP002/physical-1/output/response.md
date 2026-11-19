## S1 有限频带上的逆

记 \(e_k(y)=e^{2\pi i k\cdot y}\)，\(d_\alpha(k)=\alpha k_1+k_2\)，以及 \(K_N=\{k\in\mathbb Z^2:0<|k|\le N\}\)。在归一化环面上，\(e_k\) 构成 Fourier 正交归一基，且
\[
N_\alpha e_k=2\pi i\,d_\alpha(k)e_k.
\]
由 \(\alpha\) 无理，\(d_\alpha(k)\) 仅在 \(k=0\) 时为零。因此 \(N_\alpha\) 在 \(H_N\) 上的逆为
\[
(N_\alpha|_{H_N})^{-1}F
=\sum_{k\in K_N}\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}e_k.
\]

对每个 \(r\in\mathbb R\)，精确范数为
\[
\boxed{\displaystyle
\big\|(N_\alpha|_{H_N})^{-1}\big\|_{H^r\to H^r}
=\frac{1}{2\pi\min_{k\in K_N}|d_\alpha(k)|}.}
\]
在 \(H^r\) 范数的平方和中，每一项至多乘以右端的平方，故得到上界。因 \(N\ge1\)，\(K_N\) 有限且非空。取达到最小值的 \(k\)，单个模式 \(F=e_k\) 即取得等号。

## S2 有算术界的截断误差

定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}
\quad(k\ne0). \tag{1}
\]
对任意光滑 \(g\) 和整数 \(\ell\ge0\)，有
\[
|\widehat g(k)|\le A_\ell\|g\|_{C^\ell}\langle k\rangle^{-\ell}. \tag{2}
\]
事实上，对 \(k\ne0\) 选取满足 \(|k_j|\ge |k|/\sqrt2\) 的坐标，沿该坐标分部积分 \(\ell\) 次即可。反过来，若一个系数列对每个 \(\ell\) 都是 \(O(\langle k\rangle^{-\ell})\)，则其 Fourier 级数定义光滑函数。对任意 \(m\) 阶导数取 \(\ell=m+3\)，导数级数即由 \(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-3}<\infty\) 绝对一致控制。

题设给出 \(|d_\alpha(k)|^{-1}\le c^{-1}\langle k\rangle^s\)，故 (1) 中的系数仍快速衰减，定义了光滑零均值函数 \(u\)。逐项作用 \(N_\alpha\) 得 \(N_\alpha u=F\)，而每个非零模式都由 (1) 唯一确定。

由 S1，\(u_N\) 正是 \(u\) 在 \(K_N\) 上的截断。对任意 \(r\in\mathbb R\)、\(q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}
  \frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
       {4\pi^2|d_\alpha(k)|^2}\\
&\le (2\pi c)^{-2}\sum_{|k|>N}
  \langle k\rangle^{-2q}\langle k\rangle^{2(r+s+q)}
  |\widehat F(k)|^2\\
&\le (2\pi c)^{-2}(1+N^2)^{-q}\|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
最后一步使用了 \(|k|>N\) 和 \(q\ge0\)。开平方即得所要求的估计。

## S3 固定频带内改变方向

对 \(k\in K_N\)，由 S1 的逆公式，
\[
\big|\widehat{u_\alpha-u_\beta}(k)\big|
=\frac{|\alpha-\beta|\,|k_1|}
       {2\pi|d_\alpha(k)d_\beta(k)|}\,|\widehat F(k)|
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat F(k)|.
\]
频带外两解的系数都为零。乘以 \(\langle k\rangle^r\) 后取 \(\ell^2\) 范数，得到
\[
\boxed{\displaystyle
\|u_\alpha-u_\beta\|_{H^r}
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.}
\]

## S4 整体可逆性与全部正则性损失

**每个光滑零均值 \(F\) 都有唯一光滑零均值解，当且仅当 \(\alpha\) 是非 Liouville 无理数。** 若 \(p_j/q_j\) 为 \(\alpha\) 的简单连分数收敛分数，则全部允许损失组成的集合为
\[
\boxed{\displaystyle
\mathcal S(\alpha)
=\left\{s\ge0:\ \sup_{j\ge0}\frac{q_{j+1}}{q_j^s}<\infty\right\}.} \tag{3}
\]

### Fourier 判据与可逆性

令
\[
D_s(\alpha)=\inf_{k\ne0}\langle k\rangle^s|d_\alpha(k)|.
\]
若题中的 Sobolev 估计对某个 \(r\) 成立，代入 \(u=e_k\) 并约去 \(\langle k\rangle^r\)，得到
\[
1\le 2\pi C_{\alpha,r,s}\langle k\rangle^s|d_\alpha(k)|
\qquad(k\ne0).
\]
故 \(D_s(\alpha)>0\)。反之，若 \(D_s(\alpha)>0\)，逐模式估计并求和即得
\[
\|u\|_{H^r}\le \frac{1}{2\pi D_s(\alpha)}
                  \|N_\alpha u\|_{H^{r+s}}
\qquad(r\in\mathbb R).
\]
单模式检验也说明，此处的常数对每个 \(r\) 都是最优的。

周期性保证 \(N_\alpha u\) 的均值为零。无理性保证零均值解的唯一性，因为所有非零模式都必须满足 (1)。只要某个有限 \(s\) 满足 \(D_s(\alpha)>0\)，S2 就以 \(c=D_s(\alpha)\) 对每个光滑零均值右端构造出解。

若所有有限 \(s\) 都有 \(D_s(\alpha)=0\)，则可选取 \(|k_j|\) 严格递增的频率，使
\[
0<|d_\alpha(k_j)|\le\langle k_j\rangle^{-j}\qquad(j\ge1).
\]
这是因为 \(D_j(\alpha)=0\)，而任何有限个非零频率上 \(\langle k\rangle^j|d_\alpha(k)|\) 的最小值都为正。定义一个 \(F\)，令
\[
\widehat F(k_j)=2\pi i\,d_\alpha(k_j),\qquad
\widehat F(k)=0\quad\bigl(k\notin\{k_j:j\ge1\}\bigr).
\]
对每个固定的 \(\ell\)，从 \(j\ge\ell\) 起有 \(\langle k_j\rangle^\ell|\widehat F(k_j)|\le2\pi\)。故该系数列快速衰减，\(F\) 光滑且零均值。任何光滑解却都须满足 \(\widehat u(k_j)=1\) 对所有 \(j\) 成立，这与 \(u\in L^2\) 的 Fourier 系数平方可和矛盾。这就证明了整体可逆性等价于存在有限 \(s\) 使 \(D_s(\alpha)>0\)。

### 算术分类与临界端点

记 \(\|x\|_{\mathbb R/\mathbb Z}=\min_{P\in\mathbb Z}|x-P|\)。则
\[
D_s(\alpha)>0
\quad\Longleftrightarrow\quad
\inf_{Q\in\mathbb N,\ Q\ge1} Q^s\|Q\alpha\|_{\mathbb R/\mathbb Z}>0. \tag{4}
\]
正向取 \(P\) 为离 \(Q\alpha\) 最近的整数，并取 \(k=(Q,-P)\)。此时 \(\langle k\rangle\le C_\alpha Q\)，故得到右边的下界。反向对 \(k_1\ne0\) 取 \(Q=|k_1|\)，使用
\[
|d_\alpha(k)|\ge\|Q\alpha\|_{\mathbb R/\mathbb Z},
\qquad Q^{-s}\ge\langle k\rangle^{-s}.
\]
对 \(k_1=0,\ k\ne0\)，直接有 \(|d_\alpha(k)|=|k_2|\ge1\)。

式 (4) 也等价于存在 \(c>0\)，使一切 \(P\in\mathbb Z,\ Q\ge1\) 都满足
\[
\left|\alpha-\frac P Q\right|\ge c Q^{-(s+1)}.
\]
若所有有限 \(s\) 都失效，则对每个整数 \(M\ge1\)，在 (4) 中取 \(s=M-1\)，就有任意大的 \(Q\) 和相应的 \(P\) 满足 \(|\alpha-P/Q|<Q^{-M}\)。这正是 Liouville 性质。反过来，具有该性质时，对每个固定 \(s\) 取整数 \(M>s+1\)，这些逼近便使 (4) 的下确界为零。这证明了开头的可逆方向分类。

为证明全部损失的判据 (3)，记 \(\varepsilon_j=q_j\alpha-p_j\)。实无理数的简单连分数收敛分数满足
\[
\frac{1}{q_{j+1}+q_j}<|\varepsilon_j|<\frac{1}{q_{j+1}},
\qquad
|Q\alpha-P|\ge|\varepsilon_j|
\quad(P\in\mathbb Z,\ 0<Q<q_{j+1}). \tag{5}
\]
具体地，若 \(t=[a_{j+1};a_{j+2},\ldots]\) 为连分数尾数，则递推公式给出
\(\varepsilon_j=(-1)^j/(q_jt+q_{j-1})\)，其中 \(q_{-1}=0\)。由 \(a_{j+1}<t<a_{j+1}+1\) 及 \(q_{j+1}=a_{j+1}q_j+q_{j-1}\) 即得两侧误差界。再由相邻收敛分数的行列式为 \(\pm1\)，可写
\[
(Q,P)=A(q_j,p_j)+B(q_{j+1},p_{j+1}),\qquad A,B\in\mathbb Z.
\]
当 \(0<Q<q_{j+1}\) 时，若 \(B=0\) 则 \(A\ge1\)。若 \(B\ne0\) 则 \(A,B\) 异号，又因 \(\varepsilon_j,\varepsilon_{j+1}\) 异号，\(A\varepsilon_j\) 与 \(B\varepsilon_{j+1}\) 同号。两种情形都有 \(|Q\alpha-P|\ge|\varepsilon_j|\)。

若 (4) 成立，取 \(Q=q_j,\ P=p_j\)，由 (5) 得 \(c q_j^{-s}\le|\varepsilon_j|<1/q_{j+1}\)，从而 (3) 中的上确界有限。反之，设该上确界为 \(K<\infty\)。对任意 \(Q\ge1\) 取 \(q_j\le Q<q_{j+1}\)，由 (5) 得
\[
\|Q\alpha\|_{\mathbb R/\mathbb Z}
>\frac1{2q_{j+1}}\ge\frac1{2Kq_j^s}\ge\frac1{2KQ^s}.
\]
这证明了 (3)。

特别地，令
\[
\tau=\limsup_{j\to\infty}\frac{\log q_{j+1}}{\log q_j}\in[1,\infty],
\]
其中只需取 \(q_j>1\) 的尾部。则
\[
\mathcal S(\alpha)=
\begin{cases}
\varnothing,&\tau=\infty,\\
[\tau,\infty),&\tau<\infty,\quad \sup_j q_{j+1}/q_j^\tau<\infty,\\
(\tau,\infty),&\tau<\infty,\quad \sup_j q_{j+1}/q_j^\tau=\infty .
\end{cases}
\]
事实上，\(s>\tau\) 时最终有 \(q_{j+1}\le q_j^s\)。若 \(s<\tau\)，则存在 \(\eta>0\) 使 \(q_{j+1}\ge q_j^{s+\eta}\) 无穷多次，而 \(q_j\to\infty\)。在端点 \(s=\tau<\infty\) 直接应用 (3)。

### 方向 \(\alpha_*=\sqrt2-1\)

由 \(1/\alpha_*=2+\alpha_*\)，其连分数为 \([0;2,2,\ldots]\)。故 \(q_{j+1}=2q_j+q_{j-1}\le3q_j\)，按 (3)，\(s=1\) 允许。对 \(s<1\)，有 \(q_{j+1}/q_j^s\ge q_j^{1-s}\to\infty\)。所以**最小损失为 \(1\)，且端点取到**。

所问的 \(C^m\) 估计对每个 \(m\ge0\) 都成立。一般地，若 \(D_s(\alpha)>0\)，对整数 \(L>m+s+2\)，由 (1)、(2) 有
\[
\begin{aligned}
\|N_\alpha^{-1}F\|_{C^m}
&\le (2\pi)^m\sum_{k\ne0}\langle k\rangle^m|\widehat u(k)|\\
&\le \frac{(2\pi)^m A_L}{2\pi D_s(\alpha)}
 \|F\|_{C^L}\sum_{k\ne0}\langle k\rangle^{m+s-L}.
\end{aligned}
\]
最后的级数因 \(L-m-s>2\) 在二维收敛，这也给出可逆情形下逆算子在光滑拓扑中的连续性。取 \(\alpha=\alpha_*,\,s=1,\,L=m+4\)，级数即为 \(\sum_{k\ne0}\langle k\rangle^{-3}\)，得到
\[
\boxed{\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}.}
\]

## S5 邻近方向的一致估计

**不存在这样的 \(J,s,C\)。** 任取含 \(\alpha_*\) 的开区间 \(J\)，在其中取一个有理数 \(p/q\)，其中 \(q\ge1\)。固定 \(k=(q,-p)\) 和光滑零均值函数 \(u=e_k\)。令 \(\alpha_n=p/q+\sqrt2/n\)，则每个 \(\alpha_n\) 无理，且充分大时 \(\alpha_n\in J\)。此时
\[
\|u\|_{L^2}=1,\qquad
\|N_{\alpha_n}u\|_{H^s}
=2\pi\langle k\rangle^s\,|q\alpha_n-p|
=2\pi\langle k\rangle^s\frac{q\sqrt2}{n}\longrightarrow0.
\]
因此任意固定的有限 \(s,C\) 都会在同一模式 \(u\) 上失效。

## S6 一个具体方向的不可解数据

取小数截断
\[
Q_n=10^{n!},\qquad
P_n=Q_n\sum_{\ell=1}^n10^{-\ell!}\in\mathbb Z,\qquad
\epsilon_n=Q_n\alpha-P_n.
\]
因尾项的十进制指数从 \((n+1)!\) 开始且严格递增，
\[
0<\alpha-\frac{P_n}{Q_n}
\le\frac{10}{9}\,10^{-(n+1)!},
\qquad
0<\epsilon_n\le\frac{10}{9}\,Q_n^{-n}. \tag{6}
\]
若 \(\alpha=A/B\) 为有理数，\(B\ge1\)，则 \(B\epsilon_n=AQ_n-BP_n\) 是正整数。但 (6) 给出 \(B\epsilon_n\to0\)，矛盾。故 \(\alpha\) 无理。

令 \(k_n=(Q_n,-P_n)\)，构造单个右端
\[
\boxed{\displaystyle
F(y)=2\pi i\sum_{n=1}^{\infty}\epsilon_n e^{2\pi i k_n\cdot y}.}
\]
这些频率互异且非零。由 \(0<P_n/Q_n<\alpha\) 得 \(|k_n|\le C Q_n\)，所以对每个固定的 \(m\)，级数第 \(n\) 项的任意 \(m\) 阶导数都由 \(C_m Q_n^{m-n}\) 控制。当 \(n\ge m+1\) 时，该界至多为 \(C_m Q_n^{-1}\)，而 \(\sum_n Q_n^{-1}<\infty\)。因此各阶导数级数绝对一致收敛，且 \(F\) 的均值为零。

由于 \(d_\alpha(k_n)=\epsilon_n>0\)，任何光滑解在每个 \(k_n\) 上都必须满足
\[
2\pi i\epsilon_n\,\widehat u(k_n)=\widehat F(k_n)=2\pi i\epsilon_n,
\qquad\text{故}\qquad \widehat u(k_n)=1.
\]
这与光滑函数的 Fourier 系数平方可和矛盾。因此这个 \(F\) 没有光滑零均值解。