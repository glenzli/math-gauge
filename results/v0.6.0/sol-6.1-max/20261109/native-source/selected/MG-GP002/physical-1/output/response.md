记
\[
e_k(y)=e^{2\pi i k\cdot y},\qquad
\omega_\alpha(k)=\alpha k_1+k_2.
\]
则
\[
N_\alpha e_k=2\pi i\,\omega_\alpha(k)e_k.
\]
当 \(\alpha\) 无理时，所有 \(k\ne0\) 都满足 \(\omega_\alpha(k)\ne0\)。

以下使用环面上的基本傅里叶事实：光滑函数的傅里叶系数快速衰减；反之，快速衰减的系数所定义的傅里叶级数及其任意阶导数都绝对一致收敛，从而定义光滑函数。前者由反复分部积分得到，后者使用二维格点上的可和性
\(\sum_k\langle k\rangle^{-t}<\infty\)（\(t>2\)）。

**S1. 有限频带上的逆**

对 \(F\in H_N\)，定义
\[
N_{\alpha,N}^{-1}F
=\sum_{0<|k|\le N}
\frac{\widehat F(k)}{2\pi i\,\omega_\alpha(k)}e_k.
\]
所有分母非零，故这给出了 \(N_\alpha:H_N\to H_N\) 的双边逆。

对任意 \(r\in\mathbb R\)，
\[
\|N_{\alpha,N}^{-1}F\|_{H^r}^2
=\sum_{0<|k|\le N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{4\pi^2|\omega_\alpha(k)|^2}.
\]
因此精确的逆范数为
\[
\boxed{
\|N_{\alpha,N}^{-1}\|_{H^r\to H^r}
=\frac{1}{2\pi\displaystyle\min_{0<|k|\le N}
|\alpha k_1+k_2|}.
}
\]
该值与 \(r\) 无关。取达到上述最小值的频率 \(k_0\)，并令 \(F=e_{k_0}\)，即可取得范数比的等号。

**S2. 有算术界的截断误差**

定义
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}
{2\pi i\,\omega_\alpha(k)}
\quad(k\ne0).
\]
由给定算术界，
\[
|\widehat u(k)|
\le \frac1{2\pi c}\langle k\rangle^s|\widehat F(k)|.
\]
因为 \(F\) 光滑，其系数快速衰减，右侧仍快速衰减。因此该级数定义 \(u\in C^\infty_0\)，逐项求导可得 \(N_\alpha u=F\)。傅里叶系数还表明解唯一。

S1 中的 \(u_N\) 正是 \(u\) 的频带截断。于是对任意 \(r\in\mathbb R\)、\(q\ge0\)，
\[
\begin{aligned}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}
\frac{\langle k\rangle^{2r}|\widehat F(k)|^2}
{4\pi^2|\omega_\alpha(k)|^2}\\
&\le \frac1{4\pi^2c^2}
\sum_{|k|>N}
\langle k\rangle^{2(r+s+q)}
\langle k\rangle^{-2q}|\widehat F(k)|^2\\
&\le \frac{(1+N^2)^{-q}}{4\pi^2c^2}
\|F\|_{H^{r+s+q}}^2.
\end{aligned}
\]
取平方根即得
\[
\boxed{
\|u-u_N\|_{H^r}
\le (2\pi c)^{-1}(1+N^2)^{-q/2}
\|F\|_{H^{r+s+q}}.
}
\]

**S3. 固定频带内改变方向**

对 \(0<|k|\le N\)，
\[
\begin{aligned}
\widehat{u_\alpha-u_\beta}(k)
&=\frac{\widehat F(k)}{2\pi i}
\left(\frac1{\omega_\alpha(k)}
-\frac1{\omega_\beta(k)}\right)\\
&=\frac{(\beta-\alpha)k_1}
{2\pi i\,\omega_\alpha(k)\omega_\beta(k)}
\,\widehat F(k).
\end{aligned}
\]
由 \(|k_1|\le N\) 及两个除数的下界，
\[
|\widehat{u_\alpha-u_\beta}(k)|
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}
|\widehat F(k)|.
\]
乘以 Sobolev 权重、平方求和，得到对每个实数 \(r\)，
\[
\boxed{
\|u_\alpha-u_\beta\|_{H^r}
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}
\|F\|_{H^r}.
}
\]

**S4. 整体可逆性、全部允许损失及 \(\alpha_*\)**

结论是：每个光滑零均值数据都有唯一光滑零均值解，当且仅当 \(\alpha\) 具有有限无理性指数。允许的 Sobolev 损失构成一个半直线，但其左端点可能取不到。下面给出精确判据和证明。

令
\[
\|x\|_{\mathbb Z}=\min_{p\in\mathbb Z}|x-p|,
\]
并对 \(s\ge0\) 定义
\[
d_s(\alpha)=\inf_{k\ne0}
\langle k\rangle^s|\alpha k_1+k_2|,
\qquad
b_s(\alpha)=\inf_{q\ge1}q^s\|q\alpha\|_{\mathbb Z}.
\]

首先，固定损失 \(s\) 的精确判据是
\[
\boxed{
\begin{gathered}
\forall r\in\mathbb R\ \exists C_{\alpha,r,s}<\infty:
\quad
\|u\|_{H^r}\le C_{\alpha,r,s}
\|N_\alpha u\|_{H^{r+s}}
\quad(u\in C^\infty_0)
\\
\Longleftrightarrow\quad d_s(\alpha)>0.
\end{gathered}
}
\]
事实上，只要该估计对某一个 \(r\) 成立，取 \(u=e_k\) 就得到
\[
1\le 2\pi C_{\alpha,r,s}
\langle k\rangle^s|\omega_\alpha(k)|,
\]
故 \(d_s(\alpha)>0\)。反过来，若 \(d_s>0\)，逐项估计给出
\[
\|u\|_{H^r}^2
\le \frac1{4\pi^2d_s^2}
\|N_\alpha u\|_{H^{r+s}}^2.
\]
因此最优常数也是精确已知的：
\[
\boxed{C_{\alpha,r,s}^{\mathrm{opt}}
=\frac1{2\pi d_s(\alpha)}.}
\]
它与 \(r\) 无关；用单频函数逼近上述下确界即可证明最优性。

两个算术判据等价：
\[
\boxed{d_s(\alpha)>0\quad\Longleftrightarrow\quad b_s(\alpha)>0.}
\]
证明如下。若 \(b_s>0\)，则当 \(k_1\ne0\) 时，以 \(q=|k_1|\) 得
\[
|\alpha k_1+k_2|
\ge \|q\alpha\|_{\mathbb Z}
\ge b_s q^{-s}
\ge b_s\langle k\rangle^{-s}.
\]
当 \(k_1=0\) 时，除数绝对值至少为 \(1\)，故 \(d_s>0\)。

反过来，对每个 \(q\ge1\) 取最接近 \(q\alpha\) 的整数 \(p\)。有
\[
|p|\le |\alpha|q+\tfrac12,
\qquad
\langle(q,-p)\rangle\le A_\alpha q
\]
其中 \(A_\alpha<\infty\) 只依赖于 \(\alpha\)。于是
\[
\|q\alpha\|_{\mathbb Z}
\ge d_s\langle(q,-p)\rangle^{-s}
\ge d_s A_\alpha^{-s}q^{-s},
\]
所以 \(b_s>0\)。

为了列出全部允许损失，定义
\[
\tau(\alpha)
=\limsup_{q\to\infty}
\frac{\log(1/\|q\alpha\|_{\mathbb Z})}{\log q}.
\]
通常的无理性指数
\[
\mu(\alpha)
=\sup\left\{\nu:
\left|\alpha-\frac pq\right|<q^{-\nu}
\text{ 对无穷多个 }(p,q)\in\mathbb Z\times\mathbb N
\text{ 成立}\right\}
\]
满足
\[
\mu(\alpha)=1+\tau(\alpha),
\]
因为对固定 \(q\)，最小的逼近误差是
\(\|q\alpha\|_{\mathbb Z}/q\)。

先说明 \(\tau(\alpha)\ge1\)。对任意正整数 \(Q\)，将
\(\{j\alpha\}\)、\(0\le j\le Q\) 放入 \(Q\) 个等长小区间，抽屉原理给出某个 \(1\le q\le Q\)，使
\[
0<\|q\alpha\|_{\mathbb Z}<Q^{-1}\le q^{-1}.
\]
因为 \(\alpha\) 无理，随着 \(Q\to\infty\)，这些 \(q\) 必然无界。因此有无穷多个这样的 \(q\)，从而 \(\tau\ge1\)，并且每个 \(s<1\) 都不允许。

所有允许损失恰好为
\[
\boxed{
\mathcal S_\alpha=
\begin{cases}
\varnothing,&\tau(\alpha)=\infty,\\[2mm]
[\tau(\alpha),\infty),
&\tau(\alpha)<\infty,\ b_{\tau(\alpha)}(\alpha)>0,\\[2mm]
(\tau(\alpha),\infty),
&\tau(\alpha)<\infty,\ b_{\tau(\alpha)}(\alpha)=0.
\end{cases}
}
\]
这里的端点条件不可省略。证明如下：

- 若 \(s>\tau\)，取 \(\tau<\sigma<s\)。对充分大的 \(q\)，有
  \(\|q\alpha\|_{\mathbb Z}\ge q^{-\sigma}\)，故
  \(q^s\|q\alpha\|_{\mathbb Z}\ge q^{s-\sigma}\ge1\)。
  剩余有限个 \(q\) 的相应值均为正，因此 \(b_s>0\)。
- 若 \(s<\tau\)，取 \(s<\sigma<\tau\)；当 \(\tau=\infty\) 时任取有限 \(\sigma>s\)。有无穷多个趋于无穷的 \(q\) 满足
  \(\|q\alpha\|_{\mathbb Z}<q^{-\sigma}\)，故
  \(q^s\|q\alpha\|_{\mathbb Z}\to0\) 沿某个子列成立，因此 \(b_s=0\)。
- 当 \(s=\tau<\infty\) 时，是否允许恰由 \(b_\tau>0\) 决定。

等价地，临界损失是 \(\mu(\alpha)-1\)；若端点条件失败，允许损失没有最小值，其下确界仍是这个数。

也可以用连分数给出直接的算术分类。设 \(p_n/q_n\) 为无理数 \(\alpha\) 的正则连分数收敛分数，则
\[
\boxed{
s\in\mathcal S_\alpha
\quad\Longleftrightarrow\quad
\sup_n\frac{q_{n+1}}{q_n^s}<\infty.
}
\]
这里使用适用于任意无理实数的标准连分数定理：忽略有限个初始项后，
\[
\frac1{q_{n+1}+q_n}
<|q_n\alpha-p_n|<\frac1{q_{n+1}},
\]
且当 \(q_n\le q<q_{n+1}\) 时，
\[
\|q\alpha\|_{\mathbb Z}\ge |q_n\alpha-p_n|.
\]
若 \(b_s>0\)，第一组不等式给出
\[
b_s q_n^{-s}
\le\|q_n\alpha\|_{\mathbb Z}
\le |q_n\alpha-p_n|<q_{n+1}^{-1},
\]
故所述比值有界。反之，若 \(q_{n+1}\le Mq_n^s\)，则对
\(q_n\le q<q_{n+1}\)，
\[
\|q\alpha\|_{\mathbb Z}
>\frac1{q_{n+1}+q_n}
\ge\frac1{2M q_n^s}
\ge\frac1{2M q^s}.
\]
再处理有限个初始分母，即得 \(b_s>0\)。特别地，当 \(\tau=1\) 时，端点允许恰好等价于连分数部分商有界。

下面证明整体可逆性的结论。对任意无理 \(\alpha\)，若 \(N_\alpha u=0\)，则所有非零频率的 \(\widehat u(k)\) 都为零，所以 \(u\) 为常数；零均值条件使它为零。因此该算子始终单射。

若 \(\tau<\infty\)，取任意 \(s>\tau\)，则 \(d_s>0\)。S2 的全部假设以 \(c=d_s\) 成立，因而对每个 \(F\in C^\infty_0\)，公式
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}
{2\pi i\,\omega_\alpha(k)}
\]
给出唯一光滑零均值解，并且
\[
\|N_\alpha^{-1}F\|_{H^r}
\le \frac1{2\pi d_s}\|F\|_{H^{r+s}}.
\]
这些估计也说明逆在 \(C^\infty\) 拓扑下连续。

若 \(\tau=\infty\)，则每个整数 \(j\ge1\) 都有 \(d_j=0\)。由于任何有限频集上的除数均非零，可以递归选取 \(|k_j|\) 严格递增的频率，使
\[
0<|\omega_\alpha(k_j)|
\le 2^{-j}\langle k_j\rangle^{-j}.
\]
定义一个固定的数据
\[
F=\sum_{j=1}^\infty
2\pi i\,\omega_\alpha(k_j)e_{k_j}.
\]
对任意总阶数为 \(m\) 的导数，第 \(j\) 项绝对值不超过
\[
(2\pi)^{m+1}2^{-j}\langle k_j\rangle^{m-j}.
\]
当 \(j\ge m\) 时，这至多为 \((2\pi)^{m+1}2^{-j}\)。因此所有阶导数级数都绝对一致收敛，故 \(F\in C^\infty_0\)。

然而，任何解都必须满足
\[
\widehat u(k_j)
=\frac{\widehat F(k_j)}
{2\pi i\,\omega_\alpha(k_j)}=1.
\]
这违反光滑函数傅里叶系数趋于零的必要条件。因此该 \(F\) 没有光滑解，满射性失败。

综上，
\[
\boxed{
N_\alpha:C^\infty_0\longrightarrow C^\infty_0
\text{ 可逆}
\iff \tau(\alpha)<\infty
\iff \mu(\alpha)<\infty.
}
\]

现在取 \(\alpha_*=\sqrt2-1\)，其代数共轭为
\[
\alpha_*'=-\sqrt2-1.
\]
对任意非零整数频率 \(k\)，
\[
(\alpha_*k_1+k_2)(\alpha_*'k_1+k_2)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数。非零性来自 \(\sqrt2\) 无理：若 \(k_1\ne0\)，该二次式为零会迫使 \(k_2/k_1=1\pm\sqrt2\)；若 \(k_1=0\)，则它等于 \(k_2^2>0\)。

因此，令
\[
A=\sqrt{1+(\alpha_*')^2}
=\sqrt{4+2\sqrt2},
\]
由 Cauchy–Schwarz 不等式，
\[
|\alpha_*k_1+k_2|
\ge \frac1{|\alpha_*'k_1+k_2|}
\ge\frac1{A|k|}
\ge\frac1{A\langle k\rangle}.
\]
故 \(s=1\) 允许。结合所有无理数都不允许 \(s<1\) 的结论，得到
\[
\boxed{\mathcal S_{\alpha_*}=[1,\infty),\qquad
s_{\min}=1\text{，且取到。}}
\]

最后，所问 \(C^m\) 估计成立。说明所用范数比较：在二维环面上，
\[
\|v\|_{C^m}\le A_m\|v\|_{H^{m+2}},
\]
因为对各阶导数的傅里叶级数使用 Cauchy–Schwarz 后，余下的和为
\(\sum_k\langle k\rangle^{-4}<\infty\)。另一方面，对整数 \(M\ge0\)，展开 \((1+|k|^2)^M\) 并用 Parseval 恒等式，可得
\[
\|G\|_{H^M}\le B_M\|G\|_{C^M};
\]
这里也使用了归一化测度下各导数的 \(L^2\) 范数不超过其上确界范数。

以 \(c_*=A^{-1}\) 使用损失 \(1\) 的估计，
\[
\begin{aligned}
\|N_{\alpha_*}^{-1}F\|_{C^m}
&\le A_m\|N_{\alpha_*}^{-1}F\|_{H^{m+2}}\\
&\le\frac{A_m}{2\pi c_*}\|F\|_{H^{m+3}}\\
&\le\frac{A_mB_{m+3}}{2\pi c_*}\|F\|_{C^{m+3}}\\
&\le C_m\|F\|_{C^{m+4}}.
\end{aligned}
\]
常数仅依赖于 \(m\) 和固定方向 \(\alpha_*\)。事实上，上面还证明了右侧用 \(C^{m+3}\) 范数也足够。

**S5. 邻近方向的一致估计**

结论：不存在所述 \(J,s,C\)。

任取包含 \(\alpha_*\) 的开区间 \(J\)、有限 \(s\ge0\) 及有限常数 \(C\)。由有理数稠密性，选取
\[
\frac pq\in J,\qquad p\in\mathbb Z,\quad q\in\mathbb N.
\]
令
\[
k=(q,-p),\qquad u=e_k,\qquad
\alpha_\ell=\frac pq+\frac{\sqrt2}{\ell}.
\]
每个 \(\alpha_\ell\) 都无理，且充分大的 \(\ell\) 满足 \(\alpha_\ell\in J\)。同时，\(u\) 光滑、零均值，并且
\[
\|u\|_{L^2}=1,
\]
而
\[
\|N_{\alpha_\ell}u\|_{H^s}
=2\pi|q\alpha_\ell-p|\langle k\rangle^s
=\frac{2\pi q\sqrt2}{\ell}\langle k\rangle^s
\longrightarrow0.
\]
所假定的一致估计将给出
\[
1\le C\,\frac{2\pi q\sqrt2}{\ell}\langle k\rangle^s
\]
对所有充分大的 \(\ell\) 成立，矛盾。

**S6. 具体方向及同一个不可解数据**

设
\[
\alpha=\sum_{j=1}^\infty10^{-j!},\qquad
q_n=10^{n!},\qquad
p_n=q_n\sum_{j=1}^n10^{-j!}\in\mathbb Z.
\]
尾项满足
\[
0<\alpha-\frac{p_n}{q_n}
=\sum_{j=n+1}^\infty10^{-j!}
<2\,10^{-(n+1)!}.
\]
因而
\[
\boxed{
0<q_n\alpha-p_n<2q_n^{-n}.
}
\]

这首先证明 \(\alpha\) 无理。若 \(\alpha=a/b\)，其中 \(a\in\mathbb Z\)、\(b\in\mathbb N\)，则
\[
b(q_n\alpha-p_n)=q_na-bp_n
\]
是正整数，所以 \(q_n\alpha-p_n\ge b^{-1}\)，与上述上界趋于零矛盾。

令
\[
k_n=(q_n,-p_n),\qquad n\ge2,
\]
并定义
\[
\boxed{
F(y)=\sum_{n=2}^\infty
q_n^{-n/2}
e^{2\pi i(q_ny_1-p_ny_2)}.
}
\]
这是一个固定的函数。下面验证它光滑、零均值且不可解。

因为
\[
0<\frac{p_n}{q_n}<\alpha
\le\sum_{j=1}^\infty10^{-j}<1,
\]
所以 \(0<p_n<q_n\)。对于 \(a+b=m\)，第 \(n\) 项导数的绝对值至多为
\[
(2\pi)^m q_n^{m-n/2}.
\]
当 \(n\ge2m+2\) 时，该值至多为
\[
(2\pi)^m q_n^{-1}.
\]
而
\[
\sum_{n=2}^\infty q_n^{-1}
=\sum_{n=2}^\infty10^{-n!}<\infty.
\]
因此每一阶导数级数都绝对一致收敛，故 \(F\in C^\infty\)。所有频率 \(k_n\) 非零且彼此不同，所以
\[
\int_{\mathbb T^2}F=0,\qquad
\widehat F(k_n)=q_n^{-n/2}.
\]

若存在光滑解 \(u\)，则其对应系数必须满足
\[
|\widehat u(k_n)|
=\frac{q_n^{-n/2}}{2\pi|q_n\alpha-p_n|}
\ge\frac1{4\pi}q_n^{n/2}
\longrightarrow\infty.
\]
但任何光滑函数都是可积函数，其傅里叶系数满足
\[
|\widehat u(k)|\le\|u\|_{L^1}<\infty,
\]
矛盾。因此上述同一个 \(F\in C^\infty_0(\mathbb T^2)\) 使 \(N_\alpha u=F\) 没有光滑零均值解。