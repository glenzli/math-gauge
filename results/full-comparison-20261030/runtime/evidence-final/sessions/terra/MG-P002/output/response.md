记
\[
d_\alpha(q)=\min_{p\in\mathbb Z}|q\alpha-p|,
\qquad
D_\alpha(s)=\inf_{q\ge1}q^s d_\alpha(q),
\]
并定义无理逼近指数
\[
\mu(\alpha)=\sup\left\{\nu>0:
\left|\alpha-\frac pq\right|<q^{-\nu}
\text{ 对无穷多个 }(p,q)\in\mathbb Z\times\mathbb N\text{ 成立}\right\}.
\]
对每个无理数都有 \(\mu(\alpha)\ge2\)；这里允许 \(\mu(\alpha)=\infty\)。后者正是 \(\alpha\) 为刘维尔数的情形。

**定理。** 对无理数 \(\alpha\)，有以下结论。

1. \(N_\alpha\) 在 \(C^\infty_0(\mathbb T^2)\) 上是双射，当且仅当 \(\mu(\alpha)<\infty\)，即 \(\alpha\) 不是刘维尔数。此时逆算子在 \(C^\infty\) 拓扑下连续。

2. 对 \(s\ge0\)，题中的 Sobolev 估计对每个 \(r\in\mathbb R\) 成立，当且仅当
   \[
   D_\alpha(s)>0.
   \]
   这个条件与 \(r\) 无关。更具体地：
   
   - 若 \(\mu(\alpha)=\infty\)，没有允许的有限损失 \(s\)。
   - 若 \(\mu(\alpha)<\infty\)，所有 \(s>\mu(\alpha)-1\) 都允许，所有 \(s<\mu(\alpha)-1\) 都不允许。
   - 端点 \(s=\mu(\alpha)-1\) 允许，当且仅当
     \[
     \inf_{q\ge1}q^{\mu(\alpha)-1}d_\alpha(q)>0.
     \]
     因而单凭 \(\mu(\alpha)\) 的值不能判断端点是否取到。

3. 令 \(p_n/q_n\) 为 \(\alpha\) 的连分数收敛分数。一个等价的可检验判据是
   \[
   \boxed{\quad D_\alpha(s)>0
   \quad\Longleftrightarrow\quad
   \sup_n\frac{q_{n+1}}{q_n^s}<\infty.\quad}
   \]
   并且
   \[
   \mu(\alpha)
   =1+\limsup_{n\to\infty}\frac{\log q_{n+1}}{\log q_n}.
   \]

4. 对 \(\alpha_*=\sqrt2-1\)，允许的损失恰为
   \[
   \boxed{\ s\ge1\ }.
   \]
   因此最小损失是 \(1\)，而且端点取到。对每个 \(m\in\mathbb N_0\)，零均值解还满足比题目所问更强的估计
   \[
   \boxed{\quad
   \|N_{\alpha_*}^{-1}F\|_{C^m}
   \le C_m\|F\|_{C^{m+3}}
   \le C_m\|F\|_{C^{m+4}}.
   \quad}
   \]

下面证明这些结论。

对 \(k=(k_1,k_2)\)，写
\[
\lambda_k=\alpha k_1+k_2.
\]
由于 \(\alpha\) 无理，\(k\ne0\) 时 \(\lambda_k\ne0\)，且
\[
\widehat{N_\alpha u}(k)=2\pi i\lambda_k\widehat u(k).
\]
所以零均值解若存在，只能由
\[
\widehat u(0)=0,\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\lambda_k}
\quad(k\ne0)
\]
给出；这也证明了唯一性。

逐项比较傅里叶级数，并用单个指数函数
\(u(y)=e^{2\pi i k\cdot y}\) 检验，可知 Sobolev 估计的最优常数为
\[
\frac1{2\pi}
\sup_{k\in\mathbb Z^2\setminus\{0\}}
\frac{\langle k\rangle^{-s}}{|\lambda_k|},
\]
其中上确界可以是无穷大。特别地，最优常数不依赖于 \(r\)。

这个上确界有限等价于 \(D_\alpha(s)>0\)。事实上，若后者成立，对 \(k=(q,-p)\)、\(q\ne0\)，有
\[
|q\alpha-p|\ge d_\alpha(|q|)
\ge D_\alpha(s)|q|^{-s}
\ge D_\alpha(s)\langle k\rangle^{-s};
\]
\(q=0\) 的情形也显然满足所需下界。反过来，对每个 \(q\ge1\) 选取最接近 \(q\alpha\) 的整数 \(p\)，则
\(\langle(q,-p)\rangle\le C_\alpha q\)，于是小除数下界推出
\(d_\alpha(q)\ge c_{\alpha,s}q^{-s}\)。

若某个 \(D_\alpha(s)>0\)，上述除法至多使傅里叶系数增长一个多项式因子。因此光滑 \(F\) 的快速下降傅里叶系数除以 \(\lambda_k\) 后仍快速下降，得到光滑解。

反之，假设对所有 \(s\ge0\) 都有 \(D_\alpha(s)=0\)。可以依次选取不同的非零频率 \(k_j\)，使 \(|k_j|\to\infty\) 且
\[
|\lambda_{k_j}|<\langle k_j\rangle^{-j}.
\]
定义 \(F\) 的傅里叶系数为
\[
\widehat F(k_j)=\langle k_j\rangle^{-j/2},
\qquad
\widehat F(k)=0\quad(k\notin\{k_j:j\ge1\}).
\]
这些系数快速下降，所以 \(F\in C^\infty_0\)。但任何满足 \(N_\alpha u=F\) 的解都必须满足
\[
|\widehat u(k_j)|
>\frac1{2\pi}\langle k_j\rangle^{j/2}.
\]
这甚至违反了环面上分布的傅里叶系数至多多项式增长的性质。因此这个光滑 \(F\) 没有分布解，更没有光滑解。由此得到双射性的充要条件。

为证明关于 \(\mu(\alpha)\) 的分类，Dirichlet 抽屉原理给出无穷多个 \(p/q\) 满足
\[
\left|\alpha-\frac pq\right|<q^{-2},
\]
所以 \(\mu(\alpha)\ge2\)。若 \(s+1>\mu(\alpha)\)，满足
\(|\alpha-p/q|<q^{-(s+1)}\) 的整数对只有有限多个；把有限个例外吸收到常数中，即得 \(D_\alpha(s)>0\)。若 \(s+1<\mu(\alpha)\)，选
\(\nu\in(s+1,\mu(\alpha))\)，则无穷多个近似满足
\[
q^s d_\alpha(q)\le q^{s+1-\nu}\longrightarrow0,
\]
故 \(D_\alpha(s)=0\)。当 \(\mu(\alpha)=\infty\) 时，同一论证对每个有限 \(s\) 成立。端点则由 \(D_\alpha(\mu(\alpha)-1)>0\) 精确决定。

连分数判据来自收敛分数的两个基本估计：
\[
\frac1{q_{n+1}+q_n}
<|q_n\alpha-p_n|<\frac1{q_{n+1}},
\]
并且对 \(0<q<q_{n+1}\) 和任意整数 \(p\)，
\[
|q\alpha-p|\ge |q_n\alpha-p_n|.
\]
第二个估计可由相邻收敛分数构成的整数格基证明：将
\((p,q)\) 写成 \((p_n,q_n)\) 与 \((p_{n+1},q_{n+1})\) 的整数线性组合，再利用相邻误差异号。于是，对 \(q_n\le q<q_{n+1}\)，
\[
d_\alpha(q)>\frac1{q_{n+1}+q_n},
\qquad
d_\alpha(q_n)<\frac1{q_{n+1}}.
\]
这立即给出所述的 \(D_\alpha(s)\) 判据；取允许损失的下确界便得到 \(\mu(\alpha)\) 的连分数公式。

端点确实有两种可能。更一般地，固定任意 \(\tau\ge1\)，从 \(a_0=0,a_1=1\) 开始，分别递归指定连分数的部分商为
\[
a_{n+1}=\left\lceil q_n^{\tau-1}\right\rceil
\quad\text{或}\quad
a_{n+1}=\left\lceil q_n^{\tau-1}\log(q_n+1)\right\rceil.
\]
由 \(q_{n+1}=a_{n+1}q_n+q_{n-1}\) 可知，两种构造都有
\(\mu=1+\tau\)；前者的 \(q_{n+1}/q_n^\tau\) 有界，后者则趋于无穷。因此前者取到端点 \(s=\tau\)，后者取不到。

对 \(\alpha_*=\sqrt2-1\)，令其共轭数为
\(\alpha'=-1-\sqrt2\)。对于非零 \(k\in\mathbb Z^2\)，
\[
(\alpha_*k_1+k_2)(\alpha'k_1+k_2)
=k_2^2-2k_1k_2-k_1^2
\]
是非零整数，故绝对值至少为 \(1\)。又
\[
|\alpha'k_1+k_2|
\le \sqrt{4+2\sqrt2}\,|k|,
\]
因此
\[
|\alpha_*k_1+k_2|
\ge \frac1{\sqrt{4+2\sqrt2}\,|k|}.
\]
这给出端点估计
\[
\|u\|_{H^r}
\le \frac{\sqrt{4+2\sqrt2}}{2\pi}
\|N_{\alpha_*}u\|_{H^{r+1}}
\qquad(r\in\mathbb R).
\]
另一方面，Dirichlet 近似已表明任何无理数都不能允许 \(s<1\)，所以该损失最小。

最后说明 \(C^m\) 估计。由 Cauchy–Schwarz 和
\(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}<\infty\)，
\[
\|v\|_{C^m}
\le (2\pi)^m
\left(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}\right)^{1/2}
\|v\|_{H^{m+2}}.
\]
对整数 \(M\)，Parseval 恒等式和归一化测度给出
\(\|F\|_{H^M}\le C_M\|F\|_{C^M}\)。将这两个估计与上面的损失 \(1\) 估计相接，即得
\[
\|N_{\alpha_*}^{-1}F\|_{C^m}
\le C_m\|N_{\alpha_*}^{-1}F\|_{H^{m+2}}
\le C_m\|F\|_{H^{m+3}}
\le C_m\|F\|_{C^{m+3}}.
\]
同样的方法也证明：只要 \(D_\alpha(s)>0\)，就有
\[
\|N_\alpha^{-1}F\|_{C^m}
\le C_{\alpha,m,s}\,
\|F\|_{C^{m+\lceil s\rceil+2}},
\]
从而逆算子在 \(C^\infty\) 拓扑下连续。