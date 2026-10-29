# 参考论证：环面输运方程的逆与正则性

这是评审材料。候选只接收 task.md。本题的固定方向目标成立；一般无理方向的光滑满射性有实际边界。以下证明所有题面目标。允许任何正确的等价刻画或更短证明，不要求使用本稿的指标、顺序或全部补充结论。

## 1. 主定理

对固定的无理数 $\alpha$，写

$$d_\alpha(k)=\alpha k_1+k_2,
\qquad
D_s(\alpha)=\inf_{k\in\mathbb Z^2\setminus\{0\}}\langle k\rangle^s|d_\alpha(k)|
\quad(s\ge0),$$

$$Q_s(\alpha)=\inf_{q\ge1}q^s\operatorname{dist}(q\alpha,\mathbb Z).$$

其中 $q$ 为正整数。则：

1. $N_\alpha$ 在 $C^\infty_0(\mathbb T^2)$ 上总是单射。它满射当且仅当存在有限的 $s\ge0$ 使 $D_s(\alpha)>0$，也等价于存在这样的 $s$ 使 $Q_s(\alpha)>0$。
2. 题面 Sobolev 估计的允许损失集合恰为

   $$\mathcal L_\alpha=\{s\ge0:D_s(\alpha)>0\}=\{s\ge0:Q_s(\alpha)>0\}.$$

   对允许的 $s$，每个 $r\in\mathbb R$ 的最佳常数都是 $1/(2\pi D_s(\alpha))$。不要求候选求出最佳常数。
3. 对 $\alpha_* =\sqrt2-1$，有 $\mathcal L_{\alpha_*}=[1,\infty)$；因此最小损失为 $1$，且取到。题面要求的全部 $C^{m+4}\to C^m$ 估计成立。

第 2 点直接保留端点：$s$ 等于某个逼近指数的临界值时，仍须检查严格正的统一下界；不能仅凭所有更大的 $s$ 都允许，就断言端点允许。

## 2. Fourier 表示与唯一性

分部积分给出

$$\widehat{N_\alpha u}(k)=2\pi i\,d_\alpha(k)\widehat u(k).$$

由于 $\alpha$ 无理，$d_\alpha(k)=0$ 只可能在 $k=0$。若 $N_\alpha u=0$ 且 $u$ 零均值，则所有 Fourier 系数均为零；由 Fourier 唯一性，$u=0$。同样，任何解都必须满足

$$\widehat u(0)=0,
\qquad
\widehat u(k)=\frac{\widehat F(k)}{2\pi i\,d_\alpha(k)}\quad(k\ne0). \tag{1}$$

这里尚未据此宣称级数定义光滑函数。对光滑 $F$，反复分部积分说明其系数快速衰减：对每个整数 $M\ge0$，存在 $A_M$ 使

$$|\widehat F(k)|\le A_M\langle k\rangle^{-M}.$$

具体地，对非零 $k$ 选 $|k_j|\ge |k|/\sqrt2$，沿第 $j$ 个变量积分 $M$ 次，再用该导数的 $L^1$ 范数即可。反过来，快速衰减的系数及其每阶导数级数绝对且一致收敛，因为在二维有 $\sum_k\langle k\rangle^{-a}<\infty$ 对 $a>2$ 成立；这给出光滑函数。Fourier 唯一性可由 $L^2$ 中指数函数的完备性使用，不需要未声明的可逆性假设。

若 $D_s(\alpha)>0$，则由 (1)

$$|\widehat u(k)|\le\frac{\langle k\rangle^s}{2\pi D_s(\alpha)}|\widehat F(k)|.$$

右侧仍快速衰减。因此 (1) 确实定义光滑零均值函数；逐项微分和 Fourier 唯一性给出 $N_\alpha u=F$。这证明了满射性的充分方向，也构造了逆。

## 3. 全部 Sobolev 损失的精确刻画

若 $D_s(\alpha)>0$，则对每个 $r$ 和每个光滑零均值 $u$，逐项有

$$\langle k\rangle^{2r}|\widehat u(k)|^2
\le\frac{1}{(2\pi D_s(\alpha))^2}\,
\langle k\rangle^{2(r+s)}|2\pi i\,d_\alpha(k)\widehat u(k)|^2.$$

求和并开平方即得估计。实数 $r$ 的正负不影响这个逐项比较，常数也不依赖 $r$。

反过来，对任意非零 $k$，取实际的光滑零均值函数 $u_k(y)=e^{2\pi i k\cdot y}$。其范数比为

$$\frac{\|u_k\|_{H^r}}{\|N_\alpha u_k\|_{H^{r+s}}}
=\frac{1}{2\pi\langle k\rangle^s|d_\alpha(k)|}.$$

只要某一个 $r$ 的估计有有限常数 $C$，就有 $D_s(\alpha)\ge1/(2\pi C)>0$。因此已得到充要条件；对所有频率的比值取上确界也给出最佳常数。

为把条件写成一维有理逼近形式，先对每个 $q\ge1$ 选离 $q\alpha$ 最近的整数 $p_q$。存在只依赖 $\alpha$ 的 $A\ge1$，使

$$\langle(q,-p_q)\rangle\le Aq.$$

故 $D_s>0$ 蕴含 $q^s\operatorname{dist}(q\alpha,\mathbb Z)\ge D_s/A^s$，从而 $Q_s>0$。反向设 $Q_s>0$：若 $k_1=0$ 且 $k\ne0$，则 $|d_\alpha(k)|=|k_2|\ge1$；若 $q=|k_1|\ge1$，则

$$|d_\alpha(k)|\ge\operatorname{dist}(q\alpha,\mathbb Z)\ge Q_s q^{-s}.$$

由于 $\langle k\rangle\ge q$ 且 $s\ge0$，有 $D_s\ge\min(1,Q_s)>0$。这证明两个刻画等价。

## 4. 光滑满射性的必要方向：一个固定的坏右端

现在假设对每个有限 $s\ge0$ 都有 $D_s(\alpha)=0$。对每个整数 $j\ge1$，递归选择非零频率 $k_j$，使 $|k_j|\ge2^j$、模长严格递增，并满足

$$0<|d_\alpha(k_j)|\le\langle k_j\rangle^{-2j}.$$

这种选择是可能的：每个有界频率集合是有限的，其非零小除数有严格正的最小加权值；$D_{2j}=0$ 因而可在任意给定半径之外实现任意小的加权值。

定义一个固定的右端

$$F(y)=\sum_{j=1}^{\infty}\langle k_j\rangle^{-j}e^{2\pi i k_j\cdot y}. \tag{2}$$

对总阶数为 $m$ 的任意偏导，级数第 $j$ 项的绝对值至多为

$$ (2\pi)^m\langle k_j\rangle^{m-j}.$$

当 $j\ge m+2$ 时，该值至多为 $(2\pi)^m 2^{-2j}$。故所有导数级数均绝对且一致收敛，(2) 定义 $C^\infty_0(\mathbb T^2)$ 中的函数，且其在 $k_j$ 处的系数正是 $\langle k_j\rangle^{-j}$。模长严格递增确保频率不重复。

若存在光滑解 $u$，由 (1) 必有

$$|\widehat u(k_j)|\ge\frac1{2\pi}\langle k_j\rangle^j\longrightarrow\infty.$$

但任意连续函数满足 $|\widehat u(k)|\le\|u\|_{L^1}$，矛盾。因此这个固定的光滑零均值右端没有光滑解。此处不能仅用“每个估计都有一个坏频率”代替 (2)：后者才否定“每个光滑右端都有光滑解”的量词。

结合第 2、3 节，满射性与存在有限允许损失等价。

## 5. 可选的逼近指数表述及其端点

前四节已经完整回答一般 $\alpha$ 的分类要求。也可令

$$\mu(\alpha)=\sup\left\{\nu\ge0:
\left|\alpha-\frac pq\right|<q^{-\nu}
\text{ 对无穷多对 }(p,q)\in\mathbb Z\times\mathbb N_{>0}\text{ 成立}\right\}.$$

则 $\mu(\alpha)\ge2$。一个简短证明是：把 $0,\alpha,\ldots,Q\alpha$ 的小数部分放进 $Q$ 个长度 $1/Q$ 的区间，得到某个 $1\le q\le Q$ 和整数 $p$ 满足 $|q\alpha-p|<1/Q\le1/q$。随着 $Q$ 增大，这些 $q$ 必无界，否则有限个正数 $\operatorname{dist}(q\alpha,\mathbb Z)$ 不可能趋于零。因此得到无穷多个 $|\alpha-p/q|<q^{-2}$。

若 $\mu<\infty$，记 $\rho=\mu-1$。对 $s>\rho$，以指数 $s+1>\mu$ 的近似只有有限多个，故除了有限多个 $q$ 外，$q^s\operatorname{dist}(q\alpha,\mathbb Z)\ge1$；有限例外的最小值仍为正，于是 $Q_s>0$。对 $s<\rho$，选 $s+1<\nu<\mu$；无穷多近似给出

$$q^s\operatorname{dist}(q\alpha,\mathbb Z)<q^{s+1-\nu}\longrightarrow0,$$

故 $Q_s=0$。端点 $s=\rho$ 属于允许集合，当且仅当 $Q_\rho>0$。所以集合为 $(\rho,\infty)$ 或 $[\rho,\infty)$，端点由上述统一下界决定。若 $\mu=\infty$，所有有限 $s$ 均不允许，且由第 4 节有光滑不可解右端。

因此“非 Liouville 无理数”也是满射性的等价刻画，但只说这个名称而不给所需证明或适用的准确定理，不足以替代论证。候选无需引入 $\mu$，也无需另举端点不取到的无理数；$Q_s>0$ 的精确充要条件已经包含端点信息。

## 6. 固定方向 $\sqrt2-1$ 的最小 Sobolev 损失

写 $k=(p,q)$、$a=q-p$，则

$$d_{\alpha_*}(k)=a+\sqrt2p,
\qquad
(a+\sqrt2p)(a-\sqrt2p)=a^2-2p^2.$$

对 $k\ne0$，最后一项为非零整数，所以绝对值至少为 $1$。而

$$|a-\sqrt2p|\le |q|+(1+\sqrt2)|p|\le(2+\sqrt2)\langle k\rangle.$$

因此

$$|d_{\alpha_*}(k)|\ge\frac1{(2+\sqrt2)\langle k\rangle},$$

说明 $D_1(\alpha_*)>0$，损失 $1$ 确实允许。对 $s\ge1$，因 $\langle k\rangle\ge1$，同样允许。

下面给出排除每个 $s<1$ 的明确频率列。令 $\lambda=1+\sqrt2$，用二项式展开定义整数 $P_n,Q_n$：

$$P_n+\sqrt2Q_n=\lambda^n,
\qquad
P_n-\sqrt2Q_n=(1-\sqrt2)^n\quad(n\ge1).$$

取 $k_n=(Q_n,Q_n-P_n)$。则 $Q_n\to\infty$，存在固定 $A$ 使 $\langle k_n\rangle\le A\lambda^n$，并且

$$|d_{\alpha_*}(k_n)|=|\sqrt2Q_n-P_n|=\lambda^{-n}.$$

对 $0\le s<1$，

$$\langle k_n\rangle^s|d_{\alpha_*}(k_n)|
\le A^s\lambda^{n(s-1)}\longrightarrow0.$$

故 $D_s=0$。单频函数 $e^{2\pi i k_n\cdot y}$ 是第 3 节范数比发散的实际输入。这证明最小损失恰为 $1$ 且取到。正确使用 Dirichlet 逼近来排除 $s<1$ 也是更短的有效替代路线。

## 7. 原定 $C^{m+4}\to C^m$ 估计

固定 $m\ge0$、$F\in C^\infty_0$。第 2、6 节已构造唯一光滑零均值解。对非零 $k$，选择 $|k_j|\ge|k|/\sqrt2$，沿该方向分部积分 $m+4$ 次。因环面测度归一化，得到

$$|\widehat F(k)|
\le (2\pi |k_j|)^{-(m+4)}\|\partial_{y_j}^{m+4}F\|_{L^1}
\le B_m\langle k\rangle^{-(m+4)}\|F\|_{C^{m+4}},$$

其中 $B_m$ 有限且不依赖 $F,k$；最后一步使用非零整频率满足 $|k|\ge1$。若 $\beta$ 为任意总阶数至多 $m$ 的多重指标，由第 6 节的小除数界，解的 $\beta$ 阶导数级数的第 $k$ 项绝对值至多为

$$B'_m\langle k\rangle^{m+1}|\widehat F(k)|
\le B''_m\langle k\rangle^{-3}\|F\|_{C^{m+4}}.$$

二维可和性可以直接核对：$|k|_\infty=n$ 的整点恰有 $8n$ 个，且 $\langle k\rangle\ge n$，所以

$$\sum_{k\ne0}\langle k\rangle^{-3}\le8\sum_{n\ge1}n^{-2}<\infty.$$

于是对导数级数逐项取绝对值、对 $y$ 取上确界，再对有限个 $|\beta|\le m$ 取最大值，得到所求

$$\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}.$$

本题没有要求 $C_m$ 最优，也没有声称在 $C^m$ 范数中四阶损失最优。“最小损失为一阶”只针对题面精确定义的 Sobolev 估计。更强而合法的 $C^m$ 估计若蕴含题面结论，应接受。

## 8. 评分与来源边界

最小完成要求是：准确刻画一般无理方向的光滑可解性及全部 Sobolev 损失，证明两向并给出实际逆或合法不可解论证，完成固定方向的最小损失与四阶 $C^m$ 估计。闭图定理与光滑 Fréchet 空间的连续性等工具如被正确使用，也可以替代第 4 节的显式构造；不强制候选复刻作者路线。

已有五阶输入估计不能仅凭 $\|F\|_{C^{m+4}}\le\|F\|_{C^{m+5}}$ 反推出四阶输入估计；该范数序方向只给出反向的弱化。但本稿已经独立证明四阶估计成立。因此估计阶数不一致不构成原估计为假的证据，更不构成整个 Navier–Stokes 主定理为假的证据。

取材自公开论文的环面辅助输运逆及其公开形式化差异，来源、固定版本和改编边界见 source-notes.md。一般无理方向分类、不可解光滑右端和精确 Sobolev 阈值是本题独立扩展；它们没有被当作原论文或其 Lean 文件已经完成的内容。

本稿为 AI 作者自查版本，独立数学审核与人工审核均未完成；没有候选模型试跑。未提供本题的 Lean 形式化，也未在本次任务编译或重新认证外部 Navier–Stokes Lean 项目。全文的 Fourier 分析、光滑不可解构造及估计证明目前只具有本文的数学论证证据。
