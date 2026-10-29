# Fourier 逆、截断误差与参数边界：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 有限频带上的逆

判定：construction。

Fourier 模 e_k 的乘子为 2πi(αk_1+k_2)，无理性使每个非零频率乘子非零，故逐系数除法给唯一逆。H^r 中各模正交且权重在输入输出相同，逆范数为 max_{0<|k|≤N}1/(2π|αk_1+k_2|)，由单频模取得。空间有限维保证该最大值有限；未给 N 一致界。

判准：实际逆与单频最优常数；固定 N 的有限性。

## S2 有算术界的截断误差

判定：true。

逐系数设 û(k)=F̂(k)/(2πid(k))，零系数为零。多项式增长的逆乘子保持快速衰减，所以各阶导数级数绝对一致收敛，给光滑解。尾部 |k|>N 时 ⟨k⟩^{-q}≤(1+N²)^{-q/2}，逐项平方估计 ⟨k⟩^{2r}|û(k)|²≤(2πc)^{-2}(1+N²)^{-q}⟨k⟩^{2(r+s+q)}|F̂(k)|²，求和开平方即得。q=0 也成立；唯一性用非零频率乘子及零均值。

判准：光滑级数真正收敛；尾范数定量。

## S3 固定频带内改变方向

判定：true。

两个逆乘子的差为 (β−α)k_1/[2πi d_α(k)d_β(k)]，绝对值≤|α−β|N/(2πδ²)。H^r 正交求和给估计，任意实 r 均同样成立。该式的 δ 与 N 是固定频带信息，不能无证选成全频率、全参数的一致常数。

判准：逐模差的正确分母；与 r 无关的估计。

## S4 整体对象与全部恢复目标

判定：true。

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

判准：Characterize exactly which irrational alpha make N_alpha surjective on smooth complex zero-mean functions, and justify uniqueness and both directions of the characterization. A finite polynomial small-divisor lower bound, the equivalent rational-approximation condition, or an equivalent correctly proved formulation is sufficient.；Determine all nonnegative Sobolev losses s under the stated quantifiers, including an exact criterion at the endpoint. Establish both sufficiency and necessity; a one-sided sufficient bound is incomplete.；For alpha=sqrt(2)-1, prove that the smallest Sobolev loss is 1 and is attained, with a valid obstruction for every smaller nonnegative loss.；Prove the requested C^(m+4)-to-C^m estimate for every nonnegative integer m, with a finite constant independent of the smooth forcing. A stronger valid estimate that implies this bound is also accepted.。

## S5 邻近方向的一致估计

判定：false。

否。任一 J 含有理数 p/q，q>0。取 k=(q,−p) 固定，以及 J 内无理 α_n→p/q。单频 u=e_k 给所需常数下界 1/[2π⟨k⟩^s|qα_n−p|]→∞，与固定 C 矛盾。此反例中每个参数仍无理，固定 α_* 的正确估计没有问题；失效的是参数间的共同常数。

判准：对任意候选 J、s、C 反驳统一估计；接受任何有效反例；精确量词反驳。

## S6 一个具体方向的不可解数据

判定：construction。

十进展开在充分大位有越来越长的零段及无穷多个非零位，不最终周期，故 α 无理。令 q_n=10^{n!}，p_n/q_n 为前 n 项和，则 0<|q_nα−p_n|<2q_n^{−n}，且 p_n/q_n 有界，所以 k_n=(q_n,−p_n) 的长度与 q_n 可比。递归抽子列 l_j，使 |l_j|≥2^j 且 |d_α(l_j)|≤⟨l_j⟩^{−2j}（取 n 远大于 2j 可吸收固定比较常数）。令 F=Σ_j⟨l_j⟩^{−j}e_{l_j}。每个 m 阶导数尾部被常数 Σ_j2^{j(m−j)} 控制，可和，故 F 光滑且零均值。任何解在 l_j 处系数绝对值≥(2π)^{-1}⟨l_j⟩^j，无界，违背连续函数 Fourier 系数被 L¹ 范数界住。频率不同，故不存在系数抵消。

判准：无理性和超多项式逼近；全部导数收敛；同一右端的不可解性。
