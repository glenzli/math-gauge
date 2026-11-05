{}
# Fourier 逆、截断误差与参数边界

---

## S1 有限频带上的逆

### 1. 算子在基底上的作用与可逆性
在归一化环面 $\mathbb T^2 = \mathbb R^2 / \mathbb Z^2$ 上，标准 Fourier 基底为
$$e_k(y) = e^{2\pi i k \cdot y} \qquad (k = (k_1, k_2) \in \mathbb Z^2).$$
对 $e_k$ 作用微分算子 $N_\alpha = \alpha \partial_1 + \partial_2$ 得：
$$N_\alpha e_k(y) = \alpha (2\pi i k_1) e_k(y) + (2\pi i k_2) e_k(y) = 2\pi i (\alpha k_1 + k_2) e_k(y).$$
空间 $H_N$ 定义为
$$H_N = \operatorname{span}_{\mathbb C}\left\{ e_k : k \in \mathbb Z^2,\ 0 < |k| \le N \right\}.$$
因为 $\alpha \in \mathbb R \setminus \mathbb Q$ 是无理数，对任意非零整数向量 $k = (k_1, k_2) \ne (0,0)$：
- 若 $k_1 = 0$，则 $k_2 \ne 0$，故 $\alpha k_1 + k_2 = k_2 \ne 0$；
- 若 $k_1 \ne 0$，由于 $\alpha$ 为无理数，$k_2/k_1$ 为有理数，故 $\alpha k_1 + k_2 = k_1 (\alpha + k_2/k_1) \ne 0$。

从而特征值 $\lambda_k = 2\pi i (\alpha k_1 + k_2) \ne 0$ 对所有满足 $0 < |k| \le N$ 的频率 $k$ 恒成立。由于 $H_N$ 为有限维复线性空间且各基底向量 $e_k$ 为 $N_\alpha$ 的互不相同非零特征值的特征向量，$N_\alpha$ 在 $H_N$ 上的限制为双射。

### 2. 逆算子构造
对任意 $F \in H_N$，$F(y) = \sum_{0 < |k| \le N} \widehat{F}(k) e^{2\pi i k \cdot y}$，其在 $H_N$ 上的唯一逆象为
$$N_\alpha^{-1} F(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y}.$$

### 3. $H^r \to H^r$ 逆范数精确式
对于任意实数 $r \in \mathbb R$，空间 $H_N$ 上的 $H^r$ 范数为
$$\|F\|_{H^r}^2 = \sum_{0 < |k| \le N} \langle k \rangle^{2r} |\widehat{F}(k)|^2, \qquad \langle k \rangle = (1+|k|^2)^{1/2}.$$
因此
$$\|N_\alpha^{-1} F\|_{H^r}^2 = \sum_{0 < |k| \le N} \langle k \rangle^{2r} \frac{|\widehat{F}(k)|^2}{4\pi^2 |\alpha k_1 + k_2|^2} \le \left(\max_{0 < |k| \le N} \frac{1}{2\pi |\alpha k_1 + k_2|}\right)^2 \|F\|_{H^r}^2.$$
由于有限集 $\{k \in \mathbb Z^2 : 0 < |k| \le N\}$ 上的最小值可以取到，记
$$k^* \in \mathop{\operatorname{argmin}}_{0 < |k| \le N} |\alpha k_1 + k_2|.$$
取测试函数 $F^*(y) = e^{2\pi i k^* \cdot y} \in H_N$，显然 $\|F^*\|_{H^r} = \langle k^* \rangle^r$，且
$$\|N_\alpha^{-1} F^*\|_{H^r} = \frac{\langle k^* \rangle^r}{2\pi |\alpha k_1^* + k_2^*|} = \left(\frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|}\right) \|F^*\|_{H^r}.$$
因此，对任意实数 $r \in \mathbb R$，$H^r \to H^r$ 的算子逆范数精确式为：
$$\|N_\alpha^{-1}\|_{\mathcal L(H^r \cap H_N, H^r \cap H_N)} = \frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|}.$$

---

## S2 有算术界的截断误差

### 1. 光滑解 $u$ 的构造与正则性验证
给定 $F \in C^\infty_0(\mathbb T^2)$，其均值为零：$\widehat{F}(0) = \int_{\mathbb T^2} F = 0$。由光滑性，$F$ 的 Fourier 系数急速衰减：对任意 $M \ge 0$，存在常数 $A_M < \infty$ 使得
$$|\widehat{F}(k)| \le A_M \langle k \rangle^{-M} \qquad (\forall k \in \mathbb Z^2).$$
形式定义
$$u(y) = \sum_{k \in \mathbb Z^2 \setminus \{0\}} \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y}.$$
已知算术下界条件：$|\alpha k_1 + k_2| \ge c \langle k \rangle^{-s}$（$c > 0, s \ge 0$），故
$$|\widehat{u}(k)| = \frac{|\widehat{F}(k)|}{2\pi |\alpha k_1 + k_2|} \le \frac{1}{2\pi c} \langle k \rangle^s |\widehat{F}(k)|.$$
对任意多重指标 $\beta = (\beta_1, \beta_2) \in \mathbb N_0^2$，取 $M = |\beta| + s + 3$，则
$$\left| \partial^\beta \left( \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y} \right) \right| \le (2\pi)^{|\beta|} \langle k \rangle^{|\beta|} |\widehat{u}(k)| \le \frac{(2\pi)^{|\beta|-1}}{c} \langle k \rangle^{|\beta|+s} |\widehat{F}(k)| \le \frac{(2\pi)^{|\beta|-1} A_M}{c} \langle k \rangle^{-3}.$$
由于 $\sum_{k \in \mathbb Z^2} \langle k \rangle^{-3} < \infty$，由 Weierstrass M 判别法，导数级数在 $\mathbb T^2$ 上绝对且一致收敛。因此 $u \in C^\infty(\mathbb T^2)$。同时 $\widehat{u}(0) = 0 \implies \int_{\mathbb T^2} u = 0$，即 $u \in C_0^\infty(\mathbb T^2)$。逐项微分立得 $N_\alpha u = F$。

### 2. 截断误差估计的证明
频带截断解为
$$u_N(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y}.$$
两者的误差为高频尾项：
$$u(y) - u_N(y) = \sum_{|k| > N} \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y}.$$
计算其在 $H^r$ 范数下的值：
$$\|u - u_N\|_{H^r}^2 = \sum_{|k| > N} \langle k \rangle^{2r} \frac{|\widehat{F}(k)|^2}{4\pi^2 |\alpha k_1 + k_2|^2} \le \frac{1}{4\pi^2 c^2} \sum_{|k| > N} \langle k \rangle^{2r + 2s} |\widehat{F}(k)|^2.$$
对满足 $|k| > N$ 的整频率 $k$，其 Euclidean 模长满足 $|k|^2 \ge N^2$（由于 $k \in \mathbb Z^2$，若 $N \in \mathbb N$ 则 $|k|^2 \ge N^2 + 1$；一般而言 $|k| > N \implies 1+|k|^2 \ge 1+N^2$），从而
$$\langle k \rangle^2 = 1 + |k|^2 \ge 1 + N^2.$$
对于任意给定的 $q \ge 0$，有
$$\langle k \rangle^{-2q} \le (1+N^2)^{-q}.$$
将此不等式拆入权因子中：
$$\langle k \rangle^{2r + 2s} = \langle k \rangle^{-2q} \langle k \rangle^{2(r+s+q)} \le (1+N^2)^{-q} \langle k \rangle^{2(r+s+q)}.$$
代入求和式得到：
$$\|u - u_N\|_{H^r}^2 \le \frac{1}{4\pi^2 c^2} (1+N^2)^{-q} \sum_{|k| > N} \langle k \rangle^{2(r+s+q)} |\widehat{F}(k)|^2 \le (2\pi c)^{-2} (1+N^2)^{-q} \|F\|_{H^{r+s+q}}^2.$$
开平方即得所证不等式：
$$\|u - u_N\|_{H^r} \le (2\pi c)^{-1} (1 + N^2)^{-q/2} \|F\|_{H^{r+s+q}}.$$

---

## S3 固定频带内改变方向

### 1. 对应解的差项展开
设 $F \in H_N$，其 Fourier 展开仅含 $0 < |k| \le N$ 的项。由 S1，对应的解分别为
$$u_\alpha(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y}, \qquad u_\beta(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i (\beta k_1 + k_2)} e^{2\pi i k \cdot y}.$$
作差可得：
$$u_\alpha(y) - u_\beta(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i} \left( \frac{1}{\alpha k_1 + k_2} - \frac{1}{\beta k_1 + k_2} \right) e^{2\pi i k \cdot y}.$$
计算括号中的代数式：
$$\frac{1}{\alpha k_1 + k_2} - \frac{1}{\beta k_1 + k_2} = \frac{(\beta k_1 + k_2) - (\alpha k_1 + k_2)}{(\alpha k_1 + k_2)(\beta k_1 + k_2)} = \frac{(\beta - \alpha) k_1}{(\alpha k_1 + k_2)(\beta k_1 + k_2)}.$$

### 2. 逐点频率与范数估计
在频带 $0 < |k| \le N$ 内：
1. 分子中的整频率满足 $|k_1| \le \sqrt{k_1^2 + k_2^2} = |k| \le N$；
2. 分母满足小除数下界假设：$|\alpha k_1 + k_2| \ge \delta$ 且 $|\beta k_1 + k_2| \ge \delta$。

因此，乘子在每个模上的绝对值满足：
$$\left| \frac{1}{2\pi i} \left( \frac{1}{\alpha k_1 + k_2} - \frac{1}{\beta k_1 + k_2} \right) \right| = \frac{|\alpha - \beta| |k_1|}{2\pi |\alpha k_1 + k_2| |\beta k_1 + k_2|} \le \frac{|\alpha - \beta| N}{2\pi \delta^2}.$$
代入 $H^r$ 范数计算式：
$$\begin{aligned}
\|u_\alpha - u_\beta\|_{H^r}^2 &= \sum_{0 < |k| \le N} \langle k \rangle^{2r} \left| \frac{\widehat{F}(k)}{2\pi i} \left( \frac{1}{\alpha k_1 + k_2} - \frac{1}{\beta k_1 + k_2} \right) \right|^2 \\
&\le \left( \frac{|\alpha - \beta| N}{2\pi \delta^2} \right)^2 \sum_{0 < |k| \le N} \langle k \rangle^{2r} |\widehat{F}(k)|^2 = \left( \frac{|\alpha - \beta| N}{2\pi \delta^2} \right)^2 \|F\|_{H^r}^2.
\end{aligned}$$
两端开平方即证：
$$\|u_\alpha - u_\beta\|_{H^r} \le |\alpha - \beta| N (2\pi \delta^2)^{-1} \|F\|_{H^r}.$$

---

## S4 整体对象与全部恢复目标

### 1. 刻画可逆的 $\alpha$ 类（光滑零均值解的存在唯一性）
**结论**：$N_\alpha: C_0^\infty(\mathbb T^2) \to C_0^\infty(\mathbb T^2)$ 为双射当且仅当 $\alpha$ 为 **Diophantine 数**（即非 Liouville 数，无理性测度 $\mu(\alpha) < \infty$）。等价地，存在常数 $c > 0, \tau \ge 1$ 使得
$$|\alpha k_1 + k_2| \ge c \langle k \rangle^{-\tau} \qquad (\forall k \in \mathbb Z^2 \setminus \{0\}).$$

**证明**：
- **唯一性**：对任意无理数 $\alpha$，若 $u \in C_0^\infty(\mathbb T^2)$ 满足 $N_\alpha u = 0$，则其 Fourier 系数满足 $2\pi i (\alpha k_1 + k_2) \widehat{u}(k) = 0$。由 $\alpha \notin \mathbb Q$，当 $k \ne 0$ 时 $\alpha k_1 + k_2 \ne 0$，故 $\widehat{u}(k) = 0$。又因 $u$ 零均值，$\widehat{u}(0) = 0$。由 Fourier 级数惟一性，$u \equiv 0$。
- **充分性**：若 $\alpha$ 为 Diophantine 数，则对任意 $F \in C_0^\infty(\mathbb T^2)$，形式解系数满足 $|\widehat{u}(k)| \le \frac{1}{2\pi c} \langle k \rangle^\tau |\widehat{F}(k)|$。由 $F$ 的光滑性，$|\widehat{F}(k)|$ 衰减快于任意多项式反比，从而 $|\widehat{u}(k)|$ 亦快于任意多项式反比衰减。由标准 Fourier 逆变换理论，$u(y) = \sum_{k \ne 0} \widehat{u}(k) e^{2\pi i k \cdot y} \in C_0^\infty(\mathbb T^2)$，且 $N_\alpha u = F$。
- **必要性**：若 $\alpha$ 不是 Diophantine 数（即为 Liouville 数），则对任意 $M \in \mathbb N$，$\inf_{k \ne 0} \langle k \rangle^M |\alpha k_1 + k_2| = 0$。由此可选出一列频率 $k^{(j)} \in \mathbb Z^2 \setminus \{0\}$，满足 $\langle k^{(j+1)} \rangle > 2 \langle k^{(j)} \rangle$ 且
$$|\alpha k_1^{(j)} + k_2^{(j)}| \le \langle k^{(j)} \rangle^{-j}.$$
构造 $F(y) = \sum_{j=1}^\infty \langle k^{(j)} \rangle^{-j/2} e^{2\pi i k^{(j)} \cdot y}$。对于任意固定 $p > 0$，当 $j \ge 2p$ 时 $\langle k^{(j)} \rangle^p |\widehat{F}(k^{(j)})| \le 1$，故 $F \in C_0^\infty(\mathbb T^2)$。但形式解的 Fourier 系数满足
$$|\widehat{u}(k^{(j)})| = \frac{\langle k^{(j)} \rangle^{-j/2}}{2\pi |\alpha k_1^{(j)} + k_2^{(j)}|} \ge \frac{1}{2\pi} \langle k^{(j)} \rangle^{j/2} \to +\infty \quad (j \to \infty).$$
由 Riemann-Lebesgue 引理，任何 $C^0(\mathbb T^2)$ 函数（特别是光滑函数）的 Fourier 系数必须有界，矛盾！故此时不存在光滑解。

### 2. 确定允许的损失指标集合 $\{s \ge 0\}$
**结论**：对固定的无理数 $\alpha$ 及 $s \ge 0$，存在与 $u$ 无关的有限常数 $C_{\alpha, r, s}$ 使得
$$\|u\|_{H^r} \le C_{\alpha, r, s} \|N_\alpha u\|_{H^{r+s}} \qquad (\forall u \in C_0^\infty(\mathbb T^2))$$
当且仅当
$$\exists c > 0 \quad \text{使得} \quad |\alpha k_1 + k_2| \ge c \langle k \rangle^{-s} \qquad (\forall k \in \mathbb Z^2 \setminus \{0\}).$$
**证明**：
- **充分性**：若上述算术下界成立，由 Parseval 定理：
$$\|u\|_{H^r}^2 = \sum_{k \ne 0} \langle k \rangle^{2r} \frac{|\widehat{N_\alpha u}(k)|^2}{4\pi^2 |\alpha k_1 + k_2|^2} \le \frac{1}{4\pi^2 c^2} \sum_{k \ne 0} \langle k \rangle^{2(r+s)} |\widehat{N_\alpha u}(k)|^2 = \frac{1}{4\pi^2 c^2} \|N_\alpha u\|_{H^{r+s}}^2,$$
取 $C_{\alpha, r, s} = \frac{1}{2\pi c} < \infty$ 即可。
- **必要性**：对每个单一频率 $k \ne 0$，取 $u_k(y) = e^{2\pi i k \cdot y} \in C_0^\infty(\mathbb T^2)$。此时 $\|u_k\|_{H^r} = \langle k \rangle^r$，且 $\|N_\alpha u_k\|_{H^{r+s}} = 2\pi |\alpha k_1 + k_2| \langle k \rangle^{r+s}$。先验估计蕴含：
$$\langle k \rangle^r \le 2\pi C_{\alpha, r, s} |\alpha k_1 + k_2| \langle k \rangle^{r+s} \implies |\alpha k_1 + k_2| \ge \frac{1}{2\pi C_{\alpha, r, s}} \langle k \rangle^{-s}.$$
注：由 Dirichlet 逼近定理，对任何无理数 $\alpha$，必存在无穷多个 $k$ 使得 $|\alpha k_1 + k_2| < |k_1|^{-1}$，因此对任意无理数 $\alpha$，合法的损失指标必有 $s \ge 1$。具体地：
- 若 $\alpha$ 的无理性测度为 $\mu(\alpha) < \infty$，则对所有 $s > \mu(\alpha) - 1$，该估计恒成立；对所有 $s < \mu(\alpha) - 1$，该估计不成立；在端点 $s = \mu(\alpha) - 1$，成立当且仅当 $\liminf_{|k| \to \infty} \langle k \rangle^{\mu(\alpha)-1} |\alpha k_1 + k_2| > 0$。
- 若 $\alpha$ 为 Liouville 数，则合法的 $s$ 集合为空集 $\emptyset$。

### 3. $\alpha_* = \sqrt{2} - 1$ 的最小损失 $s_{\min}$ 及其可达性
**结论**：最小损失为 **$s = 1$**，且 **能够取到**。

**证明**：
$\alpha_* = \sqrt{2} - 1 = [0; 2, 2, 2, \dots] = [0; \overline{2}]$。其连分数展开的部分商全部为有限常数 $a_n = 2$。
由连分数经典理论，$\alpha_*$ 属于坏逼近数（badly approximable number）。对所有 $q \ge 1, p \in \mathbb Z$，有
$$|q \alpha_* - p| \ge \frac{1}{q_{n+1} + q_n} = \frac{1}{(a_{n+1} + 1) q_n + q_{n-1}} > \frac{1}{4q}.$$
对频率向量 $k = (k_1, k_2) \in \mathbb Z^2 \setminus \{0\}$：
1. 若 $k_1 = 0$，则 $|\alpha_* k_1 + k_2| = |k_2| \ge 1 \ge \langle k \rangle^{-1}$；
2. 若 $k_1 \ne 0$ 且 $|k_2| \ge 2 |k_1|$，则 $|\alpha_* k_1 + k_2| \ge |k_2| - \alpha_* |k_1| \ge |k_1| \ge 1 \ge \langle k \rangle^{-1}$；
3. 若 $k_1 \ne 0$ 且 $|k_2| < 2 |k_1|$，则 $\langle k \rangle = (1 + k_1^2 + k_2^2)^{1/2} \le \sqrt{6} |k_1|$，故
$$|\alpha_* k_1 + k_2| \ge \frac{1}{4 |k_1|} \ge \frac{\sqrt{6}}{4} \langle k \rangle^{-1}.$$
取 $c = \frac{\sqrt{6}}{4} > 0$，即有 $|\alpha_* k_1 + k_2| \ge c \langle k \rangle^{-1}$ 对所有非零频率成立。故 $s = 1$ 是允许的损失。

若 $s < 1$，取 $\alpha_*$ 的渐近分数序列 $p_n/q_n$，设 $k^{(n)} = (q_n, -p_n)$，则 $|q_n \alpha_* - p_n| \le \frac{1}{q_{n+1}} \le \frac{1}{2 q_n}$，故
$$\langle k^{(n)} \rangle^s |\alpha_* q_n - p_n| \le C q_n^s \frac{1}{q_n} = C q_n^{s-1} \to 0 \quad (n \to \infty).$$
因此对任意 $s < 1$ 都不存在正下界常数 $c$。故 $s_{\min} = 1$ 且在 $s = 1$ 处取到。

### 4. 连续可微模估计 $\|N_{\alpha_*}^{-1} F\|_{C^m} \le C_m \|F\|_{C^{m+4}}$
**结论**：**成立**。

**证明**：
令 $u = N_{\alpha_*}^{-1} F \in C_0^\infty(\mathbb T^2)$。对任意满足 $a+b \le m$ 的导数，
$$\partial_{y_1}^a \partial_{y_2}^b u(y) = \sum_{k \ne 0} (2\pi i k_1)^a (2\pi i k_2)^b \frac{\widehat{F}(k)}{2\pi i (\alpha_* k_1 + k_2)} e^{2\pi i k \cdot y}.$$
利用 $s = 1$ 时的下界 $|\alpha_* k_1 + k_2| \ge c \langle k \rangle^{-1}$：
$$\|\partial_{y_1}^a \partial_{y_2}^b u\|_{C^0} \le \sum_{k \ne 0} (2\pi)^{m-1} \langle k \rangle^m \frac{|\widehat{F}(k)|}{|\alpha_* k_1 + k_2|} \le \frac{(2\pi)^{m-1}}{c} \sum_{k \ne 0} \langle k \rangle^{m+1} |\widehat{F}(k)|.$$
另一方面，通过分部积分，对任意非零 $k$，
$$(2\pi i k_1)^{m+4} \widehat{F}(k) = \int_{\mathbb T^2} \partial_{y_1}^{m+4} F(y) e^{-2\pi i k \cdot y} dy \implies |2\pi k_1|^{m+4} |\widehat{F}(k)| \le \|\partial_{y_1}^{m+4} F\|_{C^0} \le \|F\|_{C^{m+4}},$$
$$(2\pi i k_2)^{m+4} \widehat{F}(k) = \int_{\mathbb T^2} \partial_{y_2}^{m+4} F(y) e^{-2\pi i k \cdot y} dy \implies |2\pi k_2|^{m+4} |\widehat{F}(k)| \le \|\partial_{y_2}^{m+4} F\|_{C^0} \le \|F\|_{C^{m+4}}.$$
由初等不等式 $\langle k \rangle^{m+4} \le A_m (|k_1|^{m+4} + |k_2|^{m+4})$ 对 $k \in \mathbb Z^2 \setminus \{0\}$ 成立，存在有限常数 $K_m$ 满足：
$$|\widehat{F}(k)| \le K_m \langle k \rangle^{-(m+4)} \|F\|_{C^{m+4}}.$$
将此式代入前述导数和式中：
$$\sum_{k \ne 0} \langle k \rangle^{m+1} |\widehat{F}(k)| \le K_m \|F\|_{C^{m+4}} \sum_{k \ne 0} \langle k \rangle^{m+1 - (m+4)} = K_m \|F\|_{C^{m+4}} \sum_{k \ne 0} \langle k \rangle^{-3}.$$
在二维环面上，$\sum_{k \ne 0} \langle k \rangle^{-3} \le \sum_{R=1}^\infty (8R) R^{-3} = 8 \sum_{R=1}^\infty R^{-2} < \infty$。
记 $S = \sum_{k \ne 0} \langle k \rangle^{-3} < \infty$，则对所有 $a+b \le m$：
$$\sup_{y \in \mathbb T^2} |\partial_{y_1}^a \partial_{y_2}^b u(y)| \le \frac{(2\pi)^{m-1} K_m S}{c} \|F\|_{C^{m+4}}.$$
取有限常数 $C_m = \frac{(2\pi)^{m-1} K_m S}{c}$，即证：
$$\|N_{\alpha_*}^{-1} F\|_{C^m} \le C_m \|F\|_{C^{m+4}} \qquad (\forall F \in C_0^\infty(\mathbb T^2)).$$

---

## S5 邻近方向的一致估计

### 1. 结论
**不存在** 满足要求的开区间 $J \ni \alpha_*$、有限 $s \ge 0$ 及常数 $C < \infty$。

### 2. 完整证明（反证法）
反设存在开区间 $J \ni \alpha_*$、有限 $s \ge 0$ 及 $C < \infty$，使得对所有无理数 $\alpha \in J$ 及所有 $u \in C_0^\infty(\mathbb T^2)$，均有
$$\|u\|_{L^2} \le C \|N_\alpha u\|_{H^s}.$$

**步骤 1：频率模测试**
对任意固定非零整频率 $k = (k_1, k_2) \in \mathbb Z^2 \setminus \{0\}$，选取单模函数
$$u_k(y) = e^{2\pi i k \cdot y}.$$
显然 $u_k \in C_0^\infty(\mathbb T^2)$，其模长满足 $\|u_k\|_{L^2} = 1$。
由于 $N_\alpha u_k(y) = 2\pi i (\alpha k_1 + k_2) e^{2\pi i k \cdot y}$，其 Sobolev 范数为
$$\|N_\alpha u_k\|_{H^s} = 2\pi |\alpha k_1 + k_2| \langle k \rangle^s.$$
代入假设的不等式即得：
$$1 \le 2\pi C |\alpha k_1 + k_2| \langle k \rangle^s \iff |\alpha k_1 + k_2| \ge \frac{1}{2\pi C} \langle k \rangle^{-s},$$
此不等式必须对区间 $J$ 内的 **每一个** 无理数 $\alpha$ 及 **每一个** 非零频率 $k$ 均成立。

**步骤 2：构造邻近有理点的反例方向**
由于 $J \subset \mathbb R$ 为包含 $\alpha_*$ 的开区间，有理数集 $\mathbb Q$ 在 $J$ 中稠密。
在 $J$ 中任取一个有理数 $p/q \in J$，其中 $q \in \mathbb N, p \in \mathbb Z$。
因为 $J$ 为开集，存在 $\varepsilon_0 > 0$ 使得开邻域 $[p/q - \varepsilon_0, p/q + \varepsilon_0] \subset J$。
固定整频率向量为
$$k^* = (q, -p) \in \mathbb Z^2 \setminus \{0\}.$$
此时 $\langle k^* \rangle = (1 + q^2 + p^2)^{1/2}$ 为一固定的有限正数。
考虑微扰参数 $\varepsilon > 0$，定义方向：
$$\alpha_\varepsilon = \frac{p}{q} + \frac{\varepsilon}{\sqrt{2}}.$$
只要 $0 < \varepsilon < \varepsilon_0 \sqrt{2}$，便有 $\alpha_\varepsilon \in J$；且由于 $\sqrt{2}$ 是无理数，$\alpha_\varepsilon$ 必为无理数。
在此方向下计算小除数：
$$\alpha_\varepsilon k_1^* + k_2^* = \left(\frac{p}{q} + \frac{\varepsilon}{\sqrt{2}}\right) q - p = \frac{q \varepsilon}{\sqrt{2}}.$$
现在选取满足下列条件的 $\varepsilon$：
$$0 < \varepsilon < \min\left\{ \varepsilon_0 \sqrt{2}, \ \frac{\sqrt{2}}{4\pi C q \langle k^* \rangle^s} \right\}.$$
对于此无理数 $\alpha_\varepsilon \in J$，小除数满足：
$$|\alpha_\varepsilon k_1^* + k_2^*| = \frac{q \varepsilon}{\sqrt{2}} < \frac{1}{4\pi C \langle k^* \rangle^s} < \frac{1}{2\pi C} \langle k^* \rangle^{-s}.$$
这直接违背了步骤 1 中必须成立的必要条件！
此外，任意开区间 $J$ 中均包含不可数个 Liouville 数，对于任意单个 Liouville 数方向，均不存在有限的 $(C, s)$ 使得该先验估计成立。因此该一致估计在任何开区间上均不可能成立。

---

## S6 一个具体方向的不可解数据

### 1. 证明 $\alpha = \sum_{n=1}^\infty 10^{-n!}$ 是无理数
对每个正整数 $m \ge 1$，令
$$q_m = 10^{m!}, \qquad p_m = \sum_{n=1}^m 10^{m! - n!} \in \mathbb Z.$$
显然 $q_m \in \mathbb N, p_m \in \mathbb Z$，且有理数逼近项为
$$\frac{p_m}{q_m} = \sum_{n=1}^m 10^{-n!}.$$
考察尾项级数：
$$0 < \alpha - \frac{p_m}{q_m} = \sum_{n=m+1}^\infty 10^{-n!} = 10^{-(m+1)!} \left( 1 + \sum_{n=m+2}^\infty 10^{-(n! - (m+1)!)} \right).$$
由于对 $n \ge m+2$ 有 $n! - (m+1)! \ge (m+2)! - (m+1)! = (m+1) \cdot (m+1)! \ge 2(n - m - 1)$，故公比小于 $1/10$：
$$0 < \alpha - \frac{p_m}{q_m} < 10^{-(m+1)!} \sum_{j=0}^\infty 10^{-j} = \frac{10}{9} 10^{-(m+1)!}.$$
由于 $(m+1)! = (m+1) m! = m \cdot m! + m!$，可得
$$10^{-(m+1)!} = 10^{-m \cdot m!} \cdot 10^{-m!} = q_m^{-(m+1)}.$$
特别地，当 $m \ge 2$ 时，$q_m \ge 100$，故 $0 < \alpha - \frac{p_m}{q_m} < \frac{10}{9} q_m^{-(m+1)} < q_m^{-m}$。

假设 $\alpha$ 为有理数，设 $\alpha = a/b$（$a \in \mathbb Z, b \in \mathbb N$）。
由于 $\alpha - p_m/q_m > 0$，对所有 $m$ 均有 $\alpha \ne p_m/q_m$。因此：
$$\left| \alpha - \frac{p_m}{q_m} \right| = \left| \frac{a}{b} - \frac{p_m}{q_m} \right| = \frac{|a q_m - b p_m|}{b q_m} \ge \frac{1}{b q_m}.$$
但根据上面的上界，当 $m$ 充分大使得 $q_m^{m-1} > \frac{10}{9} b$ 时（由于 $q_m \to \infty$ 且 $m \ge 2$，此式显然成立）：
$$\alpha - \frac{p_m}{q_m} < \frac{10}{9} q_m^{-(m+1)} = \frac{10}{9 q_m^{m-1}} \frac{1}{q_m^2} < \frac{1}{b q_m},$$
产生矛盾！故 $\alpha$ 必为无理数（且为 Liouville 超越数）。

### 2. 构造同一个光滑零均值数据 $F$
取整频率序列：
$$k^{(m)} = (q_m, -p_m) \in \mathbb Z^2 \qquad (m \ge 2).$$
因为 $q_m = 10^{m!} \ge 100$，且 $q_m < q_{m+1}$，所有频点 $k^{(m)}$ 均非零且两两互异。
由于 $p_m/q_m < 1$，欧氏范数满足：
$$q_m \le |k^{(m)}| = \sqrt{q_m^2 + p_m^2} \le \sqrt{2} q_m.$$
在各频点处的小除数绝对值为：
$$|\alpha k_1^{(m)} + k_2^{(m)}| = |\alpha q_m - p_m| = q_m \left(\alpha - \frac{p_m}{q_m}\right).$$
结合上式的严格上下界，有
$$10^{-m \cdot m!} < |\alpha q_m - p_m| < \frac{10}{9} 10^{-m \cdot m!}.$$
定义单一的光滑零均值函数 $F \in C_0^\infty(\mathbb T^2)$，其 Fourier 系数设定为：
$$\widehat{F}(k) = \begin{cases}
10^{-\frac{1}{2} m \cdot m!}, & k = k^{(m)} \quad (m \ge 2), \\
0, & \text{其他 } k \in \mathbb Z^2.
\end{cases}$$
即：
$$F(y) = \sum_{m=2}^\infty 10^{-\frac{1}{2} m \cdot m!} e^{2\pi i (q_m y_1 - p_m y_2)}.$$

### 3. 性质与无解性证明
1. **零均值**：各 $k^{(m)} \ne (0,0)$，故 $\int_{\mathbb T^2} F(y) dy = \widehat{F}(0) = 0$。
2. **光滑性**：对任意阶导数指标 $\beta = (a, b) \in \mathbb N_0^2$（记 $|\beta| = a+b$）：
$$\left| \partial^\beta \left( \widehat{F}(k^{(m)}) e^{2\pi i k^{(m)} \cdot y} \right) \right| \le (2\pi)^{|\beta|} q_m^{|\beta|} 10^{-\frac{1}{2} m \cdot m!} = (2\pi)^{|\beta|} 10^{|\beta| m! - \frac{1}{2} m \cdot m!} = (2\pi)^{|\beta|} 10^{-\left(\frac{m}{2} - |\beta|\right) m!}.$$
当 $m \ge 2|\beta| + 2$ 时，指数满足 $\left(\frac{m}{2} - |\beta|\right) m! \ge m! \ge 2^m$。由 Weierstrass M 判别法，导数级数在 $\mathbb T^2$ 上一致绝对收敛，因此 $F \in C_0^\infty(\mathbb T^2)$。
3. **不存在光滑零均值解**：
反设存在 $u \in C_0^\infty(\mathbb T^2)$ 满足 $N_\alpha u = F$。
两边取 Fourier 系数，对任意 $k \in \mathbb Z^2$ 均有：
$$2\pi i (\alpha k_1 + k_2) \widehat{u}(k) = \widehat{F}(k).$$
在选定的频率序列 $k = k^{(m)}$（$m \ge 2$）上，计算解的 Fourier 系数模长：
$$|\widehat{u}(k^{(m)})| = \frac{|\widehat{F}(k^{(m)})|}{2\pi |\alpha q_m - p_m|} > \frac{10^{-\frac{1}{2} m \cdot m!}}{2\pi \cdot \frac{10}{9} 10^{-m \cdot m!}} = \frac{9}{20\pi} 10^{\frac{1}{2} m \cdot m!}.$$
随着 $m \to \infty$：
$$|\widehat{u}(k^{(m)})| \ge \frac{9}{20\pi} 10^{\frac{1}{2} m \cdot m!} \to +\infty.$$
然而，任何连续函数 $u \in C^0(\mathbb T^2)$ 的 Fourier 系数必须一致有界：
$$|\widehat{u}(k)| = \left| \int_{\mathbb T^2} u(y) e^{-2\pi i k \cdot y} dy \right| \le \int_{\mathbb T^2} |u(y)| dy \le \|u\|_{C^0} < \infty.$$
这与 $|\widehat{u}(k^{(m)})| \to \infty$ 发生直接矛盾！
因此，$N_\alpha u = F$ 甚至没有任何连续解，更不可能存在光滑零均值解 $u \in C_0^\infty(\mathbb T^2)$。
