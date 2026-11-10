我将按 S1 至 S6 的顺序逐项给出完整的构造、分类、证明与反例。首先统一记号（与 S4 一致）：

在配备归一化 Haar 测度 $dy$（$\int_{\mathbb{T}^2} dy = 1$）的环面 $\mathbb{T}^2 = \mathbb{R}^2/\mathbb{Z}^2$ 上，记 $e_k(y) := e^{2\pi i k \cdot y}$（$k = (k_1, k_2) \in \mathbb{Z}^2$），$|k| = (k_1^2 + k_2^2)^{1/2}$，$\langle k \rangle = (1 + |k|^2)^{1/2}$。对 $u \in C^\infty(\mathbb{T}^2)$，Fourier 系数与逆变换为
$$\widehat{u}(k) = \int_{\mathbb{T}^2} u(y) e^{-2\pi i k \cdot y}\,dy, \qquad u(y) = \sum_{k \in \mathbb{Z}^2} \widehat{u}(k) e^{2\pi i k \cdot y}.$$
算子 $N_\alpha = \alpha \partial_{y_1} + \partial_{y_2}$ 在基函数 $e_k$ 上的作用为 $N_\alpha e_k = 2\pi i (\alpha k_1 + k_2) e_k$，对光滑函数分部积分有 $\widehat{N_\alpha u}(k) = 2\pi i (\alpha k_1 + k_2)\widehat{u}(k)$。

---

## S1 有限频带上的逆

### 1. 逆算子的构造
记非零有限整频带指标集为
$$\Lambda_N := \left\{ k = (k_1, k_2) \in \mathbb{Z}^2 : 0 < |k| \le N \right\} \qquad (N \ge 1).$$
由于 $N \ge 1$，$(\pm 1, 0), (0, \pm 1) \in \Lambda_N$，故 $\Lambda_N$ 非空且有限。空间 $H_N$ 为
$$H_N = \left\{ u(y) = \sum_{k \in \Lambda_N} \widehat{u}(k) e^{2\pi i k \cdot y} : \widehat{u}(k) \in \mathbb{C} \right\}.$$

**小除数非零性**：对任意 $k = (k_1, k_2) \in \Lambda_N$，因 $|k| > 0$，故 $(k_1, k_2) \ne (0,0)$。
- 若 $k_1 = 0$，则 $k_2 \ne 0$，从而 $\alpha k_1 + k_2 = k_2 \ne 0$；
- 若 $k_1 \ne 0$，因 $\alpha \in \mathbb{R}\setminus\mathbb{Q}$ 无理而 $-k_2/k_1 \in \mathbb{Q}$，必有 $\alpha k_1 + k_2 \ne 0$。

因此，对所有 $k \in \Lambda_N$，特征值 $\lambda_k(\alpha) := 2\pi i(\alpha k_1 + k_2) \ne 0$。

**逆的显式定义**：对任意 $F(y) = \sum_{k \in \Lambda_N} \widehat{F}(k) e^{2\pi i k \cdot y} \in H_N$，定义线性算子 $T_{\alpha,N} = (N_\alpha|_{H_N})^{-1}: H_N \to H_N$ 为
$$u_N(y) = (N_\alpha|_{H_N})^{-1} F(y) := \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y}.$$
由于求和是有限项，逐项求导立得对任意 $F, u \in H_N$：
$$N_\alpha \big((N_\alpha|_{H_N})^{-1} F\big) = \sum_{0 < |k| \le N} 2\pi i(\alpha k_1 + k_2)\frac{\widehat{F}(k)}{2\pi i(\alpha k_1 + k_2)} e^{2\pi i k\cdot y} = F, \qquad (N_\alpha|_{H_N})^{-1}(N_\alpha u) = u.$$
因此 $(N_\alpha|_{H_N})^{-1}$ 是 $N_\alpha$ 在 $H_N$ 上的双射逆算子。

### 2. $H^r \to H^r$ 逆范数精确式
对任意实数 $r \in \mathbb{R}$，逆算子的精确算子范数为（与 $r$ 无关）：
$$\left\| (N_\alpha|_{H_N})^{-1} \right\|_{H^r \to H^r} = \max_{0 < |k| \le N} \frac{1}{2\pi |\alpha k_1 + k_2|} = \frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|}.$$

**证明**：记 $M_{\alpha, N} := \max_{k \in \Lambda_N} (2\pi|\alpha k_1 + k_2|)^{-1}$。因为 $\Lambda_N$ 非空有限且每项 $|\alpha k_1 + k_2| > 0$，该最大值在某个 $k^* \in \Lambda_N$ 处取到且 $0 < M_{\alpha,N} < \infty$。
1. **上界**：对任意 $F \in H_N$，由 $H^r$ 范数定义，
   $$\left\| (N_\alpha|_{H_N})^{-1} F \right\|_{H^r}^2 = \sum_{k \in \Lambda_N} \langle k \rangle^{2r} \left| \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} \right|^2 \le M_{\alpha, N}^2 \sum_{k \in \Lambda_N} \langle k \rangle^{2r} |\widehat{F}(k)|^2 = M_{\alpha, N}^2 \|F\|_{H^r}^2.$$
   故 $\|(N_\alpha|_{H_N})^{-1}\|_{H^r \to H^r} \le M_{\alpha, N}$。
2. **可达性（下界）**：取非零函数 $F^*(y) = e^{2\pi i k^* \cdot y} \in H_N$，则 $\|F^*\|_{H^r} = \langle k^* \rangle^r > 0$，且
   $$\left\| (N_\alpha|_{H_N})^{-1} F^* \right\|_{H^r} = \frac{\langle k^* \rangle^r}{2\pi |\alpha k_1^* + k_2^*|} = M_{\alpha, N} \|F^*\|_{H^r}.$$
   故 $\|(N_\alpha|_{H_N})^{-1}\|_{H^r \to H^r} = M_{\alpha, N}$。$\blacksquare$

---

## S2 有算术界的截断误差

### 1. 光滑零均值解 $u$ 的构造与光滑性证明
首先，算术界 $|\alpha k_1 + k_2| \ge c \langle k \rangle^{-s} > 0$（$\forall k \in \mathbb{Z}^2 \setminus \{0\}$）蕴含 $\alpha \in \mathbb{R}\setminus\mathbb{Q}$（否则若 $\alpha = p/q \in \mathbb{Q}$，$q \ge 1$，取 $k = (q,-p) \ne 0$ 得 $\alpha k_1 + k_2 = 0$，矛盾）。

设 $F \in C^\infty_0(\mathbb{T}^2)$，则 $\widehat{F}(0) = \int_{\mathbb{T}^2} F(y)\,dy = 0$。对任意 $\sigma \in \mathbb{R}$，由 $F$ 的光滑性及分部积分，对任意整数 $M \ge 0$ 有
$$|k_1|^M |\widehat{F}(k)| = (2\pi)^{-M} \left|\widehat{\partial_{y_1}^M F}(k)\right| \le (2\pi)^{-M} \|\partial_{y_1}^M F\|_{C^0}, \qquad |k_2|^M |\widehat{F}(k)| \le (2\pi)^{-M} \|\partial_{y_2}^M F\|_{C^0},$$
故 $|\widehat{F}(k)|$ 关于 $\langle k \rangle$ 快速衰减，从而对一切 $\sigma \in \mathbb{R}$ 有 $\|F\|_{H^\sigma} < \infty$。

定义 $u$ 的 Fourier 系数为 $\widehat{u}(0) := 0$，且对 $k \in \mathbb{Z}^2 \setminus \{0\}$：
$$\widehat{u}(k) := \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)}, \qquad u(y) := \sum_{k \in \mathbb{Z}^2 \setminus \{0\}} \frac{\widehat{F}(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k \cdot y}.$$

**验证 $u \in C^\infty_0(\mathbb{T}^2)$ 且 $N_\alpha u = F$**：
- 由算术条件 $|\alpha k_1 + k_2| \ge c \langle k \rangle^{-s}$，对任意 $k \ne 0$ 有
  $$|\widehat{u}(k)| \le \frac{\langle k \rangle^s}{2\pi c} |\widehat{F}(k)|.$$
- 因此对任意 $r \in \mathbb{R}$，
  $$\|u\|_{H^r}^2 = \sum_{k \ne 0} \langle k \rangle^{2r} |\widehat{u}(k)|^2 \le \frac{1}{(2\pi c)^2} \sum_{k \ne 0} \langle k \rangle^{2(r+s)} |\widehat{F}(k)|^2 = \frac{1}{(2\pi c)^2} \|F\|_{H^{r+s}}^2 < \infty.$$
- 对任意非负整数 $a, b \ge 0$（记 $m = a+b$），级数形式求偏导 $\partial_{y_1}^a \partial_{y_2}^b$ 后的通项绝对值满足 $|(2\pi i k_1)^a(2\pi i k_2)^b \widehat{u}(k) e^{2\pi i k\cdot y}| \le (2\pi)^m \langle k \rangle^m |\widehat{u}(k)|$。在二维格点 $\mathbb{Z}^2$ 上级数 $S_2 := \sum_{k \ne 0} \langle k \rangle^{-4} < \infty$ 收敛，由 Cauchy-Schwarz 不等式，
  $$\sum_{k \ne 0} |(2\pi i k_1)^a (2\pi i k_2)^b \widehat{u}(k)| \le (2\pi)^m \left(\sum_{k \ne 0} \langle k \rangle^{-4}\right)^{1/2} \|u\|_{H^{m+2}} \le \frac{(2\pi)^{m-1} S_2^{1/2}}{c} \|F\|_{H^{m+s+2}} < \infty.$$
- 由 Weierstrass M-判别法，$u$ 的 Fourier 级数及其任意阶形式偏导数级数均在 $\mathbb{T}^2$ 上绝对且一致收敛。故 $u \in C^\infty(\mathbb{T}^2)$，可以逐项求导并逐项积分：
  $$\int_{\mathbb{T}^2} u(y)\,dy = \widehat{u}(0) = 0 \implies u \in C^\infty_0(\mathbb{T}^2),$$
  $$N_\alpha u(y) = \sum_{k \ne 0} 2\pi i(\alpha k_1 + k_2)\widehat{u}(k) e^{2\pi i k\cdot y} = \sum_{k \ne 0} \widehat{F}(k) e^{2\pi i k\cdot y} = F(y).$$

### 2. 截断误差估计的证明
对频带截断 $F_N(y) = \sum_{0 < |k| \le N} \widehat{F}(k) e^{2\pi i k\cdot y} \in H_N$，由 S1 知 $N_\alpha u_N = F_N$ 在 $H_N$ 中的解为
$$u_N(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i(\alpha k_1 + k_2)} e^{2\pi i k\cdot y}.$$
因此余项 $u - u_N$ 的 Fourier 展开仅含 $|k| > N$ 的频率：
$$u(y) - u_N(y) = \sum_{|k| > N} \frac{\widehat{F}(k)}{2\pi i(\alpha k_1 + k_2)} e^{2\pi i k\cdot y}.$$
对任意 $|k| > N$，有 $\langle k \rangle^2 = 1 + |k|^2 > 1 + N^2$。因为 $q \ge 0$，函数 $t \mapsto t^{-q}$ 在 $(0, \infty)$ 上单调非增，故对所有 $|k| > N$ 有
$$\langle k \rangle^{-2q} = (1 + |k|^2)^{-q} \le (1 + N^2)^{-q}.$$
结合算术界 $|\alpha k_1 + k_2| \ge c \langle k \rangle^{-s}$，对任意 $r \in \mathbb{R}$ 及 $q \ge 0$ 有
$$\begin{aligned}
\|u - u_N\|_{H^r}^2 &= \sum_{|k| > N} \langle k \rangle^{2r} \frac{|\widehat{F}(k)|^2}{4\pi^2 |\alpha k_1 + k_2|^2} \\
&\le \frac{1}{(2\pi c)^2} \sum_{|k| > N} \langle k \rangle^{2(r+s)} |\widehat{F}(k)|^2 \\
&= \frac{1}{(2\pi c)^2} \sum_{|k| > N} \langle k \rangle^{-2q} \langle k \rangle^{2(r+s+q)} |\widehat{F}(k)|^2 \\
&\le \frac{1}{(2\pi c)^2} (1 + N^2)^{-q} \sum_{|k| > N} \langle k \rangle^{2(r+s+q)} |\widehat{F}(k)|^2 \\
&\le \frac{1}{(2\pi c)^2} (1 + N^2)^{-q} \|F\|_{H^{r+s+q}}^2.
\end{aligned}$$
两边开方即得
$$\|u - u_N\|_{H^r} \le (2\pi c)^{-1} (1 + N^2)^{-q/2} \|F\|_{H^{r+s+q}}. \qquad \blacksquare$$

---

## S3 固定频带内改变方向

**证明**：设 $F \in H_N$。由 S1（适用条件：$\alpha, \beta \in \mathbb{R}\setminus\mathbb{Q}$ 且 $F \in H_N$），方程 $N_\alpha u_\alpha = F$ 与 $N_\beta u_\beta = F$ 在 $H_N$ 中的唯一解分别为
$$u_\alpha(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i(\alpha k_1 + k_2)} e^{2\pi i k\cdot y}, \qquad u_\beta(y) = \sum_{0 < |k| \le N} \frac{\widehat{F}(k)}{2\pi i(\beta k_1 + k_2)} e^{2\pi i k\cdot y}.$$
对每个 $k \in \Lambda_N = \{0 < |k| \le N\}$，$u_\alpha - u_\beta$ 的第 $k$ 个 Fourier 系数为
$$\widehat{u_\alpha - u_\beta}(k) = \frac{\widehat{F}(k)}{2\pi i} \left( \frac{1}{\alpha k_1 + k_2} - \frac{1}{\beta k_1 + k_2} \right) = \frac{\widehat{F}(k)}{2\pi i} \cdot \frac{(\beta - \alpha)k_1}{(\alpha k_1 + k_2)(\beta k_1 + k_2)}.$$
由已知条件，在 $0 < |k| \le N$ 上有 $|\alpha k_1 + k_2| \ge \delta > 0$，$|\beta k_1 + k_2| \ge \delta > 0$，且 $|k_1| \le (k_1^2 + k_2^2)^{1/2} = |k| \le N$。因此对每个 $0 < |k| \le N$，
$$\left|\widehat{u_\alpha - u_\beta}(k)\right| = \frac{|\alpha - \beta|\,|k_1|}{2\pi |\alpha k_1 + k_2|\,|\beta k_1 + k_2|} |\widehat{F}(k)| \le \frac{|\alpha - \beta| N}{2\pi \delta^2} |\widehat{F}(k)|.$$
对任意 $r \in \mathbb{R}$，在 $0 < |k| \le N$ 上带权 $\langle k \rangle^{2r}$ 求和：
$$\|u_\alpha - u_\beta\|_{H^r}^2 = \sum_{0 < |k| \le N} \langle k \rangle^{2r} \left|\widehat{u_\alpha - u_\beta}(k)\right|^2 \le \left(\frac{|\alpha - \beta| N}{2\pi \delta^2}\right)^2 \sum_{0 < |k| \le N} \langle k \rangle^{2r} |\widehat{F}(k)|^2 = \left(\frac{|\alpha - \beta| N}{2\pi \delta^2}\right)^2 \|F\|_{H^r}^2.$$
两边开方即得
$$\|u_\alpha - u_\beta\|_{H^r} \le |\alpha - \beta| N (2\pi \delta^2)^{-1} \|F\|_{H^r}. \qquad \blacksquare$$

---

## S4 整体对象与全部恢复目标

**总体结论**：在给定条件下，S4 所列的全部理论目标与具体估计**均成立**。下面给出完整的分类定理、显式构造与严格证明。

### 定理 4.1（$N_\alpha: C^\infty_0(\mathbb{T}^2) \to C^\infty_0(\mathbb{T}^2)$ 的可逆性与正则性分类）
设 $\alpha \in \mathbb{R} \setminus \mathbb{Q}$。
1. **单射性（唯一性）恒成立**：对任意无理数 $\alpha \in \mathbb{R}\setminus\mathbb{Q}$，$N_\alpha: C^\infty_0(\mathbb{T}^2) \to C^\infty_0(\mathbb{T}^2)$ 都是单射（即对任意 $F \in C^\infty_0(\mathbb{T}^2)$，$N_\alpha u = F$ 的光滑零均值解若存在必唯一）。
2. **先验 Sobolev 估计的精确刻画**：对给定 $\alpha \in \mathbb{R}\setminus\mathbb{Q}$ 和给定 $s \ge 0$，下列三条等价：
   - **(a)** 对每个 $r \in \mathbb{R}$ 存在与 $u$ 无关的有限常数 $C_{\alpha, r, s} < \infty$，使对所有 $u \in C^\infty_0(\mathbb{T}^2)$ 成立 $\|u\|_{H^r} \le C_{\alpha, r, s} \|N_\alpha u\|_{H^{r+s}}$；
   - **(b)** 存在某个 $r_0 \in \mathbb{R}$ 和有限常数 $C < \infty$，使对所有 $u \in C^\infty_0(\mathbb{T}^2)$ 成立 $\|u\|_{H^{r_0}} \le C \|N_\alpha u\|_{H^{r_0+s}}$；
   - **(c)** $\alpha$ 满足指数为 $s$ 的丢番图（Diophantine）条件：存在常数 $c > 0$，使得
     $$|\alpha k_1 + k_2| \ge c \langle k \rangle^{-s} \qquad \forall k = (k_1, k_2) \in \mathbb{Z}^2 \setminus \{0\}. \tag{DC$_s$}$$
   因此，使 Sobolev 估计成立的全部 $s \ge 0$ 的集合为
   $$\mathcal{S}(\alpha) := \left\{ s \ge 0 : \inf_{k \in \mathbb{Z}^2\setminus\{0\}} \langle k \rangle^s |\alpha k_1 + k_2| > 0 \right\}.$$
   特别地，由 Dirichlet 逼近定理，对任何 $\alpha \in \mathbb{R}\setminus\mathbb{Q}$ 都有 $\mathcal{S}(\alpha) \subset [1, \infty)$（即 $0 \le s < 1$ 永不成立）。
3. **满射性（存在唯一性）的充要条件**：每个 $F \in C^\infty_0(\mathbb{T}^2)$ 都有唯一的光滑零均值解 $N_\alpha u = F$（即 $N_\alpha: C^\infty_0(\mathbb{T}^2) \to C^\infty_0(\mathbb{T}^2)$ 为双射），**当且仅当** $\alpha$ 是丢番图数（即非 Liouville 数，等价于 $\mathcal{S}(\alpha) \ne \emptyset$，即存在某个 $s \ge 1$ 和 $c > 0$ 使 $\text{(DC}_s\text{)}$ 成立）。

#### 定理 4.1 的证明
**(1) 唯一性**：若 $u_1, u_2 \in C^\infty_0(\mathbb{T}^2)$ 满足 $N_\alpha u_1 = N_\alpha u_2$，令 $w = u_1 - u_2 \in C^\infty_0(\mathbb{T}^2)$，则 $\widehat{w}(0) = 0$，且对任意 $k \in \mathbb{Z}^2\setminus\{0\}$ 有 $2\pi i(\alpha k_1 + k_2)\widehat{w}(k) = \widehat{N_\alpha w}(k) = 0$。由于 $\alpha \notin \mathbb{Q}$，对所有 $k \ne 0$ 有 $\alpha k_1 + k_2 \ne 0$，故 $\widehat{w}(k) = 0$（$\forall k \in \mathbb{Z}^2$）。由光滑函数的 Fourier 级数一致收敛性知 $w \equiv 0$。

**(2) Sobolev 损失 $s$ 的刻画**：
- **(c) $\implies$ (a)**：若 $\text{(DC}_s\text{)}$ 成立，则对任意 $r \in \mathbb{R}$ 及任意 $u \in C^\infty_0(\mathbb{T}^2)$（此时 $\widehat{u}(0)=0$），
  $$\|N_\alpha u\|_{H^{r+s}}^2 = \sum_{k \ne 0} \langle k \rangle^{2(r+s)} 4\pi^2 |\alpha k_1 + k_2|^2 |\widehat{u}(k)|^2 \ge (2\pi c)^2 \sum_{k \ne 0} \langle k \rangle^{2r} |\widehat{u}(k)|^2 = (2\pi c)^2 \|u\|_{H^r}^2,$$
  故取 $C_{\alpha, r, s} = (2\pi c)^{-1} < \infty$ 即满足要求。
- **(a) $\implies$ (b)**：显然。
- **(b) $\implies$ (c)**：设在某个 $r_0 \in \mathbb{R}$ 处有 $\|u\|_{H^{r_0}} \le C \|N_\alpha u\|_{H^{r_0+s}}$（$C > 0$）。对每个 $k \in \mathbb{Z}^2\setminus\{0\}$，代入单频光滑零均值函数 $u_k(y) = e^{2\pi i k \cdot y} \in C^\infty_0(\mathbb{T}^2)$，计算得 $\|u_k\|_{H^{r_0}} = \langle k \rangle^{r_0}$ 且 $\|N_\alpha u_k\|_{H^{r_0+s}} = 2\pi |\alpha k_1 + k_2| \langle k \rangle^{r_0+s}$。代入估计式并约去 $\langle k \rangle^{r_0} > 0$ 得
  $$1 \le 2\pi C |\alpha k_1 + k_2| \langle k \rangle^s \implies |\alpha k_1 + k_2| \ge (2\pi C)^{-1} \langle k \rangle^{-s} \qquad \forall k \in \mathbb{Z}^2\setminus\{0\},$$
  即 $\text{(DC}_s\text{)}$ 对 $c = (2\pi C)^{-1} > 0$ 成立。
- **为何必有 $s \ge 1$**：由 Dirichlet 逼近定理（适用条件：$\alpha \in \mathbb{R}\setminus\mathbb{Q}$），存在无穷多对互素整数 $(q_n, p_n)$（$1 \le q_1 < q_2 < \cdots$）满足 $|q_n \alpha - p_n| < q_n^{-1}$。取 $k^{(n)} = (q_n, -p_n) \in \mathbb{Z}^2\setminus\{0\}$，因 $|p_n| \le |\alpha|q_n + 1$，有 $\langle k^{(n)} \rangle \ge q_n$ 且 $|\alpha k_1^{(n)} + k_2^{(n)}| < q_n^{-1}$。若 $s < 1$，则
  $$\langle k^{(n)} \rangle^s |\alpha k_1^{(n)} + k_2^{(n)}| \le (1 + (1 + (|\alpha|+1)^2)q_n^2)^{s/2} q_n^{-1} = O(q_n^{s-1}) \to 0 \quad (n \to \infty),$$
  故 $\text{(DC}_s\text{)}$ 对 $s < 1$ 绝不成立。

**(3) 可逆性（双射性）的充要条件**：
- **充分性（$\mathcal{S}(\alpha) \ne \emptyset \implies N_\alpha$ 双射）**：设存在 $s \ge 1$ 和 $c > 0$ 使 $\text{(DC}_s\text{)}$ 成立。对任意 $F \in C^\infty_0(\mathbb{T}^2)$，直接援引 **S2 第 1 部分**（适用条件：$|\alpha k_1 + k_2| \ge c\langle k \rangle^{-s}$ 且 $F \in C^\infty_0(\mathbb{T}^2)$），由
  $$u(y) = \sum_{k \in \mathbb{Z}^2\setminus\{0\}} \frac{\widehat{F}(k)}{2\pi i(\alpha k_1 + k_2)} e^{2\pi i k \cdot y}$$
  定义了唯一的光滑零均值解 $u \in C^\infty_0(\mathbb{T}^2)$ 满足 $N_\alpha u = F$。
- **必要性（$\mathcal{S}(\alpha) = \emptyset \implies N_\alpha$ 非满射）**：设 $\mathcal{S}(\alpha) = \emptyset$（即 $\alpha$ 是 Liouville 数）。则对每个整数 $m \ge 1$，有 $\inf_{k \ne 0} \langle k \rangle^{m^2} |\alpha k_1 + k_2| = 0$。由于在任意有限球 $0 < |k| \le R$ 上 $|\alpha k_1 + k_2|$ 有正下界，可归纳选取整格点列 $k^{(m)} = (k_1^{(m)}, k_2^{(m)}) \in \mathbb{Z}^2\setminus\{0\}$（$m \ge 1$），满足 $1 \le |k^{(1)}| < |k^{(2)}| < \cdots < |k^{(m)}| < \cdots$（从而 $\langle k^{(m)} \rangle \ge m$ 且 $k^{(m)}$ 两两不同），以及
  $$0 < |\alpha k_1^{(m)} + k_2^{(m)}| \le \langle k^{(m)} \rangle^{-m^2} \qquad \forall m \ge 1.$$
  构造级数
  $$F(y) := \sum_{m=1}^\infty 2\pi i(\alpha k_1^{(m)} + k_2^{(m)}) e^{2\pi i k^{(m)} \cdot y}.$$
  对任意 $a, b \in \mathbb{N}_0$（记 $r = a+b$），当 $m \ge r + 2$ 时有 $m^2 - r \ge 2$，故形式偏导级数通项满足
  $$|(2\pi i k_1^{(m)})^a (2\pi i k_2^{(m)})^b 2\pi i(\alpha k_1^{(m)} + k_2^{(m)})| \le (2\pi)^{r+1} \langle k^{(m)} \rangle^{r - m^2} \le (2\pi)^{r+1} m^{-2}.$$
  由 Weierstrass M-判别法，$F \in C^\infty(\mathbb{T}^2)$ 且 $\int_{\mathbb{T}^2} F = 0$，即 $F \in C^\infty_0(\mathbb{T}^2)$，并且 $\widehat{F}(k^{(m)}) = 2\pi i(\alpha k_1^{(m)} + k_2^{(m)})$。若存在 $u \in C^\infty_0(\mathbb{T}^2)$ 使 $N_\alpha u = F$，则比较第 $k^{(m)}$ 个 Fourier 系数得
  $$2\pi i(\alpha k_1^{(m)} + k_2^{(m)})\widehat{u}(k^{(m)}) = \widehat{F}(k^{(m)}) = 2\pi i(\alpha k_1^{(m)} + k_2^{(m)}) \implies \widehat{u}(k^{(m)}) = 1 \quad (\forall m \ge 1),$$
  这与 $u \in C^\infty_0(\mathbb{T}^2) \subset L^2(\mathbb{T}^2)$ 的 Parseval 恒等式 $\sum_{k \in \mathbb{Z}^2} |\widehat{u}(k)|^2 = \|u\|_{L^2}^2 < \infty$ 矛盾！故此时 $N_\alpha$ 不是满射。$\blacksquare$

---

### 定理 4.2（$\alpha_* = \sqrt{2}-1$ 的最优损失与 $C^m$ 正则性估计）
对 $\alpha_* = \sqrt{2} - 1$：
1. 允许的 Sobolev 损失集合为 $\mathcal{S}(\alpha_*) = [1, \infty)$；**最小允许损失为 $s_{\min} = 1$，且 $s = 1$ 可以取到**，具体满足
   $$|\alpha_* k_1 + k_2| \ge \frac{1}{2\sqrt{2}} \langle k \rangle^{-1} \qquad \forall k \in \mathbb{Z}^2 \setminus \{0\},$$
   以及对所有 $r \in \mathbb{R}$ 和 $u \in C^\infty_0(\mathbb{T}^2)$：
   $$\|u\|_{H^r} \le \frac{\sqrt{2}}{\pi} \|N_{\alpha_*} u\|_{H^{r+1}}.$$
2. **结论：成立**。对每个 $m \in \mathbb{N}_0$，都存在与 $F$ 无关的有限常数 $C_m < \infty$，使对所有 $F \in C^\infty_0(\mathbb{T}^2)$，零均值解 $N_{\alpha_*}^{-1} F \in C^\infty_0(\mathbb{T}^2)$ 满足
   $$\|N_{\alpha_*}^{-1} F\|_{C^m} \le C_m \|F\|_{C^{m+4}}.$$

#### 定理 4.2 的证明
**(1) 最小允许损失 $s_{\min} = 1$ 及其可达性**：
- 由定理 4.1(2)，对任何无理数都有 $\mathcal{S}(\alpha_*) \subset [1, \infty)$，故允许的 $s$ 必满足 $s \ge 1$。
- 下面直接证明 $s = 1$ 可以取到：设 $k = (k_1, k_2) \in \mathbb{Z}^2 \setminus \{0\}$。
  - 若 $k_1 = 0$，则 $k_2 \in \mathbb{Z}\setminus\{0\}$，$|\alpha_* k_1 + k_2| = |k_2| \ge 1 \ge \langle k \rangle^{-1} > \frac{1}{2\sqrt{2}}\langle k \rangle^{-1}$。
  - 若 $k_1 \ne 0$，令 $q = k_1 \in \mathbb{Z}\setminus\{0\}$，$p = k_1 - k_2 \in \mathbb{Z}$，则 $\alpha_* k_1 + k_2 = (\sqrt{2}-1)k_1 + k_2 = q\sqrt{2} - p$。由于 $2q^2 - p^2 \in \mathbb{Z}$ 且 $\sqrt{2} \notin \mathbb{Q}$（故 $2q^2 \ne p^2$），必有 $|2q^2 - p^2| \ge 1$。利用平方差分解 $(q\sqrt{2}-p)(q\sqrt{2}+p) = 2q^2 - p^2$，且由 Cauchy-Schwarz 不等式 $|p| = |k_1 - k_2| \le |k_1| + |k_2| \le \sqrt{2}|k|$，可得
    $$|q\sqrt{2} + p| \le \sqrt{2}|k_1| + |k_1 - k_2| \le \sqrt{2}|k| + \sqrt{2}|k| = 2\sqrt{2}|k| < 2\sqrt{2}\langle k \rangle.$$
    因此
    $$|\alpha_* k_1 + k_2| = \frac{|2q^2 - p^2|}{|q\sqrt{2} + p|} \ge \frac{1}{2\sqrt{2}} \langle k \rangle^{-1}.$$
  这证明了 $\text{(DC}_1\text{)}$ 对 $c = (2\sqrt{2})^{-1}$ 成立，故 $1 \in \mathcal{S}(\alpha_*)$，最小损失 $s_{\min} = 1$ 且在 $s=1$ 处取到，且由定理 4.1(2) 知 $C_{\alpha_*, r, 1} = (2\pi c)^{-1} = \frac{\sqrt{2}}{\pi}$。

**(2) $\|N_{\alpha_*}^{-1} F\|_{C^m} \le C_m \|F\|_{C^{m+4}}$ 的证明**：
设 $F \in C^\infty_0(\mathbb{T}^2)$，令 $u = N_{\alpha_*}^{-1} F \in C^\infty_0(\mathbb{T}^2)$。
- **第一步（由 $H^{m+3}$ 控制 $C^m$ 范数）**：对任意非负整数 $a, b \ge 0$（$a+b \le m$），有 $|(2\pi i k_1)^a (2\pi i k_2)^b| \le (2\pi)^m |k|^{a+b} \le (2\pi)^m \langle k \rangle^m$。对任意 $y \in \mathbb{T}^2$，利用 Cauchy-Schwarz 不等式：
  $$\begin{aligned}
  |\partial_{y_1}^a \partial_{y_2}^b u(y)| &\le \sum_{k \in \mathbb{Z}^2\setminus\{0\}} (2\pi)^m \langle k \rangle^m |\widehat{u}(k)| \\
  &= (2\pi)^m \sum_{k \ne 0} \langle k \rangle^{-3} \cdot \langle k \rangle^{m+3} |\widehat{u}(k)| \\
  &\le (2\pi)^m \left( \sum_{k \ne 0} \langle k \rangle^{-6} \right)^{1/2} \|u\|_{H^{m+3}}.
  \end{aligned}$$
  因为在二维格点 $\mathbb{Z}^2$ 上指数 $6 > 2$，常数 $K_0 := \left(\sum_{k \ne 0} \langle k \rangle^{-6}\right)^{1/2} < \infty$ 有限。对 $y \in \mathbb{T}^2$ 取上确界并对 $a+b \le m$ 取最大值，得
  $$\|u\|_{C^m} \le (2\pi)^m K_0 \|u\|_{H^{m+3}}.$$
- **第二步（应用 $\alpha_*$ 在 $r = m+3, s = 1$ 处的 Sobolev 逆估计）**：由本定理第 (1) 部分，
  $$\|u\|_{H^{m+3}} \le \frac{\sqrt{2}}{\pi} \|F\|_{H^{m+4}}.$$
- **第三步（由 $C^{m+4}$ 控制 $H^{m+4}$ 范数）**：记 $M = m+4 \ge 4$。对任意 $k = (k_1, k_2) \in \mathbb{Z}^2\setminus\{0\}$，有 $|k|^2 = k_1^2 + k_2^2 \le 2\max(k_1^2, k_2^2)$，且因 $|k| \ge 1$，有 $\langle k \rangle^2 = 1 + |k|^2 \le 2|k|^2 \le 4\max(k_1^2, k_2^2)$。因此
  $$\langle k \rangle^{2M} \le 4^M \max(k_1^{2M}, k_2^{2M}) \le 4^M (k_1^{2M} + k_2^{2M}) = \frac{4^M}{(2\pi)^{2M}} \left( |(2\pi i k_1)^M|^2 + |(2\pi i k_2)^M|^2 \right).$$
  由于 $\widehat{F}(0) = 0$，且 $\widehat{\partial_{y_j}^M F}(k) = (2\pi i k_j)^M \widehat{F}(k)$（$j=1,2$），由 $\mathbb{T}^2$ 上的 Parseval 恒等式及归一化测度性质 $\|g\|_{L^2(\mathbb{T}^2)} \le \|g\|_{C^0}$，有
  $$\begin{aligned}
  \|F\|_{H^{m+4}}^2 &= \sum_{k \ne 0} \langle k \rangle^{2M} |\widehat{F}(k)|^2 \\
  &\le \frac{4^M}{(2\pi)^{2M}} \sum_{k \ne 0} \left( \left|\widehat{\partial_{y_1}^M F}(k)\right|^2 + \left|\widehat{\partial_{y_2}^M F}(k)\right|^2 \right) \\
  &= \frac{4^M}{(2\pi)^{2M}} \left( \|\partial_{y_1}^M F\|_{L^2(\mathbb{T}^2)}^2 + \|\partial_{y_2}^M F\|_{L^2(\mathbb{T}^2)}^2 \right) \\
  &\le \frac{4^M}{(2\pi)^{2M}} \left( \|\partial_{y_1}^M F\|_{C^0}^2 + \|\partial_{y_2}^M F\|_{C^0}^2 \right) \\
  &\le \frac{2 \cdot 4^{m+4}}{(2\pi)^{2(m+4)}} \|F\|_{C^{m+4}}^2.
  \end{aligned}$$
  开方得 $\|F\|_{H^{m+4}} \le \frac{\sqrt{2} \cdot 2^{m+4}}{(2\pi)^{m+4}} \|F\|_{C^{m+4}}$。
- **综合三步**：联立以上三式，对所有 $F \in C^\infty_0(\mathbb{T}^2)$ 有
  $$\|N_{\alpha_*}^{-1} F\|_{C^m} \le C_m \|F\|_{C^{m+4}}, \qquad \text{其中 } C_m := \frac{K_0 2^{m+5}}{(2\pi)^4 \pi} = \frac{2^{m+1}}{\pi^5} \left(\sum_{k \ne 0} \langle k \rangle^{-6}\right)^{1/2} < \infty.$$
  常数 $C_m$ 有限且与 $F$ 无关。$\blacksquare$

---

## S5 邻近方向的一致估计

**结论**：**不存在**（该命题不成立）。

**完整证明与反例构造**：
假设存在开区间 $J \ni \alpha_*$、有限数 $s \ge 0$ 及有限常数 $C < \infty$，使对每个无理数 $\alpha \in J \setminus \mathbb{Q}$ 和每个 $u \in C^\infty_0(\mathbb{T}^2)$ 都满足 $\|u\|_{L^2} \le C \|N_\alpha u\|_{H^s}$。我们给出满足全部前提的显式反例：

1. 因为 $J$ 是包含 $\alpha_*$ 的非空开区间，由有理数集 $\mathbb{Q}$ 在 $\mathbb{R}$ 中的稠密性，存在有理数 $r_0 = \frac{p}{q} \in J \cap \mathbb{Q}$，其中 $p \in \mathbb{Z}$，$q \in \mathbb{N}$ 且 $q \ge 1$。
2. 固定非零整频向量 $k^* := (q, -p) \in \mathbb{Z}^2 \setminus \{0\}$，并取光滑零均值单频函数
   $$u^*(y) := e^{2\pi i (q y_1 - p y_2)} \in C^\infty_0(\mathbb{T}^2).$$
   直接计算得
   $$\|u^*\|_{L^2} = 1,$$
   且对任意 $\alpha \in \mathbb{R}$，由于 $N_\alpha u^*(y) = 2\pi i(\alpha q - p) e^{2\pi i(q y_1 - p y_2)}$，有
   $$\|N_\alpha u^*\|_{H^s} = 2\pi |\alpha q - p| \langle k^* \rangle^s = 2\pi q (1 + q^2 + p^2)^{s/2} \left| \alpha - \frac{p}{q} \right|.$$
3. 因为 $p/q \in J$ 且 $J$ 为开区间，存在 $\varepsilon_0 > 0$ 使 $(p/q - \varepsilon_0, p/q + \varepsilon_0) \subset J$。取正整数 $M \in \mathbb{N}$ 充分大，满足
   $$M > \max\left\{ \frac{\sqrt{2}}{\varepsilon_0},\ 4\pi \sqrt{2}\, (C + 1) q (1 + q^2 + p^2)^{s/2} \right\},$$
   并定义
   $$\alpha := \frac{p}{q} + \frac{\sqrt{2}}{M}.$$
   由于 $p/q \in \mathbb{Q}$、$\sqrt{2} \notin \mathbb{Q}$ 且 $M \in \mathbb{N}$，显然 $\alpha \in \mathbb{R} \setminus \mathbb{Q}$ 为无理数；又 $|\alpha - p/q| = \frac{\sqrt{2}}{M} < \varepsilon_0$，故 $\alpha \in J \setminus \mathbb{Q}$。
4. 对该无理方向 $\alpha \in J \setminus \mathbb{Q}$ 及光滑零均值函数 $u^* \in C^\infty_0(\mathbb{T}^2)$，有
   $$C \|N_\alpha u^*\|_{H^s} = 2\pi C q (1 + q^2 + p^2)^{s/2} \frac{\sqrt{2}}{M} < \frac{C}{2(C+1)} < \frac{1}{2} < 1 = \|u^*\|_{L^2},$$
   即 $\|u^*\|_{L^2} > C \|N_\alpha u^*\|_{H^s}$，与假设矛盾！

（注：甚至若允许常数 $C$ 依赖于 $\alpha$，命题依然不成立，因为在开区间 $J$ 内可取如 $\alpha = \frac{p}{q} + \sum_{n=N_0}^\infty 10^{-n!} \in J \setminus \mathbb{Q}$ 的 Liouville 数，由定理 4.1(2) 知对该单一 $\alpha$ 也不存在任何有限的 $(s, C)$。）$\blacksquare$

---

## S6 一个具体方向的不可解数据

设 $\alpha = \sum_{n=1}^\infty 10^{-n!}$。对每个正整数 $n \ge 1$，定义正整数
$$q_n := 10^{n!} \in \mathbb{N}, \qquad p_n := 10^{n!} \sum_{j=1}^n 10^{-j!} = \sum_{j=1}^n 10^{n! - j!} \in \mathbb{N}.$$

**引理（逼近阶估计）**：对任意 $n \ge 1$，成立
$$0 < q_n \alpha - p_n < \frac{10}{9} 10^{-n \cdot n!} = \frac{10}{9} q_n^{-n}.$$
*引理证明*：由定义，
$$q_n \alpha - p_n = 10^{n!} \sum_{j=n+1}^\infty 10^{-j!} = \sum_{j=n+1}^\infty 10^{n! - j!} > 0.$$
当 $j \ge n+1$ 时，$j! - n! \ge (n+1)! - n! + (j - n - 1) = n \cdot n! + (j - n - 1)$。故由等比级数求和，
$$q_n \alpha - p_n \le 10^{-n \cdot n!} \sum_{m=0}^\infty 10^{-m} = \frac{10}{9} 10^{-n \cdot n!} = \frac{10}{9} q_n^{-n}. \qquad \square$$

### 1. 证明 $\alpha$ 无理
反证法：假设 $\alpha \in \mathbb{Q}$，则存在整数 $p \in \mathbb{Z}$ 和正整数 $q \in \mathbb{N}$（$q \ge 1$）使得 $\alpha = p/q$。
于是对任意 $n \ge 1$，有
$$q(q_n \alpha - p_n) = q_n p - q p_n \in \mathbb{Z}.$$
由上述引理，$q_n \alpha - p_n > 0$ 且 $q \ge 1$，因此整数 $q(q_n \alpha - p_n)$ 必为正整数，从而
$$q(q_n \alpha - p_n) \ge 1 \implies q_n \alpha - p_n \ge \frac{1}{q} \qquad \forall n \ge 1.$$
但另一方面，当 $n \to \infty$ 时，$\frac{10}{9} 10^{-n \cdot n!} \to 0$。取 $n = q + 1$，则 $q \cdot \frac{10}{9} 10^{-n \cdot n!} < (q+1) 10^{-(q+1)} < 1$，故
$$\frac{1}{q} \le q_n \alpha - p_n < \frac{10}{9} 10^{-n \cdot n!} < \frac{1}{q},$$
矛盾！因此 $\alpha \in \mathbb{R} \setminus \mathbb{Q}$ 是无理数。$\blacksquare$

### 2. 构造同一个光滑零均值函数 $F \in C^\infty_0(\mathbb{T}^2)$ 使 $N_\alpha u = F$ 无光滑零均值解
对每个 $n \ge 1$，取整频向量 $k^{(n)} := (q_n, -p_n) \in \mathbb{Z}^2 \setminus \{0\}$（因 $q_1 < q_2 < \cdots < q_n < \cdots$，序列 $\{k^{(n)}\}_{n=1}^\infty$ 中的格点两两互异且均非零）。定义单一函数 $F: \mathbb{T}^2 \to \mathbb{C}$ 为
$$F(y) := \sum_{n=1}^\infty 2\pi i (q_n \alpha - p_n) e^{2\pi i (q_n y_1 - p_n y_2)}.$$

**(i) 证明 $F \in C^\infty_0(\mathbb{T}^2)$**：
- 注意到 $\alpha = \sum_{j=1}^\infty 10^{-j!} < \sum_{m=1}^\infty 10^{-m} = \frac{1}{9} < 1$，故 $0 < p_n < q_n \alpha < q_n$。
- 对任意非负整数 $a, b \ge 0$（记 $m = a+b$），将定义 $F$ 的级数逐项形式求偏导 $\partial_{y_1}^a \partial_{y_2}^b$，其第 $n$ 项在 $\mathbb{T}^2$ 上的绝对值一致有界于：
  $$\sup_{y \in \mathbb{T}^2} \left| (2\pi i q_n)^a (-2\pi i p_n)^b 2\pi i (q_n \alpha - p_n) e^{2\pi i (q_n y_1 - p_n y_2)} \right| \le (2\pi)^{m+1} q_n^m (q_n \alpha - p_n).$$
- 由前述引理 $q_n \alpha - p_n < \frac{10}{9} q_n^{-n}$，当 $n \ge m + 1$ 时有 $q_n^{m-n} = 10^{(m-n)n!} \le 10^{-n!} \le 10^{-n}$，从而
  $$\sum_{n=m+1}^\infty (2\pi)^{m+1} q_n^m (q_n \alpha - p_n) \le \frac{10}{9} (2\pi)^{m+1} \sum_{n=m+1}^\infty 10^{-n} < \infty.$$
- 由 Weierstrass M-判别法，$F$ 的级数及其任意阶偏导数级数在 $\mathbb{T}^2$ 上绝对且一致收敛，故 $F \in C^\infty(\mathbb{T}^2)$。
- 由一致收敛性可逐项积分，又因对每个 $n \ge 1$ 有 $k^{(n)} = (q_n, -p_n) \ne (0,0)$，故
  $$\int_{\mathbb{T}^2} F(y)\,dy = \sum_{n=1}^\infty 2\pi i(q_n \alpha - p_n) \int_{\mathbb{T}^2} e^{2\pi i k^{(n)} \cdot y}\,dy = 0,$$
  即 $F \in C^\infty_0(\mathbb{T}^2)$。同时，由一致收敛性及指数函数系 $\{e_k\}_{k \in \mathbb{Z}^2}$ 的正交性，对所有 $n \ge 1$ 有
  $$\widehat{F}(k^{(n)}) = 2\pi i(q_n \alpha - p_n).$$

**(ii) 证明 $N_\alpha u = F$ 没有光滑零均值解**：
反证法：假设存在光滑零均值函数 $u \in C^\infty_0(\mathbb{T}^2)$ 满足 $N_\alpha u = F$。
对每个 $n \ge 1$，在等式 $N_\alpha u = F$ 两边取第 $k^{(n)} = (q_n, -p_n)$ 个 Fourier 系数（分部积分）：
$$2\pi i(\alpha k_1^{(n)} + k_2^{(n)}) \widehat{u}(k^{(n)}) = \widehat{N_\alpha u}(k^{(n)}) = \widehat{F}(k^{(n)}) = 2\pi i(q_n \alpha - p_n).$$
因为 $\alpha k_1^{(n)} + k_2^{(n)} = q_n \alpha - p_n > 0$，两边约去非零因子 $2\pi i(q_n \alpha - p_n)$ 得
$$\widehat{u}(k^{(n)}) = 1 \qquad \forall n \ge 1.$$
然而，$u \in C^\infty_0(\mathbb{T}^2) \subset L^2(\mathbb{T}^2)$，且 $\{k^{(n)}\}_{n=1}^\infty$ 是 $\mathbb{Z}^2$ 中两两不同的整格点序列。由 Parseval 恒等式（或 Riemann-Lebesgue 引理），必有
$$\sum_{n=1}^\infty |\widehat{u}(k^{(n)})|^2 \le \sum_{k \in \mathbb{Z}^2} |\widehat{u}(k)|^2 = \|u\|_{L^2}^2 < \infty \implies \lim_{n \to \infty} \widehat{u}(k^{(n)}) = 0,$$
这与 $\widehat{u}(k^{(n)}) = 1$（$\forall n \ge 1$）矛盾！因此 $N_\alpha u = F$ 不存在光滑零均值解。$\blacksquare$
