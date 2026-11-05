# Fourier 逆、截断误差与参数边界

---

## S1 有限频带上的逆

### 1. 算子结构与逆的构造

在归一化环面 $\mathbb T^2 = \mathbb R^2/\mathbb Z^2$ 上，配备标准正交基 $e_k(y) = e^{2\pi i k\cdot y}$ ($k\in\mathbb Z^2$)。对 $k\in\mathbb Z^2\setminus\{0\}$，微商作用于基函数为：
$$\partial_{y_1} e_k = 2\pi i k_1 e_k, \qquad \partial_{y_2} e_k = 2\pi i k_2 e_k,$$
故微分算子 $N_\alpha = \alpha\partial_{y_1} + \partial_{y_2}$ 作用于每个模态有：
$$N_\alpha e_k = 2\pi i (\alpha k_1 + k_2) e_k.$$

**非退化性**：若 $\alpha k_1 + k_2 = 0$，因 $\alpha\in\mathbb R\setminus\mathbb Q$，必有 $k_1 = 0$，进而 $k_2 = 0$。因此在 $0 < |k| \le N$ 上恒有 $\alpha k_1 + k_2 \neq 0$。

复三角多项式空间 $H_N = \operatorname{span}_{\mathbb C}\{e_k : 0 < |k| \le N\}$ 是一有限维不变子空间。任取 $F\in H_N$，其 Fourier 展开为
$$F(y) = \sum_{0 < |k| \le N} \widehat F(k) e^{2\pi i k\cdot y}.$$
定义逆算子 $T_N = (N_\alpha|_{H_N})^{-1}: H_N \to H_N$ 为
$$T_N F(y) = \sum_{0 < |k| \le N} \frac{\widehat F(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k\cdot y}.$$
显然 $N_\alpha (T_N F) = T_N (N_\alpha F) = F$，故 $T_N$ 是 $N_\alpha|_{H_N}$ 的唯一双边逆。

### 2. $H^r\to H^r$ 逆范数精确式

对任意实数 $r\in\mathbb R$，$H_N$ 上的 $H^r$ 范数定义为
$$\|F\|_{H^r}^2 = \sum_{0 < |k| \le N} \langle k\rangle^{2r} |\widehat F(k)|^2, \qquad \langle k\rangle = (1+|k|^2)^{1/2}.$$
代入 $T_N F$ 的 Fourier 展开式：
$$\|T_N F\|_{H^r}^2 = \sum_{0 < |k| \le N} \frac{1}{4\pi^2 |\alpha k_1 + k_2|^2} \langle k\rangle^{2r} |\widehat F(k)|^2.$$
记集合 $\mathcal K_N = \{k\in\mathbb Z^2 : 0 < |k| \le N\}$，由于 $\mathcal K_N$ 有限且对所有 $k\in\mathcal K_N$ 均有 $|\alpha k_1 + k_2| > 0$，其最小值必然取到：
$$0 < \min_{0 < |k| \le N} |\alpha k_1 + k_2| = |\alpha k_1^* + k_2^*|, \qquad k^*\in\mathcal K_N.$$
因此对任意 $F\in H_N$：
$$\|T_N F\|_{H^r}^2 \le \left(\frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|}\right)^2 \sum_{0 < |k| \le N} \langle k\rangle^{2r} |\widehat F(k)|^2 = \left(\frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|}\right)^2 \|F\|_{H^r}^2.$$
取极值模态 $F(y) = e_{k^*}(y) = e^{2\pi i k^*\cdot y} \in H_N$，此时 $\|F\|_{H^r} = \langle k^*\rangle^r \neq 0$，且
$$\|T_N e_{k^*}\|_{H^r} = \frac{1}{2\pi |\alpha k_1^* + k_2^*|} \langle k^*\rangle^r = \frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|} \|e_{k^*}\|_{H^r}.$$
故对任意实数 $r\in\mathbb R$，逆算子范数的精确表达式为：
$$\|T_N\|_{H^r\to H^r} = \frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|}.$$
（注：该算子范数对所有实数 $r\in\mathbb R$ 恒等，与 $r$ 无关。）

---

## S2 有算术界的截断误差

### 1. 光滑解 $u$ 的构造与存在唯一性

设 $|\alpha k_1 + k_2| \ge c \langle k\rangle^{-s}$ 对全部 $k\in\mathbb Z^2\setminus\{0\}$ 成立，其中 $c > 0, s \ge 0$。
对 $F\in C^\infty_0(\mathbb T^2)$，有 $\widehat F(0) = \int_{\mathbb T^2} F(y) dy = 0$。构造形式解：
$$u(y) = \sum_{k\in\mathbb Z^2\setminus\{0\}} \frac{\widehat F(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k\cdot y}, \qquad \widehat u(0) = 0.$$
**正则性验证**：对任意 $k\neq 0$，利用算术下界估计其 Fourier 系数：
$$|\widehat u(k)| = \frac{|\widehat F(k)|}{2\pi |\alpha k_1 + k_2|} \le \frac{1}{2\pi c} \langle k\rangle^s |\widehat F(k)|.$$
由于 $F\in C^\infty(\mathbb T^2)$，其 Fourier 系数速降：对任意 $M \ge 0$，存在常数 $C_{M+s} < \infty$ 使得 $|\widehat F(k)| \le C_{M+s} \langle k\rangle^{-(M+s)}$。从而
$$|\widehat u(k)| \le \frac{C_{M+s}}{2\pi c} \langle k\rangle^{-M} \qquad (\forall k\neq 0).$$
这表明 $\widehat u(k)$ 亦为速降序列，因此其 Fourier 级数及其任意阶微商均在 $\mathbb T^2$ 上绝对且一致收敛。由环面上光滑函数的 Fourier 刻画可知 $u\in C^\infty(\mathbb T^2)$。又 $\int_{\mathbb T^2} u = \widehat u(0) = 0$，故 $u\in C^\infty_0(\mathbb T^2)$。
逐项微商验证得：
$$N_\alpha u(y) = \sum_{k\neq 0} 2\pi i (\alpha k_1 + k_2) \widehat u(k) e^{2\pi i k\cdot y} = \sum_{k\neq 0} \widehat F(k) e^{2\pi i k\cdot y} = F(y).$$
即 $u$ 为所需的光滑零均值解。

### 2. 截断误差的先验估计证明

截断函数 $F_N = \sum_{0 < |k| \le N} \widehat F(k) e_k \in H_N$，由 S1 知
$$u_N = \sum_{0 < |k| \le N} \frac{\widehat F(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k\cdot y}.$$
因此误差函数为纯高频尾部：
$$u - u_N = \sum_{|k| > N} \frac{\widehat F(k)}{2\pi i (\alpha k_1 + k_2)} e^{2\pi i k\cdot y}.$$
计算其 $H^r$ 范数平方：
$$\|u - u_N\|_{H^r}^2 = \sum_{|k| > N} \langle k\rangle^{2r} \frac{|\widehat F(k)|^2}{4\pi^2 |\alpha k_1 + k_2|^2}.$$
利用算术界 $|\alpha k_1 + k_2|^{-2} \le c^{-2} \langle k\rangle^{2s}$，得：
$$\langle k\rangle^{2r} \frac{1}{4\pi^2 |\alpha k_1 + k_2|^2} \le \frac{1}{(2\pi c)^2} \langle k\rangle^{2(r+s)}.$$
对任意 $q \ge 0$，恒等变形分解权重：
$$\langle k\rangle^{2(r+s)} = \langle k\rangle^{-2q} \langle k\rangle^{2(r+s+q)}.$$
在求和区域 $|k| > N$ 内，由于 $|k|^2 \ge N^2 + 1 > N^2$，恒有
$$\langle k\rangle^2 = 1 + |k|^2 > 1 + N^2 \implies \langle k\rangle^{-2q} \le (1+N^2)^{-q}.$$
将此点态上界代入级数：
$$\begin{aligned}
\|u - u_N\|_{H^r}^2 
&\le \frac{1}{(2\pi c)^2} (1+N^2)^{-q} \sum_{|k| > N} \langle k\rangle^{2(r+s+q)} |\widehat F(k)|^2 \\
&\le \frac{1}{(2\pi c)^2} (1+N^2)^{-q} \sum_{k\in\mathbb Z^2\setminus\{0\}} \langle k\rangle^{2(r+s+q)} |\widehat F(k)|^2 \\
&= (2\pi c)^{-2} (1+N^2)^{-q} \|F\|_{H^{r+s+q}}^2.
\end{aligned}$$
两边开平方，即证得对任意 $r\in\mathbb R, q\ge 0$：
$$\|u - u_N\|_{H^r} \le (2\pi c)^{-1} (1+N^2)^{-q/2} \|F\|_{H^{r+s+q}}.$$

---

## S3 固定频带内改变方向

设 $\alpha, \beta \in \mathbb R\setminus\mathbb Q$，且满足在有限频带 $0 < |k| \le N$ 上：
$$|\alpha k_1 + k_2| \ge \delta > 0, \qquad |\beta k_1 + k_2| \ge \delta > 0.$$
对同一 $F\in H_N$，$F(y) = \sum_{0 < |k| \le N} \widehat F(k) e_k(y)$，对应的解分别为：
$$u_\alpha = \sum_{0 < |k| \le N} \frac{\widehat F(k)}{2\pi i (\alpha k_1 + k_2)} e_k, \qquad u_\beta = \sum_{0 < |k| \le N} \frac{\widehat F(k)}{2\pi i (\beta k_1 + k_2)} e_k.$$
作差计算模态系数：
$$\frac{1}{2\pi i (\alpha k_1 + k_2)} - \frac{1}{2\pi i (\beta k_1 + k_2)} = \frac{(\beta - \alpha) k_1}{2\pi i (\alpha k_1 + k_2)(\beta k_1 + k_2)}.$$
由于 $0 < |k| \le N$，其分量满足 $|k_1| \le |k| \le N$。结合小除数下界条件，对所有 $0 < |k| \le N$ 均有：
$$\left|\frac{(\beta - \alpha) k_1}{2\pi i (\alpha k_1 + k_2)(\beta k_1 + k_2)}\right| \le \frac{|\alpha - \beta| |k_1|}{2\pi |\alpha k_1 + k_2| |\beta k_1 + k_2|} \le \frac{|\alpha - \beta| N}{2\pi \delta^2}.$$
因此其 $H^r$ 范数平方估计为：
$$\begin{aligned}
\|u_\alpha - u_\beta\|_{H^r}^2 
&= \sum_{0 < |k| \le N} \langle k\rangle^{2r} \left|\frac{(\beta - \alpha) k_1}{2\pi i (\alpha k_1 + k_2)(\beta k_1 + k_2)}\right|^2 |\widehat F(k)|^2 \\
&\le \left(\frac{|\alpha - \beta| N}{2\pi \delta^2}\right)^2 \sum_{0 < |k| \le N} \langle k\rangle^{2r} |\widehat F(k)|^2 \\
&= \left[ |\alpha - \beta| N (2\pi \delta^2)^{-1} \right]^2 \|F\|_{H^r}^2.
\end{aligned}$$
两边开平方，即证：
$$\|u_\alpha - u_\beta\|_{H^r} \le |\alpha - \beta| N (2\pi \delta^2)^{-1} \|F\|_{H^r}.$$

---

## S4 整体对象与全部恢复目标

### 1. 全局可逆性的充分必要条件分类

**结论**：算子 $N_\alpha: C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 是双射（即对每个 $F\in C^\infty_0(\mathbb T^2)$ 均存在唯一的零均值光滑解 $u$）**当且仅当 $\alpha$ 不是 Liouville 数**（即 $\alpha$ 具有有限无理度 / 为 Diophantine 数）：
$$\exists\, c > 0, \ \tau < \infty \quad \text{s.t.} \quad |\alpha k_1 + k_2| \ge c \langle k\rangle^{-\tau} \quad (\forall k\in\mathbb Z^2\setminus\{0\}).$$

**证明**：
1. **单射性**：对任意无理数 $\alpha$，若 $N_\alpha u = 0$，在 Fourier 空间为 $2\pi i (\alpha k_1 + k_2) \widehat u(k) = 0$。由 $\alpha\notin\mathbb Q$，$k\neq 0 \implies \alpha k_1 + k_2 \neq 0$；又 $u\in C^\infty_0(\mathbb T^2) \implies \widehat u(0) = 0$。故全部 $\widehat u(k) = 0$，即 $u = 0$。单射性对一切无理数无条件成立。
2. **充分性**：若 $\alpha$ 不是 Liouville 数，存在 $c>0, \tau\ge 0$ 使 $|\alpha k_1 + k_2| \ge c\langle k\rangle^{-\tau}$。对任意 $F\in C^\infty_0(\mathbb T^2)$，形式解 $\widehat u(k) = \frac{\widehat F(k)}{2\pi i (\alpha k_1 + k_2)}$ 满足
   $$|\widehat u(k)| \le \frac{1}{2\pi c} \langle k\rangle^\tau |\widehat F(k)|.$$
   由于 $F$ 光滑，$\widehat F(k)$ 衰减快于任意多项式反比，故 $\widehat u(k)$ 亦具有速降性，级数定义了唯一的 $u\in C^\infty_0(\mathbb T^2)$，满足 $N_\alpha u = F$。
3. **必要性**：若 $\alpha$ 为 Liouville 数，则对任意 $j\ge 1$，存在整数对 $(q_j, p_j)$ ($q_j \ge 1$) 使得
   $$0 < |\alpha q_j - p_j| < \langle (q_j, -p_j)\rangle^{-j}.$$
   可选取子列使 $k^{(j)} = (q_j, -p_j)$ 满足 $\langle k^{(j)}\rangle$ 严格递增且 $\langle k^{(j)}\rangle \ge 2^j$。
   构造函数 $F$ 的 Fourier 系数为：当 $k = k^{(j)}$ 时令 $\widehat F(k^{(j)}) = |\alpha q_j - p_j|^{1/2}$，其余频率处取为 $0$。
   - 对任意固定的正整数 $M$，当 $j > 2M$ 时：
     $$\langle k^{(j)}\rangle^M |\widehat F(k^{(j)})| = \langle k^{(j)}\rangle^M |\alpha q_j - p_j|^{1/2} < \langle k^{(j)}\rangle^{M - j/2} \le 1.$$
     故 $\widehat F(k)$ 是速降序列，定义了光滑零均值函数 $F\in C^\infty_0(\mathbb T^2)$。
   - 但若存在解 $u$，其 Fourier 系数必满足
     $$|\widehat u(k^{(j)})| = \frac{|\widehat F(k^{(j)})|}{2\pi |\alpha q_j - p_j|} = \frac{1}{2\pi |\alpha q_j - p_j|^{1/2}} > \frac{1}{2\pi} \langle k^{(j)}\rangle^{j/2} \to \infty \quad (j\to\infty).$$
     这与光滑函数（乃至 $L^1(\mathbb T^2)$ 函数）Fourier 系数必须有界矛盾。故 $N_\alpha u = F$ 无光滑解。

### 2. 允许损失 $s$ 的完全确定

**定理**：对给定的无理数 $\alpha$，存在有限常数 $C_{\alpha,r,s}$ 使先验估计 $\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$ 对所有 $u\in C^\infty_0(\mathbb T^2)$ 成立，**当且仅当**存在 $c > 0$ 使得
$$|\alpha k_1 + k_2| \ge c \langle k\rangle^{-s} \qquad (\forall k\in\mathbb Z^2\setminus\{0\}).$$

**证明**：
- **充分性**：若该算术界成立，S2 的推导直接给出 $\|u\|_{H^r} \le \frac{1}{2\pi c} \|N_\alpha u\|_{H^{r+s}}$，此时可取 $C_{\alpha,r,s} = \frac{1}{2\pi c}$（与 $r$ 无关）。
- **必要性**：取单频试验函数 $u_k(y) = e^{2\pi i k\cdot y}$ ($k\neq 0$)，则 $\|u_k\|_{H^r} = \langle k\rangle^r$，$N_\alpha u_k = 2\pi i (\alpha k_1 + k_2) e_k$，$\|N_\alpha u_k\|_{H^{r+s}} = 2\pi |\alpha k_1 + k_2| \langle k\rangle^{r+s}$。带入先验估计得：
  $$\langle k\rangle^r \le C_{\alpha,r,s} \cdot 2\pi |\alpha k_1 + k_2| \langle k\rangle^{r+s} \implies |\alpha k_1 + k_2| \ge \frac{1}{2\pi C_{\alpha,r,s}} \langle k\rangle^{-s}.$$
  取 $c = (2\pi C_{\alpha,r,s})^{-1} > 0$ 即得算术界。

**与无理度的对应分类**：
设 $\mu(\alpha) = \inf\{\mu > 0 : \exists c>0, |\alpha - p/q| \ge c/q^\mu, \forall q\ge 1\}$ 为 $\alpha$ 的无理度。由 Dirichlet 逼近定理，对**任意**无理数 $\alpha$，必存在无穷多互素的 $(q_n, p_n)$ 使得 $|\alpha q_n - p_n| < 1/q_n$。令 $k^{(n)} = (q_n, -p_n)$，则 $\langle k^{(n)}\rangle \asymp q_n$，故
$$|\alpha k_1^{(n)} + k_2^{(n)}| \langle k^{(n)}\rangle^s \le \frac{C^s}{q_n^{1-s}}.$$
若 $s < 1$，当 $n\to\infty$ 时此式趋于 $0$，故对**任何**无理数 $\alpha$，允许的导数损失必须满足 $s \ge 1$。
更精确地：
1. 若 $\alpha$ 为 Liouville 数（$\mu(\alpha) = \infty$），则不存在任何有限的 $s \ge 0$ 使估计成立。
2. 若 $\alpha$ 具有有限无理度 $\mu(\alpha) < \infty$：
   - 对所有 $s > \mu(\alpha) - 1$，该估计恒成立；
   - 对所有 $s < \mu(\alpha) - 1$，该估计恒不成立；
   - 在临界端点 $s = \mu(\alpha) - 1$，估计成立当且仅当 $\alpha$ 具有有限常数型（即有极值界 $|\alpha - p/q| \ge c/q^{\mu(\alpha)}$）。

### 3. $\alpha_* = \sqrt 2 - 1$ 的最小损失

对于 $\alpha_* = \sqrt 2 - 1 = [0; \overline{2}]$，其连分数部分商有界（全为 $2$），是经典的 Badly Approximable 数，无理度 $\mu(\alpha_*) = 2$。
**结论**：最小允许损失为 **$s_{\min} = 1$**，且该最小值**可以取到**。

**证明**：
1. 由前述 Dirichlet 定理，任何无理数都不可能满足 $s < 1$，故 $s_{\min} \ge 1$。
2. 验证 $s = 1$ 确实成立：
   $\alpha_*$ 满足二次整系数方程 $x^2 + 2x - 1 = 0$，其共轭根为 $\alpha_*' = -\sqrt 2 - 1$。
   对任意非零整向量 $(k_1, k_2) \in \mathbb Z^2\setminus\{0\}$：
   - 若 $k_1 = 0$，则 $k_2 \neq 0$，从而 $|\alpha_* k_1 + k_2| = |k_2| \ge 1 \ge \langle k\rangle^{-1}$。
   - 若 $k_1 \neq 0$，考虑整值非退化二次型：
     $$Q(k_1, k_2) = k_2^2 - 2k_1 k_2 - k_1^2 = (k_2 + \alpha_* k_1)(k_2 - (\sqrt 2 + 1)k_1) \in \mathbb Z.$$
     因 $\sqrt 2\notin\mathbb Q$ 且 $k\neq 0$，该整数绝不为 $0$，故 $|Q(k_1, k_2)| \ge 1$。
     从而
     $$|\alpha_* k_1 + k_2| \cdot |k_2 - (\sqrt 2 + 1)k_1| \ge 1.$$
     对于第二项，三角不等式给出：
     $$|k_2 - (\sqrt 2 + 1)k_1| \le |\alpha_* k_1 + k_2| + 2\sqrt 2 |k_1|.$$
     若 $|\alpha_* k_1 + k_2| \ge 1$，则显然满足 $|\alpha_* k_1 + k_2| \ge \langle k\rangle^{-1}$。
     若 $|\alpha_* k_1 + k_2| < 1$，则
     $$|k_2 - (\sqrt 2 + 1)k_1| \le 1 + 2\sqrt 2 |k_1| \le (1+2\sqrt 2) \langle k\rangle.$$
     从而
     $$|\alpha_* k_1 + k_2| \ge \frac{1}{1+2\sqrt 2} \langle k\rangle^{-1}.$$
   取 $c = \frac{1}{1+2\sqrt 2} > 0$，对所有非零 $k$ 均有点态界 $|\alpha_* k_1 + k_2| \ge c\langle k\rangle^{-1}$。
   由第 2 部分的等价性，这严格证明了 $s = 1$ 允许且被取到。

### 4. 连续微商控制估计 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$ 的判定

**结论**：**命题成立**。对每个 $m\in\mathbb N_0$，均存在有限常数 $C_m < \infty$ 满足该估计。

**证明**：
记 $u = N_{\alpha_*}^{-1} F$。论证分三步完成控制链：

**第一步：$C^m(\mathbb T^2)$ 控制于 $H^{m+2}(\mathbb T^2)$（二维 Sobolev 嵌入）**
对任意多重指标 $a, b \ge 0, a+b \le m$，微商点态展开为：
$$\partial_{y_1}^a \partial_{y_2}^b u(y) = \sum_{k\neq 0} (2\pi i k_1)^a (2\pi i k_2)^b \widehat u(k) e^{2\pi i k\cdot y}.$$
因此
$$|\partial_{y_1}^a \partial_{y_2}^b u(y)| \le (2\pi)^m \sum_{k\neq 0} \langle k\rangle^m |\widehat u(k)|.$$
对求和利用 Cauchy-Schwarz 不等式：
$$\sum_{k\neq 0} \langle k\rangle^m |\widehat u(k)| = \sum_{k\neq 0} \langle k\rangle^{-2} \cdot \langle k\rangle^{m+2} |\widehat u(k)| \le \left(\sum_{k\neq 0} \langle k\rangle^{-4}\right)^{1/2} \left(\sum_{k\neq 0} \langle k\rangle^{2(m+2)} |\widehat u(k)|^2\right)^{1/2}.$$
在二维空间中，$\sum_{k\neq 0} \langle k\rangle^{-4} = \sum_{k\neq 0} (1+|k|^2)^{-2} \le \sum_{k\neq 0} |k|^{-4} =: K_0^2 < \infty$。
从而
$$\|u\|_{C^m} \le (2\pi)^m K_0 \|u\|_{H^{m+2}}.$$

**第二步：$H^{m+2}$ 阶解控制于 $H^{m+3}$ 阶右端项（利用 $s = 1$ 的导数损失）**
由第 3 款已证的算术界，对 $r = m+2$ 应用 $H^r$ 先验估计：
$$\|u\|_{H^{m+2}} \le \frac{1}{2\pi c} \|N_{\alpha_*} u\|_{H^{(m+2)+1}} = \frac{1}{2\pi c} \|F\|_{H^{m+3}}.$$

**第三步：$H^{m+3}(\mathbb T^2)$ 控制于 $C^{m+3}(\mathbb T^2)$ 进而控制于 $C^{m+4}(\mathbb T^2)$**
令正整数 $L = m+3$。利用多元二项式展开：
$$\langle k\rangle^{2L} = (1 + k_1^2 + k_2^2)^L = \sum_{j_0+j_1+j_2=L} \frac{L!}{j_0! j_1! j_2!} k_1^{2j_1} k_2^{2j_2}.$$
由 Plancherel 等距定理：
$$\sum_{k\in\mathbb Z^2} k_1^{2j_1} k_2^{2j_2} |\widehat F(k)|^2 = \frac{1}{(2\pi)^{2(j_1+j_2)}} \|\partial_{y_1}^{j_1} \partial_{y_2}^{j_2} F\|_{L^2(\mathbb T^2)}^2.$$
在归一化测度环面上，对任意连续函数 $g$ 均有 $\|g\|_{L^2}^2 = \int_{\mathbb T^2} |g|^2 dy \le \sup_{y\in\mathbb T^2} |g(y)|^2 = \|g\|_{C^0}^2$。
故
$$\|\partial_{y_1}^{j_1} \partial_{y_2}^{j_2} F\|_{L^2}^2 \le \|F\|_{C^{j_1+j_2}}^2 \le \|F\|_{C^L}^2 = \|F\|_{C^{m+3}}^2.$$
代入和式：
$$\|F\|_{H^{m+3}}^2 \le \sum_{j_0+j_1+j_2=L} \frac{L!}{j_0! j_1! j_2!} \|F\|_{C^{m+3}}^2 = 3^{m+3} \|F\|_{C^{m+3}}^2.$$
即 $\|F\|_{H^{m+3}} \le 3^{(m+3)/2} \|F\|_{C^{m+3}} \le 3^{(m+3)/2} \|F\|_{C^{m+4}}$。

**综合上述三步**：
$$\|N_{\alpha_*}^{-1} F\|_{C^m} \le (2\pi)^m K_0 \cdot \frac{1}{2\pi c} \cdot 3^{(m+3)/2} \|F\|_{C^{m+4}} = C_m \|F\|_{C^{m+4}},$$
其中 $C_m = \frac{(2\pi)^{m-1} K_0 3^{(m+3)/2}}{c} < \infty$ 为与 $F$ 无关的有限常数。命题证毕。

---

## S5 邻近方向的一致估计

### 1. 结论

**不存在**这样的开区间 $J\ni \alpha_*$、有限 $s\ge 0$ 及常数 $C < \infty$。

### 2. 完整证明与反例构造

**反证法**：假设存在包含 $\alpha_* = \sqrt 2 - 1$ 的开区间 $J$、实数 $s \ge 0$ 以及有限常数 $C < \infty$，使得对**每个**无理数 $\alpha\in J$ 和每个 $u\in C^\infty_0(\mathbb T^2)$，均成立：
$$\|u\|_{L^2} \le C \|N_\alpha u\|_{H^s}.$$

**机制一：单频率模态在有理逼近下的失效（最简反例）**
由于 $J$ 是实数轴上的非空开区间，有理数集 $\mathbb Q$ 在 $\mathbb R$ 中稠密，因此 $J$ 中必包含至少一个有理数，记为 $p/q\in J$（$q\ge 1, p\in\mathbb Z$）。
取单频试验函数：
$$u(y) = e^{2\pi i (q y_1 - p y_2)}.$$
显然 $u$ 零均值且光滑，且 $\|u\|_{L^2} = 1$。
算子作用后计算 $H^s$ 范数：
$$N_\alpha u = 2\pi i (\alpha q - p) u \implies \|N_\alpha u\|_{H^s} = 2\pi |\alpha q - p| \langle (q, -p)\rangle^s.$$
依据假设的先验估计，对 $J$ 内的**任意**无理数 $\alpha$，必须满足：
$$1 \le 2\pi C |\alpha q - p| \langle (q, -p)\rangle^s \implies |\alpha - p/q| \ge \frac{1}{2\pi C q \langle (q, -p)\rangle^s} =: \eta > 0.$$
这表明在以 $p/q$ 为中心、半径为 $\eta$ 的开区间 $(p/q - \eta, \ p/q + \eta) \subset J$ 内，**不可能存在任何无理数**。
然而，无理数集 $\mathbb R\setminus\mathbb Q$ 在任意非空开区间内均是稠密的（基数连续统），矛盾！

**机制二：区间内 Liouville 数导致的失稳**
即使排除单一频率，在开区间 $J$ 内必然存在 Liouville 无理数 $\widetilde\alpha\in J$。
由 S4 第 2 款所证，对任何固定有限的 $s \ge 0$，Liouville 数满足：
$$\inf_{k\in\mathbb Z^2\setminus\{0\}} |\widetilde\alpha k_1 + k_2| \langle k\rangle^s = 0.$$
取单频序列 $u_k(y) = e^{2\pi i k\cdot y}$，其范数商为：
$$\frac{\|u_k\|_{L^2}}{\|N_{\widetilde\alpha} u_k\|_{H^s}} = \frac{1}{2\pi |\widetilde\alpha k_1 + k_2| \langle k\rangle^s} \to \infty.$$
故该不等式在任何包含无理数全集的开区间上都不可能有一致的有限导数损失 $s$ 与常数 $C$。

---

## S6 一个具体方向的不可解数据

考虑数 $\alpha = \sum_{n=1}^\infty 10^{-n!}$。

### 1. $\alpha$ 为无理数的证明

对任意正整数 $m\ge 1$，令
$$q_m = 10^{m!}, \qquad p_m = q_m \sum_{n=1}^m 10^{-n!} = \sum_{n=1}^m 10^{m! - n!} \in \mathbb Z^+.$$
则 $p_m / q_m$ 是有理数，且其逼近误差满足：
$$0 < \alpha - \frac{p_m}{q_m} = \sum_{n=m+1}^\infty 10^{-n!} = 10^{-(m+1)!} \sum_{n=m+1}^\infty 10^{-(n! - (m+1)!)}.$$
由于当 $n\ge m+1$ 时，$n! - (m+1)! \ge n - (m+1)$，故
$$0 < \alpha - \frac{p_m}{q_m} < 10^{-(m+1)!} \sum_{j=0}^\infty 10^{-j} = \frac{10}{9} 10^{-(m+1)!} \le 2\cdot 10^{-(m+1)!}.$$

假设 $\alpha$ 为有理数，即 $\alpha = a/b$（$a\in\mathbb Z, b\in\mathbb Z^+$）。
因级数各项均为严格正数，对任何有限项截断均有 $\alpha > p_m / q_m$，即 $a q_m - b p_m > 0$。
作为正整数，必有 $a q_m - b p_m \ge 1$。
从而误差有下界：
$$\alpha - \frac{p_m}{q_m} = \frac{a q_m - b p_m}{b q_m} \ge \frac{1}{b q_m} = \frac{1}{b \cdot 10^{m!}}.$$
结合上界，对所有 $m\ge 1$ 均需成立：
$$\frac{1}{b \cdot 10^{m!}} < 2\cdot 10^{-(m+1)!} \implies 10^{(m+1)! - m!} < 2b.$$
由于 $(m+1)! - m! = m\cdot m!$，上式即：
$$10^{m\cdot m!} < 2b \qquad (\forall m\ge 1).$$
但当 $m\to\infty$ 时，$10^{m\cdot m!}\to\infty$，而 $2b$ 为固定有限常数，产生矛盾！
故 $\alpha$ 必为无理数（实际上为超越数）。

### 2. 构造具体的反例函数 $F\in C^\infty_0(\mathbb T^2)$

对每个 $m\ge 2$，定义整频点
$$k^{(m)} = (q_m, -p_m) \in \mathbb Z^2\setminus\{0\}.$$
因 $q_m = 10^{m!}$ 严格单调递增，所有频率点 $k^{(m)}$ 两两互不相同。
其小除数满足：
$$0 < \alpha q_m - p_m = q_m \left(\alpha - \frac{p_m}{q_m}\right) < 10^{m!} \cdot \frac{10}{9} 10^{-(m+1)!} = \frac{10}{9} 10^{-m\cdot m!}.$$
其 Euclidean 范数满足 $q_m < |k^{(m)}| = \sqrt{q_m^2 + p_m^2} < \sqrt 2 q_m = \sqrt 2 \cdot 10^{m!}$。

构造函数 $F$ 的 Fourier 系数为：
$$\widehat F(k) = \begin{cases} 
10^{-\frac{1}{2} m\cdot m!}, & k = k^{(m)} \ (m\ge 2), \\
0, & \text{其他 } k\in\mathbb Z^2.
\end{cases}$$
即同一个解析给出的函数：
$$F(y) = \sum_{m=2}^\infty 10^{-\frac{1}{2} m\cdot m!} e^{2\pi i (q_m y_1 - p_m y_2)}.$$

**性质验证**：
1. **零均值**：由于所有 $k^{(m)} \neq (0,0)$，常数项 $\widehat F(0) = 0$，故 $\int_{\mathbb T^2} F(y) dy = 0$。
2. **光滑性 $F\in C^\infty(\mathbb T^2)$**：
   对任意微商阶数 $a, b \ge 0$，逐项求导级数的通项模为：
   $$\begin{aligned}
   \left| 10^{-\frac{1}{2} m\cdot m!} (2\pi i q_m)^a (-2\pi i p_m)^b \right| 
   &\le (2\pi)^{a+b} 10^{-\frac{1}{2} m\cdot m!} q_m^{a+b} \\
   &= (2\pi)^{a+b} 10^{\left(a+b - \frac{m}{2}\right) m!}.
   \end{aligned}$$
   对任意固定的 $a, b$，当 $m \ge 2(a+b) + 2$ 时，指数满足 $(a+b - m/2)m! \le -m! \le -2^m$。
   由 Weierstrass M-判别法，逐项微商级数在 $\mathbb T^2$ 上绝对且一致收敛。
   故 $F\in C^\infty(\mathbb T^2)$，因而 $F\in C^\infty_0(\mathbb T^2)$。

### 3. 不存在零均值光滑解的证明

假设存在 $u\in C^\infty_0(\mathbb T^2)$ 满足 $N_\alpha u = F$。
在频域上，必有点态等式：
$$2\pi i (\alpha k_1 + k_2) \widehat u(k) = \widehat F(k) \qquad (\forall k\in\mathbb Z^2).$$
对频率点列 $k = k^{(m)} = (q_m, -p_m)$ ($m\ge 2$)，解的 Fourier 系数模必为：
$$|\widehat u(k^{(m)})| = \frac{\widehat F(k^{(m)})}{2\pi (\alpha q_m - p_m)} > \frac{10^{-\frac{1}{2} m\cdot m!}}{2\pi \cdot \frac{10}{9} 10^{-m\cdot m!}} = \frac{9}{20\pi} 10^{\frac{1}{2} m\cdot m!}.$$
当 $m\to\infty$ 时，
$$\lim_{m\to\infty} |\widehat u(k^{(m)})| = +\infty.$$
然而，若 $u\in C^\infty(\mathbb T^2)$（甚至仅需 $u\in C^0(\mathbb T^2)$ 或 $u\in L^1(\mathbb T^2)$），由 Riemann-Lebesgue 引理及积分模控制，其 Fourier 系数必须有界：
$$|\widehat u(k)| = \left|\int_{\mathbb T^2} u(y) e^{-2\pi i k\cdot y} dy\right| \le \|u\|_{L^1} < \infty \qquad (\forall k\in\mathbb Z^2).$$
这与 $|\widehat u(k^{(m)})| \to \infty$ 发生不可调和的矛盾。
因此，方程 $N_\alpha u = F$ 绝不可能存在光滑零均值解（且在广义函数空间 $\mathcal D'(\mathbb T^2)$ 中亦无解）。构造完成。
