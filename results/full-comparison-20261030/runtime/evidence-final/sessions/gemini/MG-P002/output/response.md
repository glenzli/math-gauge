本题旨在建立二维环面 $\mathbb T^2 = \mathbb R^2 / \mathbb Z^2$ 上的输运算子

$$N_\alpha = \alpha\,\partial_{y_1} + \partial_{y_2}$$

在零均值光滑函数空间 $C^\infty_0(\mathbb T^2)$ 上的可逆性、小分母问题、Sobolev 空间与 $C^m$ 空间的正则性理论。

以下给出完整的理论体系、严格定理与构造性论证。

---

## 一、 主要结论概览

1. **可逆性刻画**：
   $N_\alpha : C^\infty_0(\mathbb T^2) \to C^\infty_0(\mathbb T^2)$ 为双射（即对每个 $F\in C^\infty_0(\mathbb T^2)$ 均存在唯一的零均值光滑解 $u$）的**充要条件是 $\alpha$ 不是刘维尔数（Liouville number）**，即 $\alpha$ 具有有限的无理性指数（$\mu(\alpha) < \infty$）。
2. **Sobolev 导数损失 $s\ge0$ 的完全刻画**：
   估计式 $\|u\|_{H^r} \le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$ 对所有 $r\in\mathbb R$ 成立，等价于对某个 $r$ 成立，且等价于存在 $c>0$ 使得对所有 $k\in\mathbb Z^2\setminus\{0\}$ 满足 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$。
   - 若 $\alpha$ 是刘维尔数（$\mu(\alpha)=\infty$），则**不存在**任何允许的 $s$；
   - 若 $\alpha$ 的无理性指数 $\mu(\alpha) < \infty$：
     - 必要条件为 $s \ge \mu(\alpha) - 1$；
     - 对所有 $s > \mu(\alpha) - 1$，该估计恒成立；
     - 临界点 $s = \mu(\alpha) - 1$ 成立当且仅当 $\alpha$ 满足严格类型估计 $\exists c>0, |\alpha - p/q| \ge c/q^{\mu(\alpha)}$。
3. **$\alpha_* = \sqrt{2}-1$ 的极小损失**：
   $\alpha_*$ 为有界部分商数（badly approximable），$\mu(\alpha_*)=2$。
   - 最小允许损失为 **$s_{\min} = 1$**；
   - 该极小值**可以取到**，允许损失集合为 **$[1, \infty)$**。
4. **$C^m$ 正则性估计**：
   **结论成立**。对每个 $m\in\mathbb N_0$，均存在常数 $C_m < \infty$，使得对所有 $F\in C^\infty_0(\mathbb T^2)$，零均值解满足
   $$\|N_{\alpha_*}^{-1}F\|_{C^m} \le C_m \|F\|_{C^{m+4}}.$$

---

## 二、 傅里叶表象与算子的单射性

设 $u\in C^\infty(\mathbb T^2)$，其傅里叶级数展开为
$$u(y) = \sum_{k\in\mathbb Z^2} \widehat u(k) e^{2\pi i k\cdot y}, \qquad \widehat u(k) = \int_{\mathbb T^2} u(y) e^{-2\pi i k\cdot y}\,dy.$$
零均值条件 $\int_{\mathbb T^2} u = 0$ 等价于 $\widehat u(0) = 0$。因此 $u\in C^\infty_0(\mathbb T^2)$ 等价于 $\widehat u(0)=0$ 且傅里叶系数 $(\widehat u(k))_{k\in\mathbb Z^2}$ 快速衰减，即对任意 $N\in\mathbb N_0$，
$$\sup_{k\in\mathbb Z^2} \langle k\rangle^N |\widehat u(k)| < \infty.$$

输运算子作用在基函数上：
$$N_\alpha\left(e^{2\pi i k\cdot y}\right) = \left(\alpha (2\pi i k_1) + 2\pi i k_2\right) e^{2\pi i k\cdot y} = 2\pi i (\alpha k_1 + k_2) e^{2\pi i k\cdot y}.$$
从而对 $u\in C^\infty_0(\mathbb T^2)$：
$$N_\alpha u(y) = \sum_{k\in\mathbb Z^2\setminus\{0\}} 2\pi i (\alpha k_1 + k_2)\widehat u(k) e^{2\pi i k\cdot y}.$$
积分得 $\int_{\mathbb T^2} N_\alpha u = \widehat{N_\alpha u}(0) = 0$，故 $N_\alpha$ 确将 $C^\infty_0(\mathbb T^2)$ 映入 $C^\infty_0(\mathbb T^2)$。

### 单射性命题
> **命题 1**：对任意无理数 $\alpha\in\mathbb R\setminus\mathbb Q$，$N_\alpha : C^\infty_0(\mathbb T^2) \to C^\infty_0(\mathbb T^2)$ 均为单射。

**证明**：
若 $N_\alpha u = 0$，则对所有 $k\in\mathbb Z^2\setminus\{0\}$，有
$$2\pi i (\alpha k_1 + k_2) \widehat u(k) = 0.$$
若 $\alpha k_1 + k_2 = 0$：
- 若 $k_1 = 0$，则 $k_2 = 0$；
- 若 $k_1 \neq 0$，则 $\alpha = -k_2 / k_1 \in \mathbb Q$，与 $\alpha$ 无理矛盾。
因此对所有 $k\in\mathbb Z^2\setminus\{0\}$，均有 $\alpha k_1 + k_2 \neq 0$。由此得 $\widehat u(k) = 0$（$\forall k\neq 0$）。又 $\widehat u(0) = 0$，故 $u \equiv 0$。 $\blacksquare$

---

## 三、 可逆性定理：非刘维尔数的充要刻画

给定 $F\in C^\infty_0(\mathbb T^2)$，形式解 $u$ 的傅里叶系数必由下式唯一确定：
$$\widehat u(0) = 0, \qquad \widehat u(k) = \frac{\widehat F(k)}{2\pi i (\alpha k_1 + k_2)} \quad (k\in\mathbb Z^2\setminus\{0\}).$$

> **定理 1**：$N_\alpha : C^\infty_0(\mathbb T^2) \to C^\infty_0(\mathbb T^2)$ 是满射（从而为双射）的充分必要条件是 **$\alpha$ 不是刘维尔数**（即 $\alpha$ 具有有限无理性指数 $\mu(\alpha) < \infty$）。

### 1. 充分性证明
假设 $\alpha$ 不是刘维尔数。根据定义，存在常数 $\tau \ge 2$ 与 $c_0 > 0$，使得对所有 $p\in\mathbb Z, q\in\mathbb N$，
$$\left|\alpha - \frac{p}{q}\right| \ge \frac{c_0}{q^\tau}.$$
我们证明存在常数 $c > 0$，使得对一切 $k = (k_1, k_2)\in\mathbb Z^2\setminus\{0\}$，满足
$$|\alpha k_1 + k_2| \ge \frac{c}{\langle k\rangle^{\tau - 1}}.$$
- 若 $k_1 = 0$，则 $|k_2|\ge 1$，故 $|\alpha k_1 + k_2| = |k_2| \ge 1 \ge \frac{1}{\langle k\rangle^{\tau-1}}$；
- 若 $k_1 \neq 0$，令 $q = |k_1|\ge 1$，$p = -\operatorname{sgn}(k_1) k_2 \in\mathbb Z$。则
  $$|\alpha k_1 + k_2| = q \left|\alpha - \frac{p}{q}\right|.$$
  - 若 $|\alpha - p/q| \ge 1$，则 $|\alpha k_1 + k_2| \ge q \ge 1 \ge \langle k\rangle^{-(\tau-1)}$；
  - 若 $|\alpha - p/q| < 1$，则 $|p| \le (|\alpha|+1)q$，故 $|k| = \sqrt{q^2 + p^2} \le \sqrt{1 + (|\alpha|+1)^2}\,q$。因此 $\langle k\rangle \le C_\alpha q$。代入丢番图条件得：
    $$|\alpha k_1 + k_2| = q \left|\alpha - \frac{p}{q}\right| \ge q \frac{c_0}{q^\tau} = \frac{c_0}{q^{\tau-1}} \ge \frac{c_0 C_\alpha^{-(\tau-1)}}{\langle k\rangle^{\tau-1}} =: \frac{c}{\langle k\rangle^{\tau-1}}.$$

因 $F\in C^\infty_0(\mathbb T^2)$，对任意正整数 $N$，存在常数 $M_N < \infty$ 使 $|\widehat F(k)| \le M_N \langle k\rangle^{-(N + \tau - 1)}$。于是
$$|\widehat u(k)| = \frac{|\widehat F(k)|}{2\pi |\alpha k_1 + k_2|} \le \frac{M_N}{2\pi c} \langle k\rangle^{-(N + \tau - 1)} \langle k\rangle^{\tau-1} = \frac{M_N}{2\pi c} \langle k\rangle^{-N}.$$
由 $N$ 的任意性知 $(\widehat u(k))$ 快速衰减，因此 $u(y) = \sum_{k\neq 0} \widehat u(k) e^{2\pi i k\cdot y} \in C^\infty_0(\mathbb T^2)$，且显然 $N_\alpha u = F$。

### 2. 必要性证明（反例构造）
假设 $\alpha$ 为刘维尔数。根据定义，对任意 $n\in\mathbb N$，存在互素的整数对 $(p_n, q_n)$ 满足 $q_n \ge 2$ 且
$$0 < \left|\alpha - \frac{p_n}{q_n}\right| < \frac{1}{q_n^n}.$$
不妨取严格递增子序列满足 $q_{n+1} \ge q_n^2$。取格点序列
$$k^{(n)} = (q_n, -p_n) \in \mathbb Z^2\setminus\{0\}.$$
注意到由 $|\alpha - p_n/q_n| < 1/q_n^n \le 1$ 可知 $|p_n| \le (|\alpha|+1)q_n$，从而 $\langle k^{(n)}\rangle \le C_\alpha q_n$。同时，其小分母满足：
$$|\alpha k_1^{(n)} + k_2^{(n)}| = |\alpha q_n - p_n| = q_n \left|\alpha - \frac{p_n}{q_n}\right| < \frac{1}{q_n^{n-1}}.$$

现构造函数 $F(y)$，定义其傅里叶系数为：
$$\widehat F(k) = \begin{cases}
q_n^{-n/2}, & \text{若 } k = k^{(n)} \text{ 或 } k = -k^{(n)} \ (n\in\mathbb N), \\
0, & \text{其他.}
\end{cases}$$
显然 $\widehat F(0) = 0$ 且 $\overline{\widehat F(k)} = \widehat F(-k)$。对任意给定的 $N\in\mathbb N$，当 $n \ge 2N$ 时，
$$\langle k^{(n)}\rangle^N |\widehat F(k^{(n)})| \le (C_\alpha q_n)^N q_n^{-n/2} = C_\alpha^N q_n^{N - n/2} \le C_\alpha^N.$$
因此 $\sup_{k\in\mathbb Z^2} \langle k\rangle^N |\widehat F(k)| < \infty$，从而 $F \in C^\infty_0(\mathbb T^2)$。

但对于形式解 $u$，在格点 $k^{(n)}$ 处的傅里叶系数满足：
$$|\widehat u(k^{(n)})| = \frac{|\widehat F(k^{(n)})|}{2\pi |\alpha q_n - p_n|} > \frac{q_n^{-n/2}}{2\pi q_n^{-(n-1)}} = \frac{q_n^{n/2 - 1}}{2\pi}.$$
因为 $q_n \ge 2$，当 $n\to\infty$ 时，
$$|\widehat u(k^{(n)})| \to \infty.$$
傅里叶系数甚至不趋于 $0$，故 $u \notin L^2(\mathbb T^2)$，更不可能为 $C^\infty(\mathbb T^2)$ 中的函数（事实上 $u$ 甚至不是缓增分布）。这说明方程 $N_\alpha u = F$ 在 $C^\infty_0(\mathbb T^2)$ 中无解。 $\blacksquare$

---

## 四、 Sobolev 空间的先验估计与导数损失 $s$ 的确定

我们考虑先验估计：
$$\|u\|_{H^r} \le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}} \qquad (\forall u\in C^\infty_0(\mathbb T^2)).$$

### 1. 傅里叶空间等价化
由 Plancherel 定理与 $H^r$ 范数定义：
$$\|u\|_{H^r}^2 = \sum_{k\in\mathbb Z^2\setminus\{0\}} \langle k\rangle^{2r} |\widehat u(k)|^2,$$
$$\|N_\alpha u\|_{H^{r+s}}^2 = \sum_{k\in\mathbb Z^2\setminus\{0\}} 4\pi^2 \langle k\rangle^{2(r+s)} |\alpha k_1 + k_2|^2 |\widehat u(k)|^2.$$

- **必要性**：将单一频率函数 $u_k(y) = e^{2\pi i k\cdot y} - e^{-2\pi i k\cdot y}$（或复指数基函数）代入不等式，立即得到对任意 $k\in\mathbb Z^2\setminus\{0\}$：
  $$\langle k\rangle^{2r} \le 4\pi^2 C_{\alpha,r,s}^2 \langle k\rangle^{2r+2s} |\alpha k_1 + k_2|^2 \iff |\alpha k_1 + k_2| \ge \frac{1}{2\pi C_{\alpha,r,s}} \langle k\rangle^{-s}.$$
- **充分性**：若存在 $c > 0$ 使得 $|\alpha k_1 + k_2| \ge c \langle k\rangle^{-s}$ 对所有 $k\neq 0$ 成立，则
  $$\|N_\alpha u\|_{H^{r+s}}^2 = \sum_{k\neq 0} 4\pi^2 \langle k\rangle^{2r} \cdot \left(\langle k\rangle^s |\alpha k_1 + k_2|\right)^2 |\widehat u(k)|^2 \ge 4\pi^2 c^2 \|u\|_{H^r}^2.$$
  因此不等式对常数 $C_{\alpha,r,s} = \frac{1}{2\pi c}$ 成立（该常数与 $r$ 无关）。

由此得出关键判据：**估计式对所有 $r\in\mathbb R$ 成立 $\iff$ 存在常数 $c>0$，使得**
$$\inf_{k\in\mathbb Z^2\setminus\{0\}} \langle k\rangle^s |\alpha k_1 + k_2| \ge c > 0.$$

### 2. 与无理性指数 $\mu(\alpha)$ 的联系及全体允许的 $s$

回忆无理数 $\alpha$ 的**无理性指数**（irrationality exponent）定义为
$$\mu(\alpha) = \inf \left\{\mu \in \mathbb R : \exists C>0 \text{ 使得 } \left|\alpha - \frac{p}{q}\right| \ge \frac{C}{q^\mu}, \ \forall p\in\mathbb Z, q\in\mathbb N\right\}.$$
根据前文几何分析，$k_1\neq 0$ 时，当 $|\alpha - p/q| < 1$ 时 $\langle k\rangle \asymp q$ 且 $|\alpha k_1 + k_2| = q |\alpha - p/q|$。
故条件 $\langle k\rangle^s |\alpha k_1 + k_2| \ge c$ 等价于
$$\left|\alpha - \frac{p}{q}\right| \ge \frac{c'}{q^{s+1}} \qquad (\forall p\in\mathbb Z, q\in\mathbb N).$$

> **定理 2**：
> 1. 由 Dirichlet 逼近定理，对**任意**无理数 $\alpha$，均存在无穷多对互素整数 $(p,q)$ 满足 $|\alpha - p/q| < 1/q^2$。故 $s+1 \ge 2$，即 **$s \ge 1$ 是任何无理数允许该先验估计的必要条件**。
> 2. 若 $\alpha$ 为刘维尔数（$\mu(\alpha) = \infty$），则**不存在任何 $s\ge 0$** 满足该估计（允许的 $s$ 构成的集合为空集 $\emptyset$）。
> 3. 若 $\alpha$ 的无理性指数 $\mu(\alpha) < \infty$：
>    - 允许的 $s$ 必满足 $s \ge \mu(\alpha) - 1$；
>    - 对所有开区间内的 $s \in (\mu(\alpha) - 1, \infty)$，估计恒成立；
>    - 临界端点 $s = \mu(\alpha) - 1$ 允许，当且仅当存在常数 $C>0$ 使得 $|\alpha - p/q| \ge C / q^{\mu(\alpha)}$ 对一切 $p,q$ 成立。

---

## 五、 特例 $\alpha_* = \sqrt{2}-1$ 的极小损失及其可达性

设 $\alpha_* = \sqrt{2}-1$。

### 1. 连分数展开与代数下界
计算 $\alpha_*$ 的连分数：
$$\alpha_* = \frac{1}{\sqrt{2}+1} = \frac{1}{2 + (\sqrt{2}-1)} = [0; 2, 2, 2, \dots] = [0; \overline{2}].$$
其所有部分商均为 $a_n = 2 \le 2 < \infty$。因此 $\alpha_*$ 为极值不可逼近数（badly approximable number），其无理性指数取到理论最小值：
$$\mu(\alpha_*) = 2.$$

我们直接给出初等代数证明：
对任意 $p\in\mathbb Z, q\in\mathbb N$，令 $P = p + q \in \mathbb Z$。
由于 $\sqrt{2}$ 是无理数，$2q^2 - P^2 \neq 0$；又因 $2q^2 - P^2\in\mathbb Z$，故 $|2q^2 - P^2| \ge 1$。
因式分解得：
$$1 \le |2q^2 - P^2| = |q\sqrt{2} - P| \cdot |q\sqrt{2} + P| = q^2 \left|\sqrt{2} - \frac{P}{q}\right| \left(\sqrt{2} + \frac{P}{q}\right).$$
- 若 $|\sqrt{2} - P/q| \ge 1$，则显然 $|\alpha_* - p/q| = |\sqrt{2} - P/q| \ge 1 > \frac{1}{4q^2}$；
- 若 $|\sqrt{2} - P/q| < 1$，则 $P/q < \sqrt{2} + 1$，由此 $\sqrt{2} + P/q < 2\sqrt{2} + 1 < 4$。
代入分解式得：
$$\left|\alpha_* - \frac{p}{q}\right| = \left|\sqrt{2} - \frac{P}{q}\right| \ge \frac{1}{q^2 \left(\sqrt{2} + \frac{P}{q}\right)} > \frac{1}{4q^2}.$$

### 2. 小分母一致下界与极小损失 $s_{\min}$
现验证小分母下界：
- 当 $k_1 = 0$ 时，$k_2\neq 0$，则 $|\alpha_* k_1 + k_2| = |k_2| \ge 1 \ge \frac{1}{\langle k\rangle}$；
- 当 $k_1 \neq 0$ 时，设 $q = |k_1| \ge 1, p = -\operatorname{sgn}(k_1) k_2$。
  - 若 $|\alpha_* - p/q| \ge 1$，则 $|\alpha_* k_1 + k_2| \ge q \ge 1 \ge \frac{1}{\langle k\rangle}$；
  - 若 $|\alpha_* - p/q| < 1$，则 $|p| < (\alpha_* + 1)q = \sqrt{2}q$。格点范数满足：
    $$|k|^2 = q^2 + p^2 < 3q^2 \implies \langle k\rangle = \sqrt{1+|k|^2} \le 2q.$$
    因此：
    $$|\alpha_* k_1 + k_2| = q \left|\alpha_* - \frac{p}{q}\right| > q \cdot \frac{1}{4q^2} = \frac{1}{4q} \ge \frac{1}{8\langle k\rangle}.$$

综合以上两类情形，存在常数 $c_* = \frac{1}{8} > 0$，使得对所有 $k\in\mathbb Z^2\setminus\{0\}$ 均有
$$|\alpha_* k_1 + k_2| \ge \frac{c_*}{\langle k\rangle^1}.$$

> **结论 1**：
> 1. 允许的最小损失为 **$s_{\min} = 1$**；
> 2. 该极小值**可以取到**（在 $s = 1$ 处不等式成立）；
> 3. 全体允许的损失指数集为闭区间 **$[1, \infty)$**。

---

## 六、 $C^m$ 空间上的正则性估计

现判断是否存在常数 $C_m < \infty$，使得对所有 $F\in C^\infty_0(\mathbb T^2)$，
$$\|N_{\alpha_*}^{-1} F\|_{C^m} \le C_m \|F\|_{C^{m+4}}.$$

> **结论 2**：**该断言完全成立（判断为：是）**。
>
> 导数损失 $+4$ 的数学本质可精确分解为：
> 1. **输运方程的小分母逆算子损失 $1$ 阶导数**（因为 $s_{\min}=1$）；
> 2. **在 2 维环面上，将傅里叶级数求和控制回 $L^\infty$ 范数需损失严格大于 2 阶（取整数即为 3 阶）导数**以保证级数收敛；
> 3. 两者相加恰为 $1 + 3 = 4$ 阶导数损失。

下面给出两种严谨的证明。

### 论证方法一：傅里叶级数直接估计法（显式常数）
设 $F\in C^\infty_0(\mathbb T^2)$，$u = N_{\alpha_*}^{-1}F$。对任意指标 $\beta = (a, b)\in\mathbb N_0^2$ 满足 $a+b \le m$，
$$\partial_{y_1}^a \partial_{y_2}^b u(y) = \sum_{k\in\mathbb Z^2\setminus\{0\}} (2\pi i k_1)^a (2\pi i k_2)^b \frac{\widehat F(k)}{2\pi i (\alpha_* k_1 + k_2)} e^{2\pi i k\cdot y}.$$
取绝对值，利用 $k_1^2 + k_2^2 \le |k|^2$ 与下界 $|\alpha_* k_1 + k_2| \ge c_* \langle k\rangle^{-1}$（取 $c_* = 1/8$）：
$$|\partial_{y_1}^a \partial_{y_2}^b u(y)| \le \sum_{k\neq 0} (2\pi)^{m-1} |k|^m \frac{|\widehat F(k)|}{|\alpha_* k_1 + k_2|} \le \frac{(2\pi)^{m-1}}{c_*} \sum_{k\neq 0} \langle k\rangle^{m+1} |\widehat F(k)|.$$
将上式裂项分解为：
$$\sum_{k\neq 0} \langle k\rangle^{m+1} |\widehat F(k)| = \sum_{k\neq 0} \langle k\rangle^{-3} \cdot \left(\langle k\rangle^{m+4} |\widehat F(k)|\right).$$
1. **级数收敛性**：在二维格点 $\mathbb Z^2$ 上，
   $$S := \sum_{k\in\mathbb Z^2\setminus\{0\}} \langle k\rangle^{-3} < \infty.$$
   （注：$\sum_{k\neq 0} |k|^{-3} \le \sum_{R=1}^\infty \sum_{R\le |k|<R+1} R^{-3} \le \sum_{R=1}^\infty 8R \cdot R^{-3} = 8\sum_{R=1}^\infty R^{-2} < \infty$）。
2. **傅里叶系数与 $C^{m+4}$ 范数的控制**：
   对任意 $k = (k_1, k_2)\neq 0$，取绝对值较大者对应的坐标 $j\in\{1, 2\}$，使得 $|k_j| = \max(|k_1|, |k_2|) \ge \frac{1}{\sqrt{2}}|k|$。
   对分量 $y_j$ 进行 $m+4$ 次分部积分：
   $$(2\pi i k_j)^{m+4} \widehat F(k) = \int_{\mathbb T^2} \partial_{y_j}^{m+4} F(y) e^{-2\pi i k\cdot y}\,dy.$$
   两边取模：
   $$(2\pi |k_j|)^{m+4} |\widehat F(k)| \le \|\partial_{y_j}^{m+4} F\|_{L^1} \le \|\partial_{y_j}^{m+4} F\|_{C^0} \le \|F\|_{C^{m+4}}.$$
   由于 $|k| \le \sqrt{2}|k_j|$ 且 $\langle k\rangle \le \sqrt{2}|k|$（对 $k\neq 0$），有 $\langle k\rangle \le 2|k_j|$。因此
   $$\langle k\rangle^{m+4} |\widehat F(k)| \le 2^{m+4} |k_j|^{m+4} |\widehat F(k)| \le \frac{2^{m+4}}{(2\pi)^{m+4}} \|F\|_{C^{m+4}} = \pi^{-(m+4)} \|F\|_{C^{m+4}}.$$
3. 将上述两项代入求和：
   $$\|u\|_{C^m} \le \frac{(2\pi)^{m-1}}{c_*} \cdot \pi^{-(m+4)} S \cdot \|F\|_{C^{m+4}} =: C_m \|F\|_{C^{m+4}},$$
   其中常数 $C_m = \frac{2^{m-1} S}{c_* \pi^5} < \infty$ 与 $F$ 无关。

### 论证方法二：Sobolev 嵌入定理路线
1. **Sobolev 嵌入**：因为底流形维数为 $d=2$，根据 Sobolev 嵌入定理，对任意 $\epsilon > 0$ 有 $H^{m + 1 + \epsilon}(\mathbb T^2) \hookrightarrow C^m(\mathbb T^2)$。特别取 $\epsilon = 1$，存在有限常数 $K_m$ 满足：
   $$\|u\|_{C^m} \le K_m \|u\|_{H^{m+2}}.$$
2. **逆算子估计**：由第三节结论，在 $\alpha_*$ 下 $s=1$ 成立。取 $r = m+2$，存在常数 $C_{\alpha_*, m+2, 1}$ 使得：
   $$\|u\|_{H^{m+2}} \le C_{\alpha_*, m+2, 1} \|N_{\alpha_*} u\|_{H^{m+3}} = C_{\alpha_*, m+2, 1} \|F\|_{H^{m+3}}.$$
3. **$C^k$ 对 $H^k$ 的控制**：因为 $\mathbb T^2$ 具有有限 Haar 测度 $1$，由定义：
   $$\|F\|_{H^{m+3}}^2 = \sum_{|\beta|\le m+3} \|\partial^\beta F\|_{L^2}^2 \le \sum_{|\beta|\le m+3} \|\partial^\beta F\|_{L^\infty}^2 \le \binom{m+5}{2} \|F\|_{C^{m+3}}^2.$$
   显然 $\|F\|_{C^{m+3}} \le \|F\|_{C^{m+4}}$。
4. 联立上述三式：
   $$\|N_{\alpha_*}^{-1} F\|_{C^m} \le K_m C_{\alpha_*, m+2, 1} \sqrt{\binom{m+5}{2}} \|F\|_{C^{m+4}}.$$
令 $C_m = K_m C_{\alpha_*, m+2, 1} \sqrt{\binom{m+5}{2}} < \infty$，结论得证。 $\blacksquare$
