{}
本题要求从循环单调子集 $\Gamma \subseteq E \times E'$ 及固定记录 $(\bar x, \bar y) \in \Gamma$ 出发，构造一个正规、下半连续、凸函数 $f: E \to \mathbb{R} \cup \{+\infty\}$，使其满足基准化条件 $f(\bar x) = 0$ 和次微分包含关系 $\Gamma \subseteq \partial f$，并在此类函数中实现逐点最小。这是凸分析中著名的 **Rockafellar 循环单调性定理（Rockafellar's Theorem, 1966）** 的核心构造。

下面给出势函数的完整构造、各条性质的验证、逐点最小性的证明以及关于唯一性的完整论证。

---

### 一、凸势函数 $f$ 的构造

定义指标集 $\mathcal{S}$ 为所有始于选定记录 $(\bar x, \bar y)$ 的 $\Gamma$ 中有限序列（路径）：
$$
\mathcal{S} = \bigcup_{n=0}^{\infty} \Bigl\{ \sigma = \bigl((x_0, y_0), (x_1, y_1), \dots, (x_n, y_n)\bigr) \ \Big|\ (x_0, y_0) = (\bar x, \bar y),\ (x_j, y_j) \in \Gamma\ (\forall j=1,\dots,n) \Bigr\}.
$$
对于任意序列 $\sigma = ((x_0, y_0), \dots, (x_n, y_n)) \in \mathcal{S}$，定义连续仿射函数 $L_\sigma: E \to \mathbb{R}$ 为：
$$
L_\sigma(x) = y_n(x - x_n) + \sum_{j=0}^{n-1} y_j(x_{j+1} - x_j),
$$
其中当 $n = 0$ 时，求和项为空，约定为 $0$，即：
$$
L_0(x) = y_0(x - x_0) = \bar y(x - \bar x).
$$
定义函数 $f: E \to \mathbb{R} \cup \{+\infty\}$ 为所有此类仿射函数的逐点上确界：
$$
\boxed{f(x) = \sup_{\sigma \in \mathcal{S}} L_\sigma(x) = \sup_{n \ge 0,\ (x_j, y_j) \in \Gamma \atop (x_0, y_0) = (\bar x, \bar y)} \left\{ y_n(x - x_n) + \sum_{j=0}^{n-1} y_j(x_{j+1} - x_j) \right\}.}
$$

---

### 二、构造函数的性质验证

#### 1. 凸性 (Convexity) 与下半连续性 (Lower Semicontinuity)
- **仿射性与连续性**：对任意固定的 $\sigma \in \mathcal{S}$，由于 $y_n \in E'$ 是拓扑向量空间 $E$ 上的连续实线性泛函，映射 $x \mapsto y_n(x)$ 连续，常数项 $c_\sigma = \sum_{j=0}^{n-1} y_j(x_{j+1} - x_j) - y_n(x_n) \in \mathbb{R}$，因此 $L_\sigma(x) = y_n(x) + c_\sigma$ 是 $E$ 上的连续仿射泛函。
- **凸性**：对任意 $x_1, x_2 \in E$ 及 $\lambda \in [0, 1]$，由 $L_\sigma$ 的仿射性有：
  $$
  L_\sigma(\lambda x_1 + (1-\lambda)x_2) = \lambda L_\sigma(x_1) + (1-\lambda) L_\sigma(x_2) \le \lambda f(x_1) + (1-\lambda) f(x_2).
  $$
  两端对 $\sigma \in \mathcal{S}$ 取上确界，即得：
  $$
  f(\lambda x_1 + (1-\lambda)x_2) \le \lambda f(x_1) + (1-\lambda) f(x_2),
  $$
  故 $f$ 是凸函数。
- **下半连续性**：对任意实数 $\alpha \in \mathbb{R}$，考察其下水平集：
  $$
  \{x \in E : f(x) \le \alpha\} = \bigcap_{\sigma \in \mathcal{S}} \{x \in E : L_\sigma(x) \le \alpha\}.
  $$
  因为每个 $L_\sigma$ 是连续函数，集合 $\{x \in E : L_\sigma(x) \le \alpha\}$ 是 $E$ 中的闭集。任意多个闭集的交集仍为闭集，因此 $f$ 的所有下水平集均为闭集，即 $f$ 在 $E$ 上是下半连续的。

#### 2. 基准点取值 $f(\bar x) = 0$ 与正规性 (Properness)
- **下界**：取平凡序列 $\sigma = ((\bar x, \bar y))$（即 $n = 0$），有：
  $$
  f(x) \ge L_0(x) = \bar y(x - \bar x) > -\infty \quad (\forall x \in E).
  $$
  特别地，在 $x = \bar x$ 处：
  $$
  f(\bar x) \ge L_0(\bar x) = \bar y(\bar x - \bar x) = 0.
  $$
- **上界**：对任意序列 $\sigma = ((x_0, y_0), \dots, (x_n, y_n)) \in \mathcal{S}$，在 $x = \bar x$ 处，设 $x_{n+1} = \bar x = x_0$，则：
  $$
  L_\sigma(\bar x) = y_n(\bar x - x_n) + \sum_{j=0}^{n-1} y_j(x_{j+1} - x_j) = \sum_{j=0}^{n} y_j(x_{j+1} - x_j).
  $$
  由 $\Gamma$ 的循环单调性，闭合环路上的和满足：
  $$
  \sum_{j=0}^{n} y_j(x_{j+1} - x_j) \le 0.
  $$
  因此对所有 $\sigma \in \mathcal{S}$ 均有 $L_\sigma(\bar x) \le 0$。两端取上确界得到：
  $$
  f(\bar x) = \sup_{\sigma \in \mathcal{S}} L_\sigma(\bar x) \le 0.
  $$
- 综合上下界可得：
  $$
  f(\bar x) = 0.
  $$
  由于 $f(x) > -\infty$ 对所有 $x \in E$ 成立，且在 $\bar x$ 处取有限值 $0$，故 $f$ 为正规函数。

#### 3. 在 $\pi_1(\Gamma)$ 上的有限性
对于任意 $(x, y) \in \Gamma$，我们验证 $f(x) < +\infty$：
对于任意 $\sigma = ((x_0, y_0), \dots, (x_n, y_n)) \in \mathcal{S}$，我们在末尾追加 $(x_{n+1}, y_{n+1}) = (x, y) \in \Gamma$，并令 $x_{n+2} = x_0 = \bar x$。由 $\Gamma$ 的循环单调性：
$$
\sum_{j=0}^{n+1} y_j(x_{j+1} - x_j) \le 0 \iff \sum_{j=0}^{n-1} y_j(x_{j+1} - x_j) + y_n(x - x_n) + y(\bar x - x) \le 0.
$$
即：
$$
L_\sigma(x) + y(\bar x - x) \le 0 \implies L_\sigma(x) \le y(x - \bar x).
$$
由于该上界与 $\sigma$ 的选取无关，对所有 $\sigma \in \mathcal{S}$ 取上确界得：
$$
f(x) \le y(x - \bar x) < +\infty.
$$
结合 $f(x) \ge \bar y(x - \bar x) > -\infty$，可知 $f(x) \in \mathbb{R}$。

#### 4. 次微分包含关系 $(x, y) \in \Gamma \Longrightarrow y \in \partial f(x)$
已知对任意 $(x, y) \in \Gamma$，有 $f(x) < +\infty$。需证明：
$$
\forall z \in E, \quad f(z) \ge f(x) + y(z - x).
$$
**证明**：
任取 $z \in E$。对于任意一条始于 $(\bar x, \bar y)$ 的路径 $\sigma = ((x_0, y_0), \dots, (x_n, y_n)) \in \mathcal{S}$，在其末端接上 $(x_{n+1}, y_{n+1}) = (x, y) \in \Gamma$，得到一条新的路径 $\sigma' \in \mathcal{S}$，长度为 $n+1$。
计算 $L_{\sigma'}$ 在 $z$ 处的值：
$$
\begin{aligned}
L_{\sigma'}(z) &= y_{n+1}(z - x_{n+1}) + \sum_{j=0}^{n} y_j(x_{j+1} - x_j) \\
&= y(z - x) + y_n(x - x_n) + \sum_{j=0}^{n-1} y_j(x_{j+1} - x_j) \\
&= y(z - x) + L_\sigma(x).
\end{aligned}
$$
由于 $\sigma' \in \mathcal{S}$，根据 $f(z)$ 的定义：
$$
f(z) \ge L_{\sigma'}(z) = y(z - x) + L_\sigma(x).
$$
上式对任意 $\sigma \in \mathcal{S}$ 均成立。在不等式右端对所有 $\sigma \in \mathcal{S}$ 取上确界，即得：
$$
f(z) \ge y(z - x) + \sup_{\sigma \in \mathcal{S}} L_\sigma(x) = y(z - x) + f(x).
$$
根据凸分析中次微分的定义，这确凿证明了：
$$
y \in \partial f(x).
$$

---

### 三、逐点最小性的证明 (Minimality)

设 $g: E \to \mathbb{R} \cup \{+\infty\}$ 为满足下列条件的**任意**函数：
1. $g(\bar x) = 0$；
2. 对所有 $(x, y) \in \Gamma$，有 $y \in \partial g(x)$。

我们要证明：对所有 $x \in E$，均有 $g(x) \ge f(x)$。

**证明**：
任取 $x \in E$。
任取一条序列 $\sigma = ((x_0, y_0), \dots, (x_n, y_n)) \in \mathcal{S}$，其中 $(x_0, y_0) = (\bar x, \bar y)$，且 $(x_j, y_j) \in \Gamma$。
由条件 (2)，对每个 $j = 0, 1, \dots, n$，都有 $y_j \in \partial g(x_j)$。根据次微分的定义：
$$
\forall w \in E, \quad g(w) \ge g(x_j) + y_j(w - x_j).
$$
于是我们依次写出链式不等式：
- 在 $x_n$ 处评估 $x$：
  $$g(x) \ge g(x_n) + y_n(x - x_n)$$
- 在 $x_{n-1}$ 处评估 $x_n$：
  $$g(x_n) \ge g(x_{n-1}) + y_{n-1}(x_n - x_{n-1})$$
- 依此类推，直到在 $x_0$ 处评估 $x_1$：
  $$g(x_1) \ge g(x_0) + y_0(x_1 - x_0)$$

将以上 $n+1$ 个不等式逐项相累加（由于 $g(x_j) < +\infty$ 且有限，加减运算良定）：
$$
\begin{aligned}
g(x) &\ge g(x_0) + y_0(x_1 - x_0) + y_1(x_2 - x_1) + \cdots + y_{n-1}(x_n - x_{n-1}) + y_n(x - x_n) \\
&= g(x_0) + \sum_{j=0}^{n-1} y_j(x_{j+1} - x_j) + y_n(x - x_n).
\end{aligned}
$$
代入已知基准条件 $g(x_0) = g(\bar x) = 0$，不等式右侧恰为 $L_\sigma(x)$：
$$
g(x) \ge L_\sigma(x).
$$
由于该不等式对任意给定的路径 $\sigma \in \mathcal{S}$ 都成立，在右侧对所有 $\sigma \in \mathcal{S}$ 取上确界，便得到：
$$
g(x) \ge \sup_{\sigma \in \mathcal{S}} L_\sigma(x) = f(x).
$$
因为 $x \in E$ 是任意选取的，故：
$$
g \ge f \quad \text{在 } E \text{ 上逐点成立}.
$$
因为 $f$ 自身已验证满足上述所有条件，所以 $f$ 必然是满足条件的所有函数中**逐点最小的**。

---

### 四、唯一性的完整论证 (Uniqueness)

关于唯一性，从两个层次进行完整论述：

#### 1. 逐点最小函数的唯一性
假设存在两个函数 $f_1, f_2: E \to \mathbb{R} \cup \{+\infty\}$，均满足：
- $f_i$ 是正规、下半连续、凸函数；
- $f_i(\bar x) = 0$；
- $(x, y) \in \Gamma \Longrightarrow y \in \partial f_i(x)$；
- $f_i$ 在满足上述所有条件的函数族中逐点最小。

由 $f_1$ 的逐点最小性，以及 $f_2$ 满足前三条条件，必有：
$$
f_1(x) \le f_2(x), \quad \forall x \in E.
$$
同理，由 $f_2$ 的逐点最小性，以及 $f_1$ 满足前三条条件，必有：
$$
f_2(x) \le f_1(x), \quad \forall x \in E.
$$
两式联立，立得：
$$
f_1(x) = f_2(x), \quad \forall x \in E \implies f_1 \equiv f_2.
$$
因此，**满足条件的逐点最小凸势函数在全局意义下是严格唯一的**。

#### 2. 一般满足条件函数的非唯一性与上包络
若去掉“逐点最小”的要求，仅满足 $g(\bar x)=0$ 且 $\Gamma \subseteq \partial g$ 的正规下半连续凸函数**一般不唯一**。
- **反例说明**：取 $E = \mathbb{R}$，$E' = \mathbb{R}$，$\Gamma = \{(0, 0)\}$，基准点 $(\bar x, \bar y) = (0, 0)$。
  条件为 $g(0) = 0$ 且 $0 \in \partial g(0)$。
  - 按上述构造得到的最小势函数为：$f(x) \equiv 0$；
  - 但函数 $g_1(x) = |x|$、$g_2(x) = x^2$ 乃至指示函数 $g_3(x) = \begin{cases} 0, & x = 0 \\ +\infty, & x \ne 0 \end{cases}$ 均为满足该条件的正规、下半连续凸函数，且均严格大于 $f$。
- **上界包络函数**：事实上，所有满足条件的函数 $g$ 不仅有下确界包络 $f_{\min} = f$，还存在一个逐点最大函数 $f_{\max}$（可通过对偶理论或反向链构造）：
  $$
  f(x) \le g(x) \le f_{\max}(x), \quad \forall x \in E.
  $$

#### 3. 势函数完全唯一的充要情形（极大循环单调性）
由 Rockafellar 定理，若 $\Gamma$ 进一步是**极大循环单调的**（Maximal Cyclically Monotone），则：
$$
\Gamma = \partial f,
$$
即 $\Gamma$ 完整地构成了凸函数 $f$ 的次微分图。在适当的连通性/支撑条件下（例如 $E$ 为赋范空间且 $\operatorname{dom} f$ 具内部），由次微分所确定的凸函数在相差一个常数的意义下是唯一的。此时附加条件 $f(\bar x) = 0$ 将常数唯一固定，从而使满足条件的所有正规下半连续凸函数全部重合于 $f$。
