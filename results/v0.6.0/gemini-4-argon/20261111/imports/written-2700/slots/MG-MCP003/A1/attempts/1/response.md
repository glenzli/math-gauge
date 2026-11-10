基于 **CH1 扩展规范空间** $(\mathcal{X}, \mathcal{G}, \bot)$ 与**算子空间** $\mathcal{X}_{\mathrm{op}}$ 的公理体系，下面将你提出的四个核心想法——**分量关系的矩阵化表示**、**上下界（Lipschitz 与逆向膨胀下界）的对偶估计**、**在 $\bar{\mathbb{R}}_+ = [0, +\infty]$ 上的统一扩展（支持 $+\infty$）**，以及**输入落入一定范畴时输出不可区分的对等矩阵刻画**——整理为一套自洽、严密的数学定义与基本性质体系，并给出完整论证。

---

## 一、 预备约定与距离向量

设 $(\mathcal{X}, \mathcal{G}, \bot)$ 为扩展规范空间，其中 $\mathcal{G} = \{d_i\}_{i \in I}$，$I$ 为有限非空指标集（记 $|I| = n$）。

### 1.1 完备格 $\bar{\mathbb{R}}_+$ 上的算术与伴随商
在 $\bar{\mathbb{R}}_+ = [0, +\infty]$ 上，除 CH1 约定的扩展算术（$a + (+\infty) = +\infty$，$0 \cdot (+\infty) = 0$，$a \cdot (+\infty) = +\infty\ (a>0)$）外，赋予标准全序 $\le$。此时 $(\bar{\mathbb{R}}_+, \le)$ 构成完备格，其空集确界按标准格论约定为：

$$\inf \emptyset = +\infty, \qquad \sup \emptyset = 0.$$

> **注记（乘法对任意上确界的保持性）**：在 $0 \cdot (+\infty) = 0$ 约定下，对任意固定的 $d \in \bar{\mathbb{R}}_+$，映射 $c \mapsto c \cdot d$ 在 $\bar{\mathbb{R}}_+$ 上单调递增且保持任意上确界，即 $\sup_{c \in S}(c \cdot d) = (\sup S) \cdot d$；同时 $\bar{\mathbb{R}}_+$ 上的乘法满足结合律 $(a \cdot b) \cdot c = a \cdot (b \cdot c)$ 及对加法的分配律 $a \cdot (b + c) = a \cdot b + a \cdot c$。

为统一处理比例估计中的零距与无穷距，对任意 $\alpha, \beta \in \bar{\mathbb{R}}_+$，由乘法诱导其**上扩展商** $\rho^+(\alpha, \beta)$ 与**下扩展商** $\rho^-(\alpha, \beta)$：

$$\rho^+(\alpha, \beta) := \inf\bigl\{\, c \in \bar{\mathbb{R}}_+ \;\big|\; \alpha \le c \cdot \beta \,\bigr\}, \qquad \rho^-(\alpha, \beta) := \sup\bigl\{\, c \in \bar{\mathbb{R}}_+ \;\big|\; c \cdot \beta \le \alpha \,\bigr\}.$$

当 $0 < \alpha, \beta < +\infty$ 时，二者均退化为普通实数商 $\alpha / \beta$；而在边界处（如 $\alpha = \beta = 0$），自动给出 $\rho^+(0, 0) = 0$（对 $\sup$ 为中性元）与 $\rho^-(0, 0) = +\infty$（对 $\inf$ 为中性元）。

### 1.2 距离向量与有效定义域限制
**定义 1.1（规范距离向量与矩阵偏序）**：
对任意 $x, y \in \mathcal{X}$，定义其**距离向量**为：

$$\mathbf{d}(x, y) := \bigl(d_i(x, y)\bigr)_{i \in I} \in \bar{\mathbb{R}}_+^I.$$

在向量空间 $\bar{\mathbb{R}}_+^I$ 与矩阵空间 $\bar{\mathbb{R}}_+^{I \times I}$ 上赋予逐分量偏序 $\preceq$：

$$\mathbf{u} \preceq \mathbf{v} \iff \forall\, i \in I,\; u_i \le v_i; \qquad A \preceq B \iff \forall\, i, j \in I,\; A_{ij} \le B_{ij}.$$

> **重要说明（为何算子度量特征定义在 $\mathrm{dom}(\phi)$ 上）**：
> 对 $\phi \in \mathcal{X}_{\mathrm{op}}$，若 $x \in \mathrm{dom}(\phi)$ 而 $y \notin \mathrm{dom}(\phi)$（且 $y \neq \bot$），由吸收元隔离公理 (iv) 有 $d_i(\phi(x), \phi(y)) = d_i(\phi(x), \bot) = +\infty$，但 $d_j(x, y)$ 可以有限；若 $x, y \notin \mathrm{dom}(\phi)$，则 $d_i(\phi(x), \phi(y)) = d_i(\bot, \bot) = 0$。因此，算子的几何估计天然建立在其有效定义域 $\mathrm{dom}(\phi) = \{x \in \mathcal{X} \mid \phi(x) \neq \bot\}$ 上（若需局部估计，可将下述定义中的 $\mathrm{dom}(\phi)$ 替换为任意子集 $D \subseteq \mathrm{dom}(\phi)$）。

---

## 二、 核心定义：算子的三类对等特征矩阵

在多伪度量场景下，刻画算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 各分量间的关系有两个自然且互补的层级：
1. **逐分量典型特征矩阵（Canonical Componentwise Matrices）**：直接度量第 $j$ 输入分量对第 $i$ 输出分量的独立极值控制，使**每一个**算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 都唯一对应三个 $\bar{\mathbb{R}}_+^{I \times I}$ 中的标准矩阵；
2. **联合矩阵-向量控制（Joint Matrix-Vector Control）**：通过矩阵-向量乘法描述多输入分量对输出分量的线性组合协同控制。

下面先给出核心的逐分量对等矩阵定义，再给出联合控制形式。约定矩阵行指标 $i \in I$ 对应**输出分量**，列指标 $j \in I$ 对应**输入分量**（以保证算子复合对应矩阵乘法顺序）。

### 2.1 上 Lipschitz 矩阵、下 Lipschitz 矩阵与不可区分阈矩阵

**定义 2.1（上 Lipschitz 矩阵 / 膨胀上界矩阵）**：
设 $\phi \in \mathcal{X}_{\mathrm{op}}$。定义 $\phi$ 的**上 Lipschitz 矩阵** $L^+(\phi) = \bigl(L^+_{ij}(\phi)\bigr)_{i, j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$，其 $(i, j)$ 元为：

$$L^+_{ij}(\phi) := \inf \Bigl\{\, c \in \bar{\mathbb{R}}_+ \;\Big|\; \forall\, x, y \in \mathrm{dom}(\phi),\; d_i(\phi(x), \phi(y)) \le c \cdot d_j(x, y) \,\Bigr\}.$$

当集合非空且 $L^+_{ij}(\phi) < +\infty$ 时，称输出分量 $i$ 关于输入分量 $j$ 是**上 Lipschitz 受控的**；若不存在有限常数 $c$ 满足上式，则由完备格约定自动有 $L^+_{ij}(\phi) = +\infty$。

**定义 2.2（下 Lipschitz 矩阵 / 膨胀下界矩阵）**：
设 $\phi \in \mathcal{X}_{\mathrm{op}}$。定义 $\phi$ 的**下 Lipschitz 矩阵**（或 **co-Lipschitz 矩阵**）$L^-(\phi) = \bigl(L^-_{ij}(\phi)\bigr)_{i, j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$，其 $(i, j)$ 元为：

$$L^-_{ij}(\phi) := \sup \Bigl\{\, c \in \bar{\mathbb{R}}_+ \;\Big|\; \forall\, x, y \in \mathrm{dom}(\phi),\; c \cdot d_j(x, y) \le d_i(\phi(x), \phi(y)) \,\Bigr\}.$$

> **注**：因 $c = 0$ 恒满足 $0 \cdot d_j(x, y) = 0 \le d_i(\phi(x), \phi(y))$，上述集合恒非空，且 $L^-_{ij}(\phi) \in [0, +\infty]$。当 $L^-_{ij}(\phi) > 0$ 时，输出分量 $i$ 对输入分量 $j$ 具有非退化的可区分保持（逆压缩）能力。

**定义 2.3（不可区分阈矩阵 / 零化半径矩阵）**：
设 $\phi \in \mathcal{X}_{\mathrm{op}}$。在规范空间中（不预设族分离性），两点 $u, v \in \mathcal{X}$ 在第 $i$ 分量下**不可区分**是指 $d_i(u, v) = 0$。定义 $\phi$ 的**不可区分阈矩阵** $\Theta(\phi) = \bigl(\Theta_{ij}(\phi)\bigr)_{i, j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$，其 $(i, j)$ 元为：

$$\Theta_{ij}(\phi) := \sup \Bigl\{\, r \in \bar{\mathbb{R}}_+ \;\Big|\; \forall\, x, y \in \mathrm{dom}(\phi),\; d_j(x, y) < r \implies d_i(\phi(x), \phi(y)) = 0 \,\Bigr\}.$$

$\Theta_{ij}(\phi)$ 刻画了从输入分量 $j$ 到输出分量 $i$ 的**不可区分范畴（死区/分辨率阈值）**：只要输入对 $x, y \in \mathrm{dom}(\phi)$ 在第 $j$ 分量上的距离落入范畴 $[0, \Theta_{ij}(\phi))$，其输出在第 $i$ 分量下即不可区分（$d_i(\phi(x), \phi(y)) = 0$）。

---

### 2.2 三类矩阵的对等性综述

将定义 2.1、2.2、2.3 并列，可以清晰看到三者在数学结构上的严格对等性：

| 特征矩阵 | 符号与取值空间 | 定义核心约束（$\forall\, x, y \in \mathrm{dom}(\phi)$） | 极值方向 | 几何/分析意义 |
| :--- | :--- | :--- | :--- | :--- |
| **上 Lipschitz 矩阵** | $L^+(\phi) \in \bar{\mathbb{R}}_+^{I \times I}$ | $d_i(\phi(x), \phi(y)) \le c \cdot d_j(x, y)$ | $\inf c$ | 距离膨胀速率**上限**（连续性/稳定性度规） |
| **下 Lipschitz 矩阵** | $L^-(\phi) \in \bar{\mathbb{R}}_+^{I \times I}$ | $c \cdot d_j(x, y) \le d_i(\phi(x), \phi(y))$ | $\sup c$ | 距离保持速率**下限**（可逆性/扩张性度规） |
| **不可区分阈矩阵** | $\Theta(\phi) \in \bar{\mathbb{R}}_+^{I \times I}$ | $d_j(x, y) < r \implies d_i(\phi(x), \phi(y)) = 0$ | $\sup r$ | 输出坍缩为零距的**输入范畴半径**（分辨率/死区度规） |

---

### 2.3 联合矩阵-向量控制形式（多分量协同形式）

当算子 $\phi$ 的输出分量 $i$ 同时依赖多个输入分量时，单一输入分量 $d_j(x, y)$ 为零未必能阻止其余分量驱动 $d_i(\phi(x), \phi(y)) > 0$。为此，对等地引入矩阵-向量联合控制类：

**定义 2.4（联合上下界控制矩阵类与联合不可区分矩阵类）**：
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，对矩阵 $M^+, M^-, R \in \bar{\mathbb{R}}_+^{I \times I}$：
1. **联合上 Lipschitz 矩阵类** $\mathcal{M}^+(\phi)$：称 $M^+ \in \mathcal{M}^+(\phi)$，若
   $$\forall\, x, y \in \mathrm{dom}(\phi), \quad \mathbf{d}(\phi(x), \phi(y)) \preceq M^+ \mathbf{d}(x, y), \quad \text{即} \quad d_i(\phi(x), \phi(y)) \le \sum_{j \in I} M^+_{ij} \, d_j(x, y) \;\; (\forall\, i \in I).$$
2. **联合下 Lipschitz 矩阵类** $\mathcal{M}^-(\phi)$：称 $M^- \in \mathcal{M}^-(\phi)$，若
   $$\forall\, x, y \in \mathrm{dom}(\phi), \quad M^- \mathbf{d}(x, y) \preceq \mathbf{d}(\phi(x), \phi(y)), \quad \text{即} \quad \sum_{j \in I} M^-_{ij} \, d_j(x, y) \le d_i(\phi(x), \phi(y)) \;\; (\forall\, i \in I).$$
3. **联合不可区分阈矩阵类** $\mathcal{R}(\phi)$：称 $R \in \mathcal{R}(\phi)$，若
   $$\forall\, i \in I,\; \forall\, x, y \in \mathrm{dom}(\phi), \quad \bigl(\forall\, j \in I,\; d_j(x, y) < R_{ij}\bigr) \implies d_i(\phi(x), \phi(y)) = 0.$$

---

## 三、 基本性质与严格论证

### 性质 1：完备格上的对偶商表示与最优界可达性

**定理 3.1（对偶刻画与可达性定理）**：
对任意算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 及任意 $(i, j) \in I \times I$，矩阵元 $L^+_{ij}(\phi), L^-_{ij}(\phi), \Theta_{ij}(\phi) \in \bar{\mathbb{R}}_+$ 恒良定义，且具有如下对偶表出与可达性质：

**(1) 上下 Lipschitz 矩阵的扩展商表出**：

$$L^+_{ij}(\phi) = \sup_{x, y \in \mathrm{dom}(\phi)} \rho^+\bigl(d_i(\phi(x), \phi(y)),\, d_j(x, y)\bigr), \qquad L^-_{ij}(\phi) = \inf_{x, y \in \mathrm{dom}(\phi)} \rho^-\bigl(d_i(\phi(x), \phi(y)),\, d_j(x, y)\bigr).$$

**(2) 下 Lipschitz 界的无条件可达性**：
对任意 $\phi \in \mathcal{X}_{\mathrm{op}}$ 及任意 $x, y \in \mathrm{dom}(\phi)$，最优下界常数 $L^-_{ij}(\phi)$ **恒可达**：

$$L^-_{ij}(\phi) \cdot d_j(x, y) \le d_i(\phi(x), \phi(y)).$$

**(3) 上 Lipschitz 界的可达性与 $0 \cdot (+\infty) = 0$ 的边界二分性**：
- 当 $0 < L^+_{ij}(\phi) < +\infty$ 时，对任意 $x, y \in \mathrm{dom}(\phi)$，最优上界恒可达：
  $$d_i(\phi(x), \phi(y)) \le L^+_{ij}(\phi) \cdot d_j(x, y).$$
- 当 $L^+_{ij}(\phi) = 0$ 时，对一切满足 $d_j(x, y) < +\infty$ 的 $x, y \in \mathrm{dom}(\phi)$ 均有 $d_i(\phi(x), \phi(y)) = 0$；而在 $d_j(x, y) = +\infty$ 处，因 $0 \cdot (+\infty) = 0$，不等式 $d_i(\phi(x), \phi(y)) \le 0 \cdot d_j(x, y)$ 成立当且仅当 $d_i(\phi(x), \phi(y)) = 0$。
- 当 $L^+_{ij}(\phi) = +\infty$ 时，存在两种子情形：
  - **保零无界型**：$\phi$ 满足 $(i, j)$-保零性（即 $d_j(x, y) = 0 \implies d_i(\phi(x), \phi(y)) = 0$），此时 $c = +\infty$ 满足 $d_i(\phi(x), \phi(y)) \le (+\infty) \cdot d_j(x, y)$；
  - **破零发散型**：存在 $x, y \in \mathrm{dom}(\phi)$ 使得 $d_j(x, y) = 0$ 但 $d_i(\phi(x), \phi(y)) > 0$。此时因 $(+\infty) \cdot 0 = 0 < d_i(\phi(x), \phi(y))$，没有任何 $c \in \bar{\mathbb{R}}_+$ 满足不等式，由 $\inf \emptyset = +\infty$ 统一赋予 $L^+_{ij}(\phi) = +\infty$。

**(4) 不可区分阈矩阵的三种等价表出与可达性**：
$\Theta_{ij}(\phi)$ 恒满足如下三个恒等式：

$$\begin{aligned}
\Theta_{ij}(\phi) &= \sup \Bigl\{\, r \in \bar{\mathbb{R}}_+ \;\Big|\; \forall\, x, y \in \mathrm{dom}(\phi),\; d_j(x, y) < r \implies d_i(\phi(x), \phi(y)) = 0 \,\Bigr\} \\
&= \sup \Bigl\{\, r \in \bar{\mathbb{R}}_+ \;\Big|\; \forall\, x, y \in \mathrm{dom}(\phi),\; d_j(x, y) \le r \implies d_i(\phi(x), \phi(y)) = 0 \,\Bigr\} \\
&= \inf \Bigl\{\, d_j(x, y) \;\Big|\; x, y \in \mathrm{dom}(\phi),\; d_i(\phi(x), \phi(y)) > 0 \,\Bigr\},
\end{aligned}$$

且严格阈值蕴含式恒可达：对一切 $x, y \in \mathrm{dom}(\phi)$，只要 $d_j(x, y) < \Theta_{ij}(\phi)$，必有 $d_i(\phi(x), \phi(y)) = 0$。

**证明**：
1. 对每对 $(x, y) \in \mathrm{dom}(\phi)^2$，记 $U_{x, y} = \{c \in \bar{\mathbb{R}}_+ \mid d_i(\phi(x), \phi(y)) \le c \cdot d_j(x, y)\}$。由乘法单调性，$U_{x, y}$ 为 $\bar{\mathbb{R}}_+$ 中的向上闭区间（或空集），且 $\inf U_{x, y} = \rho^+(d_i(\phi(x), \phi(y)), d_j(x, y))$。在完备格 $[0, +\infty]$ 中，任意一族向上闭区间之交的下确界等于各区间下确界的上确界，故 $L^+_{ij}(\phi) = \inf \bigcap_{x, y} U_{x, y} = \sup_{x, y} \inf U_{x, y}$。同理，由 $c \mapsto c \cdot d_j(x, y)$ 保任意上确界，$L_{x, y} = \{c \in \bar{\mathbb{R}}_+ \mid c \cdot d_j(x, y) \le d_i(\phi(x), \phi(y))\} = [0, \rho^-(d_i(\phi(x), \phi(y)), d_j(x, y))]$，故 $L^-_{ij}(\phi) = \sup \bigcap_{x, y} L_{x, y} = \inf_{x, y} \rho^-(d_i(\phi(x), \phi(y)), d_j(x, y))$，且上确界在交集中恒取到，这证明了 (1) 与 (2)。
2. 对 (3)，当 $0 < L^+_{ij}(\phi) < +\infty$ 时，取 $c_n = L^+_{ij}(\phi) + 1/n$，对 $d_j(x, y) < +\infty$ 令 $n \to \infty$ 即得 $d_i(\phi(x), \phi(y)) \le L^+_{ij}(\phi) \cdot d_j(x, y)$；对 $d_j(x, y) = +\infty$，因 $L^+_{ij}(\phi) > 0$，右端为 $L^+_{ij}(\phi) \cdot (+\infty) = +\infty$，不等式亦成立。边界情形 $L^+_{ij}(\phi) \in \{0, +\infty\}$ 直接由 $0 \cdot (+\infty) = 0$ 验证。
3. 对 (4)，记 $m := \inf \{ d_j(x, y) \mid x, y \in \mathrm{dom}(\phi),\ d_i(\phi(x), \phi(y)) > 0 \}$。由逆否命题：
   $$\bigl(\forall\, x, y \in \mathrm{dom}(\phi),\; d_j(x, y) < r \implies d_i(\phi(x), \phi(y)) = 0\bigr) \iff \bigl(\forall\, x, y \in \mathrm{dom}(\phi),\; d_i(\phi(x), \phi(y)) > 0 \implies d_j(x, y) \ge r\bigr) \iff r \le m.$$
   故严格不等式对应的可行集恰为闭区间 $S_< = [0, m]$，其最大值即为 $\sup S_< = m$，且 $r = m$ 自身属于 $S_<$。对于非严格不等式可行集 $S_\le$，$r \in S_\le \iff (\forall\, d_i(\phi(x), \phi(y)) > 0 \implies d_j(x, y) > r)$，故 $[0, m) \subseteq S_\le \subseteq [0, m]$。在 $\bar{\mathbb{R}}_+$ 中无论 $m = 0$（$\sup \emptyset = 0$）还是 $m > 0$，均有 $\sup S_\le = \sup [0, m) = m = \sup S_<$。证毕。 $\blacksquare$

---

### 性质 2：上下界序关系与三类矩阵间的制约关系

**定理 3.2（基本序关系与三矩阵互制约原理）**：
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，对任意 $(i, j) \in I \times I$：

**(1) 上下界相容性**：
若存在 $x, y \in \mathrm{dom}(\phi)$ 使得 $0 < d_j(x, y) < +\infty$，则必有：

$$0 \le L^-_{ij}(\phi) \le L^+_{ij}(\phi) \le +\infty.$$

（注：仅当 $\mathrm{dom}(\phi)$ 上 $d_j$ 只取值于 $\{0, +\infty\}$ 等退化情形时，才可能出现 $L^+_{ij}(\phi) = 0 < L^-_{ij}(\phi) = +\infty$，例如 $|\mathrm{dom}(\phi)| \le 1$。）

**(2) 下 Lipschitz 界与不可区分阈的互斥性（可分保持 vs. 零化坍缩）**：
- 若在不可区分范畴内存在正距离输入对，即存在 $x, y \in \mathrm{dom}(\phi)$ 使得 $0 < d_j(x, y) < \Theta_{ij}(\phi)$，则必有：
  $$L^-_{ij}(\phi) = 0.$$
- 对偶地，若 $L^-_{ij}(\phi) > 0$，则对一切满足 $d_j(x, y) > 0$ 的 $x, y \in \mathrm{dom}(\phi)$ 均有 $d_i(\phi(x), \phi(y)) > 0$，从而：
  $$\Theta_{ij}(\phi) = \inf\bigl\{\, d_j(x, y) \;\big|\; x, y \in \mathrm{dom}(\phi),\; d_j(x, y) > 0 \,\bigr\}$$
  （即 $\Theta_{ij}(\phi)$ 退化为输入伪度量 $d_j$ 自身在 $\mathrm{dom}(\phi)$ 上的最小正距离间隙；若 $d_j$ 可取任意小正值，则 $\Theta_{ij}(\phi) = 0$）。

**(3) 输出最小可分步长不等式**：
对任意 $x, y \in \mathrm{dom}(\phi)$，只要输出在第 $i$ 分量下可区分（即 $d_i(\phi(x), \phi(y)) > 0$），则必有：

$$d_i(\phi(x), \phi(y)) \ge \max_{j \in I} \bigl( L^-_{ij}(\phi) \cdot \Theta_{ij}(\phi) \bigr).$$

**(4) 有限有界算子的上 Lipschitz 界与不可区分阈关系**：
若输出分量 $i$ 在 $\mathrm{dom}(\phi)$ 上的直径 $D_i(\phi) := \sup_{x, y \in \mathrm{dom}(\phi)} d_i(\phi(x), \phi(y)) < +\infty$，且 $\Theta_{ij}(\phi) > 0$，则：

$$L^+_{ij}(\phi) \le \frac{D_i(\phi)}{\Theta_{ij}(\phi)}.$$

**(5) 全局不可区分与零上界等价性**：
$\Theta_{ij}(\phi) = +\infty$ 当且仅当对一切满足 $d_j(x, y) < +\infty$ 的 $x, y \in \mathrm{dom}(\phi)$ 均有 $d_i(\phi(x), \phi(y)) = 0$；此时必有 $L^+_{ij}(\phi) = 0$。

**证明**：
- **(1)**：取 $x_0, y_0 \in \mathrm{dom}(\phi)$ 使 $0 < d_j(x_0, y_0) < +\infty$。由定理 3.1(1)，当 $d_i(\phi(x_0), \phi(y_0)) < +\infty$ 时，$\rho^-(d_i(\phi(x_0), \phi(y_0)), d_j(x_0, y_0)) = \frac{d_i(\phi(x_0), \phi(y_0))}{d_j(x_0, y_0)} = \rho^+(d_i(\phi(x_0), \phi(y_0)), d_j(x_0, y_0))$；当 $d_i(\phi(x_0), \phi(y_0)) = +\infty$ 时，二者皆为 $+\infty$。故 $L^-_{ij}(\phi) \le \rho^- = \rho^+ \le L^+_{ij}(\phi)$。
- **(2)**：若存在 $x, y \in \mathrm{dom}(\phi)$ 使 $0 < d_j(x, y) < \Theta_{ij}(\phi)$，由定理 3.1(4) 知 $d_i(\phi(x), \phi(y)) = 0$。再由定理 3.1(2) 知 $L^-_{ij}(\phi) \cdot d_j(x, y) \le 0$。因 $d_j(x, y) > 0$，必有 $L^-_{ij}(\phi) = 0$。反之，若 $L^-_{ij}(\phi) > 0$，则 $d_j(x, y) > 0 \implies d_i(\phi(x), \phi(y)) \ge L^-_{ij}(\phi) \cdot d_j(x, y) > 0$，从而 $\{ (x, y) \mid d_i(\phi(x), \phi(y)) > 0 \} \supseteq \{ (x, y) \mid d_j(x, y) > 0 \}$；又因 $d_i(\phi(x), \phi(y)) = 0 \implies d_j(x, y) = 0$，两集合相等，取 $d_j$ 的下确界即得结论。
- **(3)**：若 $d_i(\phi(x), \phi(y)) > 0$，由定理 3.1(4) 的下确界表出，对任意 $j \in I$ 有 $d_j(x, y) \ge \Theta_{ij}(\phi)$。结合定理 3.1(2) 及乘法单调性：
  $$d_i(\phi(x), \phi(y)) \ge L^-_{ij}(\phi) \cdot d_j(x, y) \ge L^-_{ij}(\phi) \cdot \Theta_{ij}(\phi).$$
  对 $j \in I$ 取最大值即得。
- **(4)**：对任意 $x, y \in \mathrm{dom}(\phi)$，若 $d_i(\phi(x), \phi(y)) = 0$，则 $d_i(\phi(x), \phi(y)) \le \frac{D_i(\phi)}{\Theta_{ij}(\phi)} d_j(x, y)$ 显然成立；若 $d_i(\phi(x), \phi(y)) > 0$，则 $d_j(x, y) \ge \Theta_{ij}(\phi) > 0$，从而 $d_i(\phi(x), \phi(y)) \le D_i(\phi) \le \frac{D_i(\phi)}{\Theta_{ij}(\phi)} d_j(x, y)$。故 $L^+_{ij}(\phi) \le \frac{D_i(\phi)}{\Theta_{ij}(\phi)}$。
- **(5)**：由 $\Theta_{ij}(\phi) = \inf \{ d_j(x, y) \mid d_i(\phi(x), \phi(y)) > 0 \} = +\infty$ 知，凡满足 $d_j(x, y) < +\infty$ 的点对必不满足 $d_i(\phi(x), \phi(y)) > 0$，即 $d_i(\phi(x), \phi(y)) = 0$。此时对任意 $c > 0$ 及任意 $x, y \in \mathrm{dom}(\phi)$，当 $d_j(x, y) < +\infty$ 时 $0 \le c \cdot d_j(x, y)$，当 $d_j(x, y) = +\infty$ 时 $d_i(\phi(x), \phi(y)) \le +\infty = c \cdot (+\infty)$，故一切 $c > 0$ 皆为上界，取下确界得 $L^+_{ij}(\phi) = 0$。证毕。 $\blacksquare$

---

### 性质 3：逐分量特征矩阵与联合控制矩阵类的联系

**定理 3.3（逐分量矩阵与联合控制类的转换关系）**：
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$|I| = n$：
1. **上界嵌入**：若 $L^+(\phi)$ 满足对每个 $i, j$ 及 $x, y \in \mathrm{dom}(\phi)$ 有 $d_i(\phi(x), \phi(y)) \le L^+_{ij}(\phi) d_j(x, y)$（例如 $L^+_{ij}(\phi) \in (0, +\infty)$），则 $\frac{1}{n} L^+(\phi) \in \mathcal{M}^+(\phi)$ 且 $L^+(\phi) \in \mathcal{M}^+(\phi)$。
2. **下界刻画**：联合下界矩阵类 $\mathcal{M}^-(\phi)$ 中的任意矩阵 $M^-$ 均受逐分量下界矩阵 $L^-(\phi)$ 控制，且 $\frac{1}{n} L^-(\phi) \in \mathcal{M}^-(\phi)$：
   $$M^- \in \mathcal{M}^-(\phi) \implies M^- \preceq L^-(\phi), \qquad \frac{1}{n} L^-(\phi) \in \mathcal{M}^-(\phi).$$
3. **不可区分阈嵌入**：典型不可区分阈矩阵恒属于联合不可区分矩阵类，即 $\Theta(\phi) \in \mathcal{R}(\phi)$。

**证明**：
1. 对每个 $i \in I$，将 $d_i(\phi(x), \phi(y)) \le L^+_{ij}(\phi) d_j(x, y)$ 对 $j \in I$ 求和再除以 $n$，即得 $d_i(\phi(x), \phi(y)) \le \sum_{j \in I} \frac{1}{n} L^+_{ij}(\phi) d_j(x, y)$。
2. 若 $M^- \in \mathcal{M}^-(\phi)$，则对任意固定的 $(i, j) \in I \times I$ 及 $x, y \in \mathrm{dom}(\phi)$，由 $\bar{\mathbb{R}}_+$ 非负性有 $M^-_{ij} d_j(x, y) \le \sum_{k \in I} M^-_{ik} d_k(x, y) \le d_i(\phi(x), \phi(y))$，依定义 2.2 知 $M^-_{ij} \le L^-_{ij}(\phi)$。反之，将定理 3.1(2) 的 $L^-_{ij}(\phi) d_j(x, y) \le d_i(\phi(x), \phi(y))$ 对 $j \in I$ 求和除以 $n$，即得 $\frac{1}{n} L^-(\phi) \in \mathcal{M}^-(\phi)$。
3. 若对所有 $j \in I$ 有 $d_j(x, y) < \Theta_{ij}(\phi)$，任取一个 $j \in I$，由定理 3.1(4) 即得 $d_i(\phi(x), \phi(y)) = 0$，故 $\Theta(\phi) \in \mathcal{R}(\phi)$。证毕。 $\blacksquare$

---

### 性质 4：算子复合下的矩阵传递律（半环与矩阵代数结构）

在 $\mathcal{X}_{\mathrm{op}}$ 上考虑算子复合 $\psi \circ \phi$。首先注意 CH1 吸收元不变条件 $\psi(\bot) = \bot$ 的关键作用：

**引理 3.4（复合定义域相容性）**：
对任意 $\phi, \psi \in \mathcal{X}_{\mathrm{op}}$，有 $\psi \circ \phi \in \mathcal{X}_{\mathrm{op}}$，且

$$\mathrm{dom}(\psi \circ \phi) = \bigl\{\, x \in \mathrm{dom}(\phi) \;\big|\; \phi(x) \in \mathrm{dom}(\psi) \,\bigr\} \subseteq \mathrm{dom}(\phi).$$

**证明**：$(\psi \circ \phi)(\bot) = \psi(\phi(\bot)) = \psi(\bot) = \bot$，故 $\psi \circ \phi \in \mathcal{X}_{\mathrm{op}}$。若 $x \in \mathrm{dom}(\psi \circ \phi)$，则 $\psi(\phi(x)) \neq \bot$，故 $\phi(x) \in \mathrm{dom}(\psi)$；又因 $\psi(\bot) = \bot$，必有 $\phi(x) \neq \bot$，即 $x \in \mathrm{dom}(\phi)$。 $\blacksquare$

**定理 3.5（复合算子的矩阵传递律）**：
设 $\phi, \psi \in \mathcal{X}_{\mathrm{op}}$：

**(1) 逐分量特征矩阵的热带（Min-Times / Max-Times）传递律**：
对任意 $m, k \in I$：
- **下 Lipschitz 矩阵（无条件成立）**：
  $$L^-_{mk}(\psi \circ \phi) \ge \max_{i \in I} \bigl( L^-_{mi}(\psi) \cdot L^-_{ik}(\phi) \bigr).$$
- **上 Lipschitz 矩阵**：若对中间指标 $i \in I$，上界不等式对 $\psi$（关于 $(m, i)$）和 $\phi$（关于 $(i, k)$）可达（例如 $L^+_{mi}(\psi), L^+_{ik}(\phi) \in (0, +\infty)$，或满足保零性），则：
  $$L^+_{mk}(\psi \circ \phi) \le L^+_{mi}(\psi) \cdot L^+_{ik}(\phi);$$
  若对所有 $i \in I$ 可达，则 $L^+_{mk}(\psi \circ \phi) \le \min_{i \in I} \bigl( L^+_{mi}(\psi) \cdot L^+_{ik}(\phi) \bigr)$。
- **不可区分阈矩阵**：对任意满足 $L^+_{ik}(\phi) \in (0, +\infty)$ 的中间指标 $i \in I$，有：
  $$\Theta_{mk}(\psi \circ \phi) \ge \frac{\Theta_{mi}(\psi)}{L^+_{ik}(\phi)};$$
  若进一步 $\Theta_{mi}(\psi) > 0$（或 $\psi$ 关于 $(m, i)$ 保零），则同时有 $\Theta_{mk}(\psi \circ \phi) \ge \Theta_{ik}(\phi)$，从而：
  $$\Theta_{mk}(\psi \circ \phi) \ge \max\Biggl(\Theta_{ik}(\phi),\; \frac{\Theta_{mi}(\psi)}{L^+_{ik}(\phi)}\Biggr).$$

**(2) 联合控制矩阵的标准矩阵乘法传递律**：
- 若 $M^+(\phi) \in \mathcal{M}^+(\phi)$ 且 $M^+(\psi) \in \mathcal{M}^+(\psi)$，则标准矩阵乘积 $M^+(\psi) M^+(\phi) \in \mathcal{M}^+(\psi \circ \phi)$：
  $$\mathbf{d}\bigl((\psi \circ \phi)(x), (\psi \circ \phi)(y)\bigr) \preceq \bigl(M^+(\psi) M^+(\phi)\bigr) \mathbf{d}(x, y), \quad \forall\, x, y \in \mathrm{dom}(\psi \circ \phi).$$
- 若 $M^-(\phi) \in \mathcal{M}^-(\phi)$ 且 $M^-(\psi) \in \mathcal{M}^-(\psi)$，则标准矩阵乘积 $M^-(\psi) M^-(\phi) \in \mathcal{M}^-(\psi \circ \phi)$：
  $$\bigl(M^-(\psi) M^-(\phi)\bigr) \mathbf{d}(x, y) \preceq \mathbf{d}\bigl((\psi \circ \phi)(x), (\psi \circ \phi)(y)\bigr), \quad \forall\, x, y \in \mathrm{dom}(\psi \circ \phi).$$

**证明**：
1. 任取 $x, y \in \mathrm{dom}(\psi \circ \phi)$，由引理 3.4 知 $x, y \in \mathrm{dom}(\phi)$ 且 $u := \phi(x), v := \phi(y) \in \mathrm{dom}(\psi)$。
2. 对 $L^-$，由定理 3.1(2) 及 $\bar{\mathbb{R}}_+$ 乘法单调性与结合律，对任意 $i \in I$：
   $$d_m(\psi(u), \psi(v)) \ge L^-_{mi}(\psi) \cdot d_i(\phi(x), \phi(y)) \ge L^-_{mi}(\psi) \cdot \bigl(L^-_{ik}(\phi) \cdot d_k(x, y)\bigr) = \bigl(L^-_{mi}(\psi) \cdot L^-_{ik}(\phi)\bigr) \cdot d_k(x, y).$$
   故 $L^-_{mk}(\psi \circ \phi) \ge L^-_{mi}(\psi) \cdot L^-_{ik}(\phi)$，对 $i \in I$ 取最大值即得。$L^+$ 的证明完全同理。
3. 对 $\Theta$，设 $0 < L^+_{ik}(\phi) < +\infty$。若 $d_k(x, y) < \frac{\Theta_{mi}(\psi)}{L^+_{ik}(\phi)}$，则 $d_i(\phi(x), \phi(y)) \le L^+_{ik}(\phi) \cdot d_k(x, y) < \Theta_{mi}(\psi)$，由定理 3.1(4) 对 $\psi$ 知 $d_m(\psi(\phi(x)), \psi(\phi(y))) = 0$，故 $\Theta_{mk}(\psi \circ \phi) \ge \frac{\Theta_{mi}(\psi)}{L^+_{ik}(\phi)}$。若此外 $\Theta_{mi}(\psi) > 0$（或 $\psi$ 关于 $(m, i)$ 保零），则当 $d_k(x, y) < \Theta_{ik}(\phi)$ 时有 $d_i(\phi(x), \phi(y)) = 0 < \Theta_{mi}(\psi)$，同样导出 $d_m(\psi(\phi(x)), \psi(\phi(y))) = 0$，故 $\Theta_{mk}(\psi \circ \phi) \ge \Theta_{ik}(\phi)$。
4. 对联合控制形式，由 $\bar{\mathbb{R}}_+$ 上乘法对加法的分配律与结合律：
   $$d_m(\psi(u), \psi(v)) \le \sum_{i \in I} M^+_{mi}(\psi) d_i(\phi(x), \phi(y)) \le \sum_{i \in I} M^+_{mi}(\psi) \sum_{k \in I} M^+_{ik}(\phi) d_k(x, y) = \sum_{k \in I} \bigl(M^+(\psi) M^+(\phi)\bigr)_{mk} d_k(x, y).$$
   下界同理。证毕。 $\blacksquare$

---

### 性质 5：典型算子实例验证

为展示上述框架的自洽性，考察三类基本算子：

1. **全未定义（吸收）算子** $\phi_\bot(x) \equiv \bot$：
   此时 $\mathrm{dom}(\phi_\bot) = \emptyset$。空集上全称命题恒真，故：
   $$L^+_{ij}(\phi_\bot) = \inf \bar{\mathbb{R}}_+ = 0, \qquad L^-_{ij}(\phi_\bot) = \sup \bar{\mathbb{R}}_+ = +\infty, \qquad \Theta_{ij}(\phi_\bot) = \sup \bar{\mathbb{R}}_+ = +\infty.$$
2. **常值算子** $\phi_c$（在非退化定义域 $D \subseteq \mathcal{X} \setminus \{\bot\}$ 上取常值 $c_0 \neq \bot$，且存在 $x, y \in D$ 使 $0 < d_j(x, y) < +\infty$）：
   因 $d_i(\phi_c(x), \phi_c(y)) = d_i(c_0, c_0) = 0$ 恒成立，故：
   $$L^+_{ij}(\phi_c) = 0, \qquad L^-_{ij}(\phi_c) = 0, \qquad \Theta_{ij}(\phi_c) = +\infty.$$
3. **恒等算子** $\mathrm{id}_{\mathcal{X}}$（$\mathrm{dom}(\mathrm{id}_{\mathcal{X}}) = \mathcal{X} \setminus \{\bot\}$）：
   若每个分量 $d_i$ 在 $\mathcal{X} \setminus \{\bot\}$ 上存在有限正距离点对，则对角元满足：
   $$L^+_{ii}(\mathrm{id}_{\mathcal{X}}) = 1, \qquad L^-_{ii}(\mathrm{id}_{\mathcal{X}}) = 1, \qquad \Theta_{ii}(\mathrm{id}_{\mathcal{X}}) = \inf\{\, d_i(x, y) \mid d_i(x, y) > 0 \,\};$$
   而在联合控制意义下，单位矩阵 $E = (\delta_{ij})_{i, j \in I}$（其中 $\delta_{ii} = 1, \delta_{ij} = 0\ (i \neq j)$）同时属于 $\mathcal{M}^+(\mathrm{id}_{\mathcal{X}})$ 与 $\mathcal{M}^-(\mathrm{id}_{\mathcal{X}})$。
