{}
以下在 **CH1 扩展规范空间** $(\mathcal{X}, \mathcal{G}, \bot)$ 与**算子空间** $\mathcal{X}_{\mathrm{op}}$ 的严格框架下，将你提出的四点想法——**分量耦合矩阵化、上下界对称控制、扩展实数 $\bar{\mathbb{R}}_+$ 统一表达、输入落入一定范围后输出不可区分的对等矩阵刻画**——整理为一套自洽的数学定义体系，并给出完整的基本性质、必要论证与边界反例。

全文严格沿用 CH1 的记号与约定：$(\mathcal{X}, \mathcal{G}, \bot)$ 为规范空间，$\mathcal{G} = \{d_i\}_{i \in I}$（$I$ 有限非空），$\bar{\mathbb{R}}_+ = [0, +\infty]$ 采用算术约定 $a + (+\infty) = +\infty$、$0 \cdot (+\infty) = 0$、$a \cdot (+\infty) = +\infty$（$a > 0$），且不预设族分离性。

---

## §1 预备结构：扩展非负矩阵半环与规范不可区分关系

### 1.1 距离向量与扩展矩阵半环

**定义 1.1（距离向量与矩阵空间）**：对任意 $x, y \in \mathcal{X}$，记其**规范距离向量**为

$$\mathbf{d}(x, y) := \bigl(d_i(x, y)\bigr)_{i \in I} \in \bar{\mathbb{R}}_+^I,$$

并在 $\bar{\mathbb{R}}_+^I$ 上赋予逐分量偏序：$\mathbf{u} \leq \mathbf{v} \iff \forall\, i \in I,\; u_i \leq v_i$。

记 $\bar{\mathbb{R}}_+^{I \times I}$ 为指标集 $I \times I$ 上的**扩展非负矩阵空间**，约定行指标 $i \in I$ 对应**输出分量**，列指标 $j \in I$ 对应**输入分量**。对 $A, B \in \bar{\mathbb{R}}_+^{I \times I}$ 与 $\mathbf{v} \in \bar{\mathbb{R}}_+^I$：

1. **逐元偏序**：$A \leq B \iff \forall\, i, j \in I,\; A_{ij} \leq B_{ij}$；
2. **矩阵-向量作用**：$(A\mathbf{v})_i := \sum_{j \in I} A_{ij} v_j \in \bar{\mathbb{R}}_+$；
3. **半环矩阵乘法**：$(AB)_{ij} := \sum_{k \in I} A_{ik} B_{kj} \in \bar{\mathbb{R}}_+$，转置记为 $(A^{\mathsf{T}})_{ij} := A_{ji}$；
4. **特殊矩阵**：
   - 零矩阵 $\mathbf{0}$：$\mathbf{0}_{ij} = 0$；全无穷矩阵 $\mathbf{\infty}$：$\mathbf{\infty}_{ij} = +\infty$；
   - 单位矩阵 $I_{\mathrm{mat}}$：$(I_{\mathrm{mat}})_{ii} = 1$，$(I_{\mathrm{mat}})_{ij} = 0$（$i \neq j$）；
   - 对角零-非对角无穷矩阵 $E_{\diamond}$：$(E_{\diamond})_{ii} = 0$，$(E_{\diamond})_{ij} = +\infty$（$i \neq j$）。

> **引理 1.2（$\bar{\mathbb{R}}_+$ 半环相容性）**：在 CH1 算术约定下，$(\bar{\mathbb{R}}_+, +, \cdot, 0, 1, \leq)$ 构成**完备有序交换半环**：加法与乘法均满足结合律、交换律与单调性，乘法对有限和满足分配律 $a(b+c) = ab + ac$。因此 $\bar{\mathbb{R}}_+^{I \times I}$ 上的矩阵乘法满足结合律 $(AB)C = A(BC)$、单位元律 $I_{\mathrm{mat}} A = A I_{\mathrm{mat}} = A$ 及双侧单调性。
>
> *验证要点*：唯一需检验的无穷情形为 $0 \cdot (+\infty) = 0$。若 $a = 0$，则 $0 \cdot (b + c) = 0 = 0 \cdot b + 0 \cdot c$；若 $a = +\infty$，当 $b = c = 0$ 时两边均为 $0$，当 $b, c$ 不全为 $0$ 时 $b + c > 0$，两边均为 $+\infty$。结合律同理无例外成立。$\square$

---

### 1.2 不可区分关系与算子的规范相容性

由于 CH1 不预设族分离性，“两点距离为零”正是伪度量意义下“不可区分”的精确数学表达：

**定义 1.3（不可区分关系与规范相容算子）**：
1. 对 $i \in I$，称 $x, y \in \mathcal{X}$ 是 **$i$-不可区分的**（记作 $x \sim_i y$），若 $d_i(x, y) = 0$；称 $x, y$ 是**规范不可区分的**（记作 $x \sim_{\mathcal{G}} y$），若 $\mathbf{d}(x, y) = \mathbf{0}$（即 $\forall\, i \in I,\; d_i(x, y) = 0$）。由伪度量公理，$\sim_i$ 与 $\sim_{\mathcal{G}}$ 均为等价关系，且由隔离公理 (iv)，$[\bot]_{\sim_i} = [\bot]_{\sim_{\mathcal{G}}} = \{\bot\}$。
2. 设 $\phi \in \mathcal{X}_{\mathrm{op}}$。称 $\phi$ 在有效定义域 $\mathrm{dom}(\phi)$ 上是**规范相容的**（或**零距保持的**），若

   $$\forall\, x, y \in \mathrm{dom}(\phi),\qquad x \sim_{\mathcal{G}} y \implies \phi(x) \sim_{\mathcal{G}} \phi(y).$$

> **注记**：若 $(\mathcal{X}, \mathcal{G}, \bot)$ 在 $\mathrm{dom}(\phi)$ 上满足族分离性（$\mathbf{d}(x, y) = \mathbf{0} \implies x = y$），则**任意**算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 自动规范相容。在不预设族分离性的伪度量空间中，规范相容性刻画了算子不将“输入全分量不可区分的点对”撕裂为“输出可区分的点对”。

---

## §2 核心定义：三类扩展算子估计矩阵

设 $\phi \in \mathcal{X}_{\mathrm{op}}$，其有效定义域为 $\mathrm{dom}(\phi) = \{x \in \mathcal{X} \mid \phi(x) \neq \bot\}$。

**定义 2.1（扩展上 Lipschitz 矩阵）**：称矩阵 $L^+ = (L^+_{ij})_{i, j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$ 为算子 $\phi$ 的一个**扩展上 Lipschitz 矩阵**（简称**上 Lipschitz 矩阵**），若

$$\forall\, x, y \in \mathrm{dom}(\phi),\qquad \mathbf{d}(\phi(x), \phi(y)) \;\leq\; L^+\, \mathbf{d}(x, y),$$

即对每个输出分量 $i \in I$ 及任意 $x, y \in \mathrm{dom}(\phi)$，

$$d_i(\phi(x), \phi(y)) \;\leq\; \sum_{j \in I} L^+_{ij}\, d_j(x, y).$$

记 $\phi$ 的全体上 Lipschitz 矩阵之集为 $\mathcal{L}^+(\phi) \subseteq \bar{\mathbb{R}}_+^{I \times I}$。若存在有限矩阵 $L^+ \in [0, +\infty)^{I \times I} \cap \mathcal{L}^+(\phi)$，则称 $\phi$ 是**有限矩阵-Lipschitz 的**。

---

**定义 2.2（扩展下 Lipschitz 矩阵）**：称矩阵 $L^- = (L^-_{ij})_{i, j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$ 为算子 $\phi$ 的一个**扩展下 Lipschitz 矩阵**（或**余 Lipschitz 矩阵**，简称**下 Lipschitz 矩阵**），若

$$\forall\, x, y \in \mathrm{dom}(\phi),\qquad L^-\, \mathbf{d}(x, y) \;\leq\; \mathbf{d}(\phi(x), \phi(y)),$$

即对每个输出分量 $i \in I$ 及任意 $x, y \in \mathrm{dom}(\phi)$，

$$\sum_{j \in I} L^-_{ij}\, d_j(x, y) \;\leq\; d_i(\phi(x), \phi(y)).$$

记 $\phi$ 的全体下 Lipschitz 矩阵之集为 $\mathcal{L}^-(\phi) \subseteq \bar{\mathbb{R}}_+^{I \times I}$。若 $L^- \in \mathcal{L}^-(\phi)$ 且 $L^+ \in \mathcal{L}^+(\phi)$，则 $(L^-, L^+)$ 给出 $\phi$ 在 $\mathrm{dom}(\phi)$ 上的**双侧矩阵夹逼估计**：

$$L^-\, \mathbf{d}(x, y) \;\leq\; \mathbf{d}(\phi(x), \phi(y)) \;\leq\; L^+\, \mathbf{d}(x, y).$$

---

**定义 2.3（不可区分矩阵 / 坍缩阈值矩阵）**：称矩阵 $R = (R_{ij})_{i, j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$ 为算子 $\phi$ 的一个**不可区分矩阵**（或**坍缩阈值矩阵**），若对任意 $x, y \in \mathrm{dom}(\phi)$ 及每个输出分量 $i \in I$：

$$\bigl(\forall\, j \in I,\; d_j(x, y) \leq R_{ij}\bigr) \implies d_i(\phi(x), \phi(y)) = 0.$$

记 $\phi$ 的全体不可区分矩阵之集为 $\mathcal{R}(\phi) \subseteq \bar{\mathbb{R}}_+^{I \times I}$。

---

### 2.4 关键设计说明（自洽性与忠实性论证）

1. **为何在有效定义域 $\mathrm{dom}(\phi)$ 上量化而非全集 $\mathcal{X}$？**
   考察常值算子 $\phi_c$（固定 $c \in \mathcal{X} \setminus \{\bot\}$，对 $x \neq \bot$ 令 $\phi_c(x) = c$，$\phi_c(\bot) = \bot$）。直觉上常值算子必须允许零上界 $L^+ = \mathbf{0}$。若将定义 2.1 量化到全集 $\mathcal{X}$，取 $x \in \mathrm{dom}(\phi_c)$ 与 $y = \bot$，由 CH1 (iv) 及 $0 \cdot (+\infty) = 0$ 得：

   $$d_i(\phi_c(x), \phi_c(\bot)) = d_i(c, \bot) = +\infty \;>\; 0 = \sum_{j \in I} 0 \cdot d_j(x, \bot),$$

   导致常值算子反而不能取 $L^+ = \mathbf{0}$！同理，对部分定义算子若取 $x \in \mathrm{dom}(\phi)$ 与 $y \in (\mathcal{X}\setminus\{\bot\})\setminus\mathrm{dom}(\phi)$，$d_i(\phi(x), \bot) = +\infty$ 会迫使一切有限边界的部分算子退化为 $+\infty$。限制在有效定义域 $\mathrm{dom}(\phi)$ 上不仅消除了吸收元奇异性，而且对任意子集 $A \subseteq \mathcal{X} \setminus \{\bot\}$，可通过**定义域截断算子**

   $$\iota_A(x) := \begin{cases} x, & x \in A, \\ \bot, & x \notin A \end{cases} \quad (\iota_A \in \mathcal{X}_{\mathrm{op}})$$

   将算子在局部区域 $A$ 上的限制直接实现为算子复合 $\phi|_A := \phi \circ \iota_A \in \mathcal{X}_{\mathrm{op}}$（其有效定义域恰为 $\mathrm{dom}(\phi) \cap A$）。

2. **为何矩阵元素引入 $+\infty$ 在多分量规范空间中具有非平凡结构价值？**
   在单一度量下，非 Lipschitz 函数的常数退化为单一 $+\infty$；但在多伪度量下，允许 $+\infty$ 与 $0 \cdot (+\infty) = 0$ 协同工作，能够同时保留**分量无关性（$0$ 元）**与**其余分量的有限 Lipschitz 控制**。例如在 $\mathbb{R}^2 \cup \{\bot\}$（$d_1 = |\Delta x_1|,\, d_2 = |\Delta x_2|$）上取 $\phi(x_1, x_2) = (x_1^2, 3x_2)$：它虽非全局有限 Lipschitz，但拥有扩展上 Lipschitz 矩阵

   $$L^+ = \begin{pmatrix} +\infty & 0 \\ 0 & 3 \end{pmatrix} \in \mathcal{L}^+(\phi).$$

   由于 $0 \cdot d_2(x, y) = 0$ 且 $(+\infty)\cdot 0 = 0$，第一行严格编码了“第一输出分量虽对 $x_1$ 无有限 Lipschitz 上界，但完全不依赖于 $x_2$”，第二行则完整保留了精确常数 $3$。

3. **为何不可区分矩阵采用闭不等号 $\leq$ 而非严格不等号 $<$？**
   若改为 $\bigl(\forall\, j \in I,\, d_j(x, y) < R_{ij}\bigr) \implies d_i(\phi(x), \phi(y)) = 0$，则只要将第 $i$ 行某一个元素取为 $R_{ij_0} = 0$，前提中 $d_{j_0}(x, y) < 0$ 便恒假，导致该行其余元素可任意取 $+\infty$ 而空真成立，失去几何意义。采用闭阈值 $\leq$ 时，$R_{ij} = 0$ 恰对应零距条件 $d_j(x, y) = 0$，$R_{ij} \in (0, +\infty)$ 对应有限吸收半径，$R_{ij} = +\infty$ 则严格表达“输出 $i$ 的不可区分性完全不受输入分量 $j$ 影响（即使 $d_j(x, y) = +\infty$）”。

4. **不可区分矩阵与 Lipschitz 矩阵的统一代数形式**：
   在 $\bar{\mathbb{R}}_+$ 上定义支集放大算子 $\sigma(t) := (+\infty)\cdot t$（当 $t=0$ 时为 $0$，$t>0$ 时为 $+\infty$）及超阈算子 $\theta_r(t) := 0$（$t \leq r$）、$+\infty$（$t > r$），则定义 2.3 完全等价于同型求和不等式：

   $$R \in \mathcal{R}(\phi) \iff \forall\, x, y \in \mathrm{dom}(\phi),\; \forall\, i \in I:\quad (+\infty)\cdot d_i(\phi(x), \phi(y)) \;\leq\; \sum_{j \in I} \theta_{R_{ij}}\bigl(d_j(x, y)\bigr).$$

   特别当 $R = \mathbf{0}$ 时，$\theta_0(t) = (+\infty)\cdot t$，该式与 $L^+ = \mathbf{\infty} \in \mathcal{L}^+(\phi)$ 的定义不等式**逐字同一**。

---

## §3 基本性质与严格论证

### 3.1 存在性与规范相容性定理

**定理 3.1（非空性判准与统一表达定理）**：对任意算子 $\phi \in \mathcal{X}_{\mathrm{op}}$：
1. $\mathbf{0} \in \mathcal{L}^-(\phi)$ 恒成立，故 $\mathcal{L}^-(\phi)$ 无条件非空；
2. 下列五款相互等价：
   - **(a)** $\phi$ 在 $\mathrm{dom}(\phi)$ 上规范相容；
   - **(b)** $\mathcal{L}^+(\phi) \neq \emptyset$；
   - **(c)** $\mathbf{\infty} \in \mathcal{L}^+(\phi)$；
   - **(d)** $\mathcal{R}(\phi) \neq \emptyset$；
   - **(e)** $\mathbf{0} \in \mathcal{R}(\phi)$。

特别地，若 $(\mathcal{X}, \mathcal{G}, \bot)$ 满足族分离性，则对 $\mathcal{X}_{\mathrm{op}}$ 中**一切算子**（无论是否连续或有限 Lipschitz），$\mathcal{L}^+(\phi), \mathcal{L}^-(\phi), \mathcal{R}(\phi)$ 均非空。

**证明**：
1. 对任意 $x, y \in \mathrm{dom}(\phi)$ 与 $i \in I$，$\sum_{j \in I} 0 \cdot d_j(x, y) = 0 \leq d_i(\phi(x), \phi(y))$，故 $\mathbf{0} \in \mathcal{L}^-(\phi)$。
2. **(a) $\Rightarrow$ (c)**：设 $\phi$ 规范相容，任取 $x, y \in \mathrm{dom}(\phi)$ 与 $i \in I$。若 $\forall\, j \in I,\, d_j(x, y) = 0$，由规范相容性有 $d_i(\phi(x), \phi(y)) = 0 \leq 0 = \sum_{j \in I} (+\infty)\cdot d_j(x, y)$；若存在 $j_0 \in I$ 使 $d_{j_0}(x, y) > 0$，则由 CH1 算术有 $(+\infty)\cdot d_{j_0}(x, y) = +\infty$，从而 $\sum_{j \in I} (+\infty)\cdot d_j(x, y) = +\infty \geq d_i(\phi(x), \phi(y))$。故 $\mathbf{\infty} \in \mathcal{L}^+(\phi)$。
   **(c) $\Rightarrow$ (b)**：显然。
   **(b) $\Rightarrow$ (a)**：设存在 $L^+ \in \mathcal{L}^+(\phi)$。若 $x, y \in \mathrm{dom}(\phi)$ 满足 $\forall\, j \in I,\, d_j(x, y) = 0$，则对每个 $i \in I$，由 $L^+_{ij} \cdot 0 = 0$（含 $L^+_{ij} = +\infty$ 情形）得 $d_i(\phi(x), \phi(y)) \leq \sum_{j \in I} L^+_{ij} \cdot 0 = 0$，即 $d_i(\phi(x), \phi(y)) = 0$。
   **(a) $\Leftrightarrow$ (e)**：因 $d_j(x, y) \leq 0 \iff d_j(x, y) = 0$，故 $\mathbf{0} \in \mathcal{R}(\phi)$ 的定义条件即为规范相容性。
   **(e) $\Rightarrow$ (d)** 显然；**(d) $\Rightarrow$ (e)**：若 $R \in \mathcal{R}(\phi)$，当 $\forall\, j,\, d_j(x, y) \leq 0$ 时必有 $d_j(x, y) \leq R_{ij}$，故 $d_i(\phi(x), \phi(y)) = 0$，得 $\mathbf{0} \in \mathcal{R}(\phi)$。$\square$

---

### 3.2 序结构、凸性与极值可达性（附精确反例）

**定理 3.2（序结构、行解耦与凸性）**：设 $\phi \in \mathcal{X}_{\mathrm{op}}$。
1. **单调闭包性**：在偏序集 $(\bar{\mathbb{R}}_+^{I \times I}, \leq)$ 中，$\mathcal{L}^+(\phi)$ 是**上闭集**（$L^+ \in \mathcal{L}^+(\phi),\, L^+ \leq M \implies M \in \mathcal{L}^+(\phi)$），而 $\mathcal{L}^-(\phi)$ 与 $\mathcal{R}(\phi)$ 均为**下闭集**（$M \leq L^- \in \mathcal{L}^-(\phi) \implies M \in \mathcal{L}^-(\phi)$；$S \leq R \in \mathcal{R}(\phi) \implies S \in \mathcal{R}(\phi)$）。
2. **行直积解耦**：三类集合均按输出行 $i \in I$ 直积分解（各行约束彼此独立，耦合仅发生于同一行内各输入列 $j \in I$ 之间）。
3. **凸性**：对任意 $A, B \in \mathcal{L}^+(\phi)$（或 $\mathcal{L}^-(\phi)$）及满足 $\alpha + \beta = 1$ 的 $\alpha, \beta \in [0, 1]$，有 $\alpha A + \beta B \in \mathcal{L}^+(\phi)$（或 $\mathcal{L}^-(\phi)$）。
4. **有向极值的可达性**：
   - **(i) 下界上确界封闭**：对任意非空上向有向族 $\{L^{-, \lambda}\}_{\lambda \in \Lambda} \subseteq \mathcal{L}^-(\phi)$（即任二元有公共上界于族中），其逐元上确界 $\sup_{\lambda \in \Lambda} L^{-, \lambda} \in \mathcal{L}^-(\phi)$。由 Zorn 引理，$\mathcal{L}^-(\phi)$ 中任一元素均被某个**极大下 Lipschitz 矩阵**控制；特别当 $|I|=1$ 时，$\mathcal{L}^-(\phi) = [0, \ell^*(\phi)]$ 必含唯一最大元 $\ell^*(\phi) \in \bar{\mathbb{R}}_+$。
   - **(ii) 有限距离下的上界下确界封闭**：若在 $\mathrm{dom}(\phi)$ 上各分量距离均有限（$\forall\, x, y \in \mathrm{dom}(\phi),\, \forall\, j \in I,\; d_j(x, y) < +\infty$），则对任意非空下向有向族 $\{L^{+, \lambda}\}_{\lambda \in \Lambda} \subseteq \mathcal{L}^+(\phi)$，其逐元下确界 $\inf_{\lambda \in \Lambda} L^{+, \lambda} \in \mathcal{L}^+(\phi)$。由 Zorn 引理，此时每个上 Lipschitz 矩阵均控制某个**极小（Pareto 最优）上 Lipschitz 矩阵**；当 $|I|=1$ 且 $\phi$ 规范相容时，$\mathcal{L}^+(\phi) = [L^*(\phi), +\infty]$ 含唯一最小元 $L^*(\phi)$。

**证明**：
(1)–(2) 由乘加单调性及前提蕴涵链直接得出。
(3) 任取 $x, y \in \mathrm{dom}(\phi),\, i \in I$。对 $A, B \in \mathcal{L}^+(\phi)$，利用分配律（含 $d_i(\phi(x), \phi(y)) = +\infty$ 时 $(\alpha + \beta)\cdot(+\infty) = 1 \cdot (+\infty) = +\infty$）：

$$d_i(\phi(x), \phi(y)) = (\alpha + \beta) d_i(\phi(x), \phi(y)) \leq \alpha \sum_{j \in I} A_{ij} d_j(x, y) + \beta \sum_{j \in I} B_{ij} d_j(x, y) = \sum_{j \in I} (\alpha A_{ij} + \beta B_{ij}) d_j(x, y).$$

$\mathcal{L}^-(\phi)$ 的凸性反向同理。
(4-i) 在 $\bar{\mathbb{R}}_+$ 中，乘法与有限和均保持上向有向族的上确界（对有限集 $I$ 归纳：因 $\Lambda$ 上向有向，$\sup_\lambda u_\lambda + \sup_\mu v_\mu = \sup_{\lambda, \mu}(u_\lambda + v_\mu) \leq \sup_\nu (u_\nu + v_\nu)$），故

$$\sum_{j \in I} \Bigl(\sup_{\lambda \in \Lambda} L^{-, \lambda}_{ij}\Bigr) d_j(x, y) = \sum_{j \in I} \sup_{\lambda \in \Lambda} \bigl(L^{-, \lambda}_{ij} d_j(x, y)\bigr) = \sup_{\lambda \in \Lambda} \sum_{j \in I} L^{-, \lambda}_{ij} d_j(x, y) \leq d_i(\phi(x), \phi(y)).$$

(4-ii) 当 $d_j(x, y) < +\infty$ 时，乘以有限非负实数 $c = d_j(x, y) \in [0, +\infty)$ 保持任意非空下确界：$\bigl(\inf_\lambda L^{+, \lambda}_{ij}\bigr) c = \inf_\lambda (L^{+, \lambda}_{ij} c)$；再由 $I$ 有限及下向有向性，$\sum_{j \in I} \inf_\lambda (L^{+, \lambda}_{ij} d_j(x, y)) = \inf_\lambda \sum_{j \in I} L^{+, \lambda}_{ij} d_j(x, y) \geq d_i(\phi(x), \phi(y))$。$\square$

> **注记与三个精确边界反例（说明上述定理条件的不可省性）**：
> 1. **存在 $+\infty$ 距离时，$\mathcal{L}^+(\phi)$ 的下确界未必可达**：设 $\mathcal{X} = \{a, b, \bot\}$，$I = \{1\}$，$d_1(a, b) = +\infty$，取恒等算子 $\mathrm{id}_{\mathcal{X}}$。对任意 $c > 0$，$c \cdot d_1(a, b) = c \cdot (+\infty) = +\infty = d_1(a, b)$，故 $(0, +\infty] \subseteq \mathcal{L}^+(\mathrm{id}_{\mathcal{X}})$；但 $c = 0$ 时 $0 \cdot (+\infty) = 0 < +\infty = d_1(a, b)$，故 $\mathcal{L}^+(\mathrm{id}_{\mathcal{X}}) = (0, +\infty]$，其下确界 $0 \notin \mathcal{L}^+(\mathrm{id}_{\mathcal{X}})$。
> 2. **多分量 $|I| \geq 2$ 时，不存在唯一逐元最小/最大矩阵**：设 $\mathcal{X} = \{a, b, \bot\}$，$I = \{1, 2\}$，$d_1(a, b) = d_2(a, b) = 1$，取 $\phi = \mathrm{id}_{\mathcal{X}}$。则单位阵 $I_{\mathrm{mat}} = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ 与置换阵 $P = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ **同时**属于 $\mathcal{L}^+(\mathrm{id}_{\mathcal{X}}) \cap \mathcal{L}^-(\mathrm{id}_{\mathcal{X}})$，但其逐元下确界 $\min(I_{\mathrm{mat}}, P) = \mathbf{0} \notin \mathcal{L}^+(\mathrm{id}_{\mathcal{X}})$，逐元上确界 $\max(I_{\mathrm{mat}}, P) = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix} \notin \mathcal{L}^-(\mathrm{id}_{\mathcal{X}})$（因 $1 + 1 \not\leq 1$）。同理，对 $\mathcal{R}(\mathrm{id}_{\mathcal{X}})$，$\begin{pmatrix} 1/2 & +\infty \\ +\infty & 1/2 \end{pmatrix}$ 与 $\begin{pmatrix} +\infty & 1/2 \\ 1/2 & +\infty \end{pmatrix}$ 均属于 $\mathcal{R}(\mathrm{id}_{\mathcal{X}})$，但逐元上确界 $\mathbf{\infty} \notin \mathcal{R}(\mathrm{id}_{\mathcal{X}})$。这严格证明了在一般规范空间中，必须以**容许矩阵集**（而非单一矩阵值泛函）作为基础定义。
> 3. **不可区分矩阵集 $\mathcal{R}(\phi)$ 对递增序列上确界一般不封闭**：在 $\mathcal{X} = \{a, b, \bot\}$，$I = \{1\}$，$d_1(a, b) = 1$ 上取 $\mathrm{id}_{\mathcal{X}}$。对任意 $r < 1$，$d_1(x, y) \leq r \implies x = y \implies d_1(x, y) = 0$，但 $r = 1$ 不满足，故 $\mathcal{R}(\mathrm{id}_{\mathcal{X}}) = [0, 1)$。

---

### 3.3 典范算子与局部化单调性

**命题 3.3（基本算子的特征矩阵）**：
1. **恒等算子** $\mathrm{id}_{\mathcal{X}}$（$\mathrm{dom}(\mathrm{id}_{\mathcal{X}}) = \mathcal{X} \setminus \{\bot\} \neq \emptyset$）：$I_{\mathrm{mat}} \in \mathcal{L}^+(\mathrm{id}_{\mathcal{X}}) \cap \mathcal{L}^-(\mathrm{id}_{\mathcal{X}})$，且 $E_{\diamond} \in \mathcal{R}(\mathrm{id}_{\mathcal{X}})$。
2. **定义域截断与区域单调性**：对任意子集 $A \subseteq B \subseteq \mathcal{X} \setminus \{\bot\}$ 及 $\phi \in \mathcal{X}_{\mathrm{op}}$，记 $\phi|_A := \phi \circ \iota_A$，则

   $$\mathcal{L}^+(\phi|_B) \subseteq \mathcal{L}^+(\phi|_A), \qquad \mathcal{L}^-(\phi|_B) \subseteq \mathcal{L}^-(\phi|_A), \qquad \mathcal{R}(\phi|_B) \subseteq \mathcal{R}(\phi|_A).$$

3. **输出分量坍缩的充要刻画**：对任意 $\phi \in \mathcal{X}_{\mathrm{op}}$，

   $$\mathbf{0} \in \mathcal{L}^+(\phi) \iff \bigl(\forall\, x, y \in \mathrm{dom}(\phi),\; \phi(x) \sim_{\mathcal{G}} \phi(y)\bigr) \iff \mathbf{\infty} \in \mathcal{R}(\phi).$$

   （按行同样成立：第 $i$ 行可取全 $0$ 上界 $\iff \phi$ 在 $\mathrm{dom}(\phi)$ 上恒输出 $i$-不可区分值 $\iff$ 第 $i$ 行可取全 $+\infty$ 不可区分阈值。）

**证明**：(1) 对 $\mathrm{id}_{\mathcal{X}}$，$(I_{\mathrm{mat}}\mathbf{d}(x, y))_i = d_i(x, y)$；若 $\forall\, j,\, d_j(x, y) \leq (E_{\diamond})_{ij}$，取 $j = i$ 得 $d_i(x, y) \leq 0$，即 $d_i(x, y) = 0$。(2) 因 $\mathrm{dom}(\phi|_A) = \mathrm{dom}(\phi) \cap A \subseteq \mathrm{dom}(\phi) \cap B = \mathrm{dom}(\phi|_B)$ 且在交集上取值相同。(3) 由 $d_i(\phi(x), \phi(y)) \leq 0 \iff d_i(\phi(x), \phi(y)) = 0$ 及 $d_j(x, y) \leq +\infty$ 恒真即得。$\square$

---

### 3.4 算子复合的矩阵演算定律

对 $\phi, \psi \in \mathcal{X}_{\mathrm{op}}$，因 $\psi(\phi(\bot)) = \psi(\bot) = \bot$，复合 $\psi \circ \phi \in \mathcal{X}_{\mathrm{op}}$，且有效定义域满足：

$$\mathrm{dom}(\psi \circ \phi) = \bigl\{\, x \in \mathrm{dom}(\phi) \;\big|\; \phi(x) \in \mathrm{dom}(\psi) \,\bigr\}.$$

为刻画纯不可区分矩阵的复合，引入 $\bar{\mathbb{R}}_+^{I \times I}$ 上的 **$\diamond$-积**：对 $S, R \in \bar{\mathbb{R}}_+^{I \times I}$，定义

$$(S \diamond R)_{ij} := \min \bigl\{\, R_{kj} \;\big|\; k \in I,\; S_{ik} < +\infty \,\bigr\} \qquad (\text{约定 } \min \emptyset := +\infty).$$

**定理 3.4（复合演算定理）**：设 $\phi, \psi \in \mathcal{X}_{\mathrm{op}}$。
1. **$\diamond$-积的半群性质**：运算 $\diamond$ 在 $\bar{\mathbb{R}}_+^{I \times I}$ 上满足结合律 $(T \diamond S) \diamond R = T \diamond (S \diamond R)$，且以 $E_{\diamond}$ 为左单位元（$E_{\diamond} \diamond R = R$）。
2. **上界次可乘律**：若 $L^+ \in \mathcal{L}^+(\phi)$，$M^+ \in \mathcal{L}^+(\psi)$，则 $M^+ L^+ \in \mathcal{L}^+(\psi \circ \phi)$。
3. **下界超可乘律**：若 $L^- \in \mathcal{L}^-(\phi)$，$M^- \in \mathcal{L}^-(\psi)$，则 $M^- L^- \in \mathcal{L}^-(\psi \circ \phi)$。
4. **不可区分复合律**：若 $R \in \mathcal{R}(\phi)$，$S \in \mathcal{R}(\psi)$，则 $S \diamond R \in \mathcal{R}(\psi \circ \phi)$。
5. **混合拉回律（Lipschitz 传递不可区分域）**：若 $L^+ \in \mathcal{L}^+(\phi)$，$S \in \mathcal{R}(\psi)$，则对任意满足矩阵不等式

   $$R (L^+)^{\mathsf{T}} \;\leq\; S \qquad \Bigl(\text{即 } \forall\, i, k \in I,\; \sum_{j \in I} R_{ij} L^+_{kj} \leq S_{ik}\Bigr)$$

   的矩阵 $R \in \bar{\mathbb{R}}_+^{I \times I}$，均有 $R \in \mathcal{R}(\psi \circ \phi)$。

**证明**：
1. 有限集上的最小值小于 $+\infty$ 当且仅当存在某元素小于 $+\infty$。故 $(T \diamond S)_{im} < +\infty \iff \exists\, k \in I,\, (T_{ik} < +\infty \wedge S_{km} < +\infty)$。于是

   $$((T \diamond S) \diamond R)_{ij} = \min\bigl\{R_{mj} \;\big|\; \exists\, k \in I,\, T_{ik} < +\infty \wedge S_{km} < +\infty\bigr\} = (T \diamond (S \diamond R))_{ij}.$$

   又因 $(E_{\diamond})_{ik} < +\infty \iff k = i$，故 $(E_{\diamond} \diamond R)_{ij} = R_{ij}$。
2. 任取 $x, y \in \mathrm{dom}(\psi \circ \phi)$，则 $x, y \in \mathrm{dom}(\phi)$ 且 $\phi(x), \phi(y) \in \mathrm{dom}(\psi)$。由引理 1.2：

   $$d_i\bigl(\psi(\phi(x)), \psi(\phi(y))\bigr) \leq \sum_{k \in I} M^+_{ik} d_k(\phi(x), \phi(y)) \leq \sum_{k \in I} M^+_{ik} \sum_{j \in I} L^+_{kj} d_j(x, y) = \sum_{j \in I} (M^+ L^+)_{ij} d_j(x, y).$$

   （注：若某中间分量 $L^+_{kj} = +\infty$ 而外层 $M^+_{ik} = 0$，由 $0 \cdot (+\infty) = 0$ 该无穷项在复合中自动消去！）
3. 将 (2) 中不等号全部反向即得 $M^- L^- \in \mathcal{L}^-(\psi \circ \phi)$。
4. 设 $x, y \in \mathrm{dom}(\psi \circ \phi)$ 且 $\forall\, j \in I,\, d_j(x, y) \leq (S \diamond R)_{ij}$。对每个 $k \in I$：若 $S_{ik} = +\infty$，显然 $d_k(\phi(x), \phi(y)) \leq +\infty = S_{ik}$；若 $S_{ik} < +\infty$，则对一切 $j \in I$ 有 $d_j(x, y) \leq (S \diamond R)_{ij} \leq R_{kj}$，由 $R \in \mathcal{R}(\phi)$ 得 $d_k(\phi(x), \phi(y)) = 0 \leq S_{ik}$。综上 $\forall\, k \in I,\, d_k(\phi(x), \phi(y)) \leq S_{ik}$，再由 $S \in \mathcal{R}(\psi)$ 得 $d_i((\psi \circ \phi)(x), (\psi \circ \phi)(y)) = 0$。
5. 若 $\forall\, j \in I,\, d_j(x, y) \leq R_{ij}$，则对任意 $k \in I$，

   $$d_k(\phi(x), \phi(y)) \leq \sum_{j \in I} L^+_{kj} d_j(x, y) \leq \sum_{j \in I} L^+_{kj} R_{ij} = \bigl(R(L^+)^{\mathsf{T}}\bigr)_{ik} \leq S_{ik},$$

   于是由 $S \in \mathcal{R}(\psi)$ 立得 $d_i((\psi \circ \phi)(x), (\psi \circ \phi)(y)) = 0$。$\square$

---

### 3.5 三类矩阵间的代数对偶、互斥律与几何推论

定义逐元**零-无穷支集对偶映射** $\kappa : \bar{\mathbb{R}}_+^{I \times I} \to \{0, +\infty\}^{I \times I}$ 为：

$$\kappa(A)_{ij} := \begin{cases} +\infty, & A_{ij} = 0, \\ 0, & A_{ij} > 0. \end{cases}$$

**定理 3.5（对偶同态、互斥律与几何性质）**：设 $\phi \in \mathcal{X}_{\mathrm{op}}$。
1. **支集对偶幺半群同态**：$\kappa$ 是从乘性矩阵幺半群 $(\bar{\mathbb{R}}_+^{I \times I}, \cdot, I_{\mathrm{mat}}, \leq)$ 到不可区分矩阵半群 $(\bar{\mathbb{R}}_+^{I \times I}, \diamond, E_{\diamond}, \geq)$ 的**反序幺半群同态**，即：
   - $A \leq B \implies \kappa(B) \leq \kappa(A)$，$\kappa(\mathbf{0}) = \mathbf{\infty}$，$\kappa(\mathbf{\infty}) = \mathbf{0}$，$\kappa(I_{\mathrm{mat}}) = E_{\diamond}$；
   - 对任意 $A, B \in \bar{\mathbb{R}}_+^{I \times I}$，恒有 **$\kappa(AB) = \kappa(A) \diamond \kappa(B)$**；
   - 对任意算子 $\phi$，有映射关系

     $$L^+ \in \mathcal{L}^+(\phi) \implies \kappa(L^+) \in \mathcal{R}(\phi).$$

   （推论：若 $R \in \mathcal{R}(\phi)$ 且 $M^+ \in \mathcal{L}^+(\psi)$，则 $\kappa(M^+) \diamond R \in \mathcal{R}(\psi \circ \phi)$。）
2. **上下界独立见证相容律**：设 $L^- \in \mathcal{L}^-(\phi)$，$L^+ \in \mathcal{L}^+(\phi)$。若输入分量 $k \in I$ 在 $\mathrm{dom}(\phi)$ 上**独立可见**——即存在 $x, y \in \mathrm{dom}(\phi)$ 使 $0 < d_k(x, y) < +\infty$ 且 $\forall\, j \neq k,\, d_j(x, y) = 0$——则对一切 $i \in I$ 必有 $L^-_{ik} \leq L^+_{ik}$。（注：若缺乏独立见证，如 §3.2 注记 2 中 $d_1 = d_2$，取 $L^- = I_{\mathrm{mat}},\, L^+ = P$ 时可有 $L^-_{11} = 1 > 0 = L^+_{11}$。）
3. **下界扩张与不可区分坍缩的互斥律**：设 $L^- \in \mathcal{L}^-(\phi)$，$R \in \mathcal{R}(\phi)$。若存在 $x, y \in \mathrm{dom}(\phi)$ 落入第 $i$ 行的不可区分盒（$\forall\, j \in I,\, d_j(x, y) \leq R_{ij}$）且在某分量 $k \in I$ 上可区分（$d_k(x, y) > 0$），则必有 **$L^-_{ik} = 0$**。
4. **规范单射性与规范球坍缩定理**：
   - **(i) 规范单射性（可区分性保持）**：若存在 $L^- \in \mathcal{L}^-(\phi)$ 使得每一列均非零（$\forall\, j \in I,\, \exists\, i \in I,\, L^-_{ij} > 0$），则 $\phi$ 在 $\mathrm{dom}(\phi)$ 上保持规范可区分性：

     $$\forall\, x, y \in \mathrm{dom}(\phi),\qquad \phi(x) \sim_{\mathcal{G}} \phi(y) \implies x \sim_{\mathcal{G}} y.$$

   - **(ii) 局部规范球坍缩**：若 $R \in \mathcal{R}(\phi)$，任取中心 $x_0 \in \mathcal{X} \setminus \{\bot\}$ 与半径向量 $\boldsymbol{\rho} = (\rho_j)_{j \in I} \in \bar{\mathbb{R}}_+^I$，记闭规范球 $\bar{B}_{\mathcal{G}}(x_0, \boldsymbol{\rho}) := \{x \in \mathcal{X} \setminus \{\bot\} \mid \forall\, j \in I,\, d_j(x_0, x) \leq \rho_j\}$。若第 $i$ 行满足 $\forall\, j \in I,\; 2\rho_j \leq R_{ij}$，则当输入落入 $\bar{B}_{\mathcal{G}}(x_0, \boldsymbol{\rho}) \cap \mathrm{dom}(\phi)$ 时，其输出在分量 $i$ 下完全不可区分：

     $$\forall\, x, y \in \bar{B}_{\mathcal{G}}(x_0, \boldsymbol{\rho}) \cap \mathrm{dom}(\phi),\qquad d_i(\phi(x), \phi(y)) = 0.$$

**证明**：
1. 反序性与 $\kappa(I_{\mathrm{mat}}) = E_{\diamond}$ 由定义即得。证 $\kappa(AB) = \kappa(A) \diamond \kappa(B)$：在 $\bar{\mathbb{R}}_+$ 中 $(AB)_{ij} = \sum_{k \in I} A_{ik} B_{kj} > 0 \iff \exists\, k \in I,\, (A_{ik} > 0 \wedge B_{kj} > 0)$。另一方面，$\kappa(A)_{ik} < +\infty \iff A_{ik} > 0$，且此时 $\kappa(B)_{kj} \in \{0, +\infty\}$ 取 $0$ 当且仅当 $B_{kj} > 0$；故 $(\kappa(A) \diamond \kappa(B))_{ij} = 0 \iff \exists\, k \in I,\, (A_{ik} > 0 \wedge B_{kj} > 0)$，否则同为 $+\infty$。
   再证 $L^+ \in \mathcal{L}^+(\phi) \implies \kappa(L^+) \in \mathcal{R}(\phi)$：若 $\forall\, j \in I,\, d_j(x, y) \leq \kappa(L^+)_{ij}$，则当 $L^+_{ij} > 0$ 时 $\kappa(L^+)_{ij} = 0 \implies d_j(x, y) = 0 \implies L^+_{ij} d_j(x, y) = 0$（含 $L^+_{ij} = +\infty$）；当 $L^+_{ij} = 0$ 时亦有 $0 \cdot d_j(x, y) = 0$（含 $d_j(x, y) = +\infty$）。求和得 $d_i(\phi(x), \phi(y)) \leq 0$，即 $d_i(\phi(x), \phi(y)) = 0$。推论结合定理 3.4(4) 立得。
2. 将独立见证点对 $(x, y)$ 代入夹逼不等式，因 $j \neq k$ 项均为 $0$，得 $L^-_{ik} d_k(x, y) \leq L^+_{ik} d_k(x, y)$。因 $0 < d_k(x, y) < +\infty$，约去 $d_k(x, y)$ 即得 $L^-_{ik} \leq L^+_{ik}$。
3. 在题设点对 $(x, y)$ 处，由 $R \in \mathcal{R}(\phi)$ 得 $d_i(\phi(x), \phi(y)) = 0$；代入下界得 $0 \leq L^-_{ik} d_k(x, y) \leq \sum_{j \in I} L^-_{ij} d_j(x, y) \leq 0$。因 $d_k(x, y) > 0$，无论 $d_k(x, y)$ 有限还是 $+\infty$，$L^-_{ik} d_k(x, y) = 0$ 均迫使 $L^-_{ik} = 0$。
4. **(i)** 设 $\phi(x) \sim_{\mathcal{G}} \phi(y)$。对任意 $j \in I$，取 $i \in I$ 使 $L^-_{ij} > 0$，由 $L^-_{ij} d_j(x, y) \leq d_i(\phi(x), \phi(y)) = 0$ 及 $L^-_{ij} > 0$ 得 $d_j(x, y) = 0$。
   **(ii)** 任取 $x, y \in \bar{B}_{\mathcal{G}}(x_0, \boldsymbol{\rho}) \cap \mathrm{dom}(\phi)$。对每个 $j \in I$，由对称性与三角不等式：

   $$d_j(x, y) \leq d_j(x, x_0) + d_j(x_0, y) = d_j(x_0, x) + d_j(x_0, y) \leq \rho_j + \rho_j = 2\rho_j \leq R_{ij}.$$

   由 $R \in \mathcal{R}(\phi)$ 即得 $d_i(\phi(x), \phi(y)) = 0$。$\square$

---

### 小结：三类矩阵的对等关系全景表

| 矩阵类别 | 记号与定义域 ($\bar{\mathbb{R}}_+^{I \times I}$) | 核心估计条件（$\forall\, x, y \in \mathrm{dom}(\phi),\; \forall\, i \in I$） | 序方向 | 平凡元与非空条件 | 恒等算子 $\mathrm{id}_{\mathcal{X}}$ 典范元 | 复合运算 ($\psi \circ \phi$) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **上 Lipschitz 矩阵** | $L^+ \in \mathcal{L}^+(\phi)$ | $d_i(\phi(x), \phi(y)) \leq \sum_{j \in I} L^+_{ij} d_j(x, y)$ | 上闭集 | $\mathbf{\infty} \in \mathcal{L}^+(\phi) \iff \phi$ 规范相容 | $I_{\mathrm{mat}}$ | 标准半环积 $M^+ L^+$ |
| **下 Lipschitz 矩阵** | $L^- \in \mathcal{L}^-(\phi)$ | $\sum_{j \in I} L^-_{ij} d_j(x, y) \leq d_i(\phi(x), \phi(y))$ | 下闭集 | $\mathbf{0} \in \mathcal{L}^-(\phi)$ 恒成立 | $I_{\mathrm{mat}}$ | 标准半环积 $M^- L^-$ |
| **不可区分矩阵** | $R \in \mathcal{R}(\phi)$ | $(\forall\, j,\, d_j(x, y) \leq R_{ij}) \Rightarrow d_i(\phi(x), \phi(y)) = 0$ | 下闭集 | $\mathbf{0} \in \mathcal{R}(\phi) \iff \phi$ 规范相容 | $E_{\diamond} = \kappa(I_{\mathrm{mat}})$ | $\diamond$-积 $S \diamond R$（及混合拉回 $R(L^+)^{\mathsf{T}} \leq S$） |
