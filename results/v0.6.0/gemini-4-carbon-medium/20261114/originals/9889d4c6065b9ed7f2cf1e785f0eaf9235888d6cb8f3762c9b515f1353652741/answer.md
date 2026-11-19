正在使用本地形式化工具检验核心定义与定理的自洽性，稍候将继续完成整理。
在 CH1 **扩展规范空间** $(\mathcal{X}, \mathcal{G}, \bot)$ 与**算子空间** $\mathcal{X}_{\mathrm{op}}$ 的框架下，经典度量空间中的单一标量 Lipschitz 常数在四个维度上自然推广并耦合为一个自洽的矩阵体系：

1. **多分量耦合**：规范族 $\mathcal{G}=\{d_i\}_{i\in I}$ 的各分量之间存在交叉影响，算子对距离的控制由 $\bar{\mathbb{R}}_+^{I\times I}$ 中的矩阵刻画；
2. **上下界对称夹逼**：除控制距离增长上限的**上界 Lipschitz 矩阵** $L$ 外，可对称引入控制距离保持/扩张下限的**下界 Lipschitz 矩阵** $M$（并在多分量情形区分**正向分量下界**与**逆向联合余 Lipschitz 控制**）；
3. **扩展实数 $\bar{\mathbb{R}}_+ = [0, +\infty]$ 统一表达**：允许矩阵元取 $+\infty$，将非 Lipschitz 算子、无界算子乃至将有限距离映射为 $+\infty$ 的算子纳入同一套半环代数，同时揭示“存在扩展矩阵界”与 CH1“不预设族分离性”之间的精确等价条件；
4. **不可区分（坍缩）阈值矩阵 $\Theta$**：刻画“输入落入给定距离阈值范畴内时，输出在对应分量上不可区分（零距）”这一算子分辨率/死区性质，它与上界矩阵 $L$ 在定性骨架 $\{0,+\infty\}^{I\times I}$ 上严格对偶，并与 $L, M$ 形成完整的复合传播与正交互补代数。

下面给出严格定义、核心性质及完整证明。

---

## 一、代数与几何预备：$\bar{\mathbb{R}}_+$ 矩阵半环与规范相容性

设 $(\mathcal{X}, \mathcal{G}, \bot)$ 为扩展规范空间，$\mathcal{G} = \{d_i\}_{i \in I}$（$I$ 有限非空）。

### 1.1 距离向量与 $\bar{\mathbb{R}}_+$ 矩阵半环
对任意 $x, y \in \mathcal{X}$，记**规范距离向量**为

$$\mathbf{d}(x, y) := \bigl(d_i(x, y)\bigr)_{i \in I} \in \bar{\mathbb{R}}_+^I.$$

在 $\bar{\mathbb{R}}_+^I$ 与矩阵空间 $\bar{\mathbb{R}}_+^{I \times I}$ 上赋予逐分量偏序 $\preceq$：

$$u \preceq v \iff \forall\, i \in I,\; u_i \leq v_i; \qquad A \preceq B \iff \forall\, i, j \in I,\; A_{ij} \leq B_{ij}.$$

记 $\mathbf{0}$ 为全 $0$ 矩阵，$\mathbf{\infty}$ 为全 $+\infty$ 矩阵，$I_{\mathcal{G}} = (\delta_{ij})_{i,j\in I}$ 为单位矩阵（对角元为 $1$，非对角元为 $0$）。

> **引理 1.1（$\bar{\mathbb{R}}_+$ 矩阵半环）**：在 CH1 算术约定（$a+(+\infty)=+\infty$，$0\cdot(+\infty)=0$，$a>0$ 时 $a\cdot(+\infty)=+\infty$）下，$(\bar{\mathbb{R}}_+, +, \cdot, 0, 1)$ 构成交换半环，进而 $(\bar{\mathbb{R}}_+^{I \times I}, +, \cdot, \mathbf{0}, I_{\mathcal{G}})$ 构成含幺半环，且矩阵乘法关于 $\preceq$ 双侧单调：
> $$(AB)_{ik} = \sum_{j \in I} A_{ij} B_{jk}, \qquad (A u)_i = \sum_{j \in I} A_{ij} u_j.$$

**证明**：仅需核验含 $0$ 与 $+\infty$ 时的结合律 $(ab)c = a(bc)$ 与分配律 $a(b+c) = ab + ac$。
- 若 $a,b,c$ 中至少一者为 $0$，由 $0\cdot(+\infty)=0$ 知 $(ab)c = 0 = a(bc)$；若全不为 $0$ 且至少一者为 $+\infty$，则两侧均为 $+\infty$。
- 对分配律：若 $a=0$，两侧皆为 $0$；若 $a=+\infty$，当 $b=c=0$ 时两侧皆为 $0$，当 $b+c>0$ 时至少一项大于 $0$，两侧皆为 $+\infty$；若 $0<a<+\infty$，分 $b,c$ 是否含 $+\infty$ 讨论即得相等。有限指标集 $I$ 上的矩阵结合律、分配律与单调性由此直接导出。$\square$

---

### 1.2 规范不可区分关系与有效定义域限制

由于正文不预设族分离性，伪度量族自然诱导点集上的零距等价关系：

**定义 1.2（规范不可区分与规范相容算子）**：
1. 称 $x, y \in \mathcal{X}$ **在分量 $i \in I$ 上不可区分**，若 $d_i(x, y) = 0$；称 $x, y$ **规范不可区分**（记作 $x \sim_{\mathcal{G}} y$），若 $\mathbf{d}(x, y) = \mathbf{0}$（即 $\forall\, i \in I,\; d_i(x, y) = 0$）。由伪度量公理知 $\sim_{\mathcal{G}}$ 是 $\mathcal{X}$ 上的等价关系；由隔离公理 $d_i(x,\bot)=+\infty$（$x\neq\bot$）及 $I\neq\emptyset$ 知 $[\bot]_{\sim_{\mathcal{G}}} = \{\bot\}$。
2. 设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$E \subseteq \mathrm{dom}(\phi)$。称 $\phi$ 在 $E$ 上是**规范相容的**（或**保零距的**），若
   $$\forall\, x, y \in E:\quad x \sim_{\mathcal{G}} y \implies \phi(x) \sim_{\mathcal{G}} \phi(y).$$
   称 $\phi$ 在 $E$ 上是**规范常值的**，若 $\forall\, x, y \in E,\; \phi(x) \sim_{\mathcal{G}} \phi(y)$。

> **注记（为何估计式定义在 $E \subseteq \mathrm{dom}(\phi)$ 上）**：
> 1. 若允许 $x \in \mathrm{dom}(\phi)$（$\phi(x)\neq\bot$）而 $y \in \mathcal{X}\setminus(\mathrm{dom}(\phi)\cup\{\bot\})$（$y\neq\bot$ 但 $\phi(y)=\bot$），则即使输入距离 $d_j(x,y) < +\infty$，输出距离也恒有 $d_i(\phi(x),\bot) = +\infty$，这会使一切非平凡部分算子丧失有限上界。
> 2. 在 $\mathcal{X}\setminus\mathrm{dom}(\phi)$ 上，$\phi$ 将所有点统一吸收至 $\bot$，恒有 $d_i(\phi(x),\phi(y))=d_i(\bot,\bot)=0$（定义域外部的吸收坍缩）。
> 3. 对算子复合 $\psi \circ \phi \in \mathcal{X}_{\mathrm{op}}$，由 $\psi(\bot)=\bot$ 立即得到有效定义域的精确传递律：
>    $$\mathrm{dom}(\psi \circ \phi) = \bigl\{\, x \in \mathrm{dom}(\phi) \;\big|\; \phi(x) \in \mathrm{dom}(\psi) \,\bigr\}.$$
>    因此将估计定义在子集 $E \subseteq \mathrm{dom}(\phi)$ 上（取 $E = \mathrm{dom}(\phi)$ 即为算子 $\phi$ 的全局特征），既支持局部区域分析，又与算子复合无缝相容。所有定义亦可直接推广至两个不同规范空间 $(\mathcal{X}, \{d_j\}_{j\in J}, \bot_{\mathcal{X}}) \to (\mathcal{Y}, \{d'_i\}_{i\in I}, \bot_{\mathcal{Y}})$ 间的 $I \times J$ 矩阵。

---

## 二、核心定义：三类算子特征矩阵

以下固定算子 $\phi \in \mathcal{X}_{\mathrm{op}}$ 及非空或任意子集 $E \subseteq \mathrm{dom}(\phi)$；当 $E = \mathrm{dom}(\phi)$ 时，简记 $\mathcal{L}^+(\phi) := \mathcal{L}^+_{\mathrm{dom}(\phi)}(\phi)$（其余同）。

### 2.1 扩展上界 Lipschitz 矩阵

**定义 2.1（扩展上界 Lipschitz 矩阵）**：称矩阵 $L = (L_{ij})_{i,j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$ 为 $\phi$ 在 $E$ 上的一个**扩展上界 Lipschitz 矩阵**，若对任意 $x, y \in E$ 及 $i \in I$，有

$$d_i(\phi(x), \phi(y)) \leq \sum_{j \in I} L_{ij}\, d_j(x, y), \qquad \text{即}\quad \mathbf{d}(\phi(x), \phi(y)) \preceq L\, \mathbf{d}(x, y).$$

记所有满足上式的矩阵集合为 $\mathcal{L}^+_E(\phi) \subseteq \bar{\mathbb{R}}_+^{I \times I}$。

**各取值的数学含义**：
- $L_{ij} = 0$：输出分量 $i$ 的上界完全不依赖输入分量 $j$（得益于 $0 \cdot (+\infty) = 0$，即便 $d_j(x,y) = +\infty$ 亦不产生贡献）；
- $0 < L_{ij} < +\infty$：输入分量 $j$ 对输出分量 $i$ 的有限线性放大率上限；
- $L_{ij} = +\infty$：允许非 Lipschitz 连续增长（如 $x \mapsto x^2$、间断跳变），或将有限输入距离映射为无限输出距离（$0 < d_j(x,y) < +\infty$ 而 $d_i(\phi(x),\phi(y)) = +\infty$）。

---

### 2.2 扩展下界 Lipschitz 矩阵（兼论逆向余 Lipschitz 矩阵）

**定义 2.2（扩展下界 Lipschitz 矩阵）**：称矩阵 $M = (M_{ij})_{i,j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$ 为 $\phi$ 在 $E$ 上的一个**扩展下界 Lipschitz 矩阵**，若对任意 $x, y \in E$ 及 $i \in I$，有

$$\sum_{j \in I} M_{ij}\, d_j(x, y) \leq d_i(\phi(x), \phi(y)), \qquad \text{即}\quad M\, \mathbf{d}(x, y) \preceq \mathbf{d}(\phi(x), \phi(y)).$$

记所有满足上式的矩阵集合为 $\mathcal{L}^-_E(\phi) \subseteq \bar{\mathbb{R}}_+^{I \times I}$。当 $M \in \mathcal{L}^-_E(\phi)$ 且 $L \in \mathcal{L}^+_E(\phi)$ 时，算子满足统一的**双侧矩阵夹逼估计**：

$$M\, \mathbf{d}(x, y) \preceq \mathbf{d}(\phi(x), \phi(y)) \preceq L\, \mathbf{d}(x, y) \quad (\forall\, x, y \in E).$$

**各取值的数学含义**：
- $M_{ij} = 0$：不对输入分量 $j$ 在输出分量 $i$ 中的保持率作正下界要求；
- $0 < M_{ij} < +\infty$：输入分量 $j$ 的距离至少以倍率 $M_{ij}$ 保真传递至输出分量 $i$（特别地，$d_j(x,y) = +\infty \implies d_i(\phi(x),\phi(y)) = +\infty$）；
- $M_{ij} = +\infty$：极端离散扩张——凡满足 $d_j(x,y) > 0$ 的输入对，其输出在分量 $i$ 上必有 $d_i(\phi(x), \phi(y)) = +\infty$。

> **定义 2.3（补充：逆向控制 / 联合余 Lipschitz 矩阵）**：在多分量情形（$|I| \geq 2$），还可定义**逆向控制矩阵** $K \in \bar{\mathbb{R}}_+^{I \times I}$，记其集合为 $\mathcal{K}_E(\phi)$：
> $$\mathbf{d}(x, y) \preceq K\, \mathbf{d}(\phi(x), \phi(y)) \quad (\forall\, x, y \in E).$$
> **两者的本质区别**：当 $|I|=1$ 且 $0 < m < +\infty$ 时，$m\,d(x,y) \leq d(\phi(x),\phi(y))$ 与 $d(x,y) \leq m^{-1} d(\phi(x),\phi(y))$ 完全等价；但当 $|I| \geq 2$ 时，$M \in \mathcal{L}^-_E(\phi)$ 要求**单一输出分量** $d_i(\phi(x),\phi(y))$ 独立地从下方控制 $\sum_j M_{ij} d_j(x,y)$，而 $K \in \mathcal{K}_E(\phi)$ 允许**联合多个输出分量**反推输入距离。
> - **反例**：设 $\mathcal{X} = \mathbb{R}^2 \cup \{\bot\}$，$d_1(x,y)=|x_1-y_1|$，$d_2(x,y)=|x_2-y_2|$，线性双射 $\phi(x_1,x_2) = (x_1+x_2, x_1-x_2)$。取 $x=(0,0), y=(1,-1)$ 有 $\mathbf{d}(x,y)=(1,1)$ 而 $d_1(\phi(x),\phi(y))=0$，迫使 $M_{11}=M_{12}=0$；取 $x=(0,0), y=(1,1)$ 有 $d_2(\phi(x),\phi(y))=0$，迫使 $M_{21}=M_{22}=0$。故 $\mathcal{L}^-(\phi) = \{\mathbf{0}\}$，但逆向矩阵 $K = \frac{1}{2}\begin{pmatrix}1 & 1\\ 1 & 1\end{pmatrix} \in \mathcal{K}(\phi)$ 非平凡成立。反之，对非单射算子（如常值算子或投影算子），$\mathcal{K}(\phi)$ 可为空集，而 $\mathcal{L}^-(\phi)$ 恒非空（$\mathbf{0} \in \mathcal{L}^-(\phi)$）。

---

### 2.3 不可区分阈值矩阵（坍缩矩阵）

现在严格化“当输入落入一定范畴，输出就不再可区分”的矩阵刻画。在规范空间中，“输出在分量 $i$ 上不可区分”即 $d_i(\phi(x), \phi(y)) = 0$；“输入在各分量上落入给定范畴”即各输入距离 $d_j(x,y)$ 不超过对应阈值 $\Theta_{ij}$。

**定义 2.4（不可区分阈值矩阵 / 坍缩矩阵）**：称矩阵 $\Theta = (\Theta_{ij})_{i,j \in I} \in \bar{\mathbb{R}}_+^{I \times I}$ 为 $\phi$ 在 $E$ 上的一个**不可区分阈值矩阵**（简称**坍缩矩阵**），若对任意 $x, y \in E$ 及 $i \in I$，有

$$\bigl(\forall\, j \in I,\; d_j(x, y) \leq \Theta_{ij}\bigr) \implies d_i(\phi(x), \phi(y)) = 0.$$

记所有满足上式的矩阵集合为 $\mathcal{T}_E(\phi) \subseteq \bar{\mathbb{R}}_+^{I \times I}$。

**各取值的数学含义与逆否命题解释**：
- $\Theta_{ij} = 0$：要求 $d_j(x,y) \leq 0$（即 $d_j(x,y) = 0$），在输入分量 $j$ 上无正宽度死区（注：此处必须采用非严格不等号 $\leq$ 而非 $<$，否则当 $\Theta_{ij}=0$ 时 $d_j(x,y) < 0$ 恒假，无法刻画零距保持与部分分量无关性，且在 $d_j(x,y)=+\infty$ 时无法命中 $\Theta_{ij}=+\infty$）；
- $0 < \Theta_{ij} < +\infty$：输入分量 $j$ 上的**有限分辨率死区半径**——只要各分量偏差均在对应阈值 $\Theta_{ij}$ 以内，输出分量 $i$ 即坍缩为不可区分；
- $\Theta_{ij} = +\infty$：条件 $d_j(x,y) \leq +\infty$ 恒成立，表示当其余分量满足各自阈值时，**输出分量 $i$ 对输入分量 $j$ 完全脱敏/无关**（即便 $d_j(x,y) = +\infty$ 亦不破坏输出不可区分性）。
- **逆否形式（可区分性激发阈值）**：$d_i(\phi(x), \phi(y)) > 0 \implies \exists\, j \in I,\; d_j(x, y) > \Theta_{ij}$，即欲使输出分量 $i$ 产生可观测区分，至少有一个输入分量 $j$ 的差异必须严格突破阈值 $\Theta_{ij}$。

---

## 三、基本性质与核心定理

### 定理 3.1（存在性统一定理与规范相容判据）
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$E \subseteq \mathrm{dom}(\phi)$。则：
1. **下界矩阵恒存在**：$\mathbf{0} \in \mathcal{L}^-_E(\phi)$ 对任意算子 $\phi$ 无条件成立。
2. **上界矩阵与坍缩矩阵的存在性等价判据**：下列五项互相等价：
   - **(a)** $\mathcal{L}^+_E(\phi) \neq \emptyset$；
   - **(b)** $\mathbf{\infty} \in \mathcal{L}^+_E(\phi)$；
   - **(c)** $\mathcal{T}_E(\phi) \neq \emptyset$；
   - **(d)** $\mathbf{0} \in \mathcal{T}_E(\phi)$；
   - **(e)** $\phi$ 在 $E$ 上是规范相容的（即 $x \sim_{\mathcal{G}} y \implies \phi(x) \sim_{\mathcal{G}} \phi(y)$）。

特别地，若 $(\mathcal{X}, \mathcal{G}, \bot)$ 满足族分离性（$x \sim_{\mathcal{G}} y \implies x = y$），则**任意算子** $\phi \in \mathcal{X}_{\mathrm{op}}$ 均满足 $\mathbf{\infty} \in \mathcal{L}^+(\phi)$ 与 $\mathbf{0} \in \mathcal{T}(\phi)$。

**证明**：
1. 由 $0 \cdot d_j(x,y) = 0 \leq d_i(\phi(x),\phi(y))$（含 $d_j(x,y)=+\infty$ 情形），$\mathbf{0} \in \mathcal{L}^-_E(\phi)$ 显然成立。
2. **(b) $\Rightarrow$ (a)** 与 **(d) $\Rightarrow$ (c)** 显然。
   - **(a) $\Rightarrow$ (e)**：设 $L \in \mathcal{L}^+_E(\phi)$。若 $x, y \in E$ 满足 $x \sim_{\mathcal{G}} y$，则 $\forall\, j \in I,\; d_j(x,y) = 0$。由 $L_{ij} \cdot 0 = 0$（即便 $L_{ij} = +\infty$）得
     $$d_i(\phi(x), \phi(y)) \leq \sum_{j \in I} L_{ij} \cdot 0 = 0 \implies d_i(\phi(x), \phi(y)) = 0 \quad (\forall\, i \in I),$$
     故 $\phi(x) \sim_{\mathcal{G}} \phi(y)$。
   - **(e) $\Rightarrow$ (b)**：设 $\phi$ 在 $E$ 上保 $\sim_{\mathcal{G}}$。对任意 $x, y \in E$ 与 $i \in I$：若 $\forall\, j \in I,\; d_j(x,y)=0$，则由 (e) 知 $d_i(\phi(x),\phi(y)) = 0 \leq \sum_j (+\infty)\cdot 0$；若存在 $j_0 \in I$ 使 $d_{j_0}(x,y) > 0$，则 $(+\infty) \cdot d_{j_0}(x,y) = +\infty$，从而 $\sum_{j \in I} (+\infty) \cdot d_j(x,y) = +\infty \geq d_i(\phi(x),\phi(y))$。故 $\mathbf{\infty} \in \mathcal{L}^+_E(\phi)$。
   - **(c) $\Rightarrow$ (e)**：设 $\Theta \in \mathcal{T}_E(\phi)$。若 $x \sim_{\mathcal{G}} y$，则 $\forall\, j,\; d_j(x,y) = 0 \leq \Theta_{ij}$，故 $\forall\, i,\; d_i(\phi(x),\phi(y)) = 0$。
   - **(e) $\Rightarrow$ (d)**：因 $d_j(x,y) \leq 0 \iff d_j(x,y) = 0$，条件 $\forall\, j,\; d_j(x,y) \leq 0$ 恰为 $x \sim_{\mathcal{G}} y$，由 (e) 即得 $\mathbf{0} \in \mathcal{T}_E(\phi)$。$\square$

> **注记**：定理 3.1 揭示了 CH1 两项基本约定的深刻关联——在 $0 \cdot (+\infty) = 0$ 且不预设族分离性时，扩展实数 $+\infty$ 能统一表达一切**规范良定（可在商集 $E/{\sim_{\mathcal{G}}}$ 上诱导映射）**的算子；唯一没有扩展 Lipschitz 矩阵的算子，恰是将规范不可区分点拆分为可区分点的“破缺相容性”算子。

---

### 定理 3.2（上界矩阵 $\mathcal{L}^+$ 与坍缩矩阵 $\mathcal{T}$ 的定性骨架对偶定理）
在二值定性矩阵集 $\{0, +\infty\}^{I \times I}$ 上定义逐元对合映射 $(\cdot)^\sharp$：

$$(A^\sharp)_{ij} := \begin{cases} +\infty, & A_{ij} = 0, \\ 0, & A_{ij} = +\infty. \end{cases}$$

则对任意 $\phi \in \mathcal{X}_{\mathrm{op}}$、$E \subseteq \mathrm{dom}(\phi)$ 及任意 $A \in \{0, +\infty\}^{I \times I}$，恒有

$$A \in \mathcal{L}^+_E(\phi) \iff A^\sharp \in \mathcal{T}_E(\phi).$$

由此立得以下推论：
1. **常值对偶**：$\mathbf{0} \in \mathcal{L}^+_E(\phi) \iff \mathbf{\infty} \in \mathcal{T}_E(\phi) \iff \phi$ 在 $E$ 上规范常值。
2. **恒等算子特征**：对恒等算子 $\mathrm{id}_{\mathcal{X}}$，有 $I_{\mathcal{G}} \in \mathcal{L}^+(\mathrm{id}_{\mathcal{X}}) \cap \mathcal{L}^-(\mathrm{id}_{\mathcal{X}})$，且其对偶矩阵 $(I_{\mathcal{G}})^\sharp$（对角元为 $0$、非对角元为 $+\infty$）满足 $(I_{\mathcal{G}})^\sharp \in \mathcal{T}(\mathrm{id}_{\mathcal{X}})$。
3. **由上界诱导坍缩支撑**：对任意一般的 $L \in \mathcal{L}^+_E(\phi)$，令 $\Theta^{\mathrm{supp}}(L)_{ij} := +\infty$（若 $L_{ij}=0$）及 $0$（若 $L_{ij}>0$），则必有 $\Theta^{\mathrm{supp}}(L) \in \mathcal{T}_E(\phi)$。

**证明**：设 $A \in \{0, +\infty\}^{I \times I}$。
- **($\Rightarrow$)** 设 $A \in \mathcal{L}^+_E(\phi)$。任取 $x, y \in E$ 及 $i \in I$，假设 $\forall\, j \in I,\; d_j(x,y) \leq (A^\sharp)_{ij}$。对每个 $j \in I$：
  - 若 $A_{ij} = 0$，则 $A_{ij}\,d_j(x,y) = 0 \cdot d_j(x,y) = 0$（含 $d_j(x,y)=+\infty$ 情形）；
  - 若 $A_{ij} = +\infty$，则 $(A^\sharp)_{ij} = 0$，由假设 $d_j(x,y) \leq 0$ 得 $d_j(x,y) = 0$，故仍有 $A_{ij}\,d_j(x,y) = (+\infty) \cdot 0 = 0$。
  于是 $d_i(\phi(x),\phi(y)) \leq \sum_{j \in I} A_{ij}\,d_j(x,y) = 0$，即 $d_i(\phi(x),\phi(y)) = 0$，故 $A^\sharp \in \mathcal{T}_E(\phi)$。
- **($\Leftarrow$)** 设 $A^\sharp \in \mathcal{T}_E(\phi)$。任取 $x, y \in E$ 及 $i \in I$：
  - 若对所有满足 $A_{ij} = +\infty$ 的 $j$ 均有 $d_j(x,y) = 0$，则对所有 $j \in I$ 皆有 $d_j(x,y) \leq (A^\sharp)_{ij}$（因 $A_{ij}=0$ 处 $(A^\sharp)_{ij}=+\infty$）。由 $A^\sharp \in \mathcal{T}_E(\phi)$ 得 $d_i(\phi(x),\phi(y)) = 0 \leq \sum_j A_{ij}\,d_j(x,y)$；
  - 否则存在 $j_0 \in I$ 使 $A_{ij_0} = +\infty$ 且 $d_{j_0}(x,y) > 0$，此时右端和式至少含一项 $(+\infty) \cdot d_{j_0}(x,y) = +\infty$，不等式自动成立。
  故 $A \in \mathcal{L}^+_E(\phi)$。推论 1—3 由定义及 $L \preceq \bigl(\Theta^{\mathrm{supp}}(L)\bigr)^\sharp$ 直接推出。$\square$

> **几何诠释**：二值骨架 $\{0,+\infty\}^{I\times I}$ 编码了算子各分量间的**定性依赖图**。在此共同骨架之上，$\mathcal{L}^+$ 将 $+\infty$ **向下细化**为有限增长率 $L_{ij} \in (0,+\infty)$，刻画敏感强度；而 $\mathcal{T}$ 将 $0$ **向上细化**为有限死区半径 $\Theta_{ij} \in (0,+\infty)$，刻画不敏感范围。这正是两类矩阵“对等性”的精确代数根源。

---

### 定理 3.3（序结构、帕累托前沿与多分量非唯一极值性）
在偏序集 $(\bar{\mathbb{R}}_+^{I \times I}, \preceq)$ 中：
1. **上下集单调性与凸性**：
   - $\mathcal{L}^+_E(\phi)$ 是**上集**（$L \in \mathcal{L}^+_E(\phi),\, L \preceq L' \implies L' \in \mathcal{L}^+_E(\phi)$）且为凸集；
   - $\mathcal{L}^-_E(\phi)$ 是**下集**（$M \in \mathcal{L}^-_E(\phi),\, M' \preceq M \implies M' \in \mathcal{L}^-_E(\phi)$）且为凸集；
   - $\mathcal{T}_E(\phi)$ 是**下集**（$\Theta \in \mathcal{T}_E(\phi),\, \Theta' \preceq \Theta \implies \Theta' \in \mathcal{T}_E(\phi)$）。
2. **链极限与极值元存在性**：
   - $\mathcal{L}^-_E(\phi)$ 对任意有向族的逐元上确界封闭，故由 Zorn 引理，$\mathcal{L}^-_E(\phi)$ **恒存在极大元**（帕累托最优下界矩阵）；
   - 当 $E$ 上各分量距离有限（$\forall\, x,y \in E,\, d_j(x,y) < +\infty$）且 $\mathcal{L}^+_E(\phi) \neq \emptyset$ 时，$\mathcal{L}^+_E(\phi)$ 对递减链的逐元下确界封闭，故存在**极小元**（帕累托最优上界矩阵）。若允许 $E$ 内出现 $d_j(x,y) = +\infty$，递减链下确界未必封闭（例如 $d(x,y)=+\infty$ 且 $d(\phi(x),\phi(y))=1$ 时，$L^{(n)} = 1/n \in \mathcal{L}^+_E(\phi)$，但 $\inf_n L^{(n)} = 0 \notin \mathcal{L}^+_E(\phi)$）。
3. **单分量与多分量极值结构对比**：
   - 当 $|I| = 1$（单一伪度量 $d$）时，下界集恒为闭区间 $[0, M^*(\phi)]$；若 $\phi$ 保零距且 $E$ 上距离有限，上界集为闭射线 $[L^*(\phi), +\infty]$，坍缩集为以 $\Theta^*(\phi) := \inf\{d(x,y) \mid x,y\in E,\, d(\phi(x),\phi(y)) > 0\}$ 为上确界的区间。
   - 当 $|I| \geq 2$ 时，**三类集合一般均不存在唯一的逐元最小/最大矩阵**（即 $\mathcal{L}^+$ 对逐元 $\min$ 不封闭，$\mathcal{L}^-$ 与 $\mathcal{T}$ 对逐元 $\max$ 不封闭）。

**证明**：(1) 由 $\bar{\mathbb{R}}_+$ 加法与乘法的单调性及实凸组合分配律立得。(2) 中对有向族 $\{M^{(\alpha)}\} \subseteq \mathcal{L}^-_E(\phi)$，由于对任意 $d \in \bar{\mathbb{R}}_+$（含 $d = +\infty$）乘法映射 $a \mapsto a \cdot d$ 保持任意上确界，且 $I$ 有限，故
$$\sum_{j \in I} \Bigl(\sup_\alpha M^{(\alpha)}_{ij}\Bigr) d_j(x,y) = \sup_\alpha \sum_{j \in I} M^{(\alpha)}_{ij}\, d_j(x,y) \leq d_i(\phi(x),\phi(y)),$$
从而 $\sup_\alpha M^{(\alpha)} \in \mathcal{L}^-_E(\phi)$；当 $d_j(x,y) < +\infty$ 时，有限和与递减链下确界可交换，故 $\mathcal{L}^+_E(\phi)$ 对递减链封闭。
对 (3) 的多分量反例：取两点空间 $\mathcal{X} = \{a, b, \bot\}$，$I = \{1, 2\}$，$d_1(a,b) = d_2(a,b) = 1$，算子 $\phi = \mathrm{id}_{\mathcal{X}}$。易验证
$$A^{(1)} = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}, \quad A^{(2)} = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$$
同时属于 $\mathcal{L}^+(\mathrm{id}_{\mathcal{X}})$ 与 $\mathcal{L}^-(\mathrm{id}_{\mathcal{X}})$，但逐元极小 $\min(A^{(1)}, A^{(2)}) = \mathbf{0} \notin \mathcal{L}^+(\mathrm{id}_{\mathcal{X}})$，逐元极大 $\max(A^{(1)}, A^{(2)}) = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix} \notin \mathcal{L}^-(\mathrm{id}_{\mathcal{X}})$（因 $1\cdot 1 + 1\cdot 1 = 2 \not\leq 1$）。同理，$(A^{(1)})^\sharp = \begin{pmatrix} 0 & +\infty \\ +\infty & 0 \end{pmatrix}$ 与 $(A^{(2)})^\sharp = \begin{pmatrix} +\infty & 0 \\ 0 & +\infty \end{pmatrix}$ 均属于 $\mathcal{T}(\mathrm{id}_{\mathcal{X}})$，但其逐元极大 $\mathbf{\infty} \notin \mathcal{T}(\mathrm{id}_{\mathcal{X}})$。这说明多分量算子的最优估计天然呈现为**帕累托前沿（Pareto frontier）**而非单一标量。$\square$

---

### 定理 3.4（下界矩阵 $M$ 与坍缩矩阵 $\Theta$ 的正交互补律）
设 $M \in \mathcal{L}^-_E(\phi)$，$\Theta \in \mathcal{T}_E(\phi)$。对于给定的指标对 $(i, j) \in I \times I$，若 $E$ 中存在一对输入点 $x, y \in E$ 使得

$$\bigl(\forall\, k \in I,\; d_k(x, y) \leq \Theta_{ik}\bigr) \quad \text{且} \quad d_j(x, y) > 0,$$

则必有 $M_{ij} = 0$。特别地，若分量 $j$ 在 $E$ 上可独立作任意小正扰动（即 $\forall\, \varepsilon > 0$，存在 $x, y \in E$ 使 $0 < d_j(x,y) \leq \varepsilon$ 且 $\forall\, k \neq j,\; d_k(x,y) = 0$），则恒有正交关系：

$$M_{ij} \cdot \Theta_{ij} = 0 \qquad (\text{即 } \Theta_{ij} > 0 \implies M_{ij} = 0,\; M_{ij} > 0 \implies \Theta_{ij} = 0).$$

**证明**：设 $x, y \in E$ 满足定理条件。由 $\Theta \in \mathcal{T}_E(\phi)$ 知 $d_i(\phi(x), \phi(y)) = 0$；再由 $M \in \mathcal{L}^-_E(\phi)$ 得
$$0 \leq M_{ij}\, d_j(x, y) \leq \sum_{k \in I} M_{ik}\, d_k(x, y) \leq d_i(\phi(x), \phi(y)) = 0,$$
故 $M_{ij}\, d_j(x, y) = 0$。在 $\bar{\mathbb{R}}_+$ 中，因 $d_j(x,y) > 0$，必有 $M_{ij} = 0$。若分量 $j$ 可独立作任意小正扰动，当 $\Theta_{ij} > 0$ 时取 $\varepsilon = \min(1, \Theta_{ij}) > 0$ 即得满足条件的 $(x, y)$，故 $M_{ij} = 0$。$\square$

---

### 定理 3.5（算子复合定律与跨矩阵耦合传播）
设 $\phi, \psi \in \mathcal{X}_{\mathrm{op}}$，复合算子为 $\psi \circ \phi \in \mathcal{X}_{\mathrm{op}}$。则在其有效定义域上成立以下四条复合律：
1. **上界半环乘法**：若 $L^{(\psi)} \in \mathcal{L}^+(\psi)$ 且 $L^{(\phi)} \in \mathcal{L}^+(\phi)$，则
   $$L^{(\psi)} L^{(\phi)} \in \mathcal{L}^+(\psi \circ \phi).$$
2. **下界半环乘法**：若 $M^{(\psi)} \in \mathcal{L}^-(\psi)$ 且 $M^{(\phi)} \in \mathcal{L}^-(\phi)$，则
   $$M^{(\psi)} M^{(\phi)} \in \mathcal{L}^-(\psi \circ \phi).$$
3. **纯坍缩复合律**：若 $\Theta^{(\psi)} \in \mathcal{T}(\psi)$ 且 $\Theta^{(\phi)} \in \mathcal{T}(\phi)$，定义矩阵 $\Theta^{(\psi)} \triangleleft \Theta^{(\phi)} \in \bar{\mathbb{R}}_+^{I \times I}$ 为
   $$\bigl(\Theta^{(\psi)} \triangleleft \Theta^{(\phi)}\bigr)_{ij} := \min_{\substack{k \in I \\ \Theta^{(\psi)}_{ik} < +\infty}} \Theta^{(\phi)}_{kj} \qquad (\text{约定 } \min \emptyset := +\infty),$$
   则 $\Theta^{(\psi)} \triangleleft \Theta^{(\phi)} \in \mathcal{T}(\psi \circ \phi)$。
4. **Lipschitz–坍缩混合传播律**：若 $\Theta^{(\psi)} \in \mathcal{T}(\psi)$ 且 $L^{(\phi)} \in \mathcal{L}^+(\phi)$，则对任意满足矩阵不等式
   $$\Delta \bigl(L^{(\phi)}\bigr)^\top \preceq \Theta^{(\psi)} \qquad \Bigl(\text{即 } \forall\, i, k \in I,\; \sum_{j \in I} \Delta_{ij}\, L^{(\phi)}_{kj} \leq \Theta^{(\psi)}_{ik}\Bigr)$$
   的矩阵 $\Delta \in \bar{\mathbb{R}}_+^{I \times I}$，必有 $\Delta \in \mathcal{T}(\psi \circ \phi)$。

**证明**：任取 $x, y \in \mathrm{dom}(\psi \circ \phi)$。由 $\psi(\bot) = \bot$ 知 $x, y \in \mathrm{dom}(\phi)$ 且 $\phi(x), \phi(y) \in \mathrm{dom}(\psi)$。
1. 对上界，由引理 1.1 的半环单调性与结合律：
   $$\mathbf{d}\bigl(\psi(\phi(x)), \psi(\phi(y))\bigr) \preceq L^{(\psi)} \mathbf{d}(\phi(x), \phi(y)) \preceq L^{(\psi)}\bigl(L^{(\phi)} \mathbf{d}(x, y)\bigr) = \bigl(L^{(\psi)} L^{(\phi)}\bigr) \mathbf{d}(x, y).$$
2. 对下界同理：
   $$\bigl(M^{(\psi)} M^{(\phi)}\bigr) \mathbf{d}(x, y) = M^{(\psi)}\bigl(M^{(\phi)} \mathbf{d}(x, y)\bigr) \preceq M^{(\psi)} \mathbf{d}(\phi(x), \phi(y)) \preceq \mathbf{d}\bigl(\psi(\phi(x)), \psi(\phi(y))\bigr).$$
3. 对纯坍缩复合：设 $\forall\, j \in I,\; d_j(x,y) \leq (\Theta^{(\psi)} \triangleleft \Theta^{(\phi)})_{ij}$。欲证 $d_i(\psi(\phi(x)), \psi(\phi(y))) = 0$，只需验证对每个中间分量 $k \in I$ 皆有 $d_k(\phi(x), \phi(y)) \leq \Theta^{(\psi)}_{ik}$：
   - 若 $\Theta^{(\psi)}_{ik} = +\infty$，不等式自动成立；
   - 若 $\Theta^{(\psi)}_{ik} < +\infty$，则由最小值定义知 $\forall\, j \in I,\; d_j(x,y) \leq \Theta^{(\phi)}_{kj}$，结合 $\Theta^{(\phi)} \in \mathcal{T}(\phi)$ 得 $d_k(\phi(x),\phi(y)) = 0 \leq \Theta^{(\psi)}_{ik}$。
   再由 $\Theta^{(\psi)} \in \mathcal{T}(\psi)$ 即得 $d_i(\psi(\phi(x)), \psi(\phi(y))) = 0$。
4. 对混合传播律：设 $\forall\, j \in I,\; d_j(x,y) \leq \Delta_{ij}$。则对每个 $k \in I$，由 $L^{(\phi)} \in \mathcal{L}^+(\phi)$ 及交换律有
   $$d_k(\phi(x), \phi(y)) \leq \sum_{j \in I} L^{(\phi)}_{kj}\, d_j(x, y) \leq \sum_{j \in I} L^{(\phi)}_{kj}\, \Delta_{ij} = \sum_{j \in I} \Delta_{ij}\, L^{(\phi)}_{kj} \leq \Theta^{(\psi)}_{ik}.$$
   由 $\Theta^{(\psi)} \in \mathcal{T}(\psi)$ 立得 $d_i(\psi(\phi(x)), \psi(\phi(y))) = 0$。$\square$

---

### 定理 3.6（链式坍缩效应：连通度量空间与超度量空间的二分现象）
设 $\Theta \in \mathcal{T}_E(\phi)$。若 $x_0, x_1, \dots, x_m \in E$ 构成一条有限步满足阈值条件 $\forall\, r \in \{1,\dots,m\},\, \forall\, j \in I,\; d_j(x_{r-1}, x_r) \leq \Theta_{ij}$ 的点链，则必有

$$d_i\bigl(\phi(x_0), \phi(x_m)\bigr) = 0.$$

**证明与空间结构推论**：由 $\Theta \in \mathcal{T}_E(\phi)$ 知每步均有 $d_i(\phi(x_{r-1}), \phi(x_r)) = 0$，再由伪度量三角不等式归纳得
$$d_i\bigl(\phi(x_0), \phi(x_m)\bigr) \leq \sum_{r=1}^m d_i\bigl(\phi(x_{r-1}), \phi(x_r)\bigr) = 0.$$
这一性质清晰地刻画了有限正阈值 $\Theta_{ij} \in (0, +\infty)$ 在哪类规范空间上非平凡：
- **链连通空间（如赋范线性空间的凸子集）**：若任意两点均可通过步长不超过 $\delta > 0$ 的点链相连，则只要某行满足 $\forall\, j,\; \Theta_{ij} > 0$，输出分量 $i$ 在整个 $E$ 上必然坍缩为常值（自动升级为 $\Theta_{ij} = +\infty$）。
- **超度量空间、离散簇空间或含间隙子集**：当伪度量满足超度量不等式 $d_j(x, z) \leq \max\{d_j(x, y), d_j(y, z)\}$（如符号序列空间、语法树空间、分层离散空间）时，闭球关系 $\{d_j(x,y) \leq \Theta_{ij}\}$ 本身是等价关系，不存在跨越球界的短步点链，此时有限正阈值 $\Theta_{ij} \in (0, +\infty)$ 非平凡且精确刻画算子的截断分辨率。

---

## 四、综合实例：多分量耦合算子的三矩阵刻画

设 $\mathcal{X} = \bigl(\mathbb{R} \times \{0,1\}^{\mathbb{N}}\bigr) \cup \{\bot\}$，指标集 $I = \{1, 2\}$。对非吸收元 $x = (r, \sigma),\, y = (s, \tau) \in \mathbb{R} \times \{0,1\}^{\mathbb{N}}$，定义规范族：
- $d_1(x, y) = |r - s|$（连续实分量伪度量）；
- $d_2(x, y) = 2^{-\min\{n \geq 0 \mid \sigma_n \neq \tau_n\}}$（序列超度量，约定 $\sigma = \tau$ 时为 $0$）；
- 补充 $d_i(x, \bot) = +\infty$（$x \neq \bot$），$d_i(\bot, \bot) = 0$。

考察算子 $\phi \in \mathcal{X}_{\mathrm{op}}$：当 $|r| \leq 10$ 时，定义

$$\phi(r, \sigma) := \bigl(\, 2r + \sigma_0,\; \mathrm{trunc}_N(\sigma) \,\bigr),$$

其中 $N \geq 1$ 为给定截断深度，$\mathrm{trunc}_N(\sigma)$ 将序列第 $N$ 位及以后全部置零；当 $|r| > 10$ 时置 $\phi(r, \sigma) = \bot$（即 $\mathrm{dom}(\phi) = [-10, 10] \times \{0,1\}^{\mathbb{N}}$）。

对任意 $x = (r,\sigma),\, y = (s,\tau) \in \mathrm{dom}(\phi)$：
1. **输出第 1 分量**：$d_1(\phi(x), \phi(y)) = |2(r-s) + (\sigma_0 - \tau_0)|$。注意若 $\sigma_0 \neq \tau_0$，则 $d_2(x,y) = 2^0 = 1$ 且 $|\sigma_0 - \tau_0| = 1 = d_2(x,y)$；若 $\sigma_0 = \tau_0$，则 $|\sigma_0 - \tau_0| = 0 \leq d_2(x,y)$。故恒有 $d_1(\phi(x),\phi(y)) \leq 2\,d_1(x,y) + 1\cdot d_2(x,y)$。同时，当 $(r,\sigma)=(0, 100\dots)$ 与 $(s,\tau)=(\frac{1}{2}, 000\dots)$ 时 $2(r-s)+(\sigma_0-\tau_0)=0$，故第 1 行下界元必为 $0$；而当 $d_1(x,y) \leq 0$ 且 $d_2(x,y) \leq 2^{-1}$（保证 $\sigma_0 = \tau_0$）时，$d_1(\phi(x),\phi(y)) = 0$。
2. **输出第 2 分量**：$d_2(\phi(x), \phi(y)) = d_2(\mathrm{trunc}_N(\sigma), \mathrm{trunc}_N(\tau))$ 完全独立于第 1 分量 $r,s$：始终有 $d_2(\phi(x),\phi(y)) \leq 1 \cdot d_2(x,y)$；因深层差异被抹除，正向分量下界为 $0$；而只要 $d_1(x,y) \leq +\infty$ 且 $d_2(x,y) \leq 2^{-N}$（即前 $N$ 位相同），必有 $d_2(\phi(x),\phi(y)) = 0$。

综上，该算子在 $\mathrm{dom}(\phi)$ 上的三类特征矩阵可精确给出为：

$$L = \begin{pmatrix} 2 & 1 \\ 0 & 1 \end{pmatrix} \in \mathcal{L}^+(\phi), \qquad M = \begin{pmatrix} 0 & 0 \\ 0 & 0 \end{pmatrix} \in \mathcal{L}^-(\phi), \qquad \Theta = \begin{pmatrix} 0 & 2^{-1} \\ +\infty & 2^{-N} \end{pmatrix} \in \mathcal{T}(\phi).$$

若进一步限制在子集 $E_0 = [-10,10] \times \{\sigma \mid \sigma_0 = 0\} \subseteq \mathrm{dom}(\phi)$ 上，第 1 分量的交叉干扰消失，三类矩阵立即可同步收紧为

$$L|_{E_0} = \begin{pmatrix} 2 & 0 \\ 0 & 1 \end{pmatrix}, \qquad M|_{E_0} = \begin{pmatrix} 2 & 0 \\ 0 & 0 \end{pmatrix}, \qquad \Theta|_{E_0} = \begin{pmatrix} 0 & +\infty \\ +\infty & 2^{-N} \end{pmatrix},$$

直观印证了 $(L, M, \Theta)$ 在分量耦合、正交互补（$M_{11}=2>0 \implies \Theta_{11}=0$，$\Theta_{22}=2^{-N}>0 \implies M_{22}=0$）与定性对偶（$L_{12}=0 \leftrightarrow \Theta_{12}=+\infty$，$L_{21}=0 \leftrightarrow \Theta_{21}=+\infty$）上的完整统一。
