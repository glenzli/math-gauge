在 CH1 扩展规范空间 $(\mathcal{X}, \mathcal{G}, \bot)$（$\mathcal{G} = \{d_i\}_{i\in I}$，$I$ 有限非空）的框架下，上述想法可以系统地严格化为**扩展值矩阵估计体系**：用 $\bar{\mathbb{R}}_+^{I \times I}$ 上的矩阵分别刻画算子的**上界敏感度（上 Lipschitz 矩阵）**、**下界保距/反演性（直接下 Lipschitz 矩阵与余 Lipschitz 矩阵）**，以及**阈值退化/不可区分性（坍缩矩阵）**。

下面给出自洽的公理化定义、基本性质及证明。

---

## 1. 预备结构与作用域约定

### 1.1 $\bar{\mathbb{R}}_+$ 上的矩阵半环与距离向量
记 $\bar{\mathbb{R}}_+ = [0, +\infty]$。按 CH1 约定，在 $\bar{\mathbb{R}}_+$ 上采用标准扩展非负实数算术：$a + (+\infty) = +\infty$，$0 \cdot (+\infty) = (+\infty) \cdot 0 = 0$，$a \cdot (+\infty) = (+\infty) \cdot a = +\infty$（$a > 0$）。

**引理 1.1（$\bar{\mathbb{R}}_+$ 半环性质）**
$(\bar{\mathbb{R}}_+, +, \cdot, 0, 1)$ 构成一个**完备有序交换半环**：
1. 加法与乘法均满足结合律、交换律，分配律 $a(b+c) = ab + ac$ 对所有 $a, b, c \in \bar{\mathbb{R}}_+$ 成立（注意当 $a = 0$ 时两端均为 $0$；当 $a = +\infty$ 时两端在 $b=c=0$ 处为 $0$，否则均为 $+\infty$）。
2. 保序性：若 $a \le a'$ 且 $b \le b'$，则 $a + b \le a' + b'$ 且 $ab \le a'b'$。

对矩阵 $A, B \in \bar{\mathbb{R}}_+^{I \times I}$ 与向量 $\mathbf{v} \in \bar{\mathbb{R}}_+^I$，定义标准矩阵乘法与作用：
$$
(AB)_{ij} := \sum_{k \in I} A_{ik} B_{kj}, \qquad (A\mathbf{v})_i := \sum_{j \in I} A_{ij} v_j,
$$
并采用逐分量偏序：$A \le B \iff \forall i, j \in I,\, A_{ij} \le B_{ij}$；$\mathbf{u} \le \mathbf{v} \iff \forall i \in I,\, u_i \le v_i$。由引理 1.1 立即得 $(AB)\mathbf{v} = A(B\mathbf{v})$，且算子 $A \mapsto A\mathbf{v}$、$\mathbf{v} \mapsto A\mathbf{v}$ 均保序。

对任意 $x, y \in \mathcal{X}$，定义**向量距离**：
$$
\mathbf{d}(x, y) := \bigl(d_i(x, y)\bigr)_{i \in I} \in \bar{\mathbb{R}}_+^I.
$$
记特殊矩阵：$O$ 为全 $0$ 矩阵，$E$（或 $I_{\mathrm{mat}}$）为单位矩阵 $\delta_{ij}$，$\mathbf{\infty}$ 为全 $+\infty$ 矩阵，$\mathrm{diag}_\infty$ 为对角元为 $+\infty$、非对角元为 $0$ 的矩阵。

---

### 1.2 $\mathcal{G}$-不可区分性与有效作用域的选择
由于 CH1 不预设族分离性，定义 $\mathcal{X}$ 上的**$\mathcal{G}$-不可区分关系** $\sim_{\mathcal{G}}$：
$$
x \sim_{\mathcal{G}} y \iff \forall i \in I,\; d_i(x, y) = 0 \quad (\text{即 } \mathbf{d}(x, y) = \mathbf{0}).
$$
由 CH1(i)–(iv) 知 $\sim_{\mathcal{G}}$ 是等价关系，且吸收元的等价类为单点集 $[\bot]_{\sim_{\mathcal{G}}} = \{\bot\}$。

设 $\phi \in \mathcal{X}_{\mathrm{op}}$，且取非空或任意子集 $D \subseteq \mathrm{dom}(\phi)$（**默认取最大有效作用域 $D = \mathrm{dom}(\phi)$**）。在建立具体估计前，先说明**为何必须在 $\mathrm{dom}(\phi)$（或其子集 $D$）上而非全空间 $\mathcal{X} \times \mathcal{X}$ 上定义估计**：

> **命题 1.2（有效定义域作用域的必要性）**
> 若将不等式量化于全空间 $\mathcal{X} \times \mathcal{X}$，则：
> 1. **零 Lip 矩阵失真**：设 $\phi(x) = c \neq \bot$（$\forall x \neq \bot$），$\phi(\bot) = \bot$ 为非退化常值算子。在全空间上取 $x = \bot, y = c$，有 $d_i(\phi(\bot), \phi(y)) = +\infty$ 而 $\sum_j 0 \cdot d_j(\bot, y) = 0$，故 $O$ 不是全空间 Lip 矩阵，合法上矩阵族在 $O$ 处不封闭（1D 时退化为开区间 $(0, +\infty]$）。
> 2. **部分算子边界爆炸**：若 $\emptyset \neq \mathrm{dom}(\phi) \subsetneq \mathcal{X} \setminus \{\bot\}$，且存在 $x \in \mathrm{dom}(\phi)$、$y \in \mathcal{X} \setminus (\mathrm{dom}(\phi) \cup \{\bot\})$ 使 $d_j(x, y) < +\infty$，则 $d_i(\phi(x), \phi(y)) = +\infty$ 迫使全空间上所有 $U_{ij} = +\infty$ 且所有下界 $M_{ij} = 0$，从而淹没 $\phi$ 在 $\mathrm{dom}(\phi)$ 上的精细结构。

因此，以下所有矩阵估计均以子集 $D \subseteq \mathrm{dom}(\phi)$ 为作用域（记号上，当 $D = \mathrm{dom}(\phi)$ 时可省去下标 $D$）。注意到若 $D = \emptyset$ 或 $|D| = 1$，则所有估计条件均平凡满足。

---

## 2. 核心定义：四类扩展规范估计矩阵

设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$D \subseteq \mathrm{dom}(\phi)$。

### 定义 2.1（上 Lipschitz 矩阵，Upper Lipschitz Matrix）
称 $U \in \bar{\mathbb{R}}_+^{I \times I}$ 为 $\phi$ 在 $D$ 上的一个**上 Lipschitz 矩阵**，若
$$
\forall x, y \in D,\ \forall i \in I,\qquad d_i\bigl(\phi(x), \phi(y)\bigr) \le \sum_{j \in I} U_{ij}\, d_j(x, y),
$$
即向量形式 $\mathbf{d}(\phi(x), \phi(y)) \le U\,\mathbf{d}(x, y)$。记所有这类矩阵的集合为 $\mathcal{U}_D(\phi)$。

---

### 定义 2.2（下界估计矩阵：直接型与余 Lipschitz 型）
在多分量伪度量下，一维的“下限” $m\,d(x,y) \le d(\phi(x),\phi(y))$（等价于 $d(x,y) \le m^{-1} d(\phi(x),\phi(y))$）会分化为两种不等价、各有侧重的矩阵概念：

1. **直接下 Lipschitz 矩阵（Direct Lower Matrix）**：称 $M \in \bar{\mathbb{R}}_+^{I \times I}$ 为 $\phi$ 在 $D$ 上的一个**直接下 Lipschitz 矩阵**，若
   $$
   \forall x, y \in D,\ \forall i \in I,\qquad \sum_{j \in I} M_{ij}\, d_j(x, y) \le d_i\bigl(\phi(x), \phi(y)\bigr),
   $$
   即 $M\,\mathbf{d}(x, y) \le \mathbf{d}(\phi(x), \phi(y))$。其全体记为 $\mathcal{M}_D(\phi)$。

2. **余 Lipschitz 矩阵 / 逆 Lipschitz 矩阵（Co-Lipschitz Matrix）**：称 $K \in \bar{\mathbb{R}}_+^{I \times I}$ 为 $\phi$ 在 $D$ 上的一个**余 Lipschitz 矩阵**，若
   $$
   \forall x, y \in D,\ \forall j \in I,\qquad d_j(x, y) \le \sum_{i \in I} K_{ji}\, d_i\bigl(\phi(x), \phi(y)\bigr),
   $$
   即 $\mathbf{d}(x, y) \le K\,\mathbf{d}(\phi(x), \phi(y))$。其全体记为 $\mathcal{K}_D(\phi)$。

> **注 2.3（为什么需要同时区分 $M$ 与 $K$？）**
> 当 $|I| = 1$ 时（忽略 $0/\infty$ 边界细节后），两者互为倒数关系；但在 $|I| \ge 2$ 时两者互不包含：
> - 考虑 $\mathcal{X} = \mathbb{R}^2 \cup \{\bot\}$（$d_1 = |x_1 - y_1|,\; d_2 = |x_2 - y_2|$）上的可逆线性映射 $\phi(x_1, x_2) = (x_1 + x_2,\, x_1 - x_2)$。取 $x - y = (1, -1)$ 得 $d_1(\phi(x),\phi(y)) = 0$，取 $x - y = (1, 1)$ 得 $d_2(\phi(x),\phi(y)) = 0$，故其**唯一**直接下矩阵为 $M = O$；但它却拥有有限余 Lipschitz 矩阵 $K = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$，准确刻画了其全局双 Lipschitz 可逆性。
> - 反之，对投影型算子 $\phi(x_1, x_2) = (2x_1, 0)$，由于丢弃了第 2 分量，故**不存在**任何 $K \in \bar{\mathbb{R}}_+^{2 \times 2}$；然而它拥有直接下矩阵 $M = \begin{pmatrix} 2 & 0 \\ 0 & 0 \end{pmatrix}$，能局部保留第 1 分量的扩张下界。
> - 直观上：$M$ 与 $U$ 构成**正向夹逼** $M\mathbf{d}(x,y) \le \mathbf{d}(\phi(x),\phi(y)) \le U\mathbf{d}(x,y)$，而 $K$ 刻画**整体信息不丢失与逆映射的稳健性**。

---

### 定义 2.4（不可区分矩阵 / 坍缩矩阵，Collapse Matrix）
为了刻画“当输入差异落入一定范畴时，输出在相应分量上不再可区分”，我们提出与上、下 Lipschitz 矩阵完全对等的矩阵定义：

称 $C \in \bar{\mathbb{R}}_+^{I \times I}$ 为 $\phi$ 在 $D$ 上的一个**坍缩矩阵（或不可区分阈值矩阵）**，若
$$
\forall x, y \in D,\ \forall i \in I,\qquad \sum_{j \in I} C_{ij}\, d_j(x, y) < 1 \implies d_i\bigl(\phi(x), \phi(y)\bigr) = 0,
$$
即 $(C\,\mathbf{d}(x, y))_i < 1 \implies d_i(\phi(x), \phi(y)) = 0$。等价的逆否表述为：
$$
\forall x, y \in D,\ \forall i \in I,\qquad d_i\bigl(\phi(x), \phi(y)\bigr) > 0 \implies \sum_{j \in I} C_{ij}\, d_j(x, y) \ge 1.
$$
其全体记为 $\mathcal{C}_D(\phi)$。

> **注 2.5（矩阵元素 $C_{ij}$ 的几何与算子含义，以及为何采用“严格 $<1$”）**
> 1. **元素含义**：$C_{ij}$ 的量纲是“输入第 $j$ 分量距离的倒数”（可理解为**分辨率门槛 / 灵敏度逆半径**）：
>    - $C_{ij} = 0$：由 $0 \cdot (+\infty) = 0$，无论 $d_j(x, y)$ 多大（包括 $+\infty$），都不影响坍缩条件，即**输出分量 $i$ 对输入分量 $j$ 完全不敏感**；特别地，若第 $i$ 行为全 $0$，则 $\phi$ 在分量 $i$ 上在 $D$ 内常值（模 $d_i=0$）。
>    - $C_{ij} \in (0, +\infty)$：赋予分量 $j$ 一个有限容差权重（1D 时坍缩半径即为 $1/C$）。
>    - $C_{ij} = +\infty$：因 $(+\infty)\cdot 0 = 0 < 1$ 而 $(+\infty)\cdot t = +\infty \not< 1$（$t>0$），第 $j$ 分量仅在 $d_j(x,y) = 0$ 时才允许坍缩。特别地，若某行全为 $+\infty$，仅表达“当输入全分量不可区分时，输出分量 $i$ 不可区分”。
> 2. **为何取 $< 1$ 而非 $\le 1$**：
>    - 逆否条件 $\sum_j C_{ij} d_j(x,y) \ge 1$ 是**闭不等式**，使得一维时的极小坍缩系数 $C^* = 1/\delta_D(\phi)$ 在边界可达（例如集群间距离恰好为 $\delta > 0$ 时，$C = 1/\delta$ 本身合法，若用 $\le 1$ 则仅 $(1/\delta, +\infty]$ 合法且下确界不可达）。
>    - 且与方盒型条件 $(\forall j,\, d_j(x,y) \le R_{ij}) \implies d_i(\phi(x),\phi(y)) = 0$ 相比（注：方盒若用 $< R_{ij}$ 在 $R_{ij}=0$ 时会退化为空条件，无法表达“要求 $d_1=0$ 但忽略 $d_2$”），线性阈值 $(C\mathbf{d})_i < 1$ 同时避开了除法与 $\pm\infty$ 歧义，并直接与上 Lipschitz 矩阵形成乘法复合（见第 4 节）。在有限维上，方盒与单纯形至多差因子 $|I|$。
> 3. **局部定点或死区**：若需表达类似 ReLU 在原点附近或某区域内的局部坍缩，只需将作用域 $D$ 取为该区域（此时 $C = O$），或将 $y$ 固定为参考点 $x_0 \in D$ 得到**定点局部坍缩矩阵**：$(C\mathbf{d}(x, x_0))_i < 1 \implies d_i(\phi(x), \phi(x_0)) = 0$。

---

## 3. 存在性边界、$\infty$ 的统一边界与结构性质

### 定理 3.1（$\infty$ 扩展的统一能力与精确刻画）
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$D \subseteq \mathrm{dom}(\phi)$。则：
1. **对 $\mathcal{M}_D(\phi)$**：恒非空，因为 $O \in \mathcal{M}_D(\phi)$。
2. **对 $\mathcal{U}_D(\phi)$ 与 $\mathcal{C}_D(\phi)$**：以下五个条件等价：
   - (a) $\mathcal{U}_D(\phi) \neq \emptyset$；
   - (b) $\mathbf{\infty} \in \mathcal{U}_D(\phi)$；
   - (c) $\mathcal{C}_D(\phi) \neq \emptyset$；
   - (d) $\mathbf{\infty} \in \mathcal{C}_D(\phi)$；
   - (e) $\phi|_D$ **保持 $\mathcal{G}$-不可区分性**（即 $\forall x, y \in D,\; x \sim_{\mathcal{G}} y \implies \phi(x) \sim_{\mathcal{G}} \phi(y)$）。
3. **对 $\mathcal{K}_D(\phi)$**：以下三个条件等价：
   - (a) $\mathcal{K}_D(\phi) \neq \emptyset$；
   - (b) $\mathbf{\infty} \in \mathcal{K}_D(\phi)$；
   - (c) $\phi|_D$ **反射 $\mathcal{G}$-不可区分性**（即 $\forall x, y \in D,\; \phi(x) \sim_{\mathcal{G}} \phi(y) \implies x \sim_{\mathcal{G}} y$，亦即在商空间 $D/\!\sim_{\mathcal{G}}$ 上单射）。

**证明**：
- $(2)$ 中 (b)$\Rightarrow$(a) 与 (d)$\Rightarrow$(c) 平凡。若 (a) 成立，取 $U \in \mathcal{U}_D(\phi)$，对任意 $x, y \in D$ 若 $x \sim_{\mathcal{G}} y$，则 $d_j(x,y) = 0$（$\forall j$），由 $U_{ij}\cdot 0 = 0$（包括 $U_{ij} = +\infty$）得 $d_i(\phi(x), \phi(y)) \le 0$，即 (e) 成立；同理若 (c) 成立，取 $C \in \mathcal{C}_D(\phi)$，当 $d_j(x,y)=0$（$\forall j$）时 $\sum_j C_{ij} \cdot 0 = 0 < 1$，故 $d_i(\phi(x),\phi(y)) = 0$，也得 (e)。反之若 (e) 成立，对矩阵 $\mathbf{\infty}$：若 $\forall j,\, d_j(x,y) = 0$，则由 (e) 得 $\forall i,\, d_i(\phi(x), \phi(y)) = 0$，满足上界 $\le 0$ 且满足坍缩结论 $=0$；若存在 $j_0$ 使 $d_{j_0}(x,y) > 0$，则 $\sum_j (+\infty) d_j(x,y) = +\infty$，既 $\ge d_i(\phi(x),\phi(y))$（得 (b)），又不满足 $< 1$ 从而使坍缩蕴含空真（得 (d)）。
- $(3)$ 的证明完全对偶：将 $(x, y)$ 与 $(\phi(x), \phi(y))$ 角色互换即可。 $\square$

> **注 3.2（关于不保 $\sim_{\mathcal{G}}$ 算子的处理）**
> 定理 3.1 揭示了一个由 CH1 公理“$0 \cdot (+\infty) = 0$”与“不预设族分离性”共同决定的精确边界：
> - 若 $\mathcal{G}$ 分离（或 $\phi$ 在商空间 $\mathcal{X}/\!\sim_{\mathcal{G}}$ 上良定义），则所有算子（包括无界、不连续算子）均自动满足 (e)，从而**支持 $+\infty$ 的矩阵确实提供了完全统一的表达**。
> - 一般地，保 $\sim_{\mathcal{G}}$ 算子族 $\mathcal{X}_{\mathrm{op}}^{\sim} := \{ \phi \in \mathcal{X}_{\mathrm{op}} \mid \forall x,y \in \mathrm{dom}(\phi),\; x \sim_{\mathcal{G}} y \implies \phi(x) \sim_{\mathcal{G}} \phi(y) \}$ 构成 $(\mathcal{X}_{\mathrm{op}}, \circ, \mathrm{id}_{\mathcal{X}})$ 的一个子幺半群。若强行把不保 $\sim_{\mathcal{G}}$ 的算子也纳入统一符号体系，应在矩阵集外添设一个顶元 $\top_{\mathrm{mat}}$（表示“在零距离处即跃迁，无法被任何 $\bar{\mathbb{R}}_+^{I\times I}$ 矩阵控制”），而不宜在标量半环 $\bar{\mathbb{R}}_+$ 中引入破坏 $0\cdot(\cdot)=0$ 的元素（否则会破坏矩阵乘法对零列分量的屏蔽性质）。

---

### 定理 3.3（序结构、凸性与闭性）
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$D \subseteq \mathrm{dom}(\phi)$。在 $[0, +\infty]^{I \times I}$ 上赋予逐元乘积序拓扑。则：
1. **按行解耦**：四类矩阵集合均按行直积分解，如 $\mathcal{U}_D(\phi) = \prod_{i\in I} \mathcal{U}_{D,i}(\phi)$，$\mathcal{C}_D(\phi) = \prod_{i\in I} \mathcal{C}_{D,i}(\phi)$ 等。
2. **单调闭性**：$\mathcal{U}_D(\phi)$、$\mathcal{K}_D(\phi)$、$\mathcal{C}_D(\phi)$ 均为**上闭集**（若 $A$ 合法且 $A \le B$，则 $B$ 合法）；$\mathcal{M}_D(\phi)$ 为**下闭集**（若 $M$ 合法且 $M' \le M$，则 $M'$ 合法）。
3. **凸性**：$\mathcal{U}_D(\phi)$、$\mathcal{M}_D(\phi)$、$\mathcal{K}_D(\phi)$、$\mathcal{C}_D(\phi)$ 均对凸组合 $\lambda A + (1-\lambda) B$（$\lambda \in [0, 1]$）封闭。
4. **拓扑闭性（注意 $+\infty$ 距离下的边界差异）**：
   - $\mathcal{M}_D(\phi)$ 在 $[0, +\infty]^{I \times I}$ 中**恒为闭集**。
   - 若所有 $d_j|_{D \times D} < +\infty$（或对 $\mathcal{K}_D(\phi)$ 要求 $d_i|_{\phi(D)\times\phi(D)} < +\infty$），则 $\mathcal{U}_D(\phi)$、$\mathcal{K}_D(\phi)$、$\mathcal{C}_D(\phi)$ 在 $[0, +\infty]^{I \times I}$ 中也为**闭集**。
   - 若 $D$ 内允许 $d_j(x, y) = +\infty$，则因 $u \mapsto u \cdot (+\infty)$ 在 $u = 0$ 处仅下半连续而不上半连续，$\mathcal{U}_D(\phi)$、$\mathcal{K}_D(\phi)$、$\mathcal{C}_D(\phi)$ 仅保证在 $(0, +\infty]^{I \times I}$ 中相对闭。

**证明**：
- (1)、(2) 由定义与引理 1.1 保序性直接得到。
- (3) 对 $\lambda \in \{0, 1\}$ 平凡。设 $\lambda \in (0, 1)$。对 $\mathcal{U}_D, \mathcal{M}_D, \mathcal{K}_D$，线性组合直接保持 $\le$ 或 $\ge$（当出现 $+\infty$ 时，因 $\lambda, 1-\lambda > 0$，两侧亦一致为 $+\infty$）。对 $\mathcal{C}_D(\phi)$，采用逆否形式：若 $d_i(\phi(x), \phi(y)) > 0$ 且 $C^{(1)}, C^{(2)} \in \mathcal{C}_D(\phi)$，则 $\sum_j C^{(1)}_{ij} d_j(x,y) \ge 1$ 且 $\sum_j C^{(2)}_{ij} d_j(x,y) \ge 1$，从而
  $$
  \sum_{j\in I} \bigl(\lambda C^{(1)}_{ij} + (1-\lambda) C^{(2)}_{ij}\bigr) d_j(x, y) = \lambda \sum_j C^{(1)}_{ij} d_j(x, y) + (1-\lambda) \sum_j C^{(2)}_{ij} d_j(x, y) \ge 1,
  $$
  故 $\lambda C^{(1)} + (1-\lambda) C^{(2)} \in \mathcal{C}_D(\phi)$。
- (4) 函数 $u \mapsto u \cdot d$（$d \in [0, +\infty]$）在 $[0, +\infty]$ 上恒**下半连续**（仅当 $d = +\infty$ 且 $u_n \downarrow 0$ 时 $\lim u_n d = +\infty > 0 = 0\cdot d$）。因此形如 $\sum_j M_{ij} d_j(x,y) \le d_i(\phi(x),\phi(y))$ 的下水平集总闭，即 $\mathcal{M}_D(\phi)$ 恒闭。而在 $\mathcal{U}_D(\phi)$ 与 $\mathcal{C}_D(\phi)$（逆否式 $\sum_j C_{ij} d_j(x,y) \ge 1$）中涉及上水平集：当 $d_j|_{D\times D} < +\infty$ 时映射 $u \mapsto u \cdot d_j(x,y)$ 在 $[0, +\infty]$ 上连续（注意当 $d_j = 0$ 时恒为 $0$；当 $0 < d_j < +\infty$ 时在 $+\infty$ 处连续），从而上水平集为闭集。若存在 $x, y \in D$ 使 $d_j(x,y) = +\infty$ 且 $d_i(\phi(x),\phi(y)) \in (0, +\infty]$，则序列 $U^{(n)}_{ij} = 1/n$ 满足 $(1/n)\cdot(+\infty) = +\infty \ge d_i(\phi(x),\phi(y))$，而极限 $0 \cdot (+\infty) = 0$ 失效（对 $\mathcal{C}_D(\phi)$ 取 $C^{(n)}_{ij} = 1/n$ 同理）；但在 $(0, +\infty]^{I\times I}$ 中不经过 $0$，映射连续，故相对闭。 $\square$

---

### 命题 3.4（一维极值公式与多维 Pareto 前沿的非唯一性）
1. **一维退化（$|I| = 1$）**：设 $\phi|_D$ 保 $0$-距离且距离在 $D$ 上取有限值，则最优常数均可精确显式表达并取到：
   - $\mathcal{U}_D(\phi) = [L^*, +\infty]$，其中 $L^* = \sup\bigl\{ \frac{d(\phi(x),\phi(y))}{d(x,y)} \;\big|\; x, y \in D,\; d(x,y) > 0 \bigr\}$（约定 $\sup \emptyset = 0$）；
   - $\mathcal{M}_D(\phi) = [0, m^*]$，其中 $m^* = \inf\bigl\{ \frac{d(\phi(x),\phi(y))}{d(x,y)} \;\big|\; x, y \in D,\; d(x,y) > 0 \bigr\}$（约定 $\inf \emptyset = +\infty$）；
   - $\mathcal{C}_D(\phi) = [c^*, +\infty]$，其中 $c^* = \frac{1}{\delta_D(\phi)}$，$\delta_D(\phi) := \inf\bigl\{ d(x, y) \;\big|\; x, y \in D,\; d(\phi(x),\phi(y)) > 0 \bigr\}$（约定 $1/0 = +\infty,\; 1/(+\infty) = 0$）。
2. **多维非唯一性（$|I| \ge 2$）**：当输入规范分量间存在耦合时，一般**不存在**逐元素最小的上 Lip / 坍缩矩阵或逐元素最大的下矩阵，合法集合由 Pareto 极小（大）边界刻画。
   - **例**：取 $\mathcal{X} = \mathbb{R} \cup \{\bot\}$，$I = \{1, 2\}$ 且 $d_1 = d_2 = |x - y|$，$\phi = \mathrm{id}_{\mathcal{X}}$。则第 1 行在 $\mathcal{U}(\mathrm{id})$ 中的条件为 $U_{11} + U_{12} \ge 1$，故 $(1, 0)$ 与 $(0, 1)$ 均为极小行向量，但其逐元下确界 $(0, 0) \notin \mathcal{U}_1(\mathrm{id})$。同理 $(1, 0), (0, 1)$ 在 $\mathcal{M}_1(\mathrm{id})$ 中均为极大元而逐元上确界 $(1, 1) \notin \mathcal{M}_1(\mathrm{id})$；若取 $\mathcal{X} = \mathbb{Z} \cup \{\bot\}$，坍缩矩阵第 1 行满足 $C_{11} + C_{12} \ge 1$，亦无唯一最小元。

---

## 4. 恒等算子、复合代数与迭代坍缩

### 命题 4.1（恒等算子 $\mathrm{id}_{\mathcal{X}}$）
对 $\mathrm{id}_{\mathcal{X}} \in \mathcal{X}_{\mathrm{op}}$（$\mathrm{dom}(\mathrm{id}_{\mathcal{X}}) = \mathcal{X}\setminus\{\bot\}$）：
$$
E \in \mathcal{U}(\mathrm{id}_{\mathcal{X}}) \cap \mathcal{M}(\mathrm{id}_{\mathcal{X}}) \cap \mathcal{K}(\mathrm{id}_{\mathcal{X}}), \qquad \mathrm{diag}_\infty \in \mathcal{C}(\mathrm{id}_{\mathcal{X}}).
$$
（验证：$(\mathrm{diag}_\infty\,\mathbf{d}(x,y))_i = (+\infty)\cdot d_i(x,y) < 1 \iff d_i(x,y) = 0$。）

---

### 定理 4.2（复合运算法则）
设 $\phi, \psi \in \mathcal{X}_{\mathrm{op}}$，且 $D \subseteq \mathrm{dom}(\psi \circ \phi) = \{x \in \mathrm{dom}(\phi) \mid \phi(x) \in \mathrm{dom}(\psi)\}$。此时自动有 $D \subseteq \mathrm{dom}(\phi)$ 且 $\phi(D) \subseteq \mathrm{dom}(\psi)$。以下矩阵复合均成立：
1. **上 Lipschitz（协变）**：若 $U_\phi \in \mathcal{U}_D(\phi)$，$U_\psi \in \mathcal{U}_{\phi(D)}(\psi)$，则 $U_\psi U_\phi \in \mathcal{U}_D(\psi \circ \phi)$。
2. **直接下 Lipschitz（协变）**：若 $M_\phi \in \mathcal{M}_D(\phi)$，$M_\psi \in \mathcal{M}_{\phi(D)}(\psi)$，则 $M_\psi M_\phi \in \mathcal{M}_D(\psi \circ \phi)$。
3. **余 Lipschitz（反变）**：若 $K_\phi \in \mathcal{K}_D(\phi)$，$K_\psi \in \mathcal{K}_{\phi(D)}(\psi)$，则 $K_\phi K_\psi \in \mathcal{K}_D(\psi \circ \phi)$。
4. **坍缩矩阵的三条复合律**：
   对任意矩阵 $A \in \bar{\mathbb{R}}_+^{I \times I}$，定义其支撑指示矩阵 $S(A) \in \{0, 1\}^{I \times I}$ 为 $S(A)_{mi} = 1$（当 $A_{mi} > 0$）及 $0$（当 $A_{mi} = 0$）；再定义行支撑极大合成 $\diamond$：
   $$
   (A \diamond B)_{mj} := \max\bigl\{\, B_{ij} \;\big|\; i \in I,\; A_{mi} > 0 \,\bigr\} \qquad (\max \emptyset := 0).
   $$
   则：
   - **(4a) 左坍缩 $\circ$ 右上 Lip**：若 $U_\phi \in \mathcal{U}_D(\phi)$，$C_\psi \in \mathcal{C}_{\phi(D)}(\psi)$，则 $C_\psi U_\phi \in \mathcal{C}_D(\psi \circ \phi)$。
   - **(4b) 左上 Lip $\circ$ 右坍缩**：若 $C_\phi \in \mathcal{C}_D(\phi)$，$U_\psi \in \mathcal{U}_{\phi(D)}(\psi)$，则 $U_\psi \diamond C_\phi \in \mathcal{C}_D(\psi \circ \phi)$（从而更粗的矩阵乘积 $S(U_\psi) C_\phi$ 亦属于 $\mathcal{C}_D(\psi \circ \phi)$）。
   - **(4c) 纯坍缩封闭律**：若 $C_\phi \in \mathcal{C}_D(\phi)$，$C_\psi \in \mathcal{C}_{\phi(D)}(\psi)$，则 $C_\psi \diamond C_\phi \in \mathcal{C}_D(\psi \circ \phi)$（且 $S(C_\psi) C_\phi \in \mathcal{C}_D(\psi \circ \phi)$）。

**证明**：
- (1)–(3) 由引理 1.1 的保序性与结合律直接串联即得：例如对 $x, y \in D$，
  $\mathbf{d}(\psi(\phi(x)), \psi(\phi(y))) \le U_\psi \mathbf{d}(\phi(x), \phi(y)) \le U_\psi (U_\phi \mathbf{d}(x, y)) = (U_\psi U_\phi) \mathbf{d}(x, y)$。
- (4a)：对 $x, y \in D$，若 $(C_\psi U_\phi \mathbf{d}(x, y))_i < 1$，则由 $(C_\psi \mathbf{d}(\phi(x), \phi(y)))_i \le (C_\psi (U_\phi \mathbf{d}(x, y)))_i = (C_\psi U_\phi \mathbf{d}(x, y))_i < 1$（包括 $0 \cdot (+\infty) = 0$ 情形），由 $C_\psi \in \mathcal{C}_{\phi(D)}(\psi)$ 即得 $d_i(\psi(\phi(x)), \psi(\phi(y))) = 0$。
- (4b)：设 $((U_\psi \diamond C_\phi)\mathbf{d}(x, y))_m < 1$。对所有满足 $(U_\psi)_{mi} > 0$ 的分量 $i$，由 $(C_\phi)_{ij} \le (U_\psi \diamond C_\phi)_{mj}$ 得 $\sum_j (C_\phi)_{ij} d_j(x, y) < 1$，故 $d_i(\phi(x), \phi(y)) = 0$。而对 $(U_\psi)_{mi} = 0$ 的分量 $i$，有 $(U_\psi)_{mi} d_i(\phi(x), \phi(y)) = 0$（即使 $d_i(\phi(x), \phi(y)) = +\infty$）。于是 $d_m(\psi(\phi(x)), \psi(\phi(y))) \le \sum_i (U_\psi)_{mi} d_i(\phi(x), \phi(y)) = 0$。又 $U_\psi \diamond C_\phi \le S(U_\psi) C_\phi$，由上闭性即得 $S(U_\psi) C_\phi \in \mathcal{C}_D(\psi \circ \phi)$。
- (4c)：设 $((C_\psi \diamond C_\phi)\mathbf{d}(x, y))_m < 1$。同理可知对所有 $(C_\psi)_{mk} > 0$ 的 $k$ 均有 $d_k(\phi(x), \phi(y)) = 0$，于是 $\sum_k (C_\psi)_{mk} d_k(\phi(x), \phi(y)) = 0 < 1$（因 $(C_\psi)_{mk}=0$ 项贡献 $0\cdot(+\infty)=0$），由 $C_\psi \in \mathcal{C}_{\phi(D)}(\psi)$ 得 $d_m(\psi(\phi(x)), \psi(\phi(y))) = 0$。 $\square$

---

### 推论 4.3（迭代传播与有限步全局坍缩）
若 $\phi(D) \subseteq D$（例如 $\mathrm{dom}(\phi^2) = \mathrm{dom}(\phi)$ 且取 $D = \mathrm{dom}(\phi)$），则对一切 $n \ge 1$：
$$
U \in \mathcal{U}_D(\phi) \implies U^n \in \mathcal{U}_D(\phi^n), \qquad
C \in \mathcal{C}_D(\phi),\; U \in \mathcal{U}_D(\phi) \implies C U^{n-1} \in \mathcal{C}_D(\phi^n).
$$
特别地，若 $D$ 具有有限 $\mathcal{G}$-直径（即 $\exists \mathbf{B} \in [0, +\infty)^I$ 使 $\forall x, y \in D,\; \mathbf{d}(x,y) \le \mathbf{B}$），$C \in \mathcal{C}_D(\phi)$ 为有限矩阵，且 $U \in \mathcal{U}_D(\phi)$ 为有限矩阵且谱半径 $\rho(U) < 1$，则 $U^n \to O$，故存在有限步数 $N \ge 1$ 使 $(C U^{N-1}\mathbf{B})_i < 1$（$\forall i \in I$），从而 **$\phi^N(D)$ 完全坍缩为单一的 $\sim_{\mathcal{G}}$-等价类**。

---

## 5. 矩阵间的交互定理、刚性与标量化归约

### 命题 5.1（四类矩阵之间的相互关系与相容约束）
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$D \subseteq \mathrm{dom}(\phi)$：
1. **上下夹逼（$M$ 与 $U$）**：若 $M \in \mathcal{M}_D(\phi)$ 且 $U \in \mathcal{U}_D(\phi)$，则对所有 $x, y \in D$ 有 $M\mathbf{d}(x,y) \le U\mathbf{d}(x,y)$。若对特定 $(i, j)$ 存在 $x, y \in D$ 使 $0 < d_j(x, y) < +\infty$ 且 $\forall k \neq j,\; d_k(x, y) = 0$，则必有 $M_{ij} \le U_{ij}$。
2. **直接下界导出余 Lipschitz（$M$ 到 $K$）**：设 $M \in \mathcal{M}_D(\phi)$，且对每个 $j \in I$ 均存在 $i(j) \in I$ 使 $M_{i(j), j} > 0$。构造矩阵 $K$ 如下（其中 $\varepsilon > 0$ 任意）：
   $$
   K_{j, i} := \begin{cases} 1 / M_{i(j), j}, & i = i(j) \text{ 且 } 0 < M_{i(j), j} < +\infty, \\ \varepsilon, & i = i(j) \text{ 且 } M_{i(j), j} = +\infty, \\ 0, & i \neq i(j). \end{cases}
   $$
   则 $K \in \mathcal{K}_D(\phi)$。（注：当 $M_{i(j),j} = +\infty$ 时，仅知 $d_j > 0 \Rightarrow d_{i(j)}(\phi(x),\phi(y)) = +\infty$，此时取 $\varepsilon = 0$ 会因 $0 \cdot (+\infty) = 0$ 失效，必须取 $\varepsilon > 0$。）
3. **上 Lipschitz 导出坍缩（$U$ 到 $C$）**：
   - 一般情形：若 $U \in \mathcal{U}_D(\phi)$，则 $C^{(U)} := \mathrm{diag}_\infty\, U \in \mathcal{C}_D(\phi)$（即 $C^{(U)}_{ij} = 0$ 当 $U_{ij} = 0$，否则为 $+\infty$）。这是定理 4.2(4a) 应用于 $\mathrm{id}\circ\phi$ 的特例。
   - **量子化输出情形**：若输出分量 $i$ 在 $\phi(D)$ 上具有正最小非零间隔 $\delta_i := \inf\{ d_i(u,v) \mid u, v \in \phi(D),\; d_i(u,v) > 0 \} \in (0, +\infty)$，则取 $C_{ij} := U_{ij}/\delta_i$ 即得 $C \in \mathcal{C}_D(\phi)$（因为 $(C\mathbf{d}(x,y))_i < 1 \Rightarrow d_i(\phi(x),\phi(y)) \le (U\mathbf{d}(x,y))_i < \delta_i \Rightarrow d_i(\phi(x),\phi(y)) = 0$）。
4. **坍缩与下界的互斥律（$C$ 与 $M$）**：若 $C \in \mathcal{C}_D(\phi)$ 且 $M \in \mathcal{M}_D(\phi)$，则对任意 $x, y \in D$，一旦 $(C\mathbf{d}(x, y))_i < 1$，必有 $\forall j \in I,\; M_{ij} d_j(x, y) = 0$。故只要在坍缩区域 $\{ (x, y) \in D^2 \mid (C\mathbf{d}(x, y))_i < 1 \}$ 内存在 $d_j(x, y) > 0$ 的点对，必有 $M_{ij} = 0$。

---

### 定理 5.2（链连通空间上坍缩矩阵的刚性定理）
设 $C \in \mathcal{C}_D(\phi)$，对固定行 $i \in I$ 记加权伪度量 $\rho_i(x, y) := \sum_{j \in I} C_{ij} d_j(x, y)$（由引理 1.1 知 $\rho_i$ 满足非负对称与三角不等式）。若 $x, y \in D$ 之间存在 $D$ 中的有限链 $x = z_0, z_1, \dots, z_N = y$ 满足 $\rho_i(z_{k-1}, z_k) < 1$（$k = 1, \dots, N$），则
$$
d_i\bigl(\phi(x), \phi(y)\bigr) = 0.
$$
**推论**：在每个 $(D, \rho_i)$ 的 $1$-链连通分支上，$\phi$ 在分量 $i$ 上必常值（模 $d_i=0$）。

**证明**：对每个 $k$ 由 $\rho_i(z_{k-1}, z_k) < 1$ 及 $C \in \mathcal{C}_D(\phi)$ 得 $d_i(\phi(z_{k-1}), \phi(z_k)) = 0$，对 $d_i$ 反复应用三角不等式即得 $d_i(\phi(x), \phi(y)) \le \sum_{k=1}^N d_i(\phi(z_{k-1}), \phi(z_k)) = 0$。 $\square$

> **意义解释**：该定理阐明了坍缩矩阵 $C$ 在何种结构中取有限非零值：
> - 若 $(D, d_j)$ 是像 $\mathbb{R}$ 一样的连通无间隙空间且全行 $C_{ij} < +\infty$，则刚性定理迫使 $\phi$ 在分量 $i$ 上全局常值（故行 $i$ 可降为全 $0$）；
> - 真正非平凡的有限非零 $C_{ij} \in (0, +\infty)$ 出现在**非连通 / 聚簇 / 离散间隔 / 分片有效域**（例如以 $+\infty$ 或正间隔分离的聚类空间、含 margin 的分类/量化算子）或**局部子区域 $D$** 中；而在连通空间中，$C_{ij} \in \{0, +\infty\}$ 的 $0/\infty$ 型坍缩矩阵仍非平凡，精确刻画“哪些输入分量可被完全忽略（$C_{ij}=0$）”。

---

### 命题 5.3（加权标量化与压缩归约）
取任意正权向量 $\mathbf{w} = (w_i)_{i\in I} \in (0, +\infty)^I$，定义标量加权距离 $d_{\mathbf{w}}(x, y) := \sum_{i\in I} w_i d_i(x, y)$。由于 $I$ 有限非空且 $w_i > 0$，$d_{\mathbf{w}}$ 仍是满足 CH1(i)–(iv) 的扩展伪度量。
1. 若 $U \in \mathcal{U}_D(\phi)$ 存在 $\lambda \in \bar{\mathbb{R}}_+$ 使 $\mathbf{w}^T U \le \lambda \mathbf{w}^T$（左次特征不等式，即 $\forall j,\; \sum_i w_i U_{ij} \le \lambda w_j$），则对一切 $x, y \in D$ 有
   $$
   d_{\mathbf{w}}\bigl(\phi(x), \phi(y)\bigr) \le \lambda\, d_{\mathbf{w}}(x, y)
   $$
   （包括 $\lambda = 0$ 且 $d_j = +\infty$ 的情形：因 $w_i > 0$ 迫使 $U = O$，两端均为 $0$）。
2. 对偶地，若 $M \in \mathcal{M}_D(\phi)$ 满足 $\mathbf{w}^T M \ge \mu \mathbf{w}^T$（$\mu \in \bar{\mathbb{R}}_+$），则 $d_{\mathbf{w}}(\phi(x), \phi(y)) \ge \mu\, d_{\mathbf{w}}(x, y)$。

由此，当 $U$ 为有限矩阵且谱半径 $\rho(U) < 1$ 时，由 Perron–Frobenius 扰动必存在正权 $\mathbf{w}$ 及 $\lambda \in (0, 1)$ 使 $\mathbf{w}^T U \le \lambda \mathbf{w}^T$，从而将多分量矩阵估计直接归约为经典标量压缩映射（Perov 型不动点框架）。

---

## 总结一览

| 矩阵类型 | 记号与空间 | 定义条件（$\forall x, y \in D \subseteq \mathrm{dom}(\phi)$） | 极值与存在边界（$\bar{\mathbb{R}}_+$ 下） | 复合法则（$\psi \circ \phi$） |
| :--- | :---: | :--- | :--- | :---: |
| **上 Lipschitz** | $U \in \mathcal{U}_D(\phi)$ | $\mathbf{d}(\phi(x), \phi(y)) \le U\,\mathbf{d}(x, y)$ | 非空 $\iff$ 保 $\sim_{\mathcal{G}}$；上闭、凸；$O$ 最强、$\mathbf{\infty}$ 最弱 | $U_\psi U_\phi$ |
| **直接下 Lipschitz** | $M \in \mathcal{M}_D(\phi)$ | $M\,\mathbf{d}(x, y) \le \mathbf{d}(\phi(x), \phi(y))$ | 恒非空（含 $O$）；下闭、凸、恒拓扑闭 | $M_\psi M_\phi$ |
| **余 Lipschitz** | $K \in \mathcal{K}_D(\phi)$ | $\mathbf{d}(x, y) \le K\,\mathbf{d}(\phi(x), \phi(y))$ | 非空 $\iff$ 反演 $\sim_{\mathcal{G}}$（商单射）；上闭、凸 | $K_\phi K_\psi$ |
| **坍缩（不可区分）** | $C \in \mathcal{C}_D(\phi)$ | $(C\,\mathbf{d}(x, y))_i < 1 \Rightarrow d_i(\phi(x), \phi(y)) = 0$ | 非空 $\iff$ 保 $\sim_{\mathcal{G}}$；上闭、凸；$O$ 最强、$\mathbf{\infty}$ 最弱 | $C_\psi U_\phi$、$U_\psi \diamond C_\phi$、$C_\psi \diamond C_\phi$ |
