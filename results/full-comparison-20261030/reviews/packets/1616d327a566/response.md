本题探讨了无穷维线性观测中关于商结构、空间完备化与最佳逼近（广义逆/最优恢复）的核心泛函分析框架。以下在 ZFC 公理体系下给出严格的构造与证明。

---

### 一、商空间 $Q$ 上的范数与内积结构

1. **范数良定性**：
   对于任意 $x_1, x_2 \in E$，若 $q(x_1) = q(x_2)$，则 $x_1 - x_2 \in \ker A$，从而 $Ax_1 = Ax_2$，故 $\|Ax_1\|_H = \|Ax_2\|_H$。因此映射
   $$
   \|q(x)\|_A := \|Ax\|_H
   $$
   良定。
2. **满足范数公理**：
   - **正定性**：$\|q(x)\|_A = 0 \iff \|Ax\|_H = 0 \iff Ax = 0 \iff x \in \ker A \iff q(x) = 0$。
   - **绝对齐次性**：对任意 $\alpha \in \mathbb{R}$，$q(\alpha x) = \alpha q(x)$，且 $\|\alpha q(x)\|_A = \|A(\alpha x)\|_H = |\alpha|\|Ax\|_H = |\alpha|\|q(x)\|_A$。
   - **三角不等式**：$\|q(x_1) + q(x_2)\|_A = \|A(x_1 + x_2)\|_H \le \|Ax_1\|_H + \|Ax_2\|_H = \|q(x_1)\|_A + \|q(x_2)\|_A$。
   
   因此，$(Q, \|\cdot\|_A)$ 是实赋范线性空间。
   
> **注**：该范数是由内积 $\langle q(x_1), q(x_2)\rangle_A := \langle Ax_1, Ax_2\rangle_H$ 诱导的（平行四边形恒等式直接由 $H$ 的内积性质继承），故 $(Q, \|\cdot\|_A)$ 是实内积空间（准 Hilbert 空间）。

---

### 二、完备化 $\widehat Q$ 的构造、等距算子 $J$ 及其性质

#### 1. 完备化 $(\widehat Q, \iota)$ 的构造
按赋范空间的标准构造：
- 设 $\mathcal{C}(Q)$ 为 $Q$ 中全体 Cauchy 列构成的实向量空间，$\mathcal{N}(Q)$ 为趋于 $0$ 的 Cauchy 列构成的子空间。
- 取商空间 $\widehat Q = \mathcal{C}(Q) / \mathcal{N}(Q)$，对 Cauchy 列 $(u_n)_{n=1}^\infty$ 的等价类 $[(u_n)]$ 定义范数 $\|[(u_n)]\|_{\widehat Q} = \lim_{n\to\infty} \|u_n\|_A$。
- 定义规范嵌入 $\iota: Q \to \widehat Q$ 为 $\iota(u) = [(u, u, \dots)]$。
则 $(\widehat Q, \|\cdot\|_{\widehat Q})$ 是完备赋范空间（实 Hilbert 空间），$\iota$ 为线性等距映射，且 $\iota(Q)$ 在 $\widehat Q$ 中稠密。

#### 2. 线性等距映射 $J$ 的构造与像的确定
首先，在代数商空间 $Q$ 上定义映射 $j_0: Q \to H$：
$$
j_0(q(x)) = Ax.
$$
- **良定性与等距性**：若 $q(x_1) = q(x_2)$，则 $Ax_1 = Ax_2$；且 $\|j_0(q(x))\|_H = \|Ax\|_H = \|q(x)\|_A$。故 $j_0$ 是线性等距映射，其像为 $j_0(Q) = A(E) = \mathrm{Im}(A)$。

对于任意 $u \in \widehat Q$，由于 $\iota(Q)$ 在 $\widehat Q$ 中稠密，存在序列 $(u_n)_{n=1}^\infty \subset Q$ 使得 $\iota(u_n) \to u$。
- 由于 $\iota$ 是等距映射，$(u_n)$ 是 $Q$ 中的 Cauchy 列。
- 又因 $j_0$ 是等距映射，$(j_0(u_n))_{n=1}^\infty$ 是 $H$ 中的 Cauchy 列。
- 由 $H$ 的完备性，极限 $\lim_{n\to\infty} j_0(u_n)$ 在 $H$ 中存在。

定义映射 $J: \widehat Q \to H$ 为：
$$
J(u) = \lim_{n\to\infty} j_0(u_n), \quad \text{其中 } \lim_{n\to\infty} \iota(u_n) = u.
$$
- **良定性与线性**：若另有 $\iota(u'_n) \to u$，则 $\|u_n - u'_n\|_A = \|\iota(u_n) - \iota(u'_n)\|_{\widehat Q} \to 0$，进而 $\|j_0(u_n) - j_0(u'_n)\|_H \to 0$。由极限性质，极限与近似序列的选择无关，且 $J$ 保持加法与数乘，因而是良定的线性算子。
- **等距性**：对任意 $u \in \widehat Q$：
  $$
  \|J(u)\|_H = \lim_{n\to\infty} \|j_0(u_n)\|_H = \lim_{n\to\infty} \|u_n\|_A = \lim_{n\to\infty} \|\iota(u_n)\|_{\widehat Q} = \|u\|_{\widehat Q}.
  $$
- **满足分解条件**：对任意 $x \in E$，取常值序列 $u_n = q(x)$，则
  $$
  J(\iota(q(x))) = j_0(q(x)) = Ax \implies J\iota q = A.
  $$
- **确定 $J$ 的像**：
  $$
  \mathrm{Im}(J) = \overline{A(E)} = \overline{\mathrm{Im}(A)}.
  $$
  *证明*：
  1. 一方面，$A(E) = j_0(Q) = J(\iota(Q)) \subseteq J(\widehat Q)$。因为 $J$ 是等距算子且 $\widehat Q$ 完备，$J(\widehat Q)$ 是 $H$ 的完备度量子空间，从而为 $H$ 的闭子空间。于是 $\overline{A(E)} \subseteq J(\widehat Q)$。
  2. 另一方面，任取 $u \in \widehat Q$，设 $\iota(u_n) \to u$（其中 $u_n = q(x_n)$），则 $J(u) = \lim_{n\to\infty} Ax_n \in \overline{A(E)}$。因此 $J(\widehat Q) \subseteq \overline{A(E)}$。
  综上，$\mathrm{Im}(J) = \overline{A(E)}$。

#### 3. 满足 $J\iota q = A$ 的线性等距映射 $J$ 的唯一性证明
设固定的完备化为 $(\widehat Q, \iota)$。假设另有线性等距映射 $\widetilde J: \widehat Q \to H$ 满足 $\widetilde J \iota q = A$。
- 对任意 $v \in Q$，由商映射 $q: E \to Q$ 的满射性，存在 $x \in E$ 使得 $q(x) = v$。
- 于是：
  $$
  \widetilde J(\iota(v)) = \widetilde J(\iota(q(x))) = Ax = J(\iota(q(x))) = J(\iota(v)).
  $$
  即 $\widetilde J$ 与 $J$ 在线性子空间 $\iota(Q) \subseteq \widehat Q$ 上完全一致。
- 由于 $\iota(Q)$ 在 $\widehat Q$ 中稠密，且等距映射必为连续映射（Lipschitz 连续），而度量空间 $H$ 是 Hausdorff 空间，由稠密集上连续映射的延拓唯一性定理，必有：
  $$
  \widetilde J = J \quad (\text{在整个 } \widehat Q \text{ 上}).
  $$

---

### 三、极小化问题与最优恢复算子 $R$

记闭子空间 $M := \mathrm{Im}(J) = \overline{A(E)} \subseteq H$。

#### 1. 极小点 $R(y)$ 的构造与唯一性
考虑极小化问题：
$$
\inf_{u\in\widehat Q}\|y-Ju\|_H.
$$
- 因为 $J: \widehat Q \to M$ 为双射线性等距算子，当 $u$ 遍历 $\widehat Q$ 时，$Ju$ 刚好遍历闭子空间 $M$。
- 于是该问题等价于求 $y$ 在闭子空间 $M$ 上的最佳逼近点：
  $$
  \inf_{u\in\widehat Q}\|y-Ju\|_H = \inf_{v\in M}\|y-v\|_H.
  $$
- 由 **Hilbert 空间正交投影定理**，存在唯一的 $v^* \in M$ 达到下确界，该点为 $v^* = P_M y$，其中 $P_M: H \to M$ 为 $H$ 到闭子空间 $M$ 上的正交投影算子。
- 由于 $J: \widehat Q \to M$ 为等距同构（双射），存在唯一的逆映射 $J^{-1}: M \to \widehat Q$（亦为线性等距算子）。方程 $Ju = P_M y$ 在 $\widehat Q$ 中存在唯一解：
  $$
  R(y) := J^{-1}(P_M y).
  $$
  故 $R(y)$ 为唯一的极小点。

#### 2. $R$ 的线性与 $1$-Lipschitz 连续性
- **线性**：
  正交投影算子 $P_M: H \to M$ 为线性算子，逆映射 $J^{-1}: M \to \widehat Q$ 为线性算子。作为二者的复合，$R = J^{-1} \circ P_M: H \to \widehat Q$ 必为线性算子。
- **$1$-Lipschitz**：
  对任意 $y_1, y_2 \in H$，利用 $R$ 的线性以及 $J^{-1}$ 的等距性：
  $$
  \|R(y_1) - R(y_2)\|_{\widehat Q} = \|R(y_1 - y_2)\|_{\widehat Q} = \|J^{-1}(P_M(y_1 - y_2))\|_{\widehat Q} = \|P_M(y_1 - y_2)\|_H.
  $$
  由正交投影的勾股定理：
  $$
  \|y_1 - y_2\|_H^2 = \|P_M(y_1 - y_2)\|_H^2 + \|(I - P_M)(y_1 - y_2)\|_H^2 \ge \|P_M(y_1 - y_2)\|_H^2,
  $$
  可得 $\|P_M(y_1 - y_2)\|_H \le \|y_1 - y_2\|_H$。因此：
  $$
  \|R(y_1) - R(y_2)\|_{\widehat Q} \le \|y_1 - y_2\|_H.
  $$
  即 $R$ 是 $1$-Lipschitz 的（当 $M \neq \{0\}$ 时，其算子范数 $\|R\| = 1$；当 $M = \{0\}$ 时为 $0$）。

#### 3. 两个极小值之间的关系
$$
\inf_{u\in\widehat Q}\|y-Ju\|_H = \inf_{x\in E}\|y-Ax\|_H = \|y - P_M y\|_H.
$$
*证明*：
因为 $A(E) = J(\iota(Q)) \subseteq M$，显然有
$$
\inf_{u\in\widehat Q}\|y-Ju\|_H = \inf_{v\in M}\|y-v\|_H \le \inf_{w\in A(E)}\|y-w\|_H = \inf_{x\in E}\|y-Ax\|_H.
$$
另一方面，因为 $A(E)$ 在 $M = \overline{A(E)}$ 中稠密，对任意 $\varepsilon > 0$，存在 $w \in A(E)$ 使得 $\|P_M y - w\|_H < \varepsilon$。由三角不等式：
$$
\|y - w\|_H \le \|y - P_M y\|_H + \|P_M y - w\|_H < \|y - P_M y\|_H + \varepsilon.
$$
令 $\varepsilon \to 0^+$ 即得 $\inf_{w\in A(E)}\|y-w\|_H \le \|y - P_M y\|_H$。
因此二者**严格相等**，均等于距离 $d(y, M) = \|y - P_M y\|_H$。

---

### 四、原空间中极小点集 $M_y$ 的非空充要条件与完整描述

集合定义为：
$$
M_y = \left\{x\in E: \|y-Ax\|_H = \inf_{z\in E}\|y-Az\|_H\right\}.
$$

#### 1. 元素归属判定
根据前文，$\inf_{z\in E}\|y-Az\|_H = \|y - P_M y\|_H$。
因为 $Ax \in M$，根据 Hilbert 空间中正交投影的最优逼近唯一性：
$$
\|y - Ax\|_H = \|y - P_M y\|_H \iff Ax = P_M y.
$$
再结合 $P_M y = J(R(y))$ 与 $Ax = J(\iota(q(x)))$，由于 $J$ 是单射（等距映射），上述条件等价于：
$$
Ax = P_M y \iff J(\iota(q(x))) = J(R(y)) \iff \iota(q(x)) = R(y).
$$

#### 2. $M_y$ 非空的充要条件
以下条件等价：
1. **像空间表述**：
   $$
   P_M y \in A(E) = \mathrm{Im}(A).
   $$
   （即：$y$ 在 $\overline{A(E)}$ 上的正交投影属于 $A$ 的代数像 $A(E)$。）
2. **完备化载体表述**：
   $$
   R(y) \in \iota(Q) = \mathrm{Im}(\iota).
   $$
   （即：极小化算子在 $\widehat Q$ 中产生的最优恢复解恰好落在原商空间的嵌入像中。）
3. **正规方程（变分正交性）表述**：
   $$
   \exists x \in E, \quad \forall z \in E, \quad \langle y - Ax, Az \rangle_H = 0.
   $$

#### 3. $M_y$ 非空时的完整描述
若 $M_y \neq \emptyset$：
- **商空间中的单一性**：
  由于 $\iota: Q \to \widehat Q$ 是单射，当 $R(y) \in \iota(Q)$ 时，原商空间 $Q$ 中存在唯一元素 $u_y := \iota^{-1}(R(y))$。
  任何 $x \in E$ 满足 $x \in M_y$ 当且仅当 $q(x) = u_y$。
  即在商空间 $Q$ 中，极小点集的商映射像为单点集：
  $$
  q(M_y) = \{\iota^{-1}(R(y))\}.
  $$
- **原空间 $E$ 中的仿射流形结构**：
  任取一个特解 $x_0 \in M_y$（即满足 $Ax_0 = P_M y$ 的任意元素），则对任意 $x \in E$：
  $$
  x \in M_y \iff Ax = Ax_0 \iff A(x - x_0) = 0 \iff x - x_0 \in \ker A.
  $$
  因此，$M_y$ 是 $E$ 中以 $\ker A$ 为方向的仿射子空间（陪集）：
  $$
  M_y = x_0 + \ker A = q^{-1}\left(\iota^{-1}(R(y))\right).
  $$
- **观测像中的不变性**：
  对所有 $x \in M_y$，观测值均恒定且唯一对应于正交投影：
  $$
  Ax \equiv P_M y.
  $$
