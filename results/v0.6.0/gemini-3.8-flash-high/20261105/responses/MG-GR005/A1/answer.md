# 凸成本记录、紧性与闭上图恢复（版本 0.1.1）

---

## S1　原始记录

### 1. 证明 $g_F$ 非负、凸且至少一点有限

- **非负性**：
  对任意 $y \in F^*$：
  - 若纤维 $q_F^{-1}(y) = \emptyset$，按定义空纤维下确界为 $g_F(y) = +\infty \ge 0$；
  - 若 $q_F^{-1}(y) \ne \emptyset$，因设定中 $f: E \to [0, +\infty]$，对任意 $x \in q_F^{-1}(y)$ 均有 $f(x) \ge 0$。非负数集的下确界仍非负，故
    $$
    g_F(y) = \inf_{x \in q_F^{-1}(y)} f(x) \ge 0.
    $$
  因此 $g_F: F^* \to [0, +\infty]$。

- **至少一点有限**：
  已知 $f$ 至少一点有限，即存在 $x_0 \in E$ 使得 $f(x_0) < +\infty$。
  令 $y_0 = q_F(x_0) \in F^*$。由于 $x_0 \in q_F^{-1}(y_0)$，由下确界定义有：
  $$
  g_F(y_0) = \inf_{q_F x = y_0} f(x) \le f(x_0) < +\infty.
  $$
  结合非负性知 $g_F(y_0) \in [0, +\infty)$ 为有限实数，故 $g_F$ 至少在 $y_0$ 处有限。

- **凸性**：
  按题设，函数凸性指其实高度上图 $\operatorname{epi}_{\mathbb{R}}(g_F) = \{(y, t) \in F^* \times \mathbb{R} : g_F(y) \le t\}$ 为凸集。
  设 $(y_1, t_1), (y_2, t_2) \in \operatorname{epi}_{\mathbb{R}}(g_F)$，且任取 $\lambda \in [0, 1]$。
  由 $g_F(y_1) \le t_1$ 与 $g_F(y_2) \le t_2$ 知，对任意 $\varepsilon > 0$，存在 $x_1, x_2 \in E$ 满足：
  $$
  q_F(x_1) = y_1, \quad f(x_1) \le t_1 + \varepsilon; \qquad q_F(x_2) = y_2, \quad f(x_2) \le t_2 + \varepsilon.
  $$
  令 $x_\lambda = \lambda x_1 + (1 - \lambda) x_2$。由 $q_F: E \to F^*$ 的线性性质：
  $$
  q_F(x_\lambda) = \lambda q_F(x_1) + (1 - \lambda) q_F(x_2) = \lambda y_1 + (1 - \lambda) y_2.
  $$
  由 $f$ 的凸性：
  $$
  f(x_\lambda) \le \lambda f(x_1) + (1 - \lambda) f(x_2) \le \lambda t_1 + (1 - \lambda) t_2 + \varepsilon.
  $$
  因此：
  $$
  g_F(\lambda y_1 + (1 - \lambda) y_2) = \inf_{q_F x = \lambda y_1 + (1 - \lambda) y_2} f(x) \le f(x_\lambda) \le \lambda t_1 + (1 - \lambda) t_2 + \varepsilon.
  $$
  令 $\varepsilon \to 0^+$，即得：
  $$
  g_F(\lambda y_1 + (1 - \lambda) y_2) \le \lambda t_1 + (1 - \lambda) t_2.
  $$
  故 $\lambda(y_1, t_1) + (1 - \lambda)(y_2, t_2) \in \operatorname{epi}_{\mathbb{R}}(g_F)$，即 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 是凸集，$g_F$ 是凸函数。

---

### 2. 证明 $g_F(y) = \inf_{r_{KF} z = y} g_K(z)$

当 $F \subset K$ 时，限制算子 $r_{KF}: K^* \to F^*$ 定义为 $r_{KF}(z) = z|_F$。
对任意 $x \in E$，根据 $q_K$ 与 $q_F$ 的定义，对任意 $\varphi \in F \subset K$：
$$
[r_{KF}(q_K(x))](\varphi) = [q_K(x)](\varphi) = \varphi(x) = [q_F(x)](\varphi).
$$
因此 $r_{KF} \circ q_K = q_F$。
于是，对任意给定的 $y \in F^*$，$q_F$ 在 $y$ 处的纤维可划分为：
$$
q_F^{-1}(y) = \{x \in E : q_F(x) = y\} = \{x \in E : r_{KF}(q_K(x)) = y\} = \bigcup_{\substack{z \in K^* \\ r_{KF}(z) = y}} \{x \in E : q_K(x) = z\}.
$$
对两边的集合取 $f(x)$ 的下确界：
$$
\begin{aligned}
g_F(y) &= \inf_{x \in q_F^{-1}(y)} f(x) \\
&= \inf_{\substack{z \in K^* \\ r_{KF}(z) = y}} \left( \inf_{x \in q_K^{-1}(z)} f(x) \right) \\
&= \inf_{\substack{z \in K^* \\ r_{KF}(z) = y}} g_K(z).
\end{aligned}
$$
（若纤维为空，集合下确界按约定为 $+\infty$，上式自然成立）。

---

### 3. 说明证明是否需要纤维下确界取到

**不需要**。
- 在证明 $g_F$ 的凸性时，仅利用了下确界的 $\varepsilon$-逼近性质（取 $\varepsilon > 0$ 构造近似取到下确界的可行点，再令 $\varepsilon \to 0$）；
- 在证明投影关系 $g_F(y) = \inf_{r_{KF} z = y} g_K(z)$ 时，仅利用了集合划分时下确界的结合律 $\inf_{x \in \bigcup_{i \in I} A_i} f(x) = \inf_{i \in I} \inf_{x \in A_i} f(x)$，该恒等式对任意扩展实值族均成立；
- 两处的论证均完全不依赖纤维下确界在任一点是否能够实际取到。

---

## S2　紧次水平集

**本阶段附加条件**：$f$ 下半连续，且对每个有限实数 $c$，次水平集 $\{x \in E : f(x) \le c\}$ 在 $E$ 中紧。

### 1. 映射 $q_F$ 的连续性与适用条件
$E$ 为实 Hausdorff 局部凸空间，$E'$ 为其连续对偶空间。
对有限维子空间 $F \subset E'$，设其一组基为 $\{\varphi_1, \ldots, \varphi_m\} \subset E'$。每个 $\varphi_i: E \to \mathbb{R}$ 均为连续线性泛函。
有限维空间 $F^*$ 赋予唯一下 Hausdorff 拓扑（与标准欧氏空间 $\mathbb{R}^m$ 同胚）。
映射 $q_F: E \to F^*$ 的坐标表示为 $x \mapsto (\varphi_1(x), \ldots, \varphi_m(x))$，每一分量均连续，故 $q_F: E \to F^*$ 是连续线性映射。

---

### 2. 证明当 $g_F(y) < \infty$ 时纤维下确界必取到

设 $y \in F^*$ 满足 $g_F(y) < \infty$。
由 S1 知 $g_F \ge 0$，故令 $c := g_F(y) \in [0, +\infty)$ 为有限实数。
对任意整数 $n \ge 1$，由下确界定义，集合
$$
C_n := q_F^{-1}(y) \cap \left\{ x \in E : f(x) \le c + \frac{1}{n} \right\}
$$
均非空。
我们验证 $C_n$ 的拓扑性质：
1. 由于 $F^*$ 为 Hausdorff 空间，单点集 $\{y\}$ 闭，由 $q_F$ 连续性知 $q_F^{-1}(y)$ 在 $E$ 中闭；
2. 由于 $f$ 下半连续，次水平集 $\{f \le c + 1/n\}$ 在 $E$ 中闭；
3. 因而 $C_n$ 作为两闭集之交，在 $E$ 中闭；
4. 注意到对所有 $n \ge 1$ 均有 $C_n \subset \{x \in E : f(x) \le c + 1\}$。根据附加条件，$\{f \le c + 1\}$ 是 $E$ 中的紧集；
5. 作为紧空间的闭子集，每个 $C_n$ 均是 $E$ 中的非空紧集；
6. 序列 $\{C_n\}_{n=1}^\infty$ 是单调递减的紧集列：$C_1 \supset C_2 \supset \cdots \supset C_n \supset \cdots$。

由紧空间的有限交性质（Cantor 紧集交定理），其总交非空：
$$
C_\infty := \bigcap_{n=1}^\infty C_n \ne \emptyset.
$$
取 $x^* \in C_\infty$：
- $x^* \in q_F^{-1}(y)$，即 $q_F(x^*) = y$；
- 对所有 $n \ge 1$ 均有 $f(x^*) \le c + \frac{1}{n}$，令 $n \to \infty$ 得 $f(x^*) \le c = g_F(y)$；
- 另一方面，由下确界定义，$g_F(y) \le f(x^*)$ 恒成立。

因此 $f(x^*) = g_F(y)$，即纤维下确界在 $x^* \in q_F^{-1}(y)$ 处取到。

---

### 3. 证明各 $g_F$ 下半连续

函数 $g_F: F^* \to [0, +\infty]$ 下半连续等价于对每个实数 $c \in \mathbb{R}$，其次水平集 $\operatorname{Sub}_c(g_F) = \{y \in F^* : g_F(y) \le c\}$ 在 $F^*$ 中闭。
- 若 $c < 0$：因 $g_F \ge 0$，$\operatorname{Sub}_c(g_F) = \emptyset$，显然闭；
- 若 $c \ge 0$：我们断言
  $$
  \operatorname{Sub}_c(g_F) = q_F\left(\{x \in E : f(x) \le c\}\right).
  $$
  - 若 $y \in q_F(\{f \le c\})$，存在 $x \in E$ 满足 $q_F x = y$ 且 $f(x) \le c$，则 $g_F(y) \le f(x) \le c$，故 $y \in \operatorname{Sub}_c(g_F)$；
  - 反之，若 $y \in \operatorname{Sub}_c(g_F)$，则 $g_F(y) \le c < \infty$。由前述纤维下确界可达性，存在 $x^* \in E$ 满足 $q_F x^* = y$ 且 $f(x^*) = g_F(y) \le c$，故 $x^* \in \{f \le c\}$，从而 $y = q_F x^* \in q_F(\{f \le c\})$。

根据 S2 附加条件，$\{x \in E : f(x) \le c\}$ 是 $E$ 中的紧集。
由于 $q_F: E \to F^*$ 连续，紧集在连续映射下的像是紧集，故 $\operatorname{Sub}_c(g_F) = q_F(\{f \le c\})$ 是 $F^*$ 中的紧集。
又因为有限维拓扑向量空间 $F^*$ 是 Hausdorff 空间，Hausdorff 空间中的紧子集必为闭集。
因此，对所有 $c \in \mathbb{R}$，$\operatorname{Sub}_c(g_F)$ 均在 $F^*$ 中闭，从而 $g_F$ 是下半连续函数。

---

## S3　兼容成本记录的实现

**本阶段附加条件**：继承 S2 条件（$f$ 下半连续且实数次水平集紧）。

### 1. 存在性构造

对任意有限维子空间 $F \subset E'$，定义候选集：
$$
A_F := \{x \in E : q_F(x) = y_F \text{ 且 } f(x) \le c\} = q_F^{-1}(y_F) \cap \{x \in E : f(x) \le c\}.
$$
- **非空性**：由条件 $g_F(y_F) \le c < \infty$ 及 S2 已证的纤维下确界取到性，存在 $x \in q_F^{-1}(y_F)$ 使得 $f(x) = g_F(y_F) \le c$。故 $A_F \ne \emptyset$；
- **紧性**：由 $q_F$ 连续性知 $q_F^{-1}(y_F)$ 在 $E$ 中闭。又依条件 $\{f \le c\}$ 是紧集，故 $A_F$ 作为紧集中的闭子集，是 $E$ 中的非空紧集；
- **有限交性质**：
  设 $\mathcal{F}$ 为 $E'$ 的全部有限维子空间按包含关系构成的有向族。
  任取有限个子空间 $F_1, \ldots, F_n \in \mathcal{F}$，定义
  $$
  K := \sum_{i=1}^n F_i = \operatorname{span}(F_1 \cup \cdots \cup F_n).
  $$
  因各 $F_i$ 有限维，故 $K \in \mathcal{F}$，且对所有 $i=1,\ldots,n$ 均有 $F_i \subset K$。
  由相容性假定，$r_{K F_i}(y_K) = y_{F_i}$。
  又由 S1 知 $r_{K F_i} \circ q_K = q_{F_i}$，故对任意 $x \in A_K$：
  $$
  q_K(x) = y_K \implies q_{F_i}(x) = r_{K F_i}(q_K(x)) = r_{K F_i}(y_K) = y_{F_i}.
  $$
  同时 $f(x) \le c$。由此可得 $x \in A_{F_i}$（$i=1,\ldots,n$），即：
  $$
  \emptyset \ne A_K \subset \bigcap_{i=1}^n A_{F_i}.
  $$
  这证明了闭集族 $\{A_F\}_{F \in \mathcal{F}}$ 在紧空间 $\{f \le c\}$ 中具有有限交性质。

由紧空间的有限交性质定理，全交非空：
$$
\bigcap_{F \in \mathcal{F}} A_F \ne \emptyset.
$$
任取 $x \in \bigcap_{F \in \mathcal{F}} A_F$，则：
1. 对所有有限维 $F \subset E'$，均有 $q_F(x) = y_F$；
2. 且 $f(x) \le c$。
存在性得证。

---

### 2. 唯一性证明

设 $x_1, x_2 \in E$ 均满足对所有有限维 $F \subset E'$ 有 $q_F(x_1) = y_F$ 和 $q_F(x_2) = y_F$。
则对所有 $F \in \mathcal{F}$，均有 $q_F(x_1) = q_F(x_2)$。
任取 $\varphi \in E'$，取一维（或零维）子空间 $F = \operatorname{span}\{\varphi\} \in \mathcal{F}$。
根据 $q_F$ 的定义：
$$
\varphi(x_1) = [q_F(x_1)](\varphi) = [q_F(x_2)](\varphi) = \varphi(x_2) \implies \varphi(x_1 - x_2) = 0.
$$
由于该式对所有连续线性泛函 $\varphi \in E'$ 均成立：
**援引定理说明**：$E$ 为实 Hausdorff 局部凸空间，由局部凸空间的 Hahn-Banach 点分离定理（几何形式推论），若 $x_1 - x_2 \ne 0$，必存在 $\varphi \in E'$ 使得 $\varphi(x_1 - x_2) \ne 0$。
因此必有 $x_1 - x_2 = 0$，即 $x_1 = x_2$。
唯一性得证。

---

## S4　一般成本的恢复

**本阶段设定**：只使用共同设定（不假定 $f$ 下半连续，不假定次水平集紧）。

### 1. 明确结论

**能**。
此 $G$ 存在且唯一，即为 $f$ 的最大下半连续凸下界（即闭凸包 $\overline{f} = f^{**}$）。

---

### 2. 构造方法

可从对偶或原空间有向网两个等价视角直接由族 $\{g_F\}_{F \in \mathcal{F}}$ 构造 $G$：

- **对偶构造（利用一维或有限维共轭）**：
  对任意 $\varphi \in E'$，取任意包含 $\varphi$ 的有限维子空间 $F \subset E'$（例如取 $F = \operatorname{span}\{\varphi\}$）。
  利用 $g_F$，在有限维空间 $F^*$ 上计算 Fenchel 共轭：
  $$
  g_F^*(\varphi) = \sup_{y \in F^*} (\langle y, \varphi \rangle - g_F(y)).
  $$
  由 $g_F(y) = \inf_{q_F x = y} f(x)$，直接代入即有：
  $$
  g_F^*(\varphi) = \sup_{y \in F^*} \sup_{x \in q_F^{-1}(y)} (\langle q_F x, \varphi \rangle - f(x)) = \sup_{x \in E} (\varphi(x) - f(x)) = f^*(\varphi).
  $$
  此值完全由 $g_F$ 决定，且与包含 $\varphi$ 的 $F$ 的选取无关。特别地，仅用一维观测 $F = \mathbb{R}\varphi$ 即可确定：
  $$
  f^*(\varphi) = \sup_{y \in (\mathbb{R}\varphi)^*} (\langle y, \varphi \rangle - g_{\mathbb{R}\varphi}(y)).
  $$
  据此定义 $G: E \to [0, +\infty]$ 为：
  $$
  G(x) := \sup_{\varphi \in E'} (\varphi(x) - f^*(\varphi)).
  $$

- **原空间网构造**：
  对每个有限维 $F \subset E'$，令 $\overline{g_F}: F^* \to [0, +\infty]$ 为有限维空间 $F^*$ 上的非负凸函数 $g_F$ 的最大下半连续凸下界（即 $g_F^{**}$）。定义：
  $$
  G_F(x) := \overline{g_F}(q_F(x)).
  $$
  由于在 $F^*$ 上 $\overline{g_F}(y) = \sup_{\varphi \in F}(\langle y, \varphi \rangle - f^*(\varphi))$，故：
  $$
  G_F(x) = \sup_{\varphi \in F} (\varphi(x) - f^*(\varphi)).
  $$
  定义 $G: E \to [0, +\infty]$ 为：
  $$
  G(x) := \sup_{F \in \mathcal{F}} G_F(x) = \sup_{F \in \mathcal{F}} \overline{g_F}(q_F(x)).
  $$

---

### 3. 所需性质核验

1. **下半连续性与凸性**：
   对每个 $F \in \mathcal{F}$，$\overline{g_F}$ 是 $F^*$ 上的下半连续凸函数，而 $q_F: E \to F^*$ 是连续线性映射，故复合函数 $G_F = \overline{g_F} \circ q_F$ 在 $E$ 上下半连续且凸（其任意实次水平集是闭集的连续原像，故闭；上图为凸集的凸线性原像，故凸）。
   $G = \sup_{F \in \mathcal{F}} G_F$ 是一族下半连续凸函数的逐点上确界。
   其上图为闭凸集之交：
   $$
   \operatorname{epi}_{\mathbb{R}}(G) = \bigcap_{F \in \mathcal{F}} \operatorname{epi}_{\mathbb{R}}(G_F),
   $$
   任意个闭凸集的交集必为闭凸集。因此 $G$ 下半连续且凸。

2. **取值范围**：
   因各 $g_F \ge 0$，故 $\overline{g_F} \ge 0$，从而 $G_F \ge 0$，由此 $G(x) \ge 0$；又存在 $x_0 \in E$ 使得 $f(x_0) < +\infty$，由下述 $G \le f$ 知 $G(x_0) \le f(x_0) < +\infty$。故 $G: E \to [0, +\infty]$。

3. **$G \le f$**：
   对任意 $F \in \mathcal{F}$ 与 $x \in E$，$\overline{g_F}(q_F(x)) \le g_F(q_F(x)) \le f(x)$。
   两边对 $F \in \mathcal{F}$ 取上确界即得 $G(x) \le f(x)$。

4. **最大性**：
   设 $h: E \to [-\infty, +\infty]$ 下半连续、凸且满足 $h \le f$。
   若 $h \equiv -\infty$，显然 $h \le G$；
   若 $h$ 不恒为 $-\infty$，由 $h \le f$ 且 $f \ge 0$ 知 $h$ 为真下半连续凸函数。
   **援引定理说明**：$E$ 为实 Hausdorff 局部凸空间，由 Fenchel-Moreau 对偶定理，任意真下半连续凸函数均等于其双共轭，即：
   $$
   h(x) = \sup_{\varphi \in E'} (\varphi(x) - h^*(\varphi)).
   $$
   由 $h \le f$，共轭泛函满足 $h^*(\varphi) = \sup_x (\varphi(x) - h(x)) \ge \sup_x (\varphi(x) - f(x)) = f^*(\varphi)$。
   因此：
   $$
   \varphi(x) - h^*(\varphi) \le \varphi(x) - f^*(\varphi), \quad \forall \varphi \in E'.
   $$
   两端对 $\varphi \in E'$ 取上确界，即得：
   $$
   h(x) \le \sup_{\varphi \in E'} (\varphi(x) - f^*(\varphi)) = G(x).
   $$
   故 $G$ 是 $f$ 的最大下半连续凸下界。

---

### 4. 扩大观测空间时的关系

设 $F \subset K$ 为两个有限维观测子空间（即观测空间扩大）：
- 在对偶表象中，由于 $F \subset K$：
  $$
  G_F(x) = \sup_{\varphi \in F} (\varphi(x) - f^*(\varphi)) \le \sup_{\varphi \in K} (\varphi(x) - f^*(\varphi)) = G_K(x).
  $$
  因此随着观测子空间扩大，近似函数族满足单调性：
  $$
  F \subset K \implies G_F \le G_K \le f.
  $$
- 由于有限维子空间族 $\mathcal{F}$ 依包含关系构成向上有向集（对任意 $F_1, F_2 \in \mathcal{F}$，均有 $F_1 + F_2 \in \mathcal{F}$），因此 $\{G_F\}_{F \in \mathcal{F}}$ 构成 $E$ 上的单调递增网，且其按网收敛的逐点极限精确给出 $G$：
  $$
  G(x) = \lim_{F \in \mathcal{F}} G_F(x) = \sup_{F \in \mathcal{F}} G_F(x).
  $$
- 对应到各投影空间的成本记录上，当 $F \subset K$ 时，由限制算子 $r_{KF}: K^* \to F^*$，对任意 $y \in F^*$ 恒有 $\overline{g_F}(y) \le \inf_{r_{KF} z = y} \overline{g_K}(z)$，这体现了增大观测空间后信息精细化所带来的下界逐级抬升。

---

## S5　闭成本的有限投影

**本阶段设定**：$E = \mathbb{R}^2$，$f: E \to [0, +\infty]$ 下半连续、凸且至少一点有限。

### 1. 明确结论

**不一定**（各有限维 $F$ 的 $g_F$ 不必下半连续）。

---

### 2. 完整核验反例

在 $E = \mathbb{R}^2$ 上，坐标记为 $(x_1, x_2)$。考虑双曲线支上方的闭凸集：
$$
C := \{(x_1, x_2) \in \mathbb{R}^2 : x_1 > 0, x_1 x_2 \ge 1\} = \{(x_1, x_2) \in \mathbb{R}^2 : x_1 \ge 0, x_2 \ge 0, x_1 x_2 \ge 1\}.
$$
定义成本函数 $f: \mathbb{R}^2 \to [0, +\infty]$ 为集合 $C$ 的示性函数（indicator function）：
$$
f(x_1, x_2) := \begin{cases} 0, & (x_1, x_2) \in C, \\ +\infty, & (x_1, x_2) \notin C. \end{cases}
$$

#### 检验 $f$ 满足全部前提条件：
1. **取值范围**：$f(x) \in \{0, +\infty\} \subset [0, +\infty]$，非负；
2. **至少一点有限**：$(1, 1) \in C$，故 $f(1, 1) = 0 < +\infty$；
3. **凸性**：$C$ 是凸函数 $t \mapsto 1/t$（$t > 0$）的严格上图，为 $\mathbb{R}^2$ 的凸集。凸集的示性函数必为凸函数；
4. **下半连续性**：映射 $(x_1, x_2) \mapsto x_1$、$(x_1, x_2) \mapsto x_2$ 以及 $(x_1, x_2) \mapsto x_1 x_2$ 均在 $\mathbb{R}^2$ 上连续，故
   $$
   C = \{x_1 \ge 0\} \cap \{x_2 \ge 0\} \cap \{x_1 x_2 \ge 1\}
   $$
   是闭集。闭集的示性函数的实上图 $\operatorname{epi}_{\mathbb{R}}(f) = C \times [0, +\infty)$ 在 $\mathbb{R}^2 \times \mathbb{R}$ 中闭，故 $f$ 是下半连续函数（即闭成本）。

#### 构造有限维子空间 $F$ 并计算 $g_F$：
取连续线性泛函 $\varphi \in (\mathbb{R}^2)^*$ 为到第一个坐标的投影：$\varphi(x_1, x_2) = x_1$。
令 $F = \operatorname{span}\{\varphi\}$，为 1 维子空间。
通过对偶基将 $F^*$ 等同于 $\mathbb{R}$，则对任意 $(x_1, x_2) \in \mathbb{R}^2$ 有 $q_F(x_1, x_2) = x_1$。
对任意 $y \in \mathbb{R}$，计算纤维下确界 $g_F(y) = \inf_{x_2 \in \mathbb{R}} f(y, x_2)$：
- 若 $y > 0$：取 $x_2 = 1/y$，则 $(y, x_2) \in C$，此时 $f(y, 1/y) = 0$。由 $f \ge 0$ 可得：
  $$
  g_F(y) = 0;
  $$
- 若 $y \le 0$：对任意 $x_2 \in \mathbb{R}$，均有 $(y, x_2) \notin C$（因为 $C$ 中元素的第一个坐标恒满足 $x_1 > 0$），此时纤维上的取值恒为 $+\infty$（空纤维），故：
  $$
  g_F(y) = +\infty.
  $$

综合可得：
$$
g_F(y) = \begin{cases} 0, & y > 0, \\ +\infty, & y \le 0. \end{cases}
$$

#### 检验 $g_F$ 的下半连续性：
考察点 $y = 0$：
$$
\liminf_{y \to 0} g_F(y) \le \lim_{y \to 0^+} g_F(y) = 0.
$$
但由上式定义：
$$
g_F(0) = +\infty.
$$
由于 $\liminf_{y \to 0} g_F(y) = 0 < g_F(0) = +\infty$（或考察其水平集 $\{y \in \mathbb{R} : g_F(y) \le 0\} = (0, +\infty)$ 在 $\mathbb{R}$ 中不闭），$g_F$ 在 $y = 0$ 处不满足下半连续性。
因此，$g_F$ 不是下半连续函数。

*(注：在 $E = \mathbb{R}^2$ 上，若凸函数处处有限实值，则其在一维上的投影亦处处有限，而 $\mathbb{R}$ 上有限凸函数必连续。因此，投影非闭现象的产生本质上依赖于凸有效域在无穷远处具有渐近方向，致使投影域边界无法闭合。)*

---

## S6　恢复与投影的精确关系

**共同设定下**：$\overline{u}$ 表示非负凸函数 $u$ 的最大下半连续凸下界。

### 1. 证明 $G = f \iff f$ 下半连续

- **充分性 ($\impliedby$)**：
  若 $f$ 下半连续，结合共同设定中 $f: E \to [0, +\infty]$ 凸且非负，可知 $f$ 本身就是一个下半连续、凸且满足 $f \le f$ 的扩展实值函数。
  由 S4 中 $G$ 作为“满足 $h \le f$ 的所有下半连续凸函数 $h$ 的上确界（最大元）”的性质，必有：
  $$
  f \le G.
  $$
  另一方面，S4 的构造直接保证 $G \le f$。
  两式结合即得 $G = f$。

- **必要性 ($\implies$)**：
  若 $G = f$，由于 S4 中证明了 $G$ 必是下半连续函数，因此 $f$ 作为与 $G$ 相同的函数，自身必定下半连续。

---

### 2. 证明 $\overline{g_F} = \overline{y \mapsto \inf_{r_{KF} z = y} \overline{g_K}(z)}$

设 $F \subset K$ 为 $E'$ 的有限维子空间。记映射
$$
H(y) := \inf_{\substack{z \in K^* \\ r_{KF} z = y}} \overline{g_K}(z).
$$
我们需要证明 $\overline{g_F} = \overline{H}$。

#### 证明论证（原空间双向夹逼与对偶结合）：
1. **上界夹逼**：
   因为 $\overline{g_K}$ 是 $g_K$ 的最大下半连续凸下界，故 $\overline{g_K} \le g_K$。
   对任意 $y \in F^*$，取纤维下确界即得：
   $$
   H(y) = \inf_{r_{KF} z = y} \overline{g_K}(z) \le \inf_{r_{KF} z = y} g_K(z) = g_F(y) \quad (\text{由 S1}).
   $$
2. **下界夹逼**：
   在有限维空间 $K^*$ 上，根据 Fenchel-Moreau 定理，$\overline{g_K} = g_K^{**}$。
   由 S4 知，对任意 $\psi \in K$，$g_K^*(\psi) = f^*(\psi)$。因此：
   $$
   \overline{g_K}(z) = \sup_{\psi \in K} (\langle z, \psi \rangle - f^*(\psi)).
   $$
   由于 $F \subset K$，取上确界的集合缩小，故对任意 $z \in K^*$：
   $$
   \overline{g_K}(z) \ge \sup_{\varphi \in F} (\langle z, \varphi \rangle - f^*(\varphi)).
   $$
   若 $z \in K^*$ 满足 $r_{KF} z = y$，则对任意 $\varphi \in F$，由限制映射定义：
   $$
   \langle z, \varphi \rangle = \langle r_{KF} z, \varphi \rangle = \langle y, \varphi \rangle.
   $$
   代入上式，可知对所有满足 $r_{KF} z = y$ 的 $z \in K^*$，均成立：
   $$
   \overline{g_K}(z) \ge \sup_{\varphi \in F} (\langle y, \varphi \rangle - f^*(\varphi)) = g_F^{**}(y) = \overline{g_F}(y).
   $$
   由于 $F \subset K$ 为有限维子空间，限制映射 $r_{KF}: K^* \to F^*$（对应内射 $F \hookrightarrow K$ 的伴随）必是满射，纤维 $r_{KF}^{-1}(y)$ 恒非空。
   对所有 $z \in r_{KF}^{-1}(y)$ 取下确界，即得：
   $$
   H(y) = \inf_{r_{KF} z = y} \overline{g_K}(z) \ge \overline{g_F}(y).
   $$
3. **闭包相等**：
   综合上述步骤 1 与步骤 2，对所有 $y \in F^*$ 成立夹逼不等式：
   $$
   \overline{g_F}(y) \le H(y) \le g_F(y).
   $$
   由于 $\overline{g_F}$ 自身是有限维空间 $F^*$ 上的下半连续凸函数，操作 $u \mapsto \overline{u}$ 是单调且幂等的：
   $$
   \overline{g_F} = \overline{\overline{g_F}} \le \overline{H} \le \overline{g_F}.
   $$
   因此两端夹逼必有：
   $$
   \overline{g_F} = \overline{H} = \overline{y \mapsto \inf_{r_{KF} z = y} \overline{g_K}(z)}.
   $$

---

### 3. 判断右式的最外层 $\overline{\,\cdot\,}$ 能否总省去

**明确结论**：**不能总省去**。

#### 反例与核验论证：
若右式的最外层 $\overline{\,\cdot\,}$ 总能省去，则意味着对任意有限维 $F \subset K$，函数 $H(y) = \inf_{r_{KF} z = y} \overline{g_K}(z)$ 必须总是下半连续的，从而恒有 $\overline{g_F}(y) = \inf_{r_{KF} z = y} \overline{g_K}(z)$。

我们利用 S5 中的构造给出明确反例：
1. 设 $E = \mathbb{R}^2$。对偶空间 $E' = (\mathbb{R}^2)^* \cong \mathbb{R}^2$ 本身即为有限维空间。
2. 取大观测空间为全部对偶空间：$K := E'$（有限维，$\dim K = 2$）。
   则 $q_K: E \to K^*$ 为典范同构。
3. 设 $f: \mathbb{R}^2 \to [0, +\infty]$ 为 S5 中的闭凸示性函数：
   $$
   f(x_1, x_2) = \begin{cases} 0, & x_1 > 0, x_1 x_2 \ge 1, \\ +\infty, & \text{其它}. \end{cases}
   $$
   已知 $f$ 本身是下半连续凸函数。
   由于 $q_K$ 是拓扑同构，$g_K$ 在同构对应下即为 $f$。因为 $f$ 已是下半连续凸函数，故其闭下界即为其自身：
   $$
   \overline{g_K} = g_K.
   $$
4. 取小观测空间 $F = \operatorname{span}\{\varphi\} \subset K$，其中 $\varphi(x_1, x_2) = x_1$（$\dim F = 1$）。
   此时限制投影 $r_{KF}: K^* \to F^*$ 正是对第一分量的投影。
   右式括号内部的函数即为：
   $$
   H(y) = \inf_{r_{KF} z = y} \overline{g_K}(z) = \inf_{r_{KF} z = y} g_K(z) = g_F(y).
   $$
   按 S5 中已完成的精确计算：
   $$
   H(y) = g_F(y) = \begin{cases} 0, & y > 0, \\ +\infty, & y \le 0. \end{cases}
   $$
5. 现在计算其最大下半连续凸下界 $\overline{g_F}$（即 $\overline{H}$）：
   在 $\mathbb{R}$ 上，非负凸函数 $g_F$ 的共轭函数为：
   $$
   g_F^*(\lambda) = \sup_{y > 0} (\lambda y - 0) = \begin{cases} 0, & \lambda \le 0, \\ +\infty, & \lambda > 0. \end{cases}
   $$
   再取一次共轭可得双共轭（即最大下半连续凸下界）：
   $$
   \overline{g_F}(y) = g_F^{**}(y) = \sup_{\lambda \le 0} (\lambda y) = \begin{cases} 0, & y \ge 0, \\ +\infty, & y < 0. \end{cases}
   $$
6. 特别考察点 $y = 0$：
   - 左端为：$\overline{g_F}(0) = 0$；
   - 若省去右端最外层 $\overline{\,\cdot\,}$，右端取值为：
     $$
     H(0) = \inf_{r_{KF} z = 0} \overline{g_K}(z) = g_F(0) = +\infty.
     $$
   两端在原点处不相等：
   $$
   \overline{g_F}(0) = 0 \ne +\infty = \inf_{r_{KF} z = 0} \overline{g_K}(z).
   $$
   该不等表明 $H$ 在 $y = 0$ 处发生跳跃破坏了下半连续性，若省去最外层闭包操作，等式不再成立。

因此，最外层的 $\overline{\,\cdot\,}$ **不能总省去**。
