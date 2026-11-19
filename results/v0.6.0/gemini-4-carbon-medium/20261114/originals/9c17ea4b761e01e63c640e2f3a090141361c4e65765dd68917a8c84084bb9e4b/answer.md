{}
以下逐阶段（S1–S6）给出完整作答。全文记 $\mathcal{F}$ 为 $E'$ 的全体有限维实线性子空间之族（含零维子空间 $\{0\}$，其代数对偶 $\{0\}^* = \{0\}$ 赋单点 Hausdorff 拓扑）。对任意 $F \in \mathcal{F}$，因每个 $\varphi \in F \subset E'$ 线性，映射 $q_F: E \to F^*$（$q_F(x)(\varphi) = \varphi(x)$）为实线性映射；当 $F \subset K$（$F, K \in \mathcal{F}$）时，限制映射 $r_{KF}: K^* \to F^*$ 为线性映射，且对一切 $x \in E$ 及 $\varphi \in F \subset K$ 有
$$(r_{KF}(q_K x))(\varphi) = (q_K x)(\varphi) = \varphi(x) = (q_F x)(\varphi), \quad \text{即 } r_{KF} \circ q_K = q_F.$$

---

## S1　原始记录

### 1. 证明 $g_F$ 非负、凸且至少一点有限

1. **非负性（取值于 $[0, +\infty]$）**：
   任取 $y \in F^*$，记纤维 $A_y := \{x \in E : q_F x = y\}$。
   - 若 $A_y = \emptyset$，按约定 $g_F(y) = \inf \emptyset = +\infty \ge 0$。
   - 若 $A_y \neq \emptyset$，因对一切 $x \in E$ 有 $f(x) \ge 0$，$0$ 是集合 $\{f(x) : x \in A_y\}$ 的下界，故由下确界定义得 $g_F(y) = \inf_{x \in A_y} f(x) \ge 0$。
   因此 $g_F: F^* \to [0, +\infty]$ 非负。

2. **至少一点有限**：
   由共同设定，存在 $x_0 \in E$ 使 $0 \le f(x_0) < +\infty$。令 $y_0 := q_F x_0 \in F^*$，则 $x_0 \in \{x \in E : q_F x = y_0\}$，于是
   $$0 \le g_F(y_0) \le f(x_0) < +\infty,$$
   故 $g_F$ 在 $y_0$ 处有限。

3. **凸性（即 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^* \times \mathbb{R}$ 中为凸集）**：
   任取 $(y_1, t_1), (y_2, t_2) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 及 $\lambda \in [0, 1]$，需证 $(\lambda y_1 + (1-\lambda)y_2,\, \lambda t_1 + (1-\lambda)t_2) \in \operatorname{epi}_{\mathbb{R}}(g_F)$。
   - 若 $\lambda = 0$ 或 $\lambda = 1$，该点即 $(y_2, t_2)$ 或 $(y_1, t_1)$，显然属于 $\operatorname{epi}_{\mathbb{R}}(g_F)$。
   - 设 $\lambda \in (0, 1)$。任取 $\varepsilon > 0$。由 $(y_i, t_i) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 知 $t_i \in \mathbb{R}$ 且 $g_F(y_i) \le t_i < t_i + \varepsilon$（$i = 1, 2$）。由下确界定义（此时 $g_F(y_i) < +\infty$，纤维非空），存在 $x_1, x_2 \in E$ 使得
     $$q_F x_i = y_i, \qquad f(x_i) \le t_i + \varepsilon \qquad (i = 1, 2).$$
     这表明 $(x_i, t_i + \varepsilon) \in \operatorname{epi}_{\mathbb{R}}(f)$（$i = 1, 2$）。因 $f$ 为凸函数，按定义 $\operatorname{epi}_{\mathbb{R}}(f)$ 在 $E \times \mathbb{R}$ 中为凸集，故
     $$\bigl(\lambda x_1 + (1-\lambda)x_2,\, \lambda(t_1 + \varepsilon) + (1-\lambda)(t_2 + \varepsilon)\bigr) = \bigl(\lambda x_1 + (1-\lambda)x_2,\, \lambda t_1 + (1-\lambda)t_2 + \varepsilon\bigr) \in \operatorname{epi}_{\mathbb{R}}(f),$$
     即 $f(\lambda x_1 + (1-\lambda)x_2) \le \lambda t_1 + (1-\lambda)t_2 + \varepsilon$。又由 $q_F$ 的线性性，
     $$q_F(\lambda x_1 + (1-\lambda)x_2) = \lambda q_F x_1 + (1-\lambda)q_F x_2 = \lambda y_1 + (1-\lambda)y_2,$$
     从而
     $$g_F(\lambda y_1 + (1-\lambda)y_2) \le f(\lambda x_1 + (1-\lambda)x_2) \le \lambda t_1 + (1-\lambda)t_2 + \varepsilon.$$
     由 $\varepsilon > 0$ 的任意性，令 $\varepsilon \downarrow 0$ 得 $g_F(\lambda y_1 + (1-\lambda)y_2) \le \lambda t_1 + (1-\lambda)t_2$，故 $(\lambda y_1 + (1-\lambda)y_2,\, \lambda t_1 + (1-\lambda)t_2) \in \operatorname{epi}_{\mathbb{R}}(g_F)$。因此 $g_F$ 为凸函数。

### 2. 证明 $g_F(y) = \inf_{r_{KF} z = y} g_K(z)$

设 $F \subset K$（$F, K \in \mathcal{F}$），固定 $y \in F^*$，记右式为 $R(y) := \inf\{g_K(z) : z \in K^*,\, r_{KF} z = y\}$。利用恒等式 $r_{KF} \circ q_K = q_F$ 分双向不等号证明：

- **$R(y) \le g_F(y)$**：
  对任意满足 $q_F x = y$ 的 $x \in E$，令 $z := q_K x \in K^*$，则 $r_{KF} z = r_{KF}(q_K x) = q_F x = y$，且由 $g_K(z)$ 的定义有 $g_K(z) \le f(x)$，从而 $R(y) \le g_K(z) \le f(x)$。故 $R(y)$ 是集合 $\{f(x) : q_F x = y\}$ 的下界（若该纤维为空，则 $g_F(y) = +\infty \ge R(y)$ 自动成立）。对满足 $q_F x = y$ 的 $x$ 取下确界得 $R(y) \le g_F(y)$。

- **$g_F(y) \le R(y)$**：
  任取满足 $r_{KF} z = y$ 的 $z \in K^*$。对任意满足 $q_K x = z$ 的 $x \in E$，有 $q_F x = r_{KF}(q_K x) = r_{KF} z = y$，故 $g_F(y) \le f(x)$。这说明 $g_F(y)$ 是集合 $\{f(x) : q_K x = z\}$ 的下界（若该纤维为空，则 $g_K(z) = +\infty \ge g_F(y)$ 仍成立），取下确界得 $g_F(y) \le g_K(z)$。再对所有满足 $r_{KF} z = y$ 的 $z \in K^*$ 取下确界，得 $g_F(y) \le R(y)$。

综上，$g_F(y) = \inf_{r_{KF} z = y} g_K(z)$。

### 3. 是否需要纤维下确界取到

**结论：不需要。**

**说明**：
1. 在 $g_F$ 凸性的证明中，我们从未要求存在 $x_i$ 使 $f(x_i) = g_F(y_i)$，而是利用下确界定义对任意 $\varepsilon > 0$ 选取纤维 $\{q_F = y_i\}$ 中的 $\varepsilon$-近似点（满足 $f(x_i) \le t_i + \varepsilon$），结合 $\operatorname{epi}_{\mathbb{R}}(f)$ 的凸性后再令 $\varepsilon \downarrow 0$ 即可。
2. 在 $g_F(y) = \inf_{r_{KF} z = y} g_K(z)$ 的证明中，仅用到了纤维分解 $\{x \in E : q_F x = y\} = \bigsqcup_{r_{KF} z = y} \{x \in E : q_K x = z\}$ 以及下确界作为最大下界的序刻画（含 $\inf \emptyset = +\infty$ 的约定），不论 $g_F(y)$、$g_K(z)$ 或右式关于 $z$ 的下确界是否取到，双向不等式均严格成立。

---

## S2　紧次水平集

我们先给出实高度上图闭性与次水平集闭性的等价刻画，以及 $F^*$ 与 $q_F$ 的拓扑性质。

**引理 2.1（下半连续与闭次水平集的等价性）**：设 $X$ 为拓扑空间，$u: X \to [-\infty, +\infty]$。则 $\operatorname{epi}_{\mathbb{R}}(u)$ 在乘积空间 $X \times \mathbb{R}$ 中闭，当且仅当对每个 $c \in \mathbb{R}$，次水平集 $\{x \in X : u(x) \le c\}$ 在 $X$ 中闭。
- *证明*：（$\Rightarrow$）固定 $c \in \mathbb{R}$，映射 $\iota_c: X \to X \times \mathbb{R}$，$\iota_c(x) = (x, c)$ 连续，故 $\{u \le c\} = \iota_c^{-1}(\operatorname{epi}_{\mathbb{R}}(u))$ 在 $X$ 中闭。
  （$\Leftarrow$）任取 $(x_0, t_0) \in (X \times \mathbb{R}) \setminus \operatorname{epi}_{\mathbb{R}}(u)$，则 $t_0 \in \mathbb{R}$ 且 $u(x_0) > t_0$。取实数 $c$ 满足 $t_0 < c < u(x_0)$。因 $\{u \le c\}$ 闭，集合 $U := (X \setminus \{u \le c\}) \times (-\infty, c)$ 是 $(x_0, t_0)$ 在 $X \times \mathbb{R}$ 中的开邻域；对任意 $(x, t) \in U$ 有 $u(x) > c > t$，故 $U \cap \operatorname{epi}_{\mathbb{R}}(u) = \emptyset$。因此 $\operatorname{epi}_{\mathbb{R}}(u)$ 闭。$\square$

**引理 2.2（$F^*$ 的 Hausdorff 性与 $q_F$ 的连续性）**：对任意 $F \in \mathcal{F}$，$F^*$ 在有限维拓扑下是实 Hausdorff 局部凸空间，且 $q_F: E \to F^*$ 连续。
- *证明*：令 $m = \dim F < \infty$。若 $m = 0$，则 $F^* = \{0\}$ 赋单点 Hausdorff 拓扑，$q_F$ 为常值映射从而连续。若 $m \ge 1$，取 $F$ 的一组基 $\varphi_1, \dots, \varphi_m \in F \subset E'$，定义线性双射 $\Phi: F^* \to \mathbb{R}^m$，$\Phi(y) = (y(\varphi_1), \dots, y(\varphi_m))$。由有限维实拓扑向量空间上 Hausdorff 向量拓扑的唯一性定理（此处 $\dim F^* = m < \infty$ 满足定理条件），$\Phi$ 是拓扑向量空间同构，特别地 $F^*$ 是实 Hausdorff 局部凸空间。又对任意 $x \in E$ 有 $(\Phi \circ q_F)(x) = (\varphi_1(x), \dots, \varphi_m(x))$，每个分量 $\varphi_j \in E'$ 在 $E$ 上连续，故 $\Phi \circ q_F: E \to \mathbb{R}^m$ 连续，从而 $q_F = \Phi^{-1} \circ (\Phi \circ q_F): E \to F^*$ 连续。$\square$

### 1. 证明 $g_F(y) < +\infty$ 时纤维下确界取到

设 $y \in F^*$ 满足 $g_F(y) < +\infty$。由 S1 知 $g_F(y) \in [0, +\infty)$。取定实数 $c_0 := g_F(y) + 1 > g_F(y)$，对每个 $c \in (g_F(y), c_0]$ 定义
$$A_c := \{x \in E : q_F x = y \text{ 且 } f(x) \le c\} = q_F^{-1}(\{y\}) \cap \{f \le c\}.$$
1. **非空性**：因 $g_F(y) = \inf_{q_F x = y} f(x) < c$，由下确界定义知 $A_c \neq \emptyset$。
2. **在紧集 $K_0 := \{f \le c_0\}$ 中为闭集**：由本阶段假设，$K_0$ 与 $\{f \le c\}$ 均为 Hausdorff 空间 $E$ 中的紧集，而 Hausdorff 空间中的紧集必闭，故 $\{f \le c\}$ 在 $E$ 中闭（亦直接由 $f$ 下半连续及引理 2.1 得到）。又由引理 2.2，$F^*$ 为 Hausdorff 空间故单点集 $\{y\}$ 闭，$q_F$ 连续故 $q_F^{-1}(\{y\})$ 在 $E$ 中闭。因此对一切 $c \in (g_F(y), c_0]$，$A_c \subset K_0$ 且在紧空间 $K_0$ 中闭。
3. **有限交性质**：对任意有限个 $c_1, \dots, c_k \in (g_F(y), c_0]$，令 $\bar{c} := \min_{1 \le j \le k} c_j \in (g_F(y), c_0]$，由单调性知 $\bigcap_{j=1}^k A_{c_j} = A_{\bar{c}} \neq \emptyset$。

由紧空间的有限交刻画定理（$K_0$ 紧，闭子集族 $\{A_c\}_{c \in (g_F(y), c_0]}$ 具有有限交性质），交集 $\bigcap_{c \in (g_F(y), c_0]} A_c$ 非空。取其中一点 $x_* \in E$，则 $q_F x_* = y$（故 $f(x_*) \ge g_F(y)$），且对一切 $c \in (g_F(y), c_0]$ 有 $f(x_*) \le c$。令 $c \downarrow g_F(y)$ 得 $f(x_*) \le g_F(y)$，从而 $f(x_*) = g_F(y)$，纤维下确界在 $x_*$ 处取到。

### 2. 证明各 $g_F$ 下半连续

固定 $F \in \mathcal{F}$。由引理 2.1，只需证对每个 $c \in \mathbb{R}$，次水平集 $\{y \in F^* : g_F(y) \le c\}$ 在 $F^*$ 中闭。断言对每个 $c \in \mathbb{R}$ 有集合恒等式：
$$\{y \in F^* : g_F(y) \le c\} = q_F(\{x \in E : f(x) \le c\}).$$
- **（$\supset$）**：若 $y = q_F x$ 且 $f(x) \le c$，则 $g_F(y) \le f(x) \le c$。
- **（$\subset$）**：若 $g_F(y) \le c$，因 $c \in \mathbb{R}$，必有 $g_F(y) < +\infty$。由上面刚证得的纤维下确界可达性，存在 $x_* \in E$ 使 $q_F x_* = y$ 且 $f(x_*) = g_F(y) \le c$，故 $y \in q_F(\{f \le c\})$。

由本阶段假设，$\{f \le c\}$ 在 $E$ 中紧；由引理 2.2，$q_F: E \to F^*$ 连续，紧集的连续像紧，故 $q_F(\{f \le c\})$ 在 $F^*$ 中紧。又由引理 2.2，$F^*$ 为 Hausdorff 空间，其紧子集必为闭集，故 $\{g_F \le c\}$ 在 $F^*$ 中闭。由引理 2.1 知 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^* \times \mathbb{R}$ 中闭，即 $g_F$ 下半连续。

---

## S3　兼容成本记录的实现

### 1. 构造

记 $K_c := \{z \in E : f(z) \le c\}$。对每个 $F \in \mathcal{F}$，定义子集
$$C_F := \{z \in E : f(z) \le c \text{ 且 } q_F z = y_F\} = K_c \cap q_F^{-1}(\{y_F\}),$$
并定义全族交集
$$C_\infty := \bigcap_{F \in \mathcal{F}} C_F.$$
我们将证明 $C_\infty$ 恰为单点集，并取 $x \in E$ 为 $C_\infty$ 中唯一的元素。

### 2. 存在性、唯一性与所需性质的验证

1. **$C_\infty$ 非空（存在性）**：
   - 对每个 $F \in \mathcal{F}$，由假设 $g_F(y_F) \le c < +\infty$。因当前处于 S2 条件下，S2 的全部前提满足，援引 S2 中纤维下确界可达的结论，存在 $z_F \in E$ 使 $q_F z_F = y_F$ 且 $f(z_F) = g_F(y_F) \le c$，故 $z_F \in C_F$，即 $C_F \neq \emptyset$。
   - 由 S2 假设，$K_c = \{f \le c\}$ 是 $E$ 的紧子集；由引理 2.2，$F^*$ 为 Hausdorff 空间且 $q_F$ 连续，故 $q_F^{-1}(\{y_F\})$ 在 $E$ 中闭，从而每个 $C_F$ 是紧空间 $K_c$ 的闭子集。
   - 若 $F \subset K$（$F, K \in \mathcal{F}$），对任意 $z \in C_K$，利用 $r_{KF} \circ q_K = q_F$ 与兼容性条件 $r_{KF} y_K = y_F$，有
     $$q_F z = r_{KF}(q_K z) = r_{KF} y_K = y_F,$$
     结合 $f(z) \le c$ 知 $z \in C_F$。因此 $F \subset K \implies C_K \subset C_F$。
   - 任取有限个 $F_1, \dots, F_n \in \mathcal{F}$（$n \ge 1$），令 $K := F_1 + \dots + F_n \subset E'$。因各 $F_i$ 有限维，$\dim K \le \sum_{i=1}^n \dim F_i < +\infty$，故 $K \in \mathcal{F}$，且对每个 $i$ 有 $F_i \subset K$，于是
     $$\emptyset \neq C_K \subset \bigcap_{i=1}^n C_{F_i}.$$
     这表明紧空间 $K_c$ 的闭子集族 $\{C_F\}_{F \in \mathcal{F}}$ 具有有限交性质。由紧空间的有限交性质定理，$C_\infty = \bigcap_{F \in \mathcal{F}} C_F \neq \emptyset$。

2. **唯一性（故 $C_\infty$ 为单点集，且在整个 $E$ 中满足条件的点唯一）**：
   设 $x_1, x_2 \in E$ 均满足对一切 $F \in \mathcal{F}$ 有 $q_F x_1 = y_F$ 与 $q_F x_2 = y_F$（注意唯一性甚至无需用到 $f(x_i) \le c$）。任取 $\varphi \in E'$，令 $F_\varphi := \operatorname{span}\{\varphi\}$，则 $\dim F_\varphi \le 1$，故 $F_\varphi \in \mathcal{F}$。由假设得
   $$\varphi(x_1) = (q_{F_\varphi} x_1)(\varphi) = y_{F_\varphi}(\varphi) = (q_{F_\varphi} x_2)(\varphi) = \varphi(x_2),$$
   即对一切 $\varphi \in E'$ 有 $\varphi(x_1 - x_2) = 0$。
   由共同设定，$E$ 是实 Hausdorff 局部凸空间。若 $v := x_1 - x_2 \neq 0$，由局部凸性与 Hausdorff 性，存在 $E$ 上的连续半范数 $p$ 使 $p(v) > 0$；对一维子空间 $\mathbb{R}v$ 上的线性泛函 $\lambda v \mapsto \lambda p(v)$（受控于连续半范数 $p$）应用实 Hahn–Banach 延拓定理，可得 $\varphi \in E'$ 使 $\varphi(v) = p(v) > 0$，矛盾。因此 $x_1 = x_2$。

3. **性质核验**：
   由此知 $C_\infty$ 为单点集 $\{x\}$。由 $x \in C_\infty = \bigcap_{F \in \mathcal{F}} C_F$：
   - 对每个 $F \in \mathcal{F}$，因 $x \in C_F$，有 $q_F x = y_F$；
   - 因 $x \in K_c$，有 $f(x) \le c$；
   - 上述第 2 步已证任何满足 $\forall F \in \mathcal{F},\, q_F x' = y_F$（特别地还满足 $f(x') \le c$）的 $x' \in E$ 必等于 $x$。全部所需性质均成立。

---

## S4　一般成本的恢复

### 1. 判断结论

**结论：能。** 仅由全部 $g_F$（$F \in \mathcal{F}$）即可构造满足全部要求的 $G: E \to [0, +\infty]$。

### 2. 预备引理（闭上图包）

**引理 4.1**：设 $X$ 为任一实拓扑向量空间，$u: X \to [0, +\infty]$ 为凸函数。令 $M := \overline{\operatorname{epi}_{\mathbb{R}}(u)}$（在乘积拓扑向量空间 $X \times \mathbb{R}$ 中取闭包），并定义
$$u_{\operatorname{cl}}(x) := \inf\{t \in \mathbb{R} : (x, t) \in M\} \qquad (x \in X,\ \inf \emptyset = +\infty).$$
则：
1. $u_{\operatorname{cl}}$ 取值于 $[0, +\infty]$，且 $\operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}}) = M$；
2. $u_{\operatorname{cl}}$ 下半连续、凸，且 $u_{\operatorname{cl}} \le u$；
3. 若 $h: X \to [-\infty, +\infty]$ 下半连续（允许同时取 $-\infty$ 与 $+\infty$）且 $h \le u$，则 $h \le u_{\operatorname{cl}}$。

- *证明*：
  1. 因 $u \ge 0$，$\operatorname{epi}_{\mathbb{R}}(u) \subset X \times [0, +\infty)$。而 $X \times [0, +\infty)$ 在 $X \times \mathbb{R}$ 中闭，故 $M \subset X \times [0, +\infty)$，从而对每个 $x \in X$ 有 $u_{\operatorname{cl}}(x) \in [0, +\infty]$。
     验证 $\operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}}) = M$：若 $(x, t) \in M$，由下确界定义知 $u_{\operatorname{cl}}(x) \le t$，故 $M \subset \operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}})$。反之，设 $(x, t) \in \operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}})$（$t \in \mathbb{R}$，$u_{\operatorname{cl}}(x) \le t$）。对每个整数 $n \ge 1$，存在 $t_n \in \mathbb{R}$ 使 $(x, t_n) \in M$ 且 $t_n < t + \frac{1}{n}$。对任意 $r \ge 0$，平移映射 $(z, s) \mapsto (z, s + r)$ 是 $X \times \mathbb{R}$ 的同胚且将 $\operatorname{epi}_{\mathbb{R}}(u)$ 映入自身，故也将闭包 $M$ 映入 $M$；取 $r = t + \frac{1}{n} - t_n > 0$ 知 $(x, t + \frac{1}{n}) \in M$。在 $X \times \mathbb{R}$ 中令 $n \to \infty$，由 $M$ 的闭性得 $(x, t) \in M$。故 $\operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}}) = M$。
  2. $M$ 为闭集；又在实拓扑向量空间 $X \times \mathbb{R}$ 中，对固定 $\lambda \in [0, 1]$，凸组合映射 $(w_1, w_2) \mapsto \lambda w_1 + (1-\lambda)w_2$ 连续，故凸集 $\operatorname{epi}_{\mathbb{R}}(u)$ 的闭包 $M$ 仍为凸集。因此 $u_{\operatorname{cl}}$ 下半连续且凸。由 $\operatorname{epi}_{\mathbb{R}}(u) \subset M = \operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}})$ 即得 $u_{\operatorname{cl}} \le u$。
  3. 设 $h: X \to [-\infty, +\infty]$ 下半连续且 $h \le u$。对任意 $(x, t) \in \operatorname{epi}_{\mathbb{R}}(u)$ 有 $h(x) \le u(x) \le t$，故 $\operatorname{epi}_{\mathbb{R}}(u) \subset \operatorname{epi}_{\mathbb{R}}(h)$。因 $\operatorname{epi}_{\mathbb{R}}(h)$ 闭，取闭包得 $\operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}}) = M \subset \operatorname{epi}_{\mathbb{R}}(h)$。现对任意 $x \in X$：若 $u_{\operatorname{cl}}(x) = +\infty$，显然 $h(x) \le +\infty = u_{\operatorname{cl}}(x)$；若 $u_{\operatorname{cl}}(x) = t \in [0, +\infty)$，则 $(x, t) \in \operatorname{epi}_{\mathbb{R}}(u_{\operatorname{cl}}) \subset \operatorname{epi}_{\mathbb{R}}(h)$，按定义即 $h(x) \le t = u_{\operatorname{cl}}(x)$。故恒有 $h \le u_{\operatorname{cl}}$。$\square$

### 3. $G$ 的显式构造

仅使用共同设定：对每个有限维子空间 $F \in \mathcal{F}$，由 S1（仅依赖共同设定）知 $g_F: F^* \to [0, +\infty]$ 非负且凸；由引理 2.2（仅依赖 $F$ 有限维及 $F \subset E'$）知 $F^*$ 是实拓扑向量空间。因此可对 $g_F$ 应用引理 4.1，纯粹由 $g_F$ 及 $F^*$ 的有限维拓扑定义 $(g_F)_{\operatorname{cl}}: F^* \to [0, +\infty]$：
$$(g_F)_{\operatorname{cl}}(y) := \inf\left\{t \in \mathbb{R} : (y, t) \in \overline{\operatorname{epi}_{\mathbb{R}}(g_F)}\right\} \qquad (y \in F^*).$$
进而在 $E$ 上定义对应于观测空间 $F$ 的恢复函数 $G_F: E \to [0, +\infty]$ 与总恢复函数 $G: E \to [0, +\infty]$：
$$G_F(x) := (g_F)_{\operatorname{cl}}(q_F x), \qquad G(x) := \sup_{F \in \mathcal{F}} G_F(x) = \sup_{F \in \mathcal{F}} (g_F)_{\operatorname{cl}}(q_F x) \qquad (x \in E).$$
该构造完全由族 $\{g_F\}_{F \in \mathcal{F}}$（连同典范映射 $q_F$ 与 $F^*$ 的有限维拓扑）给出。

### 4. $G$ 的性质验证

1. **取值范围与 $G \le f$**：
   由引理 4.1(1)，每个 $(g_F)_{\operatorname{cl}}$ 取值于 $[0, +\infty]$，且 $\mathcal{F} \neq \emptyset$（例如 $\{0\} \in \mathcal{F}$），故 $G: E \to [0, +\infty]$。对任意 $F \in \mathcal{F}$ 与 $x \in E$，由引理 4.1(2) 及 $g_F$ 定义有
   $$G_F(x) = (g_F)_{\operatorname{cl}}(q_F x) \le g_F(q_F x) \le f(x),$$
   对 $F \in \mathcal{F}$ 取上确界得 $G \le f$。

2. **下半连续性与凸性**：
   对每个 $F \in \mathcal{F}$，定义映射 $Q_F: E \times \mathbb{R} \to F^* \times \mathbb{R}$，$Q_F(x, t) = (q_F x, t)$。由引理 2.2 知 $q_F$ 连续且线性，故 $Q_F$ 连续且线性。注意到
   $$\operatorname{epi}_{\mathbb{R}}(G_F) = \{(x, t) \in E \times \mathbb{R} : (g_F)_{\operatorname{cl}}(q_F x) \le t\} = Q_F^{-1}\bigl(\operatorname{epi}_{\mathbb{R}}((g_F)_{\operatorname{cl}})\bigr).$$
   由引理 4.1(2)，$\operatorname{epi}_{\mathbb{R}}((g_F)_{\operatorname{cl}})$ 在 $F^* \times \mathbb{R}$ 中闭且凸，连续线性映射下闭凸集的原像仍闭且凸，故 $\operatorname{epi}_{\mathbb{R}}(G_F)$ 在 $E \times \mathbb{R}$ 中闭且凸。又因 $\sup_{F \in \mathcal{F}} G_F(x) \le t \iff \forall F \in \mathcal{F},\, G_F(x) \le t$，有
   $$\operatorname{epi}_{\mathbb{R}}(G) = \bigcap_{F \in \mathcal{F}} \operatorname{epi}_{\mathbb{R}}(G_F).$$
   任意族闭凸集的交集仍闭且凸，故 $\operatorname{epi}_{\mathbb{R}}(G)$ 在 $E \times \mathbb{R}$ 中闭且凸，即 $G$ 下半连续且凸。

3. **在全部下半连续凸下界（含允许同时取 $-\infty$ 与 $+\infty$ 的竞争函数）中的最大性**：
   我们先证明上图恒等式 $\operatorname{epi}_{\mathbb{R}}(G) = \overline{\operatorname{epi}_{\mathbb{R}}(f)}$：
   - 由 $G \le f$ 及 $\operatorname{epi}_{\mathbb{R}}(G)$ 闭，立即有 $\overline{\operatorname{epi}_{\mathbb{R}}(f)} \subset \operatorname{epi}_{\mathbb{R}}(G)$。
   - 反之，任取 $(x_1, t_1) \in (E \times \mathbb{R}) \setminus \overline{\operatorname{epi}_{\mathbb{R}}(f)}$。验证实局部凸空间中 Hahn–Banach 严格分离定理的适用条件：由共同设定，$E$ 是实 Hausdorff 局部凸空间，故乘积空间 $E \times \mathbb{R}$ 也是实 Hausdorff 局部凸空间；$f$ 为凸函数且存在 $x_0 \in E$ 使 $f(x_0) < +\infty$，故 $(x_0, f(x_0)) \in \operatorname{epi}_{\mathbb{R}}(f)$，从而 $M_f := \overline{\operatorname{epi}_{\mathbb{R}}(f)}$ 是 $E \times \mathbb{R}$ 中**非空闭凸集**；单点集 $\{(x_1, t_1)\}$ 是与 $M_f$ 不交的**紧凸集**。
     应用 Hahn–Banach 严格分离定理，存在连续线性泛函 $\Phi \in (E \times \mathbb{R})'$ 及实数 $\alpha \in \mathbb{R}$ 使
     $$\Phi(x_1, t_1) < \alpha < \inf_{(x, t) \in M_f} \Phi(x, t).$$
     因乘积空间连续对偶满足 $(E \times \mathbb{R})' \cong E' \times \mathbb{R}$，可将 $\Phi$ 唯一表为 $\Phi(x, t) = -\varphi(x) + s t$，其中 $\varphi \in E'$（$\varphi(x) = -\Phi(x, 0)$），$s = \Phi(0, 1) \in \mathbb{R}$。令 $\varepsilon := \alpha - \Phi(x_1, t_1) > 0$，则对一切 $(x, \tau) \in \operatorname{epi}_{\mathbb{R}}(f) \subset M_f$ 有
     $$-\varphi(x) + s\tau \ge -\varphi(x_1) + s t_1 + \varepsilon.$$
     取一维（或零维）观测子空间 $F := \operatorname{span}\{\varphi\} \in \mathcal{F}$，定义 $F^*$ 上的求值泛函 $\ell_\varphi(y) := y(\varphi)$（在有限维空间 $F^*$ 上线性从而连续），并令 $\Psi: F^* \times \mathbb{R} \to \mathbb{R}$，$\Psi(y, t) := -\ell_\varphi(y) + s t$（连续函数）。注意对一切 $x \in E$ 有 $\ell_\varphi(q_F x) = \varphi(x)$。
     任取 $(y, t) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 及任意 $\eta > 0$，因 $g_F(y) \le t < t + \eta$，存在 $x \in E$ 使 $q_F x = y$ 且 $f(x) \le t + \eta$，即 $(x, t + \eta) \in \operatorname{epi}_{\mathbb{R}}(f)$。代入分离不等式得
     $$\Psi(y, t) + s\eta = -\varphi(x) + s(t + \eta) \ge -\varphi(x_1) + s t_1 + \varepsilon = \Psi(q_F x_1, t_1) + \varepsilon.$$
     令 $\eta \downarrow 0$，得对一切 $(y, t) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 有 $\Psi(y, t) \ge \Psi(q_F x_1, t_1) + \varepsilon$。因 $\Psi$ 连续，闭半空间 $\{(y, t) \in F^* \times \mathbb{R} : \Psi(y, t) \ge \Psi(q_F x_1, t_1) + \varepsilon\}$ 包含闭包 $\overline{\operatorname{epi}_{\mathbb{R}}(g_F)} = \operatorname{epi}_{\mathbb{R}}((g_F)_{\operatorname{cl}})$。而 $\Psi(q_F x_1, t_1) < \Psi(q_F x_1, t_1) + \varepsilon$，故 $(q_F x_1, t_1) \notin \operatorname{epi}_{\mathbb{R}}((g_F)_{\operatorname{cl}})$，即 $G_F(x_1) = (g_F)_{\operatorname{cl}}(q_F x_1) > t_1$，从而 $G(x_1) \ge G_F(x_1) > t_1$，即 $(x_1, t_1) \notin \operatorname{epi}_{\mathbb{R}}(G)$。
   - 因此 $\operatorname{epi}_{\mathbb{R}}(G) = \overline{\operatorname{epi}_{\mathbb{R}}(f)} = \operatorname{epi}_{\mathbb{R}}(f_{\operatorname{cl}})$，从而 $G = f_{\operatorname{cl}}$。
   - 现在任取满足下半连续、凸且 $h \le f$ 的竞争函数 $h: E \to [-\infty, +\infty]$（允许同时取 $-\infty$ 与 $+\infty$）。由引理 4.1(3)（取 $X = E$，$u = f$），直接得 $h \le f_{\operatorname{cl}} = G$。（并且满足该普遍性质的 $G$ 唯一：若有另一 $G'$ 也满足，互取竞争函数即得 $G \le G'$ 与 $G' \le G$。）

### 5. 扩大观测空间时的关系

设观测空间由 $F$ 扩大为 $K$，即 $F \subset K$（$F, K \in \mathcal{F}$）：
1. **对偶空间上的保序关系**：
   因 $F^*, K^*$ 均为有限维实 Hausdorff 拓扑向量空间，线性限制映射 $r_{KF}: K^* \to F^*$ 连续，从而映射 $R_{KF}: K^* \times \mathbb{R} \to F^* \times \mathbb{R}$，$R_{KF}(z, t) = (r_{KF} z, t)$ 连续。由 S1 的结论 $g_F(y) = \inf_{r_{KF} w = y} g_K(w)$，对任意 $z \in K^*$ 有 $g_F(r_{KF} z) \le g_K(z)$，故
   $$\operatorname{epi}_{\mathbb{R}}(g_K) \subset R_{KF}^{-1}\bigl(\operatorname{epi}_{\mathbb{R}}(g_F)\bigr) \subset R_{KF}^{-1}\bigl(\operatorname{epi}_{\mathbb{R}}((g_F)_{\operatorname{cl}})\bigr).$$
   右端为闭集在连续映射 $R_{KF}$ 下的原像，在 $K^* \times \mathbb{R}$ 中闭；对左端取闭包并由引理 4.1(1) 得 $\operatorname{epi}_{\mathbb{R}}((g_K)_{\operatorname{cl}}) \subset R_{KF}^{-1}(\operatorname{epi}_{\mathbb{R}}((g_F)_{\operatorname{cl}}))$，等价于
   $$(g_F)_{\operatorname{cl}}(r_{KF} z) \le (g_K)_{\operatorname{cl}}(z) \qquad (\forall z \in K^*).$$
2. **原空间恢复序列的单调递增性与定向网极限**：
   在上式中令 $z = q_K x$ 并用 $r_{KF} \circ q_K = q_F$，得逐点单调性
   $$F \subset K \implies G_F(x) \le G_K(x) \le G(x) \le f(x) \qquad (\forall x \in E).$$
   又因 $(\mathcal{F}, \subset)$ 构成向上定向集（对任意 $F_1, F_2 \in \mathcal{F}$，$F_1 + F_2 \in \mathcal{F}$ 同时包含 $F_1, F_2$），扩大观测空间时 $\{G_F\}_{F \in \mathcal{F}}$ 单调不减地逼近 $G$，上确界即为定向网极限：
   $$G(x) = \sup_{F \in \mathcal{F}} G_F(x) = \lim_{F \in (\mathcal{F}, \subset)} G_F(x) \qquad (\forall x \in E).$$

---

## S5　闭成本的有限投影

### 1. 判断结论

**结论：否（每个有限维 $F$ 的 $g_F$ 不必下半连续）。**

### 2. 反例构造与完整核验

设 $E = \mathbb{R}^2$（赋标准 Euclid 拓扑，为实 Hausdorff 局部凸空间）。记闭双曲区域
$$C := \{(x_1, x_2) \in \mathbb{R}^2 : x_1 \ge 0,\ x_2 \ge 0,\ x_1 x_2 \ge 1\},$$
定义 $f: \mathbb{R}^2 \to [0, +\infty]$ 为 $C$ 的示性函数：
$$f(x_1, x_2) := \begin{cases} 0, & (x_1, x_2) \in C, \\ +\infty, & (x_1, x_2) \notin C. \end{cases}$$

1. **核验 $f$ 满足本阶段全部条件**：
   - **非负与至少一点有限**：$f$ 取值于 $\{0, +\infty\} \subset [0, +\infty]$；点 $(1, 1) \in C$，故 $f(1, 1) = 0 < +\infty$。
   - **下半连续性（$\operatorname{epi}_{\mathbb{R}}(f)$ 闭）**：对 $(x_1, x_2, t) \in \mathbb{R}^2 \times \mathbb{R}$，$f(x_1, x_2) \le t \iff (x_1, x_2) \in C \text{ 且 } t \ge 0$，故
     $$\operatorname{epi}_{\mathbb{R}}(f) = C \times [0, +\infty) = \{(x_1, x_2, t) \in \mathbb{R}^2 \times \mathbb{R} : x_1 \ge 0,\ x_2 \ge 0,\ x_1 x_2 \ge 1,\ t \ge 0\}.$$
     因映射 $(x_1, x_2, t) \mapsto x_1,\, x_2,\, x_1 x_2,\, t$ 在 $\mathbb{R}^2 \times \mathbb{R}$ 上均连续，$\operatorname{epi}_{\mathbb{R}}(f)$ 是四个闭集之交，故在 $\mathbb{R}^2 \times \mathbb{R}$ 中闭。
   - **凸性（$\operatorname{epi}_{\mathbb{R}}(f)$ 凸）**：任取 $(u_1, u_2, t_1), (v_1, v_2, t_2) \in \operatorname{epi}_{\mathbb{R}}(f)$ 及 $\lambda \in [0, 1]$。由 $u_1 \ge 0, u_2 \ge 0, u_1 u_2 \ge 1$ 知 $u_1 > 0$ 且 $u_2 \ge 1/u_1$；同理 $v_1 > 0$ 且 $v_2 \ge 1/v_1$。令 $w_1 = \lambda u_1 + (1-\lambda)v_1 > 0$，$w_2 = \lambda u_2 + (1-\lambda)v_2 > 0$，$t = \lambda t_1 + (1-\lambda)t_2 \ge 0$。利用 $\frac{u_1}{v_1} + \frac{v_1}{u_1} \ge 2$ 有
     $$w_1 w_2 \ge (\lambda u_1 + (1-\lambda)v_1)\left(\frac{\lambda}{u_1} + \frac{1-\lambda}{v_1}\right) = \lambda^2 + (1-\lambda)^2 + \lambda(1-\lambda)\left(\frac{u_1}{v_1} + \frac{v_1}{u_1}\right) \ge (\lambda + 1 - \lambda)^2 = 1.$$
     故 $(w_1, w_2, t) \in C \times [0, +\infty) = \operatorname{epi}_{\mathbb{R}}(f)$，$\operatorname{epi}_{\mathbb{R}}(f)$ 为凸集。

2. **选取有限维子空间 $F$ 并计算 $g_F$**：
   定义 $\varphi_1 \in (\mathbb{R}^2)'$ 为第一坐标投影 $\varphi_1(x_1, x_2) = x_1$（线性且连续），取一维子空间 $F := \operatorname{span}\{\varphi_1\} \subset (\mathbb{R}^2)'$。线性双射 $\Phi: F^* \to \mathbb{R}$，$\Phi(y) = y(\varphi_1)$ 给出有限维拓扑下的拓扑向量空间同构；对每个 $s \in \mathbb{R}$，记 $y_s := \Phi^{-1}(s) \in F^*$（即满足 $y_s(\varphi_1) = s$ 的唯一元）。
   对 $x = (x_1, x_2) \in \mathbb{R}^2$，有 $q_F x = y_s \iff \varphi_1(x_1, x_2) = s \iff x_1 = s$。于是
   $$g_F(y_s) = \inf_{x_2 \in \mathbb{R}} f(s, x_2) = \begin{cases} 0, & s > 0 \quad (\text{取 } x_2 = 1/s > 0 \text{ 时 } (s, 1/s) \in C,\, f(s, 1/s) = 0), \\ +\infty, & s \le 0 \quad (\forall x_2 \in \mathbb{R},\, s x_2 \ge 1 \text{ 与 } s \ge 0, x_2 \ge 0 \text{ 不能同时成立，故 } (s, x_2) \notin C). \end{cases}$$

3. **核验 $g_F$ 不下半连续**：
   对每个正整数 $n \ge 1$，因 $1/n > 0$，有 $g_F(y_{1/n}) = 0 \le 0$，故 $(y_{1/n}, 0) \in \operatorname{epi}_{\mathbb{R}}(g_F)$。在同构 $\Phi \times \operatorname{id}_{\mathbb{R}}: F^* \times \mathbb{R} \to \mathbb{R} \times \mathbb{R}$ 下，点列 $(y_{1/n}, 0)$ 对应于 $(1/n, 0) \to (0, 0)$（$n \to \infty$），故在 $F^* \times \mathbb{R}$ 中 $(y_{1/n}, 0) \to (y_0, 0)$。然而 $g_F(y_0) = +\infty > 0$，故 $(y_0, 0) \notin \operatorname{epi}_{\mathbb{R}}(g_F)$。因此 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^* \times \mathbb{R}$ 中不闭，即 $g_F$ 不下半连续。

---

## S6　恢复与投影的精确关系

在共同设定下，对任一实拓扑向量空间 $X$（此处为 $E$、$F^*$ 或 $K^*$）上的非负凸函数 $u: X \to [0, +\infty]$，由 S4 的引理 4.1 知，$u$ 的最大下半连续凸下界 $\bar{u}$ 唯一存在且恰为闭上图包 $u_{\operatorname{cl}}$，满足 $\bar{u}: X \to [0, +\infty]$ 及 $\operatorname{epi}_{\mathbb{R}}(\bar{u}) = \overline{\operatorname{epi}_{\mathbb{R}}(u)}$。特别地，对 $F \in \mathcal{F}$ 有 $\overline{g_F} = (g_F)_{\operatorname{cl}}$，且 S4 构造的 $G$ 满足 $G = \bar{f}$。

### 1. 证明 $G = f$ 当且仅当 $f$ 下半连续

- **（$\Rightarrow$）**：若 $G = f$，因 S4（同样仅依赖共同设定）已证 $G$ 下半连续，故 $f = G$ 下半连续。
- **（$\Leftarrow$）**：若 $f$ 下半连续，结合共同设定中 $f$ 为凸函数且 $f \le f$，将 $h = f$ 代入 S4 所证 $G$ 的最大下界性质即得 $f \le G$；结合 S4 已证的 $G \le f$，得 $G = f$。

### 2. 证明 $\overline{g_F} = \overline{\bigl(y \mapsto \inf_{r_{KF} z = y} \overline{g_K}(z)\bigr)}$

设 $F \subset K$（$F, K \in \mathcal{F}$），记 $h_{KF}: F^* \to [0, +\infty]$ 为
$$h_{KF}(y) := \inf_{r_{KF} z = y} \overline{g_K}(z) \qquad (y \in F^*,\ \inf \emptyset = +\infty).$$
1. **先验证 $h_{KF}$ 非负且凸（使 $\overline{h_{KF}}$ 有定义）**：
   因 $\overline{g_K}$ 取值于 $[0, +\infty]$，故 $h_{KF}$ 取值于 $[0, +\infty]$。又 $\overline{g_K}: K^* \to [0, +\infty]$ 为凸函数，$r_{KF}: K^* \to F^*$ 为线性映射：对任意 $(y_1, t_1), (y_2, t_2) \in \operatorname{epi}_{\mathbb{R}}(h_{KF})$、$\lambda \in (0, 1)$ 及 $\varepsilon > 0$，存在 $z_i \in K^*$ 使 $r_{KF} z_i = y_i$ 且 $\overline{g_K}(z_i) \le t_i + \varepsilon$（$i = 1, 2$）；由 $\operatorname{epi}_{\mathbb{R}}(\overline{g_K})$ 的凸性及 $r_{KF}$ 的线性性，有 $r_{KF}(\lambda z_1 + (1-\lambda)z_2) = \lambda y_1 + (1-\lambda)y_2$ 且 $\overline{g_K}(\lambda z_1 + (1-\lambda)z_2) \le \lambda t_1 + (1-\lambda)t_2 + \varepsilon$，令 $\varepsilon \downarrow 0$ 即知 $h_{KF}$ 为凸函数。
2. **证明夹逼不等式 $\overline{g_F} \le h_{KF} \le g_F$**：
   - 因 $\overline{g_K} \le g_K$，对每个 $y \in F^*$ 在纤维 $\{r_{KF} z = y\}$ 上取下确界并援引 S1（仅依赖共同设定）得
     $$h_{KF}(y) = \inf_{r_{KF} z = y} \overline{g_K}(z) \le \inf_{r_{KF} z = y} g_K(z) = g_F(y),$$
     即 $h_{KF} \le g_F$。
   - 另一方面，援引 S4 第 5 节已证的对偶保序不等式 $\overline{g_F}(r_{KF} z) \le \overline{g_K}(z)$（$\forall z \in K^*$，仅依赖共同设定）：对固定 $y \in F^*$ 及任意满足 $r_{KF} z = y$ 的 $z \in K^*$，有 $\overline{g_F}(y) = \overline{g_F}(r_{KF} z) \le \overline{g_K}(z)$；对 $r_{KF} z = y$ 取下确界得 $\overline{g_F}(y) \le h_{KF}(y)$，即 $\overline{g_F} \le h_{KF}$。
3. **导出 $\overline{g_F} = \overline{h_{KF}}$**：
   - 因 $\overline{h_{KF}}$ 下半连续、凸且 $\overline{h_{KF}} \le h_{KF} \le g_F$，由 $\overline{g_F}$ 作为 $g_F$ 最大下半连续凸下界的定义得 $\overline{h_{KF}} \le \overline{g_F}$；
   - 因 $\overline{g_F}$ 本身下半连续、凸且 $\overline{g_F} \le h_{KF}$，由 $\overline{h_{KF}}$ 作为 $h_{KF}$ 最大下半连续凸下界的定义得 $\overline{g_F} \le \overline{h_{KF}}$。
   故 $\overline{g_F} = \overline{h_{KF}}$。

### 3. 判断右式的最外层 bar 能否总省去

**结论：否（最外层 bar 不能总省去）。**

**反例与完整核验**：
取 $E = \mathbb{R}^2$ 及 S5 中的函数 $f = \iota_C: \mathbb{R}^2 \to [0, +\infty]$，其中 $C = \{(x_1, x_2) \in \mathbb{R}^2 : x_1 \ge 0,\ x_2 \ge 0,\ x_1 x_2 \ge 1\}$。如 S5 所核验，$E$ 为实 Hausdorff 局部凸空间，$f$ 非负、凸、在 $(1, 1)$ 处有限（故完全符合共同设定），且 $f$ 在 $\mathbb{R}^2$ 上下半连续。

取坐标投影 $\varphi_1(x_1, x_2) = x_1$，$\varphi_2(x_1, x_2) = x_2$，令
$$K := (\mathbb{R}^2)' = \operatorname{span}\{\varphi_1, \varphi_2\} \quad (\dim K = 2), \qquad F := \operatorname{span}\{\varphi_1\} \subset K \quad (\dim F = 1),$$
则 $F, K \in \mathcal{F}$ 且 $F \subset K$。
1. **计算 $\overline{g_K}$**：
   考虑线性映射 $q_K: \mathbb{R}^2 \to K^*$，$q_K(x_1, x_2)(a_1\varphi_1 + a_2\varphi_2) = a_1 x_1 + a_2 x_2$。若 $q_K(x_1, x_2) = 0$，分别代入 $\varphi_1, \varphi_2$ 得 $x_1 = x_2 = 0$，故 $q_K$ 单射；又 $\dim \mathbb{R}^2 = 2 = \dim K^*$，故 $q_K$ 为线性双射。由有限维实 Hausdorff 拓扑向量空间之间线性双射必为同胚的标准定理，$q_K: \mathbb{R}^2 \to K^*$ 是线性同胚。
   对任意 $z \in K^*$，纤维 $\{x \in \mathbb{R}^2 : q_K x = z\} = \{q_K^{-1} z\}$ 为单点集，故 $g_K(z) = f(q_K^{-1} z)$。因 $f$ 在 $\mathbb{R}^2$ 上下半连续且凸，而 $q_K^{-1} \times \operatorname{id}_{\mathbb{R}}: K^* \times \mathbb{R} \to \mathbb{R}^2 \times \mathbb{R}$ 为同胚，$\operatorname{epi}_{\mathbb{R}}(g_K) = (q_K \times \operatorname{id}_{\mathbb{R}})(\operatorname{epi}_{\mathbb{R}}(f))$ 在 $K^* \times \mathbb{R}$ 中闭且凸，即 $g_K$ 已下半连续且凸，从而
   $$\overline{g_K} = g_K.$$
2. **比较无外层 bar 的右式 $h_{KF}$ 与左式 $\overline{g_F}$**：
   由 $\overline{g_K} = g_K$ 及 S1 的结论，对任意 $y \in F^*$ 有
   $$h_{KF}(y) = \inf_{r_{KF} z = y} \overline{g_K}(z) = \inf_{r_{KF} z = y} g_K(z) = g_F(y).$$
   沿用 S5 的记号 $y_s \in F^*$（$y_s(\varphi_1) = s$）：在 $y_0 = 0 \in F^*$ 处，由 S5 已算得
   $$\inf_{r_{KF} z = y_0} \overline{g_K}(z) = g_F(y_0) = +\infty.$$
   另一方面，在 S5 中已验证 $(y_{1/n}, 0) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 且在 $F^* \times \mathbb{R}$ 中 $(y_{1/n}, 0) \to (y_0, 0)$，故 $(y_0, 0) \in \overline{\operatorname{epi}_{\mathbb{R}}(g_F)} = \operatorname{epi}_{\mathbb{R}}(\overline{g_F})$，即 $\overline{g_F}(y_0) \le 0$；结合 $\overline{g_F} \ge 0$ 得
   $$\overline{g_F}(y_0) = 0.$$
   因此在 $y_0 = 0 \in F^*$ 处，$\overline{g_F}(y_0) = 0 \neq +\infty = \inf_{r_{KF} z = y_0} \overline{g_K}(z)$，右式的最外层 bar 不能总省去。
