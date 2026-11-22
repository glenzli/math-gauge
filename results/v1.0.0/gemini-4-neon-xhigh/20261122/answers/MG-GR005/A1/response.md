以下按 S1–S6 逐阶段作答。全文记 $\mathcal{F}$ 为 $E'$ 中所有有限维线性子空间的族。

---

## S1　原始记录

### 1. $g_F$ 非负、凸且至少一点有限

先验证 $q_F: E \to F^*$ 是线性的：对任意 $x_1, x_2 \in E$，$\alpha, \beta \in \mathbb{R}$ 与 $\varphi \in F$，有
$$
q_F(\alpha x_1 + \beta x_2)(\varphi) = \varphi(\alpha x_1 + \beta x_2) = \alpha \varphi(x_1) + \beta \varphi(x_2) = \bigl(\alpha q_F(x_1) + \beta q_F(x_2)\bigr)(\varphi).
$$

- **非负性**：由共同设定，$f(x) \in [0, +\infty]$ 对所有 $x \in E$ 成立。故对每个 $y \in F^*$，集合 $\{f(x) : q_F x = y\}$ 以 $0$ 为下界；若纤维非空则其下确界 $g_F(y) \in [0, +\infty]$，若纤维为空则按约定 $g_F(y) = +\infty \ge 0$。于是 $g_F: F^* \to [0, +\infty]$。
- **至少一点有限**：由共同设定，存在 $x_0 \in E$ 使 $f(x_0) < +\infty$。令 $y_0 = q_F(x_0) \in F^*$，则 $x_0 \in \{x \in E : q_F x = y_0\}$，故
  $$
  0 \le g_F(y_0) = \inf\{f(x) : q_F x = y_0\} \le f(x_0) < +\infty,
  $$
  即 $g_F$ 在 $y_0$ 处有限。
- **凸性（即 $\mathrm{epi}_{\mathbb{R}}(g_F)$ 为 $F^* \times \mathbb{R}$ 中的凸集）**：任取 $(y_1, t_1), (y_2, t_2) \in \mathrm{epi}_{\mathbb{R}}(g_F)$ 以及 $\lambda \in [0, 1]$。于是 $t_1, t_2 \in \mathbb{R}$ 且 $g_F(y_i) \le t_i$（$i = 1, 2$）。
  对任意 $\varepsilon > 0$，由 $g_F(y_i) < t_i + \varepsilon$ 及下确界定义，存在 $x_i \in E$ 满足 $q_F(x_i) = y_i$ 且 $f(x_i) < t_i + \varepsilon$，从而 $(x_i, t_i + \varepsilon) \in \mathrm{epi}_{\mathbb{R}}(f)$（$i = 1, 2$）。
  由 $f$ 的凸性，$\mathrm{epi}_{\mathbb{R}}(f)$ 为凸集，故
  $$
  \bigl(\lambda x_1 + (1-\lambda) x_2,\; \lambda t_1 + (1-\lambda) t_2 + \varepsilon\bigr) = \lambda(x_1, t_1 + \varepsilon) + (1-\lambda)(x_2, t_2 + \varepsilon) \in \mathrm{epi}_{\mathbb{R}}(f),
  $$
  即 $f\bigl(\lambda x_1 + (1-\lambda)x_2\bigr) \le \lambda t_1 + (1-\lambda)t_2 + \varepsilon$。又由 $q_F$ 的线性性，
  $$
  q_F\bigl(\lambda x_1 + (1-\lambda)x_2\bigr) = \lambda q_F(x_1) + (1-\lambda)q_F(x_2) = \lambda y_1 + (1-\lambda)y_2,
  $$
  因此
  $$
  g_F\bigl(\lambda y_1 + (1-\lambda)y_2\bigr) \le f\bigl(\lambda x_1 + (1-\lambda)x_2\bigr) \le \lambda t_1 + (1-\lambda)t_2 + \varepsilon.
  $$
  令 $\varepsilon \to 0^+$，得 $g_F\bigl(\lambda y_1 + (1-\lambda)y_2\bigr) \le \lambda t_1 + (1-\lambda)t_2$，即 $\bigl(\lambda y_1 + (1-\lambda)y_2,\, \lambda t_1 + (1-\lambda)t_2\bigr) \in \mathrm{epi}_{\mathbb{R}}(g_F)$。故 $g_F$ 是凸的。

### 2. 限制相容性：$g_F(y) = \inf_{r_{KF} z = y} g_K(z)$

设 $F \subset K$ 为 $E'$ 的有限维子空间。对任意 $x \in E$ 与 $\varphi \in F$，
$$
\bigl(r_{KF}(q_K(x))\bigr)(\varphi) = q_K(x)(\varphi) = \varphi(x) = q_F(x)(\varphi),
$$
故 $r_{KF} \circ q_K = q_F$。固定 $y \in F^*$，记 $L := g_F(y)$，$R := \inf\{g_K(z) : z \in K^*,\; r_{KF} z = y\}$（空集下确界仍为 $+\infty$）。

- **证明 $L \le R$**：任取满足 $r_{KF} z = y$ 的 $z \in K^*$。对任意满足 $q_K(x) = z$ 的 $x \in E$，有 $q_F(x) = r_{KF}(q_K(x)) = r_{KF}(z) = y$，从而 $L = g_F(y) \le f(x)$。对所有满足 $q_K(x) = z$ 的 $x$ 取下确界得 $L \le g_K(z)$（若 $\{x : q_K x = z\} = \emptyset$，则 $g_K(z) = +\infty \ge L$ 同样成立）。再对所有满足 $r_{KF} z = y$ 的 $z$ 取下确界即得 $L \le R$（若无此 $z$，则 $R = +\infty \ge L$ 平凡成立）。
- **证明 $R \le L$**：任取满足 $q_F(x) = y$ 的 $x \in E$，令 $z := q_K(x) \in K^*$。则 $r_{KF}(z) = r_{KF}(q_K(x)) = q_F(x) = y$，从而
  $$
  R \le g_K(z) \le f(x).
  $$
  对所有满足 $q_F(x) = y$ 的 $x$ 取下确界得 $R \le L$（若 $\{x : q_F x = y\} = \emptyset$，则 $L = +\infty \ge R$ 平凡成立）。

综上，$g_F(y) = \inf_{r_{KF} z = y} g_K(z)$。

### 3. 证明是否需要纤维下确界取到

**不需要。**

- 非负性与至少一点有限仅直接利用下确界定义（$0$ 是下界；$g_F(q_F x_0) \le f(x_0)$）。
- 凸性证明中对任意 $\varepsilon > 0$ 取满足 $f(x_i) < t_i + \varepsilon$ 的近似点，最后令 $\varepsilon \to 0^+$，全程不要求存在使 $f(x_i) = g_F(y_i)$ 成立的极小点。
- 相容恒等式 $g_F(y) = \inf_{r_{KF} z = y} g_K(z)$ 仅使用下确界的泛性质与纤维分解 $r_{KF} \circ q_K = q_F$，无论 $g_F(y)$、$g_K(z)$ 还是关于 $z$ 的外层下确界是否取到，两侧均严格相等。

---

## S2　紧次水平集

先给出两个仅依赖共同设定（或一般拓扑）的预备事实，供 S2 及后续阶段复用。

**预备事实 A（仅用共同设定）**：对任意 $F, K \in \mathcal{F}$ 且 $F \subset K$，$F^*$ 在有限维拓扑下是 Hausdorff 空间，且映射 $q_F: E \to F^*$ 与 $r_{KF}: K^* \to F^*$ 均线性连续。

*证明*：若 $F = \{0\}$，则 $F^* = \{0\}$ 平凡为 Hausdorff 空间，$q_F$ 与 $r_{KF}$ 为常值零映射，故连续。若 $\dim F = n \ge 1$，取 $F$ 的一组基 $\varphi_1, \dots, \varphi_n \in E'$，定义线性同构 $\Phi: F^* \to \mathbb{R}^n$ 为 $\Phi(y) = \bigl(y(\varphi_1), \dots, y(\varphi_n)\bigr)$。有限维实向量空间上只有唯一的 Hausdorff 拓扑向量空间拓扑，故 $\Phi$ 为同胚，从而 $F^*$ 是 Hausdorff 空间。由于 $(\Phi \circ q_F)(x) = \bigl(\varphi_1(x), \dots, \varphi_n(x)\bigr)$ 的每个分量 $\varphi_i \in E'$ 连续，故 $\Phi \circ q_F$ 连续，从而 $q_F = \Phi^{-1} \circ (\Phi \circ q_F)$ 连续。同理，对 $r_{KF}: K^* \to F^*$，线性映射 $\Phi \circ r_{KF}: K^* \to \mathbb{R}^n$ 是有限维 Hausdorff 拓扑向量空间之间的线性映射，必连续（显式地，其第 $i$ 个分量 $z \mapsto z(\varphi_i)$ 是 $K^*$ 上坐标投影的线性组合），故 $r_{KF}$ 连续。$\square$

**预备事实 B（一般拓扑空间）**：设 $X$ 为拓扑空间，$u: X \to [-\infty, +\infty]$，则 $\mathrm{epi}_{\mathbb{R}}(u)$ 在 $X \times \mathbb{R}$ 中闭，当且仅当对每个 $c \in \mathbb{R}$，次水平集 $\{x \in X : u(x) \le c\}$ 在 $X$ 中闭。

*证明*：（$\Rightarrow$）对每个 $c \in \mathbb{R}$，连续映射 $x \mapsto (x, c)$ 下 $\mathrm{epi}_{\mathbb{R}}(u)$ 的原像正是 $\{u \le c\}$，故其为闭集。（$\Leftarrow$）若 $(x_0, t_0) \in (X \times \mathbb{R}) \setminus \mathrm{epi}_{\mathbb{R}}(u)$，则 $t_0 < u(x_0) \le +\infty$。取实数 $\alpha \in (t_0, u(x_0))$，则 $U := X \setminus \{u \le \alpha\}$ 为含 $x_0$ 的开集，$(-\infty, \alpha)$ 为含 $t_0$ 的开集，且对任意 $(x, t) \in U \times (-\infty, \alpha)$ 有 $t < \alpha < u(x)$，即 $(x, t) \notin \mathrm{epi}_{\mathbb{R}}(u)$。故 $\mathrm{epi}_{\mathbb{R}}(u)$ 的补集开，即 $\mathrm{epi}_{\mathbb{R}}(u)$ 闭。$\square$

现在启用 S2 的附加假设：$f$ 下半连续，且对每个 $c \in \mathbb{R}$，$\{f \le c\}$ 在 $E$ 中紧。

### 1. 当 $g_F(y) < +\infty$ 时纤维下确界取到

设 $y \in F^*$ 满足 $m := g_F(y) < +\infty$（由 S1 知 $m \in [0, +\infty)$）。对每个正整数 $n \ge 1$，令
$$
K_n := \bigl\{x \in E : f(x) \le m + \tfrac{1}{n}\bigr\} \cap q_F^{-1}(\{y\}).
$$
- **非空性**：因 $m = \inf\{f(x) : q_F x = y\} < m + \frac{1}{n}$，存在 $x_n \in E$ 使 $q_F(x_n) = y$ 且 $f(x_n) \le m + \frac{1}{n}$，故 $K_n \neq \emptyset$。
- **闭性与紧性**：由 $f$ 下半连续及预备事实 B，$\{f \le m + \frac{1}{n}\}$ 在 $E$ 中闭；由预备事实 A，$F^*$ 为 Hausdorff 空间且 $q_F$ 连续，故 $\{y\}$ 在 $F^*$ 中闭，从而 $q_F^{-1}(\{y\})$ 在 $E$ 中闭。因此每个 $K_n$ 是 $E$ 中闭集。特别地，$K_1$ 是紧集 $\{f \le m + 1\}$（S2 假设）的闭子集，故 $K_1$ 紧，且各 $K_n$ 为 $K_1$ 的闭子集。
- **有限交性质**：显然 $K_1 \supset K_2 \supset \cdots$，任取有限个 $K_{n_1}, \dots, K_{n_k}$，其交等于 $K_{\max_i n_i} \neq \emptyset$。

由紧空间的有限交性质，$\bigcap_{n=1}^{\infty} K_n \neq \emptyset$。任取 $x^* \in \bigcap_{n=1}^{\infty} K_n$，则 $q_F(x^*) = y$，且对所有 $n \ge 1$ 有 $f(x^*) \le m + \frac{1}{n}$，故 $f(x^*) \le m = g_F(y)$。另一方面，由 $q_F(x^*) = y$ 知 $g_F(y) \le f(x^*)$。因此 $f(x^*) = g_F(y)$，纤维下确界在 $x^*$ 处取到。

### 2. $g_F$ 下半连续

任取 $c \in \mathbb{R}$，我们断言：
$$
\{y \in F^* : g_F(y) \le c\} = q_F\bigl(\{x \in E : f(x) \le c\}\bigr).
$$
- （$\supset$）若 $y = q_F(x)$ 且 $f(x) \le c$，则 $g_F(y) \le f(x) \le c$。
- （$\subset$）若 $g_F(y) \le c$，则 $g_F(y) < +\infty$。由上面已证的纤维下确界取到性，存在 $x \in E$ 使 $q_F(x) = y$ 且 $f(x) = g_F(y) \le c$，故 $y \in q_F(\{f \le c\})$。（当 $c < 0$ 时两端皆为空集，等式亦成立。）

由 S2 假设，$\{f \le c\}$ 是 $E$ 中紧集；由预备事实 A，$q_F: E \to F^*$ 连续，故连续像 $q_F(\{f \le c\})$ 是 $F^*$ 中紧集；又因 $F^*$ 是 Hausdorff 空间，紧子集必为闭集。于是对每个 $c \in \mathbb{R}$，$\{g_F \le c\}$ 在 $F^*$ 中闭。由预备事实 B，$\mathrm{epi}_{\mathbb{R}}(g_F)$ 在 $F^* \times \mathbb{R}$ 中闭，即 $g_F$ 下半连续。

---

## S3　兼容成本记录的实现

在 S2 条件下，记 $C := \{x \in E : f(x) \le c\}$。因 $c \in \mathbb{R}$ 有限，由 S2 假设，$C$ 是 $E$ 中的紧集。

对每个 $F \in \mathcal{F}$，定义集合
$$
A_F := C \cap q_F^{-1}(\{y_F\}) = \{x \in E : f(x) \le c \text{ 且 } q_F(x) = y_F\}.
$$
我们验证如下性质：
1. **$A_F$ 为 $C$ 中的闭集**：由预备事实 A（仅用共同设定），$F^*$ 是 Hausdorff 空间且 $q_F: E \to F^*$ 连续，故 $\{y_F\}$ 在 $F^*$ 中闭，$q_F^{-1}(\{y_F\})$ 在 $E$ 中闭，从而 $A_F$ 是 $C$ 的闭子集。
2. **$A_F$ 非空**：已知 $g_F(y_F) \le c < +\infty$，且当前处于 S2 条件下，故由 S2（纤维下确界取到）存在 $x_F \in E$ 满足 $q_F(x_F) = y_F$ 且 $f(x_F) = g_F(y_F) \le c$，于是 $x_F \in A_F$。
3. **有限交性质**：任取有限个 $F_1, \dots, F_m \in \mathcal{F}$，令 $K := F_1 + \dots + F_m \subset E'$，则 $K \in \mathcal{F}$ 且 $F_i \subset K$（$i = 1, \dots, m$）。对任意 $x \in A_K$，有 $f(x) \le c$ 且 $q_K(x) = y_K$；结合 S1 中 $r_{KF_i} \circ q_K = q_{F_i}$（仅用共同设定）以及给定相容性 $r_{KF_i}(y_K) = y_{F_i}$，得
   $$
   q_{F_i}(x) = r_{KF_i}\bigl(q_K(x)\bigr) = r_{KF_i}(y_K) = y_{F_i} \qquad (i = 1, \dots, m).
   $$
   故 $A_K \subset \bigcap_{i=1}^m A_{F_i}$。因为 $A_K \neq \emptyset$，所以 $\bigcap_{i=1}^m A_{F_i} \neq \emptyset$。

### 存在性与构造

由于 $C$ 紧且 $\{A_F\}_{F \in \mathcal{F}}$ 是 $C$ 中具有有限交性质的闭集族，由紧空间的有限交性质得
$$
\bigcap_{F \in \mathcal{F}} A_F \neq \emptyset.
$$
任取 $x \in \bigcap_{F \in \mathcal{F}} A_F$，则由 $A_F$ 的定义直接有 $f(x) \le c$，且对所有 $F \in \mathcal{F}$ 均有 $q_F(x) = y_F$。

### 唯一性

设 $x_1, x_2 \in E$ 均满足 $q_F(x_1) = y_F = q_F(x_2)$（对所有 $F \in \mathcal{F}$）。对任意 $\varphi \in E'$，取有限维子空间 $F = \mathrm{span}\{\varphi\} \in \mathcal{F}$，有
$$
\varphi(x_1) = q_F(x_1)(\varphi) = y_F(\varphi) = q_F(x_2)(\varphi) = \varphi(x_2).
$$
若 $x_1 \neq x_2$，则在实 Hausdorff 局部凸空间 $E$ 中，$\{x_1\}$ 是非空紧凸集，$\{x_2\}$ 是非空闭凸集（因 $E$ 为 Hausdorff 空间）且 $\{x_1\} \cap \{x_2\} = \emptyset$。由 Hahn–Banach 几何严格分离定理，存在 $\varphi \in E'$ 使 $\varphi(x_1) \neq \varphi(x_2)$，矛盾。因此 $x_1 = x_2$。

综上，$\bigcap_{F \in \mathcal{F}} A_F = \{x\}$ 是单点集，其唯一元素 $x$ 即为所构造的满足 $q_F x = y_F$（$\forall F \in \mathcal{F}$）且 $f(x) \le c$ 的唯一点。

---

## S4　一般成本的恢复

**结论：能（成立）。** 本阶段仅使用共同设定（不再使用 S2 的紧性与 $f$ 下半连续假设）。

### 1. 两个基础引理

**引理 4.1（序关系与实高度上图）**：设 $X$ 为集合，$u, v: X \to [-\infty, +\infty]$，则
$$
u \le v \iff \mathrm{epi}_{\mathbb{R}}(v) \subset \mathrm{epi}_{\mathbb{R}}(u).
$$
*证明*：（$\Rightarrow$）若 $u \le v$ 且 $(x, t) \in \mathrm{epi}_{\mathbb{R}}(v)$，则 $t \in \mathbb{R}$ 且 $u(x) \le v(x) \le t$，故 $(x, t) \in \mathrm{epi}_{\mathbb{R}}(u)$。（$\Leftarrow$）设 $\mathrm{epi}_{\mathbb{R}}(v) \subset \mathrm{epi}_{\mathbb{R}}(u)$ 并固定 $x \in X$。若 $v(x) = +\infty$，显然 $u(x) \le v(x)$；若 $v(x) \in \mathbb{R}$，则 $(x, v(x)) \in \mathrm{epi}_{\mathbb{R}}(v) \subset \mathrm{epi}_{\mathbb{R}}(u)$，故 $u(x) \le v(x)$；若 $v(x) = -\infty$，则对所有 $t \in \mathbb{R}$ 有 $(x, t) \in \mathrm{epi}_{\mathbb{R}}(v) \subset \mathrm{epi}_{\mathbb{R}}(u)$，即 $u(x) \le t$ 对所有 $t \in \mathbb{R}$ 成立，故 $u(x) = -\infty = v(x)$。$\square$

**引理 4.2（非负凸函数的下半连续包络）**：设 $X$ 为实拓扑向量空间，$u: X \to [0, +\infty]$ 为凸函数。记 $C := \overline{\mathrm{epi}_{\mathbb{R}}(u)}$（在 $X \times \mathbb{R}$ 中取闭包），并定义
$$
\hat{u}(x) := \inf\{t \in \mathbb{R} : (x, t) \in C\} \qquad (\inf \emptyset = +\infty).
$$
则：
1. $\hat{u}$ 取值于 $[0, +\infty]$，且 $\mathrm{epi}_{\mathbb{R}}(\hat{u}) = C = \overline{\mathrm{epi}_{\mathbb{R}}(u)}$；
2. $\hat{u}$ 下半连续、凸，且 $\hat{u} \le u$；
3. 对任意下半连续函数 $h: X \to [-\infty, +\infty]$（即使同时取 $-\infty$ 与 $+\infty$），若 $h \le u$，则 $h \le \hat{u}$；
4. 具有显式逐点表达式 $\hat{u}(x) = \sup_{U \in \mathcal{N}(x)} \inf_{w \in U} u(w)$，其中 $\mathcal{N}(x)$ 为 $x$ 在 $X$ 中的邻域族。

*证明*：
- （1）因 $u \ge 0$，有 $\mathrm{epi}_{\mathbb{R}}(u) \subset X \times [0, +\infty)$，后者在 $X \times \mathbb{R}$ 中闭，故 $C \subset X \times [0, +\infty)$，从而 $\hat{u}(x) \in [0, +\infty]$。其次，对任意 $s \ge 0$，平移 $T_s(x, t) = (x, t+s)$ 是 $X \times \mathbb{R}$ 上的连续映射且满足 $T_s(\mathrm{epi}_{\mathbb{R}}(u)) \subset \mathrm{epi}_{\mathbb{R}}(u) \subset C$，故 $\mathrm{epi}_{\mathbb{R}}(u) \subset T_s^{-1}(C)$，取闭包得 $C \subset T_s^{-1}(C)$，即 $(x, t) \in C \implies (x, t+s) \in C$。现验证 $\mathrm{epi}_{\mathbb{R}}(\hat{u}) = C$：若 $(x, t) \in C$，则 $t \in \mathbb{R}$ 且 $\hat{u}(x) \le t$，即 $(x, t) \in \mathrm{epi}_{\mathbb{R}}(\hat{u})$；反之若 $(x, t) \in \mathrm{epi}_{\mathbb{R}}(\hat{u})$，则对每个 $n \ge 1$ 存在 $t_n < t + \frac{1}{n}$ 使 $(x, t_n) \in C$，由 $C$ 的向上封闭性得 $(x, t + \frac{1}{n}) \in C$，令 $n \to \infty$ 并利用 $C$ 闭即得 $(x, t) \in C$。
- （2）$C$ 显然闭。对任意 $\lambda \in [0, 1]$，连续映射 $\Phi_\lambda(p, q) = \lambda p + (1-\lambda)q$ 将凸集 $\mathrm{epi}_{\mathbb{R}}(u)$ 的乘积 $\mathrm{epi}_{\mathbb{R}}(u) \times \mathrm{epi}_{\mathbb{R}}(u)$ 映入 $\mathrm{epi}_{\mathbb{R}}(u) \subset C$，故 $\Phi_\lambda(C \times C) = \Phi_\lambda\bigl(\overline{\mathrm{epi}_{\mathbb{R}}(u) \times \mathrm{epi}_{\mathbb{R}}(u)}\bigr) \subset C$，即 $C$ 凸。因此 $\hat{u}$ 下半连续且凸。由 $\mathrm{epi}_{\mathbb{R}}(u) \subset C = \mathrm{epi}_{\mathbb{R}}(\hat{u})$ 与引理 4.1 得 $\hat{u} \le u$。
- （3）若 $h: X \to [-\infty, +\infty]$ 下半连续且 $h \le u$，则由引理 4.1 得 $\mathrm{epi}_{\mathbb{R}}(u) \subset \mathrm{epi}_{\mathbb{R}}(h)$。因 $\mathrm{epi}_{\mathbb{R}}(h)$ 闭，取闭包得 $\mathrm{epi}_{\mathbb{R}}(\hat{u}) = \overline{\mathrm{epi}_{\mathbb{R}}(u)} \subset \mathrm{epi}_{\mathbb{R}}(h)$，再由引理 4.1 即得 $h \le \hat{u}$。
- （4）记 $L(x) := \sup_{U \in \mathcal{N}(x)} \inf_{w \in U} u(w) \in [0, +\infty]$。固定 $x \in X$ 与 $t \in \mathbb{R}$：若 $\hat{u}(x) \le t$，则 $(x, t) \in \overline{\mathrm{epi}_{\mathbb{R}}(u)}$，故对任意 $U \in \mathcal{N}(x)$ 与 $\varepsilon > 0$，存在 $(w, s) \in \bigl(U \times (t-\varepsilon, t+\varepsilon)\bigr) \cap \mathrm{epi}_{\mathbb{R}}(u)$，从而 $\inf_{w' \in U} u(w') \le u(w) \le s < t + \varepsilon$；先令 $\varepsilon \to 0^+$ 再对 $U$ 取上确界得 $L(x) \le t$。反之若 $L(x) \le t$，对 $(x, t)$ 的任意基本邻域 $U \times (t-\varepsilon, t+\varepsilon)$，因 $\inf_{w \in U} u(w) \le L(x) \le t < t + \frac{\varepsilon}{2}$，存在 $w \in U$ 使 $u(w) < t + \frac{\varepsilon}{2}$；取 $s = t + \frac{\varepsilon}{2} \in (t-\varepsilon, t+\varepsilon)$，则 $(w, s) \in \bigl(U \times (t-\varepsilon, t+\varepsilon)\bigr) \cap \mathrm{epi}_{\mathbb{R}}(u)$，故 $(x, t) \in \overline{\mathrm{epi}_{\mathbb{R}}(u)} = \mathrm{epi}_{\mathbb{R}}(\hat{u})$，即 $\hat{u}(x) \le t$。既然 $\hat{u}(x)$ 与 $L(x)$ 具有完全相同的实上界集合，必有 $\hat{u}(x) = L(x)$。$\square$

### 2. $G$ 的构造与性质验证

对每个 $F \in \mathcal{F}$，由 S1（仅依赖共同设定），$g_F: F^* \to [0, +\infty]$ 非负且凸。在有限维实拓扑向量空间 $F^*$ 上对 $g_F$ 施加引理 4.2，仅由 $g_F$ 构造其下半连续包络
$$
\hat{g}_F(y) := \inf\bigl\{t \in \mathbb{R} : (y, t) \in \overline{\mathrm{epi}_{\mathbb{R}}(g_F)}\bigr\} = \sup_{U \in \mathcal{N}_{F^*}(y)} \inf_{w \in U} g_F(w) \qquad (y \in F^*).
$$
进而在 $E$ 上定义
$$
G_F(x) := \hat{g}_F\bigl(q_F(x)\bigr), \qquad G(x) := \sup_{F \in \mathcal{F}} G_F(x) = \sup_{F \in \mathcal{F}} \hat{g}_F\bigl(q_F(x)\bigr) \qquad (x \in E).
$$
显然 $G$ 仅由全部 $\{g_F\}_{F \in \mathcal{F}}$ 构造。下面逐项验证所需性质：

1. **值域与上界 $G \le f$**：对每个 $F \in \mathcal{F}$，由引理 4.2 知 $\hat{g}_F$ 取值于 $[0, +\infty]$ 且 $\hat{g}_F \le g_F$，故对所有 $x \in E$，
   $$
   0 \le G_F(x) = \hat{g}_F(q_F x) \le g_F(q_F x) \le f(x).
   $$
   对 $F \in \mathcal{F}$ 取上确界得 $G: E \to [0, +\infty]$ 且 $G \le f$。

2. **下半连续性与凸性**：对每个 $F \in \mathcal{F}$，由预备事实 A（仅用共同设定），$q_F: E \to F^*$ 线性连续，从而 $q_F \times \mathrm{id}_{\mathbb{R}}: E \times \mathbb{R} \to F^* \times \mathbb{R}$ 线性连续。因为
   $$
   \mathrm{epi}_{\mathbb{R}}(G_F) = \{(x, t) \in E \times \mathbb{R} : \hat{g}_F(q_F x) \le t\} = (q_F \times \mathrm{id}_{\mathbb{R}})^{-1}\bigl(\mathrm{epi}_{\mathbb{R}}(\hat{g}_F)\bigr),
   $$
   而 $\mathrm{epi}_{\mathbb{R}}(\hat{g}_F)$ 在 $F^* \times \mathbb{R}$ 中闭且凸（引理 4.2），故 $\mathrm{epi}_{\mathbb{R}}(G_F)$ 在 $E \times \mathbb{R}$ 中闭且凸。进而
   $$
   \mathrm{epi}_{\mathbb{R}}(G) = \Bigl\{(x, t) \in E \times \mathbb{R} : \sup_{F \in \mathcal{F}} G_F(x) \le t\Bigr\} = \bigcap_{F \in \mathcal{F}} \mathrm{epi}_{\mathbb{R}}(G_F).
   $$
   任意多个闭凸集的交仍是闭凸集，因此 $\mathrm{epi}_{\mathbb{R}}(G)$ 闭且凸，即 $G$ 下半连续且凸。

3. **核心等式 $\mathrm{epi}_{\mathbb{R}}(G) = \overline{\mathrm{epi}_{\mathbb{R}}(f)}$ 及最大性（对允许同时取 $-\infty$ 与 $+\infty$ 的竞争函数 $h$）**：
   - 先证 $\overline{\mathrm{epi}_{\mathbb{R}}(f)} \subset \mathrm{epi}_{\mathbb{R}}(G)$：由 $G \le f$ 与引理 4.1 得 $\mathrm{epi}_{\mathbb{R}}(f) \subset \mathrm{epi}_{\mathbb{R}}(G)$；因 $\mathrm{epi}_{\mathbb{R}}(G)$ 在 $E \times \mathbb{R}$ 中闭，取闭包即得 $\overline{\mathrm{epi}_{\mathbb{R}}(f)} \subset \mathrm{epi}_{\mathbb{R}}(G)$。
   - 再证 $\mathrm{epi}_{\mathbb{R}}(G) \subset \overline{\mathrm{epi}_{\mathbb{R}}(f)}$：任取 $(x_0, t_0) \in (E \times \mathbb{R}) \setminus \overline{\mathrm{epi}_{\mathbb{R}}(f)}$，需证 $G(x_0) > t_0$（即 $(x_0, t_0) \notin \mathrm{epi}_{\mathbb{R}}(G)$）。
     核验 Hahn–Banach 几何严格分离定理的条件：
     - $E$ 与 $\mathbb{R}$ 均为实 Hausdorff 局部凸空间，故乘积空间 $E \times \mathbb{R}$ 也是实 Hausdorff 局部凸空间，其连续对偶为 $(E \times \mathbb{R})' \cong E' \times \mathbb{R}$（任何 $\Lambda \in (E \times \mathbb{R})'$ 唯一表示为 $\Lambda(x, t) = \varphi(x) + \alpha t$，其中 $\varphi(x) = \Lambda(x, 0) \in E'$，$\alpha = \Lambda(0, 1) \in \mathbb{R}$）；
     - 集合 $A := \{(x_0, t_0)\}$ 是非空紧凸集；
     - 集合 $B := \overline{\mathrm{epi}_{\mathbb{R}}(f)}$ 闭，因 $f$ 至少在一点 $x_1 \in E$ 有限而 $(x_1, f(x_1)) \in \mathrm{epi}_{\mathbb{R}}(f) \subset B$ 故非空，且因 $\mathrm{epi}_{\mathbb{R}}(f)$ 凸故其闭包 $B$ 凸（同引理 4.2 证明）；
     - $A \cap B = \emptyset$。

     由 Hahn–Banach 几何严格分离定理，存在 $\varphi \in E'$，$\alpha, \gamma \in \mathbb{R}$ 及 $\delta > 0$，使得对一切 $(x, t) \in \mathrm{epi}_{\mathbb{R}}(f)$ 有
     $$
     \varphi(x_0) + \alpha t_0 \le \gamma - \delta < \gamma \le \varphi(x) + \alpha t.
     $$
     取 $x = x_1$ 并让 $t \ge f(x_1)$ 趋于 $+\infty$，得 $\alpha \ge 0$。分两种情形讨论：

     - **情形 1：$\alpha > 0$。** 令 $\psi := -\frac{1}{\alpha}\varphi \in E'$，$b := \frac{\gamma}{\alpha} \in \mathbb{R}$，$\eta := \frac{\delta}{\alpha} > 0$。将上式除以 $\alpha$ 得
       $$
       t_0 - \psi(x_0) \le b - \eta < b \le t - \psi(x) \qquad \forall (x, t) \in \mathrm{epi}_{\mathbb{R}}(f).
       $$
       取有限维子空间 $F := \mathrm{span}\{\psi\} \in \mathcal{F}$（$\dim F \le 1$），并在 $F^*$ 上定义仿射函数 $a(y) := y(\psi) + b$。因 $y \mapsto y(\psi)$ 是有限维 Hausdorff 拓扑向量空间 $F^*$ 上的线性泛函，故 $a: F^* \to \mathbb{R}$ 连续（从而下半连续）。对任意 $y \in F^*$ 与满足 $q_F(x) = y$ 的 $x \in E$：若 $f(x) < +\infty$，则 $(x, f(x)) \in \mathrm{epi}_{\mathbb{R}}(f)$，故 $f(x) \ge \psi(x) + b = q_F(x)(\psi) + b = y(\psi) + b = a(y)$；若 $f(x) = +\infty$，不等式平凡成立。对所有满足 $q_F(x) = y$ 的 $x$ 取下确界得 $a(y) \le g_F(y)$（对所有 $y \in F^*$）。由引理 4.2（3）得 $a \le \hat{g}_F$，从而
       $$
       G(x_0) \ge \hat{g}_F\bigl(q_F(x_0)\bigr) \ge a\bigl(q_F(x_0)\bigr) = \psi(x_0) + b \ge t_0 + \eta > t_0.
       $$

     - **情形 2：$\alpha = 0$。** 此时对所有 $x \in \mathrm{dom}(f) := \{x \in E : f(x) < +\infty\}$ 有
       $$
       \varphi(x_0) \le \gamma - \delta < \gamma \le \varphi(x).
       $$
       取有限维子空间 $F := \mathrm{span}\{\varphi\} \in \mathcal{F}$，并考虑集合 $U := \{y \in F^* : y(\varphi) < \gamma\} \subset F^*$。因 $y \mapsto y(\varphi)$ 在 $F^*$ 上连续，故 $U$ 为 $F^*$ 中开集，且 $q_F(x_0)(\varphi) = \varphi(x_0) \le \gamma - \delta < \gamma$，即 $q_F(x_0) \in U$。对任意 $y \in U$ 与满足 $q_F(x) = y$ 的 $x \in E$，有 $\varphi(x) = y(\varphi) < \gamma$，从而 $x \notin \mathrm{dom}(f)$，即 $f(x) = +\infty$；故 $g_F(y) = +\infty$ 对一切 $y \in U$ 成立。于是 $(U \times \mathbb{R}) \cap \mathrm{epi}_{\mathbb{R}}(g_F) = \emptyset$。因为 $U \times \mathbb{R}$ 是包含 $\{q_F(x_0)\} \times \mathbb{R}$ 的开集，所以对任意 $t \in \mathbb{R}$ 有 $(q_F(x_0), t) \notin \overline{\mathrm{epi}_{\mathbb{R}}(g_F)} = \mathrm{epi}_{\mathbb{R}}(\hat{g}_F)$，即 $\hat{g}_F(q_F(x_0)) = +\infty$。因此
       $$
       G(x_0) \ge \hat{g}_F\bigl(q_F(x_0)\bigr) = +\infty > t_0.
       $$

     两种情形皆推出 $(x_0, t_0) \notin \mathrm{epi}_{\mathbb{R}}(G)$。综上，$\mathrm{epi}_{\mathbb{R}}(G) = \overline{\mathrm{epi}_{\mathbb{R}}(f)}$，即 $G = \hat{f}$。

   - **竞争函数比较**：任取下半连续、凸的 $h: E \to [-\infty, +\infty]$（允许同时取 $-\infty$ 与 $+\infty$），若 $h \le f$，则由引理 4.1 得 $\mathrm{epi}_{\mathbb{R}}(f) \subset \mathrm{epi}_{\mathbb{R}}(h)$；由于 $\mathrm{epi}_{\mathbb{R}}(h)$ 在 $E \times \mathbb{R}$ 中闭，取闭包得
     $$
     \mathrm{epi}_{\mathbb{R}}(G) = \overline{\mathrm{epi}_{\mathbb{R}}(f)} \subset \mathrm{epi}_{\mathbb{R}}(h).
     $$
     再由引理 4.1 即得 $h \le G$。（注：上述论证同时表明满足题设全部要求的 $G$ 是唯一的，即 $G = \hat{f}$。）

### 3. 扩大观测空间时的关系

设 $F, K \in \mathcal{F}$ 满足 $F \subset K$（观测空间由 $F$ 扩大到 $K$）：

1. **有限维记录闭包的单调比较**：考虑 $K^*$ 上的函数 $\hat{g}_F \circ r_{KF}$。由引理 4.2，$\hat{g}_F$ 下半连续且凸；由预备事实 A（仅用共同设定），$r_{KF}: K^* \to F^*$ 线性连续，故 $\mathrm{epi}_{\mathbb{R}}(\hat{g}_F \circ r_{KF}) = (r_{KF} \times \mathrm{id}_{\mathbb{R}})^{-1}(\mathrm{epi}_{\mathbb{R}}(\hat{g}_F))$ 闭且凸，即 $\hat{g}_F \circ r_{KF}$ 在 $K^*$ 上下半连续且凸。另一方面，由 $\hat{g}_F \le g_F$ 与 S1 的相容公式得，对所有 $z \in K^*$，
   $$
   \hat{g}_F\bigl(r_{KF}(z)\bigr) \le g_F\bigl(r_{KF}(z)\bigr) = \inf_{r_{KF} w = r_{KF} z} g_K(w) \le g_K(z).
   $$
   由引理 4.2（3）应用于 $g_K$ 即得
   $$
   \hat{g}_F\bigl(r_{KF}(z)\bigr) \le \hat{g}_K(z) \qquad \forall z \in K^*.
   $$
   对所有满足 $r_{KF} z = y$ 的 $z \in K^*$ 取下确界，并结合 $\hat{g}_K \le g_K$ 与 S1，进一步得到
   $$
   \hat{g}_F(y) \le \inf_{r_{KF} z = y} \hat{g}_K(z) \le \inf_{r_{KF} z = y} g_K(z) = g_F(y) \qquad \forall y \in F^*.
   $$

2. **$E$ 上恢复逼近的单调递增性与定向极限**：将 $\hat{g}_F(r_{KF}(z)) \le \hat{g}_K(z)$ 代入 $z = q_K(x)$ 并利用 $r_{KF} \circ q_K = q_F$（S1），得
   $$
   G_F(x) = \hat{g}_F\bigl(q_F(x)\bigr) \le \hat{g}_K\bigl(q_K(x)\bigr) = G_K(x) \le G(x) \le f(x) \qquad \forall x \in E,
   $$
   等价地，在实高度上图层面有反向包含链
   $$
   \mathrm{epi}_{\mathbb{R}}(f) \subset \mathrm{epi}_{\mathbb{R}}(G) \subset \mathrm{epi}_{\mathbb{R}}(G_K) \subset \mathrm{epi}_{\mathbb{R}}(G_F).
   $$
   此外，$(\mathcal{F}, \subset)$ 是向上定向集（对任意 $F_1, F_2 \in \mathcal{F}$，取 $K = F_1 + F_2 \in \mathcal{F}$，则 $F_1, F_2 \subset K$ 且 $G_K \ge \max(G_{F_1}, G_{F_2})$），因此 $\{G_F\}_{F \in \mathcal{F}}$ 是单调非减网，并逐点单调递增收敛到 $G$：
   $$
   G(x) = \sup_{F \in \mathcal{F}} G_F(x) = \lim_{F \uparrow} G_F(x) \qquad \forall x \in E.
   $$

---

## S5　闭成本的有限投影

**结论：否（不一定下半连续）。**

### 反例构造与完整核验

取 $E = \mathbb{R}^2$（标准欧氏拓扑，为实 Hausdorff 局部凸空间），令
$$
S := \{(x_1, x_2) \in \mathbb{R}^2 : x_1 > 0,\; x_1 x_2 \ge 1\},
$$
定义 $f: \mathbb{R}^2 \to [0, +\infty]$ 为 $S$ 的示性函数：
$$
f(x_1, x_2) := \begin{cases} 0, & (x_1, x_2) \in S, \\ +\infty, & (x_1, x_2) \notin S. \end{cases}
$$

1. **核验 $f$ 满足题设全部条件**：
   - **非负且至少一点有限**：显然 $f$ 取值于 $\{0, +\infty\} \subset [0, +\infty]$，且 $(1, 1) \in S$，故 $f(1, 1) = 0 < +\infty$。
   - **$S$ 是闭集**：注意到若 $x_1 \ge 0$ 且 $x_1 x_2 \ge 1$，则必有 $x_1 > 0$ 且 $x_2 \ge 1/x_1 > 0$，因此
     $$
     S = \{(x_1, x_2) \in \mathbb{R}^2 : x_1 \ge 0\} \cap \{(x_1, x_2) \in \mathbb{R}^2 : x_2 \ge 0\} \cap \{(x_1, x_2) \in \mathbb{R}^2 : x_1 x_2 \ge 1\}.
     $$
     等式右侧为三个连续函数下闭区间 $[0, +\infty)$ 或 $[1, +\infty)$ 原像的交，故 $S$ 在 $\mathbb{R}^2$ 中闭。
   - **$S$ 是凸集**：任取 $(x_1, x_2), (u_1, u_2) \in S$ 与 $\lambda \in [0, 1]$。于是 $x_1, x_2, u_1, u_2 > 0$，$x_1 x_2 \ge 1$，$u_1 u_2 \ge 1$。显然 $\lambda x_1 + (1-\lambda)u_1 > 0$。由算术-几何平均不等式 $x_1 u_2 + u_1 x_2 \ge 2\sqrt{(x_1 x_2)(u_1 u_2)} \ge 2$，得
     $$
     \bigl(\lambda x_1 + (1-\lambda)u_1\bigr)\bigl(\lambda x_2 + (1-\lambda)u_2\bigr)
     = \lambda^2 x_1 x_2 + (1-\lambda)^2 u_1 u_2 + \lambda(1-\lambda)(x_1 u_2 + u_1 x_2)
     \ge \lambda^2 + (1-\lambda)^2 + 2\lambda(1-\lambda) = 1.
     $$
     故 $\lambda(x_1, x_2) + (1-\lambda)(u_1, u_2) \in S$，$S$ 凸。
   - **$f$ 下半连续且凸**：直接计算得
     $$
     \mathrm{epi}_{\mathbb{R}}(f) = \{(x_1, x_2, t) \in \mathbb{R}^2 \times \mathbb{R} : (x_1, x_2) \in S,\; t \ge 0\} = S \times [0, +\infty).
     $$
     因 $S$ 与 $[0, +\infty)$ 均为闭凸集，其乘积 $S \times [0, +\infty)$ 在 $\mathbb{R}^2 \times \mathbb{R}$ 中闭且凸。故 $f$ 下半连续且凸。

2. **选取有限维子空间 $F$ 并计算 $g_F$**：
   取连续线性泛函 $\varphi \in (\mathbb{R}^2)'$ 为第一坐标投影 $\varphi(x_1, x_2) = x_1$，并取一维子空间 $F := \mathrm{span}\{\varphi\} \subset (\mathbb{R}^2)'$。
   映射 $\Phi: F^* \to \mathbb{R}$，$\Phi(y) = y(\varphi)$ 是有限维 Hausdorff 拓扑向量空间之间的线性同构，从而是同胚。对每个 $t \in \mathbb{R}$，记 $y_t := \Phi^{-1}(t) \in F^*$（即满足 $y_t(\varphi) = t$ 的唯一元素）。对 $(x_1, x_2) \in \mathbb{R}^2$，条件 $q_F(x_1, x_2) = y_t$ 等价于 $x_1 = t$，因此
   $$
   g_F(y_t) = \inf\{f(t, x_2) : x_2 \in \mathbb{R}\}.
   $$
   - 若 $t > 0$，取 $x_2 = 1/t$，则 $(t, 1/t) \in S$，故 $f(t, 1/t) = 0$；结合 $f \ge 0$ 得 $g_F(y_t) = 0$。
   - 若 $t \le 0$，则对一切 $x_2 \in \mathbb{R}$ 均有 $(t, x_2) \notin S$，故 $f(t, x_2) = +\infty$，从而 $g_F(y_t) = +\infty$。

   即
   $$
   g_F(y_t) = \begin{cases} 0, & t > 0, \\ +\infty, & t \le 0. \end{cases}
   $$

3. **核验 $g_F$ 非下半连续**：
   对每个正整数 $n \ge 1$，有 $g_F(y_{1/n}) = 0$，故 $(y_{1/n}, 0) \in \mathrm{epi}_{\mathbb{R}}(g_F)$。由于 $\Phi^{-1}: \mathbb{R} \to F^*$ 连续，当 $n \to \infty$ 时有 $(y_{1/n}, 0) \to (y_0, 0)$ 于 $F^* \times \mathbb{R}$。然而 $g_F(y_0) = +\infty > 0$，故 $(y_0, 0) \notin \mathrm{epi}_{\mathbb{R}}(g_F)$。因此 $\mathrm{epi}_{\mathbb{R}}(g_F)$ 在 $F^* \times \mathbb{R}$ 中不闭，即 $g_F$ 不是下半连续的。

---

## S6　恢复与投影的精确关系

在共同设定下，先明确记号 $\bar{u}$ 与 S4 中 $\hat{u}$ 的一致关系：对任意实拓扑向量空间 $X$（此处取 $X = E$ 或 $X = F^*$）上的非负凸函数 $u: X \to [0, +\infty]$，由 S4 引理 4.2，$\hat{u}: X \to [0, +\infty]$ 下半连续、凸、满足 $\hat{u} \le u$，且控制任意下半连续（特别地，下半连续凸）下界 $h \le u$；因此最大下半连续凸下界 $\bar{u}$ 存在唯一，且
$$
\bar{u} = \hat{u}, \qquad \mathrm{epi}_{\mathbb{R}}(\bar{u}) = \overline{\mathrm{epi}_{\mathbb{R}}(u)}.
$$
特别地，由 S4 的构造与性质，$G = \bar{f}$，且各 $\hat{g}_F = \overline{g_F}$。

### 1. 证明 $G = f$ 当且仅当 $f$ 下半连续

- **（$\Rightarrow$）**：若 $G = f$，由 S4 知 $G$ 下半连续，故 $f$ 下半连续。
- **（$\Leftarrow$）**：若 $f$ 下半连续，结合共同设定中 $f$ 凸且平凡满足 $f \le f$，将 S4 的最大性应用于竞争函数 $h = f$，得 $f \le G$。另一方面由 S4 有 $G \le f$，故 $G = f$。

（等价地，由 $\mathrm{epi}_{\mathbb{R}}(G) = \overline{\mathrm{epi}_{\mathbb{R}}(f)}$ 与引理 4.1：$G = f \iff \overline{\mathrm{epi}_{\mathbb{R}}(f)} = \mathrm{epi}_{\mathbb{R}}(f) \iff \mathrm{epi}_{\mathbb{R}}(f)$ 闭 $\iff f$ 下半连续。）

### 2. 证明 $\overline{g_F} = \overline{y \mapsto \inf_{r_{KF} z = y} \overline{g_K}(z)}$

设 $F, K \in \mathcal{F}$ 且 $F \subset K$。记函数 $\psi: F^* \to [0, +\infty]$ 为
$$
\psi(y) := \inf_{r_{KF} z = y} \overline{g_K}(z) \qquad (y \in F^*).
$$

- **先验证 $\psi$ 非负且凸（从而 $\overline{\psi}$ 按题设记号有定义）**：
  - 非负性：因 $g_K \ge 0$ 且凸（S1），由引理 4.2 知 $\overline{g_K}: K^* \to [0, +\infty]$ 非负且凸，故对所有 $y \in F^*$ 有 $\psi(y) \in [0, +\infty]$。
  - 凸性：任取 $(y_1, t_1), (y_2, t_2) \in \mathrm{epi}_{\mathbb{R}}(\psi)$ 与 $\lambda \in [0, 1]$。对任意 $\varepsilon > 0$，由 $\psi(y_i) \le t_i < t_i + \varepsilon$，存在 $z_i \in K^*$ 使 $r_{KF}(z_i) = y_i$ 且 $\overline{g_K}(z_i) < t_i + \varepsilon$，即 $(z_i, t_i + \varepsilon) \in \mathrm{epi}_{\mathbb{R}}(\overline{g_K})$（$i = 1, 2$）。由 $\overline{g_K}$ 凸性得
    $$
    \bigl(\lambda z_1 + (1-\lambda)z_2,\; \lambda t_1 + (1-\lambda)t_2 + \varepsilon\bigr) \in \mathrm{epi}_{\mathbb{R}}(\overline{g_K}).
    $$
    又因 $r_{KF}$ 线性，有 $r_{KF}(\lambda z_1 + (1-\lambda)z_2) = \lambda y_1 + (1-\lambda)y_2$，故
    $$
    \psi\bigl(\lambda y_1 + (1-\lambda)y_2\bigr) \le \overline{g_K}\bigl(\lambda z_1 + (1-\lambda)z_2\bigr) \le \lambda t_1 + (1-\lambda)t_2 + \varepsilon.
    $$
    令 $\varepsilon \to 0^+$ 得 $\psi(\lambda y_1 + (1-\lambda)y_2) \le \lambda t_1 + (1-\lambda)t_2$，故 $\mathrm{epi}_{\mathbb{R}}(\psi)$ 凸，即 $\psi$ 凸。

- **夹逼不等式与等式证明**：
  在 S4（扩大观测空间的关系，仅用共同设定）中已证得：
  $$
  \overline{g_F}(y) \le \inf_{r_{KF} z = y} \overline{g_K}(z) = \psi(y) \le \inf_{r_{KF} z = y} g_K(z) = g_F(y) \qquad \forall y \in F^*.
  $$
  由此立即推得两方向不等式：
  1. 因为 $\overline{g_F}$ 下半连续、凸且 $\overline{g_F} \le \psi$，按 $\overline{\psi}$ 为 $\psi$ 的最大下半连续凸下界，有 $\overline{g_F} \le \overline{\psi}$。
  2. 因为 $\overline{\psi}$ 下半连续、凸且 $\overline{\psi} \le \psi \le g_F$，按 $\overline{g_F}$ 为 $g_F$ 的最大下半连续凸下界，有 $\overline{\psi} \le \overline{g_F}$。

  综上，$\overline{g_F} = \overline{\psi}$，即
  $$
  \overline{g_F} = \overline{y \mapsto \inf_{r_{KF} z = y} \overline{g_K}(z)}.
  $$

### 3. 判断右式的最外层 $\bar{}$ 能否总省去

**结论：否（不能总省去）。**

**完整核验反例**：取 S5 中的 $E = \mathbb{R}^2$ 与函数
$$
f(x_1, x_2) = \begin{cases} 0, & x_1 > 0 \text{ 且 } x_1 x_2 \ge 1, \\ +\infty, & \text{其他}. \end{cases}
$$
由 S5 已核验，$f: \mathbb{R}^2 \to [0, +\infty]$ 下半连续、凸且 $f(1, 1) = 0 < +\infty$，完全满足共同设定。

取有限维子空间 $K := E' = (\mathbb{R}^2)'$（$\dim K = 2 < \infty$）与 $F := \mathrm{span}\{\varphi\} \subset K$，其中 $\varphi(x_1, x_2) = x_1$。

1. **验证 $\overline{g_K} = g_K$**：
   映射 $q_K: \mathbb{R}^2 \to K^*$ 是线性映射；若 $q_K(x) = 0$，则一切 $\psi \in (\mathbb{R}^2)'$ 满足 $\psi(x) = 0$，故 $x = 0$（单射）。因 $\dim \mathbb{R}^2 = 2 = \dim K^*$，故 $q_K$ 是有限维实 Hausdorff 拓扑向量空间之间的线性同构，从而是同胚。
   于是对每个 $z \in K^*$，纤维 $q_K^{-1}(\{z\}) = \{q_K^{-1}(z)\}$ 为单点集，从而
   $$
   g_K(z) = f\bigl(q_K^{-1}(z)\bigr) \qquad \forall z \in K^*.
   $$
   因 $q_K^{-1} \times \mathrm{id}_{\mathbb{R}}: K^* \times \mathbb{R} \to \mathbb{R}^2 \times \mathbb{R}$ 连续且 $\mathrm{epi}_{\mathbb{R}}(f)$ 闭（S5），故 $\mathrm{epi}_{\mathbb{R}}(g_K) = (q_K^{-1} \times \mathrm{id}_{\mathbb{R}})^{-1}(\mathrm{epi}_{\mathbb{R}}(f))$ 在 $K^* \times \mathbb{R}$ 中闭，即 $g_K$ 已经下半连续（且由 S1 知其凸）。因此 $\overline{g_K} = g_K$。

2. **比较左右两端（省略最外层 $\bar{}$ 后的右式记为 $\psi$）**：
   由 $\overline{g_K} = g_K$ 与 S1 的相容恒等式，对一切 $y \in F^*$ 有
   $$
   \psi(y) := \inf_{r_{KF} z = y} \overline{g_K}(z) = \inf_{r_{KF} z = y} g_K(z) = g_F(y).
   $$
   沿用 S5 的同胚 $\Phi: F^* \xrightarrow{\sim} \mathbb{R}$ 与记号 $y_t = \Phi^{-1}(t)$，已算出
   $$
   \psi(y_t) = g_F(y_t) = \begin{cases} 0, & t > 0, \\ +\infty, & t \le 0. \end{cases}
   $$
   于是 $(\Phi \times \mathrm{id}_{\mathbb{R}})\bigl(\mathrm{epi}_{\mathbb{R}}(g_F)\bigr) = (0, +\infty) \times [0, +\infty)$，其在 $\mathbb{R} \times \mathbb{R}$ 中的闭包为 $[0, +\infty) \times [0, +\infty)$。由 $\mathrm{epi}_{\mathbb{R}}(\overline{g_F}) = \overline{\mathrm{epi}_{\mathbb{R}}(g_F)}$ 得
   $$
   \overline{g_F}(y_t) = \begin{cases} 0, & t \ge 0, \\ +\infty, & t < 0. \end{cases}
   $$
   特别地，在 $y_0 = 0 \in F^*$ 处有
   $$
   \overline{g_F}(y_0) = 0 \neq +\infty = \inf_{r_{KF} z = y_0} \overline{g_K}(z).
   $$
   （且 $\psi = g_F$ 甚至非下半连续，而 $\overline{g_F}$ 下半连续。）故右式的最外层 $\bar{}$ 不能总省去。