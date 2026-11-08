{}
以下按阶段编号逐项作答。全文记 $\mathcal{F}$ 为 $E'$ 的全体有限维线性子空间族；对任意拓扑线性空间 $X$ 上的函数 $u : X \to [-\infty, +\infty]$，严格按题设以实高度上图
$$\operatorname{epi}_{\mathbb{R}}(u) = \{ (x, t) \in X \times \mathbb{R} : u(x) \le t \}$$
在乘积拓扑空间 $X \times \mathbb{R}$ 中为闭集、在实向量空间 $X \times \mathbb{R}$ 中为凸集分别定义 $u$ 的下半连续性与凸性。

---

## S1　原始记录

### 1. $g_F$ 非负且至少一点有限
- **非负性**：由共同设定，对一切 $x \in E$ 有 $f(x) \ge 0$。对任意 $y \in F^*$，纤维 $q_F^{-1}(y) = \{x \in E : q_F(x) = y\}$ 上的函数值集合 $\{f(x) : q_F(x) = y\} \subset [0, +\infty]$ 以 $0$ 为下界（当纤维为空集时，按约定 $\inf \emptyset = +\infty \ge 0$）。故对一切 $y \in F^*$ 有 $g_F(y) \ge 0$，即 $g_F : F^* \to [0, +\infty]$ 非负。
- **至少一点有限**：由共同设定，存在 $x_0 \in E$ 使得 $f(x_0) < +\infty$。令 $y_0 = q_F(x_0) \in F^*$，则 $x_0 \in \{x \in E : q_F(x) = y_0\}$，从而
  $$0 \le g_F(y_0) = \inf \{f(x) : q_F(x) = y_0\} \le f(x_0) < +\infty,$$
  即 $g_F$ 在 $y_0$ 处取有限值。

### 2. $g_F$ 的凸性
我们要证明 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 是 $F^* \times \mathbb{R}$ 中的凸集。
任取 $(y_1, t_1), (y_2, t_2) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 及 $\lambda \in [0, 1]$，记
$$(y, t) := \lambda (y_1, t_1) + (1-\lambda)(y_2, t_2) = (\lambda y_1 + (1-\lambda)y_2,\, \lambda t_1 + (1-\lambda)t_2) \in F^* \times \mathbb{R}.$$
由 $(y_i, t_i) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 知 $g_F(y_i) \le t_i < +\infty$（$i = 1, 2$）。任取 $\varepsilon > 0$，由下确界定义，存在 $x_1, x_2 \in E$ 使得
$$q_F(x_1) = y_1, \quad f(x_1) \le t_1 + \varepsilon; \qquad q_F(x_2) = y_2, \quad f(x_2) \le t_2 + \varepsilon.$$
这等价于 $(x_1, t_1 + \varepsilon), (x_2, t_2 + \varepsilon) \in \operatorname{epi}_{\mathbb{R}}(f)$。
因为 $f$ 是凸函数，按定义 $\operatorname{epi}_{\mathbb{R}}(f)$ 是 $E \times \mathbb{R}$ 中的凸集，故其凸组合满足
$$\lambda (x_1, t_1 + \varepsilon) + (1-\lambda)(x_2, t_2 + \varepsilon) = \bigl(\lambda x_1 + (1-\lambda)x_2,\, \lambda t_1 + (1-\lambda)t_2 + \varepsilon\bigr) \in \operatorname{epi}_{\mathbb{R}}(f),$$
即 $x_\varepsilon := \lambda x_1 + (1-\lambda)x_2 \in E$ 满足 $f(x_\varepsilon) \le \lambda t_1 + (1-\lambda)t_2 + \varepsilon = t + \varepsilon$。
又因为求值映射 $q_F : E \to F^*$ 是线性的（对任意 $\varphi \in F$，$q_F(\lambda x_1 + (1-\lambda)x_2)(\varphi) = \varphi(\lambda x_1 + (1-\lambda)x_2) = \lambda \varphi(x_1) + (1-\lambda)\varphi(x_2) = (\lambda q_F(x_1) + (1-\lambda)q_F(x_2))(\varphi)$），故
$$q_F(x_\varepsilon) = \lambda q_F(x_1) + (1-\lambda)q_F(x_2) = \lambda y_1 + (1-\lambda)y_2 = y.$$
于是 $x_\varepsilon$ 属于 $y$ 的纤维 $\{x \in E : q_F(x) = y\}$，从而
$$g_F(y) \le f(x_\varepsilon) \le t + \varepsilon.$$
由 $\varepsilon > 0$ 的任意性，令 $\varepsilon \downarrow 0$ 得 $g_F(y) \le t$，即 $(y, t) \in \operatorname{epi}_{\mathbb{R}}(g_F)$。因此 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 为凸集，$g_F$ 是凸函数。

### 3. 投影相容性公式 $g_F(y) = \inf_{r_{KF}z = y} g_K(z)$
设有限维子空间满足 $F \subset K \subset E'$。首先验证 $r_{KF} \circ q_K = q_F$：对任意 $x \in E$ 与 $\varphi \in F \subset K$，
$$(r_{KF}(q_K(x)))(\varphi) = (q_K(x)|_F)(\varphi) = q_K(x)(\varphi) = \varphi(x) = q_F(x)(\varphi),$$
故 $r_{KF}(q_K(x)) = q_F(x)$。固定 $y \in F^*$，分两步证明等式：
- **证明 $g_F(y) \le \inf_{r_{KF}z = y} g_K(z)$**：
  任取满足 $r_{KF}z = y$ 的 $z \in K^*$。对任意满足 $q_K(x) = z$ 的 $x \in E$，有 $q_F(x) = r_{KF}(q_K(x)) = r_{KF}z = y$，从而 $g_F(y) \le f(x)$。对满足 $q_K(x) = z$ 的全体 $x \in E$ 取下确界（若该纤维为空，则右端为 $+\infty$，不等式仍成立），得
  $$g_F(y) \le g_K(z).$$
  再对满足 $r_{KF}z = y$ 的全体 $z \in K^*$ 取下确界（若无此类 $z$，则右端为 $+\infty$），即得 $g_F(y) \le \inf_{r_{KF}z = y} g_K(z)$。
- **证明 $\inf_{r_{KF}z = y} g_K(z) \le g_F(y)$**：
  任取满足 $q_F(x) = y$ 的 $x \in E$，令 $z := q_K(x) \in K^*$。则 $r_{KF}z = r_{KF}(q_K(x)) = q_F(x) = y$，且由 $g_K(z)$ 的定义有 $g_K(z) \le f(x)$。因此
  $$\inf_{r_{KF}z' = y} g_K(z') \le g_K(z) \le f(x).$$
  对满足 $q_F(x) = y$ 的全体 $x \in E$ 取下确界（若 $q_F^{-1}(y) = \emptyset$，则右端 $g_F(y) = +\infty$，不等式自动成立），得 $\inf_{r_{KF}z = y} g_K(z) \le g_F(y)$。

综上，$g_F(y) = \inf_{r_{KF}z = y} g_K(z)$。

### 4. 关于纤维下确界是否需要取到的说明
**上述全部证明均不需要纤维下确界取到。**
- 在 $g_F$ 凸性的证明中，我们仅对任意 $\varepsilon > 0$ 选取纤维上的 $\varepsilon$-近似极小元（满足 $f(x_i) \le t_i + \varepsilon$），随后令 $\varepsilon \downarrow 0$，无需存在使 $f(x_i) = g_F(y_i)$ 的精确极小元；
- 在 $g_F(y) = \inf_{r_{KF}z = y} g_K(z)$ 的证明中，论证完全基于复合关系 $q_F = r_{KF} \circ q_K$ 将纤维 $q_F^{-1}(y)$ 分解为 $\bigsqcup_{r_{KF}z = y} q_K^{-1}(z)$ 以及完备格 $[0, +\infty]$ 上下确界的保序与结合性质，无论 $g_F(y)$、$g_K(z)$ 或外层下确界是否取到（乃至纤维为空集时）均严格成立。

---

## S2　紧次水平集

### 1. 预备引理（实高度上图闭性与次水平集闭性、求值映射连续性）
- **引理 2.1（下半连续的次水平集刻画）**：对任意拓扑空间 $X$ 及函数 $u : X \to [-\infty, +\infty]$，$\operatorname{epi}_{\mathbb{R}}(u)$ 在 $X \times \mathbb{R}$ 中闭，当且仅当对每个有限实数 $c \in \mathbb{R}$，次水平集 $\{x \in X : u(x) \le c\}$ 在 $X$ 中闭。
  *证明*：（$\Rightarrow$）固定 $c \in \mathbb{R}$，映射 $\iota_c : X \to X \times \mathbb{R}, \, x \mapsto (x, c)$ 连续，而 $\{u \le c\} = \iota_c^{-1}(\operatorname{epi}_{\mathbb{R}}(u))$，故当 $\operatorname{epi}_{\mathbb{R}}(u)$ 闭时 $\{u \le c\}$ 闭。
  （$\Leftarrow$）设对所有 $c \in \mathbb{R}$ 有 $\{u \le c\}$ 闭。任取 $(x_0, t_0) \in (X \times \mathbb{R}) \setminus \operatorname{epi}_{\mathbb{R}}(u)$，则 $t_0 \in \mathbb{R}$ 且 $u(x_0) > t_0$。取实数 $c$ 满足 $t_0 < c < u(x_0)$，则 $U := X \setminus \{u \le c\} = \{x \in X : u(x) > c\}$ 是 $x_0$ 在 $X$ 中的开邻域，$V := (-\infty, c)$ 是 $t_0$ 在 $\mathbb{R}$ 中的开邻域。开集 $U \times V$ 包含 $(x_0, t_0)$ 且与 $\operatorname{epi}_{\mathbb{R}}(u)$ 不交（因 $(x, t) \in U \times V \implies t < c < u(x)$）。故 $\operatorname{epi}_{\mathbb{R}}(u)$ 的补集开，即 $\operatorname{epi}_{\mathbb{R}}(u)$ 闭。$\square$
- **引理 2.2（$q_F$ 的连续性与 $F^*$ 的 Hausdorff 性）**：设 $\dim F = n < \infty$。当 $n = 0$ 时 $F^* = \{0\}$ 具平凡拓扑，为紧 Hausdorff 空间且 $q_F$ 常值连续；当 $n \ge 1$ 时，取 $F$ 的一组基 $\varphi_1, \dots, \varphi_n \in E'$，坐标映射 $\Phi : F^* \to \mathbb{R}^n, \, y \mapsto (y(\varphi_1), \dots, y(\varphi_n))$ 是赋予有限维拓扑的 $F^*$ 到欧氏空间 $\mathbb{R}^n$ 的线性同胚，故 $F^*$ 是 Hausdorff 拓扑向量空间。又因为 $\Phi(q_F(x)) = (\varphi_1(x), \dots, \varphi_n(x))$，且每个 $\varphi_i \in E'$ 在 $E$ 上连续，故 $\Phi \circ q_F : E \to \mathbb{R}^n$ 连续，从而 $q_F = \Phi^{-1} \circ (\Phi \circ q_F) : E \to F^*$ 连续。$\square$

### 2. 当 $g_F(y) < \infty$ 时纤维下确界取到
设 $y \in F^*$ 满足 $g_F(y) < +\infty$（由 S1 知 $g_F(y) \in [0, +\infty)$）。
对每个有限实数 $c > g_F(y)$，定义集合
$$A_c := \{ x \in E : q_F(x) = y \text{ 且 } f(x) \le c \} = q_F^{-1}(\{y\}) \cap \{f \le c\}.$$
1. **非空性**：因为 $c > g_F(y) = \inf \{f(x) : q_F(x) = y\}$，由下确界定义，存在 $x \in E$ 使得 $q_F(x) = y$ 且 $f(x) \le c$，故 $A_c \ne \emptyset$。
2. **紧性**：由引理 2.2，$F^*$ 是 Hausdorff 空间，故单点集 $\{y\}$ 在 $F^*$ 中闭；又 $q_F : E \to F^*$ 连续，故纤维 $q_F^{-1}(\{y\})$ 在 $E$ 中闭。由 S2 假设，次水平集 $\{f \le c\}$ 是 $E$ 的紧子集。紧集 $\{f \le c\}$ 的闭子集必紧，故 $A_c$ 是紧集（由于 $E$ 是 Hausdorff 空间，$A_c$ 也是闭集）。
3. **有限交性质**：固定 $c_0 = g_F(y) + 1$。指标集 $I := (g_F(y), c_0]$ 上的紧闭子集族 $\{A_c\}_{c \in I}$ 满足单调包含关系（若 $c_1 \le c_2$ 则 $A_{c_1} \subset A_{c_2}$）。因此对任意有限个 $c_1, \dots, c_m \in I$，令 $\underline{c} = \min_{1 \le i \le m} c_i \in I$，有
   $$\bigcap_{i=1}^m A_{c_i} = A_{\underline{c}} \ne \emptyset,$$
   即紧空间 $A_{c_0}$ 的闭子集族 $\{A_c\}_{c \in I}$ 具有有限交性质。
4. **交集非空与极小元存在**：由紧空间的有限交性质定理（Cantor 交集定理，其条件“紧空间中具有限交性质的闭子集族”已满足），交集
   $$\bigcap_{c \in (g_F(y), c_0]} A_c \ne \emptyset.$$
   任取 $x_* \in \bigcap_{c \in (g_F(y), c_0]} A_c$，则 $q_F(x_*) = y$，且对一切 $c \in (g_F(y), c_0]$ 有 $f(x_*) \le c$。令 $c \downarrow g_F(y)$ 得 $f(x_*) \le g_F(y)$。结合 $q_F(x_*) = y$ 所蕴含的 $g_F(y) \le f(x_*)$，得 $f(x_*) = g_F(y)$。即纤维下确界在 $x_* \in E$ 处取到。

### 3. 各 $g_F$ 下半连续
由引理 2.1，只需证明对每个有限实数 $c \in \mathbb{R}$，次水平集 $\{y \in F^* : g_F(y) \le c\}$ 在 $F^*$ 中闭。
我们先证明对任意 $c \in \mathbb{R}$，有集合等式
$$\{y \in F^* : g_F(y) \le c\} = q_F(\{x \in E : f(x) \le c\}).$$
- **（$\supset$）**：若 $x \in E$ 满足 $f(x) \le c$，令 $y = q_F(x)$，则 $g_F(y) \le f(x) \le c$，故 $y \in \{g_F \le c\}$。
- **（$\subset$）**：若 $y \in F^*$ 满足 $g_F(y) \le c$，因 $c \in \mathbb{R}$ 有限，故 $g_F(y) < +\infty$。由本阶段第 2 步已证的纤维下确界可达性，存在 $x_* \in E$ 使得 $q_F(x_*) = y$ 且 $f(x_*) = g_F(y) \le c$，故 $x_* \in \{f \le c\}$，从而 $y = q_F(x_*) \in q_F(\{f \le c\})$。

现在验证 $q_F(\{f \le c\})$ 的闭性：
- 由 S2 假设，$\{f \le c\}$ 是 $E$ 中的紧集；
- 由引理 2.2，$q_F : E \to F^*$ 是连续映射，且 $F^*$ 是 Hausdorff 空间；
- 援引一般拓扑学标准定理：**紧集在连续映射下的像是紧集，且 Hausdorff 空间中的紧子集必为闭集**（此处 $\{f \le c\}$ 紧、$q_F$ 连续、$F^*$ Hausdorff，定理条件完全具备）。

因此 $\{g_F \le c\} = q_F(\{f \le c\})$ 是 $F^*$ 中的紧集从而是闭集。由引理 2.1，$\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^* \times \mathbb{R}$ 中闭，即 $g_F$ 下半连续。

---

## S3　兼容成本记录的实现

### 1. 元素 $x \in E$ 的构造
由 S2 的条件，次水平集 $K_c := \{x \in E : f(x) \le c\}$ 是 Hausdorff 局部凸空间 $E$ 的紧子集。
对每个有限维子空间 $F \in \mathcal{F}$，在 $K_c$ 中定义子集
$$C_F := \{ x \in K_c : q_F(x) = y_F \} = K_c \cap q_F^{-1}(\{y_F\}).$$
我们构造 $x$ 为全体 $C_F$（$F \in \mathcal{F}$）的交集中的唯一元素：
$$\{x\} = \bigcap_{F \in \mathcal{F}} C_F.$$

### 2. 存在性验证（交集非空且满足所需性质）
逐步核验紧空间 $K_c$ 中子集族 $\{C_F\}_{F \in \mathcal{F}}$ 的性质：
1. **每个 $C_F$ 非空**：由题设，对每个 $F \in \mathcal{F}$ 有 $g_F(y_F) \le c < +\infty$。援引 S2 已证结论（当前处于 S2 条件下，故完全适用），$g_F(y_F)$ 的纤维下确界取到，即存在 $x_F \in E$ 使得 $q_F(x_F) = y_F$ 且 $f(x_F) = g_F(y_F) \le c$。于是 $x_F \in K_c$ 且 $q_F(x_F) = y_F$，即 $x_F \in C_F$，故 $C_F \ne \emptyset$。
2. **每个 $C_F$ 是 $K_c$ 的闭子集**：由 S2 引理 2.2，$q_F : E \to F^*$ 连续且 $F^*$ 为 Hausdorff 空间，故单点集原像 $q_F^{-1}(\{y_F\})$ 在 $E$ 中闭，从而 $C_F = K_c \cap q_F^{-1}(\{y_F\})$ 在 $K_c$ 的子空间拓扑下为闭集（同时也是紧集）。
3. **反单调性（$F \subset K \implies C_K \subset C_F$）**：若有限维子空间满足 $F \subset K \subset E'$，任取 $z \in C_K$，则 $z \in K_c$ 且 $q_K(z) = y_K$。利用 S1 已证的 $r_{KF} \circ q_K = q_F$ 以及题设相容条件 $r_{KF} y_K = y_F$，有
   $$q_F(z) = r_{KF}(q_K(z)) = r_{KF}(y_K) = y_F,$$
   故 $z \in C_F$。因此 $C_K \subset C_F$。
4. **有限交性质**：任取有限个 $F_1, \dots, F_m \in \mathcal{F}$。令 $K := F_1 + \dots + F_m = \operatorname{span}(F_1 \cup \dots \cup F_m) \subset E'$。因为有限个有限维子空间的和仍为有限维子空间，故 $K \in \mathcal{F}$，且对每个 $i = 1, \dots, m$ 有 $F_i \subset K$。由上述反单调性，$C_K \subset C_{F_i}$（$1 \le i \le m$），从而
   $$\emptyset \ne C_K \subset \bigcap_{i=1}^m C_{F_i}.$$
   这证明了闭子集族 $\{C_F\}_{F \in \mathcal{F}}$ 在紧空间 $K_c$ 中具有有限交性质。
5. **全局交非空与性质核验**：由紧空间的有限交性质定理（$K_c$ 紧且 $\{C_F\}_{F \in \mathcal{F}}$ 为具有限交性质的闭子集族），有
   $$\bigcap_{F \in \mathcal{F}} C_F \ne \emptyset.$$
   任取 $x \in \bigcap_{F \in \mathcal{F}} C_F$。一方面，$x \in K_c$ 意味着 $f(x) \le c$；另一方面，对每个 $F \in \mathcal{F}$ 有 $x \in C_F$，意味着 $q_F(x) = y_F$ 对所有有限维 $F \subset E'$ 成立。

### 3. 唯一性验证
设 $x_1, x_2 \in E$ 均满足对所有有限维 $F \subset E'$ 有 $q_F(x_1) = y_F = q_F(x_2)$。
任取 $\varphi \in E'$，令一维（或零维）子空间 $F_\varphi := \operatorname{span}\{\varphi\} \in \mathcal{F}$。则
$$\varphi(x_1) = q_{F_\varphi}(x_1)(\varphi) = y_{F_\varphi}(\varphi) = q_{F_\varphi}(x_2)(\varphi) = \varphi(x_2),$$
故对一切 $\varphi \in E'$ 有 $\varphi(x_1 - x_2) = 0$。
援引局部凸空间上的 **Hahn–Banach 分离定理**（共同设定中 $E$ 为实 Hausdorff 局部凸空间，若 $v \in E \setminus \{0\}$，则单点紧凸集 $\{v\}$ 与闭凸集 $\{0\}$ 不相交，定理条件成立，故存在 $\varphi \in E'$ 使 $\varphi(v) \ne 0$，即连续对偶 $E'$ 分离 $E$ 的点），由 $\forall \varphi \in E', \, \varphi(x_1 - x_2) = 0$ 推出 $x_1 - x_2 = 0$，即 $x_1 = x_2$。
因此满足条件的 $x \in E$ 存在且唯一。

---

## S4　一般成本的恢复

### 1. 判断结论
**结论：能（成立）。** 仅由全部 $(g_F)_{F \in \mathcal{F}}$ 即可构造满足全部要求的函数 $G : E \to [0, +\infty]$。

### 2. $G$ 的显式构造
在共同设定下，对每个有限维子空间 $F \in \mathcal{F}$：
1. 在有限维空间 $F^*$ 上，由已知的 $g_F : F^* \to [0, +\infty]$ 定义其上图闭包对应的正则化函数 $g_F^{\mathrm{cl}} : F^* \to [0, +\infty]$：令 $M_F := \operatorname{cl}_{F^* \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(g_F))$ 为 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在乘积空间 $F^* \times \mathbb{R}$ 中的闭包，定义
   $$g_F^{\mathrm{cl}}(y) := \inf \{ t \in \mathbb{R} : (y, t) \in M_F \} = \sup_{U \in \mathcal{N}_{F^*}(y)} \inf_{y' \in U} g_F(y'), \quad y \in F^*,$$
   其中 $\mathcal{N}_{F^*}(y)$ 为 $y$ 在 $F^*$ 中的邻域系（空集下确界仍约定为 $+\infty$）。
2. 定义单观测空间 $F$ 上的拉回恢复函数 $G_F : E \to [0, +\infty]$ 为
   $$G_F(x) := g_F^{\mathrm{cl}}(q_F(x)), \quad x \in E.$$
3. 对全体有限维子空间 $F \in \mathcal{F}$ 取上确界，定义 $G : E \to [0, +\infty]$ 为
   $$G(x) := \sup_{F \in \mathcal{F}} G_F(x) = \sup_{F \in \mathcal{F}} g_F^{\mathrm{cl}}(q_F(x)), \quad x \in E.$$
   （注：$G$ 仅依赖于族 $(g_F)_{F \in \mathcal{F}}$ 以及空间结构决定的典范映射 $q_F$。）

### 3. 基础性质与扩大观测空间时的单调关系验证
我们先核验每个 $g_F^{\mathrm{cl}}$ 与 $G_F$ 的性质，再建立扩大观测空间 $F \subset K$ 时的关系：
- **$g_F^{\mathrm{cl}}$ 的上图与性质**：
  由 S1 知 $g_F \ge 0$ 且凸，故 $\operatorname{epi}_{\mathbb{R}}(g_F) \subset F^* \times [0, +\infty)$ 是凸集。在拓扑向量空间 $F^* \times \mathbb{R}$ 中，凸集的闭包仍为凸集，且因 $F^* \times [0, +\infty)$ 是闭集，有 $M_F = \operatorname{cl}(\operatorname{epi}_{\mathbb{R}}(g_F)) \subset F^* \times [0, +\infty)$。
  又若 $(y, t) \in M_F$ 且 $s > t$，由于平移 $(y', t') \mapsto (y', t' + s - t)$ 是 $F^* \times \mathbb{R}$ 的同胚且将 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 映入自身，故 $(y, s) \in M_F$。结合 $M_F$ 的闭性可知，对任意 $(y, t) \in F^* \times \mathbb{R}$，
  $$g_F^{\mathrm{cl}}(y) \le t \iff (y, t) \in M_F,$$
  即 $\operatorname{epi}_{\mathbb{R}}(g_F^{\mathrm{cl}}) = M_F = \operatorname{cl}_{F^* \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(g_F))$。
  因此 $g_F^{\mathrm{cl}} : F^* \to [0, +\infty]$ 下半连续、凸，且因 $\operatorname{epi}_{\mathbb{R}}(g_F) \subset M_F$ 而满足 $0 \le g_F^{\mathrm{cl}} \le g_F$。
- **$G_F$ 的下半连续性、凸性与 $0 \le G_F \le f$**：
  映射 $Q_F := q_F \times \operatorname{id}_{\mathbb{R}} : E \times \mathbb{R} \to F^* \times \mathbb{R}, \, (x, t) \mapsto (q_F(x), t)$ 是连续线性映射（由 S2 引理 2.2，其证明仅用到共同设定，故 $q_F$ 连续线性）。而
  $$\operatorname{epi}_{\mathbb{R}}(G_F) = \{ (x, t) \in E \times \mathbb{R} : g_F^{\mathrm{cl}}(q_F(x)) \le t \} = Q_F^{-1}\bigl(\operatorname{epi}_{\mathbb{R}}(g_F^{\mathrm{cl}})\bigr) = Q_F^{-1}(M_F).$$
  闭凸集 $M_F$ 在连续线性映射 $Q_F$ 下的原像必为 $E \times \mathbb{R}$ 中的闭凸集，故 $G_F$ 在 $E$ 上下半连续且凸。
  又对任意 $x \in E$，有 $0 \le G_F(x) = g_F^{\mathrm{cl}}(q_F(x)) \le g_F(q_F(x)) = \inf \{f(x') : q_F(x') = q_F(x)\} \le f(x)$。
- **扩大观测空间时的关系（当 $F \subset K$ 时）**：
  设有限维子空间满足 $F \subset K \subset E'$。
  1. 在原始记录拉回层面，由 S1 的 $g_F(y) = \inf_{r_{KF}z = y} g_K(z)$，对任意 $z \in K^*$ 有 $g_F(r_{KF}z) \le g_K(z)$；取 $z = q_K(x)$（此时 $r_{KF}z = q_F(x)$），得
     $$g_F(q_F(x)) \le g_K(q_K(x)), \quad \forall x \in E.$$
  2. 在正则化记录与恢复层面，限制映射 $r_{KF} : K^* \to F^*$ 是有限维向量空间之间的线性映射，故在有限维拓扑下连续。从而 $R_{KF} := r_{KF} \times \operatorname{id}_{\mathbb{R}} : K^* \times \mathbb{R} \to F^* \times \mathbb{R}$ 连续线性。
     由 $\forall z \in K^*, \, g_F^{\mathrm{cl}}(r_{KF}z) \le g_F(r_{KF}z) \le g_K(z)$ 知
     $$\operatorname{epi}_{\mathbb{R}}(g_K) \subset R_{KF}^{-1}(\operatorname{epi}_{\mathbb{R}}(g_F^{\mathrm{cl}})) = R_{KF}^{-1}(M_F).$$
     因 $M_F$ 在 $F^* \times \mathbb{R}$ 中闭且 $R_{KF}$ 连续，故 $R_{KF}^{-1}(M_F)$ 在 $K^* \times \mathbb{R}$ 中闭，从而包含 $\operatorname{epi}_{\mathbb{R}}(g_K)$ 的闭包 $M_K = \operatorname{epi}_{\mathbb{R}}(g_K^{\mathrm{cl}})$。这等价于：
     $$g_F^{\mathrm{cl}}(r_{KF}z) \le g_K^{\mathrm{cl}}(z), \quad \forall z \in K^*.$$
     代入 $z = q_K(x)$ 即得扩大观测空间时的单调性关系：
     $$F \subset K \implies G_F(x) = g_F^{\mathrm{cl}}(q_F(x)) \le g_K^{\mathrm{cl}}(q_K(x)) = G_K(x), \quad \forall x \in E.$$
     因此，当观测空间 $F$ 沿包含关系扩大时，$G_F$ 单调递增，且对任意有限个 $F_1, \dots, F_m \in \mathcal{F}$，令 $K = F_1 + \dots + F_m \in \mathcal{F}$，有 $\max_{1 \le i \le m} G_{F_i} \le G_K$；故族 $\{G_F\}_{F \in \mathcal{F}}$ 构成关于包含序向上有向的函数网，$G(x) = \sup_{F \in \mathcal{F}} G_F(x) = \lim_{F \in \mathcal{F}} G_F(x)$。

### 4. 验证 $G$ 的全部所需性质
1. **值域与 $G \le f$**：对每个 $F \in \mathcal{F}$ 已证 $0 \le G_F \le f$，对 $F \in \mathcal{F}$ 取上确界得 $0 \le G(x) \le f(x)$（$\forall x \in E$），故 $G : E \to [0, +\infty]$ 且 $G \le f$。
2. **下半连续性与凸性**：由上确界定义，对任意 $(x, t) \in E \times \mathbb{R}$，
   $$G(x) \le t \iff \forall F \in \mathcal{F}, \, G_F(x) \le t,$$
   故
   $$\operatorname{epi}_{\mathbb{R}}(G) = \bigcap_{F \in \mathcal{F}} \operatorname{epi}_{\mathbb{R}}(G_F).$$
   因为每个 $\operatorname{epi}_{\mathbb{R}}(G_F)$ 是 $E \times \mathbb{R}$ 中的闭凸集，而任意族闭凸集的交集仍为闭凸集，所以 $\operatorname{epi}_{\mathbb{R}}(G)$ 在 $E \times \mathbb{R}$ 中闭且凸，即 $G$ 下半连续且凸。
3. **最大性（对任意下半连续凸竞争函数 $h : E \to [-\infty, +\infty]$，若 $h \le f$ 则 $h \le G$）**：
   任取下半连续、凸且满足 $h \le f$ 的函数 $h : E \to [-\infty, +\infty]$。按定义，$\operatorname{epi}_{\mathbb{R}}(h)$ 是 $E \times \mathbb{R}$ 中的闭凸集，且由 $h \le f$ 知 $\operatorname{epi}_{\mathbb{R}}(f) \subset \operatorname{epi}_{\mathbb{R}}(h)$。由于共同设定中存在 $x_1 \in E$ 使 $f(x_1) < +\infty$，有 $(x_1, f(x_1)) \in \operatorname{epi}_{\mathbb{R}}(f) \subset \operatorname{epi}_{\mathbb{R}}(h)$，故 $\operatorname{epi}_{\mathbb{R}}(h)$ 非空。
   我们要证对任意 $x_0 \in E$ 有 $h(x_0) \le G(x_0)$。若 $h(x_0) = -\infty$，因 $G(x_0) \ge 0$，不等式平凡成立。下设 $h(x_0) > -\infty$，任取实数 $t_0 \in \mathbb{R}$ 满足 $t_0 < h(x_0)$，只需证明 $t_0 < G(x_0)$。
   - 由 $t_0 < h(x_0)$ 知点 $(x_0, t_0) \notin \operatorname{epi}_{\mathbb{R}}(h)$。
   - 考察乘积空间 $E \times \mathbb{R}$：因 $E$ 与 $\mathbb{R}$ 均为实 Hausdorff 局部凸空间，其乘积 $E \times \mathbb{R}$ 也是实 Hausdorff 局部凸空间，且 $(E \times \mathbb{R})'$ 与 $E' \times \mathbb{R}$ 典范同构，连续线性泛函表为 $(x, t) \mapsto \varphi(x) + \alpha t$（其中 $\varphi \in E', \alpha \in \mathbb{R}$）。
   - 在 $E \times \mathbb{R}$ 中，$\{(x_0, t_0)\}$ 是非空紧凸集，$\operatorname{epi}_{\mathbb{R}}(h)$ 是与之不相交的非空闭凸集。援引**局部凸 Hausdorff 空间中紧凸集与闭凸集的 Hahn–Banach 严格分离定理**（定理条件全部满足），存在 $\varphi \in E'$、$\alpha \in \mathbb{R}$ 及实数 $\gamma \in \mathbb{R}$，使得
     $$\varphi(x_0) + \alpha t_0 < \gamma < \varphi(x) + \alpha t, \quad \forall (x, t) \in \operatorname{epi}_{\mathbb{R}}(h).$$
   - 因为 $\operatorname{epi}_{\mathbb{R}}(f) \subset \operatorname{epi}_{\mathbb{R}}(h)$，上式对一切 $(x, t) \in \operatorname{epi}_{\mathbb{R}}(f)$ 均成立。
   - 令有限维子空间 $F := \operatorname{span}\{\varphi\} \subset E'$（$\dim F \le 1$，故 $F \in \mathcal{F}$）。在 $F^*$ 上定义连续线性泛函 $\hat{\varphi} : F^* \to \mathbb{R}, \, \hat{\varphi}(y) := y(\varphi)$，则对一切 $x \in E$ 有 $\hat{\varphi}(q_F(x)) = q_F(x)(\varphi) = \varphi(x)$。
   - 任取 $(y, t) \in \operatorname{epi}_{\mathbb{R}}(g_F)$，则 $g_F(y) \le t < +\infty$。对任意 $\varepsilon > 0$，由 $g_F(y)$ 的定义，存在 $x \in E$ 使得 $q_F(x) = y$ 且 $f(x) \le t + \varepsilon$，即 $(x, t + \varepsilon) \in \operatorname{epi}_{\mathbb{R}}(f)$。代入严格分离不等式得
     $$\hat{\varphi}(y) + \alpha(t + \varepsilon) = \varphi(x) + \alpha(t + \varepsilon) > \gamma.$$
     令 $\varepsilon \downarrow 0$ 得
     $$\hat{\varphi}(y) + \alpha t \ge \gamma, \quad \forall (y, t) \in \operatorname{epi}_{\mathbb{R}}(g_F).$$
   - 因为映射 $(y, t) \mapsto \hat{\varphi}(y) + \alpha t$ 在 $F^* \times \mathbb{R}$ 上连续，闭半空间 $H_\gamma := \{ (y, t) \in F^* \times \mathbb{R} : \hat{\varphi}(y) + \alpha t \ge \gamma \}$ 是包含 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 的闭集，从而必包含其闭包 $M_F = \operatorname{cl}_{F^* \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(g_F)) = \operatorname{epi}_{\mathbb{R}}(g_F^{\mathrm{cl}})$。
   - 另一方面，对点 $(q_F(x_0), t_0) \in F^* \times \mathbb{R}$，有
     $$\hat{\varphi}(q_F(x_0)) + \alpha t_0 = \varphi(x_0) + \alpha t_0 < \gamma,$$
     故 $(q_F(x_0), t_0) \notin H_\gamma$，从而 $(q_F(x_0), t_0) \notin \operatorname{epi}_{\mathbb{R}}(g_F^{\mathrm{cl}})$。
   - 按 $\operatorname{epi}_{\mathbb{R}}(g_F^{\mathrm{cl}})$ 的定义，这意味着 $t_0 < g_F^{\mathrm{cl}}(q_F(x_0)) = G_F(x_0) \le G(x_0)$。
   - 由 $t_0 < h(x_0)$ 的任意性，证得 $h(x_0) \le G(x_0)$。因此 $h \le G$。

---

## S5　闭成本的有限投影

### 1. 判断结论
**结论：否（未必下半连续）。** 即使在 $E = \mathbb{R}^2$ 上 $f : E \to [0, +\infty]$ 下半连续、凸且至少一点有限，有限维子空间 $F \subset E'$ 对应的 $g_F$ 也未必下半连续。

### 2. 反例构造
设 $E = \mathbb{R}^2$（赋予标准欧氏拓扑）。定义闭凸集
$$C := \{ (x_1, x_2) \in \mathbb{R}^2 : x_1 > 0, \, x_1 x_2 \ge 1 \} = \{ (x_1, x_2) \in \mathbb{R}^2 : x_1 \ge 0, \, x_2 \ge 0, \, x_1 x_2 \ge 1 \},$$
并令 $f : \mathbb{R}^2 \to [0, +\infty]$ 为 $C$ 的示性函数：
$$f(x_1, x_2) := \begin{cases} 0, & \text{若 } x_1 > 0 \text{ 且 } x_1 x_2 \ge 1, \\ +\infty, & \text{其他}. \end{cases}$$
取第一坐标投影泛函 $\varphi_1 \in (\mathbb{R}^2)'$，$\varphi_1(x_1, x_2) = x_1$，并取一维子空间 $F := \operatorname{span}\{\varphi_1\} \subset (\mathbb{R}^2)'$。

### 3. 反例性质的完整核验
1. **$f$ 非负且至少一点有限**：$f$ 仅取值 $0$ 与 $+\infty$，故 $f : \mathbb{R}^2 \to [0, +\infty]$。在点 $(1, 1) \in \mathbb{R}^2$ 处，因 $1 > 0$ 且 $1 \cdot 1 = 1 \ge 1$，有 $f(1, 1) = 0 < +\infty$。
2. **$f$ 下半连续且凸（即 $\operatorname{epi}_{\mathbb{R}}(f)$ 在 $\mathbb{R}^2 \times \mathbb{R}$ 中闭且凸）**：
   直接计算知
   $$\operatorname{epi}_{\mathbb{R}}(f) = \{ (x_1, x_2, t) \in \mathbb{R}^2 \times \mathbb{R} : f(x_1, x_2) \le t \} = C \times [0, +\infty).$$
   - **闭性**：在 $\mathbb{R}^2$ 上，函数 $(x_1, x_2) \mapsto x_1$、$(x_1, x_2) \mapsto x_2$ 与 $(x_1, x_2) \mapsto x_1 x_2$ 均连续，而 $C = \{x_1 \ge 0\} \cap \{x_2 \ge 0\} \cap \{x_1 x_2 \ge 1\}$（注意若 $x_1 \ge 0$ 且 $x_1 x_2 \ge 1$，则必有 $x_1 > 0$ 且 $x_2 > 0$）。作为三个闭集的交集，$C$ 在 $\mathbb{R}^2$ 中闭；又 $[0, +\infty)$ 在 $\mathbb{R}$ 中闭，故乘积集 $\operatorname{epi}_{\mathbb{R}}(f) = C \times [0, +\infty)$ 在 $\mathbb{R}^2 \times \mathbb{R}$ 中闭，即 $f$ 下半连续。
   - **凸性**：在 $(0, +\infty)$ 上，函数 $u(s) = 1/s$ 二阶可导且 $u''(s) = 2/s^3 > 0$，故为凸函数（亦可直接代数验证：若 $(x_1, x_2), (x_1', x_2') \in C$ 且 $\lambda \in [0, 1]$，则 $\lambda x_1 + (1-\lambda)x_1' > 0$，且由均值不等式 $\frac{x_1}{x_1'} + \frac{x_1'}{x_1} \ge 2$ 有 $(\lambda x_1 + (1-\lambda)x_1')(\lambda x_2 + (1-\lambda)x_2') \ge \lambda^2 + (1-\lambda)^2 + \lambda(1-\lambda)(\frac{x_1}{x_1'} + \frac{x_1'}{x_1}) \ge (\lambda + 1 - \lambda)^2 = 1$）。因此 $C = \{(x_1, x_2) : x_1 > 0, x_2 \ge 1/x_1\}$ 是 $\mathbb{R}^2$ 中的凸集。又 $[0, +\infty)$ 是 $\mathbb{R}$ 中的凸集，故 $\operatorname{epi}_{\mathbb{R}}(f) = C \times [0, +\infty)$ 是 $\mathbb{R}^2 \times \mathbb{R}$ 中的凸集，即 $f$ 是凸函数。
3. **计算 $g_F$ 并核验其不下半连续**：
   由 $\dim F = 1$，映射 $\Psi : F^* \to \mathbb{R}, \, y \mapsto y(\varphi_1)$ 是赋予有限维拓扑的 $F^*$ 到 $\mathbb{R}$ 的线性同胚。对任意 $x = (x_1, x_2) \in \mathbb{R}^2$，$\Psi(q_F(x)) = q_F(x)(\varphi_1) = \varphi_1(x_1, x_2) = x_1$。
   对任意 $y \in F^*$，记 $\eta := \Psi(y) = y(\varphi_1) \in \mathbb{R}$，则纤维为 $\{x \in \mathbb{R}^2 : q_F(x) = y\} = \{(\eta, x_2) : x_2 \in \mathbb{R}\}$：
   - 当 $\eta > 0$ 时，取 $x_2 = 1/\eta$，有 $(\eta, 1/\eta) \in C$，故 $f(\eta, 1/\eta) = 0$；结合 $f \ge 0$ 得 $g_F(y) = 0$。
   - 当 $\eta \le 0$ 时，对任意 $x_2 \in \mathbb{R}$ 均有 $(\eta, x_2) \notin C$，故 $f(\eta, x_2) = +\infty$，从而 $g_F(y) = +\infty$。
   因此
   $$g_F(y) = \begin{cases} 0, & \text{若 } y(\varphi_1) > 0, \\ +\infty, & \text{若 } y(\varphi_1) \le 0. \end{cases}$$
   现在考察 $F^* \times \mathbb{R}$ 中的点列 $(y_n, 0)$，其中 $y_n \in F^*$ 由 $y_n(\varphi_1) = \frac{1}{n} > 0$（$n = 1, 2, \dots$）唯一确定：
   - 对每个 $n \ge 1$，因 $g_F(y_n) = 0 \le 0$，有 $(y_n, 0) \in \operatorname{epi}_{\mathbb{R}}(g_F)$；
   - 当 $n \to \infty$ 时，$\Psi(y_n) = \frac{1}{n} \to 0 = \Psi(0)$，由于 $\Psi$ 是同胚，在 $F^* \times \mathbb{R}$ 中有 $(y_n, 0) \to (0, 0)$；
   - 然而在极限点 $(0, 0)$ 处，因 $0(\varphi_1) = 0 \le 0$，有 $g_F(0) = +\infty > 0$，故 $(0, 0) \notin \operatorname{epi}_{\mathbb{R}}(g_F)$。
   这证明了 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^* \times \mathbb{R}$ 中不是闭集，故 $g_F$ **不是**下半连续函数。

---

## S6　恢复与投影的精确关系

### 0. 关于符号 $\bar{u}$ 的说明
在任意实 Hausdorff 局部凸空间 $X$（如 $E$、$F^*$ 或 $K^*$）上，对非负凸函数 $u : X \to [0, +\infty]$，如同 S4 第 3 节对 $g_F^{\mathrm{cl}}$ 的论证，$\operatorname{cl}_{X \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(u))$ 是 $X \times [0, +\infty)$ 中的闭凸集且对第二坐标向上封闭，其唯一确定的函数
$$u^{\mathrm{cl}}(x) := \inf \{ t \in \mathbb{R} : (x, t) \in \operatorname{cl}_{X \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(u)) \}$$
满足 $\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}}) = \operatorname{cl}_{X \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(u))$，从而是非负下半连续凸函数且 $u^{\mathrm{cl}} \le u$；对任意满足 $w \le u$ 的下半连续凸函数 $w : X \to [-\infty, +\infty]$，由 $\operatorname{epi}_{\mathbb{R}}(u) \subset \operatorname{epi}_{\mathbb{R}}(w)$ 及 $\operatorname{epi}_{\mathbb{R}}(w)$ 闭立得 $\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}}) \subset \operatorname{epi}_{\mathbb{R}}(w)$，即 $w \le u^{\mathrm{cl}}$。因此 $u$ 的最大下半连续凸下界 $\bar{u}$ 恒存在且唯一，满足 $\operatorname{epi}_{\mathbb{R}}(\bar{u}) = \operatorname{cl}_{X \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(u))$。特别地，S4 中构造的 $g_F^{\mathrm{cl}}$ 即为 $\overline{g_F}$，而 $G$ 即为 $\bar{f}$。

### 1. 证明 $G = f$ 当且仅当 $f$ 下半连续
- **必要性（$G = f \implies f$ 下半连续）**：
  在 S4 中已仅用共同设定证明了 $G$ 是 $E$ 上的下半连续函数（即 $\operatorname{epi}_{\mathbb{R}}(G)$ 在 $E \times \mathbb{R}$ 中闭）。若 $G = f$，则 $\operatorname{epi}_{\mathbb{R}}(f) = \operatorname{epi}_{\mathbb{R}}(G)$ 在 $E \times \mathbb{R}$ 中闭，故 $f$ 下半连续。
- **充分性（$f$ 下半连续 $\implies G = f$）**：
  在 S4 中已证明 $G \le f$，且对任意下半连续、凸并满足 $h \le f$ 的函数 $h : E \to [-\infty, +\infty]$ 有 $h \le G$。
  若 $f$ 下半连续，结合共同设定中 $f$ 是凸函数且满足 $f \le f$，取竞争函数 $h = f$ 代入 S4 的最大性结论，立即得到 $f \le G$。结合 $G \le f$，即证得 $G = f$。

### 2. 证明 $\overline{g_F} = \overline{\bigl(y \mapsto \inf_{r_{KF}z = y} \overline{g_K}(z)\bigr)}$
设有限维子空间满足 $F \subset K \subset E'$。记右式括号内的函数为 $h_{KF} : F^* \to [0, +\infty]$：
$$h_{KF}(y) := \inf_{r_{KF}z = y} \overline{g_K}(z), \quad y \in F^*.$$
首先核验 $h_{KF}$ 是 $F^*$ 上的非负凸函数（从而 $\overline{h_{KF}}$ 有定义）：
- 因 $\overline{g_K} \ge 0$，故 $h_{KF} \ge 0$；
- 凸性：将 S1 第 2 节证明中的 $(E, F^*, q_F, f)$ 替换为 $(K^*, F^*, r_{KF}, \overline{g_K})$——由于 $\overline{g_K} : K^* \to [0, +\infty]$ 非负且凸，且限制映射 $r_{KF} : K^* \to F^*$ 是线性的，完全相同的论证给出 $\operatorname{epi}_{\mathbb{R}}(h_{KF})$ 在 $F^* \times \mathbb{R}$ 中凸，故 $h_{KF}$ 是非负凸函数。

下分双向不等式证明 $\overline{g_F} = \overline{h_{KF}}$：
- **证明 $\overline{h_{KF}} \le \overline{g_F}$**：
  因为 $\overline{g_K}$ 是 $g_K$ 的下界，对一切 $z \in K^*$ 有 $\overline{g_K}(z) \le g_K(z)$。对满足 $r_{KF}z = y$ 的 $z \in K^*$ 取下确界，并援引 S1 已证的恒等式 $\inf_{r_{KF}z = y} g_K(z) = g_F(y)$，得
  $$h_{KF}(y) = \inf_{r_{KF}z = y} \overline{g_K}(z) \le \inf_{r_{KF}z = y} g_K(z) = g_F(y), \quad \forall y \in F^*.$$
  由于 $\overline{h_{KF}}$ 是下半连续凸函数且满足 $\overline{h_{KF}} \le h_{KF} \le g_F$，而 $\overline{g_F}$ 是 $g_F$ 的最大下半连续凸下界，故
  $$\overline{h_{KF}} \le \overline{g_F}.$$
- **证明 $\overline{g_F} \le \overline{h_{KF}}$**：
  因为 $\overline{g_F} : F^* \to [0, +\infty]$ 下半连续且凸，而限制映射 $r_{KF} : K^* \to F^*$ 在有限维拓扑下连续且线性，故复合函数 $\overline{g_F} \circ r_{KF} : K^* \to [0, +\infty]$ 的实高度上图
  $$\operatorname{epi}_{\mathbb{R}}(\overline{g_F} \circ r_{KF}) = (r_{KF} \times \operatorname{id}_{\mathbb{R}})^{-1}\bigl(\operatorname{epi}_{\mathbb{R}}(\overline{g_F})\bigr)$$
  是 $K^* \times \mathbb{R}$ 中的闭凸集，即 $\overline{g_F} \circ r_{KF}$ 是 $K^*$ 上的非负下半连续凸函数。
  对任意 $z \in K^*$，由 $\overline{g_F} \le g_F$ 及 S1 的公式 $g_F(r_{KF}z) = \inf_{r_{KF}z' = r_{KF}z} g_K(z') \le g_K(z)$，有
  $$(\overline{g_F} \circ r_{KF})(z) = \overline{g_F}(r_{KF}z) \le g_F(r_{KF}z) \le g_K(z).$$
  即 $\overline{g_F} \circ r_{KF}$ 是 $g_K$ 的一个下半连续凸下界。由 $\overline{g_K}$ 作为 $g_K$ 最大下半连续凸下界的定义，必有
  $$\overline{g_F}(r_{KF}z) \le \overline{g_K}(z), \quad \forall z \in K^*.$$
  固定任意 $y \in F^*$，对满足 $r_{KF}z = y$ 的全体 $z \in K^*$ 取下确界（若此类 $z$ 为空集，则右端为 $+\infty$，不等式仍成立），得
  $$\overline{g_F}(y) \le \inf_{r_{KF}z = y} \overline{g_K}(z) = h_{KF}(y), \quad \forall y \in F^*.$$
  这说明 $\overline{g_F}$ 本身就是 $h_{KF}$ 的一个下半连续凸下界。再由 $\overline{h_{KF}}$ 作为 $h_{KF}$ 最大下半连续凸下界的定义，得
  $$\overline{g_F} \le \overline{h_{KF}}.$$

综合双向不等式，证得 $\overline{g_F} = \overline{h_{KF}} = \overline{\bigl(y \mapsto \inf_{r_{KF}z = y} \overline{g_K}(z)\bigr)}$。

### 3. 判断右式的最外层 bar 能否总省去
- **判断结论**：**否（不能总省去）。**
- **反例与完整核验**：
  沿用 S5 中已完整验证的反例设定：取 $E = \mathbb{R}^2$，
  $$f(x_1, x_2) = \begin{cases} 0, & \text{若 } x_1 > 0 \text{ 且 } x_1 x_2 \ge 1, \\ +\infty, & \text{其他}, \end{cases}$$
  以及一维子空间 $F = \operatorname{span}\{\varphi_1\} \subset E'$，其中 $\varphi_1(x_1, x_2) = x_1$。
  再取全对偶空间 $K := E' = (\mathbb{R}^2)'$。由于 $\dim K = 2 < +\infty$，$K$ 是 $E'$ 的有限维子空间且满足 $F \subset K \subset E'$。
  1. **核验 $\overline{g_K} = g_K$**：
     因为 $E = \mathbb{R}^2$ 是有限维空间且 $K = E'$，典范求值映射 $q_K : \mathbb{R}^2 \to K^*$ 是拓扑线性同构（双射且双向连续线性）。因此对每个 $z \in K^*$，纤维 $\{x \in \mathbb{R}^2 : q_K(x) = z\}$ 仅含唯一点 $q_K^{-1}(z)$，从而
     $$g_K(z) = f(q_K^{-1}(z)), \quad \forall z \in K^*.$$
     于是 $\operatorname{epi}_{\mathbb{R}}(g_K) = (q_K \times \operatorname{id}_{\mathbb{R}})(\operatorname{epi}_{\mathbb{R}}(f))$。在 S5 中已证 $f$ 下半连续且凸（即 $\operatorname{epi}_{\mathbb{R}}(f)$ 在 $\mathbb{R}^2 \times \mathbb{R}$ 中闭且凸），而 $q_K \times \operatorname{id}_{\mathbb{R}}$ 是拓扑线性同构，故 $\operatorname{epi}_{\mathbb{R}}(g_K)$ 在 $K^* \times \mathbb{R}$ 中闭且凸，即 $g_K$ 已经是下半连续凸函数。因此
     $$\overline{g_K} = g_K.$$
  2. **计算省去最外层 bar 后的右式 $h_{KF}$**：
     由 $\overline{g_K} = g_K$ 及 S1 的公式，省去最外层 bar 后的右式函数恰为 $g_F$：
     $$h_{KF}(y) = \inf_{r_{KF}z = y} \overline{g_K}(z) = \inf_{r_{KF}z = y} g_K(z) = g_F(y) = \begin{cases} 0, & \text{若 } y(\varphi_1) > 0, \\ +\infty, & \text{若 } y(\varphi_1) \le 0. \end{cases}$$
     特别地，在原点 $0 \in F^*$（满足 $0(\varphi_1) = 0$）处，有
     $$h_{KF}(0) = g_F(0) = +\infty.$$
  3. **计算左式 $\overline{g_F}$ 并与 $h_{KF}$ 对比**：
     在 S5 第 3 节中已证明：取 $y_n \in F^*$ 满足 $y_n(\varphi_1) = \frac{1}{n} > 0$，则 $(y_n, 0) \in \operatorname{epi}_{\mathbb{R}}(g_F)$ 且在 $F^* \times \mathbb{R}$ 中 $(y_n, 0) \to (0, 0)$。因此
     $$(0, 0) \in \operatorname{cl}_{F^* \times \mathbb{R}}(\operatorname{epi}_{\mathbb{R}}(g_F)) = \operatorname{epi}_{\mathbb{R}}(\overline{g_F}),$$
     这意味着 $\overline{g_F}(0) \le 0$；结合 $\overline{g_F} \ge 0$ 得
     $$\overline{g_F}(0) = 0.$$
     （事实上，在同构 $\Psi : F^* \to \mathbb{R}, \, y \mapsto y(\varphi_1)$ 下，$\operatorname{epi}_{\mathbb{R}}(g_F)$ 对应于 $(0, +\infty) \times [0, +\infty)$，其闭包 $\operatorname{epi}_{\mathbb{R}}(\overline{g_F})$ 对应于 $[0, +\infty) \times [0, +\infty)$，故当 $y(\varphi_1) \ge 0$ 时 $\overline{g_F}(y) = 0$，当 $y(\varphi_1) < 0$ 时 $\overline{g_F}(y) = +\infty$。）
  4. **结论核验**：
     在 $y = 0 \in F^*$ 处，
     $$\overline{g_F}(0) = 0 \ne +\infty = \inf_{r_{KF}z = 0} \overline{g_K}(z),$$
     故 $\overline{g_F} \ne \bigl(y \mapsto \inf_{r_{KF}z = y} \overline{g_K}(z)\bigr)$，右式的最外层 bar 不能总省去。
