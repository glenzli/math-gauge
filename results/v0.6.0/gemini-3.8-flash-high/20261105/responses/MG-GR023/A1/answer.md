# 有限测试记录与群作用的完全分类与分析

本文在 $\mathrm{ZFC}$ 公理系统下，对有限测试记录空间 $R_m(X)$、群作用下的不动记录子空间 $R_m(X)^G$ 以及无穷族乘积比较映射 $\Pi_{(X_i)}$ 给出完全分类、拓扑刻画与严格证明。全文严格覆盖空底集及空指标族的所有退化情形。

---

## 预备定义与基本性质

对参数 $m \in \mathbb{Z}_{\ge 1} \cup \{\infty\}$，集合 $X$ 的 $m$ 阶记录 $r = (r_n)_{0 \le n \le m}$ 满足 $r_n: \operatorname{Map}(X, [n]) \to [n]$，且对任意 $0 \le n, k \le m$、$f: X \to [n]$ 及 $a: [n] \to [k]$，自然性条件恒成立：
$$a(r_n(f)) = r_k(a \circ f).$$

### 引理 0（空底集判据与常值函数性质）
1. **空底集**：若 $X = \varnothing$，则对任意 $m \in \mathbb{Z}_{\ge 1} \cup \{\infty\}$，恒有 $R_m(\varnothing) = \varnothing$。
2. **常值观测**：若 $X \ne \varnothing$，设 $c_j: X \to [n]$ 为恒等于 $j \in [n]$ 的常值函数（$n \ge 1$），则必有 $r_n(c_j) = j$。

**证明**：
1. 考虑 $n = 0$。依据定义 $[0] = \varnothing$。从空集到空集的映射集合 $\operatorname{Map}(\varnothing, [0]) = \operatorname{Map}(\varnothing, \varnothing) = \{\varnothing\}$ 为非空单元素集（仅含空映射 $\varnothing$）。然而 $[0] = \varnothing$，因此不存在从非空集合到空集的映射，即不存在合法的 $r_0: \{\varnothing\} \to \varnothing$。故当 $X = \varnothing$ 时，$R_m(\varnothing) = \varnothing$。
2. 当 $X \ne \varnothing$ 时，$\operatorname{Map}(X, [0]) = \varnothing$，故 $r_0: \varnothing \to \varnothing$ 是唯一的空函数，且 $n=0$ 处的自然性条件平凡满足。对任意 $n \ge 1$ 及 $j \in [n]$，考虑常值态射 $a_j: [n] \to [n]$（将所有元素映为 $j$）。任取 $f \in \operatorname{Map}(X, [n])$（由于 $X \ne \varnothing, n \ge 1$，此类映射存在），$a_j \circ f$ 即为常值函数 $c_j$。由自然性：
   $$r_n(c_j) = r_n(a_j \circ f) = a_j(r_n(f)) = j.$$
引理证毕。$\blacksquare$

---

## 一、 截断及其相容关系

### 1.1 $R_m(X)$ 的完全分类

设 $X$ 为任意集合。若 $X = \varnothing$，分类由引理 0 给出：$R_m(\varnothing) = \varnothing$。下设 $X \ne \varnothing$。

#### (1) $m = 1$ 的情形
此时 $n \in \{0, 1\}$。由于 $X \ne \varnothing$，$r_0$ 是唯一的空函数；$[1] = \{0\}$，$\operatorname{Map}(X, [1])$ 仅含唯一常值函数 $c_0$，由引理 0 必有 $r_1(c_0) = 0$。自然性条件平凡成立。
因此，对任意非空集合 $X$：
$$R_1(X) = \{*\} \quad \text{（单点集）}.$$

#### (2) $m = 2$ 的情形
记 $\mathcal{P}(X)$ 为 $X$ 的幂集。每个映射 $f: X \to [2] = \{0, 1\}$ 与子集 $A = f^{-1}(1)$ 的特征函数 $\chi_A$ 一一对应。定义映射 $\mu: \mathcal{P}(X) \to \{0, 1\}$ 为 $\mu(A) = r_2(\chi_A)$。
- 由引理 0，$r_2(\chi_\varnothing) = r_2(c_0) = 0$，即 $\mu(\varnothing) = 0$；$r_2(\chi_X) = r_2(c_1) = 1$，即 $\mu(X) = 1$。
- 取对合对换 $\tau: [2] \to [2]$，$\tau(0) = 1, \tau(1) = 0$。则 $\tau \circ \chi_A = \chi_{X \setminus A}$。由自然性 $\tau(r_2(\chi_A)) = r_2(\tau \circ \chi_A)$，得：
  $$\mu(X \setminus A) = 1 - \mu(A).$$
- 至于映入 $[1]$ 的常值态射或恒等态射，自然性均由上述条件蕴含且平凡相容。

因此，$R_2(X)$ 与满足下述条件的所有**补自对偶指标函数（self-dual indicator）** $\mu: \mathcal{P}(X) \to \{0, 1\}$ 自然双射：
$$\mu(\varnothing) = 0, \quad \mu(X) = 1, \quad \forall A \subseteq X,\ \mu(X \setminus A) = 1 - \mu(A).$$
幂集 $\mathcal{P}(X)$ 在补运算下划分为无序对 $\{A, X \setminus A\}$。除平凡对 $\{\varnothing, X\}$（其值已固定为 $0$ 与 $1$）外，其余每个补对均可独立指定其中一个为 $1$、另一个为 $0$。
若 $X$ 为有限集且 $|X| \ge 1$，非平凡补对的数量为 $(2^{|X|} - 2) / 2 = 2^{|X|-1} - 1$。因此：
$$|R_2(X)| = 2^{2^{|X|-1} - 1}.$$

#### (3) $m \ge 3$（含 $m = \infty$）的情形
任取 $r \in R_m(X)$，定义 $\mu(A) = r_2(\chi_A)$。
对任意不相交子集 $A, B \subseteq X$，令 $C = X \setminus (A \cup B)$。定义 3-划分测试 $f: X \to [3]$：
$$f(x) = \begin{cases} 0, & x \in A, \\ 1, & x \in B, \\ 2, & x \in C. \end{cases}$$
分别考虑态射 $a, b, c: [3] \to [2]$：
- $a(0)=1, a(1)=0, a(2)=0 \implies a \circ f = \chi_A \implies a(r_3(f)) = \mu(A)$；
- $b(0)=0, b(1)=1, b(2)=0 \implies b \circ f = \chi_B \implies b(r_3(f)) = \mu(B)$；
- $c(0)=1, c(1)=1, c(2)=0 \implies c \circ f = \chi_{A \cup B} \implies c(r_3(f)) = \mu(A \cup B)$。

注意对任意 $j \in [3] = \{0, 1, 2\}$，均有 $c(j) = a(j) + b(j)$（因为 $a(j), b(j)$ 不能同时为 $1$）。代入 $j = r_3(f) \in [3]$，立即得到：
$$\mu(A \cup B) = c(r_3(f)) = a(r_3(f)) + b(r_3(f)) = \mu(A) + \mu(B).$$
故 $\mu$ 是 $\mathcal{P}(X)$ 上的有限可加 $\{0, 1\}$ 值概率测度，即**超滤子（ultrafilter）** $\mathcal{U} = \{A \subseteq X : \mu(A) = 1\}$。

反之，给定 $X$ 上的任意超滤子 $\mathcal{U}$，对每个 $n \ge 1$ 及任意 $f: X \to [n]$，原象族 $(f^{-1}(j))_{j \in [n]}$ 构成 $X$ 的有限划分。由超滤子性质，存在且仅存在唯一的 $j \in [n]$ 使得 $f^{-1}(j) \in \mathcal{U}$。定义 $r_n(f)$ 为该唯一标号 $j$。对任意 $a: [n] \to [k]$，$(a \circ f)^{-1}(a(j)) \supseteq f^{-1}(j) \in \mathcal{U}$，故必有 $r_k(a \circ f) = a(j) = a(r_n(f))$。

因此，对所有 $3 \le m \le \infty$：
$$R_m(X) \cong \beta X \quad \text{（$X$ 上的超滤子空间 / 离散空间的 Stone-Čech 紧化）}.$$

---

### 1.2 遗忘映射 $q_{m,k}$ 的像、纤维与映射相容性

设 $m \ge k \ge 1$。
- **若 $X = \varnothing$**：$R_m(\varnothing) = R_k(\varnothing) = \varnothing$，$q_{m, k}$ 为空映射，像为空，无纤维。
- **若 $X \ne \varnothing$**：
  1. **$k = 1$**：$R_1(X) = \{*\}$。由于对任意非空集 $X$，$R_m(X) \ne \varnothing$（主超滤子恒存在），故：
     $$\operatorname{Im}(q_{m, 1}) = R_1(X) = \{*\}, \quad q_{m, 1}^{-1}(*) = R_m(X).$$
  2. **$m \ge k \ge 3$**：$R_m(X)$ 与 $R_k(X)$ 均自然等同于 $\beta X$，$q_{m, k}$ 为双射。故：
     $$\operatorname{Im}(q_{m, k}) = R_k(X), \quad \forall r \in R_k(X),\ |q_{m, k}^{-1}(r)| = 1.$$
  3. **$k = 2$ 且 $m \ge 3$**：超滤子自然给出补自对偶指标函数。故：
     $$\operatorname{Im}(q_{m, 2}) = \beta X \subseteq R_2(X).$$
     对任意 $\mu \in R_2(X)$：若 $\mu$ 满足有限可加性（即 $\mu \in \beta X$），其纤维为单元素集；若 $\mu$ 不可加，其纤维为空集。
  4. **$m = k = 2$**：$q_{2, 2} = \operatorname{id}_{R_2(X)}$。

#### 与映射 $h: X \to Y$ 的相容性核验
对任意 $r \in R_m(X)$，$(R_m(h)r)_n(f) = r_n(f \circ h)$。
1. **良定义性**：对任意态射 $a: [n] \to [k]$，
   $$a\bigl((R_m(h)r)_n(f)\bigr) = a\bigl(r_n((f \circ h))\bigr) = r_k(a \circ (f \circ h)) = r_k((a \circ f) \circ h) = (R_m(h)r)_k(a \circ f),$$
   故 $R_m(h)r \in R_m(Y)$。
2. **与截断相容**：对任意 $n \le k$，$(q_{m, k}(R_m(h)r))_n(f) = r_n(f \circ h) = (R_k(h)(q_{m, k}r))_n(f)$，即
   $$q_{m, k} \circ R_m(h) = R_k(h) \circ q_{m, k}.$$
3. **点值记录相容**：
   $$(R_m(h)\eta_{m, X}(x))_n(f) = \eta_{m, X}(x)_n(f \circ h) = (f \circ h)(x) = f(h(x)) = \eta_{m, Y}(h(x))_n(f),$$
   即 $R_m(h) \circ \eta_{m, X} = \eta_{m, Y} \circ h$。
4. **超滤子推前相容（$m \ge 3$）**：若 $r$ 对应超滤子 $\mathcal{U} \in \beta X$，则 $(f \circ h)^{-1}(j) = h^{-1}(f^{-1}(j)) \in \mathcal{U} \iff f^{-1}(j) \in h_*(\mathcal{U})$，正是超滤子的前推映射 $\beta(h)$。

---

### 1.3 有限 $G$ 集合上的不动记录 $R_m(X)^G$

设 $X$ 为有限 $G$ 集合。
若 $X = \varnothing$，则对一切 $m$ 均有 $R_m(\varnothing)^G = \varnothing$，基数为 $0$。下设 $X$ 为非空有限集。

#### (1) $m = 1$
$R_1(X) = \{*\}$ 为单点集，群作用必平凡，故恒有：
$$R_1(X)^G = R_1(X), \quad |R_1(X)^G| = 1.$$
存在判准：恒非空。

#### (2) $m \ge 3$（含 $m = \infty$）
由于 $X$ 非空有限，每个超滤子均为由单点生成的**主超滤子**：$\beta X = \{\mathcal{U}_x : x \in X\}$。由此，点值记录映射 $\eta_{m, X}: X \to R_m(X)$ 为双射。
群作用在超滤子上的定义为 $g \cdot \mathcal{U}_x = \mathcal{U}_{gx}$，即 $\eta_{m, X}$ 是 $G$ 等变双射。因此：
$$R_m(X)^G = \eta_{m, X}(X^G) \cong X^G.$$
- **存在判准**：$R_m(X)^G \ne \varnothing \iff X^G \ne \varnothing$。
- **精确基数**：$|R_m(X)^G| = |X^G|$。
- **限制映射**：对任意 $m \ge k \ge 3$，$q_{m, k}: R_m(X)^G \to R_k(X)^G$ 为双射（在 $X^G$ 上为恒等映射）。

#### (3) $m = 2$
$r \in R_2(X)^G$ 等价于其指标函数 $\mu: \mathcal{P}(X) \to \{0, 1\}$ 是 $G$ 不变的，即对所有 $g \in G, A \subseteq X$，均有 $\mu(gA) = \mu(A)$。
群 $G$ 自然作用于有限集合 $\mathcal{P}(X)$。设 $\mathcal{O}$ 为其轨道集合。补运算 $A \mapsto X \setminus A$ 与群作用交换（$g(X \setminus A) = X \setminus gA$），诱导轨道集合上的对合 $\omega \mapsto \omega^c = \{X \setminus A : A \in \omega\}$。
- **自补轨道判据**：若存在轨道 $\omega \in \mathcal{O}$ 使得 $\omega = \omega^c$（即存在 $A \subseteq X, g \in G$ 使得 $gA = X \setminus A$），则由 $G$ 不变性与自对偶性：
  $$\mu(A) = \mu(gA) = \mu(X \setminus A) = 1 - \mu(A) \implies 2\mu(A) = 1,$$
  这在 $\{0, 1\}$ 中无解！故此时必有 $R_2(X)^G = \varnothing$。
  > *注*：若存在自补轨道，必有 $|A| = |X \setminus A|$，从而 $|X| = 2|A|$ 必须为偶数。若 $|X|$ 为奇数，则绝无自补轨道。
- **无自补轨道**：若对任意 $A \subseteq X$ 及任意 $g \in G$ 均有 $gA \ne X \setminus A$，则所有轨道两两配对成补轨道对 $\{\omega, \omega^c\}$。
  轨道对 $\{\{\varnothing\}, \{X\}\}$ 的值已被强制固定（$\mu=0$ 与 $\mu=1$）。对于其余的每一对互补轨道 $\{\omega, \omega^c\}$，我们可以独立且自由地选择在 $\omega$ 上取值 $1$、在 $\omega^c$ 上取值 $0$，或反之。
  设 $\mathcal{O}$ 的轨道总数为 $N_{\mathcal{O}}$，互补轨道对总数为 $N_{\mathcal{O}} / 2$。除平凡对外的自由轨道对数为 $(N_{\mathcal{O}}/2) - 1$。
因此：
- **存在判准**：$R_2(X)^G \ne \varnothing \iff \forall A \subseteq X,\ \forall g \in G,\ gA \ne X \setminus A$。
- **精确基数**：
  $$|R_2(X)^G| = \begin{cases} 2^{(N_{\mathcal{O}}/2) - 1}, & \text{不存在自补轨道}, \\ 0, & \text{存在自补轨道}. \end{cases}$$

#### (4) 不动集合间的限制映射
- 对 $m \ge k \ge 3$：$q_{m, k}: R_m(X)^G \to R_k(X)^G$ 为双射。
- 对 $m \ge 3$：$q_{m, 1}: R_m(X)^G \to R_1(X)^G$：
  - 当 $X^G = \varnothing$ 时，定义域为空，映射为空；
  - 当 $X^G \ne \varnothing$ 时，满射至唯一的单点集 $\{*\}$，纤维基数为 $|X^G|$。
- 对 $m \ge 3$：$q_{m, 2}: R_m(X)^G \to R_2(X)^G$ 为单射，其像恰为 $\eta_{2, X}(X^G)$：
  - 若 $x \in X^G$，则对应的主超滤子 $\mu_x(A) = \chi_A(x)$ 满足 $\mu_x(gA) = \chi_A(g^{-1}x) = \chi_A(x) = \mu_x(A)$，故落在 $R_2(X)^G$ 中；
  - 像的大小恰为 $|X^G|$。

---

### 1.4 有限层不动记录延拓为完整不动记录的准确范围

由上述分类，考察限制映射 $q_{\infty, m}: R_\infty(X)^G \to R_m(X)^G$ 的延拓性质：

1. **$m \ge 3$ 层**：
   由于 $q_{\infty, m}: R_\infty(X) \to R_m(X)$ 自身为 $G$ 等变双射，限制在不动子集上 $q_{\infty, m}: R_\infty(X)^G \to R_m(X)^G$ **恒为双射**。
   **范围结论**：对任意有限 $G$ 集合 $X$，$m \ge 3$ 层的每个有限层不动记录均能**唯一**延拓为完整不动记录。

2. **$m = 2$ 层**：
   $r \in R_2(X)^G$ 能够延拓为完整不动记录 $r_\infty \in R_\infty(X)^G$ 的充要条件是：$r$ 落在 $\operatorname{Im}(q_{\infty, 2})$ 中，即 $r = \eta_{2, X}(x)$ 且 $x \in X^G$（$r$ 对应于某个不动点的主超滤子）。
   - 若 $X^G = \varnothing$ 但 $R_2(X)^G \ne \varnothing$（例如 $\mathbb{Z}/3\mathbb{Z}$ 在自身上的循环移动，$|X|=3$ 无自补轨道，$|R_2(X)^G|=2$），延拓范围为**空集**（均不可延拓）。
   - 能够全部延拓（即 $q_{\infty, 2}$ 为满射）的充要条件为 $|R_2(X)^G| = |X^G|$。对非空有限集，这发生于 $|X| \le 2$ 或存在自补轨道且 $X^G = \varnothing$ 的情形。

3. **$m = 1$ 层**：
   $R_1(X)^G = \{*\}$。该唯一点能够延拓为完整不动记录的充要条件是：$X^G \ne \varnothing$。
   - 当 $X^G = \varnothing$ 时，不可延拓；
   - 当 $X^G \ne \varnothing$ 时，延拓不唯一，延拓解空间的大小恰为 $|X^G|$。

---

## 二、 完整不动记录的空间

### 2.1 内在分类与 $R_\infty(X)^G$ 的非空充要条件

设 $X$ 为任意 $G$ 集合。

#### (1) 内在拓扑分类
拓扑空间 $R_\infty(X)$ 取由全部观察 $r \mapsto r_n(f)$ 生成的最弱拓扑。当 $n = 2$ 时，$f = \chi_A$ 的原象观测给出基底开闭集：
$$\widehat{A} = \{\mathcal{U} \in \beta X : A \in \mathcal{U}\}.$$
这些集合正是 Stone-Čech 紧化 $\beta X$ 的 Stone 拓扑基。对于任意 $n$ 与 $f: X \to [n]$，$r_n(f) = j \iff f^{-1}(j) \in \mathcal{U}$，其原象亦为开闭集 $\widehat{f^{-1}(j)}$。因此，$R_\infty(X)$ 自然同胚于以离散拓扑为底的紧 Hausdorff 空间 $\beta X$。

群元素 $g \in G$ 诱导的自同构 $R_\infty(g_X)$ 对应于 $\beta X$ 上的同胚 $\beta(g_X): \mathcal{U} \mapsto g_*\mathcal{U}$，其中 $A \in g_*\mathcal{U} \iff g^{-1}A \in \mathcal{U}$。
因此，$R_\infty(X)^G$ 作为拓扑空间自然同胚于 **$G$ 不变超滤子空间**：
$$(\beta X)^G = \{\mathcal{U} \in \beta X : \forall g \in G,\ \forall A \in \mathcal{U},\ gA \in \mathcal{U}\},$$
它是紧 Hausdorff 空间 $\beta X$ 中的闭子空间，因而是**紧 Hausdorff 空间**。

进一步地，引入布尔代数 $\mathcal{P}(X)$ 中由所有群作用对称差生成的理想（变异理想 / equidecomposability ideal）：
$$\mathcal{I}_G = \bigl\{ E \subseteq X : \exists k \ge 1,\ A_1, \ldots, A_k \subseteq X,\ g_1, \ldots, g_k \in G \text{ 使得 } E \subseteq \bigcup_{i=1}^k (A_i \mathbin{\Delta} g_i A_i) \bigr\}.$$
超滤子 $\mathcal{U}$ 是 $G$ 不变的充要条件为其对应的同态 $\phi_\mathcal{U}: \mathcal{P}(X) \to \{0, 1\}$ 在 $\mathcal{I}_G$ 上全为 $0$。依据布尔代数的 Stone 对偶理论，$R_\infty(X)^G$ 严格同胚于商布尔代数的 Stone 空间：
$$R_\infty(X)^G \cong \operatorname{Stone}(\mathcal{P}(X) / \mathcal{I}_G).$$

#### (2) $R_\infty(X)^G \ne \varnothing$ 的充要条件
由布尔素理想定理（$\mathrm{ZFC}$ 标准定理），商代数 $\mathcal{P}(X) / \mathcal{I}_G$ 拥有超滤子当且仅当该布尔代数非平凡，即全集 $X \notin \mathcal{I}_G$ 且 $X \ne \varnothing$。
因此，$R_\infty(X)^G \ne \varnothing$ 的充要条件为：
$$X \ne \varnothing \quad \text{且} \quad \forall k \ge 1,\ A_1, \ldots, A_k \subseteq X,\ g_1, \ldots, g_k \in G,\ \bigcup_{i=1}^k (A_i \mathbin{\Delta} g_i A_i) \ne X.$$

---

### 2.2 $\eta_{\infty, X}(X^G)$ 的闭包与分类定理

#### (1) $\eta_{\infty, X}(X^G)$ 在 $R_\infty(X)$ 中的闭包
在 $\beta X$ 中，子集 $Y \subseteq X$ 对应的主超滤子集合的闭包为：
$$\overline{Y} = \bigcap_{A \supseteq Y} \widehat{A} = \widehat{Y} = \{\mathcal{U} \in \beta X : Y \in \mathcal{U}\} \cong \beta Y.$$
取 $Y = X^G$。若 $X^G = \varnothing$，闭包为空。若 $X^G \ne \varnothing$，对任意 $\mathcal{U} \in \widehat{X^G}$，由于 $X^G \in \mathcal{U}$，且 $G$ 在 $X^G$ 上恒等作用，对任意 $A \subseteq X$ 必有 $gA \cap X^G = g(A \cap X^G) = A \cap X^G$。故 $gA \in \mathcal{U} \iff A \in \mathcal{U}$，即 $\mathcal{U}$ 自动是 $G$ 不变的。
因此恒有：
$$\overline{\eta_{\infty, X}(X^G)} = \widehat{X^G} \subseteq R_\infty(X)^G, \quad \overline{\eta_{\infty, X}(X^G)} \cong \beta(X^G).$$

#### (2) $\overline{\eta_{\infty, X}(X^G)} = R_\infty(X)^G$ 的充要条件
任取 $\mathcal{U} \in R_\infty(X)^G$。由 $X = X^G \sqcup (X \setminus X^G)$，超滤子必含二者之一。
- 若 $X^G \in \mathcal{U}$，则 $\mathcal{U} \in \widehat{X^G}$；
- 若 $X \setminus X^G \in \mathcal{U}$，则 $\mathcal{U}$ 是 $G$ 集合 $X \setminus X^G$ 上的不变超滤子。
因此，等式 $\overline{\eta_{\infty, X}(X^G)} = R_\infty(X)^G$ 成立的充要条件为：**在非不动点子集 $X \setminus X^G$ 上不存在任何 $G$ 不变超滤子**，即：
$$R_\infty(X \setminus X^G)^G = \varnothing.$$

#### (3) 群 $G$ 的完全分类定理
**定理**：一个群 $G$ 对其每个 $G$ 集合 $X$ 均满足 $\overline{\eta_{\infty, X}(X^G)} = R_\infty(X)^G$，**当且仅当 $G$ 是有限生成群**。

**完整证明**：
- **充分性（若 $G$ 有限生成，则等式恒成立）**：
  设 $G$ 由有限集 $S = \{g_1, \ldots, g_k\}$ 生成。设 $X$ 为任意 $G$ 集合。
  点 $x \in X$ 为不动点当且仅当其被所有生成元固定：$x \in X^G \iff \forall i \in \{1, \ldots, k\}, g_i x = x$。
  令 $Y_{g_i} = \{x \in X : g_i x \ne x\}$。则：
  $$X \setminus X^G = \bigcup_{i=1}^k Y_{g_i}.$$
  这是有限个集合的并！
  假设存在 $\mathcal{U} \in R_\infty(X)^G$ 且 $\mathcal{U} \notin \overline{\eta(X^G)}$，则必有 $X \setminus X^G \in \mathcal{U}$。由超滤子对有限并的素性，必存在某个 $i \in \{1, \ldots, k\}$ 使得
  $$Y_{g_i} \in \mathcal{U}.$$
  现在考察单个元素 $g_i$ 在 $Y_{g_i}$ 上的作用。依据定义，在 $Y_{g_i}$ 上 $g_i$ 无任何不动点，故循环群 $\langle g_i \rangle$ 在 $Y_{g_i}$ 上的每个轨道均为长度 $\ge 2$ 的有限循环或与 $\mathbb{Z}$ 同构的双向无限链。这类轨道的有向图由不相交的圈与链构成，最大度不超过 $2$，色数至多为 $3$。
  由选择公理（AC），可以对 $Y_{g_i}$ 进行正常的 3-染色，将其划分为三个独立集：
  $$Y_{g_i} = C_0 \cup C_1 \cup C_2, \quad \text{满足 } \forall j \in \{0, 1, 2\},\ g_i(C_j) \cap C_j = \varnothing.$$
  由于 $Y_{g_i} \in \mathcal{U}$，必有唯一的颜色类 $C_j \in \mathcal{U}$。
  然而 $\mathcal{U}$ 是 $G$ 不变的，故 $g_i(C_j) \in \mathcal{U}$。于是：
  $$\varnothing = C_j \cap g_i(C_j) \in \mathcal{U},$$
  导出矛盾！因此不可能存在这样的超滤子，必有 $R_\infty(X \setminus X^G)^G = \varnothing$，等式对任意 $X$ 均成立。

- **必要性（若 $G$ 非有限生成，则必存在反例）**：
  设 $G$ 不是有限生成群。记 $\mathcal{P}_{\text{fin}}(G)$ 为 $G$ 的所有有限子集族。
  对每个 $F \in \mathcal{P}_{\text{fin}}(G)$，其生成的子群 $H_F = \langle F \rangle$ 必为 $G$ 的真子群（$H_F \lneq G$）。
  构造左陪集 $G$ 集合：
  $$X_F = G / H_F, \quad x_F = e H_F \in X_F.$$
  1. 对任意 $g \in F \subseteq H_F$，均有 $g \cdot x_F = g H_F = H_F = x_F$。即基点 $x_F$ 被 $F$ 中所有元素固定；
  2. 若 $X_F$ 存在被全群 $G$ 固定的点 $a H_F$，则 $a^{-1} G a \subseteq H_F \implies H_F = G$，与 $H_F \lneq G$ 矛盾。故 $X_F^G = \varnothing$。
  令 $X = \bigsqcup_{F \in \mathcal{P}_{\text{fin}}(G)} X_F$。则 $X^G = \bigsqcup X_F^G = \varnothing$，从而 $\overline{\eta(X^G)} = \varnothing$。
  另一方面，对任意有限元组 $g_1, \ldots, g_m \in G$，取 $F_0 = \{g_1, \ldots, g_m\}$。则对任意包含 $F_0$ 的有限集 $F \supseteq F_0$，基点 $x_F \in X_F \subset X$ 同时被 $g_1, \ldots, g_m$ 固定。
  因此，不动点子集族 $\{\operatorname{Fix}_X(g) : g \in G\}$ 具有**有限交性质**。
  由超滤子引理，存在包含该族的超滤子 $\mathcal{U} \in \beta X$。对任意 $g \in G$ 及 $A \in \mathcal{U}$，由于 $\operatorname{Fix}_X(g) \in \mathcal{U}$，集合 $A \cap \operatorname{Fix}_X(g) \in \mathcal{U}$，而 $g$ 在此集合上为恒等映射，故 $gA \supseteq g(A \cap \operatorname{Fix}_X(g)) = A \cap \operatorname{Fix}_X(g) \in \mathcal{U}$。
  这证明 $\mathcal{U}$ 是 $G$ 不变超滤子，即 $\mathcal{U} \in R_\infty(X)^G$。
  由此得到 $R_\infty(X)^G \ne \varnothing = \overline{\eta(X^G)}$，等式失效。定理证毕。$\blacksquare$

---

### 2.3 可数反例构造与完整不动记录描述

#### (1) 构造
取群 $G = S_{<\infty}(\mathbb{N})$（$\mathbb{N} = \{0, 1, 2, \ldots\}$ 上具有有限支集的所有置换构成的有限对称群，即全有限对称群）。
底集取 $X = \mathbb{N}$，$G$ 在 $X$ 上的作用为自然置换作用。
- **可数性核验**：$G = \bigcup_{n=1}^\infty S_n$ 是有限群的可数递增并，故 $G$ 为可数群；底集 $X = \mathbb{N}$ 为可数集。
- **无原集合不动点**：对任意 $n \in \mathbb{N}$，对换 $(n\ n+1) \in G$ 将 $n$ 映为 $n+1 \ne n$。因此 $X^G = \varnothing$。

#### (2) 全部不动记录的完整描述
由于 $R_\infty(X) \cong \beta\mathbb{N}$，超滤子分为主超滤子与自由超滤子两类：
1. **主超滤子**：若 $\mathcal{U} = \mathcal{U}_n$（$n \in \mathbb{N}$），取置换 $g = (n\ n+1) \in G$，则 $g \cdot \mathcal{U}_n = \mathcal{U}_{n+1} \ne \mathcal{U}_n$。故**不存在任何 $G$ 不变的主超滤子**。
2. **自由超滤子**：设 $\mathcal{U} \in \beta\mathbb{N} \setminus \mathbb{N} = \mathbb{N}^*$ 为任意自由超滤子。
   任取 $g \in G$。依据定义，$g$ 的支集 $\operatorname{supp}(g) = \{x \in \mathbb{N} : gx \ne x\}$ 是有限集。
   因此，其不动点集合 $\operatorname{Fix}(g) = \mathbb{N} \setminus \operatorname{supp}(g)$ 是**余有限集（cofinite set）**。
   由于自由超滤子包含一切余有限集，必有 $\operatorname{Fix}(g) \in \mathcal{U}$。
   对任意 $A \in \mathcal{U}$，$A \cap \operatorname{Fix}(g) \in \mathcal{U}$。因 $g$ 在 $\operatorname{Fix}(g)$ 上恒等，有
   $$gA \supseteq g(A \cap \operatorname{Fix}(g)) = A \cap \operatorname{Fix}(g) \in \mathcal{U} \implies gA \in \mathcal{U}.$$
   这表明每个自由超滤子均对所有 $g \in G$ 严格不变！

**结论**：该例的不动记录空间严格等于 Stone-Čech 紧化中的全部自由超滤子集合（即日冕空间）：
$$R_\infty(X)^G = \beta\mathbb{N} \setminus \mathbb{N} = \mathbb{N}^*.$$
在子空间拓扑下，$R_\infty(X)^G$ 同胚于标准的 Cantor-型连通度为零的紧 Hausdorff 空间 $\mathbb{N}^*$（其基数为 $2^{2^{\aleph_0}} > 0$），而 $\eta_{\infty, X}(X^G) = \varnothing$。

---

## 三、 乘积比较

### 3.1 $\Pi_{(X_i)}$ 的良定义、连续性与全满射判定

#### (1) 空指标族
当 $I = \varnothing$ 时，依约定 $\prod_{i \in \varnothing} X_i = \{*\}$，平凡群作用下 $\{*\}^G = \{*\}$。
$R_\infty(\{*\})^G = \{*\}$，右端空积 $\prod_{i \in \varnothing} R_\infty(X_i)^G = \{*\}$。映射 $\Pi_\varnothing: \{*\} \to \{*\}$ 为单点间的唯一同胚，显然良定、连续且为双射。

#### (2) 任意指标族 $I$ 的良定义性与连续性
设 $I$ 任意。
- **良定义性**：对任意 $i \in I$，坐标投射 $p_i: \prod_{j \in I} X_j \to X_i$ 是 $G$ 等变的：$p_i(gx) = gx_i = gp_i(x)$。
  由第 1.2 节的映射相容性，$R_\infty(p_i)$ 亦为 $G$ 等变映射：$g \cdot (R_\infty(p_i)r) = R_\infty(p_i)(g \cdot r)$。
  若 $r \in R_\infty(\prod X_i)^G$，则 $g \cdot r = r$，从而 $g \cdot (R_\infty(p_i)r) = R_\infty(p_i)r$，即 $R_\infty(p_i)r \in R_\infty(X_i)^G$。故映射目标正确，$\Pi_{(X_i)}$ 良定。
- **连续性**：右端空间取乘积拓扑，连续性等价于每个分量映射 $\pi_i \circ \Pi_{(X_i)} = R_\infty(p_i)$ 均连续。
  目标空间 $R_\infty(X_i)^G$ 的子基开集为 $V_{n, f, j} = \{s : s_n(f) = j\}$（其中 $f: X_i \to [n]$）。其在 $R_\infty(p_i)$ 下的原象为：
  $$\{r \in R_\infty(\prod X_i)^G : r_n(f \circ p_i) = j\}.$$
  由于 $f \circ p_i: \prod X_i \to [n]$ 是合法的有限测试映射，该原象正是定义域中的子基开集。故各分量映射连续，$\Pi_{(X_i)}$ 连续。

#### (3) 全满射性判定
**结论**：**$\Pi_{(X_i)}$ 对任意群 $G$ 及任意集合指标族 $(X_i)_{i \in I}$ 恒为满射**。

**完整证明**：
1. 若存在某个 $i \in I$ 使得 $X_i = \varnothing$，则 $\prod_{i \in I} X_i = \varnothing$。此时定义域 $R_\infty(\varnothing)^G = \varnothing$，而右端因含有因子 $R_\infty(X_i)^G = \varnothing$ 亦为空积 $\varnothing$。空映射 $\varnothing \to \varnothing$ 是平凡满射。
2. 若存在某个 $i \in I$ 使得 $R_\infty(X_i)^G = \varnothing$，则右端直接为 $\varnothing$，映射亦平凡为满射。
3. 现设对所有 $i \in I$ 均有 $R_\infty(X_i)^G \ne \varnothing$。
   任取目标元素 $(\mathcal{U}_i)_{i \in I} \in \prod_{i \in I} R_\infty(X_i)^G$。
   - **两因子张量积构造**：
     对任意两个 $G$ 集合 $X, Y$ 及不动超滤子 $\mathcal{U} \in R_\infty(X)^G, \mathcal{V} \in R_\infty(Y)^G$，定义 Fubini/张量积 $\mathcal{U} \otimes \mathcal{V} \subseteq \mathcal{P}(X \times Y)$：
     $$W \in \mathcal{U} \otimes \mathcal{V} \iff \{x \in X : W_x \in \mathcal{V}\} \in \mathcal{U}, \quad \text{其中 } W_x = \{y \in Y : (x, y) \in W\}.$$
     这是 $X \times Y$ 上的超滤子。检验对角 $G$ 作用下的不变性：
     对任意 $g \in G$，$(gW)_x = g(W_{g^{-1}x})$。由 $\mathcal{V}$ 的 $G$ 不变性，$g(W_{g^{-1}x}) \in \mathcal{V} \iff W_{g^{-1}x} \in \mathcal{V}$。
     令 $A = \{x' \in X : W_{x'} \in \mathcal{V}\}$，则 $\{x : (gW)_x \in \mathcal{V}\} = gA$。
     再由 $\mathcal{U}$ 的 $G$ 不变性，$gA \in \mathcal{U} \iff A \in \mathcal{U}$。
     故 $gW \in \mathcal{U} \otimes \mathcal{V} \iff W \in \mathcal{U} \otimes \mathcal{V}$，即 $\mathcal{U} \otimes \mathcal{V} \in R_\infty(X \times Y)^G$。
     且容易直接核验其在两坐标上的投射恰为 $\mathcal{U}$ 与 $\mathcal{V}$。
   - **有限指标集的满射性**：
     通过归纳法，上述张量积立即可推广至任意有限指标集 $J \subset I$，证明有限乘积比较映射必满。
   - **向任意无限指标族推广**：
     令 $Z = \prod_{i \in I} X_i$。对任意有限子集 $J \subseteq I$，定义闭子集
     $$K_J = \bigl\{ \mathcal{W} \in R_\infty(Z)^G : \forall j \in J,\ R_\infty(p_j)\mathcal{W} = \mathcal{U}_j \bigr\}.$$
     将全空间拆分为两项乘积 $Z = (\prod_{j \in J} X_j) \times (\prod_{i \notin J} X_i)$。
     由有限情形，$X_J$ 上存在投射为 $(\mathcal{U}_j)_{j \in J}$ 的不动超滤子 $\mathcal{W}_J$。
     对于余因子 $X_{I \setminus J} = \prod_{i \notin J} X_i$：任取有限生成子群 $H \le G$，因对每个 $i \notin J$ 均有 $R_\infty(X_i)^G \ne \varnothing \implies X_i^H \ne \varnothing$（由第 2.2 节定理），故 $\prod_{i \notin J} X_i^H \ne \varnothing$。这保证了在 $X_{I \setminus J}$ 上由有限生成子群不动点生成的滤子具有有限交性质，从而由第 2.2 节的构造，$R_\infty(X_{I \setminus J})^G \ne \varnothing$。
     取其中的任一不动超滤子 $\mathcal{V}$，作两因子张量积 $\mathcal{W}_J \otimes \mathcal{V} \in R_\infty(Z)^G$，其在 $J$ 上的投射恰为 $(\mathcal{U}_j)_{j \in J}$。
     这证明：**对任意有限子集 $J \subseteq I$，$K_J \ne \varnothing$**。
   - 由于 $R_\infty(Z)^G$ 是紧 Hausdorff 空间，闭集族 $\{K_{\{i\}} : i \in I\}$ 具有有限交性质（$\bigcap_{j \in J} K_{\{j\}} = K_J \ne \varnothing$），由紧性必有：
     $$\bigcap_{i \in I} K_{\{i\}} \ne \varnothing.$$
     该交集中的任意超滤子 $\mathcal{W}$ 均满足 $\Pi_{(X_i)}(\mathcal{W}) = (\mathcal{U}_i)_{i \in I}$。全满射性证毕。$\blacksquare$

---

### 3.2 平凡群下两集合比较映射为单射的充要条件

设 $G = \{e\}$。此时比较映射即为经典的 Stone-Čech 乘积映射：
$$\Pi_{X, Y}: \beta(X \times Y) \longrightarrow \beta X \times \beta Y.$$

**定理**：$\Pi_{X, Y}$ 为单射的充要条件为：**$X = \varnothing$ 或 $Y = \varnothing$，或者 $X$ 与 $Y$ 中至少有一个是有限集合**。

**证明**：
- **充分性**：
  1. 若 $X = \varnothing$ 或 $Y = \varnothing$，则 $X \times Y = \varnothing$，映射两端皆为空集，空映射为单射。
  2. 若 $X$ 为非空有限集合，则 $X \times Y = \bigsqcup_{x \in X} (\{x\} \times Y)$ 是离散拓扑空间的有限拓扑和。由于 Stone-Čech 紧化与有限拓扑和交换：
     $$\beta(X \times Y) = \beta\Bigl(\bigsqcup_{x \in X} Y\Bigr) \cong \bigsqcup_{x \in X} \beta Y = X \times \beta Y = \beta X \times \beta Y.$$
     此时 $\Pi_{X, Y}$ 为拓扑同胚，自然为单射（双射）。同理，若 $Y$ 为非空有限集亦然。
- **必要性（若 $X, Y$ 均无限，则必非单射）**：
  若 $X, Y$ 均为无限集，则存在可数无限子集 $A \subseteq X, B \subseteq Y$。不妨建立双射 $A \cong \mathbb{N}, B \cong \mathbb{N}$。
  取 $\mathbb{N}$ 上的任意自由超滤子 $\mathcal{U} \in \beta\mathbb{N} \setminus \mathbb{N}$。
  在 $X \times Y$ 上构造两个超滤子：
  1. **对角支撑超滤子 $\mathcal{W}_1$**：令对角线 $\Delta = \{(n, n) \in X \times Y : n \in \mathbb{N}\}$。令 $\delta: \mathbb{N} \to \Delta \subset X \times Y$ 为 $\delta(n) = (n, n)$。定义 $\mathcal{W}_1 = \delta_*(\mathcal{U})$。显然 $\Delta \in \mathcal{W}_1$。且因 $p_X \circ \delta = \operatorname{id}_\mathbb{N}$，其在两坐标上的投射均为 $\mathcal{U}$。
  2. **张量积超滤子 $\mathcal{W}_2$**：定义 $\mathcal{W}_2 = \mathcal{U} \otimes \mathcal{U}$。同样，其两坐标投射亦均为 $\mathcal{U}$。
  考察对角线 $\Delta$ 是否属于 $\mathcal{W}_2$：
  $$\Delta \in \mathcal{W}_2 \iff \{n \in \mathbb{N} : \Delta_n \in \mathcal{U}\} \in \mathcal{U}.$$
  然而对任意固定的 $n \in \mathbb{N}$，切片 $\Delta_n = \{m \in \mathbb{N} : (n, m) \in \Delta\} = \{n\}$ 是单元素集。由于 $\mathcal{U}$ 为自由超滤子，其不包含任何单元素有限集，故 $\Delta_n \notin \mathcal{U}$ 恒成立。
  因此 $\{n \in \mathbb{N} : \Delta_n \in \mathcal{U}\} = \varnothing \notin \mathcal{U}$，从而 $\Delta \notin \mathcal{W}_2$。
  由于 $\Delta \in \mathcal{W}_1$ 而 $\Delta \notin \mathcal{W}_2$，必有 $\mathcal{W}_1 \ne \mathcal{W}_2$。
  然而 $\Pi_{X, Y}(\mathcal{W}_1) = (\mathcal{U}, \mathcal{U}) = \Pi_{X, Y}(\mathcal{W}_2)$。
  这证明 $\Pi_{X, Y}$ 绝非单射。充要性证毕。$\blacksquare$

---

### 3.3 任意群作用下的两个全称命题判定

#### 命题 1：若 $X, Y$ 至少一个有限，则两因子的比较映射为双射。
**判定结论**：**成立（真命题）**。

**证明**：
若 $X = \varnothing$ 或 $Y = \varnothing$，两端皆为空集，空映射为双射。
下设 $X$ 为非空有限 $G$ 集合，$Y$ 为任意 $G$ 集合。
由第 3.2 节的证明，$X \times Y$ 是 $Y$ 的有限个不相交拷贝的并，故全空间上的 Stone-Čech 乘积映射
$$\Pi_{X, Y}: R_\infty(X \times Y) \longrightarrow R_\infty(X) \times R_\infty(Y)$$
本身就是拓扑同胚（集合双射）。
且由第 3.1 节，$\Pi_{X, Y}$ 是 $G$ 等变映射。
对于任意群 $G$ 以及两个 $G$ 集合之间的 $G$ 等变双射 $\Phi: M \to N$，其逆映射 $\Phi^{-1}: N \to M$ 同样是 $G$ 等变的。
因此，$\Phi$ 诱导不动点子集间的限制映射 $\Phi|_{M^G}: M^G \to N^G$ 必为严格的双射：
- 若 $m \in M^G$，等变性保证 $\Phi(m) \in N^G$；
- 若 $n \in N^G$，$\Phi^{-1}(n) \in M^G$，且 $\Phi(\Phi^{-1}(n)) = n$；
- 单射性由原映射的单射性直接继承。
因此，限制在不动记录空间上的映射
$$\Pi_{X, Y}: R_\infty(X \times Y)^G \longrightarrow R_\infty(X)^G \times R_\infty(Y)^G$$
**必然是双射**。同理，当 $Y$ 有限时结论完全对称。命题 1 得证。$\blacksquare$

---

#### 命题 2：若 $X^G = Y^G = \varnothing$，则两因子的比较映射为单射。
**判定结论**：**不成立（假命题）**。

**证明（显式反例）**：
取群 $G = S_{<\infty}(\mathbb{N})$（即全有限对称群）。
取 $X = \mathbb{N}$，$Y = \mathbb{N}$，均为自然置换作用的 $G$ 集合。
1. **核验前提条件**：
   对任何 $n \in \mathbb{N}$，对换 $(
$n\ n+1) \in G$ 均满足 $(n\ n+1)n = n+1 \ne n$。因此：
   $$X^G = Y^G = \varnothing,$$
   命题的前提条件严格满足。
2. **两端不动记录空间的非空性**：
   由第 2.3 节的证明，$R_\infty(X)^G = R_\infty(Y)^G = \beta\mathbb{N} \setminus \mathbb{N} = \mathbb{N}^*$。
   任取一个自由超滤子 $\mathcal{U} \in \mathbb{N}^*$。
3. **构造 $R_\infty(X \times Y)^G$ 中的两个不同不动记录**：
   在积集 $\mathbb{N} \times \mathbb{N}$ 上构造两个超滤子：
   - **对角超滤子** $\mathcal{W}_1 = \delta_*(\mathcal{U})$，其中 $\delta: \mathbb{N} \to \mathbb{N} \times \mathbb{N},\ n \mapsto (n, n)$。
     由于对角映射 $\delta$ 是 $G$ 等变的（$\delta(gn) = (gn, gn) = g\delta(n)$），$\mathcal{W}_1$ 自动继承了 $\mathcal{U}$ 的 $G$ 不变性，即 $\mathcal{W}_1 \in R_\infty(X \times Y)^G$。
     其两坐标投射满足 $R_\infty(p_X)\mathcal{W}_1 = \mathcal{U}$ 及 $R_\infty(p_Y)\mathcal{W}_1 = \mathcal{U}$。
     此外，对角线集合 $\Delta = \{(n, n) : n \in \mathbb{N}\}$ 满足 $\delta^{-1}(\Delta) = \mathbb{N} \in \mathcal{U}$，故：
     $$\Delta \in \mathcal{W}_1.$$
   - **张量积超滤子** $\mathcal{W}_2 = \mathcal{U} \otimes \mathcal{U}$。
     由第 3.1 节已证结论，任意两个 $G$ 不变超滤子的张量积在对角作用下恒为 $G$ 不变的，故 $\mathcal{W}_2 \in R_\infty(X \times Y)^G$。
     其两坐标投射同样满足 $R_\infty(p_X)\mathcal{W}_2 = \mathcal{U}$ 及 $R_\infty(p_Y)\mathcal{W}_2 = \mathcal{U}$。
     但对任意 $n \in \mathbb{N}$，单点切片 $\Delta_n = \{m : (n, m) \in \Delta\} = \{n\}$ 是单点有限集，自由超滤子不包含任何有限集，故 $\Delta_n \notin \mathcal{U}$。于是 $\{n \in \mathbb{N} : \Delta_n \in \mathcal{U}\} = \varnothing \notin \mathcal{U}$，即：
     $$\Delta \notin \mathcal{W}_2.$$
4. **单射性失效**：
   由于 $\Delta \in \mathcal{W}_1$ 而 $\Delta \notin \mathcal{W}_2$，两者为不同的完整不动记录：
   $$\mathcal{W}_1 \ne \mathcal{W}_2 \in R_\infty(X \times Y)^G.$$
   然而它们在比较映射下的像完全相同：
   $$\Pi_{X, Y}(\mathcal{W}_1) = (\mathcal{U}, \mathcal{U}) = \Pi_{X, Y}(\mathcal{W}_2).$$
   这证明即便 $X^G = Y^G = \varnothing$，两因子的比较映射 $\Pi_{X, Y}$ 也**不必为单射**。命题 2 为假。$\blacksquare$

---

## 结论汇总

| 目标分类 | 核心对象 / 命题 | 最终结论与准确判据 |
| :--- | :--- | :--- |
| **目标 1** | $R_m(X)$ 结构分类 | • $X=\varnothing \implies \varnothing$；<br>• $m=1 \implies \{*\}$；<br>• $m=2 \implies$ 补自对偶指标函数（基数 $2^{2^{\|X\|-1}-1}$）；<br>• $m\ge 3 \implies$ 超滤子空间 $\beta X$。 |
| | 有限 $G$ 集合的 $R_m(X)^G$ | • $m=1$：恒为 $1$；<br>• $m=2$：无自补轨道时为 $2^{(N_{\mathcal{O}}/2)-1}$，有自补轨道时为 $0$；<br>• $m\ge 3$：基数恰为 $\|X^G\|$，与 $X^G$ 自然等同。 |
| | 有限层不动记录延拓范围 | • $m\ge 3$：始终唯一延拓（双射）；<br>• $m=2$：仅主超滤子 $\eta_{2,X}(X^G)$ 可延拓；<br>• $m=1$：$X^G \ne \varnothing$ 时可延拓（解数为 $\|X^G\|$）。 |
| **目标 2** | 内在拓扑分类与存在性 | $R_\infty(X)^G \cong (\beta X)^G \cong \operatorname{Stone}(\mathcal{P}(X)/\mathcal{I}_G)$（紧 Hausdorff 空间）；非空充要条件为全集不能被有限个轨道对称差覆盖。 |
| | 闭包与等式分类定理 | $\overline{\eta_{\infty,X}(X^G)} = \widehat{X^G} \cong \beta(X^G)$；对每个 $G$ 集合均等于 $R_\infty(X)^G$ 的充要条件是 **$G$ 为有限生成群**。 |
| | 可数反例与不动记录 | $G = S_{<\infty}(\mathbb{N})$ 作用于 $X = \mathbb{N}$，满足 $X^G = \varnothing$；其不动记录全体严格等于日冕空间 $R_\infty(X)^G = \beta\mathbb{N} \setminus \mathbb{N} = \mathbb{N}^*$。 |
| **目标 3** | 全满射性判定 | 对任意群 $G$ 及任意指标族 $(X_i)_{i\in I}$，$\Pi_{(X_i)}$ **总为满射**。 |
| | 平凡群单射充要条件 | $X = \varnothing$ 或 $Y = \varnothing$，或两集合中**至少有一个有限集合**。 |
| | 任意群全称命题 1 | 「若 $X,Y$ 至少一个有限，则比较映射为双射」**成立（真）**。 |
| | 任意群全称命题 2 | 「若 $X^G=Y^G=\varnothing$，则比较映射为单射」**不成立（假）**。 |
