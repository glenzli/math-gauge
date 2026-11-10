下面在 $\mathsf{ZFC}$ 框架下对三个目标给出完整的分类、构造与严格证明。约定 $0 \le n \le m$ 表示满足 $n \le m$ 的非负整数 $n \in \mathbb{Z}_{\ge 0}$（当 $m=\infty$ 时 $n$ 取遍全体非负整数 $\mathbb{Z}_{\ge 0}$）。

---

## 1. 截断及其相容关系

### 1.1 $R_m(X)$ 的完全分类

#### 情形 A：空底集 $X = \varnothing$
**结论：** 对任意 $m \in \mathbb{Z}_{\ge 1} \cup \{\infty\}$，均有
$$R_m(\varnothing) = \varnothing.$$
**证明：** 当 $n = 0$ 时，$[0] = \varnothing$，映射集合 $\operatorname{Map}(\varnothing, [0]) = \{\mathrm{id}_\varnothing\}$ 是单点集，而陪域 $[0] = \varnothing$。由集合论基本性质，不存在从非空集合到空集的映射 $r_0 : \operatorname{Map}(\varnothing, [0]) \to [0]$。故对一切 $m \ge 1$ 均有 $R_m(\varnothing) = \varnothing$。$\blacksquare$

---

#### 情形 B：非空底集 $X \ne \varnothing$
当 $X \ne \varnothing$ 时，$\operatorname{Map}(X, [0]) = \varnothing$，从而每个记录 $r \in R_m(X)$ 的第 $0$ 层分量 $r_0 : \varnothing \to \varnothing$ 恒为唯一的空映射，且涉及 $n=0$ 或 $k=0$ 的相容条件自动空真（因不存在 $f : X \to [0]$ 或 $a : [n] \to [0]$，$n \ge 1$）。以下对参数 $m$ 分三类给出分类：

1. **当 $m = 1$ 时：$R_1(X)$ 为单点集。**
   - **构造与证明：** $[1] = \{0\}$ 为单点集，$\operatorname{Map}(X, [1]) = \{c_0\}$（常值 $0$ 映射）亦为单点集，故 $r_1 : \operatorname{Map}(X, [1]) \to [1]$ 唯一（即 $r_1(c_0) = 0$），相容关系 $a(r_1(f)) = r_1(a \circ f)$ 恒为 $0 = 0$。因此 $R_1(X) = \{r^{(1)}\}$ 是单点集。

2. **当 $m = 2$ 时：$R_2(X)$ 与 $\mathcal{P}(X)$ 上的自对偶（保补）正规集族集合 $\mathcal{S}(X)$ 自然双射。**
   - 定义
     $$\mathcal{S}(X) := \bigl\{ \mathcal{F} \subseteq \mathcal{P}(X) \;\big|\; X \in \mathcal{F},\text{ 且 }\forall A \subseteq X,\; A \in \mathcal{F} \Longleftrightarrow (X \setminus A) \notin \mathcal{F} \bigr\}.$$
   - **分类定理：** 映射
     $$\Psi_2 : R_2(X) \longrightarrow \mathcal{S}(X), \qquad r \longmapsto \mathcal{F}_r := \bigl\{ A \subseteq X \;\big|\; r_2(\mathbf{1}_A) = 1 \bigr\}$$
     是双射（其中 $\mathbf{1}_A : X \to [2]$ 为 $A$ 的特征函数），其逆映射 $\Phi_2(\mathcal{F}) = r^\mathcal{F}$ 由 $r^\mathcal{F}_0 = \mathrm{id}_\varnothing$、$r^\mathcal{F}_1(c_0) = 0$ 及 $r^\mathcal{F}_2(f) = 1 \iff f^{-1}(\{1\}) \in \mathcal{F}$ 给出。
   - **证明：** 对 $r \in R_2(X)$，$r_0, r_1$ 唯一确定，且 $k=1$ 时的相容条件在 $[1]=\{0\}$ 中恒成立。
     - 当 $n=1, k=2$ 时，取 $f = c_0 : X \to [1]$ 及 $a_c : [1] \to [2]$（$a_c(0) = c \in \{0, 1\}$），得 $r_2(\mathbf{1}_\varnothing) = 0$ 与 $r_2(\mathbf{1}_X) = 1$（从而 $\varnothing \notin \mathcal{F}_r, X \in \mathcal{F}_r$）。
     - 当 $n=2, k=2$ 时，$\operatorname{Map}([2], [2])$ 仅含四个映射：$\mathrm{id}_{[2]}$、常值映射 $0$、常值映射 $1$ 以及对换 $\sigma(x) = 1 - x$。前三个映射给出的条件已被 $r_2(\mathbf{1}_\varnothing)=0, r_2(\mathbf{1}_X)=1$ 涵盖，而 $a = \sigma$ 给出
       $$1 - r_2(\mathbf{1}_A) = r_2(1 - \mathbf{1}_A) = r_2(\mathbf{1}_{X \setminus A}), \qquad \forall A \subseteq X,$$
       这恰等价于 $A \in \mathcal{F}_r \iff (X \setminus A) \notin \mathcal{F}_r$。
     故 $\Psi_2$ 与 $\Phi_2$ 互逆。$\blacksquare$

3. **当 $3 \le m \le \infty$ 时：$R_m(X)$ 与 $X$ 上的超滤子集合 $\beta X$ 自然双射。**
   - **分类定理：** 对任意 $3 \le m \le \infty$，映射
     $$\Psi_m : R_m(X) \longrightarrow \beta X, \qquad r \longmapsto \mathcal{U}_r := \bigl\{ A \subseteq X \;\big|\; r_2(\mathbf{1}_A) = 1 \bigr\}$$
     是双射；其逆映射 $\Phi_m : \beta X \to R_m(X)$ 将超滤子 $\mathcal{U} \in \beta X$ 映为 $r^\mathcal{U}$，其中 $r^\mathcal{U}_0 = \mathrm{id}_\varnothing$，且对 $1 \le n \le m$ 及 $f : X \to [n]$，
     $$r^\mathcal{U}_n(f) = \text{使 } f^{-1}(\{i\}) \in \mathcal{U} \text{ 的唯一指标 } i \in [n].$$
   - **证明：**
     1. **由 $r \in R_m(X)$ 导出 $\mathcal{U}_r$ 是超滤子且唯一决定 $r$：**
        由 $m=2$ 的情形已得 $\varnothing \notin \mathcal{U}_r, X \in \mathcal{U}_r$，且 $A \in \mathcal{U}_r \iff (X \setminus A) \notin \mathcal{U}_r$。
        设 $A, B \subseteq X$ 不交。因为 $m \ge 3$，定义 $f : X \to [3]$ 为：在 $A$ 上取 $1$，在 $B$ 上取 $2$，在 $X \setminus (A \cup B)$ 上取 $0$。对每个 $i \in [n]$（$1 \le n \le m$），记 $\delta_i : [n] \to [2]$ 为单点 $\{i\}$ 的特征函数（$\delta_i(j) = 1 \iff j = i$）。由相容条件：
        $$\delta_i(r_n(f)) = r_2(\delta_i \circ f) = r_2\bigl(\mathbf{1}_{f^{-1}(\{i\})}\bigr).$$
        这表明对任意 $1 \le n \le m$ 及 $f : X \to [n]$，有
        $$r_n(f) = i \Longleftrightarrow f^{-1}(\{i\}) \in \mathcal{U}_r.$$
        这直接证明了 $r$ 被 $\mathcal{U}_r$ 唯一决定（即 $\Psi_m$ 为单射）。特别地，对上述三值映射 $f : X \to [3]$，因为 $r_3(f) \in \{0, 1, 2\}$ 恰取一个值，故 $f^{-1}(\{0\}) = X \setminus (A \cup B)$、$f^{-1}(\{1\}) = A$、$f^{-1}(\{2\}) = B$ 三者中恰有一个属于 $\mathcal{U}_r$。利用补集性质，对任意不交的 $A, B \subseteq X$：
        - 若 $A \in \mathcal{U}_r$ 且 $B \subseteq X \setminus A$，则 $r_3(f) = 1 \ne 0$，故 $X \setminus (A \cup B) \notin \mathcal{U}_r$，即 $A \cup B \in \mathcal{U}_r$（向上封闭性）；
        - 若 $D_1, D_2 \in \mathcal{U}_r$，取不交集 $A = X \setminus D_1 \notin \mathcal{U}_r$ 与 $B = D_1 \setminus D_2 \subseteq X \setminus D_2 \notin \mathcal{U}_r$，则 $r_3(f) \ne 1, 2$，必有 $r_3(f) = 0$，即 $D_1 \cap D_2 = X \setminus (A \cup B) \in \mathcal{U}_r$（有限交封闭性）。
        因此 $\mathcal{U}_r \in \beta X$ 是 $X$ 上的超滤子。
     2. **任意超滤子 $\mathcal{U} \in \beta X$ 给出的 $r^\mathcal{U}$ 属于 $R_m(X)$：**
        对任意 $1 \le n \le m$ 和 $f : X \to [n]$，$X = \bigsqcup_{i=0}^{n-1} f^{-1}(\{i\})$ 是 $X$ 的有限分划。由超滤子的有限可加性，存在唯一的 $i \in [n]$ 使得 $f^{-1}(\{i\}) \in \mathcal{U}$，故 $r^\mathcal{U}_n(f) = i$ 良定义。对任意 $a : [n] \to [k]$，记 $j = a(i)$，则 $f^{-1}(\{i\}) \subseteq (a \circ f)^{-1}(\{j\})$。由超滤子向上封闭性知 $(a \circ f)^{-1}(\{j\}) \in \mathcal{U}$，故 $r^\mathcal{U}_k(a \circ f) = j = a(r^\mathcal{U}_n(f))$。因此 $r^\mathcal{U} \in R_m(X)$，且 $\Psi_m(\Phi_m(\mathcal{U})) = \mathcal{U}$。$\blacksquare$

---

### 1.2 截断映射 $q_{m,k}$ 的像与各纤维

设 $m \ge k \ge 1$。
- **若 $X = \varnothing$：** $q_{m,k} : \varnothing \to \varnothing$ 为空映射，像为 $\varnothing$，无非空纤维。
- **若 $X \ne \varnothing$：**
  1. **当 $m = k$ 时：** $q_{m,m} = \mathrm{id}_{R_m(X)}$ 为恒等双射，像为 $R_m(X)$，每个元素 $r \in R_m(X)$ 的纤维为单点集 $\{r\}$。
  2. **当 $m \ge 2, k = 1$ 时：** 因为 $X \ne \varnothing$（取 $x_0 \in X$ 即有 $\eta_{m,X}(x_0) \in R_m(X)$），$R_m(X) \ne \varnothing$ 而 $R_1(X) = \{r^{(1)}\}$ 为单点集。故 $q_{m,1}$ 是满射，像为 $R_1(X)$，唯一纤维 $q_{m,1}^{-1}(r^{(1)}) = R_m(X)$（当 $m=2$ 时同构于 $\mathcal{S}(X)$，当 $m \ge 3$ 时同构于 $\beta X$）。
  3. **当 $m \ge 3, k = 2$ 时：** 在自然双射 $\Psi_m : R_m(X) \xrightarrow{\sim} \beta X$ 与 $\Psi_2 : R_2(X) \xrightarrow{\sim} \mathcal{S}(X)$ 下，$\Psi_2 \circ q_{m,2} \circ \Phi_m$ 恰为包含映射 $\beta X \hookrightarrow \mathcal{S}(X)$。因此：
     - $q_{m,2}$ 是**单射**；
     - $q_{m,2}$ 的**像**为 $\bigl\{ r \in R_2(X) \;\big|\; \mathcal{F}_r \in \beta X \bigr\} = \bigl\{ r \in R_2(X) \;\big|\; \forall A, B \subseteq X,\; r_2(\mathbf{1}_{A \cap B}) = r_2(\mathbf{1}_A) r_2(\mathbf{1}_B) \bigr\}$（当 $1 \le |X| \le 2$ 时 $\beta X = \mathcal{S}(X)$，故 $q_{m,2}$ 为双射；当 $|X| \ge 3$ 时 $q_{m,2}$ 不满射）；
     - 对 $r \in R_2(X)$，**纤维** $q_{m,2}^{-1}(r)$ 在 $\mathcal{F}_r \in \beta X$ 时为单点集 $\{\Phi_m(\mathcal{F}_r)\}$，在 $\mathcal{F}_r \notin \beta X$ 时为 $\varnothing$。
  4. **当 $m \ge k \ge 3$ 时：** 在分类 $\Psi_m, \Psi_k$ 下，$\Psi_k \circ q_{m,k} \circ \Phi_m = \mathrm{id}_{\beta X}$。因此 $q_{m,k} : R_m(X) \to R_k(X)$ 是**双射**，像为全部 $R_k(X)$，每个 $r \in R_k(X)$ 的纤维为单点集 $\{\Phi_m(\mathcal{U}_r)\}$。

---

### 1.3 与集合映射 $h : X \to Y$ 的相容性

对任意映射 $h : X \to Y$：
1. **良定义与函子性：** 对 $r \in R_m(X)$、$f : Y \to [n]$ 和 $a : [n] \to [k]$，
   $$a\bigl((R_m(h)r)_n(f)\bigr) = a\bigl(r_n(f \circ h)\bigr) = r_k(a \circ f \circ h) = (R_m(h)r)_k(a \circ f),$$
   故 $R_m(h) : R_m(X) \to R_m(Y)$ 良定义。且对 $h' : Y \to Z$，有 $\bigl(R_m(h' \circ h)r\bigr)_n(f) = r_n(f \circ h' \circ h) = \bigl(R_m(h')(R_m(h)r)\bigr)_n(f)$，以及 $R_m(\mathrm{id}_X) = \mathrm{id}_{R_m(X)}$，故 $R_m(-)$ 是协变函子。
2. **与截断及点值记录的相容性：** 对 $m \ge k \ge 1$ 及 $x \in X$，直接由定义逐点核验得交换关系：
   $$q_{m,k} \circ R_m(h) = R_k(h) \circ q_{m,k}, \qquad R_m(h) \circ \eta_{m,X} = \eta_{m,Y} \circ h, \qquad q_{m,k} \circ \eta_{m,X} = \eta_{k,X}.$$
3. **在分类下的显式形式：**
   - 若 $X = \varnothing$，$R_m(h)$ 为空映射 $\varnothing \to R_m(Y)$。
   - 若 $X \ne \varnothing$（此时必有 $Y \ne \varnothing$）：
     - $m = 1$ 时，$R_1(h)$ 为单点集之间的唯一映射；
     - $m = 2$ 时，因 $\mathbf{1}_B \circ h = \mathbf{1}_{h^{-1}(B)}$（$B \subseteq Y$），$R_2(h)$ 在 $\mathcal{S}(-)$ 下对应前推映射 $h_* : \mathcal{S}(X) \to \mathcal{S}(Y)$，$h_*(\mathcal{F}) = \{B \subseteq Y \mid h^{-1}(B) \in \mathcal{F}\}$；
     - $3 \le m \le \infty$ 时，$R_m(h)$ 在 $\beta(-)$ 下对应超滤子的前推映射 $h_* : \beta X \to \beta Y$，$h_*(\mathcal{U}) = \{B \subseteq Y \mid h^{-1}(B) \in \mathcal{U}\}$；点值映射 $\eta_{m,X}(x)$ 对应以 $x$ 为生成元的主超滤子 $\mathcal{U}_x = \{A \subseteq X \mid x \in A\}$。

---

### 1.4 有限 $G$ 集合 $X$ 上 $R_m(X)^G$ 的存在判准、精确基数与限制映射

设 $X$ 为有限 $G$ 集合。

#### （1）当 $X = \varnothing$ 时
对所有 $1 \le m \le \infty$，$R_m(\varnothing)^G = \varnothing$（非空判准永假，基数为 $0$），各限制映射 $q_{m,k}^G$ 均为空映射。

#### （2）当 $X \ne \varnothing$ 为非空有限 $G$ 集合时
- **第 $m = 1$ 层：**
  - **存在判准：** 恒非空（因 $X \ne \varnothing$）。
  - **精确基数：** $|R_1(X)^G| = 1$（$R_1(X)^G = \{r^{(1)}\}$）。
- **第 $m = 2$ 层：**
  - $G$ 在 $R_2(X) \cong \mathcal{S}(X)$ 上的作用为 $(g \cdot r)_2(\mathbf{1}_A) = r_2(\mathbf{1}_A \circ g_X) = r_2(\mathbf{1}_{g^{-1}A})$，故 $\mathcal{F} \in \mathcal{S}(X)^G$ 当且仅当 $\mathcal{F}$ 是 $G$-不变集族（$A \in \mathcal{F} \iff gA \in \mathcal{F}$）。
  - 记 $\mathcal{P}(X)/G$ 为幂集 $\mathcal{P}(X)$ 在 $G$ 作用下的轨道集合。取补运算 $\tau(A) = X \setminus A$ 与 $G$ 作用交换，故诱导 $\mathcal{P}(X)/G$ 上的对合 $\bar{\tau}([A]) = [X \setminus A]$。元素 $\mathcal{F} \in \mathcal{S}(X)^G$ 恰对应满足 $[X] \in \widetilde{\mathcal{F}}$ 且从每个无序对 $\{[A], [X \setminus A]\}$ 中恰选出一个轨道的集合。
  - **存在判准：** $R_2(X)^G \ne \varnothing$ 当且仅当 $\bar{\tau}$ 在 $\mathcal{P}(X)/G$ 上无不动点，即**不存在 $A \subseteq X$ 和 $g \in G$ 使得 $gA = X \setminus A$**；等价地（由有限集置换的轮换分解），**不存在 $g \in G$ 使得 $g_X$ 在 $X$ 上的每个轮换长度均为偶数**。（若某 $g_X$ 的所有轮换均为偶轮换，在每个轮换上交替取点即得 $gA = X \setminus A$；反之，若 $gA = X \setminus A$，则 $g_X$ 的每个轮换在 $A$ 与 $X \setminus A$ 间交替，长度必为偶数。）
  - **精确基数：**
    $$|R_2(X)^G| = \begin{cases} 0, & \text{若存在 } g \in G \text{ 使 } g_X \text{ 在 } X \text{ 上的轮换全为偶数长}; \\[4pt] 2^{\frac{|\mathcal{P}(X)/G|}{2} - 1}, & \text{若对所有 } g \in G,\; g_X \text{ 在 } X \text{ 上至少有一个奇数长轮换}. \end{cases}$$
    （理由：在第二种情形下，$\bar{\tau}$ 将 $|\mathcal{P}(X)/G|$ 个轨道自由地配成 $|\mathcal{P}(X)/G|/2$ 对互补轨道；除 $\{[\varnothing], [X]\}$ 的取值由 $X \in \mathcal{F}, \varnothing \notin \mathcal{F}$ 唯一固定外，其余 $\frac{|\mathcal{P}(X)/G|}{2} - 1$ 对互补轨道每对恰有 $2$ 种独立选法。）
- **第 $3 \le m \le \infty$ 层：**
  - 因为 $X$ 是有限集，$X$ 上的每个超滤子 $\mathcal{U} \in \beta X$ 均为主超滤子（由 $X = \bigsqcup_{x \in X} \{x\} \in \mathcal{U}$ 及超滤子有限可加性知存在唯一的 $x \in X$ 使 $\{x\} \in \mathcal{U}$，即 $\mathcal{U} = \mathcal{U}_x$）。
  - 因此点值映射 $\eta_{m,X} : X \xrightarrow{\sim} R_m(X)$ 是 $G$-等变双射，取 $G$-不动点得
    $$R_m(X)^G = \eta_{m,X}(X^G) \cong X^G.$$
  - **存在判准：** $R_m(X)^G \ne \varnothing \iff X^G \ne \varnothing$。
  - **精确基数：** $|R_m(X)^G| = |X^G|$。
- **不动集合之间的限制映射 $q_{m,k}^G : R_m(X)^G \to R_k(X)^G$（$X \ne \varnothing$ 有限）：**
  1. 当 $m \ge k \ge 3$ 时，$q_{m,k}^G : R_m(X)^G \xrightarrow{\sim} R_k(X)^G$ 是**双射**（在 $R_m(X)^G \cong X^G$ 下即为 $\mathrm{id}_{X^G}$）；
  2. 当 $m \ge 3, k = 2$ 时，$q_{m,2}^G : R_m(X)^G \to R_2(X)^G$ 是**单射**，其像为 $\eta_{2,X}(X^G)$（即由不动点 $x \in X^G$ 生成的主超滤子所对应的记录）；
  3. 当 $m \ge 3, k = 1$ 时，$q_{m,1}^G : R_m(X)^G \to R_1(X)^G = \{r^{(1)}\}$ 在 $X^G \ne \varnothing$ 时为满射，在 $X^G = \varnothing$ 时为空映射；
  4. 当 $m = 2, k = 1$ 时，$q_{2,1}^G : R_2(X)^G \to R_1(X)^G = \{r^{(1)}\}$ 在 $R_2(X)^G \ne \varnothing$ 时为满射，在 $R_2(X)^G = \varnothing$ 时为空映射。

---

### 1.5 有限层不动记录延拓为完整不动记录的准确范围

由上述分类，对任意 $G$ 集合 $X$ 及有限层 $k \in \mathbb{Z}_{\ge 1}$，截断映射 $q_{\infty, k}^G : R_\infty(X)^G \to R_k(X)^G$ 的延拓性质如下：
1. **层数范围 $k \ge 3$（无条件唯一延拓范围）：** 对**任意** $k \ge 3$ 和任意 $G$ 集合 $X$，$q_{\infty, k}^G : R_\infty(X)^G \to R_k(X)^G$ 恒为**双射**。即每个 $k \ge 3$ 层的不动记录均**存在且唯一**地延拓为完整不动记录 $R_\infty(X)^G$。
2. **第 $k = 2$ 层：** $q_{\infty, 2}^G$ 恒为单射（若延拓存在则唯一）；一个记录 $r \in R_2(X)^G$ 可延拓至 $R_\infty(X)^G$ 的充要条件是 $\mathcal{F}_r = \{A \subseteq X \mid r_2(\mathbf{1}_A) = 1\}$ 构成 $X$ 上的超滤子（即对有限交封闭）。特别地，当 $X$ 为有限 $G$ 集合时，$r \in R_2(X)^G$ 可延拓至 $R_\infty(X)^G$ 当且仅当 $r \in \eta_{2,X}(X^G)$（即 $\mathcal{F}_r$ 是由某个 $G$-不动点 $x \in X^G$ 生成的主超滤子）。
3. **第 $k = 1$ 层：** 当 $X \ne \varnothing$ 时，$R_1(X)^G$ 的唯一元素 $r^{(1)}$ 可延拓至 $R_\infty(X)^G$ 当且仅当 $R_\infty(X)^G \ne \varnothing$（当 $X$ 有限时，这等价于 $X^G \ne \varnothing$），其全体延拓即为整个 $R_\infty(X)^G$。

---

## 2. 完整不动记录的空间

### 2.1 内在拓扑分类与非空充要条件

先确立单个群元素在超滤子空间上的不动点引理。

**引理 2.1（三色引理 / 置换的超滤子不动点）：** 设 $g_X : X \to X$ 是集合 $X$ 上的双射，记其不动点集为 $X^g := \{x \in X \mid gx = x\}$。则对任意超滤子 $\mathcal{U} \in \beta X$，
$$(g_X)_* \mathcal{U} = \mathcal{U} \Longleftrightarrow X^g \in \mathcal{U}.$$
**证明：**
- **充分性：** 若 $X^g \in \mathcal{U}$，因 $g_X$ 在 $X^g$ 上为恒等映射，对任意 $A \subseteq X$ 有 $A \cap X^g = g(A \cap X^g) = gA \cap X^g$。由 $X^g \in \mathcal{U}$ 得
  $$A \in \mathcal{U} \Longleftrightarrow A \cap X^g \in \mathcal{U} \Longleftrightarrow gA \cap X^g \in \mathcal{U} \Longleftrightarrow gA \in \mathcal{U},$$
  即 $(g_X)_* \mathcal{U} = \mathcal{U}$。
- **必要性：** 将 $X \setminus X^g$ 分解为循环群 $\langle g \rangle$ 的轨道之并，每个轨道 $O$ 的基数 $|O| \ge 2$。在 $\mathsf{ZFC}$ 中在每个轨道 $O \subseteq X \setminus X^g$ 中选取一个基点 $x_O \in O$，将 $O$ 分划为三个不交子集 $O = C_0(O) \sqcup C_1(O) \sqcup C_2(O)$：
  - 若 $O$ 无限（$O = \{g^k x_O \mid k \in \mathbb{Z}\}$）或 $|O| = 2d \ge 2$ 为偶数，取 $C_0(O) = \{g^{2j} x_O\}$、$C_1(O) = \{g^{2j+1} x_O\}$、$C_2(O) = \varnothing$；
  - 若 $|O| = 2d + 1 \ge 3$ 为奇数，取 $C_0(O) = \{g^{2j} x_O \mid 0 \le j \le d-1\}$、$C_1(O) = \{g^{2j+1} x_O \mid 0 \le j \le d-1\}$、$C_2(O) = \{g^{2d} x_O\}$。
  容易检验对每个轨道 $O$ 及 $i \in \{0, 1, 2\}$ 均有 $g(C_i(O)) \cap C_i(O) = \varnothing$。令 $B_i := \bigsqcup_{O \subseteq X \setminus X^g} C_i(O)$（$i=0,1,2$），则得到 $X$ 的四分划
  $$X = X^g \sqcup B_0 \sqcup B_1 \sqcup B_2, \qquad g(B_i) \cap B_i = \varnothing \quad (i = 0, 1, 2).$$
  若 $(g_X)_* \mathcal{U} = \mathcal{U}$ 且某 $B_i \in \mathcal{U}$，则 $g(B_i) \in \mathcal{U}$，从而 $\varnothing = B_i \cap g(B_i) \in \mathcal{U}$，矛盾！故 $B_0, B_1, B_2 \notin \mathcal{U}$，由 $X \in \mathcal{U}$ 及超滤子有限可加性必有 $X^g \in \mathcal{U}$。$\blacksquare$

#### （1）$R_\infty(X)^G$ 的内在分类（含拓扑结构）
- 当 $X = \varnothing$ 时，$R_\infty(\varnothing)^G = \varnothing$ 为空拓扑空间。
- 当 $X \ne \varnothing$ 时，在 $R_\infty(X)$ 上，观察映射 $r \mapsto r_n(f)$ 所生成的最弱拓扑以子集
  $$U_{n, f, i} := \{r \in R_\infty(X) \mid r_n(f) = i\} = \bigl\{r \in R_\infty(X) \;\big|\; r_2\bigl(\mathbf{1}_{f^{-1}(\{i\})}\bigr) = 1\bigr\}$$
  为子基。在双射 $\Psi_\infty : R_\infty(X) \xrightarrow{\sim} \beta X$ 下，$U_{n,f,i}$ 恰对应 $\beta X$ 的基本既开又闭集
  $$\widehat{A} := \{\mathcal{U} \in \beta X \mid A \in \mathcal{U}\} \qquad \bigl(A = f^{-1}(\{i\}) \subseteq X\bigr).$$
  因 $\widehat{A} \cap \widehat{B} = \widehat{A \cap B}$ 且 $\beta X \setminus \widehat{A} = \widehat{X \setminus A}$，族 $\{\widehat{A} \mid A \subseteq X\}$ 构成 $\beta X$ 上 Stone–Čech 紧化拓扑的既开又闭基，故 $\Psi_\infty : R_\infty(X) \xrightarrow{\sim} \beta X$ 是**同胚**（特别地，$R_\infty(X)$ 是紧 Hausdorff 全不连通的 Stone 空间）。
- 由引理 2.1，对任意 $r \in R_\infty(X)$，
  $$r \in R_\infty(X)^G \Longleftrightarrow \forall g \in G,\; (g_X)_* \mathcal{U}_r = \mathcal{U}_r \Longleftrightarrow \forall g \in G,\; X^g \in \mathcal{U}_r.$$
  对任意有限子集 $F \subseteq G$，记公共不动点集 $X^F := \bigcap_{g \in F} X^g$（约定 $X^\varnothing = X$）。由此得到由 $X$ 及其 $G$-作用直接构造的内在分类：
  > **定理 2.2（内在分类）：** $R_\infty(X)^G$ 在同胚 $\Psi_\infty$ 下同胚于 $X$ 上包含不动点集族 $\{X^g \mid g \in G\}$ 的全体超滤子所成之紧 Hausdorff Stone 子空间：
  > $$R_\infty(X)^G \cong \bigl\{ \mathcal{U} \in \beta X \;\big|\; \forall g \in G,\; X^g \in \mathcal{U} \bigr\} = \bigcap_{g \in G} \widehat{X^g}.$$
  > 等价地，记 $\mathcal{I}_G := \bigl\{ A \subseteq X \;\big|\; \exists \text{ 有限子集 } F \subseteq G \text{ 使 } A \cap X^F = \varnothing \bigr\}$ 为 $\mathcal{P}(X)$ 的布尔理想，则 $R_\infty(X)^G$ 自然同胚于商布尔代数 $\mathcal{P}(X)/\mathcal{I}_G$ 的 Stone 空间 $\operatorname{Ult}(\mathcal{P}(X)/\mathcal{I}_G)$，其拓扑由既开又闭基 $\bigl\{\widehat{A} \cap R_\infty(X)^G \;\big|\; A \subseteq X\bigr\}$ 生成。

#### （2）$R_\infty(X)^G$ 非空的必要充分条件
> **定理 2.3：** 对任意 $G$ 集合 $X$，
> $$R_\infty(X)^G \ne \varnothing \Longleftrightarrow \text{对 } G \text{ 的每个有限子集 } F \subseteq G,\text{ 均有 } X^F = \bigcap_{g \in F} X^g \ne \varnothing.$$
> （注：当 $X = \varnothing$ 时，取 $F = \varnothing$ 即得 $X^\varnothing = \varnothing$，判准正确给出 $R_\infty(\varnothing)^G = \varnothing$；当 $X \ne \varnothing$ 时，这等价于每个非空有限子集 $F \subseteq G$ 在 $X$ 中有公共不动点。）

**证明：** 在 $\mathsf{ZFC}$ 中由超滤子引理（Ultrafilter Lemma），子集族 $\{X^g \mid g \in G\} \subseteq \mathcal{P}(X)$ 可扩充为 $X$ 上的超滤子 $\mathcal{U} \in \beta X$ 当且仅当该子集族具有**有限交性质（FIP）**，即对任意有限子集 $F \subseteq G$（含 $F = \varnothing$），$\bigcap_{g \in F} X^g = X^F \ne \varnothing$。由定理 2.2 即得结论。$\blacksquare$

---

### 2.2 $\eta_{\infty,X}(X^G)$ 的闭包、相等判准与群的分类

#### （1）$\eta_{\infty,X}(X^G)$ 在 $R_\infty(X)$ 中的闭包
**命题 2.4：** 对任意 $G$ 集合 $X$，$\eta_{\infty,X}(X^G)$ 在 $R_\infty(X)$ 中的闭包为
$$\overline{\eta_{\infty,X}(X^G)} = \widehat{X^G} = \bigl\{ r \in R_\infty(X) \;\big|\; r_2(\mathbf{1}_{X^G}) = 1 \bigr\} \cong \bigl\{ \mathcal{U} \in \beta X \;\big|\; X^G \in \mathcal{U} \bigr\} \cong \beta(X^G)$$
（当 $X^G = \varnothing$ 时为空集；当 $X^G \ne \varnothing$ 时等于包含映射 $i : X^G \hookrightarrow X$ 诱导的像 $R_\infty(i)(R_\infty(X^G))$）。
**证明：** 在 $R_\infty(X) \cong \beta X$ 中，$\mathcal{U} \in \overline{\eta_{\infty,X}(X^G)}$ 当且仅当 $\mathcal{U}$ 的每个基本开邻域 $\widehat{A}$（即 $A \in \mathcal{U}$）都与 $\eta_{\infty,X}(X^G)$ 相交，即 $\forall A \in \mathcal{U},\; A \cap X^G \ne \varnothing$。由于 $\mathcal{U}$ 是超滤子，这等价于 $X^G \in \mathcal{U}$（若 $X^G \notin \mathcal{U}$，则 $A = X \setminus X^G \in \mathcal{U}$ 满足 $A \cap X^G = \varnothing$），即 $\mathcal{U} \in \widehat{X^G}$。$\blacksquare$

#### （2）$\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$ 的必要充分条件
> **定理 2.5：** 对任意给定的 $G$ 集合 $X$，
> $$\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G \Longleftrightarrow \text{存在有限子集 } F \subseteq G \text{ 使得 } X^F = X^G.$$

**证明：**
- **充分性：** 设存在有限子集 $F \subseteq G$ 使得 $X^F = X^G$。对任意 $\mathcal{U} \in R_\infty(X)^G \cong \bigcap_{g \in G} \widehat{X^g}$，对每个 $g \in F$ 均有 $X^g \in \mathcal{U}$。因 $F$ 有限，滤子对有限交封闭，故 $X^G = X^F = \bigcap_{g \in F} X^g \in \mathcal{U}$，即 $\mathcal{U} \in \widehat{X^G} = \overline{\eta_{\infty,X}(X^G)}$。反之 $\overline{\eta_{\infty,X}(X^G)} \subseteq R_\infty(X)^G$ 恒成立。
- **必要性：** 设对任意有限子集 $F \subseteq G$ 均有 $X^F \ne X^G$，即 $X^F \setminus X^G \ne \varnothing$。因对任意有限子集 $F_1, F_2 \subseteq G$，
  $$(X^{F_1} \setminus X^G) \cap (X^{F_2} \setminus X^G) = X^{F_1 \cup F_2} \setminus X^G \ne \varnothing,$$
  集族 $\{X^F \setminus X^G \mid F \subseteq G \text{ 有限}\}$ 具有有限交性质。由超滤子引理，存在超滤子 $\mathcal{U} \in \beta X$ 包含该集族。于是对每个 $g \in G$，$X^{\{g\}} \setminus X^G \in \mathcal{U} \implies X^g \in \mathcal{U}$，故 $\mathcal{U} \in R_\infty(X)^G$；同时 $X \setminus X^G \in \mathcal{U} \implies X^G \notin \mathcal{U}$，故 $\mathcal{U} \notin \widehat{X^G} = \overline{\eta_{\infty,X}(X^G)}$，两者不等。$\blacksquare$

#### （3）对每个 $G$ 集合都满足 $\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$ 的群 $G$ 的完全分类
> **定理 2.6：** 群 $G$ 对其每个 $G$ 集合 $X$ 都满足 $\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$ **当且仅当 $G$ 是有限生成群**。

**证明：**
- **若 $G$ 是有限生成群：** 取 $G$ 的有限生成集 $F = \{s_1, \dots, s_k\}$。对任意 $G$ 集合 $X$，$x \in X$ 被生成集 $F$ 不动当且仅当它被整个群 $G = \langle F \rangle$ 不动，故恒有 $X^F = X^G$。由定理 2.5 知 $\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$。
- **若 $G$ 不是有限生成群：** 记 $\mathcal{H}$ 为 $G$ 的全体有限生成子群构成的集合（在 $\mathsf{ZFC}$ 中 $\mathcal{H} \subseteq \mathcal{P}(G)$ 是集合）。构造左乘陪集空间的不交并
  $$X := \bigsqcup_{H \in \mathcal{H}} G/H.$$
  1. 对每个 $H \in \mathcal{H}$，因为 $G$ 不是有限生成的，$H \lneq G$，故 $|G/H| \ge 2$ 且 $G$ 在 $G/H$ 上传递作用，从而 $(G/H)^G = \varnothing$。因此 $X^G = \bigsqcup_{H \in \mathcal{H}} (G/H)^G = \varnothing$。
  2. 对任意有限子集 $F \subseteq G$，子群 $H_F := \langle F \rangle \in \mathcal{H}$，且陪集元素 $x_F := eH_F \in G/H_F \subseteq X$ 满足 $\forall g \in F,\; g x_F = gH_F = eH_F = x_F$。因此 $x_F \in X^F$，即 $X^F \ne \varnothing = X^G$。
  由定理 2.5（或定理 2.3），对该 $G$ 集合 $X$ 有 $\overline{\eta_{\infty,X}(X^G)} = \varnothing \ne R_\infty(X)^G$。$\blacksquare$

---

### 2.3 群与底集均可数且 $X^G = \varnothing, R_\infty(X)^G \ne \varnothing$ 的具体例子及全部不动记录

- **具体构造：**
  - 取底集 $X = \mathbb{N} = \{0, 1, 2, \dots\}$（可数无穷集）；
  - 取群 $G = \operatorname{Sym}_{\mathrm{fin}}(\mathbb{N}) = \bigl\{ g \in \operatorname{Sym}(\mathbb{N}) \;\big|\; \operatorname{supp}(g) := \{x \in \mathbb{N} \mid gx \ne x\} \text{ 有限} \bigr\}$ 为 $\mathbb{N}$ 上的有限支集置换群（由于 $\mathbb{N}$ 的有限子集可数，$G$ 是可数群），作用为自然置换作用 $g \cdot x = g(x)$。
- **验证 $X^G = \varnothing$ 与 $R_\infty(X)^G \ne \varnothing$：**
  - 对每个 $x \in \mathbb{N}$，对换 $g = (x, x+1) \in G$ 满足 $g(x) = x+1 \ne x$，故 $X^G = \varnothing$。
  - 对任意有限子集 $F \subseteq G$，$S_F := \bigcup_{g \in F} \operatorname{supp}(g) \subseteq \mathbb{N}$ 是有限集，从而
    $$X^F = \mathbb{N} \setminus S_F$$
    是 $\mathbb{N}$ 的余有限集（特别地非空）。由定理 2.3 知 $R_\infty(\mathbb{N})^G \ne \varnothing$。
- **全部不动记录的完整描述：**
  因为当 $g$ 取遍 $G = \operatorname{Sym}_{\mathrm{fin}}(\mathbb{N})$ 时，$\operatorname{supp}(g)$ 取遍 $\mathbb{N}$ 的一切不含单点集的有限子集（且单点集 $\{x\} \subseteq \{x, x+1\} = \operatorname{supp}((x, x+1))$），所以不动点集族 $\{X^g \mid g \in G\}$ 生成的滤子恰为 $\mathbb{N}$ 上的 **Fréchet 滤子（余有限滤子）**
  $$\mathcal{F}_{\mathrm{cofin}} = \{ A \subseteq \mathbb{N} \mid \mathbb{N} \setminus A \text{ 是有限集} \}.$$
  而包含 Fréchet 滤子的超滤子恰为 $\mathbb{N}$ 上的全体**自由超滤子（非主超滤子）** $\beta\mathbb{N} \setminus \mathbb{N}$。
  因此，该例的全部不动记录集合为
  $$R_\infty(\mathbb{N})^G = \bigl\{ r^\mathcal{U} \;\big|\; \mathcal{U} \in \beta\mathbb{N} \setminus \mathbb{N} \text{ 为 } \mathbb{N} \text{ 上的自由超滤子} \bigr\} \cong \beta\mathbb{N} \setminus \mathbb{N},$$
  其中对每个自由超滤子 $\mathcal{U} \in \beta\mathbb{N} \setminus \mathbb{N}$，$r^\mathcal{U}_0 = \mathrm{id}_\varnothing$，且对任意 $n \ge 1$ 和 $f : \mathbb{N} \to [n]$，
  $$r^\mathcal{U}_n(f) = \lim_{x \to \mathcal{U}} f(x) = \text{使 } f^{-1}(\{i\}) \in \mathcal{U} \text{ 的唯一 } i \in [n]$$
  （特别地，若两个测试 $f, f' : \mathbb{N} \to [n]$ 仅在有限个点处取值不同，则对一切 $r \in R_\infty(\mathbb{N})^G$ 均有 $r_n(f) = r_n(f')$）。

---

## 3. 乘积比较

设 $(X_i)_{i \in I}$ 为一族 $G$ 集合，记 $X := \prod_{i \in I} X_i$（带对角作用），$p_i : X \to X_i$ 为第 $i$ 个坐标投射。

### 3.1 $\Pi_{(X_i)}$ 的良定义与连续性

1. **良定义：** 对每个 $i \in I$，坐标投射 $p_i : X \to X_i$ 是 $G$-等变映射，即 $\forall g \in G,\; p_i \circ g_X = g_{X_i} \circ p_i$。若 $r \in R_\infty(X)^G$，则由 $R_\infty(-)$ 的协变函子性，对任意 $g \in G$：
   $$g \cdot \bigl(R_\infty(p_i)r\bigr) = R_\infty(g_{X_i}) R_\infty(p_i) r = R_\infty(g_{X_i} \circ p_i) r = R_\infty(p_i \circ g_X) r = R_\infty(p_i)\bigl(R_\infty(g_X) r\bigr) = R_\infty(p_i) r.$$
   故 $R_\infty(p_i) r \in R_\infty(X_i)^G$，从而 $\Pi_{(X_i)}(r) = \bigl(R_\infty(p_i) r\bigr)_{i \in I} \in \prod_{i \in I} R_\infty(X_i)^G$ 良定义。（当 $I = \varnothing$ 时，$X = \{\ast\}$ 为单点平凡 $G$ 集合，定义域与陪域均为单点集，$\Pi_\varnothing$ 为单点集间的唯一映射。）
2. **连续性：** 由乘积拓扑与子空间拓扑的泛性质，只需验证对每个 $i \in I$，映射 $R_\infty(p_i) : R_\infty(X) \to R_\infty(X_i)$ 连续。而 $R_\infty(X_i)$ 的拓扑由全体观察映射 $\mathrm{ev}_{n, f} : s \mapsto s_n(f)$（$n \ge 0, f : X_i \to [n]$）诱导，对每个这样的观察映射，复合映射
   $$\mathrm{ev}_{n, f} \circ R_\infty(p_i) : r \longmapsto \bigl(R_\infty(p_i)r\bigr)_n(f) = r_n(f \circ p_i) = \mathrm{ev}_{n, f \circ p_i}(r)$$
   恰为 $R_\infty(X)$ 上的一个定义观察映射，因而是连续的。故每个 $R_\infty(p_i)$ 连续，从而 $\Pi_{(X_i)}$ 连续。$\blacksquare$

---

### 3.2 $\Pi_{(X_i)}$ 对任意群 $G$ 与任意集合指标族 $I$ 的满射性判定

> **定理 3.1：** 对任意群 $G$ 及任意集合指标族 $(X_i)_{i \in I}$，比较映射
> $$\Pi_{(X_i)} : R_\infty\!\left(\prod_{i \in I} X_i\right)^G \longrightarrow \prod_{i \in I} R_\infty(X_i)^G$$
> **恒为满射**。

**证明：**
- 若 $I = \varnothing$，定义域 $R_\infty(\{\ast\})^G$ 与陪域 $\prod_{i \in \varnothing} R_\infty(X_i)^G$ 均为单点集，$\Pi_\varnothing$ 为双射，自然满射。
- 若 $I \ne \varnothing$ 且陪域 $\prod_{i \in I} R_\infty(X_i)^G = \varnothing$（例如某 $X_{i_0} = \varnothing$ 或 $R_\infty(X_{i_0})^G = \varnothing$），则空映射 $\varnothing \to \varnothing$ 恒为满射。
- 现设 $I \ne \varnothing$ 且陪域非空，任取一点 $\bigl(r^{(i)}\bigr)_{i \in I} \in \prod_{i \in I} R_\infty(X_i)^G$。记 $\mathcal{U}_i := \Psi_\infty(r^{(i)}) \in (\beta X_i)^G$（$i \in I$）。于是对每个 $i \in I$ 和 $g \in G$ 均有 $X_i^g \in \mathcal{U}_i$。
  我们需要在乘积集 $X = \prod_{i \in I} X_i$ 上构造一个超滤子 $\mathcal{W} \in (\beta X)^G$ 使得对所有 $i \in I$ 均有 $(p_i)_* \mathcal{W} = \mathcal{U}_i$（因为超滤子是极大滤子，$(p_i)_* \mathcal{W} = \mathcal{U}_i \iff \forall A_i \in \mathcal{U}_i,\; p_i^{-1}(A_i) \in \mathcal{W}$）。
  考虑 $X$ 的子集族：
  $$\mathcal{B} := \bigl\{ p_i^{-1}(A_i) \;\big|\; i \in I,\; A_i \in \mathcal{U}_i \bigr\} \cup \bigl\{ X^g \;\big|\; g \in G \bigr\}.$$
  验证 $\mathcal{B}$ 具有**有限交性质（FIP）**：任取有限子集 $J \subseteq I$、对每个 $j \in J$ 取 $A_j \in \mathcal{U}_j$，并任取有限子集 $F \subseteq G$。注意在对角作用下 $X^g = \prod_{i \in I} X_i^g$，故这有限个集合在 $X = \prod_{i \in I} X_i$ 中的交集为箱集：
  $$\left(\bigcap_{j \in J} p_j^{-1}(A_j)\right) \cap \left(\bigcap_{g \in F} X^g\right) = \prod_{i \in I} B_i, \quad \text{其中 } B_i := \begin{cases} A_i \cap \bigcap_{g \in F} X_i^g, & i \in J, \\[4pt] \bigcap_{g \in F} X_i^g, & i \in I \setminus J. \end{cases}$$
  由于对每个 $i \in I$，$F$ 是有限集且 $\forall g \in F,\; X_i^g \in \mathcal{U}_i$（以及对 $i \in J$ 有 $A_i \in \mathcal{U}_i$），由超滤子 $\mathcal{U}_i$ 对有限交的封闭性知对**所有** $i \in I$ 均有 $B_i \in \mathcal{U}_i$，从而 $B_i \ne \varnothing$。
  在 $\mathsf{ZFC}$ 中由选择公理，$\prod_{i \in I} B_i \ne \varnothing$。因此 $\mathcal{B}$ 具有有限交性质。由超滤子引理，$\mathcal{B}$ 可扩充为 $X$ 上的超滤子 $\mathcal{W} \in \beta X$。
  因 $\forall g \in G,\; X^g \in \mathcal{B} \subseteq \mathcal{W}$，由定理 2.2 知 $r^\mathcal{W} \in R_\infty(X)^G$；又因 $\forall i \in I, \forall A_i \in \mathcal{U}_i,\; p_i^{-1}(A_i) \in \mathcal{W}$，有 $(p_i)_* \mathcal{W} = \mathcal{U}_i$，即 $\Pi_{(X_i)}(r^\mathcal{W}) = (r^{(i)})_{i \in I}$。故 $\Pi_{(X_i)}$ 恒为满射。$\blacksquare$

---

### 3.3 平凡群下两因子比较映射为单射的充要条件

设 $G = \{e\}$ 为平凡群，此时比较映射为 $\Pi_{X, Y} : R_\infty(X \times Y) \to R_\infty(X) \times R_\infty(Y)$。

> **定理 3.2：** 对平凡群作用，比较映射 $\Pi_{X, Y} : R_\infty(X \times Y) \to R_\infty(X) \times R_\infty(Y)$ 为单射（从而为双射）**当且仅当 $X$ 与 $Y$ 中至少有一个是有限集**。

**证明：**
1. **充分性（$X, Y$ 至少一个有限 $\implies \Pi_{X, Y}$ 为单射）：**
   - 若 $X = \varnothing$ 或 $Y = \varnothing$，则 $X \times Y = \varnothing$，定义域与陪域均为 $\varnothing$，$\Pi_{X, Y}$ 空真为单射。
   - 不妨设 $X$ 为非空有限集（$Y$ 有限的情形由对称性同理）。设 $\mathcal{W} \in \beta(X \times Y)$ 的投射为 $(p_X)_* \mathcal{W} = \mathcal{U} \in \beta X$ 与 $(p_Y)_* \mathcal{W} = \mathcal{V} \in \beta Y$。因为 $X$ 有限，$\mathcal{U} = \mathcal{U}_{x_0}$ 是由唯一点 $x_0 \in X$ 生成的主超滤子，故 $\{x_0\} \in (p_X)_* \mathcal{W}$，即 $\{x_0\} \times Y = p_X^{-1}(\{x_0\}) \in \mathcal{W}$。
     对任意子集 $S \subseteq X \times Y$，记截面 $S_{x_0} := \{y \in Y \mid (x_0, y) \in S\}$，则
     $$S \cap (\{x_0\} \times Y) = \{x_0\} \times S_{x_0} = p_Y^{-1}(S_{x_0}) \cap (\{x_0\} \times Y).$$
     因 $\{x_0\} \times Y \in \mathcal{W}$，故
     $$S \in \mathcal{W} \Longleftrightarrow S \cap (\{x_0\} \times Y) \in \mathcal{W} \Longleftrightarrow p_Y^{-1}(S_{x_0}) \in \mathcal{W} \Longleftrightarrow S_{x_0} \in \mathcal{V}.$$
     这表明 $\mathcal{W} = \{S \subseteq X \times Y \mid S_{x_0} \in \mathcal{V}\}$ 被 $(\mathcal{U}, \mathcal{V})$ 唯一决定，故 $\Pi_{X, Y}$ 为单射。

2. **必要性（$X, Y$ 均无限 $\implies \Pi_{X, Y}$ 不是单射）：**
   设 $X$ 与 $Y$ 均为无穷集。在 $X, Y$ 中分别取可数无穷子集 $X_0 = \{x_0, x_1, x_2, \dots\} \subseteq X$ 与 $Y_0 = \{y_0, y_1, y_2, \dots\} \subseteq Y$（$x_n$ 互异，$y_m$ 互异）。
   由超滤子引理，在 $X$ 上取支集在 $X_0$ 上的自由超滤子 $\mathcal{U} \in \beta X$（即 $X_0 \in \mathcal{U}$ 且 $X$ 的一切有限子集不属于 $\mathcal{U}$），在 $Y$ 上取支集在 $Y_0$ 上的自由超滤子 $\mathcal{V} \in \beta Y$。
   在 $X \times Y$ 上定义两个张量积超滤子 $\mathcal{W}_1 = \mathcal{U} \otimes \mathcal{V}$ 与 $\mathcal{W}_2 = \mathcal{V} \tilde{\otimes} \mathcal{U}$：
   $$\mathcal{W}_1 := \bigl\{ S \subseteq X \times Y \;\big|\; \{x \in X \mid S_x \in \mathcal{V}\} \in \mathcal{U} \bigr\}, \quad S_x := \{y \in Y \mid (x, y) \in S\},$$
   $$\mathcal{W}_2 := \bigl\{ S \subseteq X \times Y \;\big|\; \{y \in Y \mid S^y \in \mathcal{U}\} \in \mathcal{V} \bigr\}, \quad S^y := \{x \in X \mid (x, y) \in S\}.$$
   - **$\mathcal{W}_1, \mathcal{W}_2 \in \beta(X \times Y)$：** 因为 $\mathcal{V}$ 是超滤子，映射 $S \mapsto \{x \in X \mid S_x \in \mathcal{V}\}$ 是布尔代数同态 $\mathcal{P}(X \times Y) \to \mathcal{P}(X)$，故超滤子 $\mathcal{U}$ 的原像 $\mathcal{W}_1$ 是 $X \times Y$ 上的超滤子；同理 $\mathcal{W}_2$ 也是超滤子。
   - **$\Pi_{X, Y}(r^{\mathcal{W}_1}) = \Pi_{X, Y}(r^{\mathcal{W}_2}) = (r^\mathcal{U}, r^\mathcal{V})$：** 对任意 $A \subseteq X$，$(p_X^{-1}(A))_x$ 在 $x \in A$ 时为 $Y \in \mathcal{V}$，在 $x \notin A$ 时为 $\varnothing \notin \mathcal{V}$，故 $p_X^{-1}(A) \in \mathcal{W}_1 \iff A \in \mathcal{U}$；同时对任意 $y \in Y$，$(p_X^{-1}(A))^y = A$，故 $p_X^{-1}(A) \in \mathcal{W}_2 \iff A \in \mathcal{U}$。由对称性同理有 $p_Y^{-1}(B) \in \mathcal{W}_1 \iff B \in \mathcal{V} \iff p_Y^{-1}(B) \in \mathcal{W}_2$。因此 $(p_X)_* \mathcal{W}_1 = (p_X)_* \mathcal{W}_2 = \mathcal{U}$ 且 $(p_Y)_* \mathcal{W}_1 = (p_Y)_* \mathcal{W}_2 = \mathcal{V}$。
   - **$\mathcal{W}_1 \ne \mathcal{W}_2$：** 考察上三角子集
     $$D := \bigl\{ (x_n, y_m) \;\big|\; n, m \in \mathbb{N},\; 0 \le n < m \bigr\} \subseteq X \times Y.$$
     - 对每个 $n \in \mathbb{N}$，水平截面 $D_{x_n} = \{y_m \mid m > n\}$ 在 $Y_0$ 中余有限，因 $\mathcal{V}$ 是支集在 $Y_0$ 上的自由超滤子，故 $D_{x_n} \in \mathcal{V}$。从而 $\{x \in X \mid D_x \in \mathcal{V}\} = X_0 \in \mathcal{U}$，即 **$D \in \mathcal{W}_1$**。
     - 对每个 $m \in \mathbb{N}$，竖直截面 $D^{y_m} = \{x_n \mid 0 \le n < m\}$ 是有限集，因 $\mathcal{U}$ 是自由超滤子，故 $D^{y_m} \notin \mathcal{U}$。从而 $\{y \in Y \mid D^y \in \mathcal{U}\} = \varnothing \notin \mathcal{V}$，即 **$D \notin \mathcal{W}_2$**。
     故 $r^{\mathcal{W}_1} \ne r^{\mathcal{W}_2}$，$\Pi_{X, Y}$ 不是单射。$\blacksquare$

---

### 3.4 任意群作用下两个全称命题的判定与证明

#### 命题一：若 $X, Y$ 至少一个有限，则两因子的比较映射 $\Pi_{X, Y} : R_\infty(X \times Y)^G \to R_\infty(X)^G \times R_\infty(Y)^G$ 为双射。
- **判定结果：成立（真命题）。**
- **证明：**
  1. 由定理 3.1，对任意群 $G$ 及任意 $G$ 集合 $X, Y$，$\Pi_{X, Y} : R_\infty(X \times Y)^G \to R_\infty(X)^G \times R_\infty(Y)^G$ **恒为满射**。
  2. 由定理 3.2，当 $X, Y$ 至少一个有限时，不带群作用限制的环境映射 $\Pi_{X, Y}^{\{e\}} : R_\infty(X \times Y) \to R_\infty(X) \times R_\infty(Y)$ 是**单射**。而 $\Pi_{X, Y}$ 恰为单射 $\Pi_{X, Y}^{\{e\}}$ 在子集 $R_\infty(X \times Y)^G \subseteq R_\infty(X \times Y)$ 上的限制，故 $\Pi_{X, Y}$ 必为**单射**。
  综上，$\Pi_{X, Y}$ 既是单射又是满射，从而恒为双射。$\blacksquare$

---

#### 命题二：若 $X^G = Y^G = \varnothing$，则两因子的比较映射 $\Pi_{X, Y} : R_\infty(X \times Y)^G \to R_\infty(X)^G \times R_\infty(Y)^G$ 为单射。
- **判定结果：不成立（假命题）。**
- **证明（反例与一般机制）：**
  先指出一个普遍性质：对任意两因子 $G$ 集合 $X, Y$ 及任意 $\mathcal{W} \in \beta(X \times Y)$，因为对每个 $g \in G$ 均有
  $$(X \times Y)^g = X^g \times Y^g = p_X^{-1}(X^g) \cap p_Y^{-1}(Y^g),$$
  所以由定理 2.2 及滤子对有限交的性质：
  $$(X \times Y)^g \in \mathcal{W} \Longleftrightarrow p_X^{-1}(X^g) \in \mathcal{W} \text{ 且 } p_Y^{-1}(Y^g) \in \mathcal{W} \Longleftrightarrow X^g \in (p_X)_* \mathcal{W} \text{ 且 } Y^g \in (p_Y)_* \mathcal{W}.$$
  即 $R_\infty(X \times Y)^G = \bigl(\Pi_{X, Y}^{\{e\}}\bigr)^{-1}\!\bigl(R_\infty(X)^G \times R_\infty(Y)^G\bigr)$：只要 $\mathcal{W} \in \beta(X \times Y)$ 的两个坐标投射分别属于 $(\beta X)^G$ 和 $(\beta Y)^G$，$\mathcal{W}$ 就**自动**属于 $(\beta(X \times Y))^G$！
  - **具体反例：** 取第 2.3 节中的可数群 $G = \operatorname{Sym}_{\mathrm{fin}}(\mathbb{N})$ 和 $X = Y = \mathbb{N}$。如第 2.3 节所证：
    1. $X^G = Y^G = \varnothing$；
    2. $(\beta X)^G = (\beta Y)^G = \beta\mathbb{N} \setminus \mathbb{N} \ne \varnothing$。
    任取自由超滤子 $\mathcal{U} \in \beta\mathbb{N} \setminus \mathbb{N}$，如定理 3.2 的证明构造 $\mathbb{N} \times \mathbb{N}$ 上的两个超滤子
    $$\mathcal{W}_1 = \mathcal{U} \otimes \mathcal{U}, \qquad \mathcal{W}_2 = \mathcal{U} \tilde{\otimes} \mathcal{U}.$$
    由定理 3.2 的证明，$(p_X)_* \mathcal{W}_1 = (p_X)_* \mathcal{W}_2 = \mathcal{U} \in (\beta X)^G$ 且 $(p_Y)_* \mathcal{W}_1 = (p_Y)_* \mathcal{W}_2 = \mathcal{U} \in (\beta Y)^G$，而上三角集 $D = \{(n, m) \in \mathbb{N}^2 \mid n < m\}$ 满足 $D \in \mathcal{W}_1 \setminus \mathcal{W}_2$，故 $r^{\mathcal{W}_1} \ne r^{\mathcal{W}_2}$。
    又因为对每个 $g \in G$，$X^g = Y^g \in \mathcal{U}$，故 $(X \times Y)^g = p_X^{-1}(X^g) \cap p_Y^{-1}(Y^g)$ 同时属于 $\mathcal{W}_1$ 和 $\mathcal{W}_2$，即 $r^{\mathcal{W}_1}, r^{\mathcal{W}_2} \in R_\infty(X \times Y)^G$。
    但 $\Pi_{X, Y}(r^{\mathcal{W}_1}) = (r^\mathcal{U}, r^\mathcal{U}) = \Pi_{X, Y}(r^{\mathcal{W}_2})$，故 $\Pi_{X, Y}$ 不是单射。$\blacksquare$
