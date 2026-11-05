## S1 可缩子复形的商

### 结论与证明

设 $Y$ 为有限 CW 复形，$A \subset Y$ 为非空可缩子复形。商映射记为 $q: Y \to Y/A$。

#### 1. 构造逆同伦候选映射
因为 $(Y, A)$ 是 CW 复形对，所以包含映射 $i: A \hookrightarrow Y$ 是一余纤维化，即 $(Y, A)$ 具有 Borsuk 同伦延拓性质（HEP）。

由于 $A$ 可缩，存在同伦 $h: A \times [0, 1] \to A$ 以及基点 $a_0 \in A$，满足：
- 对任意 $a \in A$，$h(a, 0) = a$；
- 对任意 $a \in A$，$h(a, 1) = a_0$。

将 $i \circ h: A \times [0, 1] \to Y$ 视作作用在子复形 $A$ 上的同伦，其初值 $i \circ h(\cdot, 0) = \mathrm{id}_Y|_A$。由 $(Y, A)$ 的同伦延拓性质，存在连续延拓映射 $H: Y \times [0, 1] \to Y$，满足：
- $H(y, 0) = y$（即 $H_0 = \mathrm{id}_Y$）；
- 对所有 $a \in A, t \in [0, 1]$，有 $H(a, t) = h(a, t) \in A$。

在时刻 $t = 1$，对所有 $a \in A$ 均有 $H(a, 1) = h(a, 1) = a_0$。即 $H_1: Y \to Y$ 把整个子空间 $A$ 映至单点 $a_0$。

由商拓扑的泛性质，由于 $H_1$ 在商映射 $q: Y \to Y/A$ 的每个纤维上为常值（仅有非单点纤维 $A$ 被映为常值 $a_0$），存在唯一的连续映射 $\bar{f}: Y/A \to Y$，满足：
$$\bar{f} \circ q = H_1.$$

#### 2. 复合映射同伦于恒等
- **第一方向**：$\bar{f} \circ q = H_1$。由定义，延拓同伦 $H$ 正是连接 $H_0 = \mathrm{id}_Y$ 与 $H_1 = \bar{f} \circ q$ 的连续同伦，故：
  $$\bar{f} \circ q \simeq \mathrm{id}_Y.$$

- **第二方向**：考查 $q \circ \bar{f}: Y/A \to Y/A$。考虑复合映射：
  $$G: Y \times [0, 1] \to Y/A,\qquad G(y, t) = q(H(y, t)).$$
  在时刻 $t=0$，$G(y, 0) = q(y)$；在时刻 $t=1$，$G(y, 1) = q(H_1(y)) = q(\bar{f}(q(y)))$。

#### 3. 说明同伦为何能下降到商空间
同伦 $G(y, t)$ 之所以能严格下降为连续同伦 $\bar{G}: (Y/A) \times [0, 1] \to Y/A$，基于以下两点拓扑事实：

1. **代数纤维相容性**：
   对任意 $a \in A$ 及任意 $t \in [0, 1]$，延拓性质保证 $H(a, t) = h(a, t) \in A$。因此 $q(H(a, t)) = [A] \in Y/A$。即对每个固定的 $t$，$G(\cdot, t)$ 在 $A$ 上恒等于商空间中的单点 $[A]$。因此映射 $G$ 在积空间映射 $q \times \mathrm{id}_{[0, 1]}: Y \times [0, 1] \to (Y/A) \times [0, 1]$ 的每个纤维上均为常值。

2. **商拓扑在紧致因子的积下保持**：
   区间 $[0, 1]$ 是紧致 Hausdorff 空间（特别地，局部紧 Hausdorff）。根据一般拓扑学定理：若 $q: Y \to Y/A$ 为商映射，且 $K$ 为局部紧 Hausdorff 空间，则积映射：
   $$q \times \mathrm{id}_K: Y \times K \to (Y/A) \times K$$
   仍然是拓扑商映射。
   
   因此，由商拓扑的泛性质，$G$ 唯一诱导出一个连续映射：
   $$\bar{G}: (Y/A) \times [0, 1] \to Y/A,\quad \text{满足}\quad \bar{G} \circ (q \times \mathrm{id}_{[0, 1]}) = G.$$
   检验端点：
   - $\bar{G}([y], 0) = G(y, 0) = q(y) = \mathrm{id}_{Y/A}([y])$；
   - $\bar{G}([y], 1) = G(y, 1) = q(\bar{f}(q(y))) = (q \circ \bar{f})([y])$。
   
   这证明了 $\bar{G}$ 是连接 $\mathrm{id}_{Y/A}$ 与 $q \circ \bar{f}$ 的连续同伦，即 $q \circ \bar{f} \simeq \mathrm{id}_{Y/A}$。

综上，$q: Y \to Y/A$ 为同伦等价。

---

## S2 非可缩底空间上的锥附着

### 证明与同伦等价构造

记 $i: L \hookrightarrow D$ 为包含映射。锥空间定义为：
$$CL = (L \times [0, 1]) / (L \times \{1\}),$$
附着空间即为映射锥 $Y = D \cup_i CL = C(i)$，其中底面 $L \times \{0\}$ 经包含映射 $i$ 与 $D$ 粘合。

#### 1. 映射锥的同伦不变量性质
已知 $i: L \hookrightarrow D$ 零伦，即存在连续映射 $H: L \times [0, 1] \to D$ 及点 $d_0 \in D$，满足：
$$H(x, 0) = i(x) = x,\qquad H(x, 1) = d_0 \quad (\forall x \in L).$$
令 $c_{d_0}: L \to D$ 为常值映射 $c_{d_0}(x) \equiv d_0$。

构造 $C(i)$ 到 $C(c_{d_0})$ 的映射 $\Phi: Y \to C(c_{d_0})$ 如下：
- 对任意 $d \in D$，$\Phi(d) = d$；
- 对任意 $[x, t] \in CL$：
  $$\Phi([x, t]) = \begin{cases} H(x, 2t) \in D, & 0 \le t \le \frac{1}{2}, \\ [x, 2t - 1] \in CL \subset C(c_{d_0}), & \frac{1}{2} \le t \le 1. \end{cases}$$
在连接处：$t = 0$ 时 $H(x, 0) = x \in D$ 与底空间重合；$t = \frac{1}{2}$ 时 $H(x, 1) = d_0 = [x, 0] \in C(c_{d_0})$；$t = 1$ 时 $[x, 1]$ 映至锥顶。故 $\Phi$ 连续。

利用反向同伦 $\bar{H}(x, t) = H(x, 1-t)$ 同理构造 $\Psi: C(c_{d_0}) \to C(i)$：
- 对任意 $d \in D$，$\Psi(d) = d$；
- 对任意 $[x, t] \in CL$：
  $$\Psi([x, t]) = \begin{cases} H(x, 1 - 2t) \in D, & 0 \le t \le \frac{1}{2}, \\ [x, 2t - 1] \in CL \subset C(i), & \frac{1}{2} \le t \le 1. \end{cases}$$
由同伦重参数化的标准延拓，$\Psi \circ \Phi$ 与 $\Phi \circ \Psi$ 分别同伦于各自空间上的恒等映射（在 $D$ 上保持相对不变）。因此 $Y = C(i) \simeq C(c_{d_0})$。

#### 2. 常值锥附着的拓扑识别
在空间 $C(c_{d_0}) = D \cup_{c_{d_0}} CL$ 中，锥底 $L \times \{0\}$ 的全部点均粘合于单点 $d_0 \in D$。
而 $CL$ 的锥顶 $L \times \{1\}$ 本身已被折叠为单点。
因此，$CL$ 在该粘合下两端均被压为单点：
$$(L \times [0, 1]) / (L \times \{0\} \sim v_0,\; L \times \{1\} \sim v_1) \cong \Sigma L,$$
这正是非约化悬挂 $\Sigma L$。并且 $CL$ 与 $D$ 仅在 $v_0 = [L \times \{0\}] = d_0$ 处相交，其余部分不与 $D$ 相交。

故存在自然同胚：
$$C(c_{d_0}) \cong D \vee_{(d_0, v_0)} \Sigma L.$$
结合前面的同伦等价，即得 $Y \simeq D \vee \Sigma L$。

#### 3. 楔点的选择说明
1. **在 $\Sigma L$ 端的楔点选择**：
   必须选取为悬挂的两个锥顶（极点）之一，记作 $v_0 = [L \times \{0\}]$（通过悬挂坐标的轴向对称 $t \mapsto 1-t$，选另一个锥顶 $v_1 = [L \times \{1\}]$ 诱导同胚空间）。注意 $L$ 一般不是带基点复形（甚至可以不连通），因此非约化悬挂 $\Sigma L$ 自身没有天然的赤道基点，两个几何锥顶是天然且唯一的锥底折叠点。
2. **在 $D$ 端的楔点选择**：
   选取为零伦同伦的终点 $d_0 \in D$。因为题目假定 $D$ 是路径连通 CW 复形，CW 复形中的点是闭且非退化的（$(D, \{d\})$ 为 Borsuk 对）。连接 $d_0$ 与任意另一选定基点 $d_1$ 的道路能够延拓为全局同伦等价，故楔和空间在同伦意义下独立于 $d_0 \in D$ 的具体选取。

---

## S3 整数扭结的实例

### 构造与证明

取给定的实射影平面 $\mathbb{R}P^2$ 的有限单纯三角剖分 $L$。

#### 1. 复形 $K$、顶点 $v$ 及子复形 $B$ 的构造
1. **顶点集**：取两个不在 $L$ 中的新顶点 $w$ 和 $v$。
2. **复形 $K$**：取 $L$ 的单纯悬挂（simplicial suspension）：
   $$K = (w * L) \cup_L (v * L).$$
   其单形包括：$L$ 的所有单形，以及形如 $\{w\} \cup \sigma$ 与 $\{v\} \cup \sigma$ 的单形（其中 $\sigma \in L$）。$K$ 为有限抽象单纯复形。
3. **选定顶点 $v$**：即上述单纯悬挂的悬挂顶点之一 $v$。
   此时 $v$ 在 $K$ 中的单纯形链环为：
   $$\mathrm{lk}_K(v) = L.$$
   而不含 $v$ 的极大子复形为：
   $$K \setminus v = w * L.$$
4. **子复形 $B$**：
   因为 $L$ 是 $\mathbb{R}P^2$ 的三角剖分，故 $L$ 非空且至少包含一个顶点。任取 $L$ 的一个顶点 $u \in L^{(0)}$。
   在 $K$ 中，由于 $u \in \mathrm{lk}_K(v)$，$\{v, u\}$ 是 $K$ 的一条 1-单形（边）。
   定义子复形 $B$ 为由该 1-单形及其面生成的子复形：
   $$B = \{\emptyset, \{v\}, \{u\}, \{v, u\}\}.$$
   显然 $v \in B \subseteq K$。

#### 2. 条件验证与性质证明

- **$|K| \setminus \{v\}$ 非空可缩**：
  在几何实现 $|K|$ 中，考虑不含 $v$ 的子复形几何实现 $|K \setminus v| = |w * L|$。对于任意 $x \in |K| \setminus \{v\}$，利用重心坐标沿射线向底面投影：
  $$r_s(x) = (1-s)x + s \frac{x - t_v(x)v}{1 - t_v(x)},\quad s \in [0, 1],$$
  构成了 $|K| \setminus \{v\}$ 到 $|K \setminus v|$ 的强形变收缩。
  而 $|K \setminus v| = |w * L| \cong C(|L|)$ 是以 $w$ 为锥顶的锥，拓扑上是非空可缩的。因此 $|K| \setminus \{v\} \simeq |K \setminus v| \simeq *$，非空可缩。

- **$(|B| \setminus \{v\}) \to |B|$ 为同伦等价**：
  由定义，$|B|$ 是连接 $v$ 与 $u$ 的闭线段，同胚于 $[0, 1]$，为可缩空间；
  $|B| \setminus \{v\}$ 是半开线段 $(v, u]$，同胚于 $(0, 1]$，亦为可缩空间。
  两个可缩空间之间的包含映射必然诱导所有同伦群的同构，因而是同伦等价。

- **$|K|$ 的约化有理同调全零**：
  几何实现 $|K| \cong \Sigma |L| = \Sigma \mathbb{R}P^2$。
  由悬挂同构定理：
  $$\tilde{H}_k(|K|; \mathbb{Q}) \cong \tilde{H}_{k-1}(\mathbb{R}P^2; \mathbb{Q}).$$
  由于 $\mathbb{R}P^2$ 的整同调为 $H_0 = \mathbb{Z}, H_1 = \mathbb{Z}/2\mathbb{Z}, H_{\ge 2} = 0$，其约化有理同调对所有度数均为零：
  $$\tilde{H}_*(\mathbb{R}P^2; \mathbb{Q}) = 0 \implies \tilde{H}_*(|K|; \mathbb{Q}) = 0 \quad (\forall * \ge 0).$$

- **$|K|$ 不可缩**：
  考查整数系数悬挂同调：
  $$\tilde{H}_2(|K|; \mathbb{Z}) \cong \tilde{H}_1(\mathbb{R}P^2; \mathbb{Z}) \cong \mathbb{Z}/2\mathbb{Z} \ne 0.$$
  由于 $|K|$ 存在非零的 2 阶整同调群，$|K|$ 绝不可能可缩。

---

## S4 整体对象与全部恢复目标

### 判定结论
**目标成立**。所要求的可能同伦类型刻画、全类型实现构造，以及仅凭包含 $v$ 的局部单形关联数据判别 $X$ 可缩的充要条件均可完整建立并证明。

---

### 1. 同伦类型刻画定理

**定理**：三元组 $(K, v, B)$ 满足条件当且仅当 $X = |K|$ 同伦等价于某个**非空有限单纯复形的非约化悬挂**，即：
$$\{ [X] \mid X = |K| \} = \{ [\Sigma |L|] \mid L \text{ 为非空有限抽象单纯复形} \}.$$

#### 证明（必要性）：
1. 记 $L_K = \mathrm{lk}_K(v)$ 为 $v$ 在 $K$ 中的单纯形链环，$K \setminus v$ 为除去 $v$ 后的子复形。
2. 同 S3 所证，利用重心坐标中关于 $v$ 的分量 $t_v < 1$ 沿射线向底投影，$O = |K| \setminus \{v\}$ 强形变收缩到 $|K \setminus v|$。因假定 $O$ 可缩，故有限 CW 复形 $|K \setminus v|$ 是可缩的。
3. 同理，$O \cap C = |B| \setminus \{v\}$ 强形变收缩到 $|B \setminus v|$。由条件包含映射 $O \cap C \hookrightarrow C = |B|$ 是同伦等价。
   - 若 $L_K = \emptyset$，则 $v$ 是 $K$ 的孤立顶点，亦为 $B$ 的孤立顶点。此时 $|B| = |B \setminus v| \sqcup \{v\}$，则包含映射 $(|B| \setminus \{v\}) \hookrightarrow |B|$ 在零阶同伦群 $\pi_0$ 上不可能满射，矛盾。
   - 因此必有 $L_K \ne \emptyset$，即 $L_K$ 是非空有限单纯复形。
4. 几何实现可表示为胞腔附着：
   $$X = |K| = |K \setminus v| \cup_{L_K} (v * L_K) = |K \setminus v| \cup_{L_K} C(L_K).$$
   由于底空间 $|K \setminus v|$ 是非空可缩的有限 CW 复形，包含映射 $i: |L_K| \hookrightarrow |K \setminus v|$ 自动零伦。根据 S2 的结论：
   $$X = C(i) \simeq |K \setminus v| \vee \Sigma |L_K| \simeq * \vee \Sigma |L_K| \cong \Sigma |L_K|.$$
   故 $X$ 必同伦等价于非空有限单纯复形 $L_K$ 的悬挂。

---

### 2. 刻画中全部类型的实现构造

**构造（充分性）**：
设 $L$ 为任意给定的非空有限单纯复形。我们要构造三元组 $(K, v, B)$ 满足全部前提且 $|K| \simeq \Sigma |L|$。

1. **构造 $K$**：
   取两个不属于 $L$ 的新顶点 $w$ 和 $v$，令
   $$K = (w * L) \cup_L (v * L) = \Sigma_{simp}(L)$$
   为 $L$ 的单纯悬挂。
2. **验证 $O$ 可缩**：
   $K \setminus v = w * L$ 为以 $w$ 为顶点的锥，几何实现 $|K \setminus v|$ 可缩。又 $O = |K| \setminus \{v\}$ 强形变收缩到 $|K \setminus v|$，故 $O$ 非空可缩。
3. **构造 $B$**：
   因为 $L \ne \emptyset$，必存在顶点 $u \in L^{(0)}$。因为 $u \in \mathrm{lk}_K(v)$，$\{v, u\}$ 是 $K$ 中的 1-单形。
   令 $B$ 为边 $\{v, u\}$ 及其面组成的子复形：
   $$B = \{\emptyset, \{v\}, \{u\}, \{v, u\}\}.$$
   则 $C = |B| = [v, u] \simeq *$，且 $O \cap C = |B| \setminus \{v\} = (v, u] \simeq *$。包含映射是两可缩空间之间的映射，必然是同伦等价。
4. **同伦类型**：
   $|K| \cong \Sigma |L|$。

至此，刻画中的每一种类型均被显式构造实现。

---

### 3. $X$ 可缩的有限关联数据检验判据

#### 关联数据提取与判据表述
设 $\mathrm{Star}_K(v) = \{ \sigma \in K \mid v \in \sigma \}$ 为包含 $v$ 的单形集合。
$v$ 的链环 $L_K = \mathrm{lk}_K(v)$ 的单形及其面关联完全由 $\mathrm{Star}_K(v)$ 确定：
$$\sigma \in L_K \iff \sigma \cup \{v\} \in \mathrm{Star}_K(v) \quad (\text{且 } v \notin \sigma).$$
链环 $L_K$ 的代数链复形 $C_*(L_K; \mathbb{Z})$ 的基与微分矩阵完全由此有限关联数据给出。

**判据定理**：
在题设条件下，$X = |K|$ 可缩的**充要条件**是：链环 $L_K = \mathrm{lk}_K(v)$ 是**整数无环的（$\mathbb{Z}$-acyclic）**，即：
$$\tilde{H}_k(L_K; \mathbb{Z}) = 0 \quad (\forall k \ge 0).$$
用有限关联数据具体检验即为：
1. **$k=0$**：$L_K$ 非空且连通（即零阶约化同调 $\tilde{H}_0(L_K; \mathbb{Z}) = 0$）；
2. **$k \ge 1$**：对所有 $1 \le k \le \dim(K)-1$，由关联数据计算的整系数边缘矩阵 $\partial_k$ 的 Smith 标准型表明 $\ker \partial_k = \mathrm{im} \partial_{k+1}$（即 $H_k(L_K; \mathbb{Z}) = 0$）。

#### 证明：
- **必要性（$\implies$）**：
  若 $X$ 可缩，则对所有 $m \ge 0$ 有 $\tilde{H}_m(X; \mathbb{Z}) = 0$。
  由前述同伦等价 $X \simeq \Sigma |L_K|$，结合悬挂同构定理：
  $$\tilde{H}_{k+1}(X; \mathbb{Z}) \cong \tilde{H}_k(|L_K|; \mathbb{Z}) \quad (\forall k \ge 0).$$
  因此对一切 $k \ge 0$ 均有 $\tilde{H}_k(L_K; \mathbb{Z}) = 0$。
  
- **充分性（$\impliedby$）**：
  假设 $\tilde{H}_*(L_K; \mathbb{Z}) = 0$：
  1. $\tilde{H}_0(L_K) = 0$ 保证了 $|L_K|$ 非空且路径连通。
  2. 根据 Seifert-van Kampen 定理，悬挂 $\Sigma |L_K|$ 是两个可缩锥沿路径连通空间 $|L_K|$ 的粘合，因此 $\pi_1(\Sigma |L_K|) = 0$，即 $\Sigma |L_K|$ 单连通。
  3. 再次由悬挂同构，$\tilde{H}_m(\Sigma |L_K|; \mathbb{Z}) \cong \tilde{H}_{m-1}(|L_K|; \mathbb{Z}) = 0$ 对所有 $m \ge 1$ 成立。
  4. 对单连通 CW 复形 $\Sigma |L_K|$，应用 Hurewicz 定理：其所有同伦群全为平凡群，即 $\pi_m(\Sigma |L_K|) = 0$（$\forall m \ge 1$）。
  5. 根据 Whitehead 定理，所有同伦群平凡的 CW 复形必同伦等价于单点，即 $\Sigma |L_K| \simeq *$。
  
  故 $X \simeq \Sigma |L_K| \simeq *$，充要性获证。

---

## S5 不提供子复形 B

### 判定结论
**不必**。当不再提供 $B$ 及其同伦条件时，$|K|$ **不一定**同伦等价于非空有限复形的悬挂。

### 1. 满足全部前提的反例
取 $K_0$ 为任一非空可缩有限单纯复形（例如单个单形 $\Delta^n$ 或单点 $\Delta^0$）。
令 $K = K_0 \sqcup \{v\}$，即在 $K_0$ 外添加一个不与 $K_0$ 中任何单形相连的孤立顶点 $v$。
- **验证前提**：
  $K$ 是有限单纯复形，$v$ 是其顶点。
  $|K| \setminus \{v\} = |K_0|$，按设定是非空可缩空间。满足前提。
- **同伦型计算**：
  $$|K| = |K_0| \sqcup \{v\} \simeq * \sqcup * \cong S^0.$$
- **为何不能表示为非空有限复形的悬挂**：
  对于任意**非空**拓扑空间 $Y$，其非约化悬挂 $\Sigma Y$ 中，任意点 $[y, t]$ 均有道路连通至锥顶 $v_1 = [y, 1]$，而任取 $y_0 \in Y$，路径 $[y_0, t]$（$t \in [-1, 1]$）连接了两端极点。因此只要 $Y \ne \emptyset$，$\Sigma Y$ 必为路径连通空间（$\pi_0(\Sigma Y) = 0$）。
  然而 $|K| \simeq S^0$ 含有 2 个路径连通分支，绝不可能同伦等价于任何非空复形的悬挂。

---

### 2. 新增可能类型的完整分类

**分类结论**：
移去 $B$ 及其条件后，新增的可能同伦类型**仅有唯一的一种**：
$$\mathbf{S^0} \quad (\text{即两点离散空间 } * \sqcup *).$$

#### 分类证明：
设 $K$ 为有限复形，使得 $|K| \setminus \{v\}$ 非空可缩。
如前所述，$|K| \setminus \{v\}$ 强形变收缩到有限子复形 $|K \setminus v|$，故 $|K \setminus v|$ 非空可缩。
考查顶点 $v$ 的链环 $L_K = \mathrm{lk}_K(v)$：
- **情形 1：$L_K \ne \emptyset$**：
  此时 $|K| = |K \setminus v| \cup_{L_K} C(L_K)$。因 $|K \setminus v| \simeq *$，由 S2 直接推出：
  $$|K| \simeq \Sigma |L_K|,$$
  其中 $L_K$ 为非空有限单纯复形。这属于原有的类型。
- **情形 2：$L_K = \emptyset$**：
  $L_K = \emptyset$ 意味着 $K$ 中没有含 $v$ 的高维单形，即 $v$ 是 $K$ 的孤立顶点。
  此时复形发生不交并分解：$K = (K \setminus v) \sqcup \{v\}$。
  由于 $|K \setminus v| \simeq *$，几何实现为：
  $$|K| = |K \setminus v| \sqcup \{v\} \simeq * \sqcup * = S^0.$$
  （注：若允许形式上取空集 $\emptyset$ 的非约化悬挂，$\Sigma \emptyset = S^0$，此即退化悬挂）。

因此，新增类型恰好且仅为 $S^0$。

---

## S6 悬挂信息的逆向恢复

### 判定结论
**否**（由 $\Sigma |L_1| \simeq \Sigma |L_2|$ **不能**推出 $|L_1| \simeq |L_2|$）。

### 完整反例与证明

#### 1. 反例构造
- **构造 $L_1$**：
  取庞加莱同调 3-球面 $P^3$（Poincaré homology 3-sphere）。$P^3$ 是闭 3-流形，其基本群为 120 阶的双十二面体群 $I^* = \mathrm{SL}_2(\mathbb{F}_5) \ne 0$，其整同调群满足：
  $$H_0(P^3) = \mathbb{Z},\quad H_1(P^3) = 0,\quad H_2(P^3) = 0,\quad H_3(P^3) = \mathbb{Z}.$$
  从 $P^3$ 中挖去一个开 3-球 $\mathrm{int}(D^3)$，得到带边紧致 3-流形：
  $$M = P^3 \setminus \mathrm{int}(D^3),\qquad \partial M = S^2.$$
  由于 $M$ 是光滑/PL 流形，取其任一有限单纯三角剖分，记为 $L_1$。
- **构造 $L_2$**：
  取单点复形 $L_2 = \Delta^0$（单个 0-单形）。

$L_1$ 与 $L_2$ 显然均为非空有限单纯复形。

#### 2. 性质验证

1. **同调性质**：
   考虑将 $D^3$ 沿 $S^2$ 粘回 $M$ 得到 $P^3$ 的 Mayer-Vietoris 序列：
   $$0 \to H_3(M) \to H_3(P^3) \xrightarrow{\partial} H_2(S^2) \to H_2(M) \to H_2(P^3) = 0.$$
   由于连接同态 $\partial: H_3(P^3) \to H_2(S^2)$ 将基本类 $[P^3]$ 映为球面定向类 $[S^2]$，是同构 $\mathbb{Z} \to \mathbb{Z}$。
   由此得：
   $$H_3(M) = 0,\qquad H_2(M) = 0.$$
   又由 $H_1(S^2) = 0 \to H_1(M) \to H_1(P^3) = 0$ 知 $H_1(M) = 0$。
   显然 $M$ 连通，故 $\tilde{H}_0(M) = 0$。
   因此 $M = |L_1|$ 是**整数无环空间**：
   $$\tilde{H}_k(|L_1|; \mathbb{Z}) = 0 \quad (\forall k \ge 0).$$

2. **基本群与底空间不等价性**：
   由于余维度为 3（$\partial D^3 = S^2$ 是单连通的），由 Seifert-van Kampen 定理，挖去开 3-球不改变基本群：
   $$\pi_1(|L_1|) \cong \pi_1(P^3) \cong I^* \ne 0.$$
   然而 $|L_2| = |\Delta^0| = \{*\}$，其基本群 $\pi_1(|L_2|) = 0$。
   由于基本群是同伦不变量，两空间基本群不同构，故：
   $$|L_1| \not\simeq |L_2|.$$

3. **悬挂同伦等价性**：
   - 对于 $L_2$：$\Sigma |L_2| = \Sigma(*) \cong [-1, 1] \simeq *$ 为可缩空间。
   - 对于 $L_1$：
     - $|L_1|$ 是路径连通的有限复形，由 Seifert-van Kampen 定理，$\Sigma |L_1|$ 单连通，即 $\pi_1(\Sigma |L_1|) = 0$。
     - 由悬挂同构定理，$\tilde{H}_k(\Sigma |L_1|; \mathbb{Z}) \cong \tilde{H}_{k-1}(|L_1|; \mathbb{Z}) = 0$（$\forall k \ge 0$）。
     - 由 Hurewicz 定理，单连通且同调平凡的 CW 复形的所有同伦群全为零：$\pi_k(\Sigma |L_1|) = 0$（$\forall k \ge 1$）。
     - 由 Whitehead 定理，$\Sigma |L_1| \simeq *$。
   
   因此：
   $$\Sigma |L_1| \simeq * \simeq \Sigma |L_2|.$$

综上，$\Sigma |L_1| \simeq \Sigma |L_2|$ 成立，但 $|L_1| \not\simeq |L_2|$。悬挂信息在逆向恢复时不可逆。
