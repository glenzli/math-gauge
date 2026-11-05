# 局部单形、锥附着与整体同伦型

---

## S1 可缩子复形的商

### 1. 命题与设置
设 $Y$ 为有限 CW 复形，$A \subset Y$ 为非空可缩子复形。商空间记为 $Y/A$，商映射记为 $q: Y \to Y/A$，并将商点记为 $[A] \in Y/A$。我们要证明 $q$ 是同伦等价，并详细说明同伦能下降到商空间的原因。

### 2. 同伦延拓性质（HEP）与同伦构造
由于 $(Y, A)$ 是有限 CW 复形对，包含映射 $i: A \hookrightarrow Y$ 是闭上纤维化（Borsuk 对），对即具有同伦延拓性质（Homotopy Extension Property, HEP）。

因为 $A$ 可缩，存在原点 $a_0 \in A$ 及零伦同伦：
$$H: A \times I \longrightarrow A,$$
满足：
- 对所有 $a \in A$，$H(a, 0) = a$；
- 对所有 $a \in A$，$H(a, 1) = a_0$；
- 对所有 $(a, t) \in A \times I$，$H(a, t) \in A$。

考虑 $Y$ 上的恒等映射 $\text{id}_Y: Y \to Y$。在子空间 $A$ 上，有 $\text{id}_Y|_A = H(-, 0)$。由 $(Y, A)$ 的同伦延拓性质，同伦 $H: A \times I \to A \subset Y$ 与初始映射 $\text{id}_Y$ 可以延拓为整体同伦：
$$F: Y \times I \longrightarrow Y,$$
满足：
1. $F(y, 0) = y,\quad \forall y \in Y$（即 $F_0 = \text{id}_Y$）；
2. $F(a, t) = H(a, t) \in A,\quad \forall a \in A, \, t \in I$；
3. 特别地，$F(a, 1) = a_0,\quad \forall a \in A$。

### 3. 同伦逆映射的定义
考察时间 $t = 1$ 的映射 $F_1 = F(-, 1): Y \to Y$。由于对所有 $a \in A$ 均有 $F_1(a) = a_0$，即 $F_1$ 将整个子集 $A$ 映为单点 $a_0$，根据商拓扑的泛性质，$F_1$ 唯一诱导出一个连续映射：
$$g: Y/A \longrightarrow Y,\qquad g([y]) = F(y, 1),$$
使得 $g \circ q = F_1$。

由延拓同伦 $F$ 本身可知：
$$g \circ q = F_1 \simeq F_0 = \text{id}_Y,$$
故 $g \circ q \simeq \text{id}_Y$。

### 4. 证明 $q \circ g \simeq \text{id}_{Y/A}$ 及“同伦为何能下降到商”的拓扑证明

考虑复合映射：
$$\Phi = q \circ F: Y \times I \longrightarrow Y/A.$$
对任意 $y \in Y$，$t \in I$，有 $\Phi(y, t) = q(F(y, t))$。

#### (1) 纤维常值性检验
商映射 $q: Y \to Y/A$ 的非单点纤维仅有 $A$，对应商点 $[A]$。因此乘积映射：
$$q \times \text{id}_I: Y \times I \longrightarrow (Y/A) \times I$$
的非单点纤维对于每个 $t \in I$ 均为 $A \times \{t\}$。
对任意 $a \in A$ 及任意 $t \in I$，由延拓条件有 $F(a, t) = H(a, t) \in A$，从而：
$$\Phi(a, t) = q(F(a, t)) = [A] \in Y/A.$$
即 $\Phi$ 在 $q \times \text{id}_I$ 的每个纤维上均为常值。

#### (2) 同伦下降到商的拓扑条件
要保证 $\Phi$ 下降得到的映射 $\bar{F}: (Y/A) \times I \to Y/A$ 是连续的，核心在于说明：
$$\mathbf{q \times \text{id}_I: Y \times I \longrightarrow (Y/A) \times I \text{ 是商映射。}}$$
- **定理适用条件**：若 $q: Y \to Z$ 是拓扑空间的商映射，且空间 $W$ 是局部紧 Hausdorff 空间，则 $q \times \text{id}_W: Y \times W \to Z \times W$ 是商映射。
- **验证**：此处 $W = I = [0, 1]$ 是紧 Hausdorff 空间，自然是局部紧 Hausdorff 空间。因此，$q \times \text{id}_I$ 严格保持商拓扑。

由商映射的泛性质，存在唯一的连续映射：
$$\bar{F}: (Y/A) \times I \longrightarrow Y/A,$$
满足 $\bar{F} \circ (q \times \text{id}_I) = q \circ F$。

#### (3) 验证同伦端点
- 当 $t = 0$ 时：
  $$\bar{F}([y], 0) = q(F(y, 0)) = q(y) = [y] = \text{id}_{Y/A}([y]).$$
- 当 $t = 1$ 时：
  $$\bar{F}([y], 1) = q(F(y, 1)) = q(g([y])) = (q \circ g)([y]).$$

因此 $\bar{F}$ 是连接 $\text{id}_{Y/A}$ 与 $q \circ g$ 的连续同伦，即：
$$q \circ g \simeq \text{id}_{Y/A}.$$

综上，$q: Y \to Y/A$ 为同伦等价。

---

## S2 非可缩底空间上的锥附着

### 1. 记号与锥、悬挂的明确定义
- $D$ 为路径连通有限 CW 复形。
- $L \subset D$ 为非空有限子复形，包含映射记为 $i: L \hookrightarrow D$。
- 已知包含映射 $i$ 零伦，即存在连续映射 $H: L \times [0, 1] \to D$ 及点 $d_0 \in D$，满足：
  $$H(x, 0) = i(x) = x,\qquad H(x, 1) = d_0,\quad \forall x \in L.$$
- 锥 $CL$ 定义为非约化锥：
  $$CL = (L \times [0, 1]) / (L \times \{1\}),$$
  锥底为 $L \times \{0\} \cong L$，锥顶为单点 $v = [L \times \{1\}]$。
- 附着空间为映射锥：
  $$Y = D \cup_L CL = (D \amalg CL) / \sim,\qquad [x, 0] \sim x \in D.$$
- 非约化悬挂 $\Sigma L$ 定义为两端分别缩为单点的柱：
  $$\Sigma L = (L \times [0, 1]) / \big(L \times \{0\} \sim s_0, \; L \times \{1\} \sim s_1\big),$$
  其中 $s_0 = [L \times \{0\}]$ 为南极，$s_1 = [L \times \{1\}]$ 为北极。

### 2. 楔点的选择
在楔和 $D \vee \Sigma L$ 中：
1. **$D$ 中的基点选择**：取零伦同伦的终点 $d_0 \in D$。
   - 说明：因为 $D$ 是路径连通 CW 复形，所有顶点均为非退化基点（well-pointed），若更换为 $D$ 中任意其它基点 $d_1$，由 $D$ 的路径连通性存在连接 $d_0$ 到 $d_1$ 的路径，该路径诱导同胚/同伦等价，同伦型在拓扑上不依赖于 $d_0$ 的选取。
2. **$\Sigma L$ 中的基点选择**：取悬挂极点之一，即南极 $s_0 = [L \times \{0\}]$。
   - 说明：在构造中，$L \times \{0\}$ 对应锥底，附着时被收缩与同伦终点 $d_0$ 粘贴。

因此，楔和空间为：
$$D \vee \Sigma L = (D \amalg \Sigma L) / (d_0 \sim s_0).$$

### 3. 同伦等价的显式构造与证明

#### (1) 构造显式映射 $\Phi: Y \to D \vee \Sigma L$
定义 $\Phi$ 如下：
- 对任意 $d \in D \subset Y$：
  $$\Phi(d) = d \in D \subset D \vee \Sigma L.$$
- 对任意 $[x, t] \in CL \subset Y$（$x \in L, t \in [0, 1]$）：
  $$\Phi([x, t]) = \begin{cases} H(x, 2t) \in D, & 0 \le t \le \frac{1}{2}, \\ [x, 2t - 1]_{\Sigma L} \in \Sigma L, & \frac{1}{2} \le t \le 1. \end{cases}$$

**连续性与良定义检验**：
- 在锥底 $t = 0$ 处：$\Phi([x, 0]) = H(x, 0) = x = \Phi|_D(x)$，与 $D$ 上的定义无缝缝合。
- 在分割点 $t = \frac{1}{2}$ 处：前半部分给出 $H(x, 1) = d_0 \in D$；后半部分给出 $[x, 0]_{\Sigma L} = s_0 \in \Sigma L$。在 $D \vee \Sigma L$ 中 $d_0 \sim s_0$ 被等同为楔点，两部分完全一致。
- 在锥顶 $t = 1$ 处：$[x, 1]_{\Sigma L} = s_1 \in \Sigma L$ 与 $x$ 无关，因此锥顶映射为悬挂北极 $s_1$，良定义。
由有限闭覆盖片断引理，$\Phi$ 连续。

#### (2) 构造显式映射 $\Psi: D \vee \Sigma L \to Y$
定义 $\Psi$ 如下：
- 对任意 $d \in D$：
  $$\Psi(d) = d \in D \subset Y.$$
- 对任意 $[x, u] \in \Sigma L$（$x \in L, u \in [0, 1]$）：
  $$\Psi([x, u]) = \begin{cases} H(x, 1 - 2u) \in D \subset Y, & 0 \le u \le \frac{1}{2}, \\ [x, 2u - 1] \in CL \subset Y, & \frac{1}{2} \le u \le 1. \end{cases}$$

**连续性与良定义检验**：
- 当 $u = 0$ 时：$\Psi([x, 0]) = H(x, 1) = d_0 = \Psi(d_0)$，故悬挂南极 $s_0$ 映为 $d_0$，与楔点一致。
- 当 $u = \frac{1}{2}$ 处：前半段为 $H(x, 0) = x \in D$；后半段为 $[x, 0] \in CL$。在 $Y = D \cup_L CL$ 中 $x \sim [x, 0]$，完全吻合。
- 当 $u = 1$ 时：$[x, 1] = v \in CL$ 为锥顶，与 $x$ 无关，良定义。
因此 $\Psi$ 连续。

#### (3) 同伦检验 $\Phi \circ \Psi \simeq \text{id}_{D \vee \Sigma L}$ 与 $\Psi \circ \Phi \simeq \text{id}_Y$
- 考察复合映射 $\Psi \circ \Phi$：
  - 在 $D$ 上为恒等映射。
  - 在 $CL$ 上，当参数沿 $t$ 变化时，前四分之一区段沿同伦 $H$ 从 $x$ 走到 $d_0$，中间四分之一区段沿逆同伦 $\bar{H}$ 从 $d_0$ 返回 $x$，后半区段为锥方向的线性重参数化。
  - 由于路径连接 $H \ast \bar{H}$ 零伦于常值路径 $c_x$（且该同伦保持端点 $x$），通过对区段长度进行标准同伦变形并抵消回环，可在保持边界 $D$ 不动的条件下构造相对同伦，使得 $\Psi \circ \Phi \simeq \text{id}_Y$。
- 同理，考察 $\Phi \circ \Psi$：
  - 在 $D$ 上为恒等。
  - 在 $\Sigma L$ 上，前半段在 $D$ 内形成闭路 $\bar{H} \ast H \simeq c_{d_0}$，收缩到楔点后，后半段退化为 $\Sigma L$ 自身的恒等映射，故 $\Phi \circ \Psi \simeq \text{id}_{D \vee \Sigma L}$。

综上，$Y \simeq D \vee \Sigma L$。

---

## S3 整数扭结的实例

### 1. 构造对象
取实射影平面 $\mathbb{R}P^2$ 的任一有限单纯三角剖分 $L$。

1. **构造有限单纯复形 $K$ 及顶点 $v$**：
   引入两个不相交的新顶点 $v$ 和 $w$（构成 0-球面 $S^0 = \{v, w\}$）。
   令 $K$ 为 $S^0$ 与 $L$ 的单纯连结（simplicial join），即 $L$ 的双锥（单纯悬挂）：
   $$K = S^0 * L = (v * L) \cup_L (w * L).$$
   其所有单形为：
   - $L$ 的单形 $\sigma$；
   - 锥单形 $v * \sigma$（$\sigma \in L$）；
   - 锥单形 $w * \sigma$（$\sigma \in L$）。
   指定 $v$ 为所求顶点。

2. **构造含 $v$ 的子复形 $B$**：
   在三角剖分 $L$ 中任意选取一个顶点 $u_0 \in L^{(0)}$。
   由于 $u_0 \in L = \text{lk}_K(v)$，一维闭单形（边）$e = [v, u_0]$ 属于 $K$。
   取 $B$ 为由该单形及其所有面构成的子复形：
   $$B = \{\emptyset, \, \{v\}, \, \{u_0\}, \, [v, u_0]\}.$$
   显然 $v \in B$，且 $B$ 是 $K$ 的有限单纯子复形。

### 2. 逐项验证全部所求条件

1. **$|K| \setminus \{v\}$ 非空且可缩**：
   - 从单纯复形中去掉顶点 $v$ 对应的开星闭包内部，即只保留不包含 $v$ 的单形。由定义，复形 $K$ 中不含 $v$ 的单形构成的全子复形恰为以 $w$ 为顶点的锥：
     $$K_0 = w * L.$$
   - 任意单形 $v * \sigma \in K$ 中除去 $v$ 后的点集，均可沿直线段强变形收缩至底单形 $\sigma \subset K_0$。该局部收缩在公共面上相容，故整体几何实现 $|K| \setminus \{v\}$ 强变形收缩到 $|K_0| = |w * L|$。
   - 由于 $|w * L|$ 是拓扑锥，它非空且是可缩空间，故 $|K| \setminus \{v\}$ 非空可缩。

2. **$(|B| \setminus \{v\}) \to |B|$ 为同伦等价**：
   - 几何实现 $|B|$ 是一维闭单形，同胚于闭区间 $[0, 1]$（令 $v$ 对应 $0$，$u_0$ 对应 $1$），故 $|B|$ 可缩。
   - 子空间 $|B| \setminus \{v\}$ 同胚于半开区间 $(0, 1]$，亦为可缩空间。
   - 包含映射 $(0, 1] \hookrightarrow [0, 1]$ 是两个可缩空间之间的连续映射，必然是同伦等价。

3. **$|K|$ 的约化有理同调全零**：
   - 几何实现 $|K|$ 同胚于非约化悬挂 $\Sigma |L| = \Sigma \mathbb{R}P^2$。
   - 由约化同调的悬挂同构定理：
     $$\widetilde{H}_k(|K|; \mathbb{Q}) \cong \widetilde{H}_k(\Sigma \mathbb{R}P^2; \mathbb{Q}) \cong \widetilde{H}_{k-1}(\mathbb{R}P^2; \mathbb{Q}),\quad \forall k \ge 0.$$
   - 实射影平面 $\mathbb{R}P^2$ 的约化有理同调为：
     $$\widetilde{H}_p(\mathbb{R}P^2; \mathbb{Q}) = 0,\quad \forall p \ge 0.$$
   - 因此对所有 $k \ge 0$ 均有 $\widetilde{H}_k(|K|; \mathbb{Q}) = 0$。

4. **$|K|$ 不可缩**：
   - 考察带整系数 $\mathbb{Z}$ 的奇异同调。悬挂同构给出：
     $$\widetilde{H}_2(|K|; \mathbb{Z}) \cong \widetilde{H}_1(\mathbb{R}P^2; \mathbb{Z}) \cong \mathbb{Z}/2\mathbb{Z} \neq 0.$$
   - 因为存在非平凡的二阶整挠同调群，空间 $|K|$ 绝不可缩。

---

## S4 整体对象与全部恢复目标

### 1. 结论判定
**结论：目标全部成立。** 能够完全刻画满足条件的所有可能同伦型、给出实现构造，并给出仅依赖 $v$ 的星/环有限关联数据的纯代数充要判据并完成证明。

### 2. $X = |K|$ 的可能同伦类型刻画定理
> **定理（同伦型分类刻画）**：
> 设 $K$ 是有限抽象单纯复形，$v \in K$ 是顶点，$B \subseteq K$ 是含 $v$ 的子复形。令 $X = |K|$，$O = X \setminus \{v\}$，$C = |B|$。若 $O$ 非空可缩且包含映射 $O \cap C \hookrightarrow C$ 是同伦等价，则：
> 1. $X$ 的同伦类型**当且仅当**是**某个非空有限单纯复形 $L$ 的非约化悬挂 $\Sigma |L|$ 的同伦型**。
> 2. 特别地，$X$ 必是单连通有限复形（$\pi_1(X) = 0$ 且具有有限 CW 复形同伦型）。

### 3. 刻画的充分性：全部类型的实现构造
设 $L$ 为任意给定的非空有限单纯复形。
- **构造三元组 $(K, v, B)$**：
  1. 取 0-单形集合 $S^0 = \{v, w\}$，定义 $K = S^0 * L = (v * L) \cup_L (w * L)$ 为双锥单纯复形。
  2. 任取 $L$ 的一个顶点 $u_0 \in L$。定义 $B$ 为闭 1-单形 $[v, u_0]$ 及其面构成的子复形。
- **验证原题全部条件**：
  - $X = |K| \cong \Sigma |L|$，实现了目标悬挂型。
  - $O = |K| \setminus \{v\}$ 强变形收缩到 $|w * L| = C|L|$，非空且可缩。
  - $C = |B| \cong [0, 1]$，$O \cap C = |B| \setminus \{v\} \cong (0, 1]$，两空间均可缩，包含映射必为同伦等价。
此构造覆盖了刻画中的全部类型。

### 4. 刻画的必要性证明
设 $(K, v, B)$ 满足条件。
1. **$v$ 在 $K$ 中的环（Link）必非空**：
   - 考虑 $L_B = \text{lk}_B(v)$。若 $L_B = \emptyset$，则 $v$ 是 $B$ 的孤立顶点，因此 $C = |B| = |B \setminus \{v\}| \amalg \{v\}$。
   - 此时 $O \cap C = |B \setminus \{v\}|$。包含映射 $O \cap C \hookrightarrow C$ 在连通分支集合诱导单射但不满（少一个分支 $\{v\}$），不可能是同伦等价。
   - 矛盾！故必有 $\text{lk}_B(v) \neq \emptyset$，进而：
     $$L = \text{lk}_K(v) \supseteq \text{lk}_B(v) \neq \emptyset.$$
2. **$|K| \simeq \Sigma |L|$ 的推导**：
   - 令 $K_0 = \{\sigma \in K : v \notin \sigma\}$ 为不含 $v$ 的全子复形。
   - 在几何实现中，对任意含 $v$ 的单形 $v * \tau$，点 $(1-t)v + t y$（$y \in |\tau|, t \in (0, 1]$）可沿直线径向投影至 $y \in |\tau| \subset |K_0|$。该局部收缩在公共面上相容，故 $|K_0|$ 是 $O = |K| \setminus \{v\}$ 的强变形收缩核。
   - 因为 $O$ 可缩，所以有限单纯复形 $|K_0|$ 是可缩空间。
   - 复形 $K$ 在几何上表达为将锥 $C|L|$ 沿底 $|L|$ 粘贴到 $|K_0|$：
     $$|K| = |K_0| \cup_{|L|} C|L|.$$
   - 因为 $|K_0|$ 可缩，包含映射 $|L| \hookrightarrow |K_0|$ 必然零伦。
   - 引用 **S2** 的结论（此时底空间 $D = |K_0|$ 路径连通，$L \neq \emptyset$ 为子复形且包含映射零伦）：
     $$|K| \simeq |K_0| \vee \Sigma |L| \simeq * \vee \Sigma |L| \cong \Sigma |L|.$$
证毕。

### 5. 判定 $X$ 可缩的有限关联数据充要条件及证明

#### (1) 关联数据提取与判据陈述
定义 $K$ 中含 $v$ 的单形集合为：
$$\text{Star}(v) = \{\sigma \in K : v \in \sigma\}.$$
完全利用这些单形及其面在 $K$ 中的有限关联数据，提取 $v$ 的环（Link）：
$$L = \text{lk}_K(v) = \{\sigma \setminus \{v\} : \sigma \in \text{Star}(v)\},$$
其面关系完全由 $\text{Star}(v)$ 的面的包含关系唯一决定。

> **判据（充要条件）**：
> 空间 $X = |K|$ 可缩，**当且仅当**环 $L = \text{lk}_K(v)$ 是**整系数无挠非空无约化同调复形（Acyclic Complex）**，即其单纯约化同调群全为零：
> $$\widetilde{H}_k(L; \mathbb{Z}) = 0,\quad \forall k \ge 0.$$

#### (2) 有限可检验性说明
- $L$ 是有限单纯复形，其链群 $C_k(L)$ 是有限秩自由阿贝尔群。
- 边缘映射矩阵 $\partial_k: C_k(L) \to C_{k-1}(L)$ 仅通过面包含的关联正负号有限确定。
- 条件 $\widetilde{H}_k(L; \mathbb{Z}) = 0$ 等价于：
  1. $k = 0$：$\operatorname{rank}(\ker \partial_0) - \operatorname{rank}(\operatorname{im} \partial_1) = 1$（即 $H_0(L) \cong \mathbb{Z}$，复形连通）；
  2. $k \ge 1$：$\ker \partial_k = \operatorname{im} \partial_{k+1}$，通过整矩阵的 Smith 标准形在有限步四则运算内完全判定不变因子是否全为 1。

#### (3) 判据的充要性证明
由前述刻画，$X \simeq \Sigma |L|$。
- **必要性（$\implies$）**：
  若 $X$ 可缩，则 $\widetilde{H}_n(X; \mathbb{Z}) = 0$（$\forall n \ge 0$）。
  根据非约化悬挂的同调同构（Suspension Isomorphism）：
  $$\widetilde{H}_{k-1}(|L|; \mathbb{Z}) \cong \widetilde{H}_k(\Sigma |L|; \mathbb{Z}) \cong \widetilde{H}_k(X; \mathbb{Z}) = 0,\quad \forall k \ge 0.$$
  故必有 $\widetilde{H}_*(L; \mathbb{Z}) = 0$。

- **充分性（$\impliedby$）**：
  假设 $\widetilde{H}_*(L; \mathbb{Z}) = 0$。
  1. $\widetilde{H}_0(L; \mathbb{Z}) = 0 \implies |L|$ 是非空路径连通空间。
  2. 计算一维基本群：因为 $|L|$ 路径连通，悬挂 $\Sigma |L|$ 是两个可缩锥 $C_+ |L|$ 与 $C_- |L|$ 沿路径连通交集 $|L|$ 的粘贴。由 Seifert-van Kampen 定理：
     $$\pi_1(\Sigma |L|) \cong \pi_1(C_+ |L|) *_{\pi_1(|L|)} \pi_1(C_- |L|) = 0 *_{\pi_1(|L|)} 0 = 0.$$
     因此 $\Sigma |L|$ 必是单连通空间。
  3. 由悬挂同构，对任意 $n \ge 0$：
     $$\widetilde{H}_n(\Sigma |L|; \mathbb{Z}) \cong \widetilde{H}_{n-1}(|L|; \mathbb{Z}) = 0.$$
  4. 引用 **Hurewicz 定理**：因为 $\Sigma |L|$ 单连通且所有约化整同调为零，其所有阶同伦群均平凡：
     $$\pi_n(\Sigma |L|) = 0,\quad \forall n \ge 1.$$
  5. 引用 **Whitehead 定理**：有限 CW 复形到单点的映射诱导所有同伦群的同构，故该映射为同伦等价：
     $$X \simeq \Sigma |L| \simeq *.$$
充要性证毕。

---

## S5 不提供子复形 B

### 1. 判定结论
**结论：不必。**
当仅假设 $|K| \setminus \{v\}$ 非空可缩、不提供子复形 $B$ 及其同伦条件时，$|K|$ **不一定**同伦等价于非空有限复形的悬挂。

### 2. 分类新增的可能类型
> **定理（无 $B$ 时的完整分类）**：
> 仅在 $|K| \setminus \{v\}$ 非空可缩的条件下，可能的同伦类型恰有两类：
> 1. **原类型**：非空有限单纯复形的悬挂 $\Sigma |L|$（对应 $\text{lk}_K(v) \neq \emptyset$）；
> 2. **唯一新增类型**：**离散双点空间 $S^0 \simeq * \amalg *$（0-球面）**（对应 $\text{lk}_K(v) = \emptyset$）。

### 3. 证明与实现

#### (1) 为什么新增类型必为 $S^0$
设 $K$ 为有限单纯复形，$v \in K$。令 $K_0 = \{\sigma \in K : v \notin \sigma\}$。
正如 S4 中证明的，$|K| \setminus \{v\}$ 强变形收缩到 $|K_0|$。因为 $|K| \setminus \{v\}$ 可缩，故 $|K_0|$ 是非空可缩有限复形（特别地，$|K_0|$ 路径连通）。

根据 $v$ 在 $K$ 中的环 $L = \text{lk}_K(v)$ 是否为空分两类：
- **情形 1：$L \neq \emptyset$**
  此时由 S2 依然可推导 $|K| = |K_0| \cup_{|L|} C|L| \simeq \Sigma |L|$，落在非空有限复形的悬挂型中。
- **情形 2：$L = \emptyset$**
  此时 $v$ 是 $K$ 的孤立顶点，没有任何单形同时包含 $v$ 与 $K_0$ 的顶点。
  因此拓扑空间 $|K|$ 是不交并：
  $$|K| = |K_0| \amalg \{v\}.$$
  因为 $|K_0|$ 可缩（$|K_0| \simeq *$），$\{v\} \cong *$，所以：
  $$|K| \simeq * \amalg * = S^0.$$

#### (2) 证明 $S^0$ 不能表示为任何非空空间的悬挂
设 $Y$ 为任意**非空**拓扑空间。其非约化悬挂为：
$$\Sigma Y = (Y \times [-1, 1]) / \big(Y \times \{-1\} \sim s_0, \; Y \times \{1\} \sim s_1\big).$$
取定任一点 $y_0 \in Y$。弧 $\{y_0\} \times [-1, 1]$ 给出连接南极 $s_0$ 与北极 $s_1$ 的连续路径；而对任意点 $[y, t] \in \Sigma Y$，弧 $\{y\} \times [-1, t]$ 将其连至南极 $s_0$。
因此，**任何非空空间的悬挂 $\Sigma Y$ 必是路径连通空间**。
然而 $S^0$ 具有 2 个路径连通分支，绝不可能同伦等价于任何非空空间的悬挂。

#### (3) 新增类型的显式实现
取 $K_0$ 为任意非空可缩有限单纯复形（例如单个 0-单形 $\{w\}$ 或任意标准单形 $\Delta^n$），取 $v$ 为一个不相交的孤立 0-单形。令 $K = K_0 \amalg \{v\}$。
- $|K| \setminus \{v\} = |K_0| \simeq *$ 非空可缩，完全满足前提；
- $|K| = |K_0| \amalg \{v\} \simeq S^0$。
此分类穷尽所有情形。

---

## S6 悬挂信息的逆向恢复

### 1. 判定结论
**结论：不成立（不必推出）。**
即对非空有限单纯复形 $L_1, L_2$，由 $\Sigma |L_1| \simeq \Sigma |L_2|$ **不能**推出 $|L_1| \simeq |L_2|$。

### 2. 完整反例构造与验证

#### (1) 反例的构造
1. **取 $L_1$ 为单个顶点（0-单形）**：
   $$L_1 = \Delta^0 = \{p\}.$$
   显然 $|L_1| = \{p\}$ 是单点可缩空间。
2. **取 $L_2$ 为带非平凡基本群的整无挠（Acyclic）2-维复形**：
   选取二阶特殊线性群 $SL(2, 5)$（即二元二十面体群，阶数为 120），其为非平凡完美群。该群拥有平衡展示（2 个生成元、2 个关系元）：
   $$G = \langle a, b \mid r_1 = 1, \; r_2 = 1 \rangle = \langle a, b \mid a^5 b^{-3} = 1, \; a^5 (ab)^{-2} = 1 \rangle.$$
   取该展示的标准 2-维展示胞腔复形 $X_G$（1 个 0-胞腔，2 个 1-胞腔，2 个 2-胞腔）。取 $X_G$ 的任一有限单纯三角剖分为 $L_2$。

#### (2) 验证 $|L_1| \not\simeq |L_2|$
- 空间 $|L_1| = \Delta^0$ 是一点，基本群为平凡群：
  $$\pi_1(|L_1|) = 0.$$
- 空间 $|L_2| \cong X_G$ 的基本群由其展示确定：
  $$\pi_1(|L_2|) \cong G = SL(2, 5).$$
  因为 $|SL(2, 5)| = 120 \neq 1$，其基本群非平凡。
- 同伦等价必诱导基本群的同构，故：
  $$|L_1| \not\simeq |L_2|.$$

#### (3) 验证 $\Sigma |L_1| \simeq \Sigma |L_2|$
1. **悬挂 $\Sigma |L_1|$ 的同伦型**：
   $\Sigma |L_1| = \Sigma(\Delta^0) \cong [-1, 1] \simeq *$（可缩）。
2. **悬挂 $\Sigma |L_2|$ 的同伦型**：
   - 先求 $|L_2|$ 的同调群。复形 $X_G$ 的胞腔链群在 1 维与 2 维均为 $\mathbb{Z}^2$：
     $$C_2(X_G) = \mathbb{Z}^2 \xrightarrow{\partial_2} C_1(X_G) = \mathbb{Z}^2 \xrightarrow{\partial_1 = 0} C_0(X_G) = \mathbb{Z}.$$
     边界映射 $\partial_2$ 的矩阵即两关系元在自由阿贝尔化群中的指数和矩阵。
     - 对 $r_1 = a^5 b^{-3}$，$a, b$ 指数和分别为 $5, -3$；
     - 对 $r_2 = a^5 b^{-1} a^{-1} b^{-1} a^{-1}$，$a$ 指数和为 $5 - 1 - 1 = 3$，$b$ 指数和为 $-1 - 1 = -2$。
     其关联矩阵为：
     $$M = \begin{pmatrix} 5 & -3 \\ 3 & -2 \end{pmatrix}.$$
     计算行列式：
     $$\det M = 5(-2) - (-3)(3) = -10 + 9 = -1 \neq 0.$$
     由于 $\det M = \pm 1$，$M$ 在整环 $\mathbb{Z}$ 上完全可逆。
     因此：
     $$H_1(|L_2|; \mathbb{Z}) = \operatorname{coker} M = 0,\qquad H_2(|L_2|; \mathbb{Z}) = \ker M = 0.$$
     由于 $\dim |L_2| = 2$，对所有 $k \ge 1$ 均有 $H_k(|L_2|; \mathbb{Z}) = 0$，且 $H_0(|L_2|; \mathbb{Z}) = \mathbb{Z}$。
     即 $|L_2|$ 是**非空路径连通且整同调全平凡的无挠复形（$\widetilde{H}_*(|L_2|; \mathbb{Z}) = 0$）**。
   - 再考察悬挂 $\Sigma |L_2|$：
     - 因为 $|L_2|$ 路径连通，由 Seifert-van Kampen 定理：
       $$\pi_1(\Sigma |L_2|) = 0.$$
     - 由悬挂同构：
       $$\widetilde{H}_k(\Sigma |L_2|; \mathbb{Z}) \cong \widetilde{H}_{k-1}(|L_2|; \mathbb{Z}) = 0,\quad \forall k \ge 0.$$
     - 因此 $\Sigma |L_2|$ 是单连通且带平凡整同调的有限 CW 复形。
     - 由 Hurewicz 定理与 Whitehead 定理，任何单连通且同调平凡的 CW 复形必定可缩：
       $$\Sigma |L_2| \simeq *.$$

综上所述：
$$\Sigma |L_1| \simeq * \simeq \Sigma |L_2|, \qquad \text{但} \quad |L_1| \not\simeq |L_2|.$$
反例成立，命题得证不成立。
