本题探讨有限单纯复形中**顶点删除**对复形整体同伦型的拓扑控制，揭示了“非可切除开闭覆盖”在同伦推出中的经典陷阱，并将整体同伦型完全归结为该顶点的**连杆（Link）**的悬空。以下给出完整的刻画定理、实现构造、代数检验判据及其严格证明。

---

### 一、 核心概念与符号约定

设 $K$ 为有限抽象单纯复形，$v \in K^{(0)}$ 为其一个顶点。
- **闭星与开星**：
  $$\overline{\operatorname{St}}_K(v) = \{\sigma \in K \mid \exists \tau \in K, v \in \tau \text{ 且 } \sigma \subseteq \tau\}, \qquad \operatorname{st}_K(v) = \{x \in |K| \mid x(v) > 0\}.$$
- **连杆（Link）**：
  $$\operatorname{lk}_K(v) = \{\tau \in \overline{\operatorname{St}}_K(v) \mid v \notin \tau\} = \{\tau \in K \mid v \notin \tau, \tau \cup \{v\} \in K\}.$$
- **顶点删除（Deletion）**：$K - v = \{\sigma \in K \mid v \notin \sigma\}$，它是 $K$ 中不含 $v$ 的极大子复形。

---

### 二、 同伦型刻画定理

> **定理 1（同伦型刻画）**  
> 设三元组 $(K, v, B)$ 满足条件：
> 1. $K$ 是有限单纯复形，$v$ 是 $K$ 的顶点，$B \subseteq K$ 是含 $v$ 的子复形；
> 2. $O = |K| \setminus \{v\}$ 非空且可缩；
> 3. 包含映射 $i: O \cap C \hookrightarrow C$ 是同伦等价（其中 $C = |B|$）。
> 
> 则空间 $X = |K|$ 的可能同伦类型为：
> **所有非空有限单纯复形的几何实现的悬空（Suspension）的同伦型**，即
> $$\mathcal{H} = \{ [X] \mid X \simeq \Sigma |L|, \text{ 其中 } L \text{ 为非空有限单纯复形} \}.$$
> 
> 特别地，$X$ 必为连通紧多面体，其基本群 $\pi_1(X)$ 必为有限秩自由群 $F_r$（$r = |\pi_0(\operatorname{lk}_K(v))| - 1 \ge 0$），且正维数约化上同调环的杯积恒为零。

---

### 三、 刻画定理的证明

#### 步骤 1：证明 $\operatorname{lk}_K(v) \ne \emptyset$
若 $\operatorname{lk}_K(v) = \emptyset$，则 $v$ 是 $K$ 的孤立顶点。因 $v \in B \subseteq K$，$v$ 也是 $B$ 的孤立顶点。
此时：
$$C = |B| = (|B| \setminus \{v\}) \sqcup \{v\} = (O \cap C) \sqcup \{v\}.$$
包含映射 $i: O \cap C \hookrightarrow C$ 的像不包含连通分支 $\{v\}$，导致诱导映射 $\pi_0(O \cap C) \to \pi_0(C)$ 不是满射，与 $i$ 是同伦等价矛盾。
因此必须有 $\operatorname{lk}_B(v) \ne \emptyset$，从而 $\operatorname{lk}_K(v) \ne \emptyset$。

#### 步骤 2：证明 $X \simeq \Sigma |\operatorname{lk}_K(v)|$
我们从两套视角给出证明：

- **法一（开覆盖与同伦推出）**：
  在 $X = |K|$ 中选取开覆盖 $\{W_1, W_2\}$：
  $$W_1 = O = X \setminus \{v\}, \qquad W_2 = \operatorname{st}_K(v) = \{x \in |K| \mid x(v) > 0\}.$$
  二者皆为 $X$ 的开子集，且 $W_1 \cup W_2 = X$。
  1. $W_1 = O$ 按题设为非空可缩空间，$W_1 \simeq *$；
  2. $W_2 = \operatorname{st}_K(v)$ 是以 $v$ 为顶点的开锥，存在向 $v$ 的星形直线同伦，故 $W_2 \simeq *$；
  3. 二者的交集为：
     $$W_1 \cap W_2 = \operatorname{st}_K(v) \setminus \{v\} = \{x \in |K| \mid 0 < x(v) < 1\}.$$
     沿以 $v$ 为起点的射线作径向形变收缩：
     $$r_t(x) = (1-t)x + t \frac{x - x(v)v}{1 - x(v)}, \quad t \in [0, 1],$$
     易见 $W_1 \cap W_2$ 强变形收缩到其边界底空间 $|\operatorname{lk}_K(v)|$。故 $W_1 \cap W_2 \simeq |\operatorname{lk}_K(v)|$。
  
  由于 $\{W_1, W_2\}$ 是开覆盖，由广义 Seifert-van Kampen 定理与同伦推出性质，$X$ 同伦等价于图表
  $$W_1 \hookleftarrow W_1 \cap W_2 \hookrightarrow W_2$$
  的同伦推出。代入同伦型即为图表 $* \leftarrow |\operatorname{lk}_K(v)| \rightarrow *$ 的同伦推出，按定义该同伦推出即为未约化悬空：
  $$X \simeq \Sigma |\operatorname{lk}_K(v)|.$$

- **法二（单纯胞腔附着）**：
  $K$ 可严格写为子复形的粘合：
  $$K = (K - v) \cup_{\operatorname{lk}_K(v)} (v * \operatorname{lk}_K(v)).$$
  在几何实现中，$O = |K| \setminus \{v\}$ 强形变收缩到 $|K - v|$。由于 $O$ 可缩，有限复形 $|K - v|$ 可缩。
  圆锥 $|v * \operatorname{lk}_K(v)| = C(|\operatorname{lk}_K(v)|)$ 可缩，且包含映射 $|\operatorname{lk}_K(v)| \hookrightarrow C(|\operatorname{lk}_K(v)|)$ 是单纯闭包含，故为余纤维化（Cofibration）。
  因此几何实现粘合即为同伦推出：
  $$X = |K| \simeq |K - v| \cup_{|\operatorname{lk}_K(v)|} C(|\operatorname{lk}_K(v)|) \simeq * \cup_{|\operatorname{lk}_K(v)|} * = \Sigma |\operatorname{lk}_K(v)|.$$

因为 $\operatorname{lk}_K(v)$ 是非空有限单纯复形，故 $X$ 必具有非空有限单纯复形悬空的同伦型。

> [!NOTE]
> **关于 $B$ 的本质作用说明**：
> 拓扑对 $(O, C)$ 中 $O$ 为开集而 $C$ 为闭集，它们不构成切除对（Excisive couple），因此空间 $X = O \cup C$ **并不等同于** $O$ 与 $C$ 沿 $O \cap C$ 的同伦推出。条件“$O \cap C \hookrightarrow C$ 是同伦等价”不意味着 $X \simeq O \simeq *$，它仅施加了 $\operatorname{lk}_B(v)$ 到 $|B| \setminus \{v\}$ 沿映射柱的可缩性约束，而允许 $X$ 具有多样的悬空同伦型。

---

### 四、 全部同伦类型的实现构造

设 $L$ 是任意给定的**非空有限抽象单纯复形**，目标是构造满足原题全部条件的三元组 $(K, v, B)$，使得 $|K| \simeq \Sigma |L|$。

#### 1. 复形 $K$ 与顶点 $v$ 的构造
取两个不在 $L$ 中的相异新顶点 $v, w \notin L^{(0)}$。
定义 $K$ 为 $L$ 的**单纯悬空（Simplicial Suspension）**：
$$K = \Sigma_{\operatorname{simp}} L = (w * L) \cup_L (v * L).$$
显式地，$K$ 的顶点集为 $V(K) = V(L) \cup \{v, w\}$，其单形为：
- $L$ 中的所有单形 $\sigma$；
- $\sigma \cup \{w\}$ 及 $\{w\}$（其中 $\sigma \in L$）；
- $\sigma \cup \{v\}$ 及 $\{v\}$（其中 $\sigma \in L$）。

因为 $L$ 有限，故 $K$ 是有限单纯复形。显然 $v \in K^{(0)}$，且：
$$\operatorname{lk}_K(v) = L.$$

#### 2. 条件检验：$O = |K| \setminus \{v\}$ 可缩
由构造，$K - v = w * L$。这是以 $w$ 为顶点的单纯圆锥。
其几何实现 $|K - v| = |w * L|$ 是几何圆锥，存在沿射线向顶点 $w$ 的压缩同伦：
$$H(x, t) = (1-t)x + tw, \quad t \in [0, 1],$$
因此 $|K - v|$ 可缩。
由于 $O = |K| \setminus \{v\}$ 强形变收缩到 $|K - v|$，复合收缩同伦可知 $O$ 是非空可缩空间。

#### 3. 子复形 $B$ 的构造与包含等价验证
因为 $L \ne \emptyset$，必存在顶点 $u \in L^{(0)}$。
在 $K$ 中，$\{v, u\}$ 构成一条 1-单形（边）。
定义 $B$ 为由该 1-单形及其面构成的子复形：
$$B = \Delta^1 = \{\{v\}, \{u\}, \{v, u\}\} \subseteq K.$$
显然 $v \in B$。
对应拓扑空间：
- $C = |B| = [v, u]$，同胚于闭单位区间 $[0, 1]$，是可缩空间；
- $O \cap C = |B| \setminus \{v\} = (v, u]$，同胚于半开区间 $(0, 1]$，亦是可缩空间。

由于定义域与陪域皆为可缩空间，包含映射
$$i: O \cap C \hookrightarrow C$$
必然是同伦等价（其逆映射可取映至任一点的常值映射）。

#### 4. 空间 $|K|$ 的同伦型
由悬空的几何实现与单纯悬空的相容性：
$$X = |K| = |\Sigma_{\operatorname{simp}} L| \cong \Sigma |L|.$$
这就为所有形如 $\Sigma |L|$ 的同伦类型构造了满足原题条件的实现三元组 $(K, v, B)$。

---

### 五、 $X$ 可缩的有限组合关联判据

#### 1. 判据陈述

> **定理 2（$X$ 可缩的充要条件）**  
> 设三元组 $(K, v, B)$ 满足题设条件。$X = |K|$ 可缩的充分必要条件是：
> **连杆 $\operatorname{lk}_K(v)$ 在整系数上是约化无圈的（Acyclic over $\mathbb{Z}$）**，即满足：
> $$\tilde{H}_k(\operatorname{lk}_K(v); \mathbb{Z}) = 0, \quad \forall k \ge -1.$$

#### 2. 判据只依赖于包含 $v$ 的单形及其面的有限关联数据
只需使用 $K$ 中含 $v$ 的单形及其面的关联数据，具体检验流程如下（完全有限且算法化）：
1. **提取连杆单形集**：
   收集 $K$ 中所有包含 $v$ 的单形，记为 $\operatorname{Star}_K(v)$。取出其全体面，构成闭星 $\overline{\operatorname{St}}_K(v)$。
   定义集合：
   $$\operatorname{lk}_K(v) = \{\tau \in \overline{\operatorname{St}}_K(v) \mid v \notin \tau\}.$$
   其单形间的包含（面）关系完全由 $K$ 中原始关联数据决定。
2. **构建单纯链复形**：
   对 $\operatorname{lk}_K(v)$ 各维单形指定任意定向，写出整系数链复形 $C_*(\operatorname{lk}_K(v))$ 的有限阶边界矩阵：
   $$\partial_k: C_k(\operatorname{lk}_K(v)) \longrightarrow C_{k-1}(\operatorname{lk}_K(v)).$$
3. **有限线性代数判定（Smith 标准形）**：
   计算各 $\partial_k$ 的 Smith 标准形：
   - **$k = -1$ 维**：$\operatorname{lk}_K(v) \ne \emptyset$（即 $\overline{\operatorname{St}}_K(v)$ 包含至少一条含 $v$ 的边）；
   - **$k = 0$ 维（连通性）**：$\operatorname{rank}(\partial_1) = n_0 - 1$（其中 $n_0 = |(\operatorname{lk}_K(v))^{(0)}|$）；
   - **$k \ge 1$ 维**：
     $$\operatorname{rank}(\partial_k) + \operatorname{rank}(\partial_{k+1}) = n_k \quad (n_k = \dim C_k(\operatorname{lk}_K(v))),$$
     且 $\partial_{k+1}$ 的所有不变因子（Elementary Divisors）均为 $1$（即无挠子群）。

满足上述有限步代数检验等价于 $\operatorname{lk}_K(v)$ 约化无圈。

---

### 六、 判据的充分性与必要性证明

#### 1. 必要性（$X$ 可缩 $\implies \operatorname{lk}_K(v)$ 约化无圈）
假设 $X = |K|$ 可缩，则其所有维数的约化同调群均为零：
$$\tilde{H}_k(X; \mathbb{Z}) = 0, \quad \forall k \ge 0.$$
由定理 1 的证明知 $X \simeq \Sigma |\operatorname{lk}_K(v)|$。
利用约化同调的悬空同构定理（Suspension Isomorphism）：
$$\tilde{H}_k(\Sigma |\operatorname{lk}_K(v)|; \mathbb{Z}) \cong \tilde{H}_{k-1}(|\operatorname{lk}_K(v)|; \mathbb{Z}), \quad \forall k \ge 0.$$
因此：
$$\tilde{H}_{k-1}(\operatorname{lk}_K(v); \mathbb{Z}) = 0, \quad \forall k \ge 0.$$
令 $m = k - 1$，即得对所有 $m \ge -1$：
$$\tilde{H}_m(\operatorname{lk}_K(v); \mathbb{Z}) = 0.$$
故 $\operatorname{lk}_K(v)$ 必为整系数约化无圈复形。

#### 2. 充分性（$\operatorname{lk}_K(v)$ 约化无圈 $\implies X$ 可缩）
假设 $\operatorname{lk}_K(v)$ 为整系数约化无圈复形：
1. **单连通性**：
   因 $\tilde{H}_{-1}(\operatorname{lk}_K(v)) = 0$，知 $\operatorname{lk}_K(v) \ne \emptyset$；
   因 $\tilde{H}_0(\operatorname{lk}_K(v); \mathbb{Z}) = 0$，知 $\operatorname{lk}_K(v)$ 是通路连通的。
   悬空空间 $\Sigma |\operatorname{lk}_K(v)|$ 可覆以两个开锥 $C_+ |\operatorname{lk}_K(v)|$ 与 $C_- |\operatorname{lk}_K(v)|$，二者均单连通（可缩），其交集同伦等价于通路连通空间 $|\operatorname{lk}_K(v)|$。
   由 Seifert-van Kampen 定理：
   $$\pi_1(\Sigma |\operatorname{lk}_K(v)|) \cong \{1\} *_{\pi_1(|\operatorname{lk}_K(v)|)} \{1\} = \{1\}.$$
   因此 $X \simeq \Sigma |\operatorname{lk}_K(v)|$ 是**单连通空间**。
2. **同伦群全消亡**：
   由悬空同构定理，对所有 $k \ge 1$：
   $$\tilde{H}_k(X; \mathbb{Z}) \cong \tilde{H}_{k-1}(\operatorname{lk}_K(v); \mathbb{Z}) = 0.$$
   由于 $X$ 单连通且约化同调群全为零，由 **Hurewicz 定理**，其所有同伦群均为平凡群：
   $$\pi_k(X) = 0, \quad \forall k \ge 1.$$
3. **可缩性**：
   有限单纯复形的几何实现 $X$ 是紧 CW 复形。由于 $X$ 连通且全部同伦群为零，由 **Whitehead 定理**，从 $X$ 到单点空间的映射是同伦等价。
   因此 $X$ 是可缩空间。

证毕。
