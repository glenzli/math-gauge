本问题涉及无限凸约束优化问题的有限松弛恢复理论。由于指标集 $I$ 可以是任意无限集（包括不可数集），我们将在此建立基于**有向网（Net）**与 **Hilbert 空间几何性质**的严格恢复理论。

---

### 一、 符号说明与基础准备

1. **有向集结构**：
   记 $\mathcal{F}(I) = \{F \subseteq I : F \text{ 是有限集}\}$ 为 $I$ 的所有有限子集构成的集合。按包含关系定义偏序：
   $$F_1 \le F_2 \iff F_1 \subseteq F_2.$$
   对任意 $F_1, F_2 \in \mathcal{F}(I)$，有 $F_1 \cup F_2 \in \mathcal{F}(I)$ 且 $F_1 \le F_1 \cup F_2, F_2 \le F_1 \cup F_2$。因此 $(\mathcal{F}(I), \subseteq)$ 是一个有向集（Directed Set），所有以 $F \in \mathcal{F}(I)$ 为标号的族均构成网（Net）。

2. **集合包含链**：
   对 $F_1 \subseteq F_2$，显然有：
   $$C \subseteq C_{F_2} \subseteq C_{F_1} \subseteq C_\varnothing = H.$$

3. **Hilbert 空间闭凸集的投影定理与变分特征**：
   设 $K \subseteq H$ 为非空闭凸集。由经典的投影定理：
   - 对任意 $x \in H$，存在唯一的 $P_K x \in K$ 使得 $\|x - P_K x\| = \inf_{z \in K} \|x - z\| = \operatorname{dist}(x, K)$。
   - 元素 $u = P_K x$ 的充要变分刻画为：
     $$u \in K \quad \text{且} \quad \langle x - u, z - u \rangle \le 0 \quad (\forall z \in K).$$
   - 由此可直接推出重要的**广义勾股等式/不等式**：对任意 $z \in K$，
     $$\|x - z\|^2 = \|(x - P_K x) - (z - P_K x)\|^2 = \|x - P_K x\|^2 + \|z - P_K x\|^2 - 2\langle x - P_K x, z - P_K x \rangle \ge \|x - P_K x\|^2 + \|z - P_K x\|^2.$$
     特别地：
     $$\|z - P_K x\|^2 \le \|x - z\|^2 - \|x - P_K x\|^2 \quad (\forall z \in K).$$

---

### 二、 映射 $P: H \to C$ 的构造与存在唯一性

#### 1. 全局可行域 $C$ 的非空性、闭性与凸性
- **闭性与凸性**：$C = \bigcap_{i\in I} C_i$ 是任意族闭凸集的交，因而是闭凸集。
- **非空性**：
  设 $K = \bar{B}(0, B) = \{z \in H : \|z\| \le B\}$ 为闭球。由实 Hilbert 空间的自反性（或 Banach-Alaoglu 定理），闭球 $K$ 在弱拓扑 $\sigma(H, H^*)$ 下是**弱紧的**。
  每个 $C_i$ 是闭凸集，由 Mazur 定理（或 Hahn-Banach 分离定理），闭凸集必为弱闭集。因此每个 $C_i \cap K$ 都是弱紧集 $K$ 的弱闭子集，从而是**弱紧集**。
  已知条件保证：对任意有限集 $F \subseteq I$，存在 $z_F \in K$ 使得 $z_F \in \bigcap_{i \in F} C_i = C_F$。即：
  $$\bigcap_{i \in F} (C_i \cap K) = C_F \cap K \neq \varnothing.$$
  这表明族 $\{C_i \cap K\}_{i \in I}$ 具有有限交性质（Finite Intersection Property）。
  由紧空间的有限交性质，全交非空：
  $$C \cap K = \bigcap_{i \in I} (C_i \cap K) \neq \varnothing.$$
  特别地，存在 $z \in C$ 满足 $\|z\| \le B$，故 $C \neq \varnothing$。

#### 2. 映射 $P$ 的定义
由于 $C \subseteq H$ 是**非空闭凸集**，根据 Hilbert 空间度量投影定理，对任意 $x \in H$，极小化问题
$$\min_{z \in C} \|x - z\|$$
存在唯一的最小点。我们定义映射 $P: H \to C$ 为：
$$Px = P_C x = \operatorname{argmin}_{z \in C} \|x - z\|.$$
由投影的唯一性，$Px$ 是 $\|x - z\|$ 在 $C$ 上的唯一最小点。

---

### 三、 网 $(P_F x)_{F \in \mathcal{F}(I)}$ 在范数中收敛到 $Px$

固定任意 $x \in H$。记有限问题的最优目标值（距离）为：
$$d_F(x) = \|x - P_F x\| = \operatorname{dist}(x, C_F).$$

#### 1. 距离网的单调性与有界性
若 $F_1 \subseteq F_2$，则 $C_{F_2} \subseteq C_{F_1}$，可行域变小导致最优目标值不减：
$$d_{F_1}(x) = \inf_{z \in C_{F_1}} \|x - z\| \le \inf_{z \in C_{F_2}} \|x - z\| = d_{F_2}(x).$$
同时，对任意 $F \in \mathcal{F}(I)$，由于 $C \subseteq C_F$，有：
$$d_F(x) \le \|x - Px\| \le \|x\| + \|Px\| \le \|x\| + B < +\infty.$$
因此，实数网 $(d_F^2(x))_{F \in \mathcal{F}(I)}$ 是**单调递增且上有界**的网。
在 $\mathbb{R}$ 中，每个单调有界的有向网必收敛到其上确界。记：
$$L(x) = \sup_{F \in \mathcal{F}(I)} d_F^2(x) = \lim_{F \in \mathcal{F}(I)} d_F^2(x) \le \|x - Px\|^2.$$

#### 2. 点列增量估计与柯西网证明
设 $F_1 \subseteq F_2$。此时 $P_{F_2} x \in C_{F_2} \subseteq C_{F_1}$。
应用第一节中关于集合 $C_{F_1}$ 投影的变分不等式，并将 $z$ 取为 $P_{F_2} x \in C_{F_1}$：
$$\|P_{F_2} x - P_{F_1} x\|^2 \le \|x - P_{F_2} x\|^2 - \|x - P_{F_1} x\|^2 = d_{F_2}^2(x) - d_{F_1}^2(x).$$

现在证明网 $(P_F x)_{F \in \mathcal{F}(I)}$ 是 $H$ 中的**柯西网**（Cauchy Net）：
- 对任意 $\varepsilon > 0$，由上确界定义，存在 $F_0 \in \mathcal{F}(I)$ 使得：
  $$L(x) - \frac{\varepsilon^2}{4} < d_{F_0}^2(x) \le L(x).$$
- 对任意 $F_1, F_2 \in \mathcal{F}(I)$ 满足 $F_1 \supseteq F_0$ 且 $F_2 \supseteq F_0$，取 $F_3 = F_1 \cup F_2 \in \mathcal{F}(I)$。
- 此时 $F_3 \supseteq F_1 \supseteq F_0$，由单调性：
  $$L(x) - \frac{\varepsilon^2}{4} < d_{F_0}^2(x) \le d_{F_1}^2(x) \le d_{F_3}^2(x) \le L(x).$$
  因此：
  $$\|P_{F_3} x - P_{F_1} x\|^2 \le d_{F_3}^2(x) - d_{F_1}^2(x) < \frac{\varepsilon^2}{4} \implies \|P_{F_3} x - P_{F_1} x\| < \frac{\varepsilon}{2}.$$
- 同理，由 $F_3 \supseteq F_2 \supseteq F_0$，有：
  $$\|P_{F_3} x - P_{F_2} x\| < \frac{\varepsilon}{2}.$$
- 结合三角不等式：
  $$\|P_{F_1} x - P_{F_2} x\| \le \|P_{F_1} x - P_{F_3} x\| + \|P_{F_3} x - P_{F_2} x\| < \frac{\varepsilon}{2} + \frac{\varepsilon}{2} = \varepsilon.$$

这证明了 $(P_F x)_{F \in \mathcal{F}(I)}$ 确实是 $H$ 中的柯西网。

#### 3. 完备性与极限定理
因为 Hilbert 空间 $H$ 是完备的度量空间，度量空间中的每个柯西网都强收敛到唯一点。
> **附注（度量空间中柯西网的收敛性）**：取单调递增序列 $F_n \in \mathcal{F}(I)$ 满足当 $F, F' \supseteq F_n$ 时 $\|P_F x - P_{F'} x\| < 2^{-n}$。则子列 $(P_{F_n} x)_{n=1}^\infty$ 是柯西列，必强收敛到某点 $x^* \in H$。进而容易验证整个网 $P_F x$ 都在范数下收敛到 $x^*$。

即存在 $x^* \in H$，满足：
$$\lim_{F \in \mathcal{F}(I)} \|P_F x - x^*\| = 0.$$

#### 4. 证明极限点 $x^* = Px$
我们需要验证 $x^*$ 的**可行性**与**最优性**：

- **可行性（$x^* \in C$）**：
  任意固定指标 $i \in I$，考察单点集 $F_{\{i\}} = \{i\} \in \mathcal{F}(I)$。
  对所有 $F \supseteq \{i\}$，根据定义均有 $P_F x \in C_F \subseteq C_i$。
  由于网的尾部 $\{P_F x : F \supseteq \{i\}\}$ 完全包含在闭集 $C_i$ 内，且 $P_F x \to x^*$（强收敛），根据闭集的序列/网闭性，必有：
  $$x^* \in C_i.$$
  由于 $i \in I$ 的任意性，推得：
  $$x^* \in \bigcap_{i \in I} C_i = C.$$

- **最优性（$x^*$ 达到最小距离）**：
  对任意固定的 $z \in C$，由于对所有有限集 $F$ 都有 $C \subseteq C_F$，故 $z \in C_F$。由有限投影 $P_F x$ 的极小性定义：
  $$\|x - P_F x\| \le \|x - z\| \quad (\forall F \in \mathcal{F}(I)).$$
  由范数的连续性，对上式两端沿网取极限，得到：
  $$\|x - x^*\| = \lim_{F \in \mathcal{F}(I)} \|x - P_F x\| \le \|x - z\| \quad (\forall z \in C).$$

由于 $x^* \in C$ 且满足 $\|x - x^*\| \le \|x - z\|$ 对所有 $z \in C$ 成立，说明 $x^*$ 是 $\|x - z\|$ 在 $C$ 上的最小点。
根据 Hilbert 空间中凸集投影的唯一性，必有：
$$x^* = Px.$$
综上，证明了网 $(P_F x)_{F \in \mathcal{F}(I)}$ 在范数中强收敛到 $Px$：
$$\lim_{F \in \mathcal{F}(I)} P_F x = Px \quad (\text{在 } H \text{ 的范数拓扑下}).$$

---

### 四、 由有限问题的最优值确定全局最优值

记全局最优距离为 $v(I; x) = \operatorname{dist}(x, C) = \|x - Px\|$，有限问题的最优距离为 $v(F; x) = \operatorname{dist}(x, C_F) = \|x - P_F x\|$。

#### 1. 最优值的确界与极限关系
由于 $P_F x \to Px$ 强收敛，根据范数的连续性与三角不等式：
$$\big| \|x - P_F x\| - \|x - Px\| \big| \le \|P_F x - Px\| \to 0.$$
结合第二节中 $d_F(x) = \|x - P_F x\|$ 的单调不减性，我们得到完全的恢复公式：
$$\operatorname{dist}(x, C) = \lim_{F \in \mathcal{F}(I)} \operatorname{dist}(x, C_F) = \sup_{F \in \mathcal{F}(I)} \operatorname{dist}(x, C_F),$$
或以目标值函数（最优距离的平方）形式表示：
$$\|x - Px\|^2 = \lim_{F \in \mathcal{F}(I)} \|x - P_F x\|^2 = \sup_{F \in \mathcal{F}(I)} \|x - P_F x\|^2.$$

#### 2. 精确能量差估计（收敛速率与误差界）
进一步地，由于 $Px \in C \subseteq C_F$，将 $z = Px$ 代入第一节的变分不等式中，立得：
$$\|Px - P_F x\|^2 \le \|x - Px\|^2 - \|x - P_F x\|^2 = \operatorname{dist}^2(x, C) - \operatorname{dist}^2(x, C_F).$$
这表明：**有限子问题的目标值与全局最优目标值的能量间隙，给出了有限近似解 $P_F x$ 逼近真实解 $Px$ 的显式强范数误差上界**。当且仅当目标值收敛时，有限近似解在范数下强收敛。

---

### 五、 证明非扩张性：$\|Px - Py\| \le \|x - y\|$

下面给出两种证明方式：

#### 证法一：由投影算子的坚实非扩张性（Firm Non-expansiveness）直接证明
因为 $Px \in C, Py \in C$，由度量投影的变分特征：
1. 取 $u = Px \in C$，针对测试点 $z = Py \in C$：
   $$\langle x - Px, Py - Px \rangle \le 0 \iff \langle Px - x, Px - Py \rangle \le 0.$$
2. 取 $u = Py \in C$，针对测试点 $z = Px \in C$：
   $$\langle y - Py, Px - Py \rangle \le 0.$$

将两式相加：
$$\langle (Px - Py) - (x - y), Px - Py \rangle \le 0,$$
展开即得**坚实非扩张性**不等式：
$$\|Px - Py\|^2 \le \langle x - y, Px - Py \rangle.$$
根据 Cauchy-Schwarz 不等式：
$$\|Px - Py\|^2 \le \|x - y\| \cdot \|Px - Py\|.$$
- 若 $\|Px - Py\| = 0$，不等式显然成立；
- 若 $\|Px - Py\| > 0$，两边同除以 $\|Px - Py\|$，即证：
$$\|Px - Py\| \le \|x - y\| \quad (\forall x, y \in H).$$

#### 证法二：通过有限维子问题的非扩张性取网极限
对每个有限集 $F \in \mathcal{F}(I)$，$P_F$ 是非空闭凸集 $C_F$ 上的度量投影。
按证法一完全相同的推导，有限问题满足非扩张性：
$$\|P_F x - P_F y\| \le \|x - y\| \quad (\forall x, y \in H).$$
根据第三节的证明，$P_F x \to Px$ 且 $P_F y \to Py$（强收敛）。
由于范数 $\|\cdot\|$ 在 $H$ 上是连续映射，在上述不等式两端沿有向网取极限 $F \in \mathcal{F}(I)$：
$$\|Px - Py\| = \lim_{F \in \mathcal{F}(I)} \|P_F x - P_F y\| \le \|x - y\|.$$
这同样严格导出了 $P$ 的非扩张性。

---

### 六、 总结

1. **构造**：通过闭球上的弱紧性与有限交性质确立了 $C = \bigcap_{i\in I} C_i$ 的非空闭凸性，由此构造出唯一的全局度量投影算子 $P: H \to C$。
2. **强收敛性**：利用有限投影的勾股递减估计 $\|P_{F_2} x - P_{F_1} x\|^2 \le d_{F_2}^2(x) - d_{F_1}^2(x)$，证明了 $(P_F x)_F$ 是 Hilbert 空间中的柯西网，其强极限点必满足全可行性与最优性，因而在范数下收敛到 $Px$。
3. **最优值恢复**：全局最优值完全由有限子问题的最优值确定，满足 $\operatorname{dist}(x, C) = \sup_{F} \operatorname{dist}(x, C_F)$，且伴随误差估计 $\|Px - P_F x\|^2 \le \operatorname{dist}^2(x, C) - \operatorname{dist}^2(x, C_F)$。
4. **非扩张性**：投影的变分不等式保证了 $P$ 满足坚实非扩张性，进而满足 $\|Px - Py\| \le \|x - y\|$。
