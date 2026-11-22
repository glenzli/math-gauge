# 线性关系、坐标纤维与无限赋值

---

## S1 有限系统的坐标纤维

### 1. 解集与非空纤维的仿射维数

在有限维向量空间 $k^I$ 上，赋予标准非退化双线性配对 $\langle u, v \rangle = u \cdot v = \sum_{i\in I} u_i v_i$。在此配对下，空间维数为 $\dim k^I = |I|$。

- **解集 $\mathcal{S}$ 的仿射维数：**
  齐次线性方程组的解空间为
  $$\mathcal{S}_0 = \{x \in k^I : a_j \cdot x = 0, \forall j \in J\} = W^\perp.$$
  由配对的非退化性，$\dim W^\perp = |I| - \dim W$。因原方程组相容，$\mathcal{S} \neq \emptyset$，故 $\mathcal{S}$ 为平行于 $W^\perp$ 的仿射子空间，其仿射维数为：
  $$\dim \mathcal{S} = |I| - \dim W.$$

- **任意坐标限制非空纤维的仿射维数：**
  设 $y \in \pi_A(\mathcal{S})$，纤维为 $\mathcal{F}_y = \{x \in \mathcal{S} : x|_A = y\}$。其齐次化方向子空间为：
  $$V_0 = \{x \in k^I : x \in W^\perp \text{ 且 } x|_A = 0\}.$$
  注意到 $x|_A = 0 \iff x \cdot e_i = 0\ (\forall i \in A) \iff x \in U_A^\perp$。因此，
  $$V_0 = W^\perp \cap U_A^\perp = (W + U_A)^\perp.$$
  从而非空纤维的仿射维数为：
  $$\dim \mathcal{F}_y = \dim (W + U_A)^\perp = |I| - \dim(W + U_A).$$
  *(注：亦可写作 $|I| - |A| - \dim W + \dim(W \cap U_A)$)*。

---

### 2. 给定坐标 $y \in k^A$ 可延拓的充要条件与证明

**充要条件：**
给定 $y \in k^A$，存在 $x \in \mathcal{S}$ 使得 $x|_A = y$ 的充要条件是：
对任意向量 $w \in W \cap U_A$，若将其表示为 $w = \sum_{j\in J} c_j a_j$，则必须满足
$$\sum_{i\in A} w_i y_i = \sum_{j\in J} c_j b_j.$$
*(由于原系统相容，右端数值仅依赖于 $w$ 本身，记为 $\beta(w)$，与系数 $c_j$ 的具体选取无关；等价地，取任意特解 $x_0 \in \mathcal{S}$，有 $\beta(w) = w \cdot x_0$)*。

**证明：**

- **必要性 ($\implies$)：**
  若存在 $x \in \mathcal{S}$ 使得 $x|_A = y$。对于任意 $w \in W \cap U_A$，因 $\operatorname{supp}(w) \subseteq A$，有
  $$\sum_{i\in A} w_i y_i = \sum_{i\in I} w_i x_i = w \cdot x = \left(\sum_{j\in J} c_j a_j\right) \cdot x = \sum_{j\in J} c_j (a_j \cdot x) = \sum_{j\in J} c_j b_j.$$

- **充分性 ($\impliedby$)：**
  取定原系统的一个特解 $x_0 \in \mathcal{S}$。则任意 $x \in \mathcal{S}$ 均可写为 $x = x_0 + v$，其中 $v \in W^\perp$。
  条件 $x|_A = y$ 等价于 $v|_A = y - x_0|_A$。
  设线性映射 $T: W^\perp \to k^A$ 为坐标限制映射 $T(v) = v|_A$。延拓的存在性等价于
  $$z := y - x_0|_A \in \operatorname{Im}(T).$$
  在标准配对下，映射 $T$ 的伴随算子 $T^*: k^A \to (W^\perp)^* \cong k^I / W$ 为 $T^*(u) = \iota_A(u) + W$，其中 $\iota_A(u) = \sum_{i\in A} u_i e_i \in U_A$。
  因此，
  $$\ker(T^*) = \{u \in k^A : \iota_A(u) \in W\} \cong W \cap U_A.$$
  由有限维空间对偶定理（Fredholm 择一性），$\operatorname{Im}(T) = (\ker T^*)^\perp$。
  故 $z \in \operatorname{Im}(T)$ 当且仅当对所有 $u \in \ker T^*$ 均有 $z \cdot u = 0$。
  令 $w = \iota_A(u) \in W \cap U_A$，则 $w_i = u_i$ ($i \in A$) 且
  $$z \cdot u = \sum_{i\in A} (y_i - (x_0)_i) u_i = \sum_{i\in A} w_i y_i - w \cdot x_0 = \sum_{i\in A} w_i y_i - \sum_{j\in J} c_j b_j.$$
  因此 $z \cdot u = 0 \iff \sum_{i\in A} w_i y_i = \sum_{j\in J} c_j b_j$。充分性得证。 $\blacksquare$

---

## S2 有限域下的精确计数

设 $|k| = q$。利用 S1 中的仿射维数结果，各计数公式如下（仅含 $|I|, |A|, \dim W, \dim(W+U_A)$）：

1. **解数：**
   解集 $\mathcal{S}$ 是维数为 $|I| - \dim W$ 的仿射空间，故
   $$|\mathcal{S}| = q^{|I| - \dim W}.$$

2. **每个可实现坐标的完成数（非空纤维大小）：**
   每个可实现的 $y \in \pi_A(\mathcal{S})$ 的纤维均为维数 $|I| - \dim(W+U_A)$ 的仿射空间，故完成数为
   $$|\mathcal{F}_y| = q^{|I| - \dim(W + U_A)}.$$

3. **可实现的 $A$ 坐标数：**
   由于限制映射 $\pi_A|_\mathcal{S}$ 在每个纤维上的原像数恒等于 $q^{|I| - \dim(W+U_A)}$，可实现的坐标数为
   $$|\pi_A(\mathcal{S})| = \frac{|\mathcal{S}|}{|\mathcal{F}_y|} = \frac{q^{|I| - \dim W}}{q^{|I| - \dim(W + U_A)}} = q^{\dim(W + U_A) - \dim W}.$$

---

## S3 有限域的无限坐标拓扑

设 $k$ 有限离散，$I, J$ 任意，每行 $a_j$ 有限支撑且有限子系统相容。在 $k^I$ 上赋予乘积拓扑。

### 1. 全解集非空、紧且全不连通的证明

- **紧性与 Hausdorff 性：**
  $k$ 有限离散，因而 $k$ 是紧 Hausdorff 空间。由 **Tychonoff 定理**，乘积空间 $k^I$ 紧且 Hausdorff。
- **闭性与非空性：**
  对每个 $j \in J$，映射 $f_j: k^I \to k$ 给定为 $f_j(x) = \sum_{i\in I} a_j(i) x_i$。因为 $a_j$ 有限支撑，该和式只包含有限项，即 $f_j$ 为有限个坐标投影的线性组合。由于投影映射与 $k$ 上的有限线性运算均连续，故 $f_j$ 是连续映射。
  因 $k$ 离散，单点集 $\{b_j\}$ 是闭集。所以单方程解集 $\mathcal{S}_j = f_j^{-1}(\{b_j\})$ 为 $k^I$ 中的闭集。
  对于任意有限子集 $F \subseteq J$，由题设有限子系统可解，有 $\bigcap_{j\in F} \mathcal{S}_j \neq \emptyset$。
  闭集族 $\{\mathcal{S}_j\}_{j\in J}$ 满足有限交性质（FIP）。根据 $k^I$ 的紧性，
  $$\mathcal{S} = \bigcap_{j\in J} \mathcal{S}_j \neq \emptyset.$$
  作为紧空间的闭子集，$\mathcal{S}$ 是**紧集**。
- **全不连通性：**
  离散空间 $k$ 是全不连通的。全不连通空间的任意乘积空间仍是全不连通的，其任意子空间亦继承全不连通性。因此 $\mathcal{S}$ **全不连通**。

---

### 2. 坐标像 $\pi_A(\mathcal{S})$ 为闭集的证明

- 坐标限制映射 $\pi_A: k^I \to k^A$ 由积拓扑的泛性质可知是连续映射。
- $\mathcal{S}$ 在 $k^I$ 中紧，故其连续像 $\pi_A(\mathcal{S})$ 在 $k^A$ 中**紧**。
- 空间 $k^A$ 作为 Hausdorff 空间 $k$ 的乘积，是 **Hausdorff 空间**。
- Hausdorff 空间中的紧子集必为闭集，因此 $\pi_A(\mathcal{S})$ 在 $k^A$ 中**闭**。

---

### 3. 元素的有限可实现性刻画与证明

**刻画命题：**
$y \in \pi_A(\mathcal{S})$ 当且仅当：对任意有限子集 $F \subseteq J$ 及任意有限子集 $B \subseteq A$，均存在 $x \in k^I$ 满足
$$\sum_{i\in I} a_j(i) x_i = b_j\quad (\forall j \in F) \qquad\text{且}\qquad x_i = y_i\quad (\forall i \in B).$$

**证明：**
- **必要性 ($\implies$)：**
  若 $y \in \pi_A(\mathcal{S})$，则存在 $x \in \mathcal{S}$ 使得 $x|_A = y$。该 $x$ 自然满足全系统，故对任意有限行集 $F \subseteq J$ 及任意有限子集 $B \subseteq A \subseteq I$，均有 $f_j(x) = b_j\ (j\in F)$ 且 $x|_B = y|_B$。
- **充分性 ($\impliedby$)：**
  对每个 $i \in A$，令闭圆柱集 $K_i = \{x \in k^I : x_i = y_i\} = \pi_i^{-1}(\{y_i\})$，它是 $k^I$ 的闭子集。
  题设条件即：对于指标集 $J$ 的任意有限子集 $F$ 和 $A$ 的任意有限子集 $B$，闭集交集
  $$\left(\bigcap_{j\in F} \mathcal{S}_j\right) \cap \left(\bigcap_{i\in B} K_i\right) \neq \emptyset.$$
  因此，闭集族 $\mathcal{F} = \{\mathcal{S}_j\}_{j\in J} \cup \{K_i\}_{i\in A}$ 满足有限交性质。
  根据 $k^I$ 的紧性，全交非空：
  $$\left(\bigcap_{j\in J} \mathcal{S}_j\right) \cap \left(\bigcap_{i\in A} K_i\right) \neq \emptyset.$$
  取属于该全交的点 $x$，则 $x \in \mathcal{S}$ 且对所有 $i \in A$ 均有 $x_i = y_i$（即 $x|_A = y$）。故 $y \in \pi_A(\mathcal{S})$。 $\blacksquare$

---

## S4 整体对象与全部恢复目标

**判定：目标成立。**

在 ZFC 公理系统下，对任意域 $k$ 与任意集合 $I, J$，全系统的整体解必存在，且其解集、投影像与纤维完全由线性代数对偶数据确定。

### 1. 代数框架与整体解的构造

记 $V = k^{(I)}$ 为 $I$ 上有限支撑函数构成的 $k$-向量空间，具有标准基 $\{e_i\}_{i\in I}$。全赋值空间 $k^I$ 自然同构于代数对偶空间 $V^* = \operatorname{Hom}_k(k^{(I)}, k)$：
$$x \in k^I \longleftrightarrow \varphi_x \in V^*,\quad \varphi_x(v) = \sum_{i\in I} v_i x_i\quad (\text{对 } v \in k^{(I)} \text{ 恒为有限和}).$$
定义子空间 $W = \operatorname{span}_k\{a_j : j \in J\} \subseteq k^{(I)}$。

- **泛函 $\beta$ 的相容性定义：**
  若有有限线性关系 $\sum_{j\in F} c_j a_j = 0$（$F \subseteq J$ 有限），由题设该有限子系统存在整体解 $x^{(F)} \in k^I$，两端与 $x^{(F)}$ 配对得到：
  $$\sum_{j\in F} c_j b_j = \sum_{j\in F} c_j \langle a_j, x^{(F)} \rangle = \left\langle \sum_{j\in F} c_j a_j, x^{(F)} \right\rangle = \langle 0, x^{(F)} \rangle = 0.$$
  故映射 $\beta: W \to k$
  $$\beta\left(\sum_{j\in F} c_j a_j\right) = \sum_{j\in F} c_j b_j$$
  是良定义的线性泛函（$\beta \in W^*$）。
- **整体解的构造（Zorn 引理 / 选择公理）：**
  在 ZFC 中，选取 $W$ 的一组 $k$-基 $\mathcal{B}_W$。由 Zorn 引理，将其扩充为 $V = k^{(I)}$ 的基 $\mathcal{B}_V$。
  定义线性泛函 $\tilde{\beta}: k^{(I)} \to k$ 为：
  $$\tilde{\beta}(v) = \beta(v)\quad (\forall v \in \mathcal{B}_W), \qquad \tilde{\beta}(v) = 0\quad (\forall v \in \mathcal{B}_V \setminus \mathcal{B}_W).$$
  令 $x^* \in k^I$ 为 $x^*_i = \tilde{\beta}(e_i)\ (i \in I)$。则对任意 $j \in J$：
  $$\sum_{i\in I} a_j(i) x^*_i = \tilde{\beta}(a_j) = \beta(a_j) = b_j.$$
  因此 $x^* \in \mathcal{S}$，证明了 $\mathcal{S} \neq \emptyset$。

---

### 2. 解集 $\mathcal{S}$ 的代数数据描述

定义 $W$ 在 $k^I$ 中的零化子（annihilator）：
$$W^\circ = \{x \in k^I : \forall w \in W, \langle w, x \rangle = 0\}.$$
则全解集完全由代数数据 $(W \subseteq k^{(I)}, \beta \in W^*)$ 刻画为仿射空间：
$$\mathcal{S} = x^* + W^\circ = \{x \in k^I : \forall w \in W, \langle w, x \rangle = \beta(w)\}.$$

---

### 3. 任意 $\pi_A$ 的像的完整描述

对任意子集 $A \subseteq I$，定义坐标子空间 $U_A = k^{(A)} = \operatorname{span}_k\{e_i : i \in A\} \subseteq k^{(I)}$。

**定理：**
$$\pi_A(\mathcal{S}) = \left\{y \in k^A : \forall w \in W \cap U_A,\ \sum_{i\in A} w_i y_i = \beta(w)\right\}.$$

**论证：**
- **包含关系 ($\subseteq$)：** 若 $y = x|_A$ 且 $x \in \mathcal{S}$，则对任意 $w \in W \cap U_A$，因 $\operatorname{supp}(w) \subseteq A$，有 $\sum_{i\in A} w_i y_i = \langle w, x \rangle = \beta(w)$。
- **反向包含 ($\supseteq$)：** 任取满足该条件的 $y \in k^A$。定义 $U_A$ 上的线性泛函 $\gamma_y: U_A \to k$ 为 $\gamma_y(u) = \sum_{i\in A} u_i y_i$。
  条件表明对所有 $w \in W \cap U_A$，$\gamma_y(w) = \beta(w)$，即两泛函在子空间交集 $W \cap U_A$ 上严格一致。
  在子空间和 $W + U_A \subseteq k^{(I)}$ 上定义泛函：
  $$\psi(w + u) = \beta(w) + \gamma_y(u)\qquad (w \in W, u \in U_A).$$
  若 $w + u = w' + u'$，则 $w - w' = u' - u \in W \cap U_A$，由一致性知 $\beta(w - w') = \gamma_y(u' - u)$，故 $\psi$ 良定且为线性泛函。
  由选择公理，将 $\psi$ 延拓为全空间 $k^{(I)}$ 上的线性泛函 $\Phi$。
  令 $x_i = \Phi(e_i)\ (i \in I)$。则：
  1. 对 $w \in W$，$\langle w, x \rangle = \Phi(w) = \psi(w) = \beta(w)$，即 $x \in \mathcal{S}$；
  2. 对 $i \in A$，$e_i \in U_A$，故 $x_i = \Phi(e_i) = \psi(e_i) = \gamma_y(e_i) = y_i$，即 $x|_A = y$。
  因此 $y \in \pi_A(\mathcal{S})$。

---

### 4. 非空纤维的完整描述

对任意 $y \in \pi_A(\mathcal{S})$，任取原像 $x \in \pi_A^{-1}(y) \cap \mathcal{S}$，其纤维为平行于 $(W + U_A)^\circ$ 的仿射空间：
$$\pi_A^{-1}(y) \cap \mathcal{S} = x + (W + U_A)^\circ,$$
其中方向空间为
$$(W + U_A)^\circ = W^\circ \cap U_A^\circ = \{v \in k^I : v|_A = 0 \text{ 且 } \forall w \in W, \langle w, v \rangle = 0\}.$$

---

### 5. 限制映射 $\pi_A|_\mathcal{S}$ 的分类理论

通过代数对偶，$\pi_A|_\mathcal{S}$ 的几何性质完全由子空间对 $(W, U_A)$ 在 $k^{(I)}$ 中的相对位置分类：

| 映射性质 | 几何/代数充要条件 | 对应代数/系统意义 |
| :--- | :--- | :--- |
| **单射**（唯一恢复） | $W + U_A = k^{(I)}$ | $(W+U_A)^\circ=\{0\}$，任意外部坐标 $i \notin A$ 的基向量可模 $U_A$ 归入 $W$，即外部坐标被 $A$ 完全决定 |
| **满射**（完全无约束） | $W \cap U_A = \{0\}$ | 方程系中不存在支撑全在 $A$ 内的非平凡线性组合，坐标 $y \in k^A$ 可完全自由选取 |
| **双射**（仿射同构） | $W \oplus U_A = k^{(I)}$ | $A$ 构成解集流形 $\mathcal{S}$ 的一组自由且完备的坐标系 |

---

## S5 赋值空间的支持

**判定：全系统不一定在 $k^{(\mathbb{N})}$ 中有解（结论不成立）。**

### 满足全部前提的反例

设 $k$ 为任意域，$I = J = \mathbb{N} = \{1, 2, 3, \dots\}$。构造如下方程组：

- 第 1 行：$x_1 = 1$（即 $a_1 = e_1, b_1 = 1$）；
- 第 $j$ 行（$j \ge 2$）：$x_{j-1} - x_j = 0$（即 $a_j = e_{j-1} - e_j, b_j = 0$）。

#### 验证前提：
1. **有限支撑行：** $\operatorname{supp}(a_1) = \{1\}$，对 $j \ge 2$，$\operatorname{supp}(a_j) = \{j-1, j\}$，每行均为有限支撑。
2. **每个有限子系统在 $k^{(\mathbb{N})}$ 中可解：**
   设 $F \subseteq \mathbb{N}$ 为任意非空有限子集，记 $M = \max(F)$。定义赋值向量 $x \in k^\mathbb{N}$：
   $$x_i = \begin{cases} 1, & 1 \le i \le M, \\ 0, & i > M. \end{cases}$$
   显然 $\operatorname{supp}(x) = \{1, \dots, M\}$ 是有限集，故 $x \in k^{(\mathbb{N})}$。
   检验方程：
   - 若 $1 \in F$，则 $x_1 = 1 = b_1$；
   - 对任意 $j \in F$ 且 $j \ge 2$，因为 $j \le M$，所以 $j-1 \le M-1 < M$，故 $x_{j-1} = 1$ 且 $x_j = 1$。
     从而 $x_{j-1} - x_j = 1 - 1 = 0 = b_j$。
   因此，有限子系统 $F$ 在 $k^{(\mathbb{N})}$ 中有解。

#### 验证全系统在 $k^{(\mathbb{N})}$ 中无解：
若全系统在 $k^\mathbb{N}$ 中有解 $x$，则：
- 由第 1 行，$x_1 = 1$；
- 对所有 $j \ge 2$，由 $x_{j-1} - x_j = 0$ 得 $x_j = x_{j-1}$。
通过数学归纳法，对所有 $n \in \mathbb{N}$ 均有 $x_n = 1$。
因此全系统在全赋值空间 $k^\mathbb{N}$ 中的唯一解是全 1 序列：
$$x = (1, 1, 1, \dots).$$
该解的支撑集 $\operatorname{supp}(x) = \mathbb{N}$ 是无限集，故 $x \notin k^{(\mathbb{N})}$。全系统在 $k^{(\mathbb{N})}$ 中无解。 $\blacksquare$

---

## S6 无限域的坐标像

**判定：每个 $\pi_A(\mathcal{S})$ 在 $k^A$ 的乘积拓扑中仍然是闭集，即使 $k$ 为无限域（结论成立）。**

### 1. 只涉及有限坐标的闭方程描述

在 S4 中已证明，对任意域 $k$ 与任意子集 $A \subseteq I$，坐标像严格由如下方程族确定：
$$\pi_A(\mathcal{S}) = \left\{y \in k^A : \sum_{i\in \operatorname{supp}(w)} w_i y_i = \beta(w)\quad (\forall w \in W \cap U_A)\right\}.$$
若选取 $W \cap U_A$ 的一组代数基 $\{w_\lambda\}_{\lambda \in \Lambda}$，则 $\pi_A(\mathcal{S})$ 可等价地描述为互不冗余的闭方程组：
$$\sum_{i\in \operatorname{supp}(w_\lambda)} w_\lambda(i) y_i = \beta(w_\lambda)\qquad (\forall \lambda \in \Lambda).$$
注意到因 $W \subseteq k^{(I)}$，对每个 $w \in W \cap U_A$，其支撑集 $\operatorname{supp}(w) \subseteq A$ **必为有限集**。因此上述每个方程均**仅涉及有限个坐标**。

---

### 2. 拓扑闭性的完整证明

设域 $k$ 带有离散拓扑，$k^A = \prod_{i\in A} k$ 带有乘积拓扑。

1. **单个方程解集的闭性（柱状集）：**
   任取 $w \in W \cap U_A$，记其有限支撑集为 $F_w = \operatorname{supp}(w) \subseteq A$。
   考虑规范有限投影映射
   $$p_{F_w}: k^A \to k^{F_w},\quad y \mapsto y|_{F_w}.$$
   由乘积拓扑定义，$p_{F_w}$ 是连续映射。
   因为 $F_w$ 是有限集，有限乘积空间 $k^{F_w} = \prod_{i\in F_w} k$ 具有有限离散空间的乘积拓扑，因而 $k^{F_w}$ **自身就是离散空间**。
   定义求和线性映射
   $$L_w: k^{F_w} \to k,\quad z \mapsto \sum_{i\in F_w} w_i z_i.$$
   离散空间到离散空间的任何映射均连续，故 $L_w$ 连续。
   复合映射
   $$g_w = L_w \circ p_{F_w}: k^A \to k,\quad y \mapsto \sum_{i\in A} w_i y_i$$
   为连续映射。
2. **闭集交集：**
   因为 $k$ 为离散拓扑空间，单点集 $\{\beta(w)\}$ 在 $k$ 中既开又闭，故其原像
   $$C_w = g_w^{-1}(\{\beta(w)\}) = \left\{y \in k^A : \sum_{i\in \operatorname{supp}(w)} w_i y_i = \beta(w)\right\}$$
   是 $k^A$ 中的闭集（亦为开集，即 Clopen 柱状集）。
3. **整体像的闭性：**
   由 S4 的代数充要条件，
   $$\pi_A(\mathcal{S}) = \bigcap_{w \in W \cap U_A} C_w.$$
   在任意拓扑空间中，**任意多个闭集的交集恒为闭集**。
   因此，无论 $k$ 是有限域还是无限域，$\pi_A(\mathcal{S})$ 在 $k^A$ 的乘积拓扑中必为闭集。 $\blacksquare$
