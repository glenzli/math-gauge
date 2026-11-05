# 线性关系、坐标纤维与无限赋值

---

## S1 有限系统的坐标纤维

### 1. 设定与代数结构
设 $k$ 为任意域，$I, J$ 为有限集合。记 $n = |I|$。将 $k^I$ 视为以标准基 $\{e_i\}_{i \in I}$ 构成的 $n$ 维 $k$-向量空间，其标准双线性配对为：
$$\langle a, x \rangle = \sum_{i \in I} a(i) x_i \qquad (a, x \in k^I).$$
由题设，$W = \mathrm{span}_k\{a_j : j \in J\} \subseteq k^I$，对子集 $A \subseteq I$，$U_A = \mathrm{span}_k\{e_i : i \in A\} \subseteq k^I$。原方程组写为：
$$\langle a_j, x \rangle = b_j \qquad (\forall j \in J).$$
由于方程相容，存在特解 $x^* \in k^I$ 满足 $\langle a_j, x^* \rangle = b_j$（$\forall j \in J$）。全解集为：
$$\mathcal S = \{x \in k^I : \langle a_j, x \rangle = b_j, \forall j \in J\}.$$

因为系统相容，由线性代数基本事实，映射 $a_j \mapsto b_j$ 可唯一线性延拓为 $W$ 上的线性泛函 $b: W \to k$：即对任意有限线性组合 $w = \sum_{j \in J} c_j a_j \in W$，定义
$$b(w) = \sum_{j \in J} c_j b_j = \langle w, x^* \rangle.$$
若 $\sum_{j \in J} c_j a_j = 0$，则对特解 $x^*$ 做内积即得 $\sum c_j b_j = \langle 0, x^* \rangle = 0$，故 $b \in W^*$ 良定。

### 2. 解集 $\mathcal S$ 的仿射维数
解集 $\mathcal S$ 是以 $x^*$ 为基点的仿射子空间，其方向子空间为齐次化解集：
$$\mathcal S_0 = \{x \in k^I : \langle a_j, x \rangle = 0, \forall j \in J\} = W^\perp.$$
由于标准配对非退化，由正交补维数公式：
$$\dim \mathcal S = \dim W^\perp = |I| - \dim W.$$

### 3. 非空坐标纤维的仿射维数
设 $\pi_A: k^I \to k^A$ 为坐标限制映射 $x \mapsto x|_A$。对给定的 $y \in k^A$，其在 $\mathcal S$ 中的纤维为：
$$\mathcal S_y = \pi_A^{-1}(y) \cap \mathcal S = \{x \in \mathcal S : x|_A = y\}.$$
若 $\mathcal S_y \neq \emptyset$，任取一纤维特解 $x_0 \in \mathcal S_y$。则 $\mathcal S_y$ 是仿射空间 $x_0 + (\mathcal S_y)_0$，其方向空间为：
$$(\mathcal S_y)_0 = \{v \in k^I : v \in W^\perp \text{ 且 } v|_A = 0\}.$$
注意 $v|_A = 0 \iff \langle e_i, v \rangle = 0 \;(\forall i \in A) \iff v \in U_A^\perp$。因此：
$$(\mathcal S_y)_0 = W^\perp \cap U_A^\perp = (W + U_A)^\perp.$$
利用正交补维数定理，非空纤维的仿射维数为：
$$\dim \mathcal S_y = \dim (W + U_A)^\perp = |I| - \dim(W + U_A).$$

### 4. 任意给定坐标 $y \in k^A$ 可延拓的充要条件与证明

**结论（充要条件）：**
给定坐标 $y \in k^A$ 可延拓到解集 $\mathcal S$（即 $y \in \pi_A(\mathcal S)$）的充要条件是：
对所有 $w \in W \cap U_A$，满足
$$\sum_{i \in A} w(i) y_i = b(w) \quad \left(\text{等价地，}\; \langle w|_A, y \rangle_A = \langle w|_A, x^*|_A \rangle_A\right).$$

**证明：**
- **必要性**：
  若 $y$ 可延拓，则存在 $x \in \mathcal S$ 使得 $x|_A = y$。
  对任意 $w \in W \cap U_A$，由于 $w \in U_A$，有 $\mathrm{supp}(w) \subseteq A$，即当 $i \notin A$ 时 $w(i) = 0$。于是：
  $$\langle w, x \rangle = \sum_{i \in I} w(i) x_i = \sum_{i \in A} w(i) x_i = \sum_{i \in A} w(i) y_i.$$
  另一方面，由于 $w \in W$，依 $b$ 的定义及 $x \in \mathcal S$，有 $\langle w, x \rangle = b(w)$。
  故 $\sum_{i \in A} w(i) y_i = b(w)$ 必然成立。

- **充分性**：
  设 $y \in k^A$ 满足上述条件。记 $\tilde{y} \in U_A \subseteq k^I$ 为 $y$ 在 $A^c = I \setminus A$ 处补零所得的零延拓向量，即 $\tilde{y}|_A = y$ 且 $\tilde{y}|_{A^c} = 0$。
  我们寻找 $z \in U_A^\perp = U_{A^c}$，使得 $x = \tilde{y} + z \in \mathcal S$。
  由于 $z \in U_{A^c}$，自动有 $z|_A = 0$，从而 $x|_A = \tilde{y}|_A = y$。
  $x \in \mathcal S$ 的要求等价于：对所有 $j \in J$，
  $$\langle a_j, \tilde{y} + z \rangle = b_j \iff \langle a_j, z \rangle = b_j - \langle a_j, \tilde{y} \rangle = b_j - \sum_{i \in A} a_j(i) y_i.$$
  将 $z$ 视为待定向量 $z \in k^{A^c}$，记 $\bar{a}_j = a_j|_{A^c} \in k^{A^c}$。上述方程即为关于未知量 $z \in k^{A^c}$ 的有限线性方程组：
  $$\langle \bar{a}_j, z \rangle_{A^c} = b_j - \sum_{i \in A} a_j(i) y_i \qquad (j \in J).$$
  由有限维线性方程组相容性的 Rouché-Capelli 定理（或对偶性）：该方程组相容当且仅当行向量的任意线性关系在右端项上均成立。
  任取其行向量的一组线性关系：设 $\sum_{j \in J} c_j \bar{a}_j = 0 \in k^{A^c}$。
  令 $w = \sum_{j \in J} c_j a_j \in W$。
  该线性关系意味着 $w|_{A^c} = 0$，即 $\mathrm{supp}(w) \subseteq A$，从而 $w \in U_A$。
  因此 $w \in W \cap U_A$。
  将这一组合作用于右端项：
  $$\sum_{j \in J} c_j \left( b_j - \sum_{i \in A} a_j(i) y_i \right) = \sum_{j \in J} c_j b_j - \sum_{i \in A} \left( \sum_{j \in J} c_j a_j(i) \right) y_i = b(w) - \sum_{i \in A} w(i) y_i.$$
  根据所给充分性前提，对于 $w \in W \cap U_A$，上式恰好等于 $0$。
  因此右端项满足所有齐次对偶关系，该关于 $z$ 的线性系统在 $k^{A^c}$ 中必有解 $z$。
  令 $x = \tilde{y} + z \in k^I$，即有 $x \in \mathcal S$ 且 $x|_A = y$。充分性得证。 $\blacksquare$

---

## S2 有限域下的精确计数

设域 $k = \mathbb F_q$（$q = p^r$）。在 S1 的设定下，由有限维向量空间的结构可直接计数：

### 1. 全解数 $|\mathcal S|$
解集 $\mathcal S$ 是维数为 $|I| - \dim W$ 的仿射子空间。因此：
$$|\mathcal S| = q^{|I| - \dim W}.$$

### 2. 每个可实现坐标的完成数（非空纤维基数）
由 S1，任意非空纤维 $\mathcal S_y$ 是仿射子空间，其维数为 $|I| - \dim(W + U_A)$。因此每个可实现坐标的完成数恒为：
$$|\mathcal S_y| = q^{|I| - \dim(W + U_A)}.$$

### 3. 可实现的 $A$ 坐标数 $|\pi_A(\mathcal S)|$
限制映射 $\pi_A|_\mathcal S: \mathcal S \to \pi_A(\mathcal S)$ 是满射，且每个纤维的基数均严格相等，故由商集分划公式：
$$|\pi_A(\mathcal S)| = \frac{|\mathcal S|}{|\mathcal S_y|} = \frac{q^{|I| - \dim W}}{q^{|I| - \dim(W + U_A)}} = q^{\dim(W + U_A) - \dim W}.$$

> **注（与 S1 条件的印证）**：
> 由格拉斯曼维数公式：
> $$\dim(W \cap U_A) = \dim W + \dim U_A - \dim(W + U_A) = \dim W + |A| - \dim(W + U_A).$$
> 可实现像 $\pi_A(\mathcal S)$ 在 $k^A$ 中由 $\dim(W \cap U_A)$ 个彼此独立的线性约束完全确定，其仿射维数为：
> $$\dim \pi_A(\mathcal S) = |A| - \dim(W \cap U_A) = \dim(W + U_A) - \dim W.$$
> 其元素个数恰为 $q^{\dim(W + U_A) - \dim W}$。以上三式均完全满足仅含 $|I|、|A|、\dim W、\dim(W+U_A)$ 的要求。

---

## S3 有限域的无限坐标拓扑

设 $k$ 为有限离散域，$I, J$ 为任意指标集。每行 $a_j \in k^{(I)}$（有限支撑），赋予 $k^I$ 乘积拓扑（Product Topology）。

### 1. 全解集 $\mathcal S$ 非空、紧且全不连通
1. **拓扑空间性质**：
   - 因为 $k$ 是有限离散空间，它是紧的、Hausdorff 的、且全不连通的。
   - 由 **Tychonoff 乘积定理**，乘积空间 $k^I = \prod_{i \in I} k$ 是紧致 Hausdorff 空间。
   - 乘积空间中每个点的连通分支是各坐标因子的连通分支的乘积；由于 $k$ 离散，各单点集即为其连通分支，故 $k^I$ 的所有连通分支均为单点集，即 $k^I$ 是全不连通空间。
2. **方程解集的开闭性**：
   - 对每个 $j \in J$，支撑集 $F_j = \mathrm{supp}(a_j) \subseteq I$ 为有限集。
   - 计算映射 $f_j: k^I \to k$ 给定为 $x \mapsto \sum_{i \in F_j} a_j(i) x_i$。该映射可分解为规范投影 $p_{F_j}: k^I \to k^{F_j}$ 与有限维映射 $k^{F_j} \to k$ 的复合。
   - 由于乘积拓扑下投影连续，且有限离散空间的映射均连续，故 $f_j$ 是连续映射。
   - 在离散拓扑下，单点集 $\{b_j\} \subseteq k$ 是闭集（事实上是既开既闭集）。
   - 故单个方程的解集 $\mathcal S_j = f_j^{-1}(\{b_j\})$ 是 $k^I$ 中的闭子集。
3. **有限交性质与非空紧性**：
   - 全解集为 $\mathcal S = \bigcap_{j \in J} \mathcal S_j$。
   - 题设假定：对任意有限子集 $F \subseteq J$，有限子系统存在解 $x \in k^I$。这意味着：
     $$\bigcap_{j \in F} \mathcal S_j \neq \emptyset.$$
   - 因此闭集族 $\{\mathcal S_j\}_{j \in J}$ 满足有限交性质（Finite Intersection Property, FIP）。
   - 由 $k^I$ 的紧致性，其全交非空：$\mathcal S = \bigcap_{j \in J} \mathcal S_j \neq \emptyset$。
   - 作为紧致空间的闭子集，$\mathcal S$ 自身是**紧空间**；作为全不连通空间的子空间，$\mathcal S$ 也是**全不连通空间**。

### 2. 坐标像 $\pi_A(\mathcal S)$ 闭性证明
- 规范投影 $\pi_A: k^I \to k^A$（$x \mapsto x|_A$）依乘积拓扑的定义是连续映射。
- 紧空间在连续映射下的像必为紧集，因此 $\pi_A(\mathcal S)$ 是 $k^A$ 中的紧子集。
- 乘积空间 $k^A = \prod_{i \in A} k$ 为 Hausdorff 空间（离散空间的乘积）。
- 由标准拓扑学定理：Hausdorff 空间中的紧子集必为闭集。
- 故 $\pi_A(\mathcal S)$ 在 $k^A$ 中为闭集。

### 3. 元素的有限可实现性刻画
**刻画命题：**
设 $y \in k^A$。则 $y \in \pi_A(\mathcal S)$ 当且仅当：对任意有限子集 $F \subseteq J$ 和任意有限子集 $A_0 \subseteq A$，限制系统
$$\sum_{i \in I} a_j(i) x_i = b_j \quad (j \in F), \qquad x_i = y_i \quad (i \in A_0)$$
在 $k^I$ 中存在解 $x$（即所有有限行与有限 $A$ 坐标限制都同时可实现）。

**证明：**
- **必要性**：
  若 $y \in \pi_A(\mathcal S)$，则存在全局解 $x \in \mathcal S$ 使得 $x|_A = y$。显然该 $x$ 对一切行方程均成立，且对所有 $i \in A_0$ 均有 $x_i = y_i$。
- **充分性**：
  对每个 $i \in A$，定义超平面闭子集 $H_i = \{x \in k^I : x_i = y_i\} = \pi_{\{i\}}^{-1}(\{y_i\})$。
  在 $k^I$ 中考虑如下闭集族：
  $$\mathcal C = \{\mathcal S_j : j \in J\} \cup \{H_i : i \in A\}.$$
  任取 $\mathcal C$ 的有限子族，它必然由有限个行方程指标 $F \subseteq J$ 及有限个坐标限制指标 $A_0 \subseteq A$ 构成：
  $$\left( \bigcap_{j \in F} \mathcal S_j \right) \cap \left( \bigcap_{i \in A_0} H_i \right).$$
  依据充分性假设，存在 $x \in k^I$ 同时满足 $F$ 中的方程并在 $A_0$ 上等于 $y|_{A_0}$，这意味着该有限交非空。
  因此闭集族 $\mathcal C$ 在紧空间 $k^I$ 中满足有限交性质。
  由紧致性，存在
  $$x^* \in \bigcap \mathcal C = \left( \bigcap_{j \in J} \mathcal S_j \right) \cap \left( \bigcap_{i \in A} H_i \right) = \mathcal S \cap \pi_A^{-1}(y).$$
  这说明 $x^* \in \mathcal S$ 且 $x^*|_A = y$，即 $y = \pi_A(x^*) \in \pi_A(\mathcal S)$。 $\blacksquare$

---

## S4 整体对象与全部恢复目标

### 1. 结论判定
**结论：在给定条件下（ZFC 系统下），所述整体实现与坐标恢复目标完全成立。**
对于任意域 $k$、任意基数指标集 $I, J$ 及任意子集 $A \subseteq I$，全系统必有整体解 $\mathcal S \neq \emptyset$，且全解集 $\mathcal S$、坐标像 $\pi_A(\mathcal S)$ 及非空纤维可以仅由线性代数数据完整构造、分类并完全描述。

---

### 2. 基础代数框架与配对
记 $V = k^{(I)}$ 为有限支撑函数空间，其基为标准基 $\{e_i\}_{i \in I}$。
$V$ 的代数对偶空间（Algebraic Dual）为：
$$V^* = (k^{(I)})^* \cong k^I.$$
二者之间的典范非退化双线性配对为：
$$\langle v, x \rangle = \sum_{i \in I} v(i) x_i \qquad (v \in k^{(I)}, x \in k^I).$$
由代数对偶理论，给定 $k^{(I)}$ 上的任意一个线性泛函 $\phi \in (k^{(I)})^*$，令 $x_i = \phi(e_i)$，则 $x = (x_i)_{i \in I} \in k^I$ 唯一对应了 $\phi$。

定义由方程系决定的代数数据：
- 关系子空间：$W = \mathrm{span}_k\{a_j : j \in J\} \subseteq k^{(I)}$。
- 齐次化零化子空间（Annihilator）：
  $$W^\circ = \{x \in k^I : \langle w, x \rangle = 0, \forall w \in W\} = \mathrm{Ann}_{k^I}(W).$$

**引理 4.1（右端项线性泛函的良定性）：**
存在良定的线性泛函 $b: W \to k$，满足 $b(a_j) = b_j$（$\forall j \in J$）。
*证明*：
若 $\sum_{j \in F} c_j a_j = 0$ 是 $\{a_j\}_{j \in J}$ 的任意有限线性关系（$F \subseteq J$ 有限）。
根据有限子系统相容性假设，存在 $x^{(F)} \in k^I$ 满足 $\langle a_j, x^{(F)} \rangle = b_j$（$\forall j \in F$）。
因此：
$$\sum_{j \in F} c_j b_j = \sum_{j \in F} c_j \langle a_j, x^{(F)} \rangle = \left\langle \sum_{j \in F} c_j a_j, x^{(F)} \right\rangle = \langle 0, x^{(F)} \rangle = 0.$$
故线性映射 $b: W \to k$ 良定。 $\blacksquare$

---

### 3. 整体解的构造与 $\mathcal S$ 的完整描述
在 ZFC 公理系统下，由选择公理（Zorn 引理），向量空间的任意子空间存在补空间（即向量空间范畴的 Hahn-Banach 延拓定理）。
取 $W$ 在 $k^{(I)}$ 中的代数补子空间 $M$，使得：
$$k^{(I)} = W \oplus M.$$
将线性泛函 $b: W \to k$ 延拓为整个 $k^{(I)}$ 上的线性泛函 $\tilde{b}: k^{(I)} \to k$：
$$\tilde{b}(w + m) = b(w) \qquad (w \in W, m \in M).$$
定义 $x^* \in k^I$ 为：$x^*_i = \tilde{b}(e_i)$（$i \in I$）。
则对任意 $j \in J$：
$$\sum_{i \in I} a_j(i) x^*_i = \tilde{b}(a_j) = b(a_j) = b_j.$$
因此 $x^* \in \mathcal S \neq \emptyset$，整体解构造完成。

**全解集 $\mathcal S$ 的代数描述：**
$$\mathcal S = x^* + W^\circ.$$
$\mathcal S$ 是以 $x^*$ 为原点的仿射空间，其方向空间为 $W^\circ \cong (k^{(I)} / W)^*$。

---

### 4. 坐标像 $\pi_A(\mathcal S)$ 的构造与完整描述
对于任意子集 $A \subseteq I$：
记 $k^{(A)} \subseteq k^{(I)}$ 为支撑集包含于 $A$ 的有限支撑函数子空间。显然有典范直和分解：
$$k^{(I)} = k^{(A)} \oplus k^{(I \setminus A)}.$$
从给定系统提取 $A$ 上的内在代数数据：
$$W_A = W \cap k^{(A)}.$$
（即系数完全落在 $A$ 内部的所有齐次线性约束组合）。

**定理 4.2（坐标恢复与像集描述定理）：**
坐标限制像 $\pi_A(\mathcal S) \subseteq k^A$ 仅由代数数据 $(W \cap k^{(A)}, b|_{W \cap k^{(A)}})$ 完全确定：
$$\pi_A(\mathcal S) = \left\{ y \in k^A : \sum_{i \in A} w(i) y_i = b(w), \; \forall w \in W \cap k^{(A)} \right\}.$$

**证明：**
- **包含关系 $\subseteq$（必要性）**：
  若 $y \in \pi_A(\mathcal S)$，则存在 $x \in \mathcal S$ 使得 $x|_A = y$。
  对任意 $w \in W \cap k^{(A)}$，由于 $\mathrm{supp}(w) \subseteq A$，在 $A^c$ 上 $w(i) = 0$。
  因此：
  $$b(w) = \langle w, x \rangle = \sum_{i \in I} w(i) x_i = \sum_{i \in A} w(i) y_i.$$
- **包含关系 $\supseteq$（充分性）**：
  设 $y \in k^A$ 满足对所有 $w \in W \cap k^{(A)}$ 均有 $\sum_{i \in A} w(i) y_i = b(w)$。
  由 $y$ 在子空间 $k^{(A)}$ 上诱导线性泛函 $y^*: k^{(A)} \to k$：
  $$y^*(v) = \sum_{i \in A} v(i) y_i \qquad (v \in k^{(A)}).$$
  在子空间交集 $W \cap k^{(A)}$ 上，由充分性前提：
  $$y^*(w) = \sum_{i \in A} w(i) y_i = b(w).$$
  即两线性泛函在交空间上完全吻合：$y^*|_{W \cap k^{(A)}} = b|_{W \cap k^{(A)}}$。
  
  在子空间和 $W + k^{(A)} \subseteq k^{(I)}$ 上定义泛函 $\Phi: W + k^{(A)} \to k$：
  $$\Phi(w + v) = b(w) + y^*(v) \qquad (w \in W, v \in k^{(A)}).$$
  *良定性验证*：若 $w_1 + v_1 = w_2 + v_2$，则 $w_1 - w_2 = v_2 - v_1 \in W \cap k^{(A)}$。
  从而：
  $$b(w_1 - w_2) = y^*(w_1 - w_2) = y^*(v_2 - v_1) \implies b(w_1) + y^*(v_1) = b(w_2) + y^*(v_2).$$
  故 $\Phi$ 是 $W + k^{(A)}$ 上良定的线性泛函。
  
  利用 Zorn 引理，在 $k^{(I)}$ 中选取 $W + k^{(A)}$ 的补子空间 $N$，使得：
  $$k^{(I)} = (W + k^{(A)}) \oplus N.$$
  定义 $\tilde{\Phi} \in (k^{(I)})^*$ 满足 $\tilde{\Phi}|_{W + k^{(A)}} = \Phi$ 且 $\tilde{\Phi}|_N = 0$。
  令 $x \in k^I$ 对应于 $\tilde{\Phi}$，即 $x_i = \tilde{\Phi}(e_i)$。
  1. 对任意 $j \in J$，$a_j \in W \subseteq W + k^{(A)}$，因此：
     $$\langle a_j, x \rangle = \tilde{\Phi}(a_j) = \Phi(a_j) = b(a_j) = b_j \implies x \in \mathcal S.$$
  2. 对任意 $i \in A$，$e_i \in k^{(A)} \subseteq W + k^{(A)}$，因此：
     $$x_i = \tilde{\Phi}(e_i) = \Phi(e_i) = y^*(e_i) = y_i \implies x|_A = y.$$
  因此 $x \in \mathcal S$ 且 $\pi_A(x) = y$，即 $y \in \pi_A(\mathcal S)$。充分性得证。 $\blacksquare$

---

### 5. 非空纤维的完整描述
任取 $y \in \pi_A(\mathcal S)$，取特解 $x^{(y)} \in \mathcal S$ 满足 $x^{(y)}|_A = y$。
纤维 $\mathcal S_y = \{x \in \mathcal S : x|_A = y\}$ 的方向子空间为：
$$\begin{aligned}
(\mathcal S_y)_0 &= \{u \in k^I : u \in W^\circ \text{ 且 } u|_A = 0\} \\
&= W^\circ \cap (k^{(A)})^\circ = (W + k^{(A)})^\circ.
\end{aligned}$$
因此，每个非空纤维均是仿射空间：
$$\mathcal S_y = x^{(y)} + (W + k^{(A)})^\circ.$$
注意到商空间同构：
$$\frac{k^{(I)}}{W + k^{(A)}} \cong \frac{k^{(I \setminus A)}}{\pi_{I \setminus A}(W)},$$
因此纤维的方向向量空间严格代数对偶于补坐标商空间：
$$(W + k^{(A)})^\circ \cong \left( \frac{k^{(I \setminus A)}}{\pi_{I \setminus A}(W)} \right)^*.$$

---

### 6. 恢复与映射性质的代数分类
基于上述构造，给出坐标恢复映射 $\pi_A$ 性质的充要代数分类：
1. **全满射性（任意坐标均可延拓，$\pi_A(\mathcal S) = k^A$）**：
   $$\iff W \cap k^{(A)} = \{0\}.$$
   即方程系在 $A$ 坐标内不包含任何内蕴齐次约束。
2. **单射性（唯一恢复性，非空纤维均为单点）**：
   $$\iff (W + k^{(A)})^\circ = \{0\} \iff W + k^{(A)} = k^{(I)} \iff \pi_{I \setminus A}(W) = k^{(I \setminus A)}.$$
   即方程系沿余维坐标的投影能够张满所有余维有限支撑空间。
3. **双射性（全局一一对应完全恢复）**：
   $$\iff W \cap k^{(A)} = \{0\} \quad \text{且} \quad W + k^{(A)} = k^{(I)} \iff k^{(I)} = W \oplus k^{(A)}.$$
   即 $W$ 恰好为从 $k^{(A)}$ 到 $k^{(I \setminus A)}$（或反之）的线性映射图子空间。

---

## S5 赋值空间的支持

### 1. 结论判定
**结论：不成立。**
即使每个有限子系统都在有限支撑空间 $k^{(\mathbb N)}$ 中有解，全系统**不一定**在 $k^{(\mathbb N)}$ 中有解。

---

### 2. 反例构造与完整证明
设 $k$ 为任意域，$I = J = \mathbb N = \{1, 2, 3, \dots\}$。
定义方程系如下：
$$\begin{aligned}
x_1 &= 1, & (j = 1) \\
x_j - x_{j-1} &= 0, & (j \ge 2)
\end{aligned}$$
即行向量与常数项为：
- $a_1 = e_1$，$b_1 = 1$；
- $a_j = e_j - e_{j-1}$，$b_j = 0$（$\forall j \ge 2$）。

**验证前提条件：**
1. **各行有限支撑**：
   $\mathrm{supp}(a_1) = \{1\}$，对 $j \ge 2$，$\mathrm{supp}(a_j) = \{j-1, j\}$，每行均为有限支撑，满足条件。
2. **每个有限子系统在 $k^{(\mathbb N)}$ 中有解**：
   设 $F \subseteq \mathbb N$ 为任意有限子集。
   - 若 $F = \emptyset$，显然 $x = 0 \in k^{(\mathbb N)}$ 是解。
   - 若 $F \neq \emptyset$，令 $M = \max(F) \in \mathbb N$。
     构造向量 $x^{(F)} \in k^{\mathbb N}$ 如下：
     $$x^{(F)}_i = \begin{cases} 1, & 1 \le i \le M, \\ 0, & i > M. \end{cases}$$
     因为当 $i > M$ 时 $x^{(F)}_i = 0$，故 $\mathrm{supp}(x^{(F)}) \subseteq \{1, \dots, M\}$ 为有限集，确实满足 $x^{(F)} \in k^{(\mathbb N)}$。
     检验 $F$ 中包含的所有方程：
     - 若 $1 \in F$，则 $x^{(F)}_1 = 1 = b_1$；
     - 对任意 $j \in F$ 且 $j \ge 2$，因 $j \le M$，必有 $1 \le j-1 < j \le M$。从而 $x^{(F)}_j = 1$ 且 $x^{(F)}_{j-1} = 1$。
       因此 $x^{(F)}_j - x^{(F)}_{j-1} = 1 - 1 = 0 = b_j$。
     因此 $x^{(F)} \in k^{(\mathbb N)}$ 满足有限子系统 $F$ 中的所有方程。

**全系统在 $k^{(\mathbb N)}$ 中无解的证明：**
假设存在全系统的解 $x \in k^{(\mathbb N)}$。
由方程 $x_1 = 1$ 及 $x_j - x_{j-1} = 0$（$\forall j \ge 2$），利用数学归纳法：
- 基础步：$x_1 = 1 \neq 0$。
- 归纳步：若 $x_{j-1} = 1$，则 $x_j = x_{j-1} = 1$。
因此，对一切正整数 $n \in \mathbb N$，均有 $x_n = 1$。
这意味着：
$$\mathrm{supp}(x) = \{n \in \mathbb N : x_n \neq 0\} = \mathbb N.$$
这是无限集合，与 $x \in k^{(\mathbb N)}$（有限支撑）产生直接矛盾。
故全系统在 $k^{(\mathbb N)}$ 中绝无解。 $\blacksquare$

---

## S6 无限域的坐标像

### 1. 结论判定
**结论：成立。**
即使域 $k$ 是无限域，赋予 $k$ 离散拓扑，赋予 $k^A$ 乘积拓扑，每个坐标像 $\pi_A(\mathcal S)$ 在 $k^A$ 中**仍然是闭集**。

---

### 2. 闭方程描述（只涉及有限坐标）
由 S4 中证明的坐标像定理，对任意子集 $A \subseteq I$，$\pi_A(\mathcal S)$ 恰好等于如下由有限坐标线性方程定义的闭集的交：
$$\pi_A(\mathcal S) = \bigcap_{w \in W \cap k^{(A)}} \left\{ y \in k^A : \sum_{i \in \mathrm{supp}(w)} w(i) y_i = b(w) \right\}.$$

若选取 $W \cap k^{(A)}$ 的一组 $k$-线性基 $\{w_\lambda\}_{\lambda \in \Lambda}$，则 $\pi_A(\mathcal S)$ 具有如下极小无冗余的显式闭方程描述：
$$\pi_A(\mathcal S) = \bigcap_{\lambda \in \Lambda} \left\{ y \in k^A : \sum_{i \in \mathrm{supp}(w_\lambda)} w_\lambda(i) y_i = b(w_\lambda) \right\}.$$
其中每个指标 $\lambda \in \Lambda$ 对应的方程满足：
1. 系数非零坐标集 $\mathrm{supp}(w_\lambda) \subseteq A$ 是**有限集合**；
2. 每一个方程仅涉及有限个坐标分量。

---

### 3. 完整拓扑闭性证明

**步骤 1：单方程水平集的既开既闭性**
任取 $w \in W \cap k^{(A)}$。其支撑集 $F_w = \mathrm{supp}(w) \subseteq A$ 是有限集。
考虑映射：
$$g_w: k^A \to k, \qquad y \mapsto \sum_{i \in F_w} w(i) y_i.$$
该映射可分解为标准坐标投影 $p_{F_w}: k^A \to k^{F_w}$ 与线性映射 $\ell_w: k^{F_w} \to k$ 的复合：
$$g_w = \ell_w \circ p_{F_w}.$$
- 在乘积拓扑定义下，有限坐标投影 $p_{F_w}$ 是连续映射；
- 空间 $k^{F_w}$ 带有乘积拓扑，由于 $F_w$ 有限且 $k$ 离散，$k^{F_w}$ 上的拓扑即为离散拓扑；
- 离散空间到离散空间的任何映射均连续，故 $\ell_w$ 连续；
- 复合映射 $g_w$ 是连续映射。
在离散拓扑下，单点集 $\{b(w)\}$ 在 $k$ 中是闭集。由连续映射的性质，原像
$$E_w = g_w^{-1}(\{b(w)\}) = \left\{ y \in k^A : \sum_{i \in \mathrm{supp}(w)} w(i) y_i = b(w) \right\}$$
是乘积拓扑空间 $k^A$ 中的闭集（且因单点集亦开，它实际上是 clopen 闭开集）。

**步骤 2：任意交的闭性与代数像的闭合**
根据 S4 的像集代数定理：
$$\pi_A(\mathcal S) = \bigcap_{w \in W \cap k^{(A)}} E_w.$$
在任意拓扑空间中，任意族闭集的交集恒为闭集。
由于每个 $E_w$ 是闭集，其任意交 $\pi_A(\mathcal S)$ 必然是 $k^A$ 中的闭集。

**步骤 3：直接拓扑闭包检验（印证其自封闭性）**
设 $y \in \overline{\pi_A(\mathcal S)}$ 为 $\pi_A(\mathcal S)$ 在 $k^A$ 乘积拓扑中的任意闭包点。
对任意 $w \in W \cap k^{(A)}$，令 $F = \mathrm{supp}(w) \subseteq A$ 为有限集。
集合
$$U = \{z \in k^A : z|_F = y|_F\} = p_F^{-1}(\{y|_F\})$$
是 $k^A$ 中包含 $y$ 的开邻域。
由闭包点定义，必有 $U \cap \pi_A(\mathcal S) \neq \emptyset$。
取点 $y' \in U \cap \pi_A(\mathcal S)$，则 $y'|_F = y|_F$。
因为 $y' \in \pi_A(\mathcal S)$，由必要性它满足 $w$ 对应的方程：
$$\sum_{i \in F} w(i) y_i = \sum_{i \in F} w(i) y'_i = b(w).$$
这表明 $y$ 满足对所有 $w \in W \cap k^{(A)}$ 的方程。
由 S4 的充分性判定（通过 ZFC 泛函延拓），$y$ 必然能够延拓为全局解，即 $y \in \pi_A(\mathcal S)$。
故 $\overline{\pi_A(\mathcal S)} = \pi_A(\mathcal S)$，$\pi_A(\mathcal S)$ 在 $k^A$ 中严格闭合。 $\blacksquare$
