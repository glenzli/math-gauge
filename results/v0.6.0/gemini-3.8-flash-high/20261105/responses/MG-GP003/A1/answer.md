# 半局部邻域、下降与层化的依赖比较

---

## S1 层的半局部拼接

### 1. 命题陈述与符号约定
设 $X$ 为光滑拟射影 $k$-概形，$\Sigma = \{x_1, \dots, x_n\} \subset |X|$ 是有限非空点集。由于 $X$ 拟射影，$\Sigma$ 包含于某个仿射开子概形 $\operatorname{Spec} A \subset X$。记点 $x_i$ 对应的素理想为 $\mathfrak{p}_i = \mathfrak{p}_{x_i}$，乘法闭子集 $M = A \setminus \bigcup_{i=1}^n \mathfrak{p}_i$。半局部概形为
$$S = \operatorname{Spec}(M^{-1}A) = \operatorname{Spec}\mathcal{O}_{X, \Sigma}.$$
其闭点恰为 $x_1, \dots, x_n$。局部化记为 $S_i = \operatorname{Spec}\mathcal{O}_{X, x_i} = \operatorname{Spec}(A_{\mathfrak{p}_i})$。

对原光滑概形 $X$ 上的 Zariski 阿贝尔群层 $G$，按滤过余极限延拓截面：
$$G(S) = \varinjlim_{\Sigma \subset U \subset X\,\text{开}} G(U), \qquad G(S_i) = \varinjlim_{x_i \in U_i \subset X\,\text{开}} G(U_i),$$
$$G(S_i \times_S S_j) = \varinjlim_{x_i \in U_i,\, x_j \in U_j} G(U_i \cap U_j).$$

### 2. 证明：$G(S)$ 是等化子
记指标集族：
$$\mathcal{I} = \prod_{i=1}^n \mathcal{I}_{x_i} = \left\{(U_1, \dots, U_n) \;\middle|\; U_i \subset X \text{ 开且 } x_i \in U_i\right\},$$
偏序定义为反向包含（即 $(U_1', \dots, U_n') \ge (U_1, \dots, U_n) \iff \forall i,\, U_i' \subset U_i$）。这是一个有向集（filtered category）。

对任一元组 $\mathbf{U} = (U_1, \dots, U_n) \in \mathcal{I}$，令 $U = \bigcup_{i=1}^n U_i$。显然 $\Sigma \subset U$，且 $\{U_i\}_{i=1}^n$ 构成开子集 $U$ 的一个 Zariski 开覆盖。由于 $G$ 是 Zariski 拓扑下的阿贝尔群层，满足层公理，由此得到等化子正合列：
$$0 \longrightarrow G(U) \longrightarrow \prod_{i=1}^n G(U_i) \xrightarrow[\operatorname{pr}_2^*]{\operatorname{pr}_1^*} \prod_{i,j=1}^n G(U_i \cap U_j),$$
即 $G(U) \cong \operatorname{eq}\left(\prod_{i=1}^n G(U_i) \rightrightarrows \prod_{i,j=1}^n G(U_i \cap U_j)\right)$。

现对有向集 $\mathcal{I}$ 取滤过余极限：
1. **左侧项的余极限**：映射 $\mathbf{U} = (U_1, \dots, U_n) \mapsto \bigcup_{i=1}^n U_i$ 在 $\Sigma$ 的全体开邻域所成有向集中是**余终的（cofinal）**：对任一包含 $\Sigma$ 的开集 $W$，只需取 $U_i = W$（对所有 $i=1,\dots,n$），即有 $\bigcup_{i=1}^n U_i = W \subset W$。因此，
   $$\varinjlim_{\mathbf{U} \in \mathcal{I}} G\left(\bigcup_{i=1}^n U_i\right) \cong \varinjlim_{\Sigma \subset U} G(U) = G(S).$$
2. **中间项的余极限**：有限积与滤过余极限可交换，且在分量 $i$ 上只需变动 $U_i$（其余分量取常开集即可），故
   $$\varinjlim_{\mathbf{U} \in \mathcal{I}} \prod_{i=1}^n G(U_i) \cong \prod_{i=1}^n \varinjlim_{x_i \in U_i} G(U_i) = \prod_{i=1}^n G(S_i).$$
3. **右侧项的余极限**：概形范畴中的纤维积在仿射极限下对应张量积，
   $$S_i \times_S S_j = \operatorname{Spec}(\mathcal{O}_{X, x_i} \otimes_{\mathcal{O}_{X, \Sigma}} \mathcal{O}_{X, x_j}) = \varprojlim_{x_i \in U_i, \, x_j \in U_j} (U_i \cap U_j).$$
   类似地，有限积与滤过余极限交换，得
   $$\varinjlim_{\mathbf{U} \in \mathcal{I}} \prod_{i,j=1}^n G(U_i \cap U_j) \cong \prod_{i,j=1}^n \varinjlim_{x_i \in U_i, \, x_j \in U_j} G(U_i \cap U_j) = \prod_{i,j=1}^n G(S_i \times_S S_j).$$
4. **正合性保持**：阿贝尔群范畴 $\mathrm{Ab}$ 中的滤过余极限是正合函子，与有限极限（特别是等化子和有限积）严格交换。

对上述层等化子正合列取 $\varinjlim_{\mathbf{U} \in \mathcal{I}}$，立即得到正合列：
$$0 \longrightarrow G(S) \longrightarrow \prod_{i=1}^n G(S_i) \xrightarrow[\operatorname{pr}_2^*]{\operatorname{pr}_1^*} \prod_{i,j=1}^n G(S_i \times_S S_j).$$
即 $G(S)$ 是该对箭头的等化子。

### 3. 说明：$S_i$ 不必是 $S$ 的开子概形
态射 $S_i = \operatorname{Spec}\mathcal{O}_{X, x_i} \to S = \operatorname{Spec}\mathcal{O}_{X, \Sigma}$ 诱导自环局部化 $M^{-1}A \to A_{\mathfrak{p}_i}$。
- **拓扑层面**：$S_i$ 在 $S$ 中的拓扑像由所有包含于 $\mathfrak{p}_i$ 的素理想构成（即 $x_i$ 的全部泛化点集合 $\{\mathfrak{q} \in \operatorname{Spec}(M^{-1}A) \mid \mathfrak{q} \subset \mathfrak{p}_i\}$）。当相对维数 $\dim\mathcal{O}_{X, x_i} \ge 1$ 且 $n \ge 2$ 时，任一包含闭点 $x_i$ 的基础开集 $D(f) \subset S$ 必满足 $f \notin \mathfrak{p}_i$。若 $\dim \mathcal{O}_{X, x_j} \ge 2$（$j \neq i$），$\mathfrak{p}_j$ 中存在无穷多个高度 1 素理想，非零元 $f$ 仅包含于其中有限多个；因而必存在高度 1 素理想 $\mathfrak{q} \subset \mathfrak{p}_j$ 使得 $f \notin \mathfrak{q}$ 且 $\mathfrak{q} \not\subset \mathfrak{p}_i$。此时 $\mathfrak{q} \in D(f)$ 但 $\mathfrak{q} \notin S_i$。因此 $x_i$ 不是 $S_i$ 的拓扑内点，$S_i$ 在 $S$ 中不是开子集。
- **概形层面**：开浸入必须是局部有限型的。然而当 $\dim \mathcal{O}_{X, x_i} \ge 1$ 时，局部环 $\mathcal{O}_{X, x_i}$ 作为 $\mathcal{O}_{X, \Sigma}$-代数不是有限生成的，故态射 $S_i \to S$ 虽然是平坦单射（flat monomorphism），但不是有限型的，因而不是开子概形。

---

## S2 分离预层的比较图

### 1. 两点情形的差映射等化子展开
在 $n = 2$ 情形，$\Sigma = \{x_1, x_2\}$。由 S1，对层 $G$：
- 目标项为 $\prod_{i, j \in \{1, 2\}} G(S_i \times_S S_j) = G(S_1) \oplus G(S_1 \times_S S_2) \oplus G(S_2 \times_S S_1) \oplus G(S_2)$。
- 在对角线分量 $(1, 1)$ 与 $(2, 2)$ 上，两个投影态射 $\operatorname{pr}_1, \operatorname{pr}_2$ 均恒等，诱导的差为零。
- 在非对角线分量 $(1, 2)$ 与 $(2, 1)$ 上，$S_1 \times_S S_2 \cong S_2 \times_S S_1$。
因此，等化子条件严格等价于核正合列：
$$0 \longrightarrow G(S) \xrightarrow{\alpha_G} G(S_1) \oplus G(S_2) \xrightarrow{\delta_G} G(S_1 \times_S S_2),$$
其中 $\delta_G(g_1, g_2) = g_1|_{S_1 \times_S S_2} - g_2|_{S_1 \times_S S_2}$。

### 2. 预层 $H$ 的 Mayer-Vietoris 滤过极限
设 $(U_0, V)$ 为分开 $x_1, x_2$ 的二开覆盖（$x_1 \in U_0, x_2 \in V$ 且覆盖 $S$）。依题设，$(U_0, V)$ 可缩为 $(U, V)$ 仍覆盖 $S$，使得
$$0 \longrightarrow H(S) \longrightarrow H(U) \oplus H(V) \longrightarrow H(U \cap V)$$
正合。在所有使该序列正合的可缩覆盖 $(U, V)$ 构成的有向系统上取滤过余极限：
- 随着 $U$ 收缩到 $x_1$，$V$ 收缩到 $x_2$，有 $\varinjlim H(U) = H(S_1)$，$\varinjlim H(V) = H(S_2)$；
- 它们的交集收缩到公共泛化，即 $\varinjlim H(U \cap V) = H(S_1 \times_S S_2)$；
- 第一项为常值或全覆盖余极限 $H(S)$。
由于滤过余极限保持正合序列，余极限复形正合：
$$0 \longrightarrow H(S) \xrightarrow{\alpha_H} H(S_1) \oplus H(S_2) \xrightarrow{\delta_H} H(S_1 \times_S S_2).$$

### 3. 比较交换图与同构证明
层化态射 $\eta: H \to G$ 诱导两正合列间的交换图：
$$\begin{array}{ccccccccc}
0 & \longrightarrow & H(S) & \xrightarrow{\alpha_H} & H(S_1) \oplus H(S_2) & \xrightarrow{\delta_H} & H(S_1 \times_S S_2) \\
& & \Big\downarrow \eta_S & & \Big\downarrow \eta_{S_1} \oplus \eta_{S_2} & & \Big\downarrow \eta_{S_1 \times_S S_2} \\
0 & \longrightarrow & G(S) & \xrightarrow{\alpha_G} & G(S_1) \oplus G(S_2) & \xrightarrow{\delta_G} & G(S_1 \times_S S_2)
\end{array}$$

根据题目假设：
1. **中坚直箭头 $\eta_{S_1} \oplus \eta_{S_2}$**：由 $H(S_i) \to G(S_i)$（$i=1,2$）是同构，故其中坚直映射为**同构**。
2. **右坚直箭头 $\eta_{S_1 \times_S S_2}$**：$T = S_1 \times_S S_2$ 为所用邻域局部化，题设 $H(T) \to G(T)$ 单射，故右坚直映射为**单射**。
3. **单射性**：题设已给定 $H(S) \to G(S)$ 单射；亦可由图追逐导出：$\alpha_H$ 单射且中坚直箭头同构，故 $\eta_S$ 必为单射。
4. **满射性（图追逐）**：
   任取 $g \in G(S)$。考虑其在底行的像 $\alpha_G(g) \in G(S_1) \oplus G(S_2)$，由底行正合，$\delta_G(\alpha_G(g)) = 0$。
   因中坚直箭头是满射，存在唯一 $(h_1, h_2) \in H(S_1) \oplus H(S_2)$ 满足
   $$(\eta_{S_1} \oplus \eta_{S_2})(h_1, h_2) = \alpha_G(g).$$
   考察 $\delta_H(h_1, h_2) \in H(S_1 \times_S S_2)$，由右侧方块交换性：
   $$\eta_{S_1 \times_S S_2}\big(\delta_H(h_1, h_2)\big) = \delta_G\big((\eta_{S_1} \oplus \eta_{S_2})(h_1, h_2)\big) = \delta_G(\alpha_G(g)) = 0.$$
   由于右坚直映射 $\eta_{S_1 \times_S S_2}$ 是**单射**，必有
   $$\delta_H(h_1, h_2) = 0.$$
   由顶行在中间项的正合性，存在 $h \in H(S)$ 使得 $\alpha_H(h) = (h_1, h_2)$。
   再由左侧方块交换性：
   $$\alpha_G(\eta_S(h)) = (\eta_{S_1} \oplus \eta_{S_2})(\alpha_H(h)) = (\eta_{S_1} \oplus \eta_{S_2})(h_1, h_2) = \alpha_G(g).$$
   因底行 $\alpha_G$ 是单射，故
   $$\eta_S(h) = g.$$
   这证明了 $\eta_S$ 是满射。

综上，$\eta_S: H(S) \to G(S)$ 是同构。

---

## S3 含指定点的开集

### 1. 余终性证明
设 $X$ 为任意拓扑空间，$\Sigma \subset X$ 为有限非空集，$W \subset X$ 为包含 $\Sigma$ 的开集。
令
$$\mathcal{I} = \{V \subset X \mid V \text{ 为开集且 } \Sigma \subset V\},$$
偏序定义为反向包含（即 $V_1 \le V_2 \iff V_2 \subset V_1$）。这是一个有向偏序集。
令
$$\mathcal{I}_W = \{U \subset W \mid U \text{ 为开集且 } \Sigma \subset U\},$$
视作 $\mathcal{I}$ 的全子偏序集（包含函子记为 $\iota: \mathcal{I}_W \hookrightarrow \mathcal{I}$）。

欲证 $\mathcal{I}_W$ 在 $\mathcal{I}$ 中余终（cofinal / final）：
1. **支配性**：对任意 $V \in \mathcal{I}$，取 $U = V \cap W$。
   - 因为 $V$ 开且 $W$ 开，故 $U$ 是 $X$ 的开集；
   - 因为 $\Sigma \subset V$ 且 $\Sigma \subset W$，故 $\Sigma \subset V \cap W = U$；
   - 因为 $U \subset W$，故 $U \in \mathcal{I}_W$；
   - 同时 $U = V \cap W \subset V$，在有向集偏序中即 $V \le U$。
2. **相容性**：若 $U_1, U_2 \in \mathcal{I}_W$ 且 $V \le U_1, U_2$（即 $U_1 \subset V, U_2 \subset V$），则取 $U_3 = U_1 \cap U_2 \in \mathcal{I}_W$，满足 $U_1 \le U_3$ 且 $U_2 \le U_3$。

因此，$\mathcal{I}_W$ 在 $\mathcal{I}$ 中余终。

### 2. 预层余极限的典范同构
设 $\mathcal{F}$ 为 $X$ 上的任意反变阿贝尔群预层。
包含函子 $\iota: \mathcal{I}_W \to \mathcal{I}$ 诱导余极限间的典范同态：
$$\phi: \varinjlim_{U \in \mathcal{I}_W} \mathcal{F}(U) \longrightarrow \varinjlim_{V \in \mathcal{I}} \mathcal{F}(V), \qquad [s]_U \longmapsto [s]_U.$$
反之，构造态射：对任意 $V \in \mathcal{I}$，限制映射 $\mathcal{F}(V) \to \mathcal{F}(V \cap W)$ 与典范映射 $\mathcal{F}(V \cap W) \to \varinjlim_{U \in \mathcal{I}_W} \mathcal{F}(U)$ 复合，得到族
$$\psi_V: \mathcal{F}(V) \longrightarrow \varinjlim_{U \in \mathcal{I}_W} \mathcal{F}(U).$$
当 $V_2 \subset V_1$ 时，由预层限制映射的传递性知族 $\{\psi_V\}_{V \in \mathcal{I}}$ 与转移映射相容。由滤过余极限的泛性质，存在唯一的群同态：
$$\psi: \varinjlim_{V \in \mathcal{I}} \mathcal{F}(V) \longrightarrow \varinjlim_{U \in \mathcal{I}_W} \mathcal{F}(U).$$
易验：
- 对任意 $U \in \mathcal{I}_W$，$U \cap W = U$，故 $\psi \circ \phi = \mathrm{id}_{\varinjlim_{U \in \mathcal{I}_W} \mathcal{F}(U)}$；
- 对任意 $V \in \mathcal{I}$，$V \cap W \subset V$ 在有向系统中给出等价类，故 $\phi \circ \psi = \mathrm{id}_{\varinjlim_{V \in \mathcal{I}} \mathcal{F}(V)}$。
因此，$\phi$ 是两邻域余极限之间的**典范同构**。

---

## S4 稠密开与邻域系统

### 1. 判定结论
**结论：不成立（否定）。**
包含 $\Sigma$ 且包含于 $W$ 的开集族**不一定**在全部 $\Sigma$ 开邻域中余终。

### 2. 反例与充分论证
满足题设全部前提的反例构造如下：
- **基域**：取任意域 $k$。
- **概形**：取 $X = \mathbb{A}^1_k = \operatorname{Spec} k[t]$。$X$ 是光滑、积分、仿射 $k$-概形。
- **有限非空点集**：取 $\Sigma = \{0\}$，即原点（对应极大理想 $(t)$）。
- **稠密开子集**：取 $W = X \setminus \{0\} = D(t) = \operatorname{Spec} k[t, t^{-1}]$。
  因为 $X$ 是整概形且 $W$ 非空，故 $W$ 是 $X$ 的稠密开子集。满足前提要求。

**检验余终性**：
考察集合族 $\mathcal{I}_W = \{U \subset X \mid U \text{ 为开集},\, \Sigma \subset U \subset W\}$。
- 若存在 $U \in \mathcal{I}_W$，则必须满足 $\Sigma \subset U$，即 $0 \in U$；
- 但同时必须满足 $U \subset W = X \setminus \{0\}$，即 $0 \notin U$。
两者矛盾！因此，
$$\mathcal{I}_W = \emptyset.$$
然而，$\Sigma = \{0\}$ 在 $X$ 中的全部开邻域构成的族 $\mathcal{I} = \{V \subset X \text{ 开} \mid 0 \in V\}$ 是非空的（例如包含 $X$ 本身及所有 $D(f)$ 其中 $f(0) \neq 0$）。

空集在非空有向集（无论考虑对象支配性还是范畴余终性）中**绝不余终**。
（注：若在此类空族上取形式余极限，将退化为始对象 0，而截面余极限为局部环 $\mathcal{O}_{X, 0} = k[t]_{(t)} \neq 0$）。

**适用条件说明**：
包含 $\Sigma$ 且包含于 $W$ 的开集在全部 $\Sigma$ 开邻域中余终的**充要条件**是 $\Sigma \subset W$（即 S3 所设条件）。当且仅当存在 $x \in \Sigma$ 满足 $x \notin W$ 时，该开集族为空，余终性必然失效。

---

## S5 整体对象与全部恢复目标

### 1. 判定结论
**结论：目标在给定条件下成立。**
典范同态 $\eta_S: F(S) \to F_{\mathrm{Zar}}(S)$ 是同构。

---

### 2. 构造、分类与基础定理

#### (1) 带转移预层的图态射与限制
范畴 $\mathrm{Cor}_k$ 中态射是有限对应。存在典范图嵌入函子 $\mathrm{Sm}/k \to \mathrm{Cor}_k$：对态射 $f: Y \to Z$，对应图子概形 $\Gamma_f \subset Y \times Z$。因此反变函子 $F: \mathrm{Cor}_k^{\mathrm{op}} \to \mathrm{Ab}$ 限制在概形态射上即为通常的 Zariski 预层，对开浸入 $j: U \hookrightarrow Y$，限制映射即 $F(j) = j^*: F(Y) \to F(U)$。

#### (2) 同伦不变性（$\mathbb{A}^1$-homotopy invariance）
假设对所有 $Y \in \mathrm{Sm}/k$，投影诱导同构 $F(Y) \xrightarrow{\sim} F(Y \times \mathbb{A}^1)$。由此，若两个有限对应 $\alpha, \beta \in \mathrm{Cor}_k(Y, Z)$ 是 $\mathbb{A}^1$-同伦的（即存在 $H \in \mathrm{Cor}_k(Y \times \mathbb{A}^1, Z)$ 分别限制在 $0, 1$ 截面上为 $\alpha, \beta$），则在群同态上必有 $F(\alpha) = F(\beta)$。

#### (3) Voevodsky 层化定理（Voevodsky's Sheafification Theorem）
依据 Voevodsky 经典定理（*Cohomological Theory of Presheaves with Transfers*, Theorem 3.1.11 及 Mazza-Voevodsky-Weibel *Lectures on Motivic Cohomology*, Theorem 4.18/5.7）：
- Zariski 层化 $F_{\mathrm{Zar}}$ 具有唯一的带转移预层结构，使 $\eta: F \to F_{\mathrm{Zar}}$ 是带转移预层的态射；
- $F_{\mathrm{Zar}}$ 保持同伦不变性；
- $F_{\mathrm{Zar}}$ 自动是 Nisnevich 拓扑下的层，且两者的层上同调群对任意光滑概形一致。

---

### 3. 性质证明一：$F$ 的分离性与 $\eta_S$ 的单射性

#### 定理（稠密开浸入单射性）
设 $Y \in \mathrm{Sm}/k$ 是连通光滑整概形，$W \subset Y$ 是稠密开子集。则限制映射
$$F(Y) \longrightarrow F(W)$$
是单射。

**证明论证**：
设余维数 $\ge 1$ 的闭集为 $Z = Y \setminus W$。依 Artin 初等纤维化定理（Elementary Fibration Theorem），在 $Y$ 的局部存在标准三元组（standard triple）$(p: C \to B, Z \subset C \subset \bar{C})$，其中 $\bar{C} \to B$ 是相对光滑射影曲线，$Z$ 有限满射于仿射底 $B$。
利用仿射直线上有限对应的高斯除法与移动引理，在曲线纤维上可在代数闭链群中构造有理同伦：恒等对应 $\mathrm{id}_C$ 在模去由有限转移生成的边界后同伦于一个支撑避开 $Z$ 的闭链 $\Phi \in \mathrm{Cor}_k(C, W)$。
由此同伦性知：若截面 $s \in F(Y)$ 在 $W$ 上的限制为 0，则由传递转移构造可知 $s = \Phi^*(s|_W) = 0$。因此 $F(Y) \to F(W)$ 单射。

#### 单射性推论
1. **$F$ 是 Zariski 分离预层**：若开覆盖 $(U_\alpha)$ 上 $s|_{U_\alpha} = 0$，则 $s$ 在稠密集 $\bigcup U_\alpha$ 上处处为 0，由上述单射性知 $s = 0$。
2. **局部化单射性**：由于 $F \to F_{\mathrm{Zar}}$ 在截面上滤过由局部重合定义，分离预层到其层化的典范态射 $F(U) \to F_{\mathrm{Zar}}(U)$ 对任一开子集 $U$ 均是单射。
3. 对任意半局部化 $S$（及其任何局部化和纤维积 $T$），由滤过余极限保持单射性知：
   $$\eta_S: F(S) \longrightarrow F_{\mathrm{Zar}}(S) \quad \text{与} \quad \eta_T: F(T) \longrightarrow F_{\mathrm{Zar}}(T) \quad \text{均是单射}。$$
这完全确认了 S2 所需的单射性条件。

---

### 4. 性质证明二：单点基期 ($|\Sigma| = 1$)
设 $\Sigma = \{x\}$，则 $S = S_x = \operatorname{Spec}\mathcal{O}_{X, x}$。
按定义：
$$F(S_x) = \varinjlim_{x \in U} F(U) = F_x \quad (\text{预层 } F \text{ 在 } x \text{ 处的茎}),$$
$$F_{\mathrm{Zar}}(S_x) = \varinjlim_{x \in U} F_{\mathrm{Zar}}(U) = (F_{\mathrm{Zar}})_x \quad (\text{层化 } F_{\mathrm{Zar}} \text{ 在 } x \text{ 处的茎}).$$
依据拓扑空间上预层层化的根本泛性质：**预层的层化诱导所有点处的茎同构**，即
$$\eta_x: F_x \stackrel{\sim}{\longrightarrow} (F_{\mathrm{Zar}})_x.$$
因此当 $|\Sigma| = 1$ 时，$\eta_{S_x}: F(S_x) \xrightarrow{\sim} F_{\mathrm{Zar}}(S_x)$ 是**自然的同构**。

---

### 5. 性质证明三：Mayer-Vietoris 邻域收缩与归纳步

设 $|\Sigma| = n \ge 2$。
由 S3，半局部邻域计算完全可在包含 $\Sigma$ 的仿射开子概形 $\operatorname{Spec} A$ 中进行。

1. **两开覆盖的收缩引理（MVW Lemma 4.22 / 5.7）**：
   对任何将 $\Sigma$ 分开为 $\Sigma_1$ 与 $\Sigma_2$ 的开邻域 $U_0 \supset \Sigma_1$ 与 $V \supset \Sigma_2$，利用曲线纤维化中有限对应对切触截面的移动技术，存在可缩开邻域 $U \subset U_0$（仍包含 $\Sigma_1$），使得差截面可经同伦由交集推回两翼，从而保证 Mayer-Vietoris 序列：
   $$0 \longrightarrow F(S) \longrightarrow F(U) \oplus F(V) \longrightarrow F(U \cap V)$$
   在有向滤过收缩下严格正合。
2. **两点情形同构（应用 S2）**：
   在 $n = 2$ 情形：
   - 援引 S1，层 $F_{\mathrm{Zar}}$ 满足核正合列 $0 \to F_{\mathrm{Zar}}(S) \to F_{\mathrm{Zar}}(S_1) \oplus F_{\mathrm{Zar}}(S_2) \to F_{\mathrm{Zar}}(S_1 \times_S S_2)$；
   - 援引前述分离性，$\eta_T$ 对所有所用局部化均单射；
   - 援引单点基期，$\eta_{S_1}$ 与 $\eta_{S_2}$ 为同构；
   - 援引收缩引理，顶行 $0 \to F(S) \to F(S_1) \oplus F(S_2) \to F(S_1 \times_S S_2)$ 正合；
   - 严格适用 S2，四引理图追逐立即给出 $\eta_S: F(S) \xrightarrow{\sim} F_{\mathrm{Zar}}(S)$ 是同构。
3. **点数 $n$ 的有限归纳**：
   设结论对闭点数 $< n$ 的所有半局部化成立。将 $\Sigma$ 划分为 $\Sigma' = \{x_1, \dots, x_{n-1}\}$ 与 $\{x_n\}$，记 $S'$ 为 $\Sigma'$ 处的半局部化。
   由归纳假设，$F(S') \cong F_{\mathrm{Zar}}(S')$ 且 $F(S_n) \cong F_{\mathrm{Zar}}(S_n)$。
   将 $S$ 视作由 $S'$ 与 $S_n$ 拼接，构造比较梯形图：
   $$\begin{array}{ccccccccc}
   0 & \longrightarrow & F(S) & \longrightarrow & F(S') \oplus F(S_n) & \longrightarrow & F(S' \times_S S_n) \\
   & & \Big\downarrow \eta_S & & \Big\downarrow \eta_{S'} \oplus \eta_{S_n} & & \Big\downarrow \eta_{S' \times_S S_n} \\
   0 & \longrightarrow & F_{\mathrm{Zar}}(S) & \longrightarrow & F_{\mathrm{Zar}}(S') \oplus F_{\mathrm{Zar}}(S_n) & \longrightarrow & F_{\mathrm{Zar}}(S' \times_S S_n)
   \end{array}$$
   - 中坚直映射为同构（由归纳假设）；
   - 右坚直映射为单射（由分离性）；
   - 两行均正合（顶行由同伦转移 MV 给出，底行由层的拼接 S1 给出）。
   由四引理（S2 证明完全相同的图追逐），$\eta_S: F(S) \to F_{\mathrm{Zar}}(S)$ 必为同构。

综上所述，对任意有限非空点集 $\Sigma$ 处的半局部化 $S$，典范同态 $\eta_S: F(S) \to F_{\mathrm{Zar}}(S)$ 是同构。

---

## S6 极限正合与阶段正合

### 1. 第一问：余极限正合判定
**判定结论：不成立（否定）。**
余极限复形正合**不能**蕴含所有充分后阶段正合。

#### 反例与充分证明
设滤过指标集为非负整数 $(\mathbb{N}, \le)$。
构造阿贝尔群二项复形滤过系统 $(C_\bullet^{(i)}, d_i)_{i \in \mathbb{N}}$ 如下：
- **各阶段复形**：对每个 $i \in \mathbb{N}$，令
  $$C_1^{(i)} = \mathbb{Z}, \qquad C_0^{(i)} = \mathbb{Z},$$
  微分算子 $d_i: C_1^{(i)} \to C_0^{(i)}$ 为乘以 2，即 $d_i(x) = 2x$。
  各阶段复形同调群为：
  $$H_1(C_\bullet^{(i)}) = \ker(d_i) = 0,$$
  $$H_0(C_\bullet^{(i)}) = \operatorname{coker}(d_i) = \mathbb{Z} / 2\mathbb{Z} \neq 0.$$
  因此，对**任意** $i \in \mathbb{N}$，$C_\bullet^{(i)}$ 均**不正合**（在第 0 项同调非零）。
- **链映射过渡态射**：
  对每个 $i \in \mathbb{N}$，链映射 $\phi_i = (\alpha_i, \beta_i): C_\bullet^{(i)} \to C_\bullet^{(i+1)}$ 定义为：
  $$\alpha_i: C_1^{(i)} \to C_1^{(i+1)}, \quad \alpha_i(x) = 2x,$$
  $$\beta_i: C_0^{(i)} \to C_0^{(i+1)}, \quad \beta_i(y) = 2y.$$
  检验链映射交换性：
  $$d_{i+1}(\alpha_i(x)) = 2 \cdot (2x) = 4x = 2 \cdot (2x) = \beta_i(d_i(x)).$$
  图表严格交换，构成良定的链复形滤过系统。
- **余极限复形**：
  在系统下，过渡映射为不断乘以 2，因此
  $$\varinjlim_{i \in \mathbb{N}} C_1^{(i)} = \varinjlim (\mathbb{Z} \xrightarrow{\times 2} \mathbb{Z} \xrightarrow{\times 2} \cdots) \cong \mathbb{Z}\left[\frac{1}{2}\right],$$
  $$\varinjlim_{i \in \mathbb{N}} C_0^{(i)} = \varinjlim (\mathbb{Z} \xrightarrow{\times 2} \mathbb{Z} \xrightarrow{\times 2} \cdots) \cong \mathbb{Z}\left[\frac{1}{2}\right].$$
  余极限微分算子
  $$d_\infty = \varinjlim d_i: \mathbb{Z}\left[\frac{1}{2}\right] \longrightarrow \mathbb{Z}\left[\frac{1}{2}\right]$$
  即为乘以 2。
  因为 2 在环 $\mathbb{Z}[1/2]$ 中可逆，乘 2 是**群同构**！
  因此：
  $$\ker(d_\infty) = 0 \implies H_1(C_\bullet) = 0,$$
  $$\operatorname{coker}(d_\infty) = 0 \implies H_0(C_\bullet) = 0.$$
  余极限复形 $C_\bullet$ **严格正合**。

然而，对任意阶段 $i \in \mathbb{N}$，阶段复形同调均为 $\mathbb{Z}/2\mathbb{Z} \neq 0$。不存在任何 $i_0$ 使得当 $i \ge i_0$ 时阶段复形正合。

---

### 2. 第二问：同调类消亡蕴含余极限正合的证明

设 $(C_\bullet^{(i)}, \phi_{ij})_{i \in I}$ 是有向集 $I$ 上的阿贝尔群链复形滤过系统，其余极限复形记为 $C_\bullet = \varinjlim_{i \in I} C_\bullet^{(i)}$。

#### 证明途径（包含函子同构与直接元素追逐双重视角）：

**方法一：利用同调函子与滤过余极限的交换性**
1. 在阿贝尔群范畴 $\mathrm{Ab}$ 中，滤过余极限是正合函子，因而与有限极限及有限余极限可交换。
   由于链复形的同调定义为
   $$H_n(C_\bullet) = \operatorname{coker}\big(\operatorname{im}(d_{n+1}) \hookrightarrow \ker(d_n)\big),$$
   它完全由有限极限（核）和有限余极限（像、余核）有限步复合而成。因此，同调函子与滤过余极限自然交换：
   $$H_n(C_\bullet) = H_n\left(\varinjlim_{i \in I} C_\bullet^{(i)}\right) \cong \varinjlim_{i \in I} H_n(C_\bullet^{(i)}).$$
2. 任取余极限同调群中的元素 $\xi \in \varinjlim_{i \in I} H_n(C_\bullet^{(i)})$。
   由滤过余极限的定义，存在某个阶段 $i \in I$ 及同调类 $c \in H_n(C_\bullet^{(i)})$，使得 $\xi$ 由 $c$ 代表，即 $\xi = \iota_i(c)$（其中 $\iota_i: H_n(C_\bullet^{(i)}) \to \varinjlim H_n(C_\bullet^{(k)})$ 为规范投射）。
3. 根据题设条件：“每个阶段的每个同调类都在某个后阶段变为零”，对于该同调类 $c \in H_n(C_\bullet^{(i)})$，必然存在 $j \ge i$ 使得
   $$H_n(\phi_{ij})(c) = 0 \in H_n(C_\bullet^{(j)}).$$
4. 于是，在余极限中：
   $$\xi = \iota_i(c) = \iota_j\big(H_n(\phi_{ij})(c)\big) = \iota_j(0) = 0.$$
   由于 $\xi$ 是任意选取的，故
   $$\varinjlim_{i \in I} H_n(C_\bullet^{(i)}) = 0.$$
   结合第 1 步的同构，得 $H_n(C_\bullet) \cong 0$。即余极限复形在每一项均正合。

**方法二：元素追逐（直接验证 $\ker(d_n) = \operatorname{im}(d_{n+1})$）**
1. 设 $z \in \ker(d_n^\infty) \subset C_n$。
2. 由 $C_n = \varinjlim C_n^{(i)}$，存在 $i_1 \in I$ 和 $z_{i_1} \in C_n^{(i_1)}$ 代表 $z$。
3. 其微分 $d_n^\infty(z) = 0 \in C_{n-1}$，由于 $C_{n-1}$ 是滤过余极限，存在 $i_2 \ge i_1$ 使得在阶段 $i_2$ 上，
   $$d_n^{(i_2)}\big(\phi_{i_1 i_2}(z_{i_1})\big) = 0.$$
   记 $z' = \phi_{i_1 i_2}(z_{i_1}) \in C_n^{(i_2)}$，则 $z' \in \ker(d_n^{(i_2)})$ 是阶段 $i_2$ 的循环元，定义了同调类 $[z'] \in H_n(C_\bullet^{(i_2)})$。
4. 依题设，存在 $j \ge i_2$ 使得 $\phi_{i_2 j}$ 将同调类 $[z']$ 映为 0。
   这意味着元 $z'' = \phi_{i_2 j}(z') \in C_n^{(j)}$ 是一个**边界元**：
   存在 $w_j \in C_{n+1}^{(j)}$ 满足
   $$d_{n+1}^{(j)}(w_j) = z''.$$
5. 将 $w_j$ 映至余极限 $C_{n+1}$，记其像为 $w \in C_{n+1}$。由链映射微分与余极限相容性：
   $$d_{n+1}^\infty(w) = [d_{n+1}^{(j)}(w_j)] = [z''] = z.$$
   这证明了 $z \in \operatorname{im}(d_{n+1}^\infty)$。
6. 因此 $\ker(d_n^\infty) \subset \operatorname{im}(d_{n+1}^\infty)$，结合复形公理 $\operatorname{im} \subset \ker$，恒有 $\ker(d_n^\infty) = \operatorname{im}(d_{n+1}^\infty)$。

余极限复形严格正合。证毕。
