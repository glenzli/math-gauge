这是一套结合了**程序形式语义（Denotational Semantics）**、**有向图上的确定性动力系统**以及**向量值度量空间上的广义不动点理论（Perov–Luxemburg 不动点理论）**的闭合理论。

以下系统地建立该相互递归算子系统的闭合理论，给出主定理、整体算子族的显式构造，以及严格完整的数学论证。

---

# 递归算子系统的闭合理论

## 一、 系统架构与符号体系

### 1. 基础空间与度量
- 设 $\mathcal X = \mathcal X^\circ \cup \{\bot\}$，其中 $\bot$ 为发散/停机元，$\mathcal X^\circ \ne \varnothing$ 为有效值空间。
- $d_1, \ldots, d_m$ 为 $\mathcal X$ 上的扩展伪度量，满足：对任意 $x \in \mathcal X^\circ$ 及 $1 \le i \le m$，$d_i(x, \bot) = +\infty$；对 $y, z \in \mathcal X^\circ$，$d_i(y, z) \in [0, +\infty]$。
- 记列向量伪度量 $\mathbf d = (d_1, \ldots, d_m)^{\mathsf T}$。在扩展实数系统 $[0, +\infty]$ 上采用测度论与凸分析标准运算约定：
  $$0 \cdot (+\infty) = (+\infty) \cdot 0 = 0.$$

### 2. 多重图与局域数据
- 给定有限有向多重图 $G = (V, E)$，其中 $V \ne \varnothing$。每条边 $e \in E$ 具有源节点 $s(e) \in V$ 和目标节点 $t(e) \in V$。
- 对每个节点 $v \in V$，其定义域 $U_v \subseteq \mathcal X^\circ$ 具有互不相交的局域划分：
  $$U_v = S_v \sqcup \bigsqcup_{e \in E: s(e)=v} D_e.$$
- **局域数据三元组**：
  1. **停机/基底算子**：$h_v: S_v \to \mathcal X^\circ$；
  2. **输入转移算子**：$b_e: D_e \to U_{t(e)}$；
  3. **返回算子**：$a_e: \mathcal X \to \mathcal X$，满足严格性 $a_e(\bot) = \bot$、有效保集性 $a_e(\mathcal X^\circ) \subseteq \mathcal X^\circ$，以及矩阵 Lipschitz 连续性：
     $$\mathbf d(a_e(y), a_e(z)) \le L_e \mathbf d(y, z) \qquad (\forall y, z \in \mathcal X^\circ),$$
     其中 $L_e \in \mathbb R_{\ge 0}^{m \times m}$ 为有限非负实矩阵。

### 3. 转移矩阵与算子空间
- 构造以节点为块指标的系统转移矩阵 $M \in \mathbb R_{\ge 0}^{(|V|m) \times (|V|m)}$，其 $(v, w)$ 块为：
  $$M_{vw} = \sum_{e \in E: s(e)=v, t(e)=w} L_e, \qquad \rho(M) < 1,$$
  其中 $\rho(M)$ 表示矩阵 $M$ 的谱半径。
- 定义算子族空间为笛卡尔积空间：
  $$\mathcal F = \prod_{v \in V} (\mathcal X^\circ)^{U_v} = \left\{ F = (F_v)_{v \in V} \;\middle|\; F_v: U_v \to \mathcal X^\circ \right\}.$$
- 定义一次展开（Bellman/递归展开）映射 $\mathcal T: \mathcal F \to \mathcal F$：
  $$(\mathcal T F)_v(x) = \begin{cases}
  h_v(x), & x \in S_v, \\
  a_e\bigl(F_{t(e)}(b_e(x))\bigr), & x \in D_e, \; e: v \to t(e).
  \end{cases}$$
  由 $h_v(S_v) \subseteq \mathcal X^\circ$ 和 $a_e(\mathcal X^\circ) \subseteq \mathcal X^\circ$ 知，$\mathcal T(\mathcal F) \subseteq \mathcal F$ 良定。
- 算子族间的距离由向量值上确界规范诱导：
  $$\Delta_{v, i}(F, G) = \sup_{x \in U_v} d_i(F_v(x), G_v(x)) \in [0, +\infty],$$
  记总距离向量为 $\boldsymbol\Delta(F, G) = (\Delta_{v, i}(F, G))_{v \in V, 1 \le i \le m} \in [0, +\infty]^{|V|m}$。

---

## 二、 主定理 (Main Theorem)

> ### 定理 1（递归算子系统的闭合与几何逼近定理）
> 设上述条件成立，且 $(\mathcal X^\circ, \mathbf d)$ 在广义柯西意义下完备（若系统所有执行轨线均有限步终止，则无需完备性假设）。
> 
> 1. **闭合存在性与唯一性 (Existence and Uniqueness of Closure)**：
>    存在唯一的算子族 $F^* = (F^*_v)_{v \in V} \in \mathcal F$（在 $\boldsymbol\Delta$-度量等价意义下唯一），满足递归闭合方程：
>    $$F^* = \mathcal T F^*.$$
> 
> 2. **谱收缩率与加权范数 (Spectral Contraction Rate)**：
>    对任意给定的收缩比 $q \in (\rho(M), 1)$，存在由 Perron–Frobenius 理论构造的正权向量 $u \in \mathbb R_{>0}^{|V|m}$，使得在加权范数 $\|\mathbf y\|_u = \max_{j} \frac{|y_j|}{u_j}$ 下，矩阵算子 $M$ 严格收缩：
>    $$\|M \mathbf y\|_u \le q \|\mathbf y\|_u \qquad (\forall \mathbf y \ge \mathbf 0).$$
> 
> 3. **几何收敛性 (Geometric Convergence)**：
>    对任意初始算子族 $H \in \mathcal F$（满足 $\boldsymbol\Delta(H, F^*)$ 有限），其有限展开序列 $\mathcal T^n H$ 按由 $M$ 决定的几何速度一致逼近闭合算子族 $F^*$：
>    $$\max_{v \in V, 1 \le i \le m} \Delta_{v, i}(\mathcal T^n H, F^*) \le C_H q^n \qquad (\forall n \ge 1),$$
>    其中常数 $C_H < +\infty$ 可显式定量确定为：
>    $$C_H = \frac{\max_j u_j}{\min_j u_j} \max_{v, i} \Delta_{v, i}(H, F^*) \quad \text{或} \quad C_H = \frac{\max_j u_j}{\min_j u_j} \left\|(I - M)^{-1} \boldsymbol\Delta(H, \mathcal T H)\right\|_\infty.$$

---

## 三、 整体算子 $F^*$ 的显式构造

整体算子 $F^*$ 可以从两个等价且互补的视角显式构造：**动力系统轨线（操作语义）构造** 与 **解析级数（不动点迭代）构造**。

### 1. 动力系统轨线构造法（Operational / Path-based Construction）
对任意给定的初始节点 $v \in V$ 和初始输入 $x \in U_v$，系统状态转移由 $b_e$ 完全决定。在不相交并集 $\bigsqcup_{w \in V} U_w$ 上定义离散动力演化轨线：
- 令 $v_0 = v, \; x_0 = x$。
- 对 $k = 0, 1, 2, \ldots$：
  - 若 $x_k \in S_{v_k}$，则动力学在第 $k$ 步**成功终止**。记停机时间 $\tau(v, x) = k$，终止节点 $\nu(v, x) = v_k$，终止状态 $\xi(v, x) = x_k \in S_{v_k}$，遍历边序列为 $p(v, x) = (e_1, e_2, \ldots, e_k)$（当 $k=0$ 时为平凡空路径）。
  - 若 $x_k \in D_{e_{k+1}}$（其中 $s(e_{k+1}) = v_k$），则转移至下一状态：
    $$v_{k+1} = t(e_{k+1}), \qquad x_{k+1} = b_{e_{k+1}}(x_k) \in U_{v_{k+1}}.$$
  - 若对一切 $k \ge 0$ 均有 $x_k \notin S_{v_k}$，则称轨线**不终止**，记 $\tau(v, x) = +\infty$，其生成一条无穷边序列 $\pi(v, x) = (e_1, e_2, \ldots)$。

根据停机时间，点态构造整体算子 $F^*_v(x)$：

#### (1) 有限终止情形 ($\tau(v, x) = k < +\infty$)
算子直接由有限次返回算子与停机输出的复合显式给出：
$$F^*_v(x) := (a_{e_1} \circ a_{e_2} \circ \cdots \circ a_{e_k})\bigl(h_{\nu(v, x)}(\xi(v, x))\bigr).$$
特别地：
- 若 $k = 0$（即 $x \in S_v$），则 $F^*_v(x) = h_v(x)$；
- 若 $k = 1$（$x \in D_{e_1}$ 且 $b_{e_1}(x) \in S_{t(e_1)}$），则 $F^*_v(x) = a_{e_1}(h_{t(e_1)}(b_{e_1}(x)))$。

由于 $h \in \mathcal X^\circ$ 且 $a_e(\mathcal X^\circ) \subseteq \mathcal X^\circ$，此复合完全在有效空间 $\mathcal X^\circ$ 内部完成，具有纯代数闭式，无需任何极限过程。

#### (2) 无穷轨线情形 ($\tau(v, x) = +\infty$)
任取参考点 $y \in \mathcal X^\circ$（或任意初始算子族 $H \in \mathcal F$），定义截断逼近点列：
$$y_n(x) = (a_{e_1} \circ a_{e_2} \circ \cdots \circ a_{e_n})\bigl(H_{v_n}(x_n)\bigr).$$
由下文引理 2 及 $\rho(M) < 1$ 知，算子乘积的 Lipschitz 界满足：
$$\mathbf d(y_{n+p}(x), y_n(x)) \le (L_{e_1} \cdots L_{e_n}) \mathbf d(y_p(x_n), H_{v_n}(x_n)) \le (M^n)_{v, v_n} \boldsymbol\Delta(\mathcal T^p H, H) \to \mathbf 0 \quad (n \to \infty).$$
因此 $(y_n(x))_{n \ge 1}$ 为 $\mathcal X^\circ$ 中的广义柯西序列。由完备性，整体算子定义为拓扑极限：
$$F^*_v(x) := \lim_{n \to \infty} (a_{e_1} \circ a_{e_2} \circ \cdots \circ a_{e_n})(y) \in \mathcal X^\circ,$$
该极限独立于参考点 $y$ 的选取。

### 2. 解析级数构造法（Neumann Series / Successive Approximation）
在算子族空间 $\mathcal F$ 上，任取基准族 $H \in \mathcal F$（例如令 $H_v(x) = h_v(x)$ 当 $x \in S_v$），整体算子 $F^*$ 表达为 Picard 迭代的收敛极限：
$$F^* = \lim_{n \to \infty} \mathcal T^n H = H + \sum_{k=0}^\infty \left(\mathcal T^{k+1} H - \mathcal T^k H\right),$$
其中级数在向量伪度量 $\boldsymbol\Delta$ 诱导的拓扑下一致绝对收敛。

---

## 四、 完整数学论证

整个论证分解为以下引理和步骤：

### 引理 1（非负矩阵的 Perron–Frobenius 严格收缩性）
设 $M \in \mathbb R_{\ge 0}^{K \times K}$，$\rho(M) < 1$。则对任意给定的常数 $q \in (\rho(M), 1)$：
1. 预解矩阵 $(q I - M)^{-1} = \sum_{k=0}^\infty q^{-(k+1)} M^k$ 存在且非负；
2. 令 $\mathbf 1 = (1, 1, \ldots, 1)^{\mathsf T}$，构造向量 $u := (q I - M)^{-1} \mathbf 1$。则 $u$ 严格正值（即 $u_j \ge q^{-1} > 0$），且满足：
   $$M u = q u - \mathbf 1 \le q u;$$
3. 定义 $\mathbb R^K$ 上的加权最大范数 $\|\mathbf y\|_u := \max_{1 \le j \le K} \frac{|y_j|}{u_j}$，则对任意非负向量 $\mathbf y \ge \mathbf 0$：
   $$\|M \mathbf y\|_u \le q \|\mathbf y\|_u.$$
   进而对任意 $n \ge 1$：
   $$\|M^n \mathbf y\|_u \le q^n \|\mathbf y\|_u.$$

**证明**：
1. 矩阵级数 $\sum_{k=0}^\infty (M/q)^k$ 的谱半径为 $\rho(M/q) = \rho(M)/q < 1$，故级数绝对收敛于 $(I - M/q)^{-1}$，乘以 $q^{-1}$ 即得 $(q I - M)^{-1} \ge q^{-1} I \ge \mathbf 0$。
2. 计算：
   $$u = (q I - M)^{-1} \mathbf 1 = q^{-1} \mathbf 1 + \sum_{k=1}^\infty q^{-(k+1)} M^k \mathbf 1 \ge q^{-1} \mathbf 1 > \mathbf 0.$$
   两边左乘 $(q I - M)$：
   $$(q I - M) u = \mathbf 1 \implies M u = q u - \mathbf 1 \le q u.$$
3. 对任意 $\mathbf y \ge \mathbf 0$，由 $\|\cdot\|_u$ 的定义可知，按分量成立 $\mathbf y \le \|\mathbf y\|_u u$。由于 $M \ge \mathbf 0$，不等式在非负矩阵乘法下保持：
   $$M \mathbf y \le \|\mathbf y\|_u M u \le q \|\mathbf y\|_u u.$$
   两边除以 $u$，按分量取上确界即得：
   $$\|M \mathbf y\|_u = \max_{j} \frac{(M \mathbf y)_j}{u_j} \le q \|\mathbf y\|_u.$$
   通过归纳法，显然有 $\|M^n \mathbf y\|_u \le q^n \|\mathbf y\|_u$。 $\blacksquare$

---

### 引理 2（展开映射 $\mathcal T$ 的向量距离单调收缩性）
对任意算子族 $F, G \in \mathcal F$，按分量成立如下矩阵–向量不等式：
$$\boldsymbol\Delta(\mathcal T F, \mathcal T G) \le M \boldsymbol\Delta(F, G).$$

**证明**：
固定任意节点 $v \in V$ 及点 $x \in U_v$。根据划分 $U_v = S_v \sqcup \bigsqcup_{e: s(e)=v} D_e$，分情况讨论：

**情形 1**：$x \in S_v$。
根据 $\mathcal T$ 的定义：
$$(\mathcal T F)_v(x) = h_v(x) = (\mathcal T G)_v(x).$$
由伪度量的自反性，$d_i((\mathcal T F)_v(x), (\mathcal T G)_v(x)) = d_i(h_v(x), h_v(x)) = 0$（对一切 $1 \le i \le m$）。故：
$$\mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) = \mathbf 0.$$

**情形 2**：$x \in D_e$，其中 $e \in E$ 是源自 $v$ 的唯一起始边，$s(e) = v$，$w = t(e)$。
此时：
$$(\mathcal T F)_v(x) = a_e\bigl(F_w(b_e(x))\bigr), \qquad (\mathcal T G)_v(x) = a_e\bigl(G_w(b_e(x))\bigr).$$
注意到 $b_e(x) \in U_w$，因此 $F_w(b_e(x)) \in \mathcal X^\circ$ 且 $G_w(b_e(x)) \in \mathcal X^\circ$。利用返回算子 $a_e$ 在 $\mathcal X^\circ$ 上的矩阵 Lipschitz 连续性：
$$\mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) \le L_e \mathbf d\bigl(F_w(b_e(x)), G_w(b_e(x))\bigr).$$
根据上确界定义，对该特定的点 $b_e(x) \in U_w$，有：
$$\mathbf d\bigl(F_w(b_e(x)), G_w(b_e(x))\bigr) \le \boldsymbol\Delta_w(F, G).$$
由于 $L_e \ge \mathbf 0$，且按约定 $0 \cdot (+\infty) = 0$：
$$\mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) \le L_e \boldsymbol\Delta_w(F, G).$$

综合上述两组情形，对整个定义域 $U_v$ 取上确界：
$$\boldsymbol\Delta_v(\mathcal T F, \mathcal T G) = \sup_{x \in U_v} \mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) = \max \left\{ \mathbf 0, \; \sup_{e: s(e)=v} \sup_{x \in D_e} \mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) \right\}$$
$$\le \sup_{e: s(e)=v} L_e \boldsymbol\Delta_{t(e)}(F, G).$$
由于对每条边 $e$ 都有 $L_e \le \sum_{e': s(e')=v, t(e')=t(e)} L_{e'} = M_{v, t(e)}$，且所有项非负，故：
$$\sup_{e: s(e)=v} L_e \boldsymbol\Delta_{t(e)}(F, G) \le \sum_{w \in V} M_{vw} \boldsymbol\Delta_w(F, G) = \bigl(M \boldsymbol\Delta(F, G)\bigr)_v.$$
上述不等式对所有分量 $v \in V$ 和 $1 \le i \le m$ 均成立，写成整块向量形式即为：
$$\boldsymbol\Delta(\mathcal T F, \mathcal T G) \le M \boldsymbol\Delta(F, G).$$
归纳即得：
$$\boldsymbol\Delta(\mathcal T^n F, \mathcal T^n G) \le M^n \boldsymbol\Delta(F, G) \qquad (\forall n \ge 1). \quad \blacksquare$$

---

### 命题 1（不动点的存在性与唯一性证明）

**存在性**：
任取初始算子族 $H \in \mathcal F$。考查迭代序列 $F^{(n)} = \mathcal T^n H$。
对任意 $n \ge 0$ 及 $p \ge 1$，由引理 2 及三角不等式：
$$\boldsymbol\Delta(F^{(n+p)}, F^{(n)}) \le \sum_{k=n}^{n+p-1} \boldsymbol\Delta(F^{(k+1)}, F^{(k)}) \le \sum_{k=n}^{n+p-1} M^k \boldsymbol\Delta(\mathcal T H, H) \le M^n \sum_{j=0}^\infty M^j \boldsymbol\Delta(\mathcal T H, H).$$
因为 $\rho(M) < 1$，矩阵级数 $(I - M)^{-1} = \sum_{j=0}^\infty M^j$ 收敛且非负。故：
$$\boldsymbol\Delta(F^{(n+p)}, F^{(n)}) \le M^n (I - M)^{-1} \boldsymbol\Delta(\mathcal T H, H).$$
由引理 1，当 $n \to \infty$ 时，$M^n \to \mathbf 0$（几何衰减）。
因此，对每个 $v \in V$ 和 $x \in U_v$，序列 $\{F^{(n)}_v(x)\}_{n=1}^\infty$ 是 $(\mathcal X^\circ, \mathbf d)$ 中的柯西序列。由空间完备性，逐点极限存在：
$$F^*_v(x) := \lim_{n \to \infty} F^{(n)}_v(x) \in \mathcal X^\circ.$$
在逐点展开式 $(\mathcal T F^{(n)})_v(x)$ 两端令 $n \to \infty$，因返回算子 $a_e$ 满足 Lipschitz 连续性，极限与算子可交换，即得：
$$F^* = \mathcal T F^*.$$
（注：在第三节构造法 1 中，对有限终止点，当 $n > \tau(v, x)$ 时 $F^{(n)}_v(x)$ 直接恒等于有限复合式，自然满足方程；对于整体有限终止系统，完全不依赖极限即精确满足 $F^* = \mathcal T F^*$）。

**唯一性**：
设另有 $\widetilde F \in \mathcal F$ 满足 $\widetilde F = \mathcal T \widetilde F$。
则对任意 $n \ge 1$：
$$\boldsymbol\Delta(F^*, \widetilde F) = \boldsymbol\Delta(\mathcal T^n F^*, \mathcal T^n \widetilde F) \le M^n \boldsymbol\Delta(F^*, \widetilde F).$$
若 $\boldsymbol\Delta(F^*, \widetilde F)$ 有限，由 $M^n \to \mathbf 0$ 直接导出 $\boldsymbol\Delta(F^*, \widetilde F) = \mathbf 0$。
即使在逐点意义下，对任意有限终止点，两者均唯一等同于有限复合链；对非终止点，其距离受控于 $M^n \to \mathbf 0$，故在伪度量意义下必有 $\mathbf d(F^*_v(x), \widetilde F_v(x)) = \mathbf 0$。唯一性得证。 $\blacksquare$

---

### 命题 2（几何收敛速度与常数 $C_H$ 的严格推导）

现证明对任意初始族 $H \in \mathcal F$，有限展开以几何速度逼近 $F^*$。

**证明**：
因为 $F^* = \mathcal T^n F^*$，应用引理 2 可得：
$$\boldsymbol\Delta(\mathcal T^n H, F^*) = \boldsymbol\Delta(\mathcal T^n H, \mathcal T^n F^*) \le M^n \boldsymbol\Delta(H, F^*).$$
现在利用引理 1 中的正特征向量 $u > \mathbf 0$ 及对应的加权范数 $\|\cdot\|_u$ 进行定界：
根据引理 1，对任意非负向量 $\mathbf y$，有 $\|M^n \mathbf y\|_u \le q^n \|\mathbf y\|_u$。
将此式应用于 $\mathbf y = \boldsymbol\Delta(H, F^*)$：
$$\|\boldsymbol\Delta(\mathcal T^n H, F^*)\|_u \le \|M^n \boldsymbol\Delta(H, F^*)\|_u \le q^n \|\boldsymbol\Delta(H, F^*)\|_u.$$
接下来建立加权范数 $\|\cdot\|_u$ 与标准的无穷范数 $\|\cdot\|_\infty$ 之间的等价双边控制：
记 $u_{\min} := \min_{1 \le j \le |V|m} u_j > 0$，$u_{\max} := \max_{1 \le j \le |V|m} u_j < +\infty$。
对任意非负向量 $\mathbf z \in \mathbb R_{\ge 0}^{|V|m}$：
$$\frac{1}{u_{\max}} \|\mathbf z\|_\infty \le \|\mathbf z\|_u = \max_j \frac{z_j}{u_j} \le \frac{1}{u_{\min}} \|\mathbf z\|_\infty.$$
因此，对于误差向量 $\boldsymbol\Delta(\mathcal T^n H, F^*)$ 的最大分量：
$$\max_{v \in V, 1 \le i \le m} \Delta_{v, i}(\mathcal T^n H, F^*) = \|\boldsymbol\Delta(\mathcal T^n H, F^*)\|_\infty$$
$$\le u_{\max} \|\boldsymbol\Delta(\mathcal T^n H, F^*)\|_u$$
$$\le u_{\max} q^n \|\boldsymbol\Delta(H, F^*)\|_u$$
$$\le \frac{u_{\max}}{u_{\min}} q^n \|\boldsymbol\Delta(H, F^*)\|_\infty.$$
令有限常数：
$$C_H := \frac{u_{\max}}{u_{\min}} \max_{v, i} \Delta_{v, i}(H, F^*),$$
即完整证明了：
$$\max_{v, i} \Delta_{v, i}(\mathcal T^n H, F^*) \le C_H q^n \qquad (\forall n \ge 1).$$

若改用单步展开初始偏差 $\boldsymbol\Delta(H, \mathcal T H)$，由：
$$\boldsymbol\Delta(\mathcal T^n H, F^*) \le M^n (I - M)^{-1} \boldsymbol\Delta(H, \mathcal T H),$$
同样立即得到：
$$C_H = \frac{u_{\max}}{u_{\min}} \left\|(I - M)^{-1} \boldsymbol\Delta(H, \mathcal T H)\right\|_\infty < +\infty.$$
证毕。 $\blacksquare$

---

## 五、 理论总结与结构全景

```
                     [ 局域系统数据 ]
      (V, E),  U_v = S_v ⊔ ⨆ D_e,  h_v,  b_e,  a_e
                             │
                             ▼
    [ 局域收缩矩阵 L_e ] ──► [ 全局转移矩阵 M = ∑ L_e ] ──► ρ(M) < 1
                             │
                             ▼
    [ 确定性转移流: x ↦ b_e(x) ] ──► 轨线分流分析
         ┌───────────────────┴───────────────────┐
         ▼                                       ▼
  【有限步终止: τ(v,x) < ∞】             【无穷步递归: τ(v,x) = ∞】
         │                                       │
         ▼                                       ▼
 显式代数复合 (无需完备性):               广义柯西极限 (由 ρ(M)<1 保证):
 F*_v(x) = (a_e1 ∘...∘ a_ek)(h)          F*_v(x) = lim (a_e1 ∘...∘ a_en)(y)
         └───────────────────┬───────────────────┘
                             │
                             ▼
              [ 唯一的闭合整体算子族 F* = T F* ]
                             │
                             ▼
              [ Perron-Frobenius 加权范数定界 ]
        max Δ_{v,i}(T^n H, F*) ≤ C_H · q^n   (几何收敛性)
```

本闭合理论证明了：
1. **多重图网络结构的拓扑递归**被完全代数化编码进非负块矩阵 $M$；
2. 只要全局谱半径 $\rho(M) < 1$，即使局域返回算子存在放大环节（某些单条边的 $L_e$ 谱半径可能大于 1，只要环路整体衰减），系统仍存在**唯一的全局递归闭合**；
3. 任意有限初始算子展开族 $\mathcal T^n H$ 均以矩阵谱半径严格决定的收敛因子 $q \in (\rho(M), 1)$ 实现一致几何衰减。
