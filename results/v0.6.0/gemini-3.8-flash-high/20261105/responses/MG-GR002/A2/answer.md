# 线性记录、有限观测与原空间恢复

---

### S1　记录的完整载体

#### 1. 兼容有界记录与 $E''$ 的双向等距识别

记 $\mathcal{F}(E')$ 为 $E'$ 中所有有限维线性子空间按包含关系偏序构成的有向集。令 $\mathcal{R}$ 为所有满足相容性条件与一致有界性条件的记录族 $\lambda = (\lambda_F)_{F \in \mathcal{F}(E')}$ 之集。

##### (1) 构造映射 $\Phi: \mathcal{R} \to E''$
对任意记录 $\lambda \in \mathcal{R}$，定义泛函 $z_\lambda: E' \to \mathbb{R}$ 为：
对任意 $\varphi \in E'$，取一维子空间 $\mathbb{R}\varphi \in \mathcal{F}(E')$，定义
$$z_\lambda(\varphi) := \lambda_{\mathbb{R}\varphi}(\varphi).$$

* **相容性与良定性**：若 $F \in \mathcal{F}(E')$ 且 $\varphi \in F$，则 $\mathbb{R}\varphi \subset F$。由题设相容性 $\lambda_F|_{\mathbb{R}\varphi} = \lambda_{\mathbb{R}\varphi}$，必有 $\lambda_F(\varphi) = \lambda_{\mathbb{R}\varphi}(\varphi) = z_\lambda(\varphi)$。
* **线性性**：对任意 $\varphi, \psi \in E'$ 及 $\alpha, \beta \in \mathbb{R}$，令 $F = \operatorname{span}\{\varphi, \psi\} \in \mathcal{F}(E')$。由 $\lambda_F$ 的线性性：
  $$z_\lambda(\alpha\varphi + \beta\psi) = \lambda_F(\alpha\varphi + \beta\psi) = \alpha\lambda_F(\varphi) + \beta\lambda_F(\psi) = \alpha z_\lambda(\varphi) + \beta z_\lambda(\psi).$$
* **有界性**：由题设 $|z_\lambda(\varphi)| = |\lambda_{\mathbb{R}\varphi}(\varphi)| \le C\|\varphi\|$，故 $z_\lambda$ 是 $E'$ 上的连续线性泛函，即 $z_\lambda \in E''$，且 $\|z_\lambda\|_{E''} \le C$。令 $\Phi(\lambda) = z_\lambda$。

##### (2) 构造映射 $\Psi: E'' \to \mathcal{R}$
对任意 $z \in E''$，对每个 $F \in \mathcal{F}(E')$，定义限制映射
$$\lambda^z_F := z|_F: F \to \mathbb{R}.$$

* **线性性**：因 $z$ 是线性的，其限制 $\lambda^z_F$ 显然为 $F$ 上的线性泛函。
* **相容性**：若 $F \subset G \in \mathcal{F}(E')$，则 $\lambda^z_G|_F = (z|_G)|_F = z|_F = \lambda^z_F$。
* **有界性**：对 $\varphi \in F$，$|\lambda^z_F(\varphi)| = |z(\varphi)| \le \|z\|_{E''}\|\varphi\|$，即满足界常数 $C = \|z\|_{E''}$。令 $\Psi(z) = (\lambda^z_F)_{F\in\mathcal{F}(E')}$。

##### (3) 双向逆与等距性
* 对任意 $z \in E''$，$\Phi(\Psi(z))(\varphi) = \lambda^z_{\mathbb{R}\varphi}(\varphi) = z(\varphi)$，故 $\Phi \circ \Psi = \operatorname{id}_{E''}$。
* 对任意 $\lambda \in \mathcal{R}$ 及 $\varphi \in F$，$\Psi(\Phi(\lambda))_F(\varphi) = z_\lambda(\varphi) = \lambda_F(\varphi)$，故 $\Psi \circ \Phi = \operatorname{id}_{\mathcal{R}}$。
* **距离等距**：
  $$d(\lambda, \mu) = \sup_{\|\varphi\|\le 1} |\lambda_{\mathbb{R}\varphi}(\varphi) - \mu_{\mathbb{R}\varphi}(\varphi)| = \sup_{\|\varphi\|\le 1} |z_\lambda(\varphi) - z_\mu(\varphi)| = \|z_\lambda - z_\mu\|_{E''}.$$
因此，$(\mathcal{R}, d)$ 与 $(E'', \|\cdot\|_{E''})$ 在映射 $\Phi$ 下实现等距同构。

---

#### 2. 规范嵌入 $J: E \to E''$ 线性等距的证明

规范映射 $J: E \to E''$ 定义为 $J(x)(\varphi) = \varphi(x)$（$\forall x \in E, \varphi \in E'$）。
* **线性性**：对任意 $x, y \in E$ 及 $\alpha, \beta \in \mathbb{R}$，$\forall \varphi \in E'$：
  $$J(\alpha x + \beta y)(\varphi) = \varphi(\alpha x + \beta y) = \alpha\varphi(x) + \beta\varphi(y) = (\alpha J(x) + \beta J(y))(\varphi).$$
* **等距性**：由算子范数定义，
  $$\|J(x)\|_{E''} = \sup_{\|\varphi\|_{E'}\le 1} |J(x)(\varphi)| = \sup_{\|\varphi\|_{E'}\le 1} |\varphi(x)| \le \sup_{\|\varphi\|_{E'}\le 1} \|\varphi\|_{E'}\|x\|_E = \|x\|_E.$$
  反之，由 Hahn-Banach 定理推论（对赋范空间中任意非零元存在赋范对偶元达范数）：对任意 $x \in E$，存在 $\varphi_0 \in E'$ 满足 $\|\varphi_0\|_{E'} = 1$ 且 $\varphi_0(x) = \|x\|_E$。
  从而 $\|J(x)\|_{E''} \ge |\varphi_0(x)| = \|x\|_E$。综合两式得 $\|J(x)\|_{E''} = \|x\|_E$。

---

#### 3. 记录变换 $\lambda \mapsto \lambda^T$ 对应 $T''$ 的证明

设 $T: E \to E$ 是有界线性算子，其对偶算子 $T': E' \to E'$ 满足 $(T'\varphi)(x) = \varphi(Tx)$，二次对偶算子 $T'': E'' \to E''$ 满足 $(T''z)(\varphi) = z(T'\varphi)$。
对任意记录 $\lambda \in \mathcal{R}$，对应泛函为 $z_\lambda = \Phi(\lambda)$。变换后的记录为 $\lambda^T$，其在任意 $\varphi \in E'$ 上对应的值为：
$$z_{\lambda^T}(\varphi) = \lambda^T_{\mathbb{R}\varphi}(\varphi) = \lambda_{T'(\mathbb{R}\varphi)}(T'\varphi).$$
注意到 $T'\varphi \in T'(\mathbb{R}\varphi)$ 且 $\dim(T'(\mathbb{R}\varphi)) \le 1$。由相容性：
$$\lambda_{T'(\mathbb{R}\varphi)}(T'\varphi) = z_\lambda(T'\varphi) = (T'' z_\lambda)(\varphi).$$
因此 $z_{\lambda^T} = T'' z_\lambda$，即 $\Phi(\lambda^T) = T''(\Phi(\lambda))$，记录变换在识别下恰为二次对偶算子 $T''$。

---

### S2　可恢复记录的稳定性

本阶段假设 $E$ 自反，即规范嵌入 $J: E \to E''$ 为满射等距同构，其逆算子 $J^{-1}: E'' \to E$ 存在且同为等距同构。

#### 1. 唯一原空间恢复 $x_\lambda$ 的构造与算子相容性
* **构造**：对任意记录 $\lambda$，令 $z_\lambda = \Phi(\lambda) \in E''$ 为 S1 中识别的泛函，定义
  $$x_\lambda := J^{-1}(z_\lambda) \in E.$$
  此时对任意有限维 $F \subset E'$ 及 $\varphi \in F$，
  $$\varphi(x_\lambda) = J(x_\lambda)(\varphi) = z_\lambda(\varphi) = \lambda_F(\varphi).$$
  特别地，对任意有限观测组 $(\varphi_1, \ldots, \varphi_k)$，均有 $\varphi_i(x_\lambda) = \lambda_F(\varphi_i)$，实现了全部记录。
* **唯一性**：若另有 $x \in E$ 满足 $\varphi(x) = \lambda_{\mathbb{R}\varphi}(\varphi) = z_\lambda(\varphi)$（$\forall \varphi \in E'$），则 $J(x) = z_\lambda$。因 $J$ 是单射，必有 $x = J^{-1}(z_\lambda) = x_\lambda$。
* **与 $T$ 相容**：需证 $x_{\lambda^T} = T x_\lambda$。
  对任意 $x \in E$ 与 $\varphi \in E'$，有
  $$(T'' J(x))(\varphi) = J(x)(T'\varphi) = (T'\varphi)(x) = \varphi(Tx) = J(Tx)(\varphi),$$
  即恒有 $T'' \circ J = J \circ T$，故 $T \circ J^{-1} = J^{-1} \circ T''$。
  由 S1，$\Phi(\lambda^T) = T'' z_\lambda$，因此：
  $$x_{\lambda^T} = J^{-1}(z_{\lambda^T}) = J^{-1}(T'' z_\lambda) = T(J^{-1}(z_\lambda)) = T x_\lambda.$$

---

#### 2. 稳定性不等式的证明
对两份记录 $\lambda, \mu$ 及两个有界算子 $T, U \in \mathcal{L}(E)$：
由上述相容性，$x_{\lambda^T} = T x_\lambda$，$x_{\mu^U} = U x_\mu$。展开得：
$$x_{\lambda^T} - x_{\mu^U} = T x_\lambda - U x_\mu = T(x_\lambda - x_\mu) + (T - U) x_\mu.$$
由三角不等式及算子范数性质：
$$\|x_{\lambda^T} - x_{\mu^U}\|_E \le \|T(x_\lambda - x_\mu)\|_E + \|(T - U) x_\mu\|_E \le \|T\| \|x_\lambda - x_\mu\|_E + \|T - U\| \|x_\mu\|_E.$$
由于 $J^{-1}: E'' \to E$ 是保范同构：
$$\|x_\lambda - x_\mu\|_E = \|J^{-1}(z_\lambda - z_\mu)\|_E = \|z_\lambda - z_\mu\|_{E''} = d(\lambda, \mu).$$
代入即得：
$$\|x_{\lambda^T} - x_{\mu^U}\| \le \|T\| d(\lambda, \mu) + \|T - U\| \|x_\mu\|.$$

---

### S3　子空间约束

本阶段在 S2 条件下（$E$ 自反），$Y \subset E$ 为闭线性子空间，$Y^\perp = \{\varphi \in E': \varphi|_Y = 0\}$。

#### 1. 证明 $x_\lambda \in Y \iff z_\lambda|_{Y^\perp} = 0$
* **必要性 ($\implies$)**：若 $x_\lambda \in Y$，则对任意 $\varphi \in Y^\perp$，按定义 $\varphi|_Y = 0$，故
  $$z_\lambda(\varphi) = \varphi(x_\lambda) = 0.$$
  因此 $z_\lambda|_{Y^\perp} = 0$。
* **充分性 ($\impliedby$)**：反设 $x_\lambda \notin Y$。
  因为 $Y$ 是赋范空间 $E$ 的闭线性子空间，由 Hahn-Banach 几何分离定理（或连续泛函分离闭子空间与点）：存在连续线性泛函 $\varphi_0 \in E'$ 使得
  $$\varphi_0|_Y = 0 \quad (\text{即 } \varphi_0 \in Y^\perp) \quad \text{且} \quad \varphi_0(x_\lambda) = \operatorname{dist}(x_\lambda, Y) > 0.$$
  于是 $z_\lambda(\varphi_0) = \varphi_0(x_\lambda) > 0$，与 $z_\lambda|_{Y^\perp} = 0$ 矛盾。故必有 $x_\lambda \in Y$。

---

#### 2. $\operatorname{dist}(x_\lambda, Y)$ 的准确对偶公式

##### 公式形式
$$\operatorname{dist}(x_\lambda, Y) = \max_{\substack{\varphi \in Y^\perp \\ \|\varphi\|_{E'} \le 1}} |\lambda_{\mathbb{R}\varphi}(\varphi)| = \sup_{\substack{\varphi \in Y^\perp \\ \|\varphi\|_{E'} \le 1}} |\lambda_{\mathbb{R}\varphi}(\varphi)|.$$

##### 论证
1. **上界不等式**：对任意 $y \in Y$ 及任意 $\varphi \in Y^\perp$ 且 $\|\varphi\| \le 1$，因 $\varphi(y) = 0$：
   $$|\varphi(x_\lambda)| = |\varphi(x_\lambda - y)| \le \|\varphi\| \|x_\lambda - y\| \le \|x_\lambda - y\|.$$
   对 $y \in Y$ 取下确界得 $|\varphi(x_\lambda)| \le \operatorname{dist}(x_\lambda, Y)$，故
   $$\sup_{\varphi \in Y^\perp, \|\varphi\|\le 1} |z_\lambda(\varphi)| \le \operatorname{dist}(x_\lambda, Y).$$
2. **达范与等式**：考虑商空间 $E/Y$ 及其规范商映射 $\pi: E \to E/Y$。由于 $Y$ 为闭子空间，$(E/Y)'$ 与 $Y^\perp$ 等距同构，且 $[x_\lambda]$ 在商空间中的范数为 $\|[x_\lambda]\|_{E/Y} = \operatorname{dist}(x_\lambda, Y)$。
   因为 $E$ 自反，$E$ 的闭子空间 $Y$ 与商空间 $E/Y$ 均自反。
   在自反空间 $E/Y$ 中，由 Hahn-Banach 定理及自反空间的达范性，存在商空间对偶元（对应某个 $\varphi_0 \in Y^\perp$，$\|\varphi_0\|_{E'} = 1$）使得
   $$\varphi_0(x_\lambda) = \|[x_\lambda]\|_{E/Y} = \operatorname{dist}(x_\lambda, Y).$$
3. **记录表达**：由于对每个 $\varphi \in Y^\perp$，$\varphi(x_\lambda) = z_\lambda(\varphi) = \lambda_{\mathbb{R}\varphi}(\varphi)$，直接代入即得由记录表示的准确极值对偶公式。

---

### S4　一般Banach空间

#### 结论
**否**。在一般实 Banach 空间上，结论不成立：并非每份合法记录都能在 $E$ 中实现。

#### 完整反例与核验

* **空间选取**：取实 Banach 空间 $E = c_0$（赋以上确界范数 $\|x\|_\infty = \sup_{n\ge 1}|x_n|$）。
  众所周知，$c_0' \cong \ell^1$（范数为 $\|\varphi\|_1 = \sum_{n=1}^\infty |\varphi_n|$），$c_0'' \cong \ell^\infty$。$c_0$ 非自反。
* **合法记录构造**：取序列 $z = (1, 1, 1, \ldots) \in \ell^\infty = c_0''$，其范数 $\|z\|_{\infty} = 1$。
  对每个有限维子空间 $F \subset \ell^1$，对任意 $\varphi = (\varphi_n)_{n=1}^\infty \in F$，定义
  $$\lambda_F(\varphi) := \sum_{n=1}^\infty \varphi_n.$$
* **核验记录合法性**：
  1. *线性性*：级数关于数列运算是线性的，$\lambda_F$ 为 $F$ 上的线性映射；
  2. *相容性*：若 $F \subset G$，$\lambda_G|_F(\varphi) = \sum_{n=1}^\infty \varphi_n = \lambda_F(\varphi)$；
  3. *一致有界性*：对任意 $\varphi \in F$，
     $$|\lambda_F(\varphi)| = \left|\sum_{n=1}^\infty \varphi_n\right| \le \sum_{n=1}^\infty |\varphi_n| = \|\varphi\|_1.$$
     故一致界 $C = 1$ 成立。
* **核验原空间不可实现**：
  假设存在 $x = (x_n)_{n=1}^\infty \in c_0$ 实现了全部记录。
  对任意固定的 $k \in \mathbb{N}$，取 $\ell^1$ 中的标准基向量 $e_k$（第 $k$ 位为 $1$，其余位为 $0$）。
  考虑一维子空间 $F_k = \mathbb{R} e_k$。按实现要求：
  $$x_k = e_k(x) = \lambda_{F_k}(e_k) = 1.$$
  由于 $k$ 是任意的，必有 $x_k = 1$ 对所有 $k \in \mathbb{N}$ 成立，即 $x = (1, 1, 1, \ldots)$。
  但 $x \in c_0$ 要求 $\lim_{k\to\infty} x_k = 0$，而此处 $\lim_{k\to\infty} x_k = 1 \ne 0$，因此 $(1, 1, 1, \ldots) \notin c_0$。
  这表明在 $c_0$ 中根本不存在任何元 $x$ 能实现该合法记录，原空间恢复全面失效。

---

### S5　单条记录的拓扑条件

#### 结论
**是，必可在 $E$ 中实现。**

#### 充要关系
设 $E$ 为任意实 Banach 空间，$\lambda$ 为合法记录，$z_\lambda \in E''$ 为 S1 赋予的对偶泛函。则：
$$\lambda \text{ 可在 } E \text{ 中实现} \iff z_\lambda: E' \to \mathbb{R} \text{ 关于弱星拓扑 } \sigma(E', E) \text{ 连续。}$$
且在满足该条件时，实现元 $x_\lambda \in E$ 是唯一的，并满足 $\|x_\lambda\|_E = \|z_\lambda\|_{E''} \le C$。

#### 论证

##### 1. 充分性 ($\impliedby$)
已知 $z_\lambda$ 是 $(E', \sigma(E', E))$ 上的连续线性泛函。
* 按弱星拓扑 $\sigma(E', E)$ 的定义，$0 \in E'$ 的邻域基由形如
  $$V(x_1, \ldots, x_m; \delta) = \{\varphi \in E' : |\varphi(x_i)| < \delta, \ i = 1, \ldots, m\}$$
  的有界开邻域构成（其中 $m \in \mathbb{N}$，$x_1, \ldots, x_m \in E$，$\delta > 0$）。
* 由 $z_\lambda$ 在 $0$ 处的连续性，存在 $x_1, \ldots, x_m \in E$ 及 $\delta > 0$，使得
  $$\varphi \in V(x_1, \ldots, x_m; \delta) \implies |z_\lambda(\varphi)| \le 1.$$
* 若 $\varphi \in \bigcap_{i=1}^m \ker(J(x_i))$，即 $\varphi(x_i) = 0$（$i=1,\ldots,m$），则对任意标量 $t \in \mathbb{R}$，均有 $t\varphi \in V(x_1, \ldots, x_m; \delta)$。
  从而 $|z_\lambda(t\varphi)| = |t||z_\lambda(\varphi)| \le 1$ 对所有 $t > 0$ 成立，迫使 $z_\lambda(\varphi) = 0$。
  因此，
  $$\bigcap_{i=1}^m \ker(J(x_i)) \subset \ker(z_\lambda).$$
* 由线性代数的基本引理（多泛函核包含引理）：设 $f, f_1, \ldots, f_m$ 为线性空间上的线性泛函，若 $\bigcap_{i=1}^m \ker(f_i) \subset \ker(f)$，则 $f \in \operatorname{span}\{f_1, \ldots, f_m\}$。
  *(证明要点：线性映射 $\varphi \mapsto (f_1(\varphi), \ldots, f_m(\varphi))$ 的核包含在 $\ker(f)$ 中，故 $f$ 可在像空间上良定为线性函数并延拓至 $\mathbb{R}^m$，即表示为线性组合)*。
* 将此引理应用于 $E'$ 上的泛函 $z_\lambda$ 与 $J(x_1), \ldots, J(x_m)$，可知存在常数 $c_1, \ldots, c_m \in \mathbb{R}$，使得
  $$z_\lambda = \sum_{i=1}^m c_i J(x_i) = J\left(\sum_{i=1}^m c_i x_i\right).$$
* 令 $x = \sum_{i=1}^m c_i x_i \in E$。则 $J(x) = z_\lambda$。
  对任意有限维 $F \subset E'$ 及 $\varphi \in F$：
  $$\varphi(x) = J(x)(\varphi) = z_\lambda(\varphi) = \lambda_F(\varphi).$$
  故 $x$ 在 $E$ 中精确实现了记录 $\lambda$。
  唯一性由 Hahn-Banach 定理保证：若 $\varphi(x) = \varphi(\tilde{x})$ 对所有 $\varphi \in E'$ 成立，则 $x = \tilde{x}$。
  又 $\|x\|_E = \|J(x)\|_{E''} = \|z_\lambda\|_{E''} \le C$。

##### 2. 必要性 ($\implies$)
若 $\lambda$ 在 $E$ 中可由某 $x \in E$ 实现，则对所有 $\varphi \in E'$ 均有 $z_\lambda(\varphi) = \lambda_{\mathbb{R}\varphi}(\varphi) = \varphi(x) = J(x)(\varphi)$。
即 $z_\lambda = J(x)$。
由弱星拓扑 $\sigma(E', E)$ 的定义，对任意网 $\varphi_\alpha \xrightarrow{\sigma(E',E)} \varphi$，按点态收敛定义均有 $\varphi_\alpha(x) \to \varphi(x)$。
因此 $z_\lambda(\varphi_\alpha) \to z_\lambda(\varphi)$，即 $z_\lambda$ 必关于 $\sigma(E', E)$ 连续。

---

### S6　有限观测的精确匹配

#### 1. 存在精确匹配元 $x_{F,\varepsilon}$ 的证明

设 $F \subset E'$ 为有限维子空间，记 $k = \dim F$。若 $k=0$，取 $x = 0$ 显然成立。
设 $k \ge 1$，取 $F$ 的一组基 $\{\varphi_1, \ldots, \varphi_k\}$。

* **商映射的满度与开映射**：
  映射 $q_F: E \to F^*$ 定义为 $q_F(x)(\varphi) = \varphi(x)$。
  通过基底识别 $F^* \cong \mathbb{R}^k$：$q_F(x) = (\varphi_1(x), \ldots, \varphi_k(x))$。
  因为 $\varphi_1, \ldots, \varphi_k$ 在 $E'$ 中线性无关，由 Hahn-Banach 定理，$q_F: E \to \mathbb{R}^k$ 必为满射（若非满射，存在非零向量 $a \in \mathbb{R}^k$ 正交于像，即 $\sum_{i=1}^k a_i \varphi_i(x) = 0$ 对所有 $x \in E$ 成立，导致 $\sum a_i \varphi_i = 0$，矛盾）。
  由 Banach 开映射定理，$q_F$ 为开映射。特别地，对任意 $\varepsilon > 0$，$q_F(B_E(0, \varepsilon))$ 是 $\mathbb{R}^k$ 中包含原点的开邻域。
* **闭包包含的 Hahn-Banach 分离论证**：
  记开球 $B_E(0, C) = \{x \in E: \|x\|_E < C\}$，令 $K = q_F(B_E(0, C)) \subset \mathbb{R}^k$。$K$ 为凸集且关于原点对称。
  将记录在基底的值记为 $c = (\lambda_F(\varphi_1), \ldots, \lambda_F(\varphi_k)) \in \mathbb{R}^k$。
  断言：$c \in \overline{K}$。
  反设 $c \notin \overline{K}$。在有限维欧氏空间 $\mathbb{R}^k$ 中，由凸集严格分离定理，存在非零向量 $a = (a_1, \ldots, a_k) \in \mathbb{R}^k$ 使得
  $$\sum_{i=1}^k a_i c_i > \sup_{w \in \overline{K}} \sum_{i=1}^k a_i w_i = \sup_{x \in B_E(0, C)} \sum_{i=1}^k a_i \varphi_i(x).$$
  记泛函 $\psi = \sum_{i=1}^k a_i \varphi_i \in F$。上式右端为
  $$\sup_{x \in B_E(0, C)} \psi(x) = C \|\psi\|_{E'}.$$
  上式左端由 $\lambda_F$ 的线性性为
  $$\sum_{i=1}^k a_i \lambda_F(\varphi_i) = \lambda_F\left(\sum_{i=1}^k a_i \varphi_i\right) = \lambda_F(\psi).$$
  从而导出 $\lambda_F(\psi) > C \|\psi\|_{E'}$，与题设界 $|\lambda_F(\psi)| \le C\|\psi\|_{E'}$ 矛盾。因此必有 $c \in \overline{K}$。
* **精确匹配构造**：
  由于 $c \in \overline{q_F(B_E(0, C))}$，且 $c - q_F(B_E(0, \varepsilon))$ 是点 $c$ 的开邻域，该邻域必与 $q_F(B_E(0, C))$ 有交点。
  即存在 $x_1 \in B_E(0, C)$ 满足 $q_F(x_1) \in c - q_F(B_E(0, \varepsilon))$。
  这意味着存在 $x_2 \in B_E(0, \varepsilon)$ 使得 $c - q_F(x_1) = q_F(x_2)$。
  令 $x_{F,\varepsilon} = x_1 + x_2 \in E$。则：
  1. $q_F(x_{F,\varepsilon}) = q_F(x_1) + q_F(x_2) = c = \lambda_F$；
  2. $\|x_{F,\varepsilon}\|_E \le \|x_1\|_E + \|x_2\|_E < C + \varepsilon \le C + \varepsilon$。
  命题得证。

---

#### 2. 判断是否总可取 $\varepsilon = 0$
**否**，不能总取 $\varepsilon = 0$。

##### 完整反例与核验
* **空间与泛函**：取 $E = c_0$（范数为 $\|\cdot\|_\infty$），对偶空间 $E' = \ell^1$。
  在 $\ell^1$ 中取泛函 $\varphi = \left(\frac{1}{2^n}\right)_{n=1}^\infty$。其范数为 $\|\varphi\|_1 = \sum_{n=1}^\infty \frac{1}{2^n} = 1$。
* **构造记录与子空间**：取一维子空间 $F = \mathbb{R}\varphi \subset \ell^1$。
  定义 $\lambda_F(t\varphi) = t$（$\forall t \in \mathbb{R}$）。
  界为 $C = 1$，因为 $|\lambda_F(t\varphi)| = |t| = |t|\|\varphi\|_1 = \|t\varphi\|_1$。
* **核验 $\varepsilon = 0$ 不可取**：
  若存在 $x = (x_n)_{n=1}^\infty \in c_0$ 满足 $q_F(x) = \lambda_F$ 且 $\|x\|_\infty \le C = 1$：
  1. $\|x\|_\infty \le 1 \implies |x_n| \le 1$ 对所有 $n \ge 1$ 成立，即 $1 - x_n \ge 0$；
  2. $q_F(x)(\varphi) = \lambda_F(\varphi) \implies \varphi(x) = \sum_{n=1}^\infty \frac{1}{2^n} x_n = 1$。
  由于 $\sum_{n=1}^\infty \frac{1}{2^n} = 1$，两式相减得：
  $$\sum_{n=1}^\infty \frac{1}{2^n} (1 - x_n) = 1 - 1 = 0.$$
  上式各项均为非负实数且系数 $\frac{1}{2^n} > 0$，级数和为 $0$ 迫使每一项均为零，即
  $$1 - x_n = 0 \implies x_n = 1 \quad (\forall n \ge 1).$$
  因此 $x = (1, 1, 1, \ldots)$。
  然而常数序列 $(1, 1, 1, \ldots) \notin c_0$（其极限为 $1 \ne 0$）。
  矛盾！因此在 $c_0$ 中不存在范数 $\le 1$ 的精确匹配元，$\varepsilon = 0$ 不可取。

---

#### 3. 为何该有限匹配不能替代 S5 的条件

1. **局部逼近元依赖于子空间 vs. 全局单一实现元**：
   有限匹配仅保证对**每一个单独的**有限维子空间 $F$ 和误差 $\varepsilon > 0$，存在一个与之依赖的匹配元 $x_{F,\varepsilon} \in E$。
   但随着观测子空间 $F$ 扩大，这些 $x_{F,\varepsilon}$ 在 $E$ 中构成的网 $(x_{F,\varepsilon})$ 通常无法保持不变，更不保证收敛到 $E$ 中的某个固定元；而 S5 寻求的是**单一且同时满足所有对偶泛函观测**的全局实现元 $x \in E$。
2. **非自反空间中弱紧性的缺失（拓扑障碍）**：
   由 Goldstine 定理，闭球 $J(B_E(0, C))$ 在 $E''$ 的弱星拓扑 $\sigma(E'', E')$ 中是稠密的。因此对**任意**合法记录（即任意 $z_\lambda \in E''$），上述有限匹配元网络 $J(x_{F,\varepsilon})$ 总是能在 $E''$ 中弱星收敛到 $z_\lambda$。
   然而，由 Kakutani 定理，$B_E(0, C)$ 在弱拓扑 $\sigma(E, E')$ 下紧当且仅当 $E$ 自反。当 $E$ 非自反时，网络 $(x_{F,\varepsilon})$ 的弱聚点可以完全脱离 $J(E)$，逃逸至 $E'' \setminus J(E)$ 中。
3. **有限匹配不具判别能力**：
   有限匹配性质是**所有**对偶元 $z_\lambda \in E''$ 的通性，无论 $z_\lambda$ 是否能被原空间实现，有限匹配均恒成立；
   而原空间全局实现性严格等价于 $z_\lambda \in J(E)$。
   因此，恒成立的有限匹配根本无法区分“可在 $E$ 中实现的记录”与“只能在 $E'' \setminus J(E)$ 中实现的记录”，无法取代 S5 中关于 $z_\lambda$ 的弱星连续性判据。
