# 线性记录、有限观测与原空间恢复

---

## S1　记录的完整载体

### 1. 兼容有界记录与 $E''$ 的等距双向构造

记所有兼容有界记录构成的空间为 $\mathcal{R}(E)$。其元素为记录族 $\lambda = (\lambda_F)_{F\in\mathcal{F}(E')}$，其中 $\mathcal{F}(E')$ 为 $E'$ 的所有有限维线性子空间按包含关系构成的有向集。

#### (1) 正向构造 $\Phi: \mathcal{R}(E) \to E''$
对任意合法记录 $\lambda \in \mathcal{R}(E)$，定义映射 $z_\lambda: E' \to \mathbb{R}$：
对任意 $\varphi \in E'$，取 1 维子空间 $\mathbb{R}\varphi \in \mathcal{F}(E')$，定义
$$z_\lambda(\varphi) := \lambda_{\mathbb{R}\varphi}(\varphi).$$

- **线性性**：任取 $\varphi_1, \varphi_2 \in E'$ 及 $\alpha, \beta \in \mathbb{R}$。令有限维子空间 $F = \mathrm{span}\{\varphi_1, \varphi_2\} \in \mathcal{F}(E')$。
  由于 $\mathbb{R}\varphi_1 \subset F$、$\mathbb{R}\varphi_2 \subset F$ 且 $\mathbb{R}(\alpha\varphi_1 + \beta\varphi_2) \subset F$，由记录族的兼容性条件 $\lambda_G|_F = \lambda_F$，有：
  $$z_\lambda(\varphi_1) = \lambda_F(\varphi_1),\quad z_\lambda(\varphi_2) = \lambda_F(\varphi_2),\quad z_\lambda(\alpha\varphi_1 + \beta\varphi_2) = \lambda_F(\alpha\varphi_1 + \beta\varphi_2).$$
  又因 $\lambda_F: F \to \mathbb{R}$ 是线性映射，得：
  $$z_\lambda(\alpha\varphi_1 + \beta\varphi_2) = \lambda_F(\alpha\varphi_1 + \beta\varphi_2) = \alpha \lambda_F(\varphi_1) + \beta \lambda_F(\varphi_2) = \alpha z_\lambda(\varphi_1) + \beta z_\lambda(\varphi_2).$$
  因此 $z_\lambda$ 是 $E'$ 上的线性泛函。

- **有界性**：由记录族的统一界条件，对任意 $\varphi \in E'$，
  $$|z_\lambda(\varphi)| = |\lambda_{\mathbb{R}\varphi}(\varphi)| \le C\|\varphi\|.$$
  故 $z_\lambda$ 在 $E'$ 上有界连续，即 $z_\lambda \in E''$，且 $\|z_\lambda\|_{E''} \le C$。令 $\Phi(\lambda) = z_\lambda$。

#### (2) 逆向构造 $\Psi: E'' \to \mathcal{R}(E)$
对任意 $z \in E''$ 及任意 $F \in \mathcal{F}(E')$，定义线性映射 $\lambda_F: F \to \mathbb{R}$ 为 $z$ 在 $F$ 上的限制：
$$\lambda_F := z|_F.$$

- **线性性与兼容性**：$z$ 线性显然蕴含 $\lambda_F$ 线性；若 $F \subset G$，则 $\lambda_G|_F = (z|_G)|_F = z|_F = \lambda_F$。
- **有界性**：对任意 $\varphi \in F$，$|\lambda_F(\varphi)| = |z(\varphi)| \le \|z\|_{E''}\|\varphi\|$，故统一常数可取 $C = \|z\|_{E''} < \infty$。

#### (3) 互逆性与等距性
- **互为逆映射**：
  - 对 $\lambda \in \mathcal{R}(E)$，$(\Psi(\Phi(\lambda)))_F(\varphi) = z_\lambda(\varphi) = \lambda_{\mathbb{R}\varphi}(\varphi) = \lambda_F(\varphi)$（因 $\mathbb{R}\varphi \subset F$），故 $\Psi(\Phi(\lambda)) = \lambda$。
  - 对 $z \in E''$，$\Phi(\Psi(z))(\varphi) = (\Psi(z))_{\mathbb{R}\varphi}(\varphi) = z(\varphi)$，故 $\Phi(\Psi(z)) = z$。
- **等距性**：对任意两份记录 $\lambda, \mu \in \mathcal{R}(E)$，
  $$d(\lambda, \mu) = \sup_{\|\varphi\|\le 1} |\lambda_{\mathbb{R}\varphi}(\varphi) - \mu_{\mathbb{R}\varphi}(\varphi)| = \sup_{\|\varphi\|\le 1} |z_\lambda(\varphi) - z_\mu(\varphi)| = \|z_\lambda - z_\mu\|_{E''}.$$
  因此，$\Phi$ 将 $(\mathcal{R}(E), d)$ 等距同构识别为赋范空间 $(E'', \|\cdot\|_{E''})$。

---

### 2. 规范嵌入 $J: E \to E''$ 为线性等距

规范嵌入 $J: E \to E''$ 定义为 $(Jx)(\varphi) = \varphi(x)$（$\forall x \in E, \varphi \in E'$）。
- **线性性**：对任意 $x, y \in E$ 及 $\alpha, \beta \in \mathbb{R}$，对任意 $\varphi \in E'$ 有
  $$(J(\alpha x + \beta y))(\varphi) = \varphi(\alpha x + \beta y) = \alpha \varphi(x) + \beta \varphi(y) = (\alpha Jx + \beta Jy)(\varphi),$$
  故 $J(\alpha x + \beta y) = \alpha Jx + \beta Jy$。
- **等距性**：
  一方面，对任意 $\|\varphi\|\le 1$，由对偶范数定义 $|(Jx)(\varphi)| = |\varphi(x)| \le \|\varphi\|\|x\| \le \|x\|$，两边取上确界得 $\|Jx\|_{E''} \le \|x\|$。
  另一方面，若 $x = 0$，显然 $\|J0\| = 0 = \|0\|$；若 $x \ne 0$，由 Hahn-Banach 定理的推论（实赋范空间中非零向量可被对偶泛函保范分离），存在 $\varphi_0 \in E'$ 满足 $\|\varphi_0\| = 1$ 且 $\varphi_0(x) = \|x\|$。因此
  $$\|Jx\|_{E''} = \sup_{\|\varphi\|\le 1}|\varphi(x)| \ge \varphi_0(x) = \|x\|.$$
  结合两式得 $\|Jx\|_{E''} = \|x\|$，故 $J$ 为线性等距算子。

---

### 3. 记录变换 $\lambda \mapsto \lambda^T$ 在该识别下恰为 $T''$

对有界线性算子 $T: E \to E$，其共轭算子 $T': E' \to E'$ 满足 $(T'\varphi)(x) = \varphi(Tx)$，二次共轭算子 $T'': E'' \to E''$ 满足 $(T'' z)(\varphi) = z(T'\varphi)$。
对任意记录 $\lambda \in \mathcal{R}(E)$，考虑变换后的记录 $\lambda^T$。其对应的泛函 $z_{\lambda^T} = \Phi(\lambda^T)$ 在任意 $\varphi \in E'$ 处的作用为：
$$z_{\lambda^T}(\varphi) = \lambda^T_{\mathbb{R}\varphi}(\varphi) = \lambda_{T'(\mathbb{R}\varphi)}(T'\varphi).$$
注意到 $T'(\mathbb{R}\varphi) = \mathbb{R}(T'\varphi)$（当 $T'\varphi = 0$ 时为 $\{0\}$）。由正向构造的定义及相容性：
$$\lambda_{\mathbb{R}(T'\varphi)}(T'\varphi) = z_\lambda(T'\varphi).$$
再由二次共轭算子 $T''$ 的定义：
$$z_\lambda(T'\varphi) = (T'' z_\lambda)(\varphi).$$
由于上述等式对所有 $\varphi \in E'$ 均成立，故
$$\Phi(\lambda^T) = z_{\lambda^T} = T'' z_\lambda = T''(\Phi(\lambda)).$$
即变换 $\lambda \mapsto \lambda^T$ 在等距识别 $\Phi$ 下恰为 $T''$。

---

## S2　可恢复记录的稳定性

### 1. 唯一原空间恢复 $x_\lambda$ 的构造与算子相容性

设 $E$ 自反，此时规范等距嵌入 $J: E \to E''$ 为满射，因而 $J$ 为等距同构，存在连续逆算子 $J^{-1}: E'' \to E$。

- **恢复元构造**：对任意合法记录 $\lambda$，由 S1 得到其唯一对应的 $z_\lambda \in E''$。定义
  $$x_\lambda := J^{-1}(z_\lambda) \in E.$$
  此恢复元满足：对任意 $\varphi \in E'$，
  $$\varphi(x_\lambda) = (J x_\lambda)(\varphi) = z_\lambda(\varphi) = \lambda_{\mathbb{R}\varphi}(\varphi).$$
  因此对任意包含有限观测组的 $F$，$\varphi(x_\lambda) = \lambda_F(\varphi)$，完全精确实现了记录 $\lambda$。

- **唯一性**：若另有 $\tilde{x} \in E$ 实现该记录，则对所有 $\varphi \in E'$ 有 $\varphi(x_\lambda - \tilde{x}) = 0$。由 Hahn-Banach 定理（或 $J$ 的单射性），$x_\lambda - \tilde{x} = 0$，即 $x_\lambda = \tilde{x}$，恢复元唯一。

- **与算子 $T$ 的相容性**：需证 $x_{\lambda^T} = T x_\lambda$。
  首先验证对任意 $x \in E$，有典范关系 $T'' J x = J(Tx)$：
  对任意 $\varphi \in E'$，
  $$(T'' J x)(\varphi) = (Jx)(T'\varphi) = (T'\varphi)(x) = \varphi(Tx) = (J(Tx))(\varphi),$$
  故 $T'' J = J T$。
  将 $x = x_\lambda$ 代入，由 S1 知 $z_{\lambda^T} = T'' z_\lambda = T'' J x_\lambda = J(Tx_\lambda)$。
  两端作用 $J^{-1}$ 即得：
  $$x_{\lambda^T} = J^{-1}(z_{\lambda^T}) = T x_\lambda.$$
  相容性得证。

---

### 2. 稳定性不等式的证明

需证：对任意有界线性算子 $T, U: E \to E$ 及记录 $\lambda, \mu$，
$$\|x_{\lambda^T} - x_{\mu^U}\| \le \|T\| d(\lambda, \mu) + \|T - U\| \|x_\mu\|.$$

**证明**：
利用算子相容性 $x_{\lambda^T} = T x_\lambda$ 与 $x_{\mu^U} = U x_\mu$，可作分解：
$$x_{\lambda^T} - x_{\mu^U} = T x_\lambda - U x_\mu = T(x_\lambda - x_\mu) + (T - U)x_\mu.$$
由范数的三角不等式及算子范数的次乘性：
$$\|x_{\lambda^T} - x_{\mu^U}\| \le \|T(x_\lambda - x_\mu)\| + \|(T - U)x_\mu\| \le \|T\| \|x_\lambda - x_\mu\| + \|T - U\| \|x_\mu\|.$$
由于规范嵌入 $J: E \to E''$ 为等距映射，且由 S1 的等距识别：
$$\|x_\lambda - x_\mu\|_E = \|J(x_\lambda - x_\mu)\|_{E''} = \|z_\lambda - z_\mu\|_{E''} = d(\lambda, \mu).$$
将 $\|x_\lambda - x_\mu\| = d(\lambda, \mu)$ 代入上式，立即得到：
$$\|x_{\lambda^T} - x_{\mu^U}\| \le \|T\| d(\lambda, \mu) + \|T - U\| \|x_\mu\|.$$
证毕。

---

## S3　子空间约束

在 S2 条件下（$E$ 自反，记录由 $x_\lambda \in E$ 唯一实现，$z_\lambda = J x_\lambda$），令 $Y \subset E$ 为闭线性子空间，$Y^\perp = \{\varphi \in E': \varphi|_Y = 0\}$ 为其零化子空间。

### 1. 证明 $x_\lambda \in Y \iff z_\lambda|_{Y^\perp} = 0$

- **必要性 ($\implies$)**：
  若 $x_\lambda \in Y$，则对任意 $\varphi \in Y^\perp$，根据 $Y^\perp$ 的定义，$\varphi|_Y = 0$，特别地 $\varphi(x_\lambda) = 0$。
  由 $z_\lambda = J x_\lambda$，有 $z_\lambda(\varphi) = \varphi(x_\lambda) = 0$。因此 $z_\lambda|_{Y^\perp} = 0$。

- **充分性 ($\impliedby$)**：
  假设 $z_\lambda|_{Y^\perp} = 0$，即对一切 $\varphi \in Y^\perp$ 均有 $\varphi(x_\lambda) = z_\lambda(\varphi) = 0$。
  若 $x_\lambda \notin Y$，由于 $Y$ 是赋范空间 $E$ 的闭线性子空间，由 Hahn-Banach 几何分离定理（点与闭子空间的分离推论），存在连续线性泛函 $\varphi_0 \in E'$ 满足：
  $$\varphi_0|_Y = 0 \quad (\text{即 } \varphi_0 \in Y^\perp) \quad \text{且} \quad \varphi_0(x_\lambda) = \mathrm{dist}(x_\lambda, Y) > 0.$$
  这与 $\varphi_0(x_\lambda) = z_\lambda(\varphi_0) = 0$ 产生矛盾。
  因此必有 $x_\lambda \in Y$。

---

### 2. 从记录给出 $\mathrm{dist}(x_\lambda, Y)$ 的准确对偶公式

**对偶公式**：
$$\mathrm{dist}(x_\lambda, Y) = \max_{\substack{\varphi \in Y^\perp \\ \|\varphi\|\le 1}} |\lambda_{\mathbb{R}\varphi}(\varphi)| = \sup_{\substack{\varphi \in Y^\perp \\ \|\varphi\|\le 1}} |\lambda_{\mathbb{R}\varphi}(\varphi)|.$$

**推导与论证**：
1. **上界估计**：
   任取 $y \in Y$ 及任意满足 $\|\varphi\|\le 1$ 的 $\varphi \in Y^\perp$。由于 $\varphi(y) = 0$，由记录实现性质有：
   $$|\lambda_{\mathbb{R}\varphi}(\varphi)| = |z_\lambda(\varphi)| = |\varphi(x_\lambda)| = |\varphi(x_\lambda - y)| \le \|\varphi\| \|x_\lambda - y\| \le \|x_\lambda - y\|.$$
   由于该式对所有 $y \in Y$ 均成立，对右端关于 $y \in Y$ 取下确界，得：
   $$|\lambda_{\mathbb{R}\varphi}(\varphi)| \le \inf_{y \in Y} \|x_\lambda - y\| = \mathrm{dist}(x_\lambda, Y).$$
   两端关于 $\varphi \in Y^\perp, \|\varphi\|\le 1$ 取上确界，即得：
   $$\sup_{\substack{\varphi \in Y^\perp \\ \|\varphi\|\le 1}} |\lambda_{\mathbb{R}\varphi}(\varphi)| \le \mathrm{dist}(x_\lambda, Y).$$

2. **下界与可达性**：
   若 $\mathrm{dist}(x_\lambda, Y) = 0$，由上述不等式非负性即得上确界为 0，公式成立。
   若 $d := \mathrm{dist}(x_\lambda, Y) > 0$：
   考虑有限维扩张子空间 $Y_0 = Y \oplus \mathbb{R} x_\lambda$。在其上定义线性泛函 $f: Y_0 \to \mathbb{R}$：
   $$f(y + t x_\lambda) := t d \qquad (y \in Y, t \in \mathbb{R}).$$
   - 显然 $f|_Y = 0$ 且 $f(x_\lambda) = d$。
   - 验证 $f$ 在 $Y_0$ 上的范数：对任意 $t \ne 0$ 和 $y \in Y$，
     $$|f(y + t x_\lambda)| = |t| d = |t| \mathrm{dist}(x_\lambda, Y) \le |t| \left\|x_\lambda - \left(-\frac{y}{t}\right)\right\| = \|y + t x_\lambda\|.$$
     因此 $\|f\|_{Y_0^*} \le 1$（且在逼近序列上显然取到 1，故 $\|f\| = 1$）。
   由 Hahn-Banach 延拓定理，存在 $\varphi_0 \in E'$ 满足 $\varphi_0|_{Y_0} = f$ 且 $\|\varphi_0\|_{E'} = \|f\| = 1$。
   此时 $\varphi_0|_Y = f|_Y = 0$，故 $\varphi_0 \in Y^\perp$ 且 $\|\varphi_0\| \le 1$；同时：
   $$\lambda_{\mathbb{R}\varphi_0}(\varphi_0) = z_\lambda(\varphi_0) = \varphi_0(x_\lambda) = f(x_\lambda) = d = \mathrm{dist}(x_\lambda, Y).$$
   这表明上确界不仅等于 $\mathrm{dist}(x_\lambda, Y)$，而且在 $\varphi_0$ 处精确达到最大值。

---

## S4　一般Banach空间

### 1. 明确结论
**结论：否。** 在一般实 Banach 空间共同设定下，并非每份合法记录都能在原空间 $E$ 中实现。

---

### 2. 论证与完整核验反例

#### (1) 机制论证
由 S1 可知，每一份合法记录族 $\lambda \in \mathcal{R}(E)$ 与二次对偶空间 $E''$ 中的有界线性泛函 $z_\lambda$ 之间存在一一等距对应。
若存在 $x_\lambda \in E$ 实现全部记录，则必满足对所有 $\varphi \in E'$，$(J x_\lambda)(\varphi) = \varphi(x_\lambda) = z_\lambda(\varphi)$，即 $J x_\lambda = z_\lambda$。
因此，全部合法记录可恢复的充要条件是规范嵌入 $J: E \to E''$ 为满射，即 $E$ 必须为**自反空间**。一旦 $E$ 非自反，$J(E) \subsetneq E''$，则任何对应于 $z \in E'' \setminus J(E)$ 的合法记录均无法在原空间中实现。

#### (2) 完整核验反例
- **空间设定**：取典型的非自反实 Banach 空间 $E = c_0$（赋以范数 $\|x\|_\infty = \sup_{n\ge1}|x_n|$）。
  其连续对偶空间为 $E' = \ell^1$（范数 $\|\varphi\|_1 = \sum_{n=1}^\infty |\varphi_n|$），二次对偶空间为 $E'' = \ell^\infty$。规范嵌入 $J: c_0 \to \ell^\infty$ 为自然包含映射。
- **记录构造**：取 $z = (1, 1, 1, \ldots) \in \ell^\infty = E''$，显然 $\|z\|_{\ell^\infty} = 1$。
  对应地，对每个有限维子空间 $F \subset \ell^1$，定义
  $$\lambda_F(\varphi) := \sum_{n=1}^\infty \varphi_n \qquad (\varphi = (\varphi_n)_{n=1}^\infty \in F).$$
- **合法记录条件核验**：
  1. *线性性*：由于级数绝对收敛且求和为线性运算，$\lambda_F$ 为 $F$ 上的线性映射。
  2. *兼容性*：若 $F \subset G$，两者的求和定义完全一致，故 $\lambda_G|_F = \lambda_F$。
  3. *统一有界性*：对任意 $\varphi \in F$，
     $$|\lambda_F(\varphi)| = \left|\sum_{n=1}^\infty \varphi_n\right| \le \sum_{n=1}^\infty |\varphi_n| = \|\varphi\|_1.$$
     因此存在统一界 $C = 1 < \infty$。记录 $\lambda$ 合法。
- **不可实现性证明**：
  假设存在 $x = (x_n)_{n=1}^\infty \in c_0$ 实现该记录。
  对每个 $k \in \mathbb{N}$，取 $\ell^1$ 中的标准单位基向量 $e_k = (0,\ldots, 0, 1, 0, \ldots)$（第 $k$ 位为 1）。
  则 $e_k \in \ell^1$，按实现要求：
  $$x_k = e_k(x) = \lambda_{\mathbb{R} e_k}(e_k) = \sum_{n=1}^\infty (e_k)_n = 1.$$
  由此推得对所有 $k \ge 1$，均有 $x_k = 1$。
  但这导致 $\lim_{k\to\infty} x_k = 1 \ne 0$，与 $x \in c_0$ 矛盾！
  因此，原空间 $c_0$ 中不存在任何元素能够实现该记录。

---

## S5　单条记录的拓扑条件

### 1. 明确结论
**结论：是。** 若 $z_\lambda: E' \to \mathbb{R}$ 关于弱星拓扑 $\sigma(E', E)$ 连续，则该记录必可在 $E$ 中唯一实现。

---

### 2. 弱星连续性与原空间可实现性的充要关系定理

**充要关系**：
设 $E$ 为任意实 Banach 空间，$\lambda$ 为合法记录，$z_\lambda \in E''$ 为其在 S1 中的载体。则：
$$\lambda \text{ 在 } E \text{ 中可由某点 } x_\lambda \text{ 实现} \iff z_\lambda: E' \to \mathbb{R} \text{ 关于弱星拓扑 } \sigma(E', E) \text{ 连续}.$$
且此时实现元 $x_\lambda \in E$ 唯一，满足 $\|x_\lambda\|_E = \|z_\lambda\|_{E''} \le C$。

---

### 3. 完整论证

#### (1) 必要性 ($\implies$)
若 $\lambda$ 在 $E$ 中可实现，即存在 $x \in E$，使得对一切 $\varphi \in E'$ 有 $z_\lambda(\varphi) = \varphi(x) = (Jx)(\varphi)$。
根据弱星拓扑 $\sigma(E', E)$ 的定义，它是使族 $\{\mathrm{ev}_y: \varphi \mapsto \varphi(y) \mid y \in E\}$ 中所有单点赋值泛函均连续的最粗（弱）拓扑。
由于 $z_\lambda = \mathrm{ev}_x$，它作为拓扑生成元之一，按定义关于 $\sigma(E', E)$ 连续。

#### (2) 充分性 ($\impliedby$)
假设线性泛函 $z_\lambda: E' \to \mathbb{R}$ 关于弱星拓扑 $\sigma(E', E)$ 连续。
由于 $z_\lambda(0) = 0$ 且 $z_\lambda$ 在原点处连续，区间 $(-1, 1) \subset \mathbb{R}$ 的原像
$$U := z_\lambda^{-1}((-1, 1)) = \{\varphi \in E': |z_\lambda(\varphi)| < 1\}$$
是 $(E', \sigma(E', E))$ 中包含原点 0 的开邻域。
由局部凸空间弱拓扑的基邻域定义，存在有限个点 $x_1, \ldots, x_m \in E$ 及 $\varepsilon > 0$，使得弱星基本开邻域
$$V := \{\varphi \in E': |\varphi(x_i)| < \varepsilon, \, i = 1, \ldots, m\} \subset U.$$

考虑子空间 $N := \bigcap_{i=1}^m \ker(Jx_i) = \{\varphi \in E': \varphi(x_i) = 0, \, i = 1, \ldots, m\}$。
对任意 $\varphi \in N$ 及任意标量 $t \in \mathbb{R}$，均有 $(t\varphi)(x_i) = t \cdot 0 = 0 < \varepsilon$（$i=1,\ldots,m$），故 $t\varphi \in V \subset U$。
按 $U$ 的定义，这意味着：
$$|z_\lambda(t\varphi)| = |t| |z_\lambda(\varphi)| < 1 \qquad (\forall t \in \mathbb{R}).$$
由于 $|t|$ 可以任意大，该式成立当且仅当 $z_\lambda(\varphi) = 0$。
由此证明了：
$$\bigcap_{i=1}^m \ker(Jx_i) \subset \ker(z_\lambda).$$

根据线性代数经典引理（若一组线性泛函的核的交包含在另一线性泛函的核中，则后者必为前者的线性组合）：
存在实常数 $c_1, \ldots, c_m \in \mathbb{R}$，使得
$$z_\lambda = \sum_{i=1}^m c_i J(x_i) = J\left(\sum_{i=1}^m c_i x_i\right).$$
令 $x_\lambda := \sum_{i=1}^m c_i x_i \in E$。则有 $z_\lambda = J x_\lambda$，即对一切 $\varphi \in E'$，
$$\lambda_{\mathbb{R}\varphi}(\varphi) = z_\lambda(\varphi) = \varphi(x_\lambda).$$
记录在原空间 $E$ 中被 $x_\lambda$ 成功实现。

#### (3) 唯一性与范数界
若另有 $\tilde{x} \in E$ 实现记录，则 $J(x_\lambda - \tilde{x}) = 0$。由 S1 中 $J$ 的等距性，$\|x_\lambda - \tilde{x}\|_E = \|J(x_\lambda - \tilde{x})\|_{E''} = 0$，故 $x_\lambda = \tilde{x}$ 唯一。
范数满足 $\|x_\lambda\|_E = \|Jx_\lambda\|_{E''} = \|z_\lambda\|_{E''} \le C$。

---

## S6　有限观测的精确匹配

### 1. 存在 $x_{F,\varepsilon}$ 满足 $q_F x_{F,\varepsilon} = \lambda_F$ 且 $\|x_{F,\varepsilon}\| \le C + \varepsilon$ 的证明

设 $F \subset E'$ 为有限维线性子空间，$\dim F = m < \infty$。
限制映射 $\lambda_F: F \to \mathbb{R}$ 是有限维赋范空间 $F$（其范数继承自 $E'$）上的连续线性泛函，即 $\lambda_F \in F^*$。
其对偶范数满足
$$\|\lambda_F\|_{F^*} = \sup_{\varphi \in F, \|\varphi\|_{E'}\le 1} |\lambda_F(\varphi)| \le C.$$
映射 $q_F: E \to F^*$ 定义为 $(q_F x)(\varphi) = \varphi(x)$。

#### 第一步：证明 $q_F$ 为满射
考虑共轭算子 $q_F^*: (F^*)^* \cong F \to E'$。对任意 $\varphi \in F$ 及 $x \in E$，
$$\langle q_F^* \varphi, x \rangle = \langle \varphi, q_F x \rangle = (q_F x)(\varphi) = \varphi(x).$$
故 $q_F^*(\varphi) = \varphi \in E'$。
若 $q_F^*(\varphi) = 0$，则说明 $\varphi$ 作为 $E'$ 中的泛函是零泛函，因此 $\ker(q_F^*) = \{0\}$。
在有限维对偶下，单射的共轭算子蕴含原算子 $q_F$ 的像 $\mathrm{Im}(q_F)$ 在 $F^*$ 中稠密；又因 $F^*$ 有限维，所有子空间皆闭，故 $q_F(E) = F^*$ 为满射。

#### 第二步：利用凸集分离定理证明 $\lambda_F \in \overline{q_F(B_C(E))}$
记闭球 $B_C(E) = \{x \in E: \|x\|\le C\}$。其像 $q_F(B_C(E))$ 是有限维空间 $F^*$ 中的凸集。
假设 $\lambda_F \notin \overline{q_F(B_C(E))}$。
由有限维空间中的严格分离定理，存在非零向量 $\xi \in (F^*)^* \cong F$，使得
$$\lambda_F(\xi) > \sup_{w \in q_F(B_C(E))} w(\xi) = \sup_{\|x\|_E \le C} (q_F x)(\xi) = \sup_{\|x\|_E \le C} \xi(x) = C \|\xi\|_{E'}.$$
然而，根据题设中 $\lambda$ 的统一界条件，$\xi \in F$ 必然满足：
$$\lambda_F(\xi) \le C \|\xi\|_{E'}.$$
两式矛盾！因此必有
$$\lambda_F \in \overline{q_F(B_C(E))}.$$

#### 第三步：消除闭包得到 $B_{C+\varepsilon}(E)$ 中的精确匹配元
任给 $\varepsilon > 0$。根据第一步，$q_F: E \to F^*$ 是 Banach 空间到有限维空间的满射有界线性算子，由开映射定理，$q_F$ 是开映射。
特别地，$q_F(B_\varepsilon^\circ(E))$ 包含 $F^*$ 中原点的一个开邻域 $W$。
由于 $\lambda_F \in \overline{q_F(B_C(E))}$，开邻域 $\lambda_F - W$ 必与 $q_F(B_C(E))$ 相交，即存在 $y \in B_C(E)$ 和 $w \in W$，使得
$$\lambda_F - w = q_F(y) \implies \lambda_F = q_F(y) + w.$$
因为 $w \in W \subset q_F(B_\varepsilon(E))$，存在 $h \in E$，$\|h\| < \varepsilon$，使得 $q_F(h) = w$。
令 $x_{F,\varepsilon} := y + h \in E$。则：
$$q_F(x_{F,\varepsilon}) = q_F(y) + q_F(h) = \lambda_F,$$
且由三角不等式：
$$\|x_{F,\varepsilon}\| \le \|y\| + \|h\| \le C + \varepsilon.$$
命题得证。

---

### 2. 判断是否总可取 $\varepsilon = 0$

**结论：否，不总可取 $\varepsilon = 0$。**

**反例与完整核验**：
- **空间设定**：取 $E = c_0$（赋范数 $\|\cdot\|_\infty$），对偶为 $E' = \ell^1$。
- **泛函选取**：构造泛函 $\varphi \in \ell^1$ 为
  $$\varphi := \left(\frac{1}{2}, \frac{1}{4}, \frac{1}{8}, \ldots, \frac{1}{2^n}, \ldots\right).$$
  其范数为 $\|\varphi\|_1 = \sum_{n=1}^\infty \frac{1}{2^n} = 1$。
- **子空间与记录定义**：
  令 1 维子空间 $F = \mathbb{R}\varphi \subset \ell^1$。
  定义 $\lambda_F(t\varphi) := t$（$t \in \mathbb{R}$）。
  对任意 $t \in \mathbb{R}$，有 $|\lambda_F(t\varphi)| = |t| = \|t\varphi\|_1$，故统一界常数可取 $C = 1$。
- **核验 $\varepsilon = 0$ 不可取**：
  若能取 $\varepsilon = 0$，则存在 $x \in c_0$，满足 $\|x\|_\infty \le C = 1$，且 $q_F x = \lambda_F$。
  即必须满足：
  $$\varphi(x) = \sum_{n=1}^\infty \frac{1}{2^n} x_n = \lambda_F(\varphi) = 1.$$
  由于 $\|x\|_\infty \le 1$，对每个 $n \ge 1$ 均有 $x_n \le 1$，即 $1 - x_n \ge 0$。考虑级数：
  $$\sum_{n=1}^\infty \frac{1}{2^n}(1 - x_n) = \sum_{n=1}^\infty \frac{1}{2^n} - \sum_{n=1}^\infty \frac{1}{2^n} x_n = 1 - 1 = 0.$$
  由于各项均为非负实数，级数和为 0 迫使每一项均为 0：
  $$\frac{1}{2^n}(1 - x_n) = 0 \implies x_n = 1 \qquad (\forall n \ge 1).$$
  因此 $x = (1, 1, 1, \ldots)$。
  然而 $\lim_{n\to\infty} x_n = 1 \ne 0$，故 $(1, 1, 1, \ldots) \notin c_0$。
  产生矛盾，说明不存在任何满足 $\|x\|_\infty \le 1$ 的 $x \in c_0$ 能够精确匹配。必须取 $\varepsilon > 0$。

---

### 3. 为何该有限匹配不能替代 S5 的条件

有限维匹配性质之所以无法替代 S5 的弱星连续性条件，其本质原因在于**局部逼近能力与全局拓扑收敛性之间的断裂**：

1. **有限匹配是所有有界记录的普遍通性，缺乏对可恢复性的甄别能力**：
   根据局部自反性原理（Principle of Local Reflexivity）以及 Goldstine 定理，Banach 空间的闭单位球在二次对偶空间 $E''$ 的闭单位球中弱星稠密。因此，**对任何 Banach 空间中的任何合法记录（即 $E''$ 中的任意泛函 $z_\lambda$）**，无论其能否在原空间中实现，上述有限维精确匹配（在 $\varepsilon>0$ 容限下）**永远全部成立**！
   例如在 S4 中完全无法在 $c_0$ 中恢复的记录，对任意有限维 $F$ 均能被有限匹配。这表明有限维匹配是所有合法记录共同具有的局部性质，根本无法区分“可在 $E$ 中实现的记录”与“不可在 $E$ 中实现的记录”。

2. **逼近族的参数依赖性与原空间的非紧性**：
   在有限匹配中，匹配点 $x_{F,\varepsilon}$ 高度依赖于子空间 $F$ 和误差 $\varepsilon$。当 $F$ 沿着有向集 $\mathcal{F}(E')$ 扩张且 $\varepsilon \to 0$ 时，族 $\{x_{F,\varepsilon}\}$ 构成 $E$ 中的一个网（net）。
   在非自反空间中，原空间闭球 $B_{C+\varepsilon}(E)$ 缺乏弱紧性，该网在 $E$ 中通常不存在任何弱极限点。

3. **双对偶极限的宿主判定依赖 S5**：
   将该网放入二次对偶 $E''$ 中，由 Banach-Alaoglu 定理，$E''$ 的闭球是弱星紧的，该网在 $E''$ 中必然弱星收敛到其唯一的理论极限定界 $z_\lambda$。
   然而，极限定界 $z_\lambda$ 是否落在原空间 $J(E)$ 之中，完全取决于其对弱星拓扑 $\sigma(E', E)$ 的连续性（即 S5 的条件）。
   **简言之：S6 仅说明 $z_\lambda$ 在任意有限维切面上可被原空间任意逼近（这是 $E''$ 泛函的天然属性）；而 S5 才是保证这个逼近的极限不会“逃逸出原空间”的充要拓扑判定。** 因此有限匹配绝不能替代 S5 的条件。
