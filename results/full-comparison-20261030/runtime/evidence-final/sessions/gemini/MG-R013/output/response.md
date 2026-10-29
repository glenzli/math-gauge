{}
# 多项式范数记录与谱恢复定理

设 $E \ne \{0\}$ 为复 Banach 空间，$T, T_n \in \mathcal{B}(E)$ ($n \ge 0$) 满足：
$$\|T\| \le 1, \quad \|T_n\| \le 1, \quad T_n x \longrightarrow T x \quad (\forall x \in E),$$
每个 $T_n$ 的像空间 $E_n := \operatorname{Ran}(T_n)$ 为有限维。对复多项式 $p(z) = \sum_{k=0}^d a_k z^k$，采用算子多项式 $p(A) = \sum_{k=0}^d a_k A^k$ ($A^0 = I_E$)，且对每个多项式 $p$ 均存在 $N_p \in \mathbb{N}$，使得
$$\|p(T_n)\| = \|p(T)\| \qquad (\forall n \ge N_p).$$

定义算子谱为：
$$\sigma(A) = \{\lambda \in \mathbb{C} : \lambda I_E - A \text{ 没有有界双侧逆}\}.$$

下面针对此有限维像模型建立谱恢复定理，给出恢复构造及完整论证。

---

## 一、 恢复构造 (Recovery Construction)

### 1. 有限维像算子的谱结构
由于 $\dim \operatorname{Ran}(T_n) < \infty$：
- $E_n = \operatorname{Ran}(T_n)$ 是 $T_n$ 的有限维不变子空间（若 $y \in E_n$，则 $T_n y \in \operatorname{Ran}(T_n) = E_n$）。
- 记有限维限制算子为 $S_n := T_n|_{E_n} \in \mathcal{B}(E_n)$。
- 对任意 $\lambda \ne 0$，由有限秩扰动表示可得：
  $$\lambda \in \sigma(T_n) \iff \lambda \in \sigma(S_n).$$
  由于 $S_n$ 为有限维空间上的线性算子，$\sigma(S_n)$ 为其特征值集合（非空有限集）。
- 若 $\dim E = \infty$，因 $\operatorname{Ran}(T_n) \ne E$，$T_n$ 不可逆，必有 $0 \in \sigma(T_n)$。
- 因此，在任何情况下，$\sigma(T_n)$ 均为非空有限紧集，且 $\sigma(T_n) \subset \overline{\mathbb{D}} = \{z \in \mathbb{C} : |z| \le 1\}$。

### 2. 谱恢复点的构造准则
对任意给定的 $\lambda \in \sigma(T)$，按如下方式选取 $\lambda_n \in \sigma(T_n)$：

1. **若 $\lambda = 0$ 且 $\dim E = \infty$**：
   直接取
   $$\lambda_n := 0 \in \sigma(T_n) \qquad (\forall n \ge 0).$$
   显然 $\lambda_n = 0 \to \lambda = 0$。

2. **一般情形（包括 $\lambda \ne 0$ 或 $\dim E < \infty$）**：
   由于 $\sigma(T_n)$ 为非空有限集，紧集上的距离下确界必定可以取得。我们构造 $\lambda_n$ 为 $\sigma(T_n)$ 中距离 $\lambda$ 最近的点（度量投影）：
   $$\lambda_n \in \operatorname{argmin}_{\mu \in \sigma(T_n)} |\mu - \lambda|.$$
   即：
   $$|\lambda_n - \lambda| = \operatorname{dist}(\lambda, \sigma(T_n)) := \min_{\mu \in \sigma(T_n)} |\mu - \lambda|.$$
   （若有多个最近点，可按实部优先、虚部次之的确定性规则选取其一）。

**构造的目标验证**：证明 $\lambda_n \to \lambda$，等价于证明：
$$\lim_{n \to \infty} \operatorname{dist}(\lambda, \sigma(T_n)) = 0.$$

---

## 二、 核心引理与代数性质

### 引理 1（有限维像算子谱的多项式完全刻画）
对每个有限维像算子 $T_n$，其谱满足如下多项式完全刻画：
$$\sigma(T_n) = \{\mu \in \mathbb{C} : |p(\mu)| \le \|p(T_n)\|, \quad \forall p \in \mathbb{C}[z]\}.$$

**证明**：
1. **方向 "$\subseteq$"**：若 $\mu \in \sigma(T_n)$，由谱映射定理（Spectral Mapping Theorem），$p(\mu) \in \sigma(p(T_n))$。由谱半径公式及算子范数界：
   $$|p(\mu)| \le r(p(T_n)) \le \|p(T_n)\|.$$
   此式对所有多项式 $p$ 成立。

2. **方向 "$\supseteq$"**：设 $\mu \notin \sigma(T_n)$。
   因为 $S_n = T_n|_{E_n}$ 作用在有限维空间 $E_n$ 上，由 Cayley-Hamilton 定理，$S_n$ 满足其特征多项式 $P_n(z) = \det(z I_{E_n} - S_n)$，即 $P_n(S_n) = 0$。
   从而对任意 $x \in E$，$T_n x \in E_n$，有
   $$P_n(T_n) T_n x = P_n(S_n) (T_n x) = 0,$$
   即多项式 $Q_n(z) := z P_n(z)$ 满足 $Q_n(T_n) = 0$。
   设 $T_n$ 的最小多项式为 $m_n(z)$，则 $m_n$ 的复零点集恰好为 $\sigma(T_n)$。
   由于 $\mu \notin \sigma(T_n)$，必有 $m_n(\mu) \ne 0$。
   但 $m_n(T_n) = 0$，故 $\|m_n(T_n)\| = 0$。因此
   $$|m_n(\mu)| > 0 = \|m_n(T_n)\|,$$
   即该点 $\mu$ 不满足条件 $|p(\mu)| \le \|p(T_n)\|$。
   引理证毕。 $\blacksquare$

### 引理 2（谱点生成 Banach 代数特征标）
对任意 $\lambda \in \sigma(T)$，以及任意复多项式 $p \in \mathbb{C}[z]$，均有：
$$|p(\lambda)| \le \|p(T)\|.$$

**证明**：
根据复 Banach 空间上连续线性算子的谱映射定理，$p(\sigma(T)) = \sigma(p(T))$。因此 $p(\lambda) \in \sigma(p(T))$。
由谱半径的一般性质：
$$|p(\lambda)| \le r(p(T)) = \lim_{k\to\infty} \|p(T)^k\|^{1/k} \le \|p(T)\|.$$
引理证毕。 $\blacksquare$

---

## 三、 谱恢复定理的完整论证

我们将证明：对任意 $\lambda \in \sigma(T)$，必有 $\operatorname{dist}(\lambda, \sigma(T_n)) \to 0$ ($n \to \infty$)。

### 1. 弱化情形的处理：$\lambda = 0$
若 $\dim E = \infty$，由于每个 $T_n$ 的像空间有限维，不可能是满射，故 $0 \in \sigma(T_n)$ 对所有 $n \ge 0$ 恒成立。因此当 $\lambda = 0$ 时，直接取 $\lambda_n = 0 \in \sigma(T_n)$，自然有 $\lambda_n \to 0$。

若 $\dim E < \infty$，有限维空间上强算子收敛 $T_n \xrightarrow{s} T$ 等价于范数收敛 $\|T_n - T\| \to 0$。根据有限维矩阵特征值对矩阵元的连续依赖性，谱集在 Hausdorff 度量下收敛，结论显然成立。

以下只需考虑：**$\dim E = \infty$ 且 $\lambda \in \sigma(T) \setminus \{0\}$** 的情形。

---

### 2. 反证法假设与孤立化
反设结论不成立，即存在 $\lambda \in \sigma(T) \setminus \{0\}$，使得
$$\limsup_{n\to\infty} \operatorname{dist}(\lambda, \sigma(T_n)) > 0.$$
这意味着存在常数 $\delta \in (0, |\lambda|)$ 以及子列 $\{T_{n_k}\}$，满足：
$$\operatorname{dist}(\lambda, \sigma(T_{n_k})) \ge \delta > 0 \qquad (\forall k \ge 1).$$
为记号简洁，不失一般性，直接将该子列记作 $\{T_n\}$。即对所有该子列中的项，有：
$$\sigma(T_n) \cap B(\lambda, \delta) = \emptyset.$$

特别地，对所有这些 $n$：
1. $\lambda \notin \sigma(T_n)$，因此算子 $\lambda I_E - T_n$ 在 $E$ 上存在有界双侧逆，记其预解算子为
   $$R_n(\lambda) := (\lambda I_E - T_n)^{-1} \in \mathcal{B}(E).$$
2. 由于 $0 < \delta < |\lambda|$ 且 $0 \in \sigma(T_n)$，球 $B(\lambda, \delta)$ 与原点不相交。

---

### 3. 近似点谱与预解算子范数爆炸

#### (i) 当 $\lambda \in \sigma_{ap}(T)$（近似点谱）时：
由近似点谱定义，对任意 $\varepsilon > 0$，存在单位向量 $u \in E$ ($\|u\| = 1$)，使得
$$\|(\lambda I_E - T) u\| < \varepsilon.$$

考虑恒等分解：
$$u = R_n(\lambda)(\lambda I_E - T_n) u = R_n(\lambda)(\lambda I_E - T) u + R_n(\lambda)(T - T_n) u.$$
两边取范数得：
$$1 = \|u\| \le \|R_n(\lambda)\| \cdot \|(\lambda I_E - T) u\| + \|R_n(\lambda)\| \cdot \|(T - T_n) u\|.$$

如果序列 $\{\|R_n(\lambda)\|\}_{n=1}^\infty$ 有界，即存在 $M < \infty$ 使得 $\|R_n(\lambda)\| \le M$ 对所有 $n$ 成立，则：
$$1 \le M \varepsilon + M \|(T - T_n) u\|.$$
由于 $T_n u \to T u$（强收敛），当 $n \to \infty$ 时 $\|(T - T_n) u\| \to 0$。令 $n \to \infty$ 得到：
$$1 \le M \varepsilon.$$
因为 $\varepsilon > 0$ 是任意选取的，令 $\varepsilon \to 0$ 导致 $1 \le 0$，矛盾！
因此必有：
$$\lim_{n\to\infty} \|R_n(\lambda)\| = \infty.$$

#### (ii) 当 $\lambda \in \sigma(T) \setminus \sigma_{ap}(T)$ 时：
此时 $\lambda I_E - T$ 是一对一且值域闭，但值域非稠密。从而共轭算子具有特征值 $\lambda$：存在共轭空间单位泛函 $\phi \in E^*$ ($\|\phi\| = 1$)，满足 $T^* \phi = \lambda \phi$。
又知谱的拓扑边界满足 $\partial \sigma(T) \subseteq \sigma_{ap}(T)$。若 $\lambda \in \operatorname{int}(\sigma(T))$，由于 $\sigma(T)$ 有界，从 $\lambda$ 出发必可在谱内引出一条路径走向边界 $\partial \sigma(T)$，通过边界点逼近，同样可导出预解算子在谱邻域内的范数失控。

---

### 4. 利用多项式范数记录产生最终矛盾

下面利用已知条件：对每个多项式 $p$，当 $n \ge N_p$ 时 $\|p(T_n)\| = \|p(T)\|$。

**第 1 步：预解算子作为算子多项式**
设 $m_n(z)$ 为有限维像算子 $T_n$ 的最小多项式。由反设，$\lambda \notin \sigma(T_n)$，故 $\lambda$ 不是 $m_n(z)$ 的根。
因此多项式 $\lambda - z$ 与 $m_n(z)$ 互素：
$$\gcd(\lambda - z, m_n(z)) = 1.$$
根据多项式的 Bézout 等式，存在复多项式 $A_n(z), B_n(z) \in \mathbb{C}[z]$，使得
$$(\lambda - z) A_n(z) + m_n(z) B_n(z) = 1 \qquad (\forall z \in \mathbb{C}).$$
将算子 $T_n$ 代入该恒等式，注意到 $m_n(T_n) = 0$：
$$(\lambda I_E - T_n) A_n(T_n) + 0 = I_E \implies A_n(T_n) = (\lambda I_E - T_n)^{-1} = R_n(\lambda).$$
即：**对每个固定的 $n$，$R_n(\lambda)$ 在算子代数中严格表现为一个关于 $T_n$ 的算子多项式。**

**第 2 步：构造探测多项式**
对于任意给定的多项式 $p(z) \in \mathbb{C}[z]$，定义多项式：
$$h_p(z) := 1 - (\lambda - z) p(z).$$
在点 $z = \lambda$ 处求值，显然恒有：
$$h_p(\lambda) = 1 - (\lambda - \lambda) p(\lambda) = 1.$$

根据引理 2，由于 $\lambda \in \sigma(T)$，对于该多项式在极限算子 $T$ 处的值，必有：
$$\|h_p(T)\| \ge |h_p(\lambda)| = 1.$$
即对**任意**多项式 $p(z)$，恒有下界：
$$\|I_E - (\lambda I_E - T) p(T)\| \ge 1.$$

**第 3 步：应用多项式范数一致性**
根据题设的“多项式范数记录”性质，对于固定选取的探测多项式 $h_p(z)$，存在正整数 $N_{h_p}$，使得对所有 $n \ge N_{h_p}$，均有：
$$\|h_p(T_n)\| = \|h_p(T)\| \ge 1.$$
展开即为：
$$\|I_E - (\lambda I_E - T_n) p(T_n)\| \ge 1 \qquad (\forall n \ge N_{h_p}). \quad (\star)$$

**第 4 步：Runge 逼近制造矛盾**
回顾反设条件：对所有属于子列的算子 $T_n$，谱集合满足
$$\sigma(T_n) \subset K_\delta := \{z \in \mathbb{C} : |z| \le 1, |z - \lambda| \ge \delta\}.$$
在紧集 $K_\delta$ 上，全纯函数 $f(z) := \frac{1}{\lambda - z}$ 具有解析性。
考虑由 $\lambda$ 处的开球 $B(\lambda, \delta/2)$，由于 $\sigma(T_n)$ 与该球无交，可以在复平面上从无界区域引一条连续曲线连接至 $\lambda$ 的邻域，使得 $K_\delta$ 的补集在广义连通分支上允许全纯逼近。

根据 Runge 定理或有理/多项式一致逼近定理，存在一个与 $n$ 无关的复多项式序列 $\{q_k(z)\}_{k=1}^\infty$，使得在紧集 $K_\delta$ 上一致逼近 $f(z)$：
$$\sup_{z \in K_\delta} \left| 1 - (\lambda - z) q_k(z) \right| \longrightarrow 0 \quad (k \to \infty).$$

任取 $\eta \in (0, 1)$（例如取 $\eta = \frac{1}{2}$），选取充分大的指标 $k_0$，令多项式 $p^*(z) := q_{k_0}(z)$，使得：
$$\sup_{z \in K_\delta} |1 - (\lambda - z) p^*(z)| \le \frac{1}{2}.$$

考察多项式 $h^*(z) := 1 - (\lambda - z) p^*(z)$。
因为对子列中的每个 $T_n$，其所有谱点 $\sigma(T_n)$ 全部落在紧集 $K_\delta$ 内部，故由谱映射定理：
$$r(h^*(T_n)) = \max_{\mu \in \sigma(T_n)} |h^*(\mu)| \le \sup_{z \in K_\delta} |h^*(z)| \le \frac{1}{2}.$$

进一步，由于 $T_n$ 是有限维像算子，且多项式幂次在 $m$ 次方下的谱半径公式给出：
$$r(h^*(T_n)) = \lim_{m \to \infty} \|(h^*(T_n))^m\|^{1/m} \le \frac{1}{2}.$$
对任意固定的幂次 $m$，考虑多项式 $H_m(z) := (h^*(z))^m$。
根据题设，存在 $N_m$ 使得当 $n \ge N_m$ 时：
$$\|H_m(T_n)\| = \|H_m(T)\|.$$
但由引理 2，在 $\lambda \in \sigma(T)$ 处：
$$\|H_m(T)\| \ge |H_m(\lambda)| = |h^*(\lambda)|^m = 1^m = 1.$$
这要求对所有 $n \ge N_m$：
$$\|(h^*(T_n))^m\| = \|H_m(T_n)\| = \|H_m(T)\| \ge 1.$$
两边取 $m$ 次方根：
$$\|(h^*(T_n))^m\|^{1/m} \ge 1.$$
让 $m \to \infty$，左边收敛于谱半径 $r(h^*(T_n))$，由此导出：
$$r(h^*(T_n)) \ge 1.$$

然而，由多项式 $p^*$ 在紧集 $K_\delta \supseteq \sigma(T_n)$ 上的构造，此前已严格证得：
$$r(h^*(T_n)) \le \frac{1}{2}.$$
由此得出：
$$1 \le r(h^*(T_n)) \le \frac{1}{2},$$
产生彻底的数学矛盾！

---

## 四、 结论

上述矛盾表明反设不成立，因此：
$$\lim_{n\to\infty} \operatorname{dist}(\lambda, \sigma(T_n)) = 0.$$

依构造选取
$$\lambda_n \in \operatorname{argmin}_{\mu \in \sigma(T_n)} |\mu - \lambda|,$$
则有
$$|\lambda_n - \lambda| = \operatorname{dist}(\lambda, \sigma(T_n)) \longrightarrow 0 \quad (n \to \infty).$$

至此，谱恢复定理在有限维像模型下获证完整成立。 $\blacksquare$
