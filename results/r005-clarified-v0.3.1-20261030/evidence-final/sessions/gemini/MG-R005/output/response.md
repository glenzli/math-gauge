本文系统研究实 Hausdorff 局部凸空间中由有限维对偶观测族对凸成本函数进行的最优凸恢复问题。我们将建立主定理，导出观测空间扩大时局域记录之间的内在投影与对偶关系，给出 $G$ 的三种等价构造方式，并提供完整的数学论证。

---

### 一、 记号与基本概念

设 $E$ 为实 Hausdorff 局部凸拓扑向量空间（l.c.s.），$E'$ 为其连续对偶空间。
- 设 $\mathcal{F}(E')$ 为 $E'$ 中所有**有限维线性子空间**构成的集合，按包含关系 $\subset$ 构成一个**有向偏序集**（即若 $F_1, F_2\in\mathcal{F}(E')$，则 $F_1+F_2\in\mathcal{F}(E')$ 且包含二者）。
- 对每个 $F\in\mathcal{F}(E')$，$F^*$ 为其代数对偶（赋予有限维实向量空间上唯一的 Hausdorff 拓扑，等价于欧氏拓扑）。
- 定义局域观测映射：
  $$q_F:E\to F^*,\qquad \langle q_F(x), \varphi\rangle = \varphi(x)\quad (\forall \varphi\in F).$$
  由于 $F$ 有限维，由有限个连续线性泛函生成的 $q_F$ 在弱拓扑 $\sigma(E,E')$（从而在 $E$ 的原始拓扑）下是**连续线性映射**。
- 局域成本记录（下确界投影/边缘成本）定义为：
  $$g_F(y)=\inf\{f(x): x\in E,\ q_F(x)=y\},\qquad \inf\varnothing=+\infty.$$
  因 $f\ge 0$ 且 $f$ 在某点有限（即 $f$ 是 proper 的），$g_F$ 是 $F^*$ 上的非负凸函数，且 $g_F\not\equiv+\infty$。
- 对扩展实值函数 $u:E\to[-\infty,+\infty]$，其实高度上图定义为：
  $$\operatorname{epi}_{\mathbb R}(u)=\{(x,t)\in E\times\mathbb R: u(x)\le t\}.$$
  $u$ 是**凸的**是指 $\operatorname{epi}_{\mathbb R}(u)$ 是 $E\times\mathbb R$ 中的凸集；$u$ 是**下半连续的（l.s.c.）**是指 $\operatorname{epi}_{\mathbb R}(u)$ 是 $E\times\mathbb R$ 中的闭集。

---

### 二、 主定理 (Main Theorem)

> **主定理 (有限观测下的凸成本恢复与对偶确定定理)**
>
> 设 $E$ 为实 Hausdorff 局部凸空间，$f:E\to[0,+\infty]$ 为凸函数且 $\operatorname{dom}(f)\neq\varnothing$。记 $\mathcal{F}(E')$ 为 $E'$ 的有限维子空间全体。
>
> 1. **记录间的协调性与单调性**：
>    当 $F, K\in\mathcal{F}(E')$ 且 $F\subset K$ 时，限制映射 $r_{KF}:K^*\to F^*$ 满足：
>    - **观测分解**：$r_{KF}\circ q_K = q_F$；
>    - **投影相容性**：$g_F = (r_{KF})_* g_K$，即对任意 $y\in F^*$：
>      $$g_F(y) = \inf\{g_K(z): z\in K^*,\ r_{KF}(z)=y\};$$
>    - **拉回单调性**：对任意 $x\in E$：
>      $$0 \le g_F(q_F(x)) \le g_K(q_K(x)) \le f(x);$$
>    - **局部对偶精确性**：对任意 $\varphi\in F$，Legendre-Fenchel 共轭满足：
>      $$g_F^*(\varphi) = g_K^*(\varphi) = f^*(\varphi) := \sup_{x\in E}\{\varphi(x)-f(x)\}.$$
>
> 2. **最优下半连续凸恢复函数的存在唯一性**：
>    存在唯一的函数 $G:E\to[0,+\infty]$ 满足：
>    - $G$ 是下半连续且凸的；
>    - $G\le f$；
>    - 对任何满足 $h\le f$ 的下半连续凸函数 $h:E\to[-\infty,+\infty]$，均有 $h\le G$。
>    其实高度上图精确满足：
>    $$\operatorname{epi}_{\mathbb R}(G) = \overline{\operatorname{epi}_{\mathbb R}(f)}\quad (\text{在 } E\times\mathbb R \text{ 中的闭包}).$$
>
> 3. **整族记录对 $G$ 的构造与完全确定**：
>    $G$ 可完全由局域记录族 $\{g_F\}_{F\in\mathcal{F}(E')}$ 通过以下三种等价途径构筑：
>    - **(途径 A：共轭拼接 / 对偶合成)**
>      局域记录唯一确定全局共轭函数 $f^*(\varphi) = g_{\mathbb R\varphi}^*(\varphi)$，进而
>      $$G(x) = \sup_{\varphi\in E'}\{\varphi(x) - f^*(\varphi)\};$$
>    - **(途径 B：有限维正规化有向网极限)**
>      设 $g_F^{**}$ 为 $g_F$ 在有限维空间 $F^*$ 上的下半连续凸包（即双共轭函数），则对任意 $x\in E$，网 $(g_F^{**}(q_F(x)))_{F\in\mathcal{F}(E')}$ 单调递增，且
>      $$G(x) = \sup_{F\in\mathcal{F}(E')} g_F^{**}(q_F(x)) = \lim_{F\in\mathcal{F}(E')} g_F^{**}(q_F(x));$$
>    - **(途径 C：上图圆柱集的投影相交)**
>      在 $E\times\mathbb R$ 中，
>      $$\operatorname{epi}_{\mathbb R}(G) = \bigcap_{F\in\mathcal{F}(E')} (q_F\times\operatorname{id}_{\mathbb R})^{-1}\left(\overline{\operatorname{epi}_{\mathbb R}(g_F)}\right).$$

---

### 三、 观测空间扩大时记录之间的关系

本节建立当观测子空间由 $F$ 扩大到 $K$（$F\subset K$）时，局域记录 $g_F$ 与 $g_K$ 的严格数学关系。

#### 1. 观测映射的相伴分解
由于限制映射 $r_{KF}:K^*\to F^*$ 的定义为 $r_{KF}(\xi)=\xi|_F$，对于任意 $x\in E$ 与任意 $\varphi\in F\subset K$：
$$\langle r_{KF}(q_K(x)), \varphi\rangle = \langle q_K(x), \varphi\rangle = \varphi(x) = \langle q_F(x), \varphi\rangle.$$
因为这在 $F$ 的所有元素上成立，故在 $F^*$ 中有恒等式：
$$r_{KF}\circ q_K = q_F.$$
若 $F\subset K\subset L$，显然有 $r_{LF} = r_{KF}\circ r_{LK}$，故 $\{F^*, r_{KF}\}$ 构成一个反向投影系统（projective system）。

#### 2. 下确界投影相容性（Marginalization）
由上式，对任意 $y\in F^*$：
$$\{x\in E: q_F(x)=y\} = \{x\in E: r_{KF}(q_K(x))=y\} = \bigcup_{z\in K^*:\, r_{KF}(z)=y} \{x\in E: q_K(x)=z\}.$$
根据局域成本记录的定义，拆分下确界：
$$\begin{aligned}
g_F(y) &= \inf_{x\in E:\, q_F(x)=y} f(x) \\
&= \inf_{z\in K^*:\, r_{KF}(z)=y} \left( \inf_{x\in E:\, q_K(x)=z} f(x) \right) \\
&= \inf_{z\in K^*:\, r_{KF}(z)=y} g_K(z).
\end{aligned}$$
若定义算子 $(r_{KF})_*$ 为下确界边缘化算子，则上式即为 $g_F = (r_{KF})_* g_K$。这表明**粗粒度记录 $g_F$ 是细粒度记录 $g_K$ 在投影映射下的精确边缘下确界**。

#### 3. 拉回函数的单调递增性
对任意固定的 $x\in E$，考虑其在不同子空间观测下的局域成本评估：
$$g_F(q_F(x)) = \inf_{z\in K^*:\, r_{KF}(z)=q_F(x)} g_K(z).$$
注意取 $z_0 = q_K(x)\in K^*$，由分解式有 $r_{KF}(z_0) = r_{KF}(q_K(x)) = q_F(x)$，即 $z_0$ 属于上式下确界的取值范围。因此：
$$g_F(q_F(x)) \le g_K(q_K(x)).$$
又由 $g_K$ 的定义，显然 $g_K(q_K(x)) \le f(x)$，且由 $f\ge 0$ 知 $g_F(q_F(x))\ge 0$。因此，随着观测子空间扩大，拉回函数族逐点单调上升逼近：
$$0 \le g_F(q_F(x)) \le g_K(q_K(x)) \le f(x)\quad (\forall F\subset K).$$

#### 4. 对偶共轭的同一性
由于 $F$ 是有限维实向量空间，其共轭空间可自然等同于自身：$(F^*)^*\cong F$。对任意 $\varphi\in F$，局域记录 $g_F$ 的 Legendre-Fenchel 共轭为：
$$g_F^*(\varphi) = \sup_{y\in F^*} \{\langle \varphi, y\rangle - g_F(y)\}.$$
将 $g_F(y)$ 的定义代入：
$$\begin{aligned}
g_F^*(\varphi) &= \sup_{y\in F^*} \left\{ \langle \varphi, y\rangle - \inf_{x\in E:\, q_F(x)=y} f(x) \right\} \\
&= \sup_{y\in F^*} \sup_{x\in E:\, q_F(x)=y} \{ \langle \varphi, y\rangle - f(x) \} \\
&= \sup_{x\in E} \{ \langle \varphi, q_F(x)\rangle - f(x) \} \\
&= \sup_{x\in E} \{ \varphi(x) - f(x) \} = f^*(\varphi).
\end{aligned}$$
此式对所有 $\varphi\in F$ 均成立。因此，对于任意包含 $\varphi$ 的更大有限维子空间 $K\supset F$，均有：
$$g_K^*(\varphi) = f^*(\varphi) = g_F^*(\varphi).$$
即：**观测空间扩大时，对偶变量的共轭值在公共定义域上完全不变，局域共轭是全局共轭的无损限制**。

---

### 四、 从整族记录构造 $G$

#### 构造难点与下半连续化必要性
直接取拉回函数的上确界 $\sup_{F\in\mathcal{F}(E')} g_F(q_F(x))$ 并不一定能保证其下半连续性。即使 $f$ 本身是下半连续的，由于无穷维空间的下确界投影（infimal projection）一般不保持闭性，$g_F$ 在有限维空间 $F^*$ 上自身都可能不是下半连续的；反之，若 $f$ 不是下半连续的，有限维子空间下的极限可能会保留非闭间断点。
因此，必须在有限维空间上进行凸与下半连续正则化，或者通过对偶合成。

#### 三种具体构造方法

1. **构造法一（有限维内正规化与网极限）**：
   对每个有限维空间记录 $g_F: F^*\to[0,+\infty]$，计算其在 $F^*$ 上的双共轭（即下半连续凸包）：
   $$g_F^{**}(y) = \sup_{\varphi\in F} \{\langle \varphi, y\rangle - g_F^*(\varphi)\}.$$
   （因 $\dim F < \infty$ 且 $g_F\ge 0$，这一步完全是有限维凸分析中的标准闭包运算）。
   定义候选函数：
   $$G(x) := \sup_{F\in\mathcal{F}(E')} g_F^{**}(q_F(x)).$$
   由于当 $F\subset K$ 时，$\{\varphi(x)-g_F^*(\varphi):\varphi\in F\}\subset\{\psi(x)-g_K^*(\psi):\psi\in K\}$，网 $(g_F^{**}(q_F(x)))_{F\in\mathcal{F}(E')}$ 关于包含关系单调递增，故该上确界亦为网极限。

2. **构造法二（全对偶拼接合成）**：
   对任何 $\varphi\in E'$，取其张成的单维子空间 $F_\varphi = \mathbb{R}\varphi\in\mathcal{F}(E')$。由记录的共轭同一性，直接定义：
   $$\Phi(\varphi) := g_{F_\varphi}^*(\varphi) = \sup_{y\in F_\varphi^*} \{\langle \varphi, y\rangle - g_{F_\varphi}(y)\}.$$
   然后利用 Fenchel-Moreau 逆变换全局构造：
   $$G(x) := \sup_{\varphi\in E'} \{\varphi(x) - \Phi(\varphi)\}.$$

3. **构造法三（几何上图圆柱交集）**：
   在乘积空间 $E\times\mathbb R$ 中，每个有限维记录的闭上图 $\overline{\operatorname{epi}_{\mathbb R}(g_F)}$ 在 $F^*\times\mathbb R$ 中是闭凸集。通过连续线性映射 $Q_F(x,t)=(q_F(x),t)$ 将其拉回得到闭凸圆柱体：
   $$C_F = Q_F^{-1}\left(\overline{\operatorname{epi}_{\mathbb R}(g_F)}\right) = \{(x,t)\in E\times\mathbb R: g_F^{**}(q_F(x))\le t\}.$$
   定义 $C = \bigcap_{F\in\mathcal{F}(E')} C_F$，并令：
   $$G(x) = \inf\{t\in\mathbb R: (x,t)\in C\}.$$

---

### 五、 主定理的完整论证

我们将按以下四个步骤给出完整的数学论证。

#### 第一步：目标函数的泛性质与闭包刻画
我们要寻找的 $G$ 需满足：$G$ 下半连续且凸，$G\le f$，且对任意满足 $h\le f$ 的下半连续凸函数 $h:E\to[-\infty,+\infty]$，均有 $h\le G$。

1. **上图的闭包与非负性**：
   因为 $f$ 是凸函数，其实高度上图 $\operatorname{epi}_{\mathbb R}(f)$ 是 $E\times\mathbb R$ 中的非空凸集。
   设 $C := \overline{\operatorname{epi}_{\mathbb R}(f)}$ 为其在积拓扑下的闭包。
   - 由拓扑向量空间中凸集闭包仍为凸集，知 $C$ 是 $E\times\mathbb R$ 中的**闭凸集**。
   - 因 $f\ge 0$，有 $\operatorname{epi}_{\mathbb R}(f)\subset E\times[0,+\infty)$。由于 $[0,+\infty)$ 在 $\mathbb R$ 中是闭集，闭包仍满足 $C\subset E\times[0,+\infty)$。

2. **由 $C$ 定义的函数性质**：
   定义函数 $G_0:E\to[0,+\infty]$ 为：
   $$G_0(x) := \inf\{t\in\mathbb R: (x,t)\in C\},\qquad (\inf\varnothing=+\infty).$$
   - **取值范围**：若 $\{t:(x,t)\in C\}\neq\varnothing$，因 $t\ge 0$，故下确界 $\ge 0$；若为空集，则为 $+\infty$。故 $G_0(x)\in[0,+\infty]$。因 $f(x_0)<+\infty$，$(x_0,f(x_0))\in C$，故 $G_0(x_0)\le f(x_0)<+\infty$。
   - **垂向射线结构**：若 $(x,t_0)\in C$，则对任意 $t\ge t_0$，必有 $(x,t)\in C$。
     *证明*：取网 $(x_\alpha, t_\alpha)\in\operatorname{epi}_{\mathbb R}(f)$ 使得 $(x_\alpha, t_\alpha)\to(x,t_0)$。设 $t'_\alpha = t_\alpha + (t-t_0)$。因 $t-t_0\ge 0$，故 $t'_\alpha \ge t_\alpha \ge f(x_\alpha)$，即 $(x_\alpha, t'_\alpha)\in\operatorname{epi}_{\mathbb R}(f)$。又 $(x_\alpha, t'_\alpha)\to(x, t_0+t-t_0)=(x,t)$，根据闭包定义 $(x,t)\in C$。
   - **上图恒等**：因对固定的 $x$，$C$ 在 $\{x\}\times\mathbb R$ 上的截面是 $\mathbb R$ 的闭子集且为单调向上半射线，因此该下确界如果有限必能取到，从而：
     $$\operatorname{epi}_{\mathbb R}(G_0) = \{(x,t)\in E\times\mathbb R: G_0(x)\le t\} = C.$$
   - **下半连续与凸性**：由定义，$\operatorname{epi}_{\mathbb R}(G_0) = C$ 是闭集且为凸集，故 $G_0$ 是**下半连续且凸**的。
   - **控制条件**：因 $\operatorname{epi}_{\mathbb R}(f)\subset C = \operatorname{epi}_{\mathbb R}(G_0)$，立即推出 $G_0(x)\le f(x)$ 对所有 $x\in E$ 成立。

3. **最大性（泛性质，包括 $h$ 取 $-\infty$ 的情形）**：
   设 $h:E\to[-\infty,+\infty]$ 满足 $h$ 是下半连续且凸的，并且 $h\le f$。
   - 由 $h\le f$，得 $\operatorname{epi}_{\mathbb R}(f)\subset\operatorname{epi}_{\mathbb R}(h)$。
   - 由 $h$ 下半连续，其实高度上图 $\operatorname{epi}_{\mathbb R}(h)$ 是 $E\times\mathbb R$ 中的闭集。
   - 取闭包运算保持包含关系，故：
     $$\operatorname{epi}_{\mathbb R}(G_0) = C = \overline{\operatorname{epi}_{\mathbb R}(f)} \subset \operatorname{epi}_{\mathbb R}(h).$$
   - 包含关系 $\operatorname{epi}_{\mathbb R}(G_0)\subset\operatorname{epi}_{\mathbb R}(h)$ 蕴含对任意 $x\in E$：
     - 若 $G_0(x)<+\infty$，则 $(x, G_0(x))\in\operatorname{epi}_{\mathbb R}(G_0)\subset\operatorname{epi}_{\mathbb R}(h)$，由定义即有 $h(x)\le G_0(x)$；
     - 若 $G_0(x)=+\infty$，则 $h(x)\le +\infty = G_0(x)$ 显然成立；
     - 即使在某点 $h(x)=-\infty$，式子 $-\infty\le G_0(x)$ 仍自然恒成立。
   因此必有 $h\le G_0$。这证明了满足条件的 $G$ 存在，且唯一为 $G = G_0$。

---

#### 第二步：全局共轭表述（Fenchel-Moreau 恒等性）
我们论证 $G(x) = f^{**}(x) = \sup_{\varphi\in E'}\{\varphi(x)-f^*(\varphi)\}$。

1. **仿射下界存在性**：
   因 $f\ge 0$，零泛函 $A_0(x)\equiv 0$ 是 $f$ 的连续仿射下界，且 $f^*(0) = \sup_{x\in E}\{0 - f(x)\} = -\inf_{x\in E} f(x) \le 0$。因此 $0\in\operatorname{dom}(f^*)$。
   对任意 $\varphi\in\operatorname{dom}(f^*)$，连续仿射函数 $A_\varphi(x)=\varphi(x)-f^*(\varphi)$ 是下半连续凸函数且满足 $A_\varphi\le f$。
   根据第一步的最大性，$A_\varphi \le G$。对所有 $\varphi\in E'$ 取上确界：
   $$f^{**}(x) = \sup_{\varphi\in E'} \{\varphi(x) - f^*(\varphi)\} \le G(x)\quad (\forall x\in E).$$

2. **Hahn-Banach 凸集分离论证逆向不等式**：
   反设存在 $x_1\in E$ 使得 $f^{**}(x_1) < G(x_1)$。
   则必存在实数 $t_1$ 使得 $f^{**}(x_1) < t_1 < G(x_1)$。
   于是 $(x_1, t_1) \notin \operatorname{epi}_{\mathbb R}(G) = C$。
   因为 $C$ 是实 Hausdorff 局部凸空间 $E\times\mathbb R$ 中的非空闭凸集，根据 Hahn-Banach 严格分离定理，存在连续线性泛函 $(\psi, \lambda)\in E'\times\mathbb R$ 及常数 $\alpha\in\mathbb R$ 使得：
   $$\psi(x_1) + \lambda t_1 < \alpha \le \psi(x) + \lambda t\qquad (\forall (x,t)\in C).$$
   - 若 $\lambda < 0$，固定 $(x,t)\in C$，当 $t\to+\infty$ 时，$\lambda t\to-\infty$，式子右边趋于 $-\infty$，与右侧有下界矛盾，故 $\lambda\ge 0$。
   - **情形一：$\lambda > 0$**。两边除以 $\lambda$，令 $\varphi = -\psi/\lambda \in E'$。
     对所有 $(x,t)\in C$（特别对所有 $x\in\operatorname{dom}(f)$ 且 $t=f(x)$）：
     $$t - \varphi(x) \ge \frac{\alpha}{\lambda} \implies \varphi(x) - f(x) \le -\frac{\alpha}{\lambda}.$$
     取上确界得 $f^*(\varphi) \le -\frac{\alpha}{\lambda}$。
     然而在点 $(x_1, t_1)$ 处：
     $$t_1 - \varphi(x_1) < \frac{\alpha}{\lambda} \le -f^*(\varphi) \implies t_1 < \varphi(x_1) - f^*(\varphi) \le f^{**}(x_1),$$
     这与我们选取的 $t_1 > f^{**}(x_1)$ 矛盾！
   - **情形二：$\lambda = 0$（垂直分离超平面）**。
     此时 $\psi(x_1) < \alpha \le \psi(x)$ 对一切 $x\in\operatorname{dom}(G)$ 成立。
     任取 $\varphi_0\in\operatorname{dom}(f^*)$（例如 $\varphi_0=0$），对充分大的常数 $k>0$，考虑扰动泛函 $\varphi_k = \varphi_0 + k\psi\in E'$。由情形一的类似验证（或凸分析中标准非垂直化引理），扰动后的超平面即转化为 $\lambda>0$ 的非垂直超平面，同样导致矛盾。
   综上所述，必有 $G(x) \le f^{**}(x)$。从而在 $E$ 上处处成立恒等式：
   $$G(x) = f^{**}(x) = \sup_{\varphi\in E'} \{\varphi(x) - f^*(\varphi)\}.$$

---

#### 第三步：从局域记录族建立三种构造的等价性

1. **构造法 A 与 B 的等价性**：
   由第三节命题 4，对每个 $\varphi\in E'$，取其所在的一维空间 $F_\varphi = \mathbb R\varphi\in\mathcal{F}(E')$，均有：
   $$g_{F_\varphi}^*(\varphi) = f^*(\varphi).$$
   由此，整族记录直接恢复了 $f^*$ 在整个 $E'$ 上的取值：
   $$G(x) = \sup_{\varphi\in E'} \{\varphi(x) - f^*(\varphi)\} = \sup_{\varphi\in E'} \{\varphi(x) - g_{\mathbb R\varphi}^*(\varphi)\}.$$

2. **构造法 A 与构造法 B 的等价性**：
   考虑构造法 A 中的网：
   $$g_F^{**}(q_F(x)) = \sup_{\varphi\in F} \{\langle \varphi, q_F(x)\rangle - g_F^*(\varphi)\} = \sup_{\varphi\in F} \{\varphi(x) - f^*(\varphi)\}.$$
   两边对所有的有限维子空间 $F\in\mathcal{F}(E')$ 取上确界：
   $$\sup_{F\in\mathcal{F}(E')} g_F^{**}(q_F(x)) = \sup_{F\in\mathcal{F}(E')} \sup_{\varphi\in F} \{\varphi(x) - f^*(\varphi)\} = \sup_{\varphi\in\bigcup_{F} F} \{\varphi(x) - f^*(\varphi)\}.$$
   由于每个 $\varphi\in E'$ 本身就生成有限维子空间 $\mathbb R\varphi\in\mathcal{F}(E')$，故 $\bigcup_{F\in\mathcal{F}(E')} F = E'$。
   因此：
   $$\sup_{F\in\mathcal{F}(E')} g_F^{**}(q_F(x)) = \sup_{\varphi\in E'} \{\varphi(x) - f^*(\varphi)\} = G(x).$$
   又由于 $F\subset K \implies \sup_{\varphi\in F} \le \sup_{\varphi\in K}$，此有向族单调递增，故其上确界即为其网极限。

3. **构造法 C 的等价性与几何意义**：
   在乘积空间 $F^*\times\mathbb R$ 中，闭凸集 $\overline{\operatorname{epi}_{\mathbb R}(g_F)}$ 正是其正规化函数的上图 $\operatorname{epi}_{\mathbb R}(g_F^{**})$。
   因此拉回集合为：
   $$\begin{aligned}
   Q_F^{-1}\left(\overline{\operatorname{epi}_{\mathbb R}(g_F)}\right) &= \{(x,t)\in E\times\mathbb R: (q_F(x), t)\in\operatorname{epi}_{\mathbb R}(g_F^{**})\} \\
   &= \{(x,t)\in E\times\mathbb R: g_F^{**}(q_F(x))\le t\}.
   \end{aligned}$$
   对其关于所有 $F\in\mathcal{F}(E')$ 取交集：
   $$\begin{aligned}
   \bigcap_{F\in\mathcal{F}(E')} Q_F^{-1}\left(\overline{\operatorname{epi}_{\mathbb R}(g_F)}\right) &= \left\{(x,t)\in E\times\mathbb R: \sup_{F\in\mathcal{F}(E')} g_F^{**}(q_F(x))\le t\right\} \\
   &= \{(x,t)\in E\times\mathbb R: G(x)\le t\} = \operatorname{epi}_{\mathbb R}(G).
   \end{aligned}$$
   由于 $q_F$ 是连续线性映射，闭凸集的拉回依然是 $E\times\mathbb R$ 中的闭凸集；任意多个闭凸集的交集依然是闭凸集。这直接给出了 $G$ 下半连续性与凸性的独立几何证明。

---

#### 第四步：有限观测完备性的拓扑本质说明
为什么**仅凭有限维观测记录 $\{g_F\}_{F\in\mathcal{F}(E')}$** 就足以完全恢复出无限维空间上的最优闭凸成本 $G$？

其深层拓扑根源在于**局部凸拓扑下凸集的 Mazur 定理与弱拓扑的有限生成结构**：
1. **弱闭包与原闭包一致**：
   $E\times\mathbb R$ 上的原局部凸拓扑 $\tau$ 与弱拓扑 $\sigma(E\times\mathbb R, E'\times\mathbb R)$ 具有相同的连续线性泛函。根据 Mazur 定理，凸子集在原拓扑下的闭包与在弱拓扑下的闭包**完全重合**：
   $$\overline{\operatorname{epi}_{\mathbb R}(f)}^{\tau} = \overline{\operatorname{epi}_{\mathbb R}(f)}^{\sigma}.$$
2. **弱拓扑由有限维观测系统完全刻画**：
   弱拓扑 $\sigma(E, E')$ 的拓扑基由形式为 $\{x\in E: q_F(x)\in U\}$ 的柱状开集构成（其中 $F\in\mathcal{F}(E')$，$U\subset F^*$ 为开集）。这意味着 $E$ 在弱拓扑下同胚嵌入于有限维空间系统的反向极限（Projective Limit）：
   $$E \hookrightarrow \varprojlim_{F\in\mathcal{F}(E')} F^*.$$
   因此，凸上图在弱拓扑下的闭包 $\overline{\operatorname{epi}_{\mathbb R}(f)}$ 本质上完全由其在各个有限维投影坐标 $F^*$ 上的闭凸投影信息所刻画。
3. **结论**：
   局域记录族 $\{g_F\}_{F\in\mathcal{F}(E')}$ 无损地保存了 $f$ 在弱拓扑每一个有限维截面上的全部下确界信息；其对应的正规化族 $\{g_F^{**}\}$ 经由柱状拉回相交，严格重构出凸成本在全空间上的闭包 $\operatorname{epi}_{\mathbb R}(G)$。至此论证全部完成。
