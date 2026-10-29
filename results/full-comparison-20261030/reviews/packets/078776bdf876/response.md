本文针对实 Hausdorff 局部凸空间上凸成本函数在有限维线性观测下的恢复问题，建立完备的理论框架。全文包含：观测空间扩大时局域记录的演化规律、下半连续凸包 $G$ 的构造、主定理的陈述与严格论证，以及整族记录对 $G$ 的几何与对偶决定机制。

---

### 一、 符号设定与数学背景

设 $E$ 为实 Hausdorff 局部凸拓扑向量空间（LCS），$E'$ 为其连续对偶空间，拓扑配对记为 $\langle x, \varphi\rangle = \varphi(x)$（$x\in E, \varphi\in E'$）。
给定凸函数 $f: E \to [0, +\infty]$，假定 $f$ 是**真**的（proper），即存在 $x_0 \in E$ 使得 $f(x_0) < +\infty$。

记 $\mathcal{F}$ 为 $E'$ 中所有有限维线性子空间构成的集合。按包含关系 $\subset$，$(\mathcal{F}, \subset)$ 构成一个**有向集**（directed set）：对任意 $F_1, F_2 \in \mathcal{F}$，均有 $F_1 + F_2 \in \mathcal{F}$ 且 $F_1 \subset F_1 + F_2, F_2 \subset F_1 + F_2$。

对于每个 $F \in \mathcal{F}$，记 $n = \dim F < \infty$：
1. $F^*$ 为 $F$ 的代数对偶空间，赋予其唯一的有限维 Hausdorff 向量拓扑（Euclidean 拓扑）。
2. **观测映射** $q_F: E \to F^*$ 定义为：
   $$q_F(x)(\varphi) = \varphi(x), \quad \forall \varphi \in F.$$
   易知 $q_F$ 是线性、连续且满射的开映射，其核空间为极集 $\ker(q_F) = F^\circ = \{x\in E: \varphi(x) = 0, \forall \varphi \in F\}$。因此 $F^* \cong E / F^\circ$。
3. **局域成本记录**（下确界边际投影 / infimal projection）$g_F: F^* \to [0, +\infty]$ 定义为：
   $$g_F(y) = \inf \{f(x) : x\in E, \, q_F(x) = y\}, \qquad (\inf \varnothing = +\infty).$$
4. 当 $F \subset K$（$F, K \in \mathcal{F}$）时，记 $i_{FK}: F \hookrightarrow K$ 为自然包含映射，限制映射 $r_{KF}: K^* \to F^*$ 定义为其伴随映射 $r_{KF} = (i_{FK})^*$，即
   $$\langle r_{KF}(z), \varphi\rangle = \langle z, \varphi\rangle, \quad \forall z \in K^*, \, \varphi \in F.$$

---

### 二、 观测空间扩大时记录之间的内在关系

当观测空间由 $F$ 扩大到 $K$（即 $F \subset K$）时，我们获取了关于系统的更精细的线性测量。局域成本记录之间满足如下严格的代数、序与对偶相容性：

#### 1. 观测映射的分解与相容性
由于对任意 $x \in E$ 及 $\varphi \in F \subset K$，有
$$r_{KF}(q_K(x))(\varphi) = q_K(x)(\varphi) = \varphi(x) = q_F(x)(\varphi),$$
故观测映射满足交换分解关系：
$$q_F = r_{KF} \circ q_K.$$

#### 2. 边际投影相容性（Tropical / 幂等 Kolmogorov 相容性）
将 $q_F(x) = y$ 展开为 $r_{KF}(q_K(x)) = y$，可知约束集合满足：
$$\{x \in E : q_F(x) = y\} = \bigcup_{z \in K^*, \, r_{KF}(z) = y} \{x \in E : q_K(x) = z\}.$$
在两端对 $f(x)$ 取下确界，立即得到：
$$g_F(y) = \inf_{z \in r_{KF}^{-1}(y)} g_K(z) =: (r_{KF} g_K)(y), \quad \forall y \in F^*.$$
这表明族 $\{g_F\}_{F\in\mathcal{F}}$ 在下确界投影运算下构成一个**反向系统（projective system）**。

#### 3. 原空间拉回函数的单调递增性
对任意固定的状态 $x \in E$，由于 $q_K(x) \in r_{KF}^{-1}(q_F(x))$，直接可得：
$$g_F(q_F(x)) = \inf_{z \in r_{KF}^{-1}(q_F(x))} g_K(z) \le g_K(q_K(x)) \le f(x).$$
因此，随着观测子空间扩大，拉回记录 $x \mapsto g_F(q_F(x))$ 构成一个**逐点单调不减**的网：
$$F \subset K \implies g_F(q_F(x)) \le g_K(q_K(x)) \le f(x), \quad \forall x \in E.$$

#### 4. Legendre-Fenchel 凸共轭的完全一致性
在有限维空间 $F^*$ 上，对任意 $\varphi \in F$，计算 $g_F$ 的凸共轭：
$$\begin{aligned}
g_F^*(\varphi) &= \sup_{y \in F^*} \big( \langle y, \varphi \rangle - g_F(y) \big) \\
&= \sup_{y \in F^*} \sup_{x \in q_F^{-1}(y)} \big( \langle q_F(x), \varphi \rangle - f(x) \big) \\
&= \sup_{x \in E} \big( \varphi(x) - f(x) \big) = f^*(\varphi).
\end{aligned}$$
同理，对 $K$ 及任意 $\varphi \in F \subset K$，有 $g_K^*(\varphi) = f^*(\varphi)$。由此得到极重要的对偶恒等式：
$$g_F^*(\varphi) = g_K^*(\varphi) = f^*(\varphi), \quad \forall \varphi \in F \subset K.$$
即：**记录的凸共轭在公共观测方向上完全相等，且精确吻合原成本 $f$ 在该方向上的共轭值。**

#### 5. 双共轭与下半连续化包络的单调性
在有限维实空间 $F^*$ 上，真凸函数 $g_F \ge 0$ 的双共轭 $g_F^{**}$ 即为其下半连续凸包（闭包）$\overline{g}_F$：
$$g_F^{**}(y) = \sup_{\varphi \in F} \big( \langle y, \varphi \rangle - g_F^*(\varphi) \big) = \sup_{\varphi \in F} \big( \langle y, \varphi \rangle - f^*(\varphi) \big) = \overline{g}_F(y).$$
当 $F \subset K$ 时，由于 $F \subset K$，对任意 $z \in K^*$：
$$g_F^{**}(r_{KF}(z)) = \sup_{\varphi \in F} \big( \langle z, \varphi \rangle - f^*(\varphi) \big) \le \sup_{\psi \in K} \big( \langle z, \psi \rangle - f^*(\psi) \big) = g_K^{**}(z).$$
将其拉回至 $E$，即得下半连续修正后的单调关系：
$$g_F^{**}(q_F(x)) \le g_K^{**}(q_K(x)) \le g_K(q_K(x)) \le f(x), \quad \forall x \in E.$$

---

### 三、 目标函数 $G$ 的构造

在有限维中，即使 $f$ 是下半连续的，由于约束优化中的下确界可能在无穷远处取得，下确界投影 $g_F$ 自身**不一定**下半连续。因此，为了直接构造下半连续函数，必须对每个局域记录进行下半连续正则化。

#### 构造方案一：原网极限构造（Primal Regularized Net）
对每个 $F \in \mathcal{F}$，定义拉回正则化函数 $G_F: E \to [0, +\infty]$：
$$G_F(x) := g_F^{**}(q_F(x)) = \overline{g}_F(q_F(x)) = \sup_{\varphi \in F} \big( \varphi(x) - f^*(\varphi) \big).$$
由前述性质，网 $(G_F(x))_{F\in\mathcal{F}}$ 沿有向集 $(\mathcal{F}, \subset)$ 逐点单调递增，定义其逐点极限为：
$$G(x) := \sup_{F \in \mathcal{F}} G_F(x) = \lim_{F \in \mathcal{F}} g_F^{**}(q_F(x)), \quad \forall x \in E.$$

#### 构造方案二：全对偶胶合构造（Dual Gluing / Legendre-Fenchel）
由于对于任意 $\varphi \in E'$，一维子空间 $\mathbb{R}\varphi \in \mathcal{F}$，定义全空间对偶函数：
$$f^*(\varphi) := g_{\mathbb{R}\varphi}^*(\varphi) = \sup_{t \in \mathbb{R}} \big( t - g_{\mathbb{R}\varphi}(t) \big), \quad \forall \varphi \in E'.$$
（当取包含 $\varphi$ 的任意 $F \in \mathcal{F}$ 时，$g_F^*(\varphi)$ 均给出相同的值）。
进而由 Fenchel-Moreau 变换构造 $G$：
$$G(x) := (f^*)^*(x) = \sup_{\varphi \in E'} \big( \varphi(x) - f^*(\varphi) \big).$$

#### 两种构造的一致性：
由于 $E' = \bigcup_{F \in \mathcal{F}} F$，有：
$$\sup_{F \in \mathcal{F}} G_F(x) = \sup_{F \in \mathcal{F}} \sup_{\varphi \in F} \big( \varphi(x) - f^*(\varphi) \big) = \sup_{\varphi \in \bigcup_{F\in\mathcal{F}} F} \big( \varphi(x) - f^*(\varphi) \big) = \sup_{\varphi \in E'} \big( \varphi(x) - f^*(\varphi) \big) = (f^*)^*(x).$$
两种构造完全一致。

---

### 四、 主定理及完整论证

#### 【主定理】
设 $E$ 为实 Hausdorff 局部凸空间，$f: E \to [0, +\infty]$ 为凸函数且至少在一点有限。由前述构造所得的函数 $G: E \to [0, +\infty]$ 满足：
1. **下半连续性与凸性**：$G$ 是 $E$ 上的下半连续凸函数；
2. **非负性与相容性**：$0 \le G(x) \le f(x)$ 对所有 $x \in E$ 成立，且 $G$ 至少在一点有限；
3. **极大性**：若 $h: E \to [-\infty, +\infty]$ 是任意满足 $h \le f$ 的下半连续凸函数，则必有
   $$h(x) \le G(x), \quad \forall x \in E.$$
   即 $G = \overline{f} = f^{**}$ 是所有不超过 $f$ 的下半连续凸函数中的最大者（即 $f$ 的下半连续凸包 / $\Gamma(E)$-正则化）。
4. **有限观测确定性**：整族记录 $\{g_F\}_{F\in\mathcal{F}}$ 唯一确定 $G$。若 $f$ 本身是下半连续的，则整族记录完全恢复 $f$：
   $$f(x) = \sup_{F \in \mathcal{F}} g_F(q_F(x)) = \sup_{F \in \mathcal{F}} g_F^{**}(q_F(x)).$$

---

#### 【主定理的完整证明】

##### 第一步：验证 $G$ 的下半连续性与凸性
对任意固定的 $\varphi \in E'$，映射 $x \mapsto \varphi(x) - f^*(\varphi)$ 是 $E$ 上的连续仿射泛函（因为 $\varphi \in E'$ 连续）。
函数 $G$ 由此族连续仿射泛函的逐点上确界给出：
$$G(x) = \sup_{\varphi \in E'} \big( \varphi(x) - f^*(\varphi) \big).$$
根据凸分析基本性质，一族连续凸（仿射）函数的逐点上确界必是凸函数，且其下水平集
$$\operatorname{lev}_{\le \alpha}(G) = \{x \in E : G(x) \le \alpha\} = \bigcap_{\varphi \in E'} \{x \in E : \varphi(x) - f^*(\varphi) \le \alpha\}$$
是闭半空间的任意交，因而是 $E$ 中的闭集。这证明了 $G$ 在 $E$ 上是下半连续的凸函数。

##### 第二步：验证值域与支配关系 $0 \le G \le f$
1. **下界 $G \ge 0$**：
   考虑零泛函 $0 \in E'$，其共轭为 $f^*(0) = \sup_{x \in E} (0 - f(x)) = -\inf_{x \in E} f(x)$。
   因为 $f \ge 0$，所以 $\inf_{x\in E} f(x) \ge 0$，从而 $f^*(0) \le 0$。
   由此得：
   $$G(x) \ge 0(x) - f^*(0) = -f^*(0) \ge 0, \quad \forall x \in E.$$
2. **上界 $G \le f$**：
   根据凸共轭的 Fenchel-Young 不等式，对任意 $\varphi \in E'$ 和 $x \in E$，有：
   $$\varphi(x) - f^*(\varphi) \le f(x).$$
   两端对所有 $\varphi \in E'$ 取上确界，即得：
   $$G(x) = \sup_{\varphi \in E'} \big( \varphi(x) - f^*(\varphi) \big) \le f(x), \quad \forall x \in E.$$
3. **真的（Proper）**：
   因为存在 $x_0 \in E$ 使得 $f(x_0) < +\infty$，由 $0 \le G(x_0) \le f(x_0) < +\infty$，知 $G$ 处处不取 $-\infty$ 且至少在一处有限。因此 $G: E \to [0, +\infty]$ 是真的。

##### 第三步：验证极大性
设 $h: E \to [-\infty, +\infty]$ 为任意下半连续凸函数，满足 $h(x) \le f(x)$（$\forall x \in E$）。
1. 若 $h$ 恒等于 $-\infty$，显然 $h \le G$ 成立。
2. 若 $h$ 不恒为 $-\infty$，由于 $h \le f$ 且 $f(x_0) < +\infty$，$h$ 不恒为 $+\infty$。
   又由于 $f \ge 0$，若 $h$ 在某点为 $-\infty$，由凸性及下半连续性，真下半连续凸函数不能在某些点取有限值又在某些点取 $-\infty$。事实上，由 $0 \le f$ 知，仿射函数 $a(x) \equiv 0 \le f$。
   依据局部凸空间上的 **Hahn-Banach 分离定理 / Fenchel-Moreau 定理**：
   在实 Hausdorff 局部凸空间上，任意真的下半连续凸函数等于其连续仿射从属泛函的上确界，亦即等于其 Fenchel 双共轭：
   $$h(x) = h^{**}(x) = \sup_{\varphi \in E'} \big( \varphi(x) - h^*(\varphi) \big).$$
3. 由 $h \le f$，对任意 $\varphi \in E'$，其凸共轭满足逆序关系：
   $$h^*(\varphi) = \sup_{x \in E} \big( \varphi(x) - h(x) \big) \ge \sup_{x \in E} \big( \varphi(x) - f(x) \big) = f^*(\varphi).$$
4. 从而对任意 $x \in E$：
   $$h(x) = \sup_{\varphi \in E'} \big( \varphi(x) - h^*(\varphi) \big) \le \sup_{\varphi \in E'} \big( \varphi(x) - f^*(\varphi) \big) = G(x).$$
这证明了 $G$ 在所有不超过 $f$ 的下半连续凸函数中是唯一的最大元。

##### 第四步：下半连续情形下的完全恢复
假定 $f$ 本身是下半连续凸函数。
由于 $G$ 是所有不大于 $f$ 的下半连续凸函数中的最大者，而 $f$ 自身符合该条件，必有：
$$G(x) = f(x), \quad \forall x \in E.$$
又因为对任意 $F \in \mathcal{F}$，均有：
$$g_F^{**}(q_F(x)) \le g_F(q_F(x)) \le f(x),$$
对两端取上确界并应用夹逼定理：
$$f(x) = G(x) = \sup_{F \in \mathcal{F}} g_F^{**}(q_F(x)) \le \sup_{F \in \mathcal{F}} g_F(q_F(x)) \le f(x),$$
由此立得：
$$\sup_{F \in \mathcal{F}} g_F(q_F(x)) = \sup_{F \in \mathcal{F}} g_F^{**}(q_F(x)) = f(x).$$
定理证毕。

---

### 五、 整族记录如何确定 $G$：几何与拓扑机制

整族有限维局域记录 $\{g_F\}_{F\in\mathcal{F}}$ 能够无损确定连续空间上的下半连续凸包 $G$，其深层原因可从对偶理论、几何逼近与反向极限三方面阐明：

```
                [原空间成本 f: E -> [0, +inf]]
                             |
             (有限维观测投影) | q_F(x)
                             v
               [局域记录 g_F: F* -> [0, +inf]]
                             |
            (有限维下半连续化) | g_F** = \bar{g}_F
                             v
        [局域正则化记录 G_F = g_F** \circ q_F: E -> [0, +inf]]
                             |
                  (有向网上确界) | \sup_{F \in F}
                             v
           [最大下半连续凸成本 G = f** = cl(f)]
```

#### 1. 对偶空间的完备覆盖与信息无损提取
$E$ 的连续对偶空间 $E'$ 是所有有限维观测子空间 $F$ 的有向并：
$$E' = \bigcup_{F \in \mathcal{F}} F.$$
每个局域记录 $g_F$ 经由一维方向的测试，完全提供了 $f$ 在方向 $\varphi \in F$ 上的支撑高程（Support Level）：
$$f^*(\varphi) = g_F^*(\varphi) = \sup_{y \in F^*} \big( \langle y, \varphi \rangle - g_F(y) \big).$$
因此，**不需要无限维全局测量，仅仅通过各个有限维切片记录，就能精确、完全地重构出 $f$ 在全连续对偶空间 $E'$ 上的共轭函数 $f^*$**。由于局部凸空间中下半连续凸集与闭凸函数完全由其闭超平面与支撑泛函确定，对偶信息 $f^*$ 经由 Legendre 变换必然完全确定了 $G$。

#### 2. 上图（Epigraph）的柱集外逼近与投影恢复几何
凸函数的下半连续性等价于其上图 $\operatorname{epi}(G) = \{(x, t) \in E \times \mathbb{R} : G(x) \le t\}$ 在积拓扑下的闭性。
- 对每个有限维观测子空间 $F$，投影映射 $q_F \times \operatorname{id}_{\mathbb{R}}: E \times \mathbb{R} \to F^* \times \mathbb{R}$ 将 $f$ 的上图投影到有限维空间，其闭包正是正则化记录的上图 $\operatorname{epi}(g_F^{**})$；
- 将有限维观测记录提升回原空间，形成以 $F^\circ \times \{0\}$ 为母线的柱形闭凸集：
  $$\operatorname{epi}(G_F) = (q_F \times \operatorname{id}_{\mathbb{R}})^{-1}\big(\operatorname{epi}(g_F^{**})\big);$$
- 随着 $F$ 在 $\mathcal{F}$ 中沿包含关系扩大，柱形集 $\operatorname{epi}(G_F)$ 逐渐收缩，其交集精确给出了 $G$ 的上图：
  $$\operatorname{epi}(G) = \bigcap_{F \in \mathcal{F}} \operatorname{epi}(G_F) = \bigcap_{F \in \mathcal{F}} (q_F \times \operatorname{id}_{\mathbb{R}})^{-1}\big(\overline{\operatorname{epi}(g_F)}\big).$$
这表明，$G$ 正是由这族有限维观测投影所能构筑出的原空间中最紧闭凸柱形包络。

#### 3. 为什么必须采用 $g_F^{**}$（反例阐释正则化的必要性）
考虑 $E = \mathbb{R}^2$，令闭凸子集 $C = \{(x_1, x_2) \in \mathbb{R}^2 : x_1 \ge 0, x_2 \ge 0, x_1 x_2 \ge 1\}$，定义 $f$ 为其示性函数：
$$f(x_1, x_2) = \begin{cases} 0, & (x_1, x_2) \in C, \\ +\infty, & (x_1, x_2) \notin C. \end{cases}$$
$f$ 是下半连续真凸函数。取一维观测子空间 $F$ 为 $x_2$ 坐标轴方向（即 $q_F(x_1, x_2) = x_2$）。
此时局域记录为：
$$g_F(y) = \inf_{x_1 \in \mathbb{R}} f(x_1, y) = \begin{cases} 0, & y > 0, \\ +\infty, & y \le 0. \end{cases}$$
注意：当 $y \to 0^+$ 时 $g_F(y) = 0$，但在 $y=0$ 处 $g_F(0) = +\infty$。因此 **$g_F$ 在有限维空间 $F^*$ 上失去了下半连续性**。
其下半连续正则化为：
$$g_F^{**}(y) = \overline{g}_F(y) = \begin{cases} 0, & y \ge 0, \\ +\infty, & y < 0. \end{cases}$$
若不进行双共轭化，原拉回函数 $g_F \circ q_F$ 在半轴 $\{x_2 = 0, x_1 > 0\}$ 处取值为 $+\infty$，无法展现真实的连续极限行为；而取双共轭 $g_F^{**}$ 则消除了无穷远点边缘效应引起的下半连续性破缺，确保了网 $(g_F^{**} \circ q_F)_{F \in \mathcal{F}}$ 能够单调无缝地收敛逼近真正的下半连续凸包 $G$。

---

### 六、 结论

通过引入有限维局域记录的对偶配对与双共轭正则化，我们证明了：
1. 有限观测记录族在扩大时满足下确界边际投影相容性与对偶共轭限制恒等式；
2. 构造 $G(x) = \sup_{F \in \mathcal{F}} g_F^{**}(q_F(x)) = (f^*)^*(x)$，精确给出了小于等于 $f$ 的最大下半连续凸函数；
3. 整族局域记录包含了原成本函数的所有连续线性支撑信息，从而在弱拓扑与原拓扑意义下完全、唯一地重构了下半连续凸成本 $G$。
