## #h-3ee3f54f03fccb92 基础

要进行计算分析，首先必须说明可比较的数值从何而来。算子演化论的起点不是某个预设的代数结构，而是承载这些数值关系的基础空间。本章从规范空间出发，建立全书最初的对象层；后续所有构造都在这一对象层上展开。

### #h-b4babd684de7c112 扩展规范空间

**定义（扩展规范空间）**：设 $\mathcal{X}$ 为集合，$\bot \in \mathcal{X}$ 为指定的**吸收元**，并要求非吸收部分非空：

$$
\mathcal{X}\setminus\{\bot\}\neq\emptyset.
$$

$\mathcal{X}$ 上的一个**规范结构** $\mathcal{G} = \{d_i\}_{i \in I}$（$I$ 为有限非空指标集）是一族**扩展伪度量**，每个 $d_i: \mathcal{X} \times \mathcal{X} \to \bar{\mathbb{R}}_+ = [0, +\infty]$ 满足：

**(i)** $d_i(x, x) = 0$，

**(ii)** $d_i(x, y) = d_i(y, x)$（对称），

**(iii)** $d_i(x, z) \leq d_i(x, y) + d_i(y, z)$（三角不等式），

**(iv)** $d_i(x, \bot) = +\infty$（$\forall\, x \neq \bot$，吸收元隔离）。

> **约定（$\bar{\mathbb{R}}_+$ 算术）**：全文采用标准扩展非负实数算术：$a + (+\infty) = +\infty$，$0 \cdot (+\infty) = 0$，$a \cdot (+\infty) = +\infty$（$a > 0$）。

称三元组 $(\mathcal{X}, \mathcal{G}, \bot)$ 为**扩展规范空间**（简称**规范空间**）。公理 (iv) 使 $\bot$ 在度量上与 $\mathcal{X} \setminus \{\bot\}$ 完全隔离；$\bot$ 的代数功能见 @h-57a1dc05727a3772。$\mathcal{G}$ 在 $\mathcal{X}$ 上生成**规范族诱导拓扑**——以所有形如 $\{x : d_i(x, x_0) < \varepsilon\}$ 的集合为子基。每个 $d_i$ 称为 $\mathcal{G}$ 的一个**分量（扩展）伪度量**，后续简称**分量伪度量**。

对 $x_0 \in \mathcal{X}$、$r \in (0, +\infty)$ 与分量伪度量 $d_i$，定义**开球**：

$$B_i(x_0, r) := \{x \in \mathcal{X} : d_i(x, x_0) < r\}$$

> **约定（半径与精度的值域）**：本书中，开球半径 $r$ 与覆盖精度 $\varepsilon$ 均取有限正实数（$0 < r < +\infty$，$0 < \varepsilon < +\infty$）。若后文对一族有限正半径取上确界，该上确界本身允许等于 $+\infty$；但这不把 $B_i(x_0,+\infty)$ 变成合法开球，覆盖数也只使用有限正精度。

**定义（族零距关系与族分离性）**：对任意 $x,y\in\mathcal X$，定义

$$
x\sim_{\mathcal G}y
\quad\Longleftrightarrow\quad
d_i(x,y)=0\qquad(\forall i\in I).
$$

若

$$
x\sim_{\mathcal G}y\quad\Longrightarrow\quad x=y
$$

对所有 $x,y\in\mathcal X$ 成立，则称规范族 $\mathcal G$ **分离** $\mathcal X$，并称相应规范空间为**分离规范空间**；否则称其为**非分离规范空间**。

**引理 #h-ecdfb943b4fb8922（族零距关系的等价性）**：$\sim_{\mathcal G}$ 是 $\mathcal X$ 上的等价关系。

**证明**：自反性由 $d_i(x,x)=0$ 得到；对称性由每个 $d_i$ 的对称性得到。若 $x\sim_{\mathcal G}y$ 且 $y\sim_{\mathcal G}z$，则对任意 $i\in I$，

$$
0\le d_i(x,z)\le d_i(x,y)+d_i(y,z)=0,
$$

故 $d_i(x,z)=0$，即 $x\sim_{\mathcal G}z$。$\square$

> **约定（正文不预设族分离性）**：除非显式加入族分离性，本卷所有零测距、计算纤维与算子距离结论均按 $\sim_{\mathcal G}$ 读取，不由全分量零测距推出点值相等。

> **约定（子集排除吸收元）**：后续凡涉及 $\mathcal{X}$ 的子集，除非显式指定，均默认不含 $\bot$。

### #h-65d0745eb743dfe2 空间覆盖与度量熵

**定义（覆盖数）**：对分量伪度量 $d_i$、精度 $\varepsilon > 0$ 与子集 $U \subseteq \mathcal{X}$，定义 $U$ 在 $d_i$ 下的 $\varepsilon$-**覆盖数**：

$$\mathcal{N}_i(\varepsilon, U) := \min\bigl\{|S| : S \subseteq U,\; |S| < \infty,\; U \subseteq \textstyle\bigcup_{s \in S} B_i(s, \varepsilon)\bigr\}$$

即从 $U$ 内部选取中心点、以开球覆盖 $U$ 所需的最小点数（内覆盖）。若 $U$ 不可有限覆盖则 $\mathcal{N}_i(\varepsilon, U) = +\infty$；由定义，$\mathcal{N}_i(\varepsilon, \emptyset) = 0$。

对任意非空指标子族 $J\subseteq I$，定义**子族复合伪度量**

$$d_J(x,y):=\max_{j\in J}d_j(x,y).$$

由于 $I$ 有限，$d_J$ 仍为扩展伪度量。定义 $S\subseteq\mathcal X$ 在 $d_J$ 下的 $\varepsilon$-**子族覆盖数**为

$$
\mathcal N_J(\varepsilon,S)
:=
\min\bigl\{|A|:A\subseteq S,\ |A|<+\infty,\
S\subseteq\textstyle\bigcup_{a\in A}\{x\in\mathcal X:d_J(x,a)<\varepsilon\}\bigr\}.
$$

若不存在有限内覆盖，则取值为 $+\infty$；由定义，$\mathcal N_J(\varepsilon,\emptyset)=0$。当 $J=\{i\}$ 时，$\mathcal N_J(\varepsilon,S)=\mathcal N_i(\varepsilon,S)$。

**定义（度量熵）**：基于覆盖数定义单分量度量熵：

$$E_{\varepsilon, i}(U) := \log_2 \mathcal{N}_i\bigl(\varepsilon,\, U\bigr)$$

并基于子族覆盖数定义**子族度量熵**

$$
E_{\varepsilon,J}(S):=\log_2\mathcal N_J(\varepsilon,S).
$$

当 $J=\{i\}$ 时，$E_{\varepsilon,J}(S)=E_{\varepsilon,i}(S)$。$E_{\varepsilon, i}$ 与 $E_{\varepsilon,J}$ 对非空子集取值于 $\bar{\mathbb{R}}_+ = [0, +\infty]$；约定空集熵为 $\log_2 0 = -\infty$。

> **约定（对数底数）**：全文固定采用 $\log_2$（以 $2$ 为底的对数）。改换底数时，须先确认所涉及的熵差或熵比在扩展实数中良定，再另行使用换底公式；本书不使用无条件的底数不变性。

### #h-57a1dc05727a3772 算子空间与诱导规范

**定义（算子空间）**：

$$\mathcal{X}_{\mathrm{op}} = \{\, \phi : \mathcal{X} \to \mathcal{X} \;\big|\; \phi(\bot) = \bot \,\}$$

$\phi \in \mathcal{X}_{\mathrm{op}}$ 称为 $\mathcal{X}$ 上的一个**算子**。条件 $\phi(\bot) = \bot$ 保证吸收元在所有算子下不变；$\phi(x) = \bot$ 表示 $\phi$ 在 $x$ 处未定义。指定 $\mathcal{X}_{\mathrm{op}}$ 的**吸收元** $\bot_{\mathrm{op}} \in \mathcal{X}_{\mathrm{op}}$ 为全未定义算子：$\bot_{\mathrm{op}}(x) = \bot$（$\forall x \in \mathcal{X}$）。

定义其**定义域**：

$$\mathrm{dom}(\phi) := \bigl\{\, x \in \mathcal{X} \;\big|\; \phi(x) \neq \bot \,\bigr\}$$

> **约定（公共定义域简写）**：对有限族 $\phi_1,\ldots,\phi_n\in\mathcal{X}_{\mathrm{op}}$（$n\geq1$），记
>
> $$\mathrm{dom}(\phi_1,\ldots,\phi_n) := \bigcap_{r=1}^n\mathrm{dom}(\phi_r).$$
>
> 特别地，$\mathrm{dom}(\phi,\psi)=\mathrm{dom}(\phi)\cap\mathrm{dom}(\psi)$。

由 $\phi(\bot) = \bot$，对所有 $\phi \in \mathcal{X}_{\mathrm{op}}$ 均有 $\bot \notin \mathrm{dom}(\phi)$。定义其**像集**：

$$\mathrm{Im}(\phi) := \phi(\mathrm{dom}(\phi)) = \{\phi(x) : x \in \mathrm{dom}(\phi)\}$$

由定义域排除 $\bot$ 及 $x \in \mathrm{dom}(\phi) \Rightarrow \phi(x) \neq \bot$，故 $\bot \notin \mathrm{Im}(\phi)$。$\bot$ 的作用是将偏函数统一为全函数，$\mathrm{dom}(\phi)$ 与 $\mathrm{Im}(\phi)$ 分别刻画 $\phi$ 给出有意义输出的源点与目标点区域。$\mathcal{X}_{\mathrm{op}}$ 在函数复合下构成**幺半群**：封闭性 $\phi_2 \circ \phi_1 \in \mathcal{X}_{\mathrm{op}}$（由 $(\phi_2 \circ \phi_1)(\bot) = \phi_2(\bot) = \bot$），单位元 $\mathrm{id}_{\mathcal{X}} \in \mathcal{X}_{\mathrm{op}}$，结合律由函数复合的一般性质继承。对有限族 $\phi_1,\ldots,\phi_k\in\mathcal X_{\mathrm{op}}$，本卷按函数复合约定记

$$c_k=\phi_k\circ\cdots\circ\phi_1,$$

并在 $k=0$ 时取 $c_0=\mathrm{id}_{\mathcal X}$。这一记号只使用 $\mathcal X_{\mathrm{op}}$ 的幺半群结构；作为链来读取时见 @h-5a1b95150c3a4df2。

#### 诱导规范结构

对分量伪度量 $d_i \in \mathcal{G}$，定义 $\mathcal{X}_{\mathrm{op}}$ 上的**诱导算子伪度量**：

$$d_{\mathrm{op},i}(\phi, \psi) := \sup_{x \in \mathcal{X}} d_i(\phi(x), \psi(x))$$

记 $\mathcal{G}_{\mathrm{op}} = \{d_{\mathrm{op},i}\}_{i \in I}$。

> **注（算子规范的选择）**：上述逐点上确界给出的是本书固定采用的 sup 型算子规范。除非另有说明，后文 $\mathcal{G}_{\mathrm{op}}$ 均指这一 sup 型诱导规范；其他可能的算子规范不在本章讨论范围内。

**命题 #h-91e0e3c458eb7786（算子规范空间）**：$d_{\mathrm{op},i}$ 是 $\mathcal{X}_{\mathrm{op}}$ 上的扩展伪度量，$(\mathcal{X}_{\mathrm{op}}, \mathcal{G}_{\mathrm{op}}, \bot_{\mathrm{op}})$ 构成扩展规范空间。

**证明**：

- 非吸收部分非空：由 @h-b4babd684de7c112，取 $z\in\mathcal X$ 且 $z\neq\bot$。恒等算子 $\mathrm{id}_{\mathcal X}$ 满足 $\mathrm{id}_{\mathcal X}(z)=z\neq\bot$，故 $\mathrm{id}_{\mathcal X}\neq\bot_{\mathrm{op}}$。
- 自距零：$d_{\mathrm{op},i}(\phi, \phi) = \sup_x d_i(\phi(x), \phi(x)) = 0$。
- 对称性：由 $d_i$ 的对称性逐点继承。
- 三角不等式：对任意 $x$，$d_i(\phi(x), \chi(x)) \leq d_i(\phi(x), \psi(x)) + d_i(\psi(x), \chi(x))$。取 $\sup_x$ 并用 $\sup(f+g) \leq \sup f + \sup g$ 即得。
- 吸收元隔离：对 $\phi \neq \bot_{\mathrm{op}}$，存在 $x_0 \in \mathrm{dom}(\phi)$，故 $d_{\mathrm{op},i}(\phi, \bot_{\mathrm{op}}) \geq d_i(\phi(x_0), \bot) = +\infty$。$\square$

> **注 #h-038952f7c6c1d6e5（定义域隔离）**：$\mathrm{dom}(\phi) \neq \mathrm{dom}(\psi)$ 蕴含 $d_{\mathrm{op},i}(\phi, \psi) = +\infty$（$\forall i \in I$）。
>
> **证明**：对称差非空，不失一般性取
>
> $$x_0 \in \mathrm{dom}(\phi) \setminus \mathrm{dom}(\psi).$$
>
> 则
>
> $$\psi(x_0)=\bot,\qquad d_i(\phi(x_0),\bot)=+\infty.$$
>
> 另一侧由 $d_{\mathrm{op},i}$ 的对称性给出。因此，对每个固定的 $i\in I$，由相同定义域确定的子集
>
> $$\mathcal{X}_{\mathrm{op},D}=\{\phi\in\mathcal{X}_{\mathrm{op}}:\mathrm{dom}(\phi)=D\}$$
>
> 在 $d_{\mathrm{op},i}$ 下彼此 $+\infty$-隔离：若 $D_1\ne D_2$、$\phi\in\mathcal{X}_{\mathrm{op},D_1}$、$\psi\in\mathcal{X}_{\mathrm{op},D_2}$，则 $d_{\mathrm{op},i}(\phi,\psi)=+\infty$。这只是诱导伪度量对不同定义域子集的距离性质，不表示 $\mathcal{X}_{\mathrm{op}}$ 作为集合额外带有独立分块结构。

#### 受限评估

对 $U \subseteq \mathcal{X}$，记**受限评估**：

$$d_{\mathrm{op},i}(\phi, \psi)\big|_U := \sup_{x \in U} d_i(\phi(x), \psi(x))$$

当 $U=\emptyset$ 时，上确界按约定取 $0$。

> **注 #h-1c441b84eff949c6（受限评估的伪度量性质与局限）**：对固定 $U$，$d_{\mathrm{op},i}(\cdot, \cdot)\big|_U$ 满足自距零、对称、三角不等式（前三条扩展伪度量公理），并且恒有
>
> $$d_{\mathrm{op},i}(\phi, \psi)\big|_U \leq d_{\mathrm{op},i}(\phi, \psi).$$
>
> 但 $d_{\mathrm{op},i}(\cdot, \cdot)\big|_U$ 一般不满足吸收元隔离（公理 (iv)），因此作为推导工具使用，不构成 @h-b4babd684de7c112 意义下的扩展规范空间。
>
> **证明**：前三条公理逐点继承，并在同一个 $U$ 上取上确界；全域上界由 $U\subseteq\mathcal{X}$ 直接给出。
>
> 若 $U=\emptyset$ 且 $\phi\neq\bot_{\mathrm{op}}$，则
>
> $$d_{\mathrm{op},i}(\phi,\bot_{\mathrm{op}})\big|_\emptyset=0,$$
>
> 不能给出 $+\infty$ 隔离。

> **注（受限评估的三角不等式）**：三角不等式只在固定同一个 $U$ 的受限评估中使用。当三项分别取不同限制域时，本书不把这些量视为同一个伪度量上的三角结构。受限评估将度量比较限定在特定子集（如上游像集或某个局部评估域），不计入 $U$ 外点的差异，因此可用于局部误差估计。

至此，底层集合、吸收元、分量伪度量族与算子空间都落入同一种规范语言。扩展规范空间描述点与集合的分量化可分辨性，$\mathcal{X}_{\mathrm{op}}$ 把偏定义过程写成保持吸收元的自映射，算子伪度量则把映射之间的差异重新写回分量距离。

----
*[OE] ⊢ [GLENZLI] ⊢ [卷 01] ⊢ [01-foundations] ⊢ [e23547c1df69ac70]*
