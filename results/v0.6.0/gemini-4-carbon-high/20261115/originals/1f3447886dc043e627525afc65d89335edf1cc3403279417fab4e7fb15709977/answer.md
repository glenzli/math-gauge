以下按共同设定逐阶段作答。全文记 $\mathcal{F}$ 为 $E'$ 的全体有限维线性子空间之族（含零子空间 $\{0\}$），对任意拓扑向量空间 $X$ 上的扩展实值函数 $u:X\to[-\infty,+\infty]$，严格按题设以实高度上图
$$\operatorname{epi}_{\mathbb{R}}(u)=\{(x,t)\in X\times\mathbb{R}:u(x)\le t\}$$
在乘积拓扑下的闭性与凸性定义 $u$ 的下半连续性与凸性。

---

## S1　原始记录

### 1. $g_F$ 非负、凸且至少一点有限

设 $F\in\mathcal{F}$。

1. **非负性（取值于 $[0,+\infty]$）**：  
   对任意 $y\in F^*$，集合 $M_y:=\{f(x):x\in E,\ q_Fx=y\}\subset[0,+\infty]$。因对所有 $x\in E$ 有 $f(x)\ge 0$，$0$ 是 $M_y$ 的下界（若纤维 $\{x\in E:q_Fx=y\}$ 为空，按约定 $g_F(y)=\inf\emptyset=+\infty\ge 0$）。故对所有 $y\in F^*$ 有 $g_F(y)=\inf M_y\in[0,+\infty]$。

2. **至少一点有限**：  
   由共同设定，存在 $x_0\in E$ 使 $f(x_0)<+\infty$（且 $f(x_0)\ge 0$）。令 $y_0:=q_F(x_0)\in F^*$，则 $x_0$ 属于纤维 $\{x\in E:q_Fx=y_0\}$，故
   $$0\le g_F(y_0)=\inf\{f(x):q_Fx=y_0\}\le f(x_0)<+\infty,$$
   即 $g_F$ 在 $y_0$ 处有限。

3. **凸性（$\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^*\times\mathbb{R}$ 中凸）**：  
   先验算 $q_F:E\to F^*$ 的线性性：对任意 $x_1,x_2\in E$、$\alpha,\beta\in\mathbb{R}$ 及 $\varphi\in F$，由 $\varphi\in E'$ 的线性性有
   $$q_F(\alpha x_1+\beta x_2)(\varphi)=\varphi(\alpha x_1+\beta x_2)=\alpha\varphi(x_1)+\beta\varphi(x_2)=(\alpha q_Fx_1+\beta q_Fx_2)(\varphi),$$
   故 $q_F$ 线性。  
   任取 $(y_1,t_1),(y_2,t_2)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 及 $\lambda\in[0,1]$。若 $\lambda=0$ 或 $\lambda=1$，凸组合即为 $(y_2,t_2)$ 或 $(y_1,t_1)$，已在 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 中。下设 $\lambda\in(0,1)$，记 $y:=\lambda y_1+(1-\lambda)y_2\in F^*$，$t:=\lambda t_1+(1-\lambda)t_2\in\mathbb{R}$。  
   对任意 $\varepsilon>0$，因 $g_F(y_i)\le t_i<t_i+\varepsilon$（$i=1,2$），由下确界定义（并注意到 $g_F(y_i)<+\infty$ 保证对应纤维非空），存在 $x_1,x_2\in E$ 使得
   $$q_Fx_1=y_1,\quad f(x_1)\le t_1+\varepsilon;\qquad q_Fx_2=y_2,\quad f(x_2)\le t_2+\varepsilon.$$
   即 $(x_1,t_1+\varepsilon),(x_2,t_2+\varepsilon)\in\operatorname{epi}_{\mathbb{R}}(f)$。由共同设定 $f$ 凸，即 $\operatorname{epi}_{\mathbb{R}}(f)$ 在 $E\times\mathbb{R}$ 中凸，故其凸组合
   $$(\lambda x_1+(1-\lambda)x_2,\ \lambda(t_1+\varepsilon)+(1-\lambda)(t_2+\varepsilon))=(\lambda x_1+(1-\lambda)x_2,\ t+\varepsilon)\in\operatorname{epi}_{\mathbb{R}}(f),$$
   即 $f(\lambda x_1+(1-\lambda)x_2)\le t+\varepsilon$。又由 $q_F$ 线性，
   $$q_F(\lambda x_1+(1-\lambda)x_2)=\lambda q_Fx_1+(1-\lambda)q_Fx_2=\lambda y_1+(1-\lambda)y_2=y,$$
   故 $g_F(y)\le f(\lambda x_1+(1-\lambda)x_2)\le t+\varepsilon$。由 $\varepsilon>0$ 的任意性，令 $\varepsilon\downarrow 0$ 得 $g_F(y)\le t$，即 $(y,t)\in\operatorname{epi}_{\mathbb{R}}(g_F)$。因此 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 为凸集，$g_F$ 凸。

### 2. 限制相容公式 $g_F(y)=\inf_{r_{KF}z=y}g_K(z)$

设 $F,K\in\mathcal{F}$ 且 $F\subset K$。对任意 $x\in E$ 与 $\varphi\in F\subset K$，
$$(r_{KF}(q_Kx))(\varphi)=(q_Kx)(\varphi)=\varphi(x)=(q_Fx)(\varphi),$$
故恒有 $r_{KF}\circ q_K=q_F$。固定 $y\in F^*$，记 $I:=\inf_{r_{KF}z=y}g_K(z)$。

- **证明 $g_F(y)\le I$**：任取满足 $r_{KF}z=y$ 的 $z\in K^*$。对任意满足 $q_Kx=z$ 的 $x\in E$，有 $q_Fx=r_{KF}(q_Kx)=r_{KF}z=y$，故 $g_F(y)\le f(x)$。因此 $g_F(y)$ 是 $\{f(x):q_Kx=z\}$ 的下界（若该集为空，其下确界为 $+\infty\ge g_F(y)$ 仍成立），取下确界得 $g_F(y)\le g_K(z)$。再对所有满足 $r_{KF}z=y$ 的 $z\in K^*$ 取下确界（空集情形同理），得 $g_F(y)\le I$。
- **证明 $I\le g_F(y)$**：任取满足 $q_Fx=y$ 的 $x\in E$，令 $z_x:=q_Kx\in K^*$。则 $r_{KF}z_x=r_{KF}(q_Kx)=q_Fx=y$，且由 $g_K(z_x)$ 的定义有 $g_K(z_x)\le f(x)$。于是 $I\le g_K(z_x)\le f(x)$。因 $I$ 是 $\{f(x):q_Fx=y\}$ 的下界（若该纤维为空，则 $g_F(y)=+\infty\ge I$ 亦成立），取下确界得 $I\le g_F(y)$。

综上，$g_F(y)=\inf_{r_{KF}z=y}g_K(z)$。

### 3. 是否需要纤维下确界取到

**不需要**。上述全部论证均不要求定义 $g_F$、$g_K$ 或 $\inf_{r_{KF}z=y}g_K(z)$ 的任何纤维下确界被取到：
- 非负性与至少一点有限仅用到下界 $0\le f$ 与单个有限点 $x_0\in\operatorname{dom}(f)$ 给出的上界 $g_F(q_Fx_0)\le f(x_0)$；
- $g_F$ 的凸性通过任意 $\varepsilon>0$ 的 $\varepsilon$-近似极小点（$f(x_i)\le t_i+\varepsilon$）结合 $\varepsilon\downarrow 0$ 完成，无需精确极小点；
- $g_F(y)=\inf_{r_{KF}z=y}g_K(z)$ 仅利用恒等式 $r_{KF}\circ q_K=q_F$ 与下确界的序刻画（$c\le\inf S\iff\forall s\in S,\ c\le s$）。（事实上在共同设定下纤维下确界一般未必取到，如 $E=\mathbb{R},F=\{0\},f(x)=e^{-x}$ 时 $g_{\{0\}}(0)=0$ 就不被取到。）

---

## S2　紧次水平集

先建立仅依赖**共同设定**的有限维对偶拓扑引理（以便后续阶段在不假定 S2 附加条件时亦可合法援引）：

> **引理 A（有限维观测空间的拓扑性质，仅依赖共同设定）**  
> 对任意 $F\in\mathcal{F}$，$F^*$ 是 Hausdorff 拓扑向量空间，$q_F:E\to F^*$ 连续线性；对任意 $\varphi\in F$，求值泛函 $\operatorname{ev}_\varphi:F^*\to\mathbb{R}$（$y\mapsto y(\varphi)$）连续线性；若 $F\subset K$（$K\in\mathcal{F}$），则限制映射 $r_{KF}:K^*\to F^*$ 连续线性。
>
> **证明**：$q_F,\operatorname{ev}_\varphi,r_{KF}$ 的线性性直接由定义验证。设 $d=\dim F<\infty$。  
> - 若 $d=0$（即 $F=\{0\}$），则 $F^*=\{0\}$ 为单点空间，其唯一拓扑平凡地是 Hausdorff 线性拓扑，映入 $\{0\}$ 的常值映射 $q_{\{0\}},r_{K,\{0\}}$ 与零映射 $\operatorname{ev}_0$ 均连续。  
> - 若 $d\ge 1$，取 $F$ 的一组线性基 $\varphi_1,\dots,\varphi_d$。由有限维实向量空间上 Hausdorff 线性拓扑的唯一性（即题设“有限维拓扑”），双射线性映射 $T_F:F^*\to\mathbb{R}^d$，$T_F(y)=(y(\varphi_1),\dots,y(\varphi_d))$ 是到标准欧氏空间 $\mathbb{R}^d$ 的线性同胚。因 $\mathbb{R}^d$ 是 Hausdorff 空间，故 $F^*$ 为 Hausdorff 空间。又 $(T_F\circ q_F)(x)=(\varphi_1(x),\dots,\varphi_d(x))$，而每个 $\varphi_i\in F\subset E'$ 在 $E$ 上连续，由乘积拓扑的泛性质知 $T_F\circ q_F:E\to\mathbb{R}^d$ 连续，从而 $q_F=T_F^{-1}\circ(T_F\circ q_F)$ 连续。对任意 $\varphi=\sum_{i=1}^d c_i\varphi_i\in F$，$\operatorname{ev}_\varphi(y)=\sum_{i=1}^d c_i y(\varphi_i)$ 为 $T_F$ 各坐标分量的线性组合，故连续。若 $F\subset K\in\mathcal{F}$，将 $\varphi_1,\dots,\varphi_d$ 扩充为 $K$ 的基 $\varphi_1,\dots,\varphi_m$，则 $T_F\circ r_{KF}\circ T_K^{-1}:\mathbb{R}^m\to\mathbb{R}^d$ 为前 $d$ 个坐标的投影，连续，故 $r_{KF}$ 连续。$\blacksquare$

现在回到 S2 条件（共同设定 + $f$ 下半连续 + 对每个 $c\in\mathbb{R}$，次水平集 $S_c:=\{x\in E:f(x)\le c\}$ 紧），固定 $F\in\mathcal{F}$。

### 1. 当 $g_F(y)<\infty$ 时纤维下确界取到

设 $y\in F^*$ 满足 $m:=g_F(y)<+\infty$。由 S1（其条件即为共同设定，在 S2 下成立）知 $m\ge 0$，故 $m\in[0,+\infty)$。对每个整数 $n\ge 1$，定义
$$K_n:=S_{m+\frac{1}{n}}\cap q_F^{-1}(\{y\})=\left\{x\in E:f(x)\le m+\tfrac{1}{n},\ q_Fx=y\right\}.$$
核验紧集有限交性质的条件：
1. **非空与递减性**：因 $m=\inf\{f(x):q_Fx=y\}<m+\frac{1}{n}$，由下确界定义存在 $x_n\in E$ 使 $q_Fx_n=y$ 且 $f(x_n)\le m+\frac{1}{n}$，故 $x_n\in K_n\neq\emptyset$。显然 $K_1\supset K_2\supset\cdots$，从而 $\{K_n\}_{n\ge 1}$ 具有有限交性质（任一有限子族之交等于其中下标最大者，非空）。
2. **紧空间的闭子集**：由 S2 假设，$S_{m+1}$ 是 $E$ 的紧子集，且对每个 $n\ge 1$，$S_{m+1/n}\subset S_{m+1}$ 紧。因 $E$ 为 Hausdorff 空间，紧集 $S_{m+1/n}$ 在 $E$ 中闭（亦可由 $\operatorname{epi}_{\mathbb{R}}(f)$ 闭及连续映射 $x\mapsto(x,m+\frac{1}{n})$ 的原像为闭集得出）。又由引理 A，$F^*$ 为 Hausdorff 空间故单点集 $\{y\}$ 在 $F^*$ 中闭，再由 $q_F$ 连续知 $q_F^{-1}(\{y\})$ 在 $E$ 中闭。因此每个 $K_n$ 都是紧空间 $S_{m+1}$ 的非空闭子集。

由紧空间的有限交刻画定理，$\bigcap_{n=1}^\infty K_n\neq\emptyset$。取 $x_*\in\bigcap_{n=1}^\infty K_n$，则 $q_Fx_*=y$（故 $g_F(y)\le f(x_*)$），且对一切 $n\ge 1$ 有 $f(x_*)\le m+\frac{1}{n}$，令 $n\to\infty$ 得 $f(x_*)\le m=g_F(y)$。故 $f(x_*)=g_F(y)$，纤维下确界在 $x_*$ 处取到。

### 2. 各 $g_F$ 下半连续

先证对每个 $c\in\mathbb{R}$，次水平集 $D_c:=\{y\in F^*:g_F(y)\le c\}$ 满足
$$D_c=q_F(S_c).$$
- 若 $y\in q_F(S_c)$，则存在 $x\in S_c$ 使 $q_Fx=y$ 且 $f(x)\le c$，故 $g_F(y)\le f(x)\le c$，即 $y\in D_c$。
- 反之，若 $y\in D_c$，则 $g_F(y)\le c<+\infty$。由上段已证的纤维下确界可达性，存在 $x_*\in E$ 使 $q_Fx_*=y$ 且 $f(x_*)=g_F(y)\le c$，即 $x_*\in S_c$，故 $y=q_Fx_*\in q_F(S_c)$。

由 S2 假设，$S_c$ 在 $E$ 中紧；由引理 A，$q_F:E\to F^*$ 连续，紧集的连续像紧，故 $D_c=q_F(S_c)$ 在 $F^*$ 中紧。再由引理 A 知 $F^*$ 为 Hausdorff 空间，Hausdorff 空间的紧子集必为闭集，故对一切 $c\in\mathbb{R}$，$D_c$ 在 $F^*$ 中闭。

据此证明 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^*\times\mathbb{R}$ 中闭：任取 $(y_0,t_0)\in(F^*\times\mathbb{R})\setminus\operatorname{epi}_{\mathbb{R}}(g_F)$，则 $t_0<g_F(y_0)$。取实数 $c\in(t_0,g_F(y_0))$。因 $D_c$ 在 $F^*$ 中闭且 $y_0\notin D_c$，$U:=F^*\setminus D_c=\{y\in F^*:g_F(y)>c\}$ 是 $y_0$ 在 $F^*$ 中的开邻域，从而 $U\times(-\infty,c)$ 是 $(y_0,t_0)$ 在乘积空间 $F^*\times\mathbb{R}$ 中的开邻域。对任意 $(y,t)\in U\times(-\infty,c)$，有 $t<c<g_F(y)$，故 $(y,t)\notin\operatorname{epi}_{\mathbb{R}}(g_F)$。因此 $(F^*\times\mathbb{R})\setminus\operatorname{epi}_{\mathbb{R}}(g_F)$ 为开集，$\operatorname{epi}_{\mathbb{R}}(g_F)$ 为闭集，即 $g_F$ 下半连续。

---

## S3　兼容成本记录的实现

在 S2 条件下（共同设定、引理 A、S1 与 S2 的结论均适用），记 $S_c:=\{z\in E:f(z)\le c\}$。对每个 $F\in\mathcal{F}$，定义
$$A_F:=S_c\cap q_F^{-1}(\{y_F\})=\{z\in E:f(z)\le c,\ q_Fz=y_F\},$$
并构造总体交集
$$A:=\bigcap_{F\in\mathcal{F}}A_F=\{z\in E:f(z)\le c\text{ 且对所有 }F\in\mathcal{F}\text{ 有 }q_Fz=y_F\}.$$
以下证明 $A$ 恰为单点集 $\{x\}$，从而取 $x$ 为 $\bigcap_{F\in\mathcal{F}}A_F$ 的唯一元素即完成构造并满足全部性质。

1. **每个 $A_F$ 为紧空间 $S_c$ 的非空闭子集**：  
   由 S2 条件，因 $c\in\mathbb{R}$，$S_c$ 是 $E$ 的紧子集。对每个 $F\in\mathcal{F}$，题设给出 $g_F(y_F)\le c<+\infty$，满足 S2 中纤维下确界可达的条件，故存在 $x_F\in E$ 使 $q_Fx_F=y_F$ 且 $f(x_F)=g_F(y_F)\le c$，即 $x_F\in A_F\neq\emptyset$。又由引理 A，$F^*$ 为 Hausdorff 空间且 $q_F$ 连续，故 $q_F^{-1}(\{y_F\})$ 在 $E$ 中闭，从而 $A_F=S_c\cap q_F^{-1}(\{y_F\})$ 是紧空间 $S_c$ 的非空闭子集（特别地，$\{0\}\in\mathcal{F}$ 给出 $S_c\supset A_{\{0\}}\neq\emptyset$）。

2. **反单调性与有限交性质（存在性）**：  
   若 $F,K\in\mathcal{F}$ 且 $F\subset K$，任取 $z\in A_K$，则 $f(z)\le c$ 且 $q_Kz=y_K$。结合 S1 的恒等式 $r_{KF}\circ q_K=q_F$ 与题设相容条件 $r_{KF}y_K=y_F$，有
   $$q_Fz=r_{KF}(q_Kz)=r_{KF}y_K=y_F,$$
   故 $z\in A_F$，即 $A_K\subset A_F$。  
   现任取有限个 $F_1,\dots,F_m\in\mathcal{F}$（$m\ge 1$），令线性子空间之和 $K:=F_1+\cdots+F_m\subset E'$。因每个 $F_i$ 有限维，$\dim K\le\sum_{i=1}^m\dim F_i<\infty$，故 $K\in\mathcal{F}$ 且对一切 $i=1,\dots,m$ 有 $F_i\subset K$。由反单调性得
   $$\emptyset\neq A_K\subset\bigcap_{i=1}^m A_{F_i}.$$
   故非空闭集族 $\{A_F\}_{F\in\mathcal{F}}$ 在紧空间 $S_c$ 中具有有限交性质。由紧空间的有限交刻画定理，$A=\bigcap_{F\in\mathcal{F}}A_F\neq\emptyset$。任取 $x\in A$，由 $A$ 的定义即满足对所有 $F\in\mathcal{F}$ 有 $q_Fx=y_F$ 且 $f(x)\le c$。

3. **在全空间 $E$ 中的唯一性**：  
   设 $x_1,x_2\in E$ 均满足对所有 $F\in\mathcal{F}$ 有 $q_Fx_1=y_F=q_Fx_2$。任取 $\varphi\in E'$，令一维（当 $\varphi=0$ 时为零维）线性子空间 $F_\varphi:=\mathbb{R}\varphi\in\mathcal{F}$，则 $\varphi\in F_\varphi$，故
   $$\varphi(x_1-x_2)=\varphi(x_1)-\varphi(x_2)=q_{F_\varphi}(x_1)(\varphi)-q_{F_\varphi}(x_2)(\varphi)=y_{F_\varphi}(\varphi)-y_{F_\varphi}(\varphi)=0.$$
   因此对一切 $\varphi\in E'$ 均有 $\varphi(x_1-x_2)=0$。  
   援引 **Hausdorff 局部凸空间的 Hahn–Banach 点分离定理**：在实 Hausdorff 局部凸空间 $E$ 中，连续对偶 $E'$ 分离点（若 $v\in E\setminus\{0\}$，因 $E$ 是 Hausdorff 局部凸空间，$\{0\}$ 与 $\{v\}$ 是不相交的非空紧凸集，由 Hahn–Banach 分离定理存在 $\varphi\in E'$ 使 $\varphi(v)\neq\varphi(0)=0$）。由共同设定，$E$ 是实 Hausdorff 局部凸空间，适用该定理，故 $x_1-x_2=0$，即 $x_1=x_2$。

综上，$A=\{x\}$ 为单点集，定义为该交集唯一元素的 $x\in E$ 是使“对所有 $F\in\mathcal{F}$ 有 $q_Fx=y_F$ 且 $f(x)\le c$”成立的唯一点。

---

## S4　一般成本的恢复

**结论：能。** 以下仅使用共同设定（及仅依赖共同设定的 S1 与 S2 中引理 A），给出 $G$ 由全部 $g_F$ 的显式构造、完整验证及扩大观测空间时的关系。

### 1. 预备引理：非负凸函数的闭上图包络

> **引理 B（闭实高度上图包络）**  
> 设 $X$ 为实拓扑向量空间，$u:X\to[0,+\infty]$ 凸（即 $\operatorname{epi}_{\mathbb{R}}(u)$ 在 $X\times\mathbb{R}$ 中凸）。记 $C:=\overline{\operatorname{epi}_{\mathbb{R}}(u)}$ 为 $\operatorname{epi}_{\mathbb{R}}(u)$ 在乘积空间 $X\times\mathbb{R}$ 中的闭包，定义
> $$u^{\mathrm{cl}}(x):=\inf\{t\in\mathbb{R}:(x,t)\in C\}\qquad(\text{约定 }\inf\emptyset=+\infty).$$
> 则：
> 1. $u^{\mathrm{cl}}:X\to[0,+\infty]$，且 $\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})=C=\overline{\operatorname{epi}_{\mathbb{R}}(u)}$；
> 2. $u^{\mathrm{cl}}$ 下半连续、凸，且 $u^{\mathrm{cl}}\le u$；
> 3. 对任意下半连续函数 $h:X\to[-\infty,+\infty]$（无需假定凸，允许同时取 $-\infty$ 与 $+\infty$），若 $h\le u$，则 $h\le u^{\mathrm{cl}}$。
>
> **证明**：  
> (1) 因 $u\ge 0$，$\operatorname{epi}_{\mathbb{R}}(u)\subset X\times[0,+\infty)$；后者在 $X\times\mathbb{R}$ 中闭，故 $C\subset X\times[0,+\infty)$，从而 $u^{\mathrm{cl}}(x)\in[0,+\infty]$。又对任意 $\delta\ge 0$，平移映射 $\tau_\delta(x,t)=(x,t+\delta)$ 是 $X\times\mathbb{R}$ 的同胚且 $\tau_\delta(\operatorname{epi}_{\mathbb{R}}(u))\subset\operatorname{epi}_{\mathbb{R}}(u)$，故 $\tau_\delta(C)\subset\overline{\tau_\delta(\operatorname{epi}_{\mathbb{R}}(u))}\subset C$，即 $(x,r)\in C$ 且 $s\ge r\implies(x,s)\in C$。由此：若 $(x,t)\in C$，显然 $u^{\mathrm{cl}}(x)\le t$，即 $C\subset\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})$；反之若 $(x,t)\in\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})$（即 $u^{\mathrm{cl}}(x)\le t\in\mathbb{R}$），对每个 $n\ge 1$ 存在 $r_n<t+\frac{1}{n}$ 使 $(x,r_n)\in C$，由向上封闭性得 $(x,t+\frac{1}{n})\in C$，令 $n\to\infty$ 并由 $C$ 闭得 $(x,t)\in C$。故 $\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})=C$。  
> (2) $\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})=C$ 为闭集，故 $u^{\mathrm{cl}}$ 下半连续。在实拓扑向量空间 $X\times\mathbb{R}$ 中，对任意 $\lambda\in[0,1]$，连续映射 $m_\lambda((p_1,p_2))=\lambda p_1+(1-\lambda)p_2$ 满足 $m_\lambda(\operatorname{epi}_{\mathbb{R}}(u)\times\operatorname{epi}_{\mathbb{R}}(u))\subset\operatorname{epi}_{\mathbb{R}}(u)\subset C$；因乘积拓扑中 $C\times C=\overline{\operatorname{epi}_{\mathbb{R}}(u)\times\operatorname{epi}_{\mathbb{R}}(u)}$ 且 $m_\lambda^{-1}(C)$ 闭，故 $m_\lambda(C\times C)\subset C$，即 $C$ 凸，$u^{\mathrm{cl}}$ 凸。又由 $\operatorname{epi}_{\mathbb{R}}(u)\subset C=\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})$ 即得 $u^{\mathrm{cl}}\le u$。  
> (3) 若 $h:X\to[-\infty,+\infty]$ 下半连续且 $h\le u$，则对任意 $(x,t)\in\operatorname{epi}_{\mathbb{R}}(u)$ 有 $h(x)\le u(x)\le t$（即使 $h(x)=-\infty$ 亦满足 $-\infty\le t$），故 $\operatorname{epi}_{\mathbb{R}}(u)\subset\operatorname{epi}_{\mathbb{R}}(h)$。因 $\operatorname{epi}_{\mathbb{R}}(h)$ 闭，取闭包得 $\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})=C\subset\operatorname{epi}_{\mathbb{R}}(h)$。对任意 $x\in X$：若 $u^{\mathrm{cl}}(x)=+\infty$，显然 $h(x)\le+\infty$；若 $u^{\mathrm{cl}}(x)=t\in[0,+\infty)$，则 $(x,t)\in\operatorname{epi}_{\mathbb{R}}(u^{\mathrm{cl}})\subset\operatorname{epi}_{\mathbb{R}}(h)$，故 $h(x)\le t=u^{\mathrm{cl}}(x)$。$\blacksquare$

### 2. 由全部 $g_F$ 构造 $G$

对每个 $F\in\mathcal{F}$，由 S1 知 $g_F:F^*\to[0,+\infty]$ 非负且凸，结合引理 A 知 $F^*$ 为实拓扑向量空间，故对 $(F^*,g_F)$ 适用引理 B：仅由 $g_F$ 定义 $F^*$ 上的闭上图恢复
$$G_F(y):=g_F^{\mathrm{cl}}(y)=\inf\left\{t\in\mathbb{R}:(y,t)\in\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}\right\}\qquad(y\in F^*),$$
及其在 $E$ 上的拉回观测恢复 $\widetilde{G}_F(x):=G_F(q_Fx)$（$x\in E$）。进而由全部 $\{g_F\}_{F\in\mathcal{F}}$ 构造 $G:E\to[0,+\infty]$ 为
$$G(x):=\sup_{F\in\mathcal{F}}\widetilde{G}_F(x)=\sup_{F\in\mathcal{F}}G_F(q_Fx)\qquad(x\in E).$$
（注：不能直接取 $\sup_F g_F(q_Fx)$，因为当 $f$ 不下半连续时，例如 $E=\mathbb{R},F=E'$ 时 $g_F(q_Fx)=f(x)$ 本身不下半连续；必须先对每个 $g_F$ 取上图闭包 $G_F$。）

### 3. 扩大观测空间时的关系

设 $F,K\in\mathcal{F}$ 且 $F\subset K$。
1. **$K^*$ 与 $F^*$ 上的投影单调性**：由引理 A，$r_{KF}:K^*\to F^*$ 连续线性，故 $R_{KF}:=r_{KF}\times\operatorname{id}_{\mathbb{R}}:K^*\times\mathbb{R}\to F^*\times\mathbb{R}$ 连续线性。对任意 $(z,t)\in\operatorname{epi}_{\mathbb{R}}(g_K)$，由 S1 知 $g_F(r_{KF}z)=\inf_{r_{KF}z'=r_{KF}z}g_K(z')\le g_K(z)\le t$，故
   $$R_{KF}(z,t)=(r_{KF}z,t)\in\operatorname{epi}_{\mathbb{R}}(g_F)\subset\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}=\operatorname{epi}_{\mathbb{R}}(G_F),$$
   即 $\operatorname{epi}_{\mathbb{R}}(g_K)\subset R_{KF}^{-1}(\operatorname{epi}_{\mathbb{R}}(G_F))$。因 $R_{KF}$ 连续且 $\operatorname{epi}_{\mathbb{R}}(G_F)$ 闭，右端在 $K^*\times\mathbb{R}$ 中闭，取闭包得 $\operatorname{epi}_{\mathbb{R}}(G_K)=\overline{\operatorname{epi}_{\mathbb{R}}(g_K)}\subset R_{KF}^{-1}(\operatorname{epi}_{\mathbb{R}}(G_F))$，从而
   $$G_F(r_{KF}z)\le G_K(z)\quad(\forall z\in K^*),\qquad G_F(y)\le\inf_{r_{KF}z=y}G_K(z)\le g_F(y)\quad(\forall y\in F^*).$$
2. **$E$ 上观测恢复的单调定向网关系**：在 $G_F(r_{KF}z)\le G_K(z)$ 中代入 $z=q_Kx$ 并用 $r_{KF}\circ q_K=q_F$，得扩大观测空间时的单调性：
   $$F\subset K\implies \widetilde{G}_F(x)=G_F(q_Fx)\le G_K(q_Kx)=\widetilde{G}_K(x)\le G(x)\qquad(\forall x\in E).$$
   因 $(\mathcal{F},\subset)$ 向上定向（对任意 $F_1,F_2\in\mathcal{F}$，$F_1+F_2\in\mathcal{F}$ 同时包含二者），$(\widetilde{G}_F)_{F\in\mathcal{F}}$ 构成递增定向网，故 $G(x)=\sup_{F\in\mathcal{F}}\widetilde{G}_F(x)=\lim_{F\in\mathcal{F}}\widetilde{G}_F(x)$（对 $\mathcal{F}$ 的任意共终子族取上确界亦给出同一 $G$）。

### 4. 验证 $G$ 的全部所需性质

1. **值域与 $G\le f$**：因 $\mathcal{F}\neq\emptyset$（$\{0\}\in\mathcal{F}$）且由引理 B(1) 每个 $G_F$ 取值于 $[0,+\infty]$，故 $G:E\to[0,+\infty]$。对任意 $F\in\mathcal{F}$ 与 $x\in E$，由引理 B(2) 及 $g_F$ 定义有 $G_F(q_Fx)\le g_F(q_Fx)\le f(x)$，对 $F\in\mathcal{F}$ 取上确界得 $G(x)\le f(x)$。
2. **$G$ 下半连续且凸**：对任意 $(x,t)\in E\times\mathbb{R}$，
   $$(x,t)\in\operatorname{epi}_{\mathbb{R}}(G)\iff\forall F\in\mathcal{F},\ G_F(q_Fx)\le t\iff(x,t)\in\bigcap_{F\in\mathcal{F}}(q_F\times\operatorname{id}_{\mathbb{R}})^{-1}\big(\operatorname{epi}_{\mathbb{R}}(G_F)\big).$$
   由引理 A，$\Phi_F:=q_F\times\operatorname{id}_{\mathbb{R}}:E\times\mathbb{R}\to F^*\times\mathbb{R}$ 连续线性；由引理 B(2)，$\operatorname{epi}_{\mathbb{R}}(G_F)$ 在 $F^*\times\mathbb{R}$ 中闭且凸，故其连续线性原像 $\Phi_F^{-1}(\operatorname{epi}_{\mathbb{R}}(G_F))$ 在 $E\times\mathbb{R}$ 中闭且凸。任意族闭凸集之交仍闭且凸，故 $\operatorname{epi}_{\mathbb{R}}(G)$ 在 $E\times\mathbb{R}$ 中闭且凸，即 $G$ 下半连续且凸。
3. **极大性（对竞争函数 $h$ 成立 $h\le G$）**：  
   任取下半连续、凸的竞争函数 $h:E\to[-\infty,+\infty]$（允许同时取 $-\infty$ 与 $+\infty$）满足 $h\le f$。反证：若存在 $x_0\in E$ 使 $h(x_0)>G(x_0)$，因 $G(x_0)\ge 0$，必有 $G(x_0)\in[0,+\infty)$ 且 $h(x_0)\in(G(x_0),+\infty]$，故可取实数 $t_0\in\mathbb{R}$ 使
   $$G(x_0)<t_0<h(x_0).$$
   记 $K_0:=\{(x_0,t_0)\}$，$H:=\operatorname{epi}_{\mathbb{R}}(h)\subset E\times\mathbb{R}$。核验 **局部凸空间的 Hahn–Banach 严格分离定理**的条件：
   - **空间局部凸性**：由共同设定 $E$ 为实（Hausdorff）局部凸空间，$\mathbb{R}$ 为实 Hausdorff 局部凸空间，二者乘积空间 $Z:=E\times\mathbb{R}$ 仍是实（Hausdorff）局部凸空间；
   - **紧凸集与闭凸集非空且不相交**：单点集 $K_0$ 非空、紧且凸；由 $h$ 下半连续且凸知 $H$ 闭且凸；由共同设定存在 $\hat x\in E$ 使 $f(\hat x)<+\infty$（且 $\ge 0$），再由 $h\le f$ 得 $h(\hat x)\le f(\hat x)\in\mathbb{R}$（即使 $h(\hat x)=-\infty$ 亦成立），故 $(\hat x,f(\hat x))\in H$，即 $H\neq\emptyset$；又因 $t_0<h(x_0)$，$(x_0,t_0)\notin H$，即 $K_0\cap H=\emptyset$。

   因此 Hahn–Banach 严格分离定理适用：存在 $\Lambda\in(E\times\mathbb{R})'$ 及实数 $\alpha<\beta$ 使得
   $$\Lambda(x_0,t_0)\le\alpha<\beta\le\Lambda(x,t)\qquad\forall(x,t)\in H.$$
   令 $\varphi(x):=\Lambda(x,0)$，$\gamma:=\Lambda(0,1)\in\mathbb{R}$。因嵌入 $x\mapsto(x,0)$ 连续线性，有 $\varphi\in E'$ 且 $\Lambda(x,t)=\varphi(x)+\gamma t$。  
   取 $F:=\mathbb{R}\varphi\in\mathcal{F}$（$\dim F\le 1$），则 $\varphi\in F$。对任意 $(y,t)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 及任意 $\varepsilon>0$，因 $g_F(y)<t+\varepsilon$，存在 $x_\varepsilon\in E$ 使 $q_Fx_\varepsilon=y$ 且 $f(x_\varepsilon)\le t+\varepsilon$。结合 $h\le f$ 得 $h(x_\varepsilon)\le t+\varepsilon$，即 $(x_\varepsilon,t+\varepsilon)\in H$，于是
   $$\beta\le\Lambda(x_\varepsilon,t+\varepsilon)=\varphi(x_\varepsilon)+\gamma(t+\varepsilon)=(q_Fx_\varepsilon)(\varphi)+\gamma(t+\varepsilon)=y(\varphi)+\gamma(t+\varepsilon).$$
   令 $\varepsilon\downarrow 0$ 得对一切 $(y,t)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 有 $y(\varphi)+\gamma t\ge\beta$。由引理 A，映射 $(y,t)\mapsto\operatorname{ev}_\varphi(y)+\gamma t=y(\varphi)+\gamma t$ 在 $F^*\times\mathbb{R}$ 上连续，故半空间 $M:=\{(y,t)\in F^*\times\mathbb{R}:y(\varphi)+\gamma t\ge\beta\}$ 在 $F^*\times\mathbb{R}$ 中闭且包含 $\operatorname{epi}_{\mathbb{R}}(g_F)$，从而包含其闭包 $\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}=\operatorname{epi}_{\mathbb{R}}(G_F)$。  
   但由 $G_F(q_Fx_0)\le G(x_0)<t_0$ 知 $(q_Fx_0,t_0)\in\operatorname{epi}_{\mathbb{R}}(G_F)\subset M$，故
   $$\beta\le(q_Fx_0)(\varphi)+\gamma t_0=\varphi(x_0)+\gamma t_0=\Lambda(x_0,t_0)\le\alpha<\beta,$$
   矛盾！故对一切 $x\in E$ 有 $h(x)\le G(x)$。

---

## S5　闭成本的有限投影

**结论：否（每个有限维 $F$ 的 $g_F$ 不必下半连续）。**

### 反例构造与完整核验

设 $E=\mathbb{R}^2$（赋标准欧氏拓扑，为实 Hausdorff 局部凸空间）。令
$$C:=\{(x_1,x_2)\in\mathbb{R}^2:x_1\ge 0,\ x_2\ge 0,\ x_1x_2\ge 1\},$$
并定义扩展实值函数 $f:\mathbb{R}^2\to[0,+\infty]$ 为 $C$ 的示性函数：
$$f(x_1,x_2):=\begin{cases}0,&(x_1,x_2)\in C,\\ +\infty,&(x_1,x_2)\notin C.\end{cases}$$

1. **核验 $f$ 满足 S5 的全部条件**：
   - **值域与至少一点有限**：$f$ 取值于 $\{0,+\infty\}\subset[0,+\infty]$；因 $(1,1)\in C$，有 $f(1,1)=0<+\infty$。
   - **下半连续性（$\operatorname{epi}_{\mathbb{R}}(f)$ 闭）**：直接核验得 $(x,t)\in\operatorname{epi}_{\mathbb{R}}(f)\iff f(x)\le t\iff x\in C$ 且 $t\ge 0$，即 $\operatorname{epi}_{\mathbb{R}}(f)=C\times[0,+\infty)$。因坐标函数 $(x_1,x_2)\mapsto x_1,x_2$ 与乘积函数 $(x_1,x_2)\mapsto x_1x_2$ 在 $\mathbb{R}^2$ 上均连续，$C=\{x_1\ge 0\}\cap\{x_2\ge 0\}\cap\{x_1x_2\ge 1\}$ 为 $\mathbb{R}^2$ 中三个闭集的交集，故 $C$ 闭；又 $[0,+\infty)$ 在 $\mathbb{R}$ 中闭，故乘积集 $\operatorname{epi}_{\mathbb{R}}(f)=C\times[0,+\infty)$ 在 $\mathbb{R}^2\times\mathbb{R}$ 中闭，即 $f$ 下半连续。
   - **凸性（$\operatorname{epi}_{\mathbb{R}}(f)$ 凸）**：注意到 $(x_1,x_2)\in C\implies x_1>0,x_2>0$（若其一为 $0$ 则 $x_1x_2=0<1$）。任取 $(a_1,a_2),(b_1,b_2)\in C$ 与 $\lambda\in[0,1]$，则 $a_1,a_2,b_1,b_2>0$ 且 $a_2\ge 1/a_1,\ b_2\ge 1/b_1$。令 $x_1=\lambda a_1+(1-\lambda)b_1>0$，$x_2=\lambda a_2+(1-\lambda)b_2>0$，则 $x_1\ge 0,x_2\ge 0$，且由 $(a_1-b_1)^2\ge 0\implies\frac{a_1}{b_1}+\frac{b_1}{a_1}\ge 2$ 有
     $$x_1x_2\ge(\lambda a_1+(1-\lambda)b_1)\left(\frac{\lambda}{a_1}+\frac{1-\lambda}{b_1}\right)=\lambda^2+(1-\lambda)^2+\lambda(1-\lambda)\left(\frac{a_1}{b_1}+\frac{b_1}{a_1}\right)\ge(\lambda+(1-\lambda))^2=1.$$
     故 $(x_1,x_2)\in C$，$C$ 在 $\mathbb{R}^2$ 中凸；结合 $[0,+\infty)$ 在 $\mathbb{R}$ 中凸，知 $\operatorname{epi}_{\mathbb{R}}(f)=C\times[0,+\infty)$ 在 $\mathbb{R}^2\times\mathbb{R}$ 中凸，即 $f$ 凸。

2. **选取有限维 $F\subset E'$ 并计算 $g_F$**：  
   取第一坐标投影 $\varphi_1\in(\mathbb{R}^2)'$，$\varphi_1(x_1,x_2)=x_1$（显然在 $\mathbb{R}^2$ 上连续线性），令一维线性子空间 $F:=\mathbb{R}\varphi_1\subset(\mathbb{R}^2)'$。因 $\{\varphi_1\}$ 是 $F$ 的基，由引理 A 的证明，$T_F:F^*\to\mathbb{R}$，$T_F(y)=y(\varphi_1)$ 是线性同胚；对每个 $s\in\mathbb{R}$，记 $y^{(s)}:=T_F^{-1}(s)\in F^*$（即 $y^{(s)}(c\varphi_1)=cs$）。  
   对任意 $(x_1,x_2)\in\mathbb{R}^2$，由 $q_F(x_1,x_2)(\varphi_1)=\varphi_1(x_1,x_2)=x_1$ 知 $q_F(x_1,x_2)=y^{(x_1)}$。故对任意 $s\in\mathbb{R}$，纤维 $\{x\in\mathbb{R}^2:q_Fx=y^{(s)}\}=\{(s,x_2):x_2\in\mathbb{R}\}$，从而：
   - 当 $s>0$ 时，取 $x_2=1/s>0$ 有 $(s,1/s)\in C$，故 $f(s,1/s)=0$，结合 $f\ge 0$ 得 $g_F(y^{(s)})=\inf_{x_2\in\mathbb{R}}f(s,x_2)=0$；
   - 当 $s\le 0$ 时，对任意 $x_2\in\mathbb{R}$ 均有 $(s,x_2)\notin C$，即 $f(s,x_2)=+\infty$，故 $g_F(y^{(s)})=+\infty$。

3. **证明 $g_F$ 不下半连续**：  
   对每个整数 $n\ge 1$，取 $y_n:=y^{(1/n)}\in F^*$。因 $1/n>0$，有 $g_F(y_n)=0\le 0$，故 $(y_n,0)\in\operatorname{epi}_{\mathbb{R}}(g_F)$。  
   因 $1/n\to 0$（$n\to\infty$）且 $T_F^{-1}:\mathbb{R}\to F^*$ 连续，在 $F^*$ 的有限维拓扑下有 $y_n=T_F^{-1}(1/n)\to T_F^{-1}(0)=0$，从而在乘积空间 $F^*\times\mathbb{R}$ 中 $(y_n,0)\to(0,0)$。  
   然而 $0=y^{(0)}$ 处 $g_F(0)=+\infty\not\le 0$，即 $(0,0)\notin\operatorname{epi}_{\mathbb{R}}(g_F)$。因此 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^*\times\mathbb{R}$ 中不是闭集，$g_F$ 不下半连续。

---

## S6　恢复与投影的精确关系

在共同设定下，先由 S4 的引理 B（其条件仅需实拓扑向量空间与非负凸函数）确认符号 $\bar u$ 的精确定义与适定性：对任意实拓扑向量空间 $X$ 上的非负凸函数 $u:X\to[0,+\infty]$，引理 B 给出的 $u^{\mathrm{cl}}:X\to[0,+\infty]$ 下半连续、凸、满足 $u^{\mathrm{cl}}\le u$，且支配一切满足 $h\le u$ 的下半连续凸函数 $h:X\to[-\infty,+\infty]$（特别地支配一切 $[0,+\infty]$ 值下半连续凸下界），故非负凸 $u$ 的最大下半连续凸下界唯一存在且恰为 $\bar u=u^{\mathrm{cl}}$（其上图满足 $\operatorname{epi}_{\mathbb{R}}(\bar u)=\overline{\operatorname{epi}_{\mathbb{R}}(u)}$）。特别地，S4 中的局部恢复即为 $G_F=\overline{g_F}$，总体恢复满足 $G=\bar f$。

### 1. 证明 $G=f$ 当且仅当 $f$ 下半连续

（S4 仅依赖共同设定，其全部结论在 S6 下适用。）
- **必要性（$\Rightarrow$）**：若 $G=f$，由 S4 知 $G$ 在 $E$ 上下半连续，故 $f=G$ 下半连续。
- **充分性（$\Leftarrow$）**：若 $f$ 下半连续，结合共同设定知 $f:E\to[0,+\infty]\subset[-\infty,+\infty]$ 同时下半连续、凸，且平凡满足 $f\le f$。将 $h:=f$ 代入 S4 中 $G$ 的极大性性质，得 $f\le G$。又由 S4 知恒有 $G\le f$，故 $G=f$。

### 2. 证明 $\overline{g_F}=\overline{y\mapsto\inf_{r_{KF}z=y}\overline{g_K}(z)}$

设 $F,K\in\mathcal{F}$ 且 $F\subset K$。记 $w:F^*\to[0,+\infty]$ 为
$$w(y):=\inf_{r_{KF}z=y}\overline{g_K}(z)\qquad(y\in F^*).$$
先验证 $w$ 非负且凸，以确保 $\overline{w}$ 有定义：因 $\overline{g_K}$ 取值于 $[0,+\infty]$，故 $w$ 取值于 $[0,+\infty]$。任取 $(y_1,t_1),(y_2,t_2)\in\operatorname{epi}_{\mathbb{R}}(w)$ 与 $\lambda\in(0,1)$，记 $y=\lambda y_1+(1-\lambda)y_2$，$t=\lambda t_1+(1-\lambda)t_2$；对任意 $\varepsilon>0$，由下确界定义取 $z_i\in K^*$ 使 $r_{KF}z_i=y_i$ 且 $\overline{g_K}(z_i)\le t_i+\varepsilon$（$i=1,2$），由 $\overline{g_K}$ 凸与 $r_{KF}$ 线性知 $z_\varepsilon:=\lambda z_1+(1-\lambda)z_2$ 满足 $r_{KF}z_\varepsilon=y$ 且 $\overline{g_K}(z_\varepsilon)\le t+\varepsilon$，故 $w(y)\le t+\varepsilon$；令 $\varepsilon\downarrow 0$ 得 $w(y)\le t$（$\lambda\in\{0,1\}$ 时平凡成立）。故 $\operatorname{epi}_{\mathbb{R}}(w)$ 凸，$w$ 非负且凸，$\overline{w}$ 适定。

现双向证明 $\overline{g_F}=\overline{w}$：
- **证明 $\overline{w}\le\overline{g_F}$**：因对一切 $z\in K^*$ 有 $\overline{g_K}(z)\le g_K(z)$，对满足 $r_{KF}z=y$ 的 $z$ 取下确界并应用 S1 的公式（S1 仅依赖共同设定，在此适用），得
  $$w(y)=\inf_{r_{KF}z=y}\overline{g_K}(z)\le\inf_{r_{KF}z=y}g_K(z)=g_F(y)\qquad(\forall y\in F^*).$$
  因 $\overline{w}$ 下半连续、凸且 $\overline{w}\le w\le g_F$，由 $\overline{g_F}$ 作为 $g_F$ 最大下半连续凸下界的定义，得 $\overline{w}\le\overline{g_F}$。
- **证明 $\overline{g_F}\le\overline{w}$**：由 S4 第 3 节已证的投影单调不等式（其中 $G_F=\overline{g_F},G_K=\overline{g_K}$，仅依赖共同设定），对一切 $z\in K^*$ 有
  $$\overline{g_F}(r_{KF}z)\le\overline{g_K}(z).$$
  固定任意 $y\in F^*$，对每个满足 $r_{KF}z=y$ 的 $z\in K^*$ 有 $\overline{g_F}(y)=\overline{g_F}(r_{KF}z)\le\overline{g_K}(z)$；对满足 $r_{KF}z=y$ 的 $z$ 取下确界（若纤维为空则下确界为 $+\infty\ge\overline{g_F}(y)$），得 $\overline{g_F}(y)\le w(y)$。因 $\overline{g_F}$ 本身已下半连续、凸且为 $w$ 的下界，由 $\overline{w}$ 作为 $w$ 最大下半连续凸下界的定义，得 $\overline{g_F}\le\overline{w}$。

故 $\overline{g_F}=\overline{w}=\overline{y\mapsto\inf_{r_{KF}z=y}\overline{g_K}(z)}$。

### 3. 判断右式的最外层 bar 能否总省去

**结论：不能总省去。**

### 反例完整核验

取 S5 中的空间与函数：$E=\mathbb{R}^2$，
$$f(x_1,x_2)=\begin{cases}0,&x_1\ge 0,\ x_2\ge 0,\ x_1x_2\ge 1,\\ +\infty,&\text{其他}.\end{cases}$$
如 S5 已完整核验，$E=\mathbb{R}^2$ 是实 Hausdorff 局部凸空间，$f:\mathbb{R}^2\to[0,+\infty]$ 凸、下半连续且在 $(1,1)$ 处有限，故完全满足共同设定。

取有限维子空间 $K:=E'=(\mathbb{R}^2)'=\operatorname{span}\{\varphi_1,\varphi_2\}$（其中 $\varphi_i(x_1,x_2)=x_i$，$\dim K=2<\infty$）及 $F:=\mathbb{R}\varphi_1\subset K$（$\dim F=1<\infty$）。
1. **计算 $\overline{g_K}$**：由引理 A 的证明，$T_K:K^*\to\mathbb{R}^2$，$T_K(z)=(z(\varphi_1),z(\varphi_2))$ 是线性同胚，且 $(T_K\circ q_K)(x_1,x_2)=(x_1,x_2)$，故 $q_K=T_K^{-1}:\mathbb{R}^2\to K^*$ 是线性同胚。因此对任意 $z\in K^*$，纤维 $\{x\in\mathbb{R}^2:q_Kx=z\}=\{T_K(z)\}$ 为单点集，从而 $g_K(z)=f(T_K(z))$。  
   因 $T_K\times\operatorname{id}_{\mathbb{R}}:K^*\times\mathbb{R}\to\mathbb{R}^2\times\mathbb{R}$ 为同胚且 S5 已证 $\operatorname{epi}_{\mathbb{R}}(f)$ 在 $\mathbb{R}^2\times\mathbb{R}$ 中闭，故 $\operatorname{epi}_{\mathbb{R}}(g_K)=(T_K\times\operatorname{id}_{\mathbb{R}})^{-1}(\operatorname{epi}_{\mathbb{R}}(f))$ 在 $K^*\times\mathbb{R}$ 中闭，即 $g_K$ 已下半连续。又由 S1 知 $g_K$ 非负且凸，故其最大下半连续凸下界就是自身：$\overline{g_K}=g_K$。
2. **比较去掉最外层 bar 后的右式与左式**：因 $\overline{g_K}=g_K$，结合 S1 公式，去掉最外层 bar 后的右式函数恰为
   $$w(y)=\inf_{r_{KF}z=y}\overline{g_K}(z)=\inf_{r_{KF}z=y}g_K(z)=g_F(y)\qquad(\forall y\in F^*).$$
   在 $y=0\in F^*$ 处，由 S5 的计算知右式值 $w(0)=g_F(0)=+\infty$；而对左式 $\overline{g_F}$，S5 已证点列 $(y^{(1/n)},0)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^*\times\mathbb{R}$ 中收敛于 $(0,0)$，故 $(0,0)\in\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}=\operatorname{epi}_{\mathbb{R}}(\overline{g_F})$，结合 $\overline{g_F}\ge 0$ 得 $\overline{g_F}(0)=0$。因此
   $$\overline{g_F}(0)=0\neq+\infty=\inf_{r_{KF}z=0}\overline{g_K}(z),$$
   右式的最外层 bar 不能省去。
