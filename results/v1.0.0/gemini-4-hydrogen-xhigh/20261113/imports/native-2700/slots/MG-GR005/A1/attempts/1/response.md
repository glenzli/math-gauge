下面严格按照题目共同设定与各阶段附加条件，逐阶段给出完整论证、构造与反例核验。

---

### 共同预备引理（仅用共同设定）

先记录两个对任意拓扑空间（或实拓扑向量空间）$X$ 及任意扩展实值函数 $u,v:X\to[-\infty,+\infty]$ 均成立的基础等价关系：

1. **序关系与上图**：
   $$u \le v \iff \operatorname{epi}_{\mathbb{R}}(v) \subset \operatorname{epi}_{\mathbb{R}}(u).$$
   *验证*：若 $u\le v$ 且 $(x,t)\in\operatorname{epi}_{\mathbb{R}}(v)$，则 $t\in\mathbb{R}$ 且 $u(x)\le v(x)\le t$，故 $(x,t)\in\operatorname{epi}_{\mathbb{R}}(u)$。反之，若 $\operatorname{epi}_{\mathbb{R}}(v)\subset\operatorname{epi}_{\mathbb{R}}(u)$，对任意 $x\in X$：若 $v(x)=+\infty$，则 $u(x)\le v(x)$ 平凡成立；若 $v(x)\in\mathbb{R}$，则 $(x,v(x))\in\operatorname{epi}_{\mathbb{R}}(v)\subset\operatorname{epi}_{\mathbb{R}}(u)$ 得 $u(x)\le v(x)$；若 $v(x)=-\infty$，则对一切 $t\in\mathbb{R}$ 有 $(x,t)\in\operatorname{epi}_{\mathbb{R}}(v)\subset\operatorname{epi}_{\mathbb{R}}(u)$，故 $u(x)\le t$ 对所有 $t\in\mathbb{R}$ 成立，从而 $u(x)=-\infty=v(x)$。
2. **下半连续与次水平集闭性**：
   $\operatorname{epi}_{\mathbb{R}}(u)$ 在 $X\times\mathbb{R}$ 中闭，当且仅当对每个 $c\in\mathbb{R}$，次水平集 $\{x\in X:u(x)\le c\}$ 在 $X$ 中闭。
   *验证*：对固定 $c\in\mathbb{R}$，映射 $x\mapsto(x,c)$ 连续，且 $\{u\le c\}$ 是 $\operatorname{epi}_{\mathbb{R}}(u)$ 在该映射下的原像，故上图闭推出各次水平集闭。反之，若所有 $\{u\le c\}$（$c\in\mathbb{R}$）闭，任取 $(x_0,t_0)\in(X\times\mathbb{R})\setminus\operatorname{epi}_{\mathbb{R}}(u)$，则 $t_0\in\mathbb{R}$ 且 $u(x_0)>t_0$。取实数 $c\in(t_0,u(x_0))$（若 $u(x_0)=+\infty$ 可取 $c=t_0+1$），则 $(X\setminus\{u\le c\})\times(-\infty,c)$ 是 $(x_0,t_0)$ 在 $X\times\mathbb{R}$ 中的开邻域且与 $\operatorname{epi}_{\mathbb{R}}(u)$ 不交，故 $\operatorname{epi}_{\mathbb{R}}(u)$ 闭。
3. **投影映射 $q_F$ 与限制映射 $r_{KF}$ 的连续性**：
   对有限维线性子空间 $F\subset E'$，若 $F=\{0\}$，则 $F^*=\{0\}$，$q_F\equiv 0$ 显然连续；若 $\dim F=d\ge 1$，取 $F$ 的一组基 $\{\varphi_1,\dots,\varphi_d\}$。因 $F^*$ 取有限维（Hausdorff 向量空间）拓扑，线性双射 $\Phi_F:F^*\to\mathbb{R}^d$、$y\mapsto(y(\varphi_1),\dots,y(\varphi_d))$ 为线性同胚。因每个 $\varphi_i\in F\subset E'$ 在 $E$ 上连续，故 $\Phi_F\circ q_F(x)=(\varphi_1(x),\dots,\varphi_d(x))$ 连续，从而 $q_F=\Phi_F^{-1}\circ(\Phi_F\circ q_F):E\to F^*$ 连续且线性。同理，对有限维子空间 $F\subset K\subset E'$，$r_{KF}:K^*\to F^*$ 是有限维 Hausdorff 拓扑向量空间之间的线性映射，故连续，且满足 $r_{KF}\circ q_K=q_F$（对所有 $x\in E$ 与 $\varphi\in F$，$(r_{KF}(q_K x))(\varphi)=(q_K x)(\varphi)=\varphi(x)=(q_F x)(\varphi)$）。

---

## S1　原始记录

### 1. 证明 $g_F$ 非负、凸且至少一点有限

- **非负性**：因 $f:E\to[0,+\infty]$，对任意 $y\in F^*$，集合 $\{f(x):q_F x=y\}\subset[0,+\infty]$；若纤维非空，该集合以 $0$ 为下界故其下确界 $\ge 0$；若纤维为空，依规定 $g_F(y)=+\infty\ge 0$。故 $g_F:F^*\to[0,+\infty]$。
- **至少一点有限**：依共同设定，存在 $x_0\in E$ 使 $f(x_0)<+\infty$。令 $y_0=q_F(x_0)\in F^*$，则 $x_0$ 属于纤维 $\{x\in E:q_F x=y_0\}$，从而 $0\le g_F(y_0)\le f(x_0)<+\infty$。
- **凸性（$\operatorname{epi}_{\mathbb{R}}(g_F)$ 为凸集）**：任取 $(y_1,t_1),(y_2,t_2)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 及 $\lambda\in[0,1]$。欲证 $(\lambda y_1+(1-\lambda)y_2,\lambda t_1+(1-\lambda)t_2)\in\operatorname{epi}_{\mathbb{R}}(g_F)$。
  任取 $\varepsilon>0$。由于 $g_F(y_i)\le t_i<t_i+\varepsilon$（$i=1,2$），依下确界定义存在 $x_1,x_2\in E$ 满足 $q_F x_i=y_i$ 且 $f(x_i)<t_i+\varepsilon$（特别地 $(x_i,t_i+\varepsilon)\in\operatorname{epi}_{\mathbb{R}}(f)$）。
  由 $\operatorname{epi}_{\mathbb{R}}(f)$ 的凸性，
  $$(\lambda x_1+(1-\lambda)x_2,\;\lambda(t_1+\varepsilon)+(1-\lambda)(t_2+\varepsilon))\in\operatorname{epi}_{\mathbb{R}}(f),$$
  即 $f(\lambda x_1+(1-\lambda)x_2)\le\lambda t_1+(1-\lambda)t_2+\varepsilon$。由 $q_F$ 的线性性，
  $$q_F(\lambda x_1+(1-\lambda)x_2)=\lambda q_F(x_1)+(1-\lambda)q_F(x_2)=\lambda y_1+(1-\lambda)y_2.$$
  于是
  $$g_F(\lambda y_1+(1-\lambda)y_2)\le f(\lambda x_1+(1-\lambda)x_2)\le\lambda t_1+(1-\lambda)t_2+\varepsilon.$$
  令 $\varepsilon\downarrow 0$ 即得 $g_F(\lambda y_1+(1-\lambda)y_2)\le\lambda t_1+(1-\lambda)t_2$，故 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 凸。

### 2. 证明 $g_F(y)=\inf_{r_{KF}z=y}g_K(z)$

设 $F\subset K\subset E'$ 为有限维子空间，固定 $y\in F^*$。

- **证明 $g_F(y)\le \inf_{r_{KF}z=y}g_K(z)$**：任取满足 $r_{KF}z=y$ 的 $z\in K^*$。对任意满足 $q_K x=z$ 的 $x\in E$，由 $q_F x = r_{KF}(q_K x) = r_{KF} z = y$ 可知 $g_F(y)\le f(x)$。对所有满足 $q_K x=z$ 的 $x$ 取下确界，得 $g_F(y)\le g_K(z)$（当 $\{x:q_K x=z\}=\emptyset$ 时右端为 $+\infty$，不等式亦成立）。再对所有满足 $r_{KF}z=y$ 的 $z\in K^*$ 取下确界，即得 $g_F(y)\le\inf_{r_{KF}z=y}g_K(z)$。
- **证明 $\inf_{r_{KF}z=y}g_K(z)\le g_F(y)$**：对任意满足 $q_F x=y$ 的 $x\in E$，令 $z=q_K x\in K^*$，则 $r_{KF}z=r_{KF}(q_K x)=q_F x=y$，且由 $g_K$ 定义有 $g_K(z)\le f(x)$。从而 $\inf_{r_{KF}z'=y}g_K(z')\le g_K(z)\le f(x)$。对所有满足 $q_F x=y$ 的 $x$ 取下确界（若 $\{x:q_F x=y\}=\emptyset$ 则 $g_F(y)=+\infty$，不等式平凡成立），即得 $\inf_{r_{KF}z=y}g_K(z)\le g_F(y)$。

两向结合即证 $g_F(y)=\inf_{r_{KF}z=y}g_K(z)$。

### 3. 是否需要纤维下确界取到

**不需要。** 以上全部证明均不依赖 $g_F(y)$ 或 $g_K(z)$ 的纤维下确界取到：
- 非负性、某点有限性（以 $x_0$ 直接给出上界）以及恒等式 $g_F(y)=\inf_{r_{KF}z=y}g_K(z)$ 仅利用 $[0,+\infty]$ 中下确界的单调性与 $r_{KF}\circ q_K=q_F$；
- 凸性论证通过任意 $\varepsilon>0$ 选取逼近元 $x_i$，对凸组合取上界后再令 $\varepsilon\downarrow 0$，无需极小元存在。

---

## S2　紧次水平集

在共同设定之外，本阶段附加假设：$f$ 下半连续，且对每个有限实数 $c\in\mathbb{R}$，次水平集 $L_c:=\{x\in E:f(x)\le c\}$ 在 $E$ 中紧。

> **注意**：$E$ 是一般 Hausdorff 局部凸空间，未必可度量化，故不使用序列紧性，而采用闭集族的有限交性质（FIP）论证。

### 1. 证明当 $g_F(y)<\infty$ 时纤维下确界取到

设 $y\in F^*$ 且 $m:=g_F(y)<+\infty$，则 $m\in[0,+\infty)$。令 $c_1:=m+1\in\mathbb{R}$，则 $L_{c_1}=\{x\in E:f(x)\le m+1\}$ 在 $E$ 中紧。对每个 $\varepsilon\in(0,1]$，定义
$$A_\varepsilon:=\{x\in E:q_F x=y\text{ 且 }f(x)\le m+\varepsilon\}=q_F^{-1}(\{y\})\cap\{x\in E:f(x)\le m+\varepsilon\}.$$
核验以下性质：
1. **$A_\varepsilon\subset L_{c_1}$**：因 $\varepsilon\le 1$，$f(x)\le m+\varepsilon\le m+1$。
2. **$A_\varepsilon$ 在 $L_{c_1}$ 中闭**：因 $F^*$ 具有有限维 Hausdorff 拓扑，单点集 $\{y\}$ 在 $F^*$ 中闭；由共同预备引理 3，$q_F:E\to F^*$ 连续，故 $q_F^{-1}(\{y\})$ 在 $E$ 中闭。又因 $f$ 下半连续，由共同预备引理 2，$\{x\in E:f(x)\le m+\varepsilon\}$ 在 $E$ 中闭。因此 $A_\varepsilon$ 在 $E$ 中闭，从而作为 $L_{c_1}$ 的子集在 $L_{c_1}$ 中闭。
3. **非空性与有限交性质（FIP）**：由 $m=\inf\{f(x):q_F x=y\}$，对任意 $\varepsilon\in(0,1]$ 存在 $x\in E$ 使 $q_F x=y$ 且 $f(x)<m+\varepsilon$，故 $A_\varepsilon\neq\emptyset$。对任意有限个 $\varepsilon_1,\dots,\varepsilon_k\in(0,1]$，令 $\varepsilon_*=\min_{1\le i\le k}\varepsilon_i\in(0,1]$，则 $\bigcap_{i=1}^k A_{\varepsilon_i}=A_{\varepsilon_*}\neq\emptyset$。

由 $L_{c_1}$ 的紧性（闭集族的有限交性质等价于总交非空），有 $\bigcap_{\varepsilon\in(0,1]}A_\varepsilon\neq\emptyset$。取 $x\in\bigcap_{\varepsilon\in(0,1]}A_\varepsilon$，则 $q_F x=y$，且对所有 $\varepsilon\in(0,1]$ 有 $f(x)\le m+\varepsilon$，令 $\varepsilon\downarrow 0$ 得 $f(x)\le m=g_F(y)$。结合 $g_F(y)\le f(x)$，即得 $f(x)=g_F(y)$，故纤维下确界取到。

### 2. 证明各 $g_F$ 下半连续

由共同预备引理 2，只需证明对每个 $c\in\mathbb{R}$，次水平集 $\{y\in F^*:g_F(y)\le c\}$ 在 $F^*$ 中闭。

断言：对任意 $c\in\mathbb{R}$，
$$\{y\in F^*:g_F(y)\le c\} = q_F(\{x\in E:f(x)\le c\}) = q_F(L_c).$$
- ($\supset$)：若 $x\in L_c$，则 $f(x)\le c$，故 $g_F(q_F x)\le f(x)\le c$，从而 $q_F x\in\{g_F\le c\}$。
- ($\subset$)：若 $y\in F^*$ 满足 $g_F(y)\le c$，则 $g_F(y)<+\infty$。由上面第 1 步，存在 $x\in E$ 使 $q_F x=y$ 且 $f(x)=g_F(y)\le c$，即 $x\in L_c$ 且 $y=q_F x\in q_F(L_c)$。（当 $c<0$ 时两端均为空集。）

对任意 $c\in\mathbb{R}$：依 S2 附加假设，$L_c$ 在 $E$ 中紧；由共同预备引理 3，$q_F:E\to F^*$ 连续。因紧集在连续映射下的像仍紧，故 $\{y\in F^*:g_F(y)\le c\}=q_F(L_c)$ 在 $F^*$ 中紧。又因 $F^*$ 取有限维（Hausdorff）拓扑，Hausdorff 空间中的紧子集必闭，故 $\{y\in F^*:g_F(y)\le c\}$ 在 $F^*$ 中闭。由此即知 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^*\times\mathbb{R}$ 中闭，即 $g_F$ 下半连续。

---

## S3　兼容成本记录的实现

在 S2 条件下，设 $\mathcal{F}$ 为 $E'$ 的全体有限维线性子空间之族，给定相容族 $\{y_F\in F^*\}_{F\in\mathcal{F}}$（$F\subset K\implies r_{KF}y_K=y_F$）与有限实数 $c\ge 0$，满足 $g_F(y_F)\le c$ 对一切 $F\in\mathcal{F}$ 成立。

### 1. 构造与存在性证明

对每个 $F\in\mathcal{F}$，定义
$$C_F:=\{x\in E:q_F x=y_F\text{ 且 }f(x)\le c\}=q_F^{-1}(\{y_F\})\cap L_c,$$
其中 $L_c=\{x\in E:f(x)\le c\}$。

逐项核验：
1. **紧包与闭性**：依 S2 条件，$L_c$ 在 $E$ 中紧。对每个 $F\in\mathcal{F}$，由 $q_F$ 连续及 $F^*$  Hausdorff，$q_F^{-1}(\{y_F\})$ 在 $E$ 中闭，故 $C_F$ 是紧集 $L_c$ 的闭子集。
2. **非空性**：因 $g_F(y_F)\le c<+\infty$，依 S2 结论，$g_F(y_F)$ 的纤维下确界取到，故存在 $x_F\in E$ 使 $q_F x_F=y_F$ 且 $f(x_F)=g_F(y_F)\le c$，从而 $x_F\in C_F$，即 $C_F\neq\emptyset$。
3. **有限交性质（FIP）**：任取有限个 $F_1,\dots,F_m\in\mathcal{F}$，令
   $$K:=F_1+\dots+F_m=\operatorname{span}(F_1\cup\dots\cup F_m)\subset E'.$$
   则 $\dim K\le\sum_{i=1}^m\dim F_i<\infty$，故 $K\in\mathcal{F}$ 且 $F_i\subset K$（$i=1,\dots,m$）。由非空性取 $x\in C_K$，则 $f(x)\le c$ 且 $q_K x=y_K$。利用相容性得对每个 $i=1,\dots,m$：
   $$q_{F_i}x = r_{KF_i}(q_K x) = r_{KF_i}(y_K) = y_{F_i},$$
   故 $x\in\bigcap_{i=1}^m C_{F_i}$，从而 $\bigcap_{i=1}^m C_{F_i}\neq\emptyset$。

由 $L_c$ 的紧性，$\bigcap_{F\in\mathcal{F}}C_F\neq\emptyset$。任取 $x\in\bigcap_{F\in\mathcal{F}}C_F$，即满足 $f(x)\le c$ 且对所有 $F\in\mathcal{F}$ 有 $q_F x=y_F$。

### 2. 唯一性证明

设 $x_1,x_2\in\bigcap_{F\in\mathcal{F}}C_F$。对任意 $\varphi\in E'$，取有限维子空间 $F_\varphi:=\operatorname{span}\{\varphi\}\in\mathcal{F}$，则
$$\varphi(x_1)=q_{F_\varphi}(x_1)(\varphi)=y_{F_\varphi}(\varphi)=q_{F_\varphi}(x_2)(\varphi)=\varphi(x_2),$$
即 $\varphi(x_1-x_2)=0$ 对一切 $\varphi\in E'$ 成立。

**援引 Hahn–Banach 分离定理（或连续半范数延拓）的适用性说明**：$E$ 是实 Hausdorff 局部凸空间。若 $x_1\neq x_2$，则 $v:=x_1-x_2\neq 0$，于是在实局部凸空间 $E$ 中 $\{0\}$ 与 $\{v\}$ 是两个不相交的紧凸集（且因 $E$ 为 Hausdorff 空间，$\{0\}$ 闭）；由 Hahn–Banach 严格分离定理（亦可由局部凸性与 Hausdorff 性取连续半范数 $p$ 使 $p(v)>0$ 并对一维子空间 $\mathbb{R}v$ 上的线性泛函 $tv\mapsto t\,p(v)$ 施以 Hahn–Banach 控制延拓定理），存在 $\varphi\in E'$ 使得 $\varphi(v)\neq 0$，这与 $\varphi(x_1-x_2)=0$ 矛盾。因此 $x_1=x_2$。

### 3. 构造结论

综合存在性与唯一性，集合 $\bigcap_{F\in\mathcal{F}}C_F=\{x\}$ 恰为单点集，这唯一地构造出满足 $q_F x=y_F$（$\forall F\in\mathcal{F}$）且 $f(x)\le c$ 的 $x\in E$。

*（补充说明：若对每个 $F\in\mathcal{F}$ 任取 $x_F\in C_F$，按包含序构成的网 $(x_F)_{F\in\mathcal{F}}$ 在 $E$ 的原拓扑下也必收敛于该 $x$：对 $x$ 的任一开邻域 $U$，闭集族 $\{C_F\setminus U\}_{F\in\mathcal{F}}$ 在紧集 $L_c$ 中的总交为 $\{x\}\setminus U=\emptyset$，故存在有限个 $F_1,\dots,F_m$ 使 $\bigcap_{i=1}^m C_{F_i}\subset U$，进而对一切 $F\supset\sum_{i=1}^m F_i$ 有 $x_F\in C_F\subset U$。）*

---

## S4　一般成本的恢复

本阶段**只使用共同设定**。

### 1. 结论

**可以**由全部 $\{g_F\}_{F\in\mathcal{F}}$ 构造满足全部要求的 $G:E\to[0,+\infty]$。

### 2. 构造与性质验证

对每个有限维子空间 $F\in\mathcal{F}$，利用 $g_F$ 在 $F^*$ 上定义其闭上图（下半连续正则化）函数 $\widetilde{g}_F:F^*\to[0,+\infty]$：
$$\widetilde{g}_F(y):=\inf\{t\in\mathbb{R}:(y,t)\in\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}\}\qquad(\inf\emptyset=+\infty),$$
其中闭包在 $F^*\times\mathbb{R}$ 中取（等价地，记 $\mathcal{N}(y)$ 为 $y$ 在 $F^*$ 中的邻域系，有 $\widetilde{g}_F(y)=\sup_{U\in\mathcal{N}(y)}\inf_{y'\in U}g_F(y')$）。

首先验证 $\widetilde{g}_F$ 的基本性质：
- **值域与上图**：因 $g_F\ge 0$，有 $\operatorname{epi}_{\mathbb{R}}(g_F)\subset F^*\times[0,+\infty)$，而 $F^*\times[0,+\infty)$ 在 $F^*\times\mathbb{R}$ 中闭，故 $\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}\subset F^*\times[0,+\infty)$，从而 $\widetilde{g}_F\ge 0$。进而 $\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)=\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}$：一方面 $\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}\subset\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)$ 由定义即得；另一方面，若 $(y,t)\in\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)$（即 $\widetilde{g}_F(y)\le t\in\mathbb{R}$），对任意 $\varepsilon>0$ 存在 $s<t+\varepsilon$ 使 $(y,s)\in\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}$，利用连续平移 $(y',t')\mapsto(y',t'+(t+\varepsilon-s))$ 将 $\operatorname{epi}_{\mathbb{R}}(g_F)$ 映入自身可得 $(y,t+\varepsilon)\in\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}$，令 $\varepsilon\downarrow 0$ 并由闭性即得 $(y,t)\in\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}$。
- **凸性与下半连续性**：由 S1，$\operatorname{epi}_{\mathbb{R}}(g_F)$ 在拓扑向量空间 $F^*\times\mathbb{R}$ 中凸。因对任意 $\lambda\in[0,1]$，映射 $(p,q)\mapsto\lambda p+(1-\lambda)q$ 连续，故凸集之闭包仍凸，从而 $\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)=\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}$ 既闭又凸。且由 $\operatorname{epi}_{\mathbb{R}}(g_F)\subset\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)$ 及共同预备引理 1，有 $\widetilde{g}_F\le g_F$。

现定义部分恢复 $G_F:E\to[0,+\infty]$ 及全局恢复 $G:E\to[0,+\infty]$ 为：
$$G_F(x):=\widetilde{g}_F(q_F x),\qquad G(x):=\sup_{F\in\mathcal{F}}G_F(x).$$
注意 $\{0\}\in\mathcal{F}$ 故 $\mathcal{F}\neq\emptyset$，且 $G_F(x)\in[0,+\infty]$，因此 $G:E\to[0,+\infty]$。下面逐项验证所需性质：

1. **验证 $G\le f$**：对任意 $F\in\mathcal{F}$ 及 $x\in E$，有
   $$G_F(x)=\widetilde{g}_F(q_F x)\le g_F(q_F x)=\inf\{f(x'):q_F x'=q_F x\}\le f(x).$$
   对所有 $F\in\mathcal{F}$ 取上确界即得 $G(x)\le f(x)$。
2. **验证 $G$ 下半连续且凸**：对每个 $F\in\mathcal{F}$，线性映射 $q_F\times\operatorname{id}_{\mathbb{R}}:E\times\mathbb{R}\to F^*\times\mathbb{R}$ 连续（由共同预备引理 3），且
   $$\operatorname{epi}_{\mathbb{R}}(G_F)=(q_F\times\operatorname{id}_{\mathbb{R}})^{-1}(\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)).$$
   作为闭凸集在连续线性映射下的原像，$\operatorname{epi}_{\mathbb{R}}(G_F)$ 在 $E\times\mathbb{R}$ 中闭且凸。又对任意 $(x,t)\in E\times\mathbb{R}$，$G(x)\le t\iff\forall F\in\mathcal{F},\;G_F(x)\le t$，故
   $$\operatorname{epi}_{\mathbb{R}}(G)=\bigcap_{F\in\mathcal{F}}\operatorname{epi}_{\mathbb{R}}(G_F).$$
   任意多个闭凸集之交仍为闭凸集，故 $G$ 下半连续且凸。
3. **验证极大性（对一切竞争函数 $h:E\to[-\infty,+\infty]$ 若下半连续、凸且 $h\le f$，则 $h\le G$）**：
   先证明 $\operatorname{epi}_{\mathbb{R}}(G)=\overline{\operatorname{epi}_{\mathbb{R}}(f)}$（闭包在 $E\times\mathbb{R}$ 中取）。
   - ($\supset$)：因 $G\le f$，由共同预备引理 1 得 $\operatorname{epi}_{\mathbb{R}}(f)\subset\operatorname{epi}_{\mathbb{R}}(G)$。又 $\operatorname{epi}_{\mathbb{R}}(G)$ 在 $E\times\mathbb{R}$ 中闭，故 $\overline{\operatorname{epi}_{\mathbb{R}}(f)}\subset\operatorname{epi}_{\mathbb{R}}(G)$。
   - ($\subset$)：反证法。设 $(x_0,t_0)\in(E\times\mathbb{R})\setminus\overline{\operatorname{epi}_{\mathbb{R}}(f)}$。
     **援引 Hahn–Banach 严格分离定理的适用性说明**：$E\times\mathbb{R}$ 作为两个实 Hausdorff 局部凸空间的乘积，仍是实 Hausdorff 局部凸空间；依共同设定存在 $x_*\in E$ 使 $f(x_*)<+\infty$，故 $(x_*,f(x_*))\in\operatorname{epi}_{\mathbb{R}}(f)$，且 $\operatorname{epi}_{\mathbb{R}}(f)$ 凸，从而 $C:=\overline{\operatorname{epi}_{\mathbb{R}}(f)}$ 是 $E\times\mathbb{R}$ 中的非空闭凸集；单点集 $\{(x_0,t_0)\}$ 是紧凸集且与 $C$ 不交。因此，由实局部凸空间中的 Hahn–Banach 严格分离定理，存在连续线性泛函 $\Lambda\in(E\times\mathbb{R})'$ 及 $\beta\in\mathbb{R}$ 使得
     $$\Lambda(x_0,t_0)<\beta\le\Lambda(x,t)\qquad(\forall (x,t)\in C).$$
     令 $\varphi(x):=\Lambda(x,0)$ 与 $\alpha:=\Lambda(0,1)$。因 $x\mapsto(x,0)$ 连续线性，故 $\varphi\in E'$，$\alpha\in\mathbb{R}$，且 $\Lambda(x,t)=\varphi(x)+\alpha t$。
     现取有限维子空间 $F:=\operatorname{span}\{\varphi\}\in\mathcal{F}$。任取 $(y,t)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 及 $\varepsilon>0$，由 $g_F(y)\le t<t+\varepsilon$，存在 $x\in E$ 使 $q_F x=y$ 且 $f(x)<t+\varepsilon$，从而 $(x,t+\varepsilon)\in\operatorname{epi}_{\mathbb{R}}(f)\subset C$。于是
     $$y(\varphi)+\alpha(t+\varepsilon)=\varphi(x)+\alpha(t+\varepsilon)=\Lambda(x,t+\varepsilon)\ge\beta.$$
     令 $\varepsilon\downarrow 0$ 得 $y(\varphi)+\alpha t\ge\beta$ 对一切 $(y,t)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 成立。由于线性泛函 $(y,t)\mapsto y(\varphi)+\alpha t$ 在 $F^*\times\mathbb{R}$ 上连续（$\varphi\in F$ 故 $y\mapsto y(\varphi)$ 是有限维空间 $F^*$ 上的连续线性泛函），闭半空间 $\{(y,t)\in F^*\times\mathbb{R}:y(\varphi)+\alpha t\ge\beta\}$ 包含 $\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}=\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)$。然而
     $$q_F(x_0)(\varphi)+\alpha t_0=\varphi(x_0)+\alpha t_0=\Lambda(x_0,t_0)<\beta,$$
     故 $(q_F(x_0),t_0)\notin\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)$，即 $(x_0,t_0)\notin\operatorname{epi}_{\mathbb{R}}(G_F)$，从而 $(x_0,t_0)\notin\operatorname{epi}_{\mathbb{R}}(G)$。这证明了 $\operatorname{epi}_{\mathbb{R}}(G)\subset\overline{\operatorname{epi}_{\mathbb{R}}(f)}$。

   于是 $\operatorname{epi}_{\mathbb{R}}(G)=\overline{\operatorname{epi}_{\mathbb{R}}(f)}$。现设任意函数 $h:E\to[-\infty,+\infty]$（允许同时取 $-\infty$ 与 $+\infty$）下半连续、凸并满足 $h\le f$。由 $h\le f$ 与共同预备引理 1 得 $\operatorname{epi}_{\mathbb{R}}(f)\subset\operatorname{epi}_{\mathbb{R}}(h)$。因 $h$ 下半连续，即 $\operatorname{epi}_{\mathbb{R}}(h)$ 在 $E\times\mathbb{R}$ 中闭，故
   $$\operatorname{epi}_{\mathbb{R}}(G)=\overline{\operatorname{epi}_{\mathbb{R}}(f)}\subset\operatorname{epi}_{\mathbb{R}}(h).$$
   再由共同预备引理 1，即得 $h\le G$。（注：此论证在 $\operatorname{epi}_{\mathbb{R}}(h)$ 上直接进行，完全避免了 $+\infty-\infty$ 问题，故对允许同时取 $-\infty$ 与 $+\infty$ 的竞争函数 $h$ 同样严格成立。）

### 3. 扩大观测空间时的关系

设 $F\subset K\subset E'$ 为有限维线性子空间（观测空间由 $F$ 扩大至 $K$），$r_{KF}:K^*\to F^*$ 为限制映射。

1. **记录层面（$K^*$ 与 $F^*$ 上）的关系**：
   由 S1 知 $g_F\circ r_{KF}\le g_K$，结合 $\widetilde{g}_F\le g_F$ 得 $\widetilde{g}_F\circ r_{KF}\le g_K$，故 $\operatorname{epi}_{\mathbb{R}}(g_K)\subset\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F\circ r_{KF})=(r_{KF}\times\operatorname{id}_{\mathbb{R}})^{-1}(\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F))$。因 $r_{KF}$ 连续且 $\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F)$ 闭，右端在 $K^*\times\mathbb{R}$ 中闭，取闭包即得 $\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_K)=\overline{\operatorname{epi}_{\mathbb{R}}(g_K)}\subset\operatorname{epi}_{\mathbb{R}}(\widetilde{g}_F\circ r_{KF})$，由共同预备引理 1 得
   $$\widetilde{g}_F\circ r_{KF}\le \widetilde{g}_K \quad \text{（即 }\forall z\in K^*,\;\widetilde{g}_F(r_{KF}z)\le\widetilde{g}_K(z)\text{）}.$$
   对所有满足 $r_{KF}z=y$ 的 $z\in K^*$ 取下确界，并结合 S1，得三明治夹逼关系：
   $$\widetilde{g}_F(y)\le \inf_{r_{KF}z=y}\widetilde{g}_K(z)\le \inf_{r_{KF}z=y}g_K(z)=g_F(y)\qquad(\forall y\in F^*).$$
2. **恢复层面（$E$ 上）的单调性与有向极限关系**：
   利用 $q_F=r_{KF}\circ q_K$，对一切 $x\in E$ 有
   $$G_F(x)=\widetilde{g}_F(q_F x)=\widetilde{g}_F(r_{KF}(q_K x))\le \widetilde{g}_K(q_K x)=G_K(x),$$
   即 $F\subset K\implies G_F\le G_K\le G\le f$。从而随着观测空间扩大，部分恢复 $\{G_F\}_{F\in\mathcal{F}}$ 按包含序构成单调递增的有向网，且在每点 $x\in E$ 满足
   $$G(x)=\sup_{F\in\mathcal{F}}G_F(x)=\lim_{F\in\mathcal{F}}G_F(x)\quad(\text{在 }[0,+\infty]\text{ 中}).$$
   特别地，若 $\mathcal{C}\subset\mathcal{F}$ 在 $\mathcal{F}$ 中共尾（即对任意 $F\in\mathcal{F}$ 存在 $K\in\mathcal{C}$ 使 $F\subset K$），则 $\sup_{K\in\mathcal{C}}G_K=G$；且若逐步扩大观测泛函集 $W_1\subset W_2\subset E'$ 并记 $G^{(W_i)}:=\sup_{F\in\mathcal{F},\,F\subset W_i}G_F$，则有单调性 $G^{(W_1)}\le G^{(W_2)}\le G^{(E')}=G$。

---

## S5　闭成本的有限投影

### 1. 结论

**否**（$g_F$ 未必下半连续）。

### 2. 反例与完整核验

取 $E=\mathbb{R}^2$（实 Hausdorff 局部凸空间），并定义集合
$$C:=\{(x_1,x_2)\in\mathbb{R}^2:x_1\ge 0,\;x_2\ge 0,\;x_1 x_2\ge 1\}.$$
（注意：对任意 $(x_1,x_2)\in C$，由 $x_1 x_2\ge 1$ 及 $x_1,x_2\ge 0$ 必有 $x_1>0$ 且 $x_2>0$。）

1. **核验 $C$ 闭且凸**：
   - **闭性**：$C=\{x_1\ge 0\}\cap\{x_2\ge 0\}\cap\{x_1 x_2\ge 1\}$ 是三个连续函数闭原像的交，故 $C$ 在 $\mathbb{R}^2$ 中闭。
   - **凸性**：任取 $(x_1,x_2),(x_1',x_2')\in C$ 及 $\lambda\in[0,1]$，令 $u_1=\lambda x_1+(1-\lambda)x_1'$，$u_2=\lambda x_2+(1-\lambda)x_2'$。显然 $u_1>0,u_2>0$；又由均值不等式，
     $$x_1 x_2'+x_1' x_2\ge 2\sqrt{(x_1 x_2')(x_1' x_2)}=2\sqrt{(x_1 x_2)(x_1' x_2')}\ge 2,$$
     结合 $x_1 x_2\ge 1$ 与 $x_1' x_2'\ge 1$ 得
     $$u_1 u_2=\lambda^2 x_1 x_2+(1-\lambda)^2 x_1' x_2'+\lambda(1-\lambda)(x_1 x_2'+x_1' x_2)\ge \lambda^2+(1-\lambda)^2+2\lambda(1-\lambda)=(\lambda+1-\lambda)^2=1.$$
     故 $(u_1,u_2)\in C$，$C$ 凸。
2. **核验 $f$ 满足 S5 全部条件**：
   定义 $f:\mathbb{R}^2\to[0,+\infty]$ 为 $C$ 的示性函数：
   $$f(x_1,x_2):=\begin{cases}0,&(x_1,x_2)\in C,\\ +\infty,&(x_1,x_2)\notin C.\end{cases}$$
   - $f$ 取值于 $[0,+\infty]$，且 $(1,1)\in C$ 故 $f(1,1)=0<+\infty$（至少一点有限）。
   - $\operatorname{epi}_{\mathbb{R}}(f)=C\times[0,+\infty)$ 是 $\mathbb{R}^2\times\mathbb{R}$ 中两个闭凸集的乘积，故闭且凸，即 $f$ 下半连续且凸。
3. **选取有限维 $F\subset E'$ 并计算 $g_F$**：
   取 $\varphi\in(\mathbb{R}^2)'$ 为第一坐标泛函 $\varphi(x_1,x_2)=x_1$，令 $F:=\operatorname{span}\{\varphi\}$，则 $\dim F=1<\infty$。
   令线性同胚 $\Phi:F^*\to\mathbb{R}$ 为 $\Phi(y)=y(\varphi)$，记 $y_s:=\Phi^{-1}(s)\in F^*$（即 $y_s(a\varphi)=as$）。对任意 $(x_1,x_2)\in\mathbb{R}^2$，$(q_F(x_1,x_2))(\varphi)=\varphi(x_1,x_2)=x_1$，故 $q_F(x_1,x_2)=y_{x_1}$。从而对任意 $s\in\mathbb{R}$：
   $$g_F(y_s)=\inf\{f(x_1,x_2):x_1=s,\;x_2\in\mathbb{R}\}=\inf_{x_2\in\mathbb{R}}f(s,x_2).$$
   - 若 $s>0$，取 $x_2=1/s>0$，则 $(s,1/s)\in C$，故 $f(s,1/s)=0$，从而 $g_F(y_s)=0$。
   - 若 $s\le 0$，则对任意 $x_2\in\mathbb{R}$ 均有 $(s,x_2)\notin C$（因 $C$ 中元素满足 $x_1>0$），故 $f(s,x_2)=+\infty$ 恒成立，从而 $g_F(y_s)=+\infty$。
4. **核验 $g_F$ 非下半连续**：
   取 $c=0$，次水平集为
   $$\{y\in F^*:g_F(y)\le 0\}=\{y_s:s>0\}=\Phi^{-1}((0,+\infty)).$$
   因 $(0,+\infty)$ 在 $\mathbb{R}$ 中不闭且 $\Phi$ 为同胚，该次水平集在 $F^*$ 中不闭（亦可直接看出 $(y_{1/n},0)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 在 $F^*\times\mathbb{R}$ 中收敛于 $(0,0)$，但 $g_F(0)=+\infty>0$ 故 $(0,0)\notin\operatorname{epi}_{\mathbb{R}}(g_F)$）。由共同预备引理 2，$g_F$ 不是下半连续的。

---

## S6　恢复与投影的精确关系

在共同设定下，对非负凸函数 $u:X\to[0,+\infty]$（$X$ 为实 Hausdorff 局部凸空间），其最大下半连续凸下界 $\bar u$ 良定义且唯一，即为 S4 中所构造的闭上图函数 $\bar u(x)=\inf\{t\in\mathbb{R}:(x,t)\in\overline{\operatorname{epi}_{\mathbb{R}}(u)}\}$：由 S4 的一般验证，$\operatorname{epi}_{\mathbb{R}}(\bar u)=\overline{\operatorname{epi}_{\mathbb{R}}(u)}$ 在 $X\times\mathbb{R}$ 中闭且凸、$\bar u\ge 0$、$\bar u\le u$，且对任意下半连续凸函数 $v\le u$（甚至仅下半连续且 $v\le u$），有 $\overline{\operatorname{epi}_{\mathbb{R}}(u)}\subset\operatorname{epi}_{\mathbb{R}}(v)$，从而由共同预备引理 1 得 $v\le\bar u$。特别地，对 $u=g_F$ 有 $\overline{g_F}=\widetilde{g}_F$，且按 S4 中的 $G$ 有 $\operatorname{epi}_{\mathbb{R}}(G)=\overline{\operatorname{epi}_{\mathbb{R}}(f)}$，即 $G=\bar f$。

### 1. 证明 $G=f$ 当且仅当 $f$ 下半连续

- **($\implies$)**：若 $G=f$，因 S4 已证明 $G$ 下半连续，故 $f$ 下半连续。
- **($\Longleftarrow$)**：若 $f$ 下半连续，结合共同设定中 $f$ 凸及 $f\le f$，可在 S4 的极大性中取竞争函数 $h=f$，得 $f\le G$。结合 S4 中的 $G\le f$，即得 $G=f$。

### 2. 证明 $\overline{g_F}=\overline{y\mapsto\inf_{r_{KF}z=y}\overline{g_K}(z)}$

设 $F\subset K\subset E'$ 为有限维子空间，定义 $m_{KF}:F^*\to[0,+\infty]$ 为
$$m_{KF}(y):=\inf_{r_{KF}z=y}\overline{g_K}(z)\qquad(y\in F^*).$$
先核验 $m_{KF}$ 满足 $\bar{}$ 记号的使用前提（非负且凸）：
- **非负性**：因 $\overline{g_K}\ge 0$，故 $m_{KF}(y)\ge 0$ 对所有 $y\in F^*$ 成立（且对 $x_0\in\operatorname{dom}(f)$，$m_{KF}(q_F x_0)\le g_F(q_F x_0)\le f(x_0)<+\infty$）。
- **凸性**：$\overline{g_K}$ 凸且 $r_{KF}:K^*\to F^*$ 线性。任取 $(y_1,t_1),(y_2,t_2)\in\operatorname{epi}_{\mathbb{R}}(m_{KF})$ 及 $\lambda\in[0,1]$。对任意 $\varepsilon>0$，存在 $z_1,z_2\in K^*$ 使 $r_{KF}z_i=y_i$ 且 $\overline{g_K}(z_i)<t_i+\varepsilon$（$i=1,2$）。由 $\operatorname{epi}_{\mathbb{R}}(\overline{g_K})$ 的凸性及 $r_{KF}$ 的线性性，$r_{KF}(\lambda z_1+(1-\lambda)z_2)=\lambda y_1+(1-\lambda)y_2$ 且 $\overline{g_K}(\lambda z_1+(1-\lambda)z_2)\le\lambda t_1+(1-\lambda)t_2+\varepsilon$，从而 $m_{KF}(\lambda y_1+(1-\lambda)y_2)\le\lambda t_1+(1-\lambda)t_2+\varepsilon$。令 $\varepsilon\downarrow 0$ 即证 $\operatorname{epi}_{\mathbb{R}}(m_{KF})$ 凸。

因此 $\overline{m_{KF}}$ 良定义。现利用 S4 第 3 步已建立的夹逼关系（此时 $\widetilde{g}_F=\overline{g_F}$、$\widetilde{g}_K=\overline{g_K}$）：
$$\overline{g_F}(y)\le m_{KF}(y)\le g_F(y)\qquad(\forall y\in F^*).$$
- 由 $m_{KF}\le g_F$：因 $\overline{m_{KF}}$ 是下半连续凸函数且 $\overline{m_{KF}}\le m_{KF}\le g_F$，依 $\overline{g_F}$ 作为 $g_F$ 最大下半连续凸下界的极大性，得
  $$\overline{m_{KF}}\le\overline{g_F}.$$
- 由 $\overline{g_F}\le m_{KF}$：因 $\overline{g_F}$ 是下半连续凸函数且 $\overline{g_F}\le m_{KF}$，依 $\overline{m_{KF}}$ 作为 $m_{KF}$ 最大下半连续凸下界的极大性，得
  $$\overline{g_F}\le\overline{m_{KF}}.$$

两式结合即证
$$\overline{g_F}=\overline{m_{KF}}=\overline{y\mapsto\inf_{r_{KF}z=y}\overline{g_K}(z)}.$$

### 3. 判断右式的最外层 $\bar{}$ 能否总省去

**不能总省去。**

**反例与完整核验**（沿用 S5 的构造）：
取 $E=\mathbb{R}^2$ 及 S5 中的闭凸集 $C=\{(x_1,x_2)\in\mathbb{R}^2:x_1\ge 0,\;x_2\ge 0,\;x_1 x_2\ge 1\}$ 与 $f=\iota_C:\mathbb{R}^2\to[0,+\infty]$。由 S5 已核验，$f$ 满足共同设定且还是下半连续的。

取有限维子空间 $K:=E'=(\mathbb{R}^2)'$（$\dim K=2<\infty$），并取 $F:=\operatorname{span}\{\varphi\}\subset K$，其中 $\varphi(x_1,x_2)=x_1$。于是 $F\subset K$ 均为 $E'$ 的有限维子空间。

1. **计算 $\overline{g_K}$**：由于 $K=E'$ 分离 $\mathbb{R}^2$ 中的点，线性映射 $q_K:\mathbb{R}^2\to K^*$ 单；又 $\dim\mathbb{R}^2=2=\dim K^*$，故 $q_K$ 是二维 Hausdorff 拓扑向量空间之间的线性同胚。对任意 $z\in K^*$，纤维 $\{x\in\mathbb{R}^2:q_K x=z\}=\{q_K^{-1}(z)\}$ 为单点集，从而
   $$g_K(z)=f(q_K^{-1}(z))\qquad(\forall z\in K^*).$$
   因 $f$ 在 $\mathbb{R}^2$ 上下半连续且凸，而 $q_K^{-1}:K^*\to\mathbb{R}^2$ 为线性同胚，故 $g_K=f\circ q_K^{-1}$ 在 $K^*$ 上已是下半连续且凸的，于是
   $$\overline{g_K}=g_K.$$
2. **比较左右两端（省略外层 $\bar{}$ 与否）**：由 S1 的传递恒等式，对一切 $y\in F^*$ 有
   $$m_{KF}(y)=\inf_{r_{KF}z=y}\overline{g_K}(z)=\inf_{r_{KF}z=y}g_K(z)=g_F(y).$$
   然而在 S5 中已算得 $g_F(0)=+\infty$，且对一切 $n\ge 1$ 有 $g_F(y_{1/n})=0$（其中 $y_s\in F^*$ 满足 $y_s(\varphi)=s$），故 $(y_{1/n},0)\in\operatorname{epi}_{\mathbb{R}}(g_F)$ 且 $(y_{1/n},0)\to(0,0)$。由此 $(0,0)\in\overline{\operatorname{epi}_{\mathbb{R}}(g_F)}=\operatorname{epi}_{\mathbb{R}}(\overline{g_F})$，结合 $\overline{g_F}\ge 0$ 得 $\overline{g_F}(0)=0$。于是
   $$\overline{g_F}(0)=0\neq+\infty=g_F(0)=\inf_{r_{KF}z=0}\overline{g_K}(z).$$

因此等式右端最外层的 $\bar{}$ 不能总省去。
