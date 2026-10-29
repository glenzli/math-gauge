# 半局部值的层化比较

设 $k$ 为域，$\mathrm{Sm}/k$ 为光滑、分离、有限型 $k$-概形的范畴，$\mathrm{Cor}_k$ 为有限对应范畴。设 $F:\mathrm{Cor}_k^{\mathrm{op}}\to\mathrm{Ab}$ 为加性反变函子（即带转移的预层，presheaf with transfers），且满足 $\mathbb A^1$-同伦不变性：对任意 $Y\in\mathrm{Sm}/k$，投影诱导的同态 $F(Y)\xrightarrow{\sim} F(Y\times_k\mathbb A^1_k)$ 是同构。

记 $F_{\mathrm{Zar}}$ 为 $F$ 关于 Zariski 拓扑的层化，$\eta:F\to F_{\mathrm{Zar}}$ 为典范态射。设 $X\in\mathrm{Sm}/k$ 拟射影，$\Sigma\subset |X|$ 为有限非空点集，$S=\operatorname{Spec}\mathcal O_{X,\Sigma}$ 为 $X$ 在 $\Sigma$ 处的半局部概形，定义
$$F(S)=\varinjlim_{\Sigma\subset U\subset X}F(U),\qquad F_{\mathrm{Zar}}(S)=\varinjlim_{\Sigma\subset U\subset X}F_{\mathrm{Zar}}(U).$$

---

### 主要结论

> **定理（Voevodsky）**  
> 典范限制同态
> $$\eta_S: F(S)\longrightarrow F_{\mathrm{Zar}}(S)$$
> 是阿贝尔群的**同构**。

---

## 一、 论证总体框架与逻辑结构

不失一般性，由于光滑概形是其连通分支的不交并，而有限点集 $\Sigma$ 仅与有限个连通分支相交；加之函子 $F$ 在不交并上取直和（加性范畴性质），我们可立即约化到 $X$ 是**连通且整（integral）**的情形。设 $k(X)$ 为 $X$ 的函数体，对应于泛点 $\eta$。

论证的核心是将 $\eta_S$ 嵌入到函数体的值 $F(k(X))$ 中进行比较，其逻辑链条如下：

```
                    F(S)  ------ \eta_S ----->  F_Zar(S)
                     |                               |
                     | 注入                          | 注入
                     v                               v
                   F(k(X)) <------ 等同 ------ F_Zar(k(X))
                     ||                              ||
        \bigcap_{x \in \Sigma} F_x  ======  \bigcap_{x \in \Sigma} F_x
```

具体分为以下关键步骤：
1. **层化保持茎**：在任意点 $y\in X$ 处，$(F_{\mathrm{Zar}})_y \cong F_y$。特别地，在泛点 $\eta$ 处，$F(k(X))\cong F_{\mathrm{Zar}}(k(X))$。
2. **单射性定理**：利用 Voevodsky 的相对曲线收缩与 $\mathbb A^1$-同伦构造，证明对半局部概形 $S$，限制映射
   $$F(S)\hookrightarrow F(k(X))$$
   是**单射**。由此立得 $\eta_S:F(S)\to F_{\mathrm{Zar}}(S)$ 是单射。
3. **极值刻画定理（未分歧性）**：证明 $F(S)$ 在 $F(k(X))$ 中的像恰好等于各个局部茎的交：
   $$\operatorname{Im}(F(S)\to F(k(X))) = \bigcap_{x\in\Sigma}\operatorname{Im}(F_x\to F(k(X))).$$
4. **满射性与同构**：由于 $F_{\mathrm{Zar}}(S)$ 注入 $F_{\mathrm{Zar}}(k(X))$ 且其像亦受限于 $\bigcap_{x\in\Sigma}F_x$，由上述像的重合性直接导出 $\eta_S$ 是**满射**，从而为同构。

---

## 二、 几何核心：曲线构造与 $\mathbb A^1$-同伦收缩

### 2.1 基础概念与同伦性质
- 在 $\mathrm{Cor}_k$ 中，若态射 $\alpha,\beta\in\mathrm{Cor}_k(Y, Z)$ 满足：存在 $H\in\mathrm{Cor}_k(Y\times_k\mathbb A^1, Z)$ 使得 $H|_{Y\times\{0\}}=\alpha$ 且 $H|_{Y\times\{1\}}=\beta$，则称 $\alpha$ 与 $\beta$ 是 $\mathbb A^1$-同伦的，记作 $\alpha\sim_{\mathbb A^1}\beta$。
- 由 $F$ 的 $\mathbb A^1$-同伦不变性，若 $\alpha\sim_{\mathbb A^1}\beta$，则诱导的同态相等：
  $$\alpha^* = \beta^*: F(Z)\longrightarrow F(Y).$$

### 2.2 相对曲线的移动引理（Moving Lemma on Curves）
设 $S_0$ 为光滑簇在有限点集处的半局部概形。设 $p:C\to S_0$ 为光滑仿射相对曲线，具有光滑射影紧化 $\bar C\to S_0$。设 $Z\subset C$ 是在 $S_0$ 上有限的闭子概形，并设 $s:S_0\to C$ 为 $p$ 的截面，满足
$$s(S_0)\cap Z = \emptyset.$$

> **引理 1**：在上述条件下，存在有限对应 $\Psi\in\mathrm{Cor}_{S_0}(S_0, C\setminus Z)$，使得在 $\mathrm{Cor}_{S_0}(S_0, C)$ 中有
> $$[s(S_0)] \sim_{\mathbb A^1} \Psi.$$

**引理 1 的证明**：
令 $Z_\infty = \bar C\setminus C$。由于 $S_0$ 是半局部整概形，$s(S_0)$ 与 $Z\cup Z_\infty$ 均为 $S_0$ 上的有限闭子概形且彼此不交。
由相对曲线上的 Riemann-Roch 定理，取充分大度数 $m\gg 0$ 以及支撑在 $Z_\infty$ 上的丰富因子 $D_\infty$，可得可逆层 $\mathcal L = \mathcal O_{\bar C}(m D_\infty)$。在有限闭子集 $s(S_0)\coprod Z$ 上的赋值映射
$$\Gamma(\bar C, \mathcal L)\twoheadrightarrow \mathcal L|_{s(S_0)}\oplus \mathcal L|_Z$$
是满射。
由于 $S_0$ 是半局部环的谱，其余子域上的相异点可被截面分离（若 $k$ 为有限域，可取充分大度数避免零点重合，或利用素数阶互素的有限转移论证）。因此，存在亚纯函数 $f\in k(\bar C)$，使得：
1. $f$ 在截面 $s(S_0)$ 处具有一阶零点；
2. $f$ 的其余零点与全部极点均与 $Z$ 及 $Z_\infty$ 不交。

此时，有主除子
$$(f) = [s(S_0)] + D_0 - D_\infty',$$
其中 $D_0, D_\infty'$ 均为 $S_0$ 上的有效有限对应，且其支撑完全落在 $C\setminus Z$ 中。
函数 $f$ 定义了态射 $f:\bar C\to\mathbb P^1_{S_0}$。利用 $\mathbb P^1$ 上的标准仿射线同伦（连接 $0$ 与 $1$），拉回至 $C$ 上即给出连接 $(f)_0$ 与 $(f)_1$ 的同伦。令 $\Psi = D_1 - D_0$（其中 $D_1=f^{-1}(1)$，同样避开 $Z$），即证得
$$[s(S_0)] \sim_{\mathbb A^1} \Psi \in \mathrm{Cor}_{S_0}(S_0, C\setminus Z).$$

### 2.3 初等纤维化与恒等对应的形变
将引理 1 推广到任意维数的光滑概形：
设 $\dim X = d$，$Z\subset X$ 为闭子集且 $Z\cap \Sigma = \emptyset$。
由 Artin 初等纤维化（Artin's Elementary Fibrations）与通有投影定理，在缩小仿射邻域后，存在包含 $\Sigma$ 的仿射开集 $U\subset X$ 以及态射
$$p: U\longrightarrow Y$$
满足：
1. $Y$ 是平滑仿射 $k$-概形，$\dim Y = d - 1$；
2. $p$ 是相对唯纳 1 的光滑态射，且具有相对射影紧化；
3. $Z\cap U$ 在 $Y$ 上是**有限**的；
4. 投影在 $\Sigma$ 上是单射，且 $\Sigma$ 中的点作为截面均不与 $Z\cap U$ 相交。

将基底变换至 $S_Y = \operatorname{Spec}\mathcal O_{Y, p(\Sigma)}$，沿用引理 1 的构造并将其延拓展平（spreading out）至 $Y$ 的充分小开邻域上，即得到下述关键结论：

> **命题 2（Voevodsky 收缩定理）**  
> 设 $X\in\mathrm{Sm}/k$，$Z\subset X$ 闭且 $\Sigma\cap Z=\emptyset$。则存在 $\Sigma$ 的仿射开邻域 $U$ 及有限对应
> $$\Phi\in\mathrm{Cor}_k(U, U\setminus Z),$$
> 使得若记 $j: U\setminus Z\hookrightarrow U$ 为开浸入，则在 $\mathrm{Cor}_k(U, U)$ 中有
> $$j\circ \Phi \sim_{\mathbb A^1} \mathrm{id}_U.$$

---

## 三、 单射性定理的证明

### 3.1 限制到函数体的单射性
> **定理 3**：限制映射 $F(S)\longrightarrow F(k(X))$ 是单射。

**证明**：  
任取 $a\in F(S)$，若 $a$ 在 $F(k(X))$ 中的像为 $0$。
根据半局部值作为滤过极限的定义，$a$ 在某个仿射开邻域 $U_0\supset \Sigma$ 上有代表元 $a\in F(U_0)$。
因为在泛点处 $a|_\eta = 0$，且 $F(k(X))=\varinjlim_{\emptyset\ne V} F(V)$，故存在稠开集 $V\subset U_0$ 使得
$$a|_V = 0 \in F(V).$$
置闭子集 $Z = U_0\setminus V$。由 $V$ 的稠密性及 $a|_\eta=0$，可知 $Z$ 为真闭子集，且 $\Sigma\cap Z = \emptyset$（否则可先将 $U_0$ 缩小使 $\Sigma\subset V$）。

对数据 $(U_0, \Sigma, Z)$ 应用命题 2，存在开邻域 $U\subset U_0$（$\Sigma\subset U$）以及对应 $\Phi\in\mathrm{Cor}_k(U, U\setminus Z)$ 满足 $j\circ\Phi \sim_{\mathbb A^1} \mathrm{id}_U$。
由于 $F$ 具有 $\mathbb A^1$-同伦不变性，应用函子 $F$ 得：
$$a|_U = \mathrm{id}_U^*(a|_U) = (j\circ \Phi)^*(a|_U) = \Phi^*(j^*(a|_U)) = \Phi^*(a|_{U\setminus Z}).$$
但 $U\setminus Z \subset V$，已知 $a|_V = 0$，从而 $a|_{U\setminus Z} = 0$。因此
$$a|_U = \Phi^*(0) = 0 \in F(U).$$
这表明 $a$ 在极限群 $F(S)=\varinjlim_{\Sigma\subset U}F(U)$ 中等于 $0$。单射性得证。

### 3.2 导出 $\eta_S$ 的单射性
考虑交换图表：
$$\begin{array}{ccc}
F(S) & \xrightarrow{\quad\eta_S\quad} & F_{\mathrm{Zar}}(S) \\
\Big\downarrow & & \Big\downarrow \\
F(k(X)) & \xrightarrow{\quad\sim\quad} & F_{\mathrm{Zar}}(k(X))
\end{array}$$
- 底部的横向映射是同构：因为预层层化在任意拓扑空间上均保持点处的茎，故对于泛点 $\eta$，$(F_{\mathrm{Zar}})_\eta \cong F_\eta$，即 $F_{\mathrm{Zar}}(k(X))\cong F(k(X))$。
- 左侧纵向映射由定理 3 保证为**单射**。

若 $a\in F(S)$ 满足 $\eta_S(a) = 0 \in F_{\mathrm{Zar}}(S)$，则 $a$ 在 $F_{\mathrm{Zar}}(k(X))$ 中的像必然为 $0$。由底横向同构及图表交换性，可知 $a$ 在 $F(k(X))$ 中的像必为 $0$。
再由左侧纵向映射为单射，立即推得
$$a = 0 \in F(S).$$
因此，$\eta_S$ 必定是**单射**。

---

## 四、 像的极值刻画与满射性证明

### 4.1 局部茎的交
对每个 $x\in\Sigma$，记 $F_x = \varinjlim_{x\in U} F(U)$ 为在点 $x$ 处的茎。由于 $x\in S$，自然存在限制映射 $F(S)\to F_x$ 以及 $F_x\to F(k(X))$，且复合映射等于 $F(S)\to F(k(X))$。
因此，
$$\operatorname{Im}(F(S)\to F(k(X))) \subseteq \bigcap_{x\in\Sigma} \operatorname{Im}(F_x\to F(k(X))).$$

> **定理 4**：上述包含关系为等式，即
> $$\operatorname{Im}(F(S)\to F(k(X))) = \bigcap_{x\in\Sigma} \operatorname{Im}(F_x\to F(k(X))).$$

**证明**：  
设 $\xi\in F(k(X))$ 属于每个 $F_x$（$x\in\Sigma$）在 $F(k(X))$ 中的像。
这意味着对每个 $x\in\Sigma$，存在包含 $x$ 的开邻域 $U_x$ 及截面 $s_x\in F(U_x)$，使得
$$s_x|_\eta = \xi \in F(k(X)).$$
置 $Z_x = X\setminus U_x$，则 $x\notin Z_x$。定义
$$Z = \bigcap_{x\in\Sigma} Z_x.$$
因为对任意 $x\in\Sigma$ 都有 $x\notin Z_x$，所以 $\Sigma\cap Z = \emptyset$。
故 $U = X\setminus Z = \bigcup_{x\in\Sigma} U_x$ 是包含 $\Sigma$ 的开邻域。

利用初等纤维化以及在每个截面 $s_x$ 处的局部分离构造（由引理 1 与命题 2 对各分支独立做移动），在进一步缩小开邻域至 $U'\subset U$（$\Sigma\subset U'$）后，存在一族有限对应
$$\Psi_x\in\mathrm{Cor}_k(U', U_x)\quad (x\in\Sigma),$$
使得若记 $j_x: U_x\hookrightarrow U$ 为自然包含，则在 $\mathrm{Cor}_k(U', U)$ 中满足：
$$\sum_{x\in\Sigma} j_x\circ \Psi_x \sim_{\mathbb A^1} \mathrm{id}_{U'}.$$

现定义元
$$s = \sum_{x\in\Sigma} \Psi_x^*(s_x) \in F(U').$$
考查 $s$ 在泛点 $\eta$ 处的值：由于每个 $s_x$ 在泛点处均为 $\xi$，由函子性与同伦不变性：
$$s|_\eta = \sum_{x\in\Sigma} \Psi_x^*(s_x|_\eta) = \sum_{x\in\Sigma} \Psi_x^*(\xi) = \left(\sum_{x\in\Sigma} j_x\circ \Psi_x\right)^*(\xi) = \mathrm{id}_{U'}^*(\xi) = \xi.$$
因此，$s\in F(U')$ 在泛点处还原出 $\xi$。由于 $U'\supset \Sigma$，$s$ 定义了 $F(S)$ 中的一个元，故
$$\xi \in \operatorname{Im}(F(S)\to F(k(X))).$$
这证明了逆包含关系，定理 4 得证。

### 4.2 层化值的结构与满射性完成
考虑层化后的半局部值 $F_{\mathrm{Zar}}(S)$：
1. **$F_{\mathrm{Zar}}(S)$ 在泛点处的像**：
   任取 $\zeta\in F_{\mathrm{Zar}}(S)$，由半局部极限定义，$\zeta$ 来自某个 $F_{\mathrm{Zar}}(U)$（$U\supset \Sigma$）。
   对于任意 $x\in\Sigma$，态射 $F_{\mathrm{Zar}}(S)\to F_{\mathrm{Zar}}(k(X))$ 分解为：
   $$F_{\mathrm{Zar}}(S)\longrightarrow (F_{\mathrm{Zar}})_x \longrightarrow F_{\mathrm{Zar}}(k(X)).$$
   由于层化保持茎，有 $(F_{\mathrm{Zar}})_x \cong F_x$。将泛点处 $F_{\mathrm{Zar}}(k(X))$ 与 $F(k(X))$ 等同后，$\zeta|_\eta$ 必然落在 $\operatorname{Im}(F_x\to F(k(X)))$ 中。对所有 $x\in\Sigma$ 取交，即得：
   $$\operatorname{Im}(F_{\mathrm{Zar}}(S)\to F(k(X))) \subseteq \bigcap_{x\in\Sigma}\operatorname{Im}(F_x\to F(k(X))).$$

2. **泛点映射的单射性**：
   若 $\zeta\in F_{\mathrm{Zar}}(S)$ 满足 $\zeta|_\eta = 0 \in F(k(X))$。
   对任意 $x\in\Sigma$，茎元 $\zeta_x\in (F_{\mathrm{Zar}})_x \cong F_x$ 在泛点处为 $0$。
   对单点集 $\{x\}$ 应用定理 3，知 $F_x\to F(k(X))$ 是单射，故对一切 $x\in\Sigma$ 均有
   $$\zeta_x = 0 \in (F_{\mathrm{Zar}})_x.$$
   在半局部概形 $S$ 上，闭点集为 $\Sigma$ 中的极大点集合 $\Sigma_0$。一个 Zariski 层的截面若在所有闭点处的茎均为 $0$，则由层公理，必存在一个包含所有闭点的开集使其限制为 $0$。而在半局部概形中，包含全部闭点的开集只能是整个 $S$。因此，截面必在 $S$ 上整体为零，即
   $$\zeta = 0 \in F_{\mathrm{Zar}}(S).$$
   这证明了映射 $F_{\mathrm{Zar}}(S)\longrightarrow F_{\mathrm{Zar}}(k(X))$ 也是**单射**。

3. **满射性论证**：
   结合定理 4 与上述结果，有：
   $$\operatorname{Im}(F(S)\to F(k(X))) = \bigcap_{x\in\Sigma} F_x = \operatorname{Im}(F_{\mathrm{Zar}}(S)\to F(k(X))).$$
   任取 $\xi\in F_{\mathrm{Zar}}(S)$，由上述等式，存在 $a\in F(S)$ 使得
   $$a|_\eta = \xi|_\eta \in F(k(X)).$$
   考虑差元
   $$\delta = \xi - \eta_S(a) \in F_{\mathrm{Zar}}(S).$$
   由于 $\delta|_\eta = \xi|_\eta - a|_\eta = 0$，再利用 $F_{\mathrm{Zar}}(S)\to F_{\mathrm{Zar}}(k(X))$ 的单射性，立即得到
   $$\delta = 0 \implies \xi = \eta_S(a).$$
   因此，$\eta_S$ 是**满射**。

---

## 五、 总结与推论

结合第三节的单射性与第四节的满射性，确立了典范同态
$$\eta_S: F(S)\xrightarrow{\sim} F_{\mathrm{Zar}}(S)$$
为**同构**。

### 理论推论
1. **Nisnevich 拓扑下的比较**：
   同样的方法适用于 Nisnevich 开覆盖。由于半局部 Hensel 环在 Nisnevich 拓扑下的完全分解性质，同理论证可证 $F(S)\xrightarrow{\sim} F_{\mathrm{Nis}}(S)$。结合本定理即导出：
   $$F_{\mathrm{Zar}}(S)\cong F_{\mathrm{Nis}}(S).$$
   这构成了 Voevodsky 证明“对任意 $\mathbb A^1$-同伦不变带转移预层 $F$，其 Zariski 层化即为其 Nisnevich 层化（$F_{\mathrm{Zar}}\cong F_{\mathrm{Nis}}$），且高阶层上同调群重合 $H^n_{\mathrm{Zar}}(X, F_{\mathrm{Zar}})\cong H^n_{\mathrm{Nis}}(X, F_{\mathrm{Nis}})$”的核心基石。
2. **半局部高阶上同调消失**：
   该同构亦是建立半局部环上同调消逝定理 $H^i_{\mathrm{Zar}}(S, F_{\mathrm{Zar}}) = 0$（$\forall i > 0$）与 Gersten 猜想在动机上同调中成立的前提。
