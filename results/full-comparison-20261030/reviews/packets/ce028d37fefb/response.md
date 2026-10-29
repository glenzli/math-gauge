在本题中，我们在 ZFC 集合论框架下，固定 Grothendieck 宇宙 $\mathcal U\in\mathcal V$ 且 $\mathbb N\in\mathcal U$。所有涉及的拓扑空间的底集均属于 $\mathcal U$。

---

### 一、 底集与拓扑的确定

#### 1. 底集的确定
考虑单点空间 $* = \{*\}$。由于 $*$ 是紧全不连通空间，显然 $* \in \operatorname{Prof}_{\mathcal U}$，且 $h_*$ 是由 $*$ 代表的探针函子。
根据探针记录的定义与 Yoneda 引理，当测试对象取 $S = *$ 时，实现空间 $M(X,Y)$ 的底集必然满足：
$$M(X,Y) \cong C(*, M(X,Y)) \cong \mathcal H_{X,Y}(*) = \operatorname{Nat}(h_* \times h_X, h_Y) \cong \operatorname{Nat}(h_X, h_Y).$$

设 $k(X)$ 为 $X$ 的紧生成修饰（Kelleyfication / $k$-反射），即 $k(X)$ 与 $X$ 拥有相同的底集，其开集定义为与 $X$ 的每个紧子集相交均为相对开集的子集。
任何自然变换 $\eta \in \operatorname{Nat}(h_X, h_Y)$ 在每个测试点 $x \in X$（即连续映射 $i_x: * \to X$）上诱导映射 $f: X \to Y$，$f(x) = \eta_*(i_x)$。由自然性，对任意 $S \in \operatorname{Prof}_{\mathcal U}$ 及连续映射 $g: S \to X$，复合 $f \circ g: S \to Y$ 必为连续映射。因为任意紧 Hausdorff 空间都是某个 profinite 空间的连续商（见下文引理 1），故 $f$ 在 $X$ 的每个紧子集上均连续，这等价于 $f: k(X) \to Y$ 连续。

因此，**实现空间 $M(X,Y)$ 的底集**为：
$$\underline{M(X,Y)} = C(k(X), Y) = \{f: X \to Y \mid \forall K \subseteq X \text{ 紧}, f|_K: K \to Y \text{ 连续}\}.$$
> 特别地，当 $X$ 本身是紧生成空间（如度量空间、CW 复形、局部紧 Hausdorff 空间等）时，$k(X) = X$，底集即为通常的连续映射集 $C(X,Y)$。
> 由 $\underline{X}, \underline{Y} \in \mathcal U$ 可知 $Y^X \in \mathcal U$，故 $\underline{M(X,Y)} \in \mathcal U$。

#### 2. 拓扑的确定
**$M(X,Y)$ 的拓扑**取为**紧开拓扑**（Compact-Open Topology）$\tau_{\mathrm{co}}$：
以如下形式的子集为拓扑的准基（Subbase）：
$$V(K, U) = \{f \in M(X,Y) \mid f(K) \subseteq U\},$$
其中 $K \subseteq X$ 为任意紧子集（等价于 $k(X)$ 中的紧子集），$U \subseteq Y$ 为任意开子集。

> **注记（紧生成拓扑修饰）**：若在紧生成 Hausdorff 空间范畴 $\mathbf{CGHaus}$ 中考虑，亦可取其紧生成修饰 $k(C_{\mathrm{co}}(k(X), Y))$。后文将严格证明，由于 profinite 空间 $S$ 是紧 Hausdorff 空间，两种拓扑在探针函子 $h_{(-)}$ 作用下产生完全相同的测试记录，具有相同的空间实现性质。在此，我们选用最标准、直接的紧开拓扑空间 $M(X,Y) = (C(k(X), Y), \tau_{\mathrm{co}})$。

#### 3. Hausdorff 性质的验证
任取两不同映射 $f, g \in M(X,Y)$，必存在 $x_0 \in X$ 使得 $f(x_0) \neq g(x_0)$。
因为单点集 $\{x_0\} \subseteq X$ 是紧子集，且 $Y$ 为 Hausdorff 空间，存在 $Y$ 中的互不相交开集 $U_1, U_2$ 使得 $f(x_0) \in U_1$，$g(x_0) \in U_2$。
则 $V(\{x_0\}, U_1)$ 与 $V(\{x_0\}, U_2)$ 为 $M(X,Y)$ 中分别包含 $f, g$ 的开邻域，且：
$$V(\{x_0\}, U_1) \cap V(\{x_0\}, U_2) = V(\{x_0\}, U_1 \cap U_2) = V(\{x_0\}, \emptyset) = \emptyset.$$
因此，$M(X,Y)$ 是 Hausdorff 空间。

---

### 二、 主定理陈述

定义求值映射族 $\mathrm{ev}_S: h_{M(X,Y)}(S) \times h_X(S) \to h_Y(S)$（$S \in \operatorname{Prof}_{\mathcal U}$）为：
$$(\mathrm{ev}_S(\sigma, g))(s) = (\sigma(s))(g(s)) \qquad (\forall s \in S),$$
其中 $\sigma \in C(S, M(X,Y))$，$g \in C(S, X)$。

**主定理**：
1. **空间实现定理**：族 $\mathrm{ev} = (\mathrm{ev}_S)_{S \in \operatorname{Prof}_{\mathcal U}}$ 定义了一个良定的自然变换
   $$\mathrm{ev}: h_{M(X,Y)} \times h_X \longrightarrow h_Y,$$
   且对任意 $S \in \operatorname{Prof}_{\mathcal U}$，映射
   $$\omega_S: C(S, M(X,Y)) \xrightarrow{\sim} \mathcal H_{X,Y}(S), \qquad \sigma \longmapsto \mathrm{ev} \circ (h_\sigma \times I_{h_X})$$
   给出在 $S$ 上自然同构的双射。

2. **一般参数空间的泛性质**：对于任意 Hausdorff 参数空间 $Z$（其底集属于 $\mathcal U$），映射
   $$\Theta_Z: \operatorname{Nat}(h_Z, h_{M(X,Y)}) \xrightarrow{\sim} \operatorname{Nat}(h_Z \times h_X, h_Y), \qquad \alpha \longmapsto \mathrm{ev} \circ (\alpha \times I_{h_X})$$
   是双射，且关于参数空间 $Z$ 的连续变换（连续映射 $w: Z' \to Z$）自然。

3. **函子性与相容性**：
   - 对任意连续映射 $f: X \to X'$，诱导预复合连续映射 $M(f, Y): M(X', Y) \to M(X, Y)$，与参数化映射记录关于 $X$ 的反变函子性相容；
   - 对任意连续映射 $g: Y \to Y'$，诱导后复合连续映射 $M(X, g): M(X, Y) \to M(X, Y')$，与参数化映射记录关于 $Y$ 的协变函子性相容。

---

### 三、 构造与引理准备

#### 引理 1（紧 Hausdorff 空间的 Profinite 覆盖与商性质）
设 $K$ 为底集属于 $\mathcal U$ 的紧 Hausdorff 空间。记 $K^\delta$ 为具离散拓扑的集合 $K$。
则其 Stone-Čech 紧化 $S = \beta(K^\delta) \in \operatorname{Prof}_{\mathcal U}$，且连续延拓映射
$$\pi: \beta(K^\delta) \twoheadrightarrow K$$
是拓扑商映射（Quotient map）。

*证明*：
$K^\delta$ 是离散空间，其 Stone-Čech 紧化 $\beta(K^\delta)$ 是紧全不连通 Hausdorff 空间（即 Stone 空间），其底集为 $K^\delta$ 上的超滤子集，显然 $\beta(K^\delta) \in \mathcal U$，故 $\beta(K^\delta) \in \operatorname{Prof}_{\mathcal U}$。
恒等映射 $\mathrm{id}: K^\delta \to K$ 连续，由 Stone-Čech 紧化的泛性质，存在唯一的连续延拓 $\pi: \beta(K^\delta) \to K$。
因 $K^\delta$ 在 $\beta(K^\delta)$ 中稠密且 $K$ 紧，$\pi$ 必为满射。
又因 $\beta(K^\delta)$ 紧且 $K$ 为 Hausdorff 空间，连续满射 $\pi$ 必为闭映射，从而 $\pi$ 是拓扑商映射。 $\square$

**推论 1.1**：映射 $f: X \to Y$ 满足“对所有 $S \in \operatorname{Prof}_{\mathcal U}$ 及所有连续映射 $g: S \to X$，$f \circ g$ 均连续”当且仅当 $f \in C(k(X), Y)$。
*证明*：
充分性：若 $f \in C(k(X), Y)$，任取 $S \in \operatorname{Prof}_{\mathcal U}$ 及连续映射 $g: S \to X$。由于 $S$ 紧，其像 $g(S)$ 是 $X$ 的紧子集。在紧子集 $g(S)$ 上，$X$ 与 $k(X)$ 的子空间拓扑完全相同，故 $g: S \to k(X)$ 连续，从而 $f \circ g: S \to Y$ 连续。
必要性：任取 $X$ 的紧子集 $K \subseteq X$。由引理 1，存在 $S \in \operatorname{Prof}_{\mathcal U}$ 及商映射 $\pi: S \twoheadrightarrow K$。包含映射 $i_K: K \hookrightarrow X$ 使得 $g = i_K \circ \pi: S \to X$ 连续。按条件，$f \circ g = (f|_K) \circ \pi: S \to Y$ 连续。因 $\pi$ 是商映射，必有 $f|_K: K \to Y$ 连续。由紧生成空间的定义，$f: k(X) \to Y$ 连续。 $\square$

**推论 1.2**：对于任意 Hausdorff 空间 $W$，有自然同构
$$\operatorname{Nat}(h_W, h_Y) \cong C(k(W), Y).$$
特别地，$h_W = h_{k(W)}$ 作为 $\operatorname{Prof}_{\mathcal U}^{\mathrm{op}} \to \mathbf{Set}_{\mathcal V}$ 的函子恒等。

---

#### 引理 2（Whitehead 定理：紧空间的乘积保持商映射）
设 $S$ 是紧 Hausdorff 空间。则函子 $- \times S: \mathbf{Top} \to \mathbf{Top}$ 保持商映射。
特别地，若 $W$ 是 $k$-空间，则 $W \times S$ 亦为 $k$-空间，且对于任意空间 $X$，有自然的同胚：
$$k(X \times S) \cong k(X) \times S.$$

*证明*：
因为 $S$ 是局部紧 Hausdorff 空间，由一般的拓扑指数律，函子 $- \times S$ 具有右伴随 $C_{\mathrm{co}}(S, -)$。
作为左伴随，$- \times S$ 保持所有极限与余极限，特别地，保持满同态即保持拓扑商映射。
任何 $k$-空间 $W$ 都是其所有紧子集拓扑不交并的商空间：
$$q: \coprod_{K \subseteq W \text{ 紧}} K \twoheadrightarrow W.$$
作用 $- \times S$ 得商映射：
$$q \times \mathrm{id}_S: \coprod_{K \subseteq W \text{ 紧}} (K \times S) \twoheadrightarrow W \times S.$$
由于每个 $K \times S$ 是两个紧 Hausdorff 空间的乘积，依然是紧 Hausdorff 空间，故 $W \times S$ 表达为紧 Hausdorff 空间之和的商空间，因此 $W \times S$ 是 $k$-空间。
对任意空间 $X$，商映射 $k(X) \to X$ 诱导商映射 $k(X) \times S \to X \times S$，由于源空间 $k(X) \times S$ 已是 $k$-空间，根据紧生成修饰的泛性质，即有 $k(X \times S) \cong k(X) \times S$。 $\square$

---

#### 引理 3（针对 Profinite 测试空间的指数同构）
设 $S \in \operatorname{Prof}_{\mathcal U}$，对任意 Hausdorff 空间 $X, Y$，典范映射（Currying / Uncurrying）
$$\Lambda: C(S \times k(X), Y) \xrightarrow{\sim} C(S, C_{\mathrm{co}}(k(X), Y)) = C(S, M(X,Y))$$
$$(\Lambda(F)(s))(x) = F(s, x)$$
是良定的双射。

*证明*：
1. **$\Lambda$ 的良定性**：
   设 $F: S \times k(X) \to Y$ 连续。需证对每个 $s \in S$，$F(s, -) \in M(X,Y)$，且映射 $\widehat{F}: s \mapsto F(s, -)$ 连续。
   显然限制映射 $F(s, -): k(X) \to Y$ 连续，故 $F(s, -) \in M(X,Y)$。
   为证 $\widehat{F}: S \to M(X,Y)$ 连续，取准基开集 $V(K, U)$，其中 $K \subseteq k(X)$ 为紧子集，$U \subseteq Y$ 为开集。
   $$\widehat{F}^{-1}(V(K, U)) = \{s \in S \mid F(\{s\} \times K) \subseteq U\}.$$
   因 $F$ 连续，$F^{-1}(U)$ 是 $S \times k(X)$ 中的开集，且 $\{s\} \times K \subseteq F^{-1}(U)$。
   由 Wallace 管状引理（Tube Lemma），由于 $K$ 是紧集，存在 $s$ 在 $S$ 中的开邻域 $W_s$ 使得 $W_s \times K \subseteq F^{-1}(U)$。
   这意味着对任意 $s' \in W_s$，均有 $F(\{s'\} \times K) \subseteq U$，即 $W_s \subseteq \widehat{F}^{-1}(V(K, U))$。
   因此 $\widehat{F}^{-1}(V(K, U))$ 在 $S$ 中是开集，$\widehat{F}$ 连续。

2. **逆映射的良定性**：
   设 $\sigma: S \to M(X,Y) = C_{\mathrm{co}}(k(X), Y)$ 连续。定义反去携映射：
   $$\widetilde{\sigma}: S \times k(X) \to Y, \qquad \widetilde{\sigma}(s, x) = (\sigma(s))(x).$$
   需证 $\widetilde{\sigma}$ 连续。
   由引理 2，$S \times k(X)$ 是 $k$-空间，因此只需证明 $\widetilde{\sigma}$ 在 $S \times k(X)$ 的每一个紧子集 $L$ 上连续。
   设 $L \subseteq S \times k(X)$ 为紧子集。记投影 $p_2: S \times k(X) \to k(X)$。
   则 $K_L = p_2(L)$ 是 $k(X)$ 中的紧子集。显然 $L \subseteq S \times K_L$。
   考虑限制映射：
   $$\mathrm{res}_{K_L}: C_{\mathrm{co}}(k(X), Y) \longrightarrow C_{\mathrm{co}}(K_L, Y), \qquad f \longmapsto f|_{K_L}.$$
   任取 $C_{\mathrm{co}}(K_L, Y)$ 的准基开集 $V_{K_L}(C, U)$（$C \subseteq K_L$ 紧，$U \subseteq Y$ 开），其原像为 $V_{k(X)}(C, U)$，因 $C$ 亦为 $k(X)$ 的紧子集，故原像是开集，$\mathrm{res}_{K_L}$ 连续。
   因此，复合映射 $\sigma_{K_L} = \mathrm{res}_{K_L} \circ \sigma: S \to C_{\mathrm{co}}(K_L, Y)$ 连续。
   由于 $K_L$ 是紧 Hausdorff 空间（因而局部紧），由古典指数律（Kelley-Morse 定理）：
   $$\widetilde{\sigma_{K_L}}: S \times K_L \longrightarrow Y, \qquad (s, x) \longmapsto (\sigma_{K_L}(s))(x) = (\sigma(s))(x)$$
   是连续映射。
   由于 $L \subseteq S \times K_L$ 是子空间，限制 $\widetilde{\sigma}|_L = \widetilde{\sigma_{K_L}}|_L$ 连续。
   由 $S \times k(X)$ 的紧生成性，$\widetilde{\sigma}: S \times k(X) \to Y$ 连续。
3. 两映射互为逆映射，故为双射。 $\square$

---

### 四、 完整论证与主定理的证明

#### 1. 求值自然变换 $\mathrm{ev}$ 的构造与良定性
对任意 $S \in \operatorname{Prof}_{\mathcal U}$，求值映射定义为：
$$\mathrm{ev}_S: C(S, M(X,Y)) \times C(S, X) \longrightarrow C(S, Y),$$
$$\mathrm{ev}_S(\sigma, g)(s) = (\sigma(s))(g(s)).$$

- **连续性**：由引理 3，$\sigma \in C(S, M(X,Y))$ 对应连续映射 $\widetilde{\sigma}: S \times k(X) \to Y$。
  由于 $S$ 紧，连续映射 $g: S \to X$ 的像 $g(S)$ 紧，故 $g: S \to k(X)$ 亦连续。
  对角映射 $(\mathrm{id}_S, g): S \to S \times k(X)$（$s \mapsto (s, g(s))$）连续。
  则 $\mathrm{ev}_S(\sigma, g) = \widetilde{\sigma} \circ (\mathrm{id}_S, g): S \to Y$ 是两个连续映射的复合，因而是连续映射，即 $\mathrm{ev}_S(\sigma, g) \in C(S, Y) = h_Y(S)$。
- **自然性**：设 $u: S' \to S$ 是 $\operatorname{Prof}_{\mathcal U}$ 中的态射。
  对任意 $\sigma \in h_{M(X,Y)}(S)$，$g \in h_X(S)$ 及任意 $s' \in S'$：
  $$(h_Y(u)(\mathrm{ev}_S(\sigma, g)))(s') = (\mathrm{ev}_S(\sigma, g))(u(s')) = (\sigma(u(s')))(g(u(s'))),$$
  $$(\mathrm{ev}_{S'}((h_{M(X,Y)} \times h_X)(u)(\sigma, g)))(s') = \mathrm{ev}_{S'}(\sigma \circ u, g \circ u)(s') = ((\sigma \circ u)(s'))((g \circ u)(s')) = (\sigma(u(s')))(g(u(s'))).$$
  二者完全一致，故 $\mathrm{ev}$ 是良定的自然变换。

#### 2. 定理 1（空间实现定理）的证明
对固定的 $S \in \operatorname{Prof}_{\mathcal U}$，需证
$$\omega_S: C(S, M(X,Y)) \longrightarrow \mathcal H_{X,Y}(S) = \operatorname{Nat}(h_S \times h_X, h_Y)$$
给出双射。

根据积函子的逐点定义，对任意 $T \in \operatorname{Prof}_{\mathcal U}$，
$$(h_S \times h_X)(T) = C(T, S) \times C(T, X) \cong C(T, S \times X) = h_{S \times X}(T).$$
由引理 1 的推论 1.2，有典范同构：
$$\mathcal H_{X,Y}(S) = \operatorname{Nat}(h_S \times h_X, h_Y) \cong \operatorname{Nat}(h_{S \times X}, h_Y) \cong C(k(S \times X), Y).$$
再结合引理 2（$k(S \times X) \cong S \times k(X)$），得到：
$$\mathcal H_{X,Y}(S) \cong C(S \times k(X), Y).$$
由引理 3 的指数双射 $\Lambda$：
$$C(S \times k(X), Y) \cong C(S, M(X,Y)).$$
追踪元素：给定 $\sigma \in C(S, M(X,Y))$，其诱导的自然变换 $\alpha = \omega_S(\sigma) \in \operatorname{Nat}(h_S \times h_X, h_Y)$ 在测试对象 $T \in \operatorname{Prof}_{\mathcal U}$ 上的作用为：
对任意 $(u, v) \in C(T, S) \times C(T, X)$ 及 $t \in T$，
$$(\alpha_T(u, v))(t) = \mathrm{ev}_T(\sigma \circ u, v)(t) = (\sigma(u(t)))(v(t)).$$
这恰好对应于通过引理 3 指数同构得到的映射。因此，$\omega_S$ 是双射。
自然性源于 $\mathrm{ev}$ 的自然性与范畴论伴随的典范性质。

---

#### 3. 定理 2（一般参数空间的泛性质）的证明
设 $Z$ 为任意底集属于 $\mathcal U$ 的 Hausdorff 空间。考虑映射
$$\Theta_Z: \operatorname{Nat}(h_Z, h_{M(X,Y)}) \longrightarrow \operatorname{Nat}(h_Z \times h_X, h_Y), \qquad \alpha \longmapsto \mathrm{ev} \circ (\alpha \times I_{h_X}).$$

- **单射性**：
  设 $\alpha, \beta \in \operatorname{Nat}(h_Z, h_{M(X,Y)})$ 使得 $\Theta_Z(\alpha) = \Theta_Z(\beta)$。
  任取 $S \in \operatorname{Prof}_{\mathcal U}$ 及 $\zeta \in h_Z(S) = C(S, Z)$。
  对任意 $x \in X$，记常值映射 $c_x \in C(S, X)$ 为 $c_x(s) = x$。
  将 $(\zeta, c_x)$ 代入 $\Theta_Z(\alpha)_S$ 与 $\Theta_Z(\beta)_S$：
  $$(\Theta_Z(\alpha)_S(\zeta, c_x))(s) = (\alpha_S(\zeta)(s))(c_x(s)) = (\alpha_S(\zeta)(s))(x),$$
  $$(\Theta_Z(\beta)_S(\zeta, c_x))(s) = (\beta_S(\zeta)(s))(c_x(s)) = (\beta_S(\zeta)(s))(x).$$
  因 $\Theta_Z(\alpha) = \Theta_Z(\beta)$，对所有 $s \in S, x \in X$，上述二式相等。
  这表明作为 $S \to M(X,Y)$ 的映射，$\alpha_S(\zeta)(s)$ 与 $\beta_S(\zeta)(s)$ 在每个 $x \in X$ 处的取值均相同，故 $\alpha_S(\zeta)(s) = \beta_S(\zeta)(s)$。
  从而 $\alpha_S(\zeta) = \beta_S(\zeta)$，由 $S$ 与 $\zeta$ 的任意性知 $\alpha = \beta$。单射性得证。

- **满射性**：
  设 $\Phi \in \operatorname{Nat}(h_Z \times h_X, h_Y) \cong \operatorname{Nat}(h_{Z \times X}, h_Y)$。
  由推论 1.2，$\Phi$ 唯一对应于连续映射
  $$\Psi: k(Z \times X) \longrightarrow Y.$$
  由紧生成空间的性质，$k(Z \times X) \cong k(k(Z) \times k(X))$，故 $\Psi: k(k(Z) \times k(X)) \to Y$ 连续。
  根据紧开拓扑的指数性质：
  映射 $f: k(Z) \to C_{\mathrm{co}}(k(X), Y) = M(X,Y)$（定义为 $(f(z))(x) = \Psi(z, x)$）连续当且仅当对 $k(Z)$ 的每个紧子集 $K_Z$，限制 $f|_{K_Z}: K_Z \to M(X,Y)$ 连续。
  对任意紧子集 $K_Z \subseteq k(Z)$，$K_Z$ 是紧 Hausdorff 空间。由引理 2，$K_Z \times k(X)$ 是 $k$-空间，故 $\Psi|_{K_Z \times k(X)}: K_Z \times k(X) \to Y$ 连续。
  由引理 3 的指数引理，携变映射 $K_Z \to M(X,Y)$ 连续。
  由 $k(Z)$ 的紧生成性，这证明了 $f: k(Z) \to M(X,Y)$ 连续！
  由推论 1.2，$f \in C(k(Z), M(X,Y))$ 唯一确定一个自然变换 $\alpha \in \operatorname{Nat}(h_Z, h_{M(X,Y)})$，其在 $S \in \operatorname{Prof}_{\mathcal U}$ 上的分量为：
  $$\alpha_S(\zeta) = f \circ \zeta \qquad (\forall \zeta \in C(S, Z)).$$
  计算其像：
  $$(\Theta_Z(\alpha)_S(\zeta, g))(s) = (\alpha_S(\zeta)(s))(g(s)) = (f(\zeta(s)))(g(s)) = \Psi(\zeta(s), g(s)) = (\Phi_S(\zeta, g))(s).$$
  因此 $\Theta_Z(\alpha) = \Phi$，满射性得证。

---

#### 4. 相容性论证
1. **参数变换的相容性**：
   设 $w: Z' \to Z$ 为 Hausdorff 空间之间的连续映射。它诱导前复合自然变换 $h_w: h_{Z'} \to h_Z$。
   对任意 $\alpha \in \operatorname{Nat}(h_Z, h_{M(X,Y)})$，
   $$\Theta_{Z'}(\alpha \circ h_w) = \mathrm{ev} \circ ((\alpha \circ h_w) \times I_{h_X}) = \mathrm{ev} \circ (\alpha \times I_{h_X}) \circ (h_w \times I_{h_X}) = \Theta_Z(\alpha) \circ (h_w \times I_{h_X}).$$
   这表明同构 $\Theta_Z$ 在 $Z$ 上具有自然性。

2. **在 $X, Y$ 上的函子性相容性**：
   - 设 $f: X \to X'$ 连续。它诱导连续映射 $k(f): k(X) \to k(X')$，从而给出连续的预复合映射
     $$M(f, Y): M(X', Y) \longrightarrow M(X, Y), \qquad \varphi \longmapsto \varphi \circ k(f).$$
     由定义，$\mathrm{ev}_{M(X,Y)} \circ (h_{M(f, Y)} \times I_{h_X}) = \mathrm{ev}_{M(X', Y)} \circ (I_{h_{M(X', Y)}} \times h_f)$，与探针记录关于 $X$ 的反变函子性完全吻合。
   - 设 $g: Y \to Y'$ 连续。后复合定义连续映射
     $$M(X, g): M(X, Y) \longrightarrow M(X, Y'), \qquad \psi \longmapsto g \circ \psi.$$
     由定义，$\mathrm{ev}_{M(X, Y')} \circ (h_{M(X, g)} \times I_{h_X}) = h_g \circ \mathrm{ev}_{M(X,Y)}$，与探针记录关于 $Y$ 的协变函子性完全吻合。

---

### 五、 总结

| 项目 | 实现空间 $M(X,Y)$ 的数学刻画 |
| :--- | :--- |
| **底集** | $C(k(X), Y) = \operatorname{Nat}(h_X, h_Y)$（在 $X$ 的每个紧子集上均连续的映射全体；若 $X$ 为紧生成空间则为 $C(X,Y)$） |
| **拓扑** | 紧开拓扑 $\tau_{\mathrm{co}}$（准基为 $V(K, U) = \{f \mid f(K) \subseteq U\}$，$K \subseteq X$ 紧，$U \subseteq Y$ 开） |
| **分离性与基数** | Hausdorff 空间，底集属于宇宙 $\mathcal U$ |
| **求值自然变换** | $\mathrm{ev}_S(\sigma, g)(s) = (\sigma(s))(g(s))$ |
| **空间实现同构** | $C(S, M(X,Y)) \cong \mathcal H_{X,Y}(S) \quad (S \in \operatorname{Prof}_{\mathcal U})$ |
| **一般参数泛性质** | $\operatorname{Nat}(h_Z, h_{M(X,Y)}) \cong \operatorname{Nat}(h_Z \times h_X, h_Y) \quad (\forall Z \in \mathbf{Haus}_{\mathcal U})$ |
