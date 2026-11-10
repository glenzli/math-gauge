{}
# 群作用下降、稳定子与基底检验（版本 0.1.1）完整解答

---

## 预备引理（共同设定下的基本性质）

在进入各阶段之前，我们先确认共同设定下层范畴 $\mathcal{C} = \mathsf{Sh}(\mathsf{Prof}_{\mathcal{U}}, \mathsf{Set}_{\mathcal{V}})$ 的两个基本事实，后续阶段将直接援引：

1. **有限无交并的乘积性质与单满射覆盖归约**：
   在 $\mathsf{Prof}_{\mathcal{U}}$ 中，空空间 $\varnothing$ 以空族为覆盖，故任何层 $F \in \mathcal{C}$ 满足 $F(\varnothing) \cong \{*\}$（终对象）；对任意有限族 $U_1, \dots, U_n \in \mathsf{Prof}_{\mathcal{U}}$，自然嵌入族 $\{U_i \hookrightarrow \bigsqcup_{i=1}^n U_i\}_{i=1}^n$ 是覆盖且当 $i \neq j$ 时 $U_i \times_{\bigsqcup_k U_k} U_j = \varnothing$，故层条件给出自然双射 $F(\bigsqcup_{i=1}^n U_i) \xrightarrow{\sim} \prod_{i=1}^n F(U_i)$。因此，任何非空有限联合满射覆盖 $\{u_i: U_i \to U\}_{i=1}^n$（$n \ge 1$）关于 $F$ 的层粘合条件，等价于单一连续满射 $p = \bigsqcup_{i=1}^n u_i: V = \bigsqcup_{i=1}^n U_i \twoheadrightarrow U$ 的等化子条件：
   $$F(U) \xrightarrow{p^*} F(V) \underset{\mathrm{pr}_2^*}{\overset{\mathrm{pr}_1^*}{\rightrightarrows}} F(V \times_U V).$$
2. **可表示预层 $h_T$ 是层（拓扑是次典范的）**：
   对任意 $T \in \mathsf{Prof}_{\mathcal{U}}$，由于紧 Hausdorff 空间之间的连续满射 $p: V \twoheadrightarrow U$ 是闭映射从而是商映射，映射 $f: U \to T$ 连续当且仅当 $f \circ p: V \to T$ 连续且在 $V \times_U V$ 的两个投射下相等。结合有限无交并的泛性质，可知 $h_T(U) = \mathsf{Prof}_{\mathcal{U}}(U, T)$ 满足全部覆盖的层条件，即 $h_T \in \mathcal{C}$；由米田引理，对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$ 及 $Y \in \mathcal{C}$，有自然双射 $\mathcal{C}(h_U, Y) \cong Y(U)$。

---

## S1　有限群的自由作用

**附加条件**：$\Gamma$ 有限且在 $T \in \mathsf{Prof}_{\mathcal{U}}$ 上自由作用（仅在本阶段 S1 生效）。

### 1. Profinite 轨道空间 $T/\Gamma$ 的构造与性质验证

定义集合 $T/\Gamma := \{\Gamma t : t \in T\}$ 为 $\Gamma$ 在 $T$ 上的轨道集，赋予由商投射 $\pi_0: T \twoheadrightarrow T/\Gamma$（$t \mapsto \Gamma t$）诱导的商拓扑。我们逐项验证 $T/\Gamma \in \mathsf{Prof}_{\mathcal{U}}$（这一构造对任意有限群连续作用均成立）：

- **$\mathcal{U}$-小性**：因 $T \in \mathcal{U}$，商集 $T/\Gamma \subset \mathcal{P}(T)$ 属于 $\mathcal{U}$。
- **紧性**：$\pi_0: T \twoheadrightarrow T/\Gamma$ 是连续满射，$T$ 紧，故 $T/\Gamma$ 紧。
- **$\pi_0$ 是既开又闭的映射**：对任意子集 $A \subseteq T$，有 $\pi_0^{-1}(\pi_0(A)) = \bigcup_{\gamma \in \Gamma} \gamma \cdot A$。因为 $\Gamma$ 有限且每个 $\gamma \cdot - : T \to T$ 是同胚，当 $A$ 为开集（或闭集、既开又闭集）时，$\bigcup_{\gamma \in \Gamma} \gamma \cdot A$ 是有限个开集（或闭集、既开又闭集）的并，从而仍是开集（或闭集、既开又闭集）。由商拓扑定义，$\pi_0(A)$ 在 $T/\Gamma$ 中是开集（或闭集、既开又闭集）。
- **Hausdorff 性与全不连通性**：只需证明 $T/\Gamma$ 中任意两个不同点可被既开又闭（clopen）子集分离。设 $\bar{x} \neq \bar{y} \in T/\Gamma$，则它们的原像 $\Gamma x$ 与 $\Gamma y$ 是 $T$ 中不相交的有限闭子集。因 $T \in \mathsf{Prof}_{\mathcal{U}}$，对每个 $s \in \Gamma x$ 和 $t \in \Gamma y$，存在 $s$ 的 clopen 邻域 $W_{s,t} \subseteq T$ 使 $t \notin W_{s,t}$。令
  $$W := \bigcup_{s \in \Gamma x} \bigcap_{t \in \Gamma y} W_{s,t}, \qquad K := \bigcap_{\gamma \in \Gamma} \gamma \cdot W.$$
  由于 $\Gamma$ 有限，$W$ 和 $K$ 均为有限个 clopen 集的布尔组合，故 $K$ 是 $T$ 的 clopen 子集。又因 $\Gamma x$ 是 $\Gamma$-不变集且 $\Gamma x \subseteq W$，故 $\Gamma x \subseteq K \subseteq W$，从而 $K \cap \Gamma y = \varnothing$。因为 $K$ 是 $\Gamma$-不变的（$\gamma \cdot K = K$），有 $\pi_0^{-1}(\pi_0(K)) = K$，故 $\pi_0(K)$ 是 $T/\Gamma$ 的 clopen 子集，且 $\bar{x} \in \pi_0(K)$，$\bar{y} \notin \pi_0(K)$。这同时证明了 $T/\Gamma$ 是 Hausdorff 且全不连通的，故 $T/\Gamma \in \mathsf{Prof}_{\mathcal{U}}$。

**自由作用下的结构性质（核对角同胚与全局连续截面）**：
定义映射
$$\alpha: \Gamma \times T = \bigsqcup_{\gamma \in \Gamma} T \longrightarrow T \times_{T/\Gamma} T, \qquad (\gamma, t) \longmapsto (t, \gamma \cdot t).$$
- 因 $\pi_0(\gamma \cdot t) = \pi_0(t)$，$\alpha$ 良定义且连续。
- **满射性**：若 $(t_1, t_2) \in T \times_{T/\Gamma} T$，则 $\pi_0(t_1) = \pi_0(t_2)$，即 $t_2 \in \Gamma t_1$，故存在 $\gamma \in \Gamma$ 使 $t_2 = \gamma \cdot t_1$。
- **单射性**：若 $(t, \gamma \cdot t) = (t', \gamma' \cdot t')$，则 $t = t'$ 且 $\gamma \cdot t = \gamma' \cdot t$；由 $\Gamma$ 在 $T$ 上**自由作用**，得 $\gamma = \gamma'$。
- 因 $\Gamma$ 有限，$\Gamma \times T \in \mathsf{Prof}_{\mathcal{U}}$ 是紧空间，而 $T \times_{T/\Gamma} T \in \mathsf{Prof}_{\mathcal{U}}$ 是 Hausdorff 空间，故连续双射 $\alpha$ 是 $\mathsf{Prof}_{\mathcal{U}}$ 中的**同胚**。

（注：进一步地，因 $\Gamma$ 有限且自由作用，对每个 $t \in T$ 可取小 clopen 邻域 $V_t$ 使 $\{\gamma \cdot V_t\}_{\gamma \in \Gamma}$ 两两不交，其像 $\pi_0(V_t)$ 构成 $T/\Gamma$ 的 clopen 覆盖；利用紧性与 clopen 集布尔运算将其加细为有限 clopen 划分，还可直接拼出 $\pi_0: T \to T/\Gamma$ 的连续截面 $s_0: T/\Gamma \to T$ 及 $\Gamma$-等变同胚 $\Gamma \times (T/\Gamma) \xrightarrow{\sim} T$。）

### 2. 证明 $Q = h_{T/\Gamma}$ 是层商

令 $Q := h_{T/\Gamma}$，商态射为 $q := h_{\pi_0}: H = h_T \to Q$。我们要证明 $q: H \to Q$ 是 $H$ 模 $\Gamma$ 作用的层商（即余等化子 $\varinjlim_{B\Gamma} H$）：对任意 $Y \in \mathcal{C}$，由 $q$ 复合诱导的映射
$$q^*: \mathcal{C}(Q, Y) \longrightarrow \mathcal{C}(H, Y)^{\Gamma} = \{ f \in \mathcal{C}(H, Y) : f \circ h_\gamma = f, \ \forall \gamma \in \Gamma \}$$
是自然双射。

**证明**：
1. 对任意 $\gamma \in \Gamma$，因 $\pi_0 \circ (\gamma \cdot -) = \pi_0$，函子性给出 $q \circ h_\gamma = h_{\pi_0} \circ h_\gamma = h_{\pi_0} = q$，故 $q^*$ 的像落在 $\mathcal{C}(H, Y)^\Gamma$ 中。
2. 因 $\pi_0: T \twoheadrightarrow T/\Gamma$ 是 $\mathsf{Prof}_{\mathcal{U}}$ 中的连续满射，单元素族 $\{\pi_0: T \to T/\Gamma\}$ 是 $T/\Gamma$ 在 $\mathsf{Prof}_{\mathcal{U}}$ 中的覆盖。对任意层 $Y \in \mathcal{C}$，层粘合条件给出正合等化子序列：
   $$Y(T/\Gamma) \xrightarrow{\pi_0^*} Y(T) \underset{\mathrm{pr}_2^*}{\overset{\mathrm{pr}_1^*}{\rightrightarrows}} Y(T \times_{T/\Gamma} T).$$
3. 利用第 1 步证明的同胚 $\alpha: \bigsqcup_{\gamma \in \Gamma} T \xrightarrow{\sim} T \times_{T/\Gamma} T$ 以及预备引理中层将有限无交并变为有限积的性质，有同构
   $$\alpha^*: Y(T \times_{T/\Gamma} T) \xrightarrow{\sim} Y\left(\bigsqcup_{\gamma \in \Gamma} T\right) \xrightarrow{\sim} \prod_{\gamma \in \Gamma} Y(T).$$
   在 $\alpha$ 的第 $\gamma$ 个分量 $t \mapsto (t, \gamma \cdot t)$ 上，$\mathrm{pr}_1 \circ \alpha_\gamma = \mathrm{id}_T$，而 $\mathrm{pr}_2 \circ \alpha_\gamma = (\gamma \cdot -)$。因此，对 $y \in Y(T)$，有
   $$\mathrm{pr}_1^*(y) = \mathrm{pr}_2^*(y) \iff \forall \gamma \in \Gamma,\ \gamma^*(y) = y.$$
4. 结合米田引理的自然同构 $\mathcal{C}(h_{T/\Gamma}, Y) \cong Y(T/\Gamma)$ 与 $\mathcal{C}(h_T, Y) \cong Y(T)$（其中 $\pi_0^*$ 对应 $q^*$，$\gamma^*$ 对应 $- \circ h_\gamma$），上述等化子正合性直接给出自然双射 $\mathcal{C}(Q, Y) \xrightarrow{\sim} \mathcal{C}(H, Y)^\Gamma$。故 $Q = h_{T/\Gamma}$ 是层商。$\blacksquare$

### 3. 证明每个等变层 $E \to H$ 都在 $Q = h_{T/\Gamma}$ 上实现

设 $(E, \pi: E \to H, a)$ 是 $H$ 上的等变层。我们需要构造层 $p: D \to Q$ 及 $H$ 上的等变同构 $E \xrightarrow{\sim} H \times_Q D$。

**证明（利用自由作用下降构造 $D$）**：
1. **构造层 $D \to Q$**：
   对任意测试对象 $U \in \mathsf{Prof}_{\mathcal{U}}$ 及任意截面 $f \in Q(U) = \mathsf{Prof}_{\mathcal{U}}(U, T/\Gamma)$，纤维积 $P_f := T \times_{T/\Gamma, f} U \in \mathsf{Prof}_{\mathcal{U}}$ 带有第一坐标上的连续 $\Gamma$-作用 $\gamma \cdot (t, u) = (\gamma \cdot t, u)$ 以及第一投射 $\mathrm{pr}_1: P_f \to T$（视为 $H(P_f)$ 中的元素）。
   定义集合
   $$D(U) := \left\{ (f, \sigma) \;\middle|\; f \in Q(U),\ \sigma \in E(P_f),\ \pi_{P_f}(\sigma) = \mathrm{pr}_1,\ \text{且 } \forall \gamma \in \Gamma,\ E(\gamma \times \mathrm{id}_U)(\sigma) = a_{\gamma^{-1}, P_f}(\sigma) \right\}$$
   （注：由于反变性，$(\gamma \times \mathrm{id}_U)^*: E(P_f) \to E(P_f)$ 是右作用，故等变条件写为 $(\gamma \times \mathrm{id}_U)^*(\sigma) = a_{\gamma^{-1}}(\sigma)$，等价于对任意态射 $(x, u): W \to P_f$，拉回满足 $((\gamma \cdot x, u))^* \sigma = a_\gamma((x, u)^* \sigma)$）。
   对任意连续映射 $g: U' \to U$，拉回诱导映射 $\tilde{g} = \mathrm{id}_T \times_{T/\Gamma} g: P_{f \circ g} \to P_f$ 与 $\Gamma$-作用交换，故定义限制映射 $D(g)(f, \sigma) := (f \circ g, E(\tilde{g})(\sigma))$，并令投射 $p_U: D(U) \to Q(U)$ 为 $(f, \sigma) \mapsto f$。
2. **验证 $D \in \mathcal{C}$ 是层**：
   若 $\{u_i: U_i \to U\}_{i=1}^n$ 是 $\mathsf{Prof}_{\mathcal{U}}$ 中的有限联合满射覆盖，因 $\mathsf{Prof}_{\mathcal{U}}$ 中有限联合满射覆盖在纤维积下拉回仍为有限联合满射覆盖，故对任意 $f \in Q(U)$（由 $Q$ 的层性质唯一粘合自 $f_i \in Q(U_i)$），族 $\{\mathrm{id}_T \times u_i: P_{f_i} \to P_f\}_{i=1}^n$ 是 $P_f$ 的覆盖。由于 $E$ 是层且截面等变条件与投射条件 $\pi(\sigma) = \mathrm{pr}_1$ 均为局部可检验的等式条件，$E(P_f)$ 中满足条件的 $\sigma$ 唯一粘合自 $E(P_{f_i})$ 中相容的 $\sigma_i$。故 $D \in \mathcal{C}$。
3. **构造并验证等变同构 $\Psi: H \times_Q D \xrightarrow{\sim} E$**：
   对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$，$(H \times_Q D)(U) = H(U) \times_{Q(U)} D(U)$ 的元素形如 $(x, (f, \sigma))$，其中 $x: U \to T$ 满足 $f = \pi_0 \circ x: U \to T/\Gamma$。
   此时，$x$ 给出截面 $(x, \mathrm{id}_U): U \to P_f = T \times_{T/\Gamma, f} U$，$u \mapsto (x(u), u)$。定义映射
   $$\Psi_U: H(U) \times_{Q(U)} D(U) \longrightarrow E(U), \qquad (x, (f, \sigma)) \longmapsto E(x, \mathrm{id}_U)(\sigma).$$
   - **在 $H$ 上且 $\Gamma$-等变**：
     $$\pi_U(\Psi_U(x, (f, \sigma))) = H(x, \mathrm{id}_U)(\pi_{P_f}(\sigma)) = H(x, \mathrm{id}_U)(\mathrm{pr}_1) = \mathrm{pr}_1 \circ (x, \mathrm{id}_U) = x,$$
     且对任意 $\gamma \in \Gamma$，因为 $(\gamma \cdot x, \mathrm{id}_U) = (\gamma^{-1} \times \mathrm{id}_U)^{-1} \circ (x, \mathrm{id}_U) = (\gamma \times \mathrm{id}_U) \circ (x, \mathrm{id}_U)$，由 $\sigma$ 的等变定义有
     $$\Psi_U(h_\gamma(x), (f, \sigma)) = E(\gamma \cdot x, \mathrm{id}_U)(\sigma) = E(x, \mathrm{id}_U)(E(\gamma \times \mathrm{id}_U)(\sigma)) = E(x, \mathrm{id}_U)(a_{\gamma, P_f}(\sigma)) = a_{\gamma, U}(\Psi_U(x, (f, \sigma))).$$
   - **每个 $\Psi_U$ 是双射**：
     固定 $x \in H(U)$ 及 $f = \pi_0 \circ x$。由第 1 步同胚 $\alpha: \Gamma \times T \xrightarrow{\sim} T \times_{T/\Gamma} T$ 沿 $x: U \to T$ 拉回，映射
     $$\beta_x: \bigsqcup_{\gamma \in \Gamma} U = \Gamma \times U \xrightarrow{\sim} P_f = T \times_{T/\Gamma, f} U, \qquad (\gamma, u) \longmapsto (\gamma \cdot x(u), u)$$
     是 $\mathsf{Prof}_{\mathcal{U}}$ 中的 $\Gamma$-等变同胚！
     由预备引理，$\beta_x^*: E(P_f) \xrightarrow{\sim} \prod_{\gamma \in \Gamma} E(U)$ 是双射，其第 $\gamma$ 个分量为 $(\gamma \cdot x, \mathrm{id}_U)^* \sigma$。在 $\beta_x^*$ 下，条件“$\pi_{P_f}(\sigma) = \mathrm{pr}_1$ 且 $\forall \gamma \in \Gamma, (\gamma \times \mathrm{id}_U)^* \sigma = a_{\gamma^{-1}}(\sigma)$”等价于：第 $e$（单位元）分量 $e_0 := (x, \mathrm{id}_U)^* \sigma \in E(U)$ 满足 $\pi_U(e_0) = x$，且对一切 $\gamma \in \Gamma$，第 $\gamma$ 分量恰为 $a_{\gamma, U}(e_0)$！
     因此，给定任意 $e_0 \in E(U)$，记 $x = \pi_U(e_0)$，$f = \pi_0 \circ x$，由 $(\beta_x^*)^{-1}((a_{\gamma, U}(e_0))_{\gamma \in \Gamma}) \in E(P_f)$ 唯一确定了一个 $\sigma_{e_0} \in E(P_f)$ 使 $(f, \sigma_{e_0}) \in D(U)$，且 $e_0 \mapsto (\pi_U(e_0), (f, \sigma_{e_0}))$ 是 $\Psi_U$ 的双边逆映射。

故 $\Psi: H \times_Q D \xrightarrow{\sim} E$ 是 $H$ 上的等变同构，$E$ 在 $Q = h_{T/\Gamma}$ 上实现。$\blacksquare$

---

## S2　有限集合上的纤维分类

**附加条件**：$\Gamma$ 和 $T$ 均有限，$X$ 为有限 $\Gamma$-集合（赋予离散拓扑后均属于 $\mathsf{Prof}_{\mathcal{U}}$），$p_X: X \to T$ 为 $\Gamma$-等变映射。在每个 $T$-轨道 $O \in T/\Gamma$ 中选定代表元 $t \in O$，记代表元集为 $\mathcal{R} \subseteq T$，稳定子为 $\Gamma_t = \{\gamma \in \Gamma : \gamma \cdot t = t\} \le \Gamma$（仅在本阶段 S2 生效）。

### 1. 有限 $\Gamma$-集合 $X \to T$ 及其等变态射的分类

设 $\mathsf{FinSet}^{\Gamma}_{/T}$ 为 $T$ 上的有限 $\Gamma$-集合及 $T$ 上 $\Gamma$-等变映射构成的范畴；对每个 $t \in \mathcal{R}$，设 $\mathsf{FinSet}^{\Gamma_t}$ 为有限左 $\Gamma_t$-集合及 $\Gamma_t$-等变映射构成的范畴。

- **取纤维函子 $\Phi$**：
  对任意 $(X, p_X) \in \mathsf{FinSet}^{\Gamma}_{/T}$ 及 $t \in \mathcal{R}$，记纤维为 $X_t := p_X^{-1}(t) \subseteq X$。因 $p_X$ 是 $\Gamma$-等变的，对任意 $h \in \Gamma_t$ 及 $x \in X_t$，有 $p_X(h \cdot x) = h \cdot p_X(x) = h \cdot t = t$，故 $X_t$ 是 $\Gamma_t$-不变有限子集。对 $T$ 上的 $\Gamma$-等变映射 $f: X \to Y$，$f(X_t) \subseteq Y_t$ 且限制映射 $f_t := f|_{X_t}: X_t \to Y_t$ 是 $\Gamma_t$-等变的。这定义了函子
  $$\Phi: \mathsf{FinSet}^{\Gamma}_{/T} \longrightarrow \prod_{t \in \mathcal{R}} \mathsf{FinSet}^{\Gamma_t}, \qquad (X, p_X) \longmapsto (X_t)_{t \in \mathcal{R}}, \quad f \longmapsto (f|_{X_t})_{t \in \mathcal{R}}.$$

- **诱导重构函子 $\Psi$**：
  反之，给定一族有限 $\Gamma_t$-集合 $(F_t)_{t \in \mathcal{R}} \in \prod_{t \in \mathcal{R}} \mathsf{FinSet}^{\Gamma_t}$，对每个 $t \in \mathcal{R}$ 定义诱导有限 $\Gamma$-集合
  $$\Gamma \times^{\Gamma_t} F_t := (\Gamma \times F_t)/\sim, \qquad (\gamma h, z) \sim (\gamma, h \cdot z) \quad (\forall \gamma \in \Gamma,\ h \in \Gamma_t,\ z \in F_t),$$
  其左 $\Gamma$-作用为 $\gamma' \cdot [\gamma, z] := [\gamma' \gamma, z]$，到轨道 $\Gamma t \subseteq T$ 的投射为 $[\gamma, z] \mapsto \gamma \cdot t$（因 $(\gamma h) \cdot t = \gamma \cdot t$ 而良定义且 $\Gamma$-等变）。定义
  $$\Psi((F_t)_{t \in \mathcal{R}}) := \bigsqcup_{t \in \mathcal{R}} \Gamma \times^{\Gamma_t} F_t \longrightarrow \bigsqcup_{t \in \mathcal{R}} \Gamma t = T.$$
  对态射族 $(\varphi_t: F_t \to F'_t)_{t \in \mathcal{R}}$，定义 $\Psi((\varphi_t))$ 在第 $t$ 分量上为 $[\gamma, z] \mapsto [\gamma, \varphi_t(z)]$。

- **范畴等价的验证（分类定理）**：
  1. 对任意 $(F_t)_{t \in \mathcal{R}}$，$\Psi((F_t))$ 在 $t \in \mathcal{R}$ 处的纤维由满足 $\gamma \cdot t = t$（即 $\gamma \in \Gamma_t$）的类 $[\gamma, z] = [1, \gamma \cdot z] \in \Gamma \times^{\Gamma_t} F_t$ 组成。映射 $z \mapsto [1, z]$ 给出自然 $\Gamma_t$-同构 $F_t \xrightarrow{\sim} \Psi((F_t))_t$，故 $\Phi \circ \Psi \cong \mathrm{id}$。
  2. 对任意 $(X, p_X) \in \mathsf{FinSet}^{\Gamma}_{/T}$，定义映射
     $$\eta_X: \bigsqcup_{t \in \mathcal{R}} \Gamma \times^{\Gamma_t} X_t \longrightarrow X, \qquad [\gamma, x] \longmapsto \gamma \cdot x \quad (x \in X_t).$$
     因 $(\gamma h) \cdot x = \gamma \cdot (h \cdot x)$，$\eta_X$ 良定义，保持到 $T$ 的投射且 $\Gamma$-等变。
     - **满射性**：对任意 $y \in X$，其投射 $p_X(y) \in T$ 落在某个唯一代表元 $t \in \mathcal{R}$ 的轨道中，即存在 $\gamma \in \Gamma$ 使 $p_X(y) = \gamma \cdot t$；于是 $x := \gamma^{-1} \cdot y \in X_t$，且 $\eta_X([\gamma, x]) = y$。
     - **单射性**：若 $x_1 \in X_{t_1}, x_2 \in X_{t_2}$ 满足 $\gamma_1 \cdot x_1 = \gamma_2 \cdot x_2$，用 $p_X$ 作用得 $\gamma_1 \cdot t_1 = \gamma_2 \cdot t_2$，故 $t_1 = t_2 =: t$ 且 $h := \gamma_2^{-1} \gamma_1 \in \Gamma_t$，从而 $[\gamma_1, x_1] = [\gamma_2 h, x_1] = [\gamma_2, h \cdot x_1] = [\gamma_2, x_2]$。
     故 $\eta_X$ 是自然同构，即 $\Psi \circ \Phi \cong \mathrm{id}$。

  **结论**：
  - **对象的分类**：$T$ 上的有限 $\Gamma$-集合 $X \to T$ 的等变同构类与有限 $\Gamma_t$-集合同构类的元组 $([X_t])_{t \in \mathcal{R}}$ 一一对应，即 $X \cong \bigsqcup_{t \in \mathcal{R}} \Gamma \times^{\Gamma_t} X_t$（进一步地，每个有限 $\Gamma_t$-集合 $X_t$ 唯一分解为传递 $\Gamma_t$-轨道 $\bigsqcup_{j=1}^{m_t} \Gamma_t / K_{t,j}$，其中子群 $K_{t,j} \le \Gamma_t$ 由共轭类唯一确定）。
  - **态射的分类**：对任意 $X, Y \in \mathsf{FinSet}^{\Gamma}_{/T}$，限制映射诱导自然双射
    $$\mathrm{Hom}_{\mathsf{FinSet}^{\Gamma}_{/T}}(X, Y) \xrightarrow{\sim} \prod_{t \in \mathcal{R}} \mathrm{Hom}_{\Gamma_t}(X_t, Y_t), \qquad f \longmapsto (f|_{X_t})_{t \in \mathcal{R}},$$
    其逆映射将 $(\varphi_t)_{t \in \mathcal{R}}$ 映为满足 $f(\gamma \cdot x) = \gamma \cdot \varphi_t(x)$（$\forall t \in \mathcal{R}, x \in X_t, \gamma \in \Gamma$）的唯一等变映射 $f: X \to Y$。

### 2. $h_X$ 在 $Q = h_{T/\Gamma}$ 上实现的充要条件

**充要条件**：
$h_X$ 在 $Q = h_{T/\Gamma}$ 上可实现，**当且仅当**对每个代表元 $t \in \mathcal{R}$，稳定子群 $\Gamma_t$ 在纤维 $X_t = p_X^{-1}(t)$ 上的作用都是**平凡的**（即 $\forall t \in \mathcal{R}, \forall \gamma \in \Gamma_t, \forall x \in X_t, \ \gamma \cdot x = x$；等价地，对所有 $x \in X$，有 $\Gamma_{p_X(x)} \le \Gamma_x$）。

**证明**：
- **必要性（$\Longrightarrow$）**：
  设存在层 $p: D \to Q = h_{T/\Gamma}$ 及 $H = h_T$ 上的等变同构 $\alpha: h_X \xrightarrow{\sim} h_T \times_{h_{T/\Gamma}} D$。在单点空间 $* \in \mathsf{Prof}_{\mathcal{U}}$ 上取值，由 $h_X(*) \cong X$，$h_T(*) \cong T$，$h_{T/\Gamma}(*) \cong T/\Gamma$，$\alpha_*$ 给出 $T$ 上的 $\Gamma$-等变双射
  $$\alpha_*: X \xrightarrow{\sim} T \times_{T/\Gamma} D(*),$$
  其中 $\Gamma$ 在右端仅作用于第一坐标：$\gamma \cdot (s, d) = (\gamma \cdot s, d)$。
  对任意 $t \in \mathcal{R}$、$x \in X_t$ 及 $\gamma \in \Gamma_t$，设 $\alpha_*(x) = (t, d)$。则
  $$\alpha_*(\gamma \cdot x) = \gamma \cdot \alpha_*(x) = (\gamma \cdot t, d) = (t, d) = \alpha_*(x).$$
  因 $\alpha_*$ 是双射，得 $\gamma \cdot x = x$。故每个 $\Gamma_t$ 在 $X_t$ 上作用平凡。

- **充分性（$\Longleftarrow$）**：
  设对每个 $t \in \mathcal{R}$，$\Gamma_t$ 在 $X_t$ 上作用平凡。则对任意 $s = \gamma_0 \cdot t \in T$，稳定子 $\Gamma_s = \gamma_0 \Gamma_t \gamma_0^{-1}$ 在 $X_s = \gamma_0 \cdot X_t$ 上也作用平凡。
  取有限离散商空间 $X/\Gamma \in \mathsf{Prof}_{\mathcal{U}}$ 及由 $p_X$ 诱导的映射 $\bar{p}_X: X/\Gamma \to T/\Gamma$（$\Gamma x \mapsto \Gamma p_X(x)$）。考察典范映射
  $$\psi: X \longrightarrow T \times_{T/\Gamma} (X/\Gamma), \qquad x \longmapsto (p_X(x), \Gamma x),$$
  其中 $\Gamma$ 在右端按 $\gamma \cdot (s, \Gamma x) = (\gamma \cdot s, \Gamma x)$ 作用。显然 $\psi$ 保持到 $T$ 的投射且 $\Gamma$-等变。
  - **满射性**：任取 $(s, \Gamma x) \in T \times_{T/\Gamma} (X/\Gamma)$，则 $\Gamma s = \Gamma p_X(x)$，故存在 $\gamma \in \Gamma$ 使 $s = \gamma \cdot p_X(x) = p_X(\gamma \cdot x)$。取 $x' = \gamma \cdot x \in X$，则 $\psi(x') = (s, \Gamma x)$。
  - **单射性**：若 $\psi(x_1) = \psi(x_2)$，则 $p_X(x_1) = p_X(x_2) =: s$ 且 $\Gamma x_1 = \Gamma x_2$，即存在 $\gamma \in \Gamma$ 使 $x_2 = \gamma \cdot x_1$。两边取 $p_X$ 得 $s = p_X(\gamma \cdot x_1) = \gamma \cdot s$，故 $\gamma \in \Gamma_s$。因 $\Gamma_s$ 在 $X_s$ 上作用平凡且 $x_1 \in X_s$，得 $x_2 = \gamma \cdot x_1 = x_1$。
  故 $\psi$ 是有限离散空间之间的 $\Gamma$-等变同胚。由于米田嵌入 $h: \mathsf{Prof}_{\mathcal{U}} \hookrightarrow \mathcal{C}$ 保持纤维积，取 $D := h_{X/\Gamma} \xrightarrow{h_{\bar{p}_X}} h_{T/\Gamma} = Q$，即得 $H$ 上的等变同构
  $$h_\psi: h_X \xrightarrow{\sim} h_{T \times_{T/\Gamma} (X/\Gamma)} \cong h_T \times_{h_{T/\Gamma}} h_{X/\Gamma} = H \times_Q D.$$
  故 $h_X$ 在 $Q = h_{T/\Gamma}$ 上可实现。$\blacksquare$

### 3. 可实现对象的自同构群计算

设 $h_X$ 在 $Q = h_{T/\Gamma}$ 上可实现。由米田嵌入的忠实满性，$h_X$ 在等变对象范畴 $\mathcal{C}^{\Gamma}_{/H}$ 中的自同构群同构于 $X$ 在 $\mathsf{FinSet}^{\Gamma}_{/T}$ 中的自同构群：
$$\mathrm{Aut}_{\mathcal{C}^{\Gamma}_{/H}}(h_X) \cong \mathrm{Aut}_{\mathsf{FinSet}^{\Gamma}_{/T}}(X).$$
由第 1 步态射的分类定理，有群同构
$$\mathrm{Aut}_{\mathsf{FinSet}^{\Gamma}_{/T}}(X) \xrightarrow{\sim} \prod_{t \in \mathcal{R}} \mathrm{Aut}_{\Gamma_t}(X_t), \qquad f \longmapsto (f|_{X_t})_{t \in \mathcal{R}}.$$
由第 2 步的充要条件，当 $h_X$ 可实现时，每个 $\Gamma_t$ 在纤维 $X_t$ 上的作用都是平凡的，因此 $X_t$ 上的任意集合双射自动是 $\Gamma_t$-等变的，即 $\mathrm{Aut}_{\Gamma_t}(X_t) = \mathrm{Sym}(X_t)$（有限集 $X_t$ 上的全对称群）。故可实现对象的自同构群为
$$\mathrm{Aut}_{\mathcal{C}^{\Gamma}_{/H}}(h_X) \cong \prod_{t \in \mathcal{R}} \mathrm{Sym}(X_t) \cong \prod_{t \in \mathcal{R}} S_{|X_t|},$$
其阶数为 $\prod_{t \in \mathcal{R}} (|X_t|!)$（并且通过商投射下纤维双射 $X_t \xrightarrow{\sim} (X/\Gamma)_{\pi_0(t)}$，该群也典范同构于 $\mathrm{Aut}_{\mathcal{C}_{/Q}}(h_{X/\Gamma}) \cong \mathrm{Aut}_{\mathsf{FinSet}_{/(T/\Gamma)}}(X/\Gamma)$）。$\blacksquare$

---

## S3　一般层的完整下降

本阶段**只使用共同设定**：$\Gamma$ 为 $\mathcal{U}$-小离散群，作用于 $T \in \mathsf{Prof}_{\mathcal{U}}$，$H = h_T \in \mathcal{C}$。

### 1. 层商 $Q$ 及 $\Gamma$-不变态射 $q: H \to Q$ 的构造与泛性质

我们对任意带有 $\Gamma$-作用的层 $F \in \mathcal{C}$（特别地，取 $F = H$）给出统一且具体的层商 $F/\Gamma$ 构造：

- **第一步（分离商预层 $F_{\mathrm{sep}}$）**：
  对每个 $U \in \mathsf{Prof}_{\mathcal{U}}$，在集合 $F(U)$ 上定义关系 $\sim_U$：对 $x_1, x_2 \in F(U)$，称 $x_1 \sim_U x_2$，如果存在 $\mathsf{Prof}_{\mathcal{U}}$ 中的有限覆盖 $\{u_i: U_i \to U\}_{i=1}^n$ 以及群元素 $\gamma_1, \dots, \gamma_n \in \Gamma$，使得对每个 $i = 1, \dots, n$，在 $F(U_i)$ 中有
  $$x_2|_{U_i} = \gamma_i \cdot (x_1|_{U_i}).$$
  - **等价关系验证**：取恒等覆盖 $\{\mathrm{id}_U: U \to U\}$ 与 $\gamma_1 = 1$ 得自反性；由 $x_1|_{U_i} = \gamma_i^{-1} \cdot (x_2|_{U_i})$ 得对称性；若 $x_2|_{U_i} = \gamma_i \cdot (x_1|_{U_i})$（在覆盖 $\{U_i \to U\}$ 上）且 $x_3|_{V_j} = \delta_j \cdot (x_2|_{V_j})$（在覆盖 $\{V_j \to U\}$ 上），则在有限乘积覆盖 $\{U_i \times_U V_j \to U\}_{i,j}$ 上有 $x_3|_{U_i \times_U V_j} = (\delta_j \gamma_i) \cdot (x_1|_{U_i \times_U V_j})$，得传递性。
  - **预层与分离性验证**：沿任意连续映射 $f: V \to U$ 拉回有限覆盖仍为有限覆盖，故 $\sim_U$ 与限制映射相容，$U \mapsto F_{\mathrm{sep}}(U) := F(U)/\sim_U$ 构成预层，商投射 $q_{\mathrm{sep}}: F \twoheadrightarrow F_{\mathrm{sep}}$ 是 $\Gamma$-不变的。若 $[x_1], [x_2] \in F_{\mathrm{sep}}(U)$ 在某个有限覆盖 $\{V_j \to U\}_{j=1}^m$ 上相等，则对每个 $j$ 存在有限覆盖 $\{W_{j,k} \to V_j\}_{k=1}^{n_j}$ 使 $x_1, x_2$ 在 $W_{j,k}$ 上相差 $\gamma_{j,k} \in \Gamma$；因有限覆盖的复合 $\{W_{j,k} \to V_j \to U\}_{j,k}$ 仍是 $U$ 的有限覆盖，故 $x_1 \sim_U x_2$，即 $[x_1] = [x_2]$。这证明 $F_{\mathrm{sep}}$ 是**分离预层**（separated presheaf）。

- **第二步（层化得到 $F/\Gamma := F_{\mathrm{sep}}^+$）**：
  因为 $F_{\mathrm{sep}}$ 已是分离预层，只需应用一次 Grothendieck 加号构造（plus-construction）即得层 $F/\Gamma := F_{\mathrm{sep}}^+ \in \mathcal{C}$：对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$，
  $$(F/\Gamma)(U) := \varinjlim_{\{U_i \to U\} \in \mathrm{Cov}(U)} \left\{ ([x_i])_{i=1}^n \in \prod_{i=1}^n F_{\mathrm{sep}}(U_i) \;\middle|\; \forall i,j,\ [x_i]|_{U_i \times_U U_j} = [x_j]|_{U_i \times_U U_j} \text{ in } F_{\mathrm{sep}}(U_i \times_U U_j) \right\}$$
  （其中对覆盖指标集在 $\mathcal{U}$ 内的等价代表上取余极限，故 $(F/\Gamma)(U) \in \mathsf{Set}_{\mathcal{V}}$）。由分离预层层化的标准定理，$F/\Gamma \in \mathcal{C}$ 是层，且典范映射 $\iota: F_{\mathrm{sep}} \hookrightarrow F/\Gamma$ 在每个 $U$ 上均为**单射**。定义商态射为复合
  $$q_F := \iota \circ q_{\mathrm{sep}}: F \longrightarrow F/\Gamma.$$
  特别地，取 $F = H = h_T$，定义
  $$Q := H/\Gamma, \qquad q := q_H: H \longrightarrow Q.$$

- **验证核心性质**：
  1. **泛性质 $\mathrm{Hom}_{\mathcal{C}}(Q, Y) \cong \mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma$**：
     对任意层 $Y \in \mathcal{C}$，若 $f \in \mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma$（即 $\forall \gamma \in \Gamma, f \circ h_\gamma = f$），则对任意 $x_1 \sim_U x_2 \in H(U)$，存在有限覆盖 $\{U_i \to U\}$ 使 $x_2|_{U_i} = h_{\gamma_i}(x_1|_{U_i})$，故 $f_U(x_2)|_{U_i} = f_{U_i}(h_{\gamma_i}(x_1|_{U_i})) = f_{U_i}(x_1|_{U_i}) = f_U(x_1)|_{U_i}$；因 $Y$ 是层，得 $f_U(x_1) = f_U(x_2)$。因此 $f: H \to Y$ 唯一分解过分离商预层 $q_{\mathrm{sep}}: H \twoheadrightarrow H_{\mathrm{sep}}$；再由层化 $\iota: H_{\mathrm{sep}} \to H^+_{\mathrm{sep}} = Q$ 的泛性质，预层态射 $H_{\mathrm{sep}} \to Y$ 唯一延拓为层态射 $\bar{f}: Q \to Y$ 使 $\bar{f} \circ q = f$。这给出关于 $Y \in \mathcal{C}$ 自然的双射：
     $$q^*: \mathrm{Hom}_{\mathcal{C}}(Q, Y) \xrightarrow{\sim} \mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma.$$
  2. **局部满射性与核对角刻画**：
     由构造，$q_F: F \to F/\Gamma$ 是局部满射（每个 $s \in (F/\Gamma)(U)$ 由某个有限覆盖 $\{U_i \to U\}$ 上的 $[x_i] \in F_{\mathrm{sep}}(U_i)$ 代表，从而在 $U_i$ 上提升为 $x_i \in F(U_i)$）；且因 $\iota_U: F_{\mathrm{sep}}(U) \hookrightarrow (F/\Gamma)(U)$ 是单射，对任意 $x_1, x_2 \in F(U)$，
     $$q_{F, U}(x_1) = q_{F, U}(x_2) \iff x_1 \sim_U x_2 \iff \exists \text{ 有限覆盖 } \{U_i \to U\}_{i=1}^n \text{ 及 } \gamma_1, \dots, \gamma_n \in \Gamma,\ \text{使 } x_2|_{U_i} = \gamma_i \cdot (x_1|_{U_i}).$$

---

### 2. 不预选 $D$ 的可实现性充要判据

**定理（稳定子判据）**：
设 $(E, \pi, a)$ 是 $H$ 上的等变对象。则 $E$ 在 $Q$ 上可实现（即存在 $(D, p: D \to Q) \in \mathcal{C}_{/Q}$ 使 $E \cong H \times_Q D$ 为 $H$ 上的等变对象），**当且仅当** $(E, \pi, a)$ 满足如下不预选 $D$ 的内在条件：
> **（判据 $\mathrm{ Stab }$）** 对每个测试对象 $U \in \mathsf{Prof}_{\mathcal{U}}$，每个截面 $e \in E(U)$ 以及每个 $\gamma \in \Gamma$，
> $$h_{\gamma, U}(\pi_U(e)) = \pi_U(e) \implies a_{\gamma, U}(e) = e.$$
> （等价表述：对每个 $\gamma \in \Gamma$，记闭不动点子空间为 $T^\gamma := \{t \in T : \gamma \cdot t = t\} \in \mathsf{Prof}_{\mathcal{U}}$，其包含映射诱导等化子 $h_{T^\gamma} = \mathrm{Eq}(h_\gamma, \mathrm{id}_H) \hookrightarrow H$；则 $a_\gamma$ 在拉回层 $E \times_H h_{T^\gamma}$ 上的限制等于恒等态射。）

**证明**：
- **必要性（$\Longrightarrow$）**：
  设存在 $(D, p) \in \mathcal{C}_{/Q}$ 及等变同构 $\alpha: E \xrightarrow{\sim} H \times_Q D$。对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$、$e \in E(U)$ 及 $\gamma \in \Gamma$，设 $\alpha_U(e) = (x, d) \in H(U) \times_{Q(U)} D(U)$，则 $x = \pi_U(e)$。若 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$，即 $h_{\gamma, U}(x) = x$，则
  $$\alpha_U(a_{\gamma, U}(e)) = a^{\mathrm{can}}_{\gamma, U}(x, d) = (h_{\gamma, U}(x), d) = (x, d) = \alpha_U(e).$$
  因 $\alpha_U$ 是双射，得 $a_{\gamma, U}(e) = e$。

- **充分性（$\Longleftarrow$）**：
  设 $(E, \pi, a)$ 满足判据（$\mathrm{Stab}$）。我们对 $E$ 应用第 1 步的层商构造，取
  $$D := E/\Gamma \in \mathcal{C}, \qquad q_E: E \longrightarrow D.$$
  因 $q \circ \pi: E \to Q$ 满足 $q \circ \pi \circ a_\gamma = q \circ h_\gamma \circ \pi = q \circ \pi$（$\Gamma$-不变），由层商 $D = E/\Gamma$ 的泛性质，存在唯一态射 $p: D \to Q$ 使 $p \circ q_E = q \circ \pi$。
  由纤维积泛性质，$\pi: E \to H$ 与 $q_E: E \to D$ 诱导典范态射
  $$\Phi_E := (\pi, q_E): E \longrightarrow H \times_Q D.$$
  因 $\pi \circ a_\gamma = h_\gamma \circ \pi$ 且 $q_E \circ a_\gamma = q_E$，$\Phi_E$ 是 $H$ 上的 $\Gamma$-等变态射。我们证明对每个 $U \in \mathsf{Prof}_{\mathcal{U}}$，$\Phi_{E, U}: E(U) \to H(U) \times_{Q(U)} D(U)$ 是双射（由于 $E$ 和 $H \times_Q D$ 均为层，只需证明 $\Phi_E$ 是单态射且局部满射）：
  1. **单射性（$\Phi_E$ 是单态射）**：
     设 $e_1, e_2 \in E(U)$ 满足 $\Phi_{E, U}(e_1) = \Phi_{E, U}(e_2)$，即 $\pi_U(e_1) = \pi_U(e_2)$ 且 $q_{E, U}(e_1) = q_{E, U}(e_2)$。
     由第 1 步关于 $q_E: E \to E/\Gamma$ 核对角的刻画，存在有限覆盖 $\{u_i: U_i \to U\}_{i=1}^n$ 及 $\gamma_1, \dots, \gamma_n \in \Gamma$，使得对每个 $i$，在 $E(U_i)$ 中有
     $$e_2|_{U_i} = a_{\gamma_i, U_i}(e_1|_{U_i}).$$
     两边用 $\pi_{U_i}$ 作用，并利用 $\pi_U(e_1) = \pi_U(e_2)$，得
     $$\pi_{U_i}(e_1|_{U_i}) = \pi_{U_i}(e_2|_{U_i}) = \pi_{U_i}(a_{\gamma_i, U_i}(e_1|_{U_i})) = h_{\gamma_i, U_i}(\pi_{U_i}(e_1|_{U_i})).$$
     在测试对象 $U_i$ 上对截面 $e_1|_{U_i} \in E(U_i)$ 和 $\gamma_i \in \Gamma$ 应用判据（$\mathrm{Stab}$），立即推出
     $$a_{\gamma_i, U_i}(e_1|_{U_i}) = e_1|_{U_i}, \quad \text{从而 } e_2|_{U_i} = e_1|_{U_i} \quad (\forall i = 1, \dots, n).$$
     因 $E$ 是层且 $\{U_i \to U\}_{i=1}^n$ 是覆盖，故 $e_1 = e_2 \in E(U)$。
  2. **局部满射性（从而 $\Phi_E$ 是同构）**：
     任取 $(x, d) \in H(U) \times_{Q(U)} D(U)$，即 $q_U(x) = p_U(d) \in Q(U)$。因 $q_E: E \to D$ 局部满射，存在有限覆盖 $\{u_i: U_i \to U\}_{i=1}^n$ 及 $e_i \in E(U_i)$ 使 $q_{E, U_i}(e_i) = d|_{U_i}$。于是
     $$q_{U_i}(\pi_{U_i}(e_i)) = p_{U_i}(q_{E, U_i}(e_i)) = p_{U_i}(d|_{U_i}) = q_{U_i}(x|_{U_i}) \quad \text{in } Q(U_i).$$
     由第 1 步关于 $q: H \to Q$ 核对角的刻画，对每个 $i$，存在有限覆盖 $\{v_{i,j}: V_{i,j} \to U_i\}_{j=1}^{m_i}$ 及 $\gamma_{i,j} \in \Gamma$，使得
     $$x|_{V_{i,j}} = h_{\gamma_{i,j}, V_{i,j}}(\pi_{V_{i,j}}(e_i|_{V_{i,j}})).$$
     令 $e'_{i,j} := a_{\gamma_{i,j}, V_{i,j}}(e_i|_{V_{i,j}}) \in E(V_{i,j})$。则
     $$\pi_{V_{i,j}}(e'_{i,j}) = h_{\gamma_{i,j}, V_{i,j}}(\pi_{V_{i,j}}(e_i|_{V_{i,j}})) = x|_{V_{i,j}}, \qquad q_{E, V_{i,j}}(e'_{i,j}) = q_{E, V_{i,j}}(e_i|_{V_{i,j}}) = d|_{V_{i,j}},$$
     即 $\Phi_{E, V_{i,j}}(e'_{i,j}) = (x, d)|_{V_{i,j}}$。因复合族 $\{u_i \circ v_{i,j}: V_{i,j} \to U\}_{i,j}$ 是 $U$ 的有限覆盖，故 $\Phi_E$ 是局部满射。
  由单态射加局部满射即层同构，知 $\Phi_E: E \xrightarrow{\sim} H \times_Q (E/\Gamma)$ 是 $H$ 上的等变同构。$\blacksquare$

---

### 3. 所有实现及态射的分类

考察商函子与实现（拉回）函子：
$$Q_\Gamma = (-)/\Gamma : \mathcal{C}^{\Gamma}_{/H} \;\rightleftarrows\; \mathcal{C}_{/Q} : R = H \times_Q -,$$
其中对 $\psi: (D_1, p_1) \to (D_2, p_2) \in \mathcal{C}_{/Q}$，$R(\psi) := \mathrm{id}_H \times_Q \psi: H \times_Q D_1 \to H \times_Q D_2$。

1. **伴随关系 $Q_\Gamma \dashv R$**：
   对任意 $(E, \pi, a) \in \mathcal{C}^{\Gamma}_{/H}$ 和 $(D, p) \in \mathcal{C}_{/Q}$，$H$ 上的态射 $\varphi: E \to H \times_Q D$ 形如 $(\pi, f)$，其中 $f: E \to D$ 满足 $p \circ f = q \circ \pi$；$\varphi$ 是 $\Gamma$-等变的当且仅当 $f \circ a_\gamma = f$（$\forall \gamma \in \Gamma$）。由层商 $q_E: E \to E/\Gamma$ 的泛性质，这样的 $f$ 与 $\mathcal{C}_{/Q}$ 中的态射 $\bar{f}: E/\Gamma \to D$（满足 $\bar{f} \circ q_E = f$）一一对应。故有自然双射
   $$\mathrm{Hom}_{\mathcal{C}^{\Gamma}_{/H}}(E, H \times_Q D) \xrightarrow{\sim} \mathrm{Hom}_{\mathcal{C}_{/Q}}(E/\Gamma, D),$$
   其伴随单位元即第 2 步中的 $\Phi_E = (\pi, q_E): E \to H \times_Q (E/\Gamma)$。
2. **余单位元 $\varepsilon_D: (H \times_Q D)/\Gamma \xrightarrow{\sim} D$ 是同构（从而 $R = H \times_Q -$ 忠实满）**：
   对任意 $(D, p) \in \mathcal{C}_{/Q}$，第二投射 $\mathrm{pr}_2: H \times_Q D \to D$ 是 $\Gamma$-不变的，诱导 $\mathcal{C}_{/Q}$ 中的余单位元 $\varepsilon_D: (H \times_Q D)/\Gamma \to D$。
   - **单态射**：若 $(x_1, d_1), (x_2, d_2) \in (H \times_Q D)(U)$ 在 $\mathrm{pr}_2$ 下有相同像，则 $d_1 = d_2 =: d$ 且 $q_U(x_1) = p_U(d) = q_U(x_2)$。由 $q: H \to Q$ 的核对角性质，在某个有限覆盖 $\{U_i \to U\}$ 上有 $x_2|_{U_i} = h_{\gamma_i}(x_1|_{U_i})$，故 $(x_2, d)|_{U_i} = a^{\mathrm{can}}_{\gamma_i}((x_1, d)|_{U_i})$，从而在 $((H \times_Q D)/\Gamma)(U)$ 中相等。
   - **局部满射**：对任意 $d \in D(U)$，因 $q: H \to Q$ 局部满射，$p_U(d) \in Q(U)$ 在某个有限覆盖 $\{U_i \to U\}$ 上提升为 $x_i \in H(U_i)$，从而 $(x_i, d|_{U_i}) \in (H \times_Q D)(U_i)$ 在 $\mathrm{pr}_2$ 下映为 $d|_{U_i}$。
   故 $\varepsilon_D: (H \times_Q D)/\Gamma \xrightarrow{\sim} D$ 是 $\mathcal{C}_{/Q}$ 中的同构，这表明函子 $R = H \times_Q -$ 是**忠实满的**（fully faithful）。
3. **分类结论**：
   - **可实现对象子范畴的等价**：$R = H \times_Q -$ 与 $Q_\Gamma = (-)/\Gamma$ 给出范畴 $\mathcal{C}_{/Q}$ 与满足判据（$\mathrm{Stab}$）的满子范畴 $\mathcal{C}^{\Gamma, \mathrm{real}}_{/H} \subseteq \mathcal{C}^{\Gamma}_{/H}$ 之间的**互逆范畴等价**。
   - **态射的分类**：对任意实现对象 $H \times_Q D_1$ 与 $H \times_Q D_2$，$H$ 上的等变态射 $\varphi: H \times_Q D_1 \to H \times_Q D_2$ 与 $Q$ 上的层态射 $\psi: D_1 \to D_2$ 通过 $\psi \mapsto \mathrm{id}_H \times_Q \psi$（逆为取 $\Gamma$-层商 $\varphi/\Gamma$）一一对应：
     $$\mathrm{Hom}_{\mathcal{C}_{/Q}}(D_1, D_2) \xrightarrow{\sim} \mathrm{Hom}_{\mathcal{C}^{\Gamma}_{/H}}(H \times_Q D_1, H \times_Q D_2).$$
   - **给定可实现对象 $E$ 的所有实现的分类**：定义 $E$ 在 $Q$ 上的一个“实现”为二元组 $((D, p), \alpha)$，其中 $(D, p) \in \mathcal{C}_{/Q}$ 且 $\alpha: E \xrightarrow{\sim} H \times_Q D$ 是 $\mathcal{C}^{\Gamma}_{/H}$ 中的同构；两个实现 $((D, p), \alpha)$ 与 $((D', p'), \alpha')$ 之间的态射为满足 $(\mathrm{id}_H \times_Q \psi) \circ \alpha = \alpha'$ 的 $Q$ 上态射 $\psi: D \to D'$。
     由 $R = H \times_Q -$ 的忠实满性，对 $E$ 的任意两个实现 $((D, p), \alpha)$ 与 $((D', p'), \alpha')$，存在**唯一**的 $Q$ 上态射（且必为同构）$\psi: D \xrightarrow{\sim} D'$ 使 $(\mathrm{id}_H \times_Q \psi) \circ \alpha = \alpha'$（即 $\psi = \varepsilon_{D'} \circ ((\alpha' \circ \alpha^{-1})/\Gamma) \circ \varepsilon_D^{-1}$）。特别地，$E$ 的任何实现都唯一地典范同构于**典范实现** $((E/\Gamma, p_E), \Phi_E)$。

---

### 4. 任意基底 $g: B \to Q$ 上的相对分类及与基底拉回的相容性

设 $g: B \to Q$ 为 $\mathcal{C}$ 中任意层态射。令 $H_B := H \times_Q B$，配备第二投射 $q_B := \mathrm{pr}_2: H_B \to B$、第一投射 $g_H := \mathrm{pr}_1: H_B \to H$，以及在第一坐标上的诱导 $\Gamma$-作用 $h^B_\gamma := h_\gamma \times_Q \mathrm{id}_B$。

1. **$B$ 是 $H_B$ 的层商**：
   将第 3 步的余单位元同构 $\varepsilon_D: (H \times_Q D)/\Gamma \xrightarrow{\sim} D$ 应用于 $D = B$，立即得知 $q_B: H_B \to B$ 诱导同构 $H_B/\Gamma \xrightarrow{\sim} B$。特别是，$q_B: H_B \to B$ 是局部满射，且 $q_{B, U}(y_1) = q_{B, U}(y_2)$（$y_1, y_2 \in H_B(U)$）当且仅当存在有限覆盖 $\{U_i \to U\}$ 及 $\gamma_i \in \Gamma$ 使 $y_2|_{U_i} = h^B_{\gamma_i, U_i}(y_1|_{U_i})$。
2. **$B$ 上的相对可实现性判据与分类**：
   设 $\mathcal{C}^{\Gamma}_{/H_B}$ 为 $H_B$ 上的等变对象 $(E_B, \pi_B: E_B \to H_B, a^B)$ 的范畴。由于 $q_B: H_B \to B$ 具有与 $q: H \to Q$ 完全相同的局部满射性与核对角刻画，第 2、3 步的证明逐字适用于 $q_B: H_B \to B$：
   - **相对稳定子判据（$\mathrm{Stab}_B$）**：$(E_B, \pi_B, a^B)$ 在 $B$ 上可实现（即 $E_B \cong H_B \times_B D_B$），**当且仅当**对所有 $U \in \mathsf{Prof}_{\mathcal{U}}$、$e \in E_B(U)$ 及 $\gamma \in \Gamma$，
     $$h^B_{\gamma, U}(\pi_{B, U}(e)) = \pi_{B, U}(e) \implies a^B_{\gamma, U}(e) = e$$
     （注：因 $h^B_\gamma = h_\gamma \times_Q \mathrm{id}_B$ 在 $B$ 分量上平凡，条件 $h^B_{\gamma, U}(\pi_{B, U}(e)) = \pi_{B, U}(e)$ 等价于 $h_{\gamma, U}(g_{H, U}(\pi_{B, U}(e))) = g_{H, U}(\pi_{B, U}(e))$）。
   - **相对分类等价**：相对商函子 $Q_{\Gamma, B} = (-)/\Gamma: \mathcal{C}^{\Gamma}_{/H_B} \to \mathcal{C}_{/B}$ 左伴随于相对实现函子 $R_B = H_B \times_B -: \mathcal{C}_{/B} \to \mathcal{C}^{\Gamma}_{/H_B}$；余单位元 $\varepsilon_{B, D_B}: (H_B \times_B D_B)/\Gamma \xrightarrow{\sim} D_B$ 恒为同构（$R_B$ 忠实满）；单位元 $\Phi_{B, E_B} = (\pi_B, q_{E_B}): E_B \to H_B \times_B (E_B/\Gamma)$ 为同构当且仅当 $E_B$ 满足（$\mathrm{Stab}_B$）。因此 $R_B$ 给出 $\mathcal{C}_{/B}$ 与 $\mathcal{C}^{\Gamma, \mathrm{real}}_{/H_B}$ 的范畴等价。
3. **与基底拉回的相容性证明**：
   设 $u: B' \to B$ 为 $\mathcal{C}_{/Q}$ 中任意态射（特别地，取 $B = Q, u = g$ 即从 $Q$ 到 $B$ 的拉回）。记基底拉回函子为
   $$u^* = - \times_B B': \mathcal{C}_{/B} \longrightarrow \mathcal{C}_{/B'}, \qquad \tilde{u}^* = - \times_B B' \cong - \times_{H_B} H_{B'}: \mathcal{C}^{\Gamma}_{/H_B} \longrightarrow \mathcal{C}^{\Gamma}_{/H_{B'}}.$$
   我们验证三项相容性：
   - **（i）实现函子与拉回交换（$\tilde{u}^* \circ R_B \cong R_{B'} \circ u^*$）**：
     对任意 $(D_B \to B) \in \mathcal{C}_{/B}$，纤维积的结合律与抵消律给出 $H_{B'} \cong H_B \times_B B'$ 上的典范等变同构：
     $$\tilde{u}^*(R_B(D_B)) = (H_B \times_B D_B) \times_B B' \xrightarrow{\sim} (H_B \times_B B') \times_{B'} (D_B \times_B B') \cong R_{B'}(u^*(D_B)).$$
     特别地，若 $E_B$ 在 $B$ 上可实现，则其拉回 $E_B \times_B B'$ 必在 $B'$ 上可实现。
   - **（ii）商函子与拉回交换（$Q_{\Gamma, B'} \circ \tilde{u}^* \xrightarrow{\sim} u^* \circ Q_{\Gamma, B}$）**：
     对任意 $E_B \in \mathcal{C}^{\Gamma}_{/H_B}$，$\Gamma$-不变投射 $E_B \times_B B' \to E_B \xrightarrow{q_{E_B}} E_B/\Gamma$ 与 $E_B \times_B B' \to B'$ 诱导 $\mathcal{C}_{/B'}$ 中的典范态射
     $$\theta_{E_B, u}: (E_B \times_B B')/\Gamma \longrightarrow (E_B/\Gamma) \times_B B'.$$
     我们来证明 $\theta_{E_B, u}$ 是**同构**：
     - *单态射*：设 $(e_1, b'_1), (e_2, b'_2) \in (E_B \times_B B')(U)$ 在 $((E_B/\Gamma) \times_B B')(U)$ 中有相同像，则 $b'_1 = b'_2 =: b'$ 且 $q_{E_B, U}(e_1) = q_{E_B, U}(e_2)$。由核对角刻画，存在有限覆盖 $\{U_i \to U\}$ 及 $\gamma_i \in \Gamma$ 使 $e_2|_{U_i} = a^B_{\gamma_i}(e_1|_{U_i})$，故 $(e_2, b')|_{U_i} = (a^B_{\gamma_i}(e_1|_{U_i}), b'|_{U_i}) = a^{B'}_{\gamma_i}((e_1, b')|_{U_i})$，从而在 $((E_B \times_B B')/\Gamma)(U)$ 中相等。
     - *局部满射*：任取 $(\bar{e}, b') \in (E_B/\Gamma)(U) \times_{B(U)} B'(U)$。在某个有限覆盖 $\{U_i \to U\}$ 上 $\bar{e}|_{U_i}$ 提升为 $e_i \in E_B(U_i)$，且 $e_i$ 在 $B(U_i)$ 中的像等于 $\bar{e}|_{U_i}$ 在 $B(U_i)$ 中的像 $u_{U_i}(b'|_{U_i})$，故 $(e_i, b'|_{U_i}) \in (E_B \times_B B')(U_i)$ 是局部提升。
     因此 $\theta_{E_B, u}$ 是同构。
   - **（iii）典范实现态射与拉回交换**：
     在上述自然同构下，$E_B \times_B B'$ 的相对伴随单位元 $\Phi_{B', E_B \times_B B'}$ 在两个坐标上分别为 $\pi_B \times_B \mathrm{id}_{B'}$ 与 $q_{E_B \times_B B'}$，故恰与 $\Phi_{B, E_B} \times_B \mathrm{id}_{B'}: E_B \times_B B' \to (H_B \times_B (E_B/\Gamma)) \times_B B'$ 重合。$\blacksquare$

---

## S4　单点上的检验

### 1. 明确结论

**结论：不一定（否）。**
在共同设定下，仅假设对单点空间 $* \in \mathsf{Prof}_{\mathcal{U}}$ 上的每个截面 $e \in E(*)$ 及 $\gamma \in \Gamma$ 都有 $\gamma \pi(e) = \pi(e) \implies a_\gamma(e) = e$，**不能**推出一般等变层 $E$ 必在 $Q$ 上可实现。

### 2. 完整反例构造与核验

我们构造一个满足全部要求的显式反例，并逐项核验：

- **第一步：设定基底 $T$ 与群 $\Gamma$**
  - 取 $T := \{*\} \in \mathsf{Prof}_{\mathcal{U}}$ 为单点空间，从而 $H = h_*$ 是 $\mathcal{C}$ 的终对象（对所有 $U \in \mathsf{Prof}_{\mathcal{U}}$，$H(U) = \{*\}$）。
  - 取 $\Gamma := \mathbb{Z}/2\mathbb{Z} = \{1, \sigma\}$（其中 $\sigma^2 = 1$），在 $T = \{*\}$ 上平凡作用（$h_\sigma = \mathrm{id}_H$）。
  - 于是层商 $Q = H/\Gamma = h_*$ 也是终对象，$q = \mathrm{id}_{h_*}: H \to Q$。

- **第二步：构造辅助 profinite 空间 $X$ 与群作用**
  - 考察可数离散集 $\mathbb{N} \times \{0, 1\}$ 的单点紧化空间：
    $$X := (\mathbb{N} \times \{0, 1\}) \cup \{\infty\}.$$
    其拓扑规定为：每个点 $(n, \varepsilon) \in \mathbb{N} \times \{0, 1\}$ 是孤立点（clopen 单点集），无穷远点 $\infty$ 的基本开邻域族为
    $$V_N := \{\infty\} \cup \{(n, \varepsilon) : n \ge N,\ \varepsilon \in \{0, 1\}\} \qquad (N \in \mathbb{N}).$$
    因 $\mathbb{N} \in \mathcal{U}$，$X \in \mathcal{U}$。显然每个 $V_N$ 的补集是有限个孤立点，故 $V_N$ 既开又闭；任意两个不同点可由孤立单点集与某个 $V_N$ 分离，且任意开覆盖中含 $\infty$ 的开集包含某个 $V_N$（余下至多 $2N$ 个点）。因此 $X$ 是紧 Hausdorff 全不连通空间，即 $X \in \mathsf{Prof}_{\mathcal{U}}$。
  - 对每个 $n \in \mathbb{N}$，定义映射 $g_n: X \to X$ 为互换孤立点对 $(n, 0) \leftrightarrow (n, 1)$ 并固定其余所有点（包括 $\infty$）。因 $g_n$ 仅移动两个孤立点，故 $g_n$ 是 $X$ 的 2 阶自同胚，且不同的 $g_n, g_m$ 彼此交换。
  - 令 $G := \bigoplus_{n \in \mathbb{N}} \langle g_n \rangle \cong \bigoplus_{n \in \mathbb{N}} \mathbb{Z}/2\mathbb{Z}$ 为由 $\{g_n : n \in \mathbb{N}\}$ 生成的 $X$ 的自同胚群（$G \in \mathcal{U}$ 为可数离散群）。$G$ 中每个元素 $h$ 具有有限支集 $\mathrm{supp}(h) \subset \mathbb{N}$：当 $n \notin \mathrm{supp}(h)$ 时，$h(n, \varepsilon) = (n, \varepsilon)$。
  - 再定义映射 $\sigma: X \to X$ 为同时互换**所有** $n \in \mathbb{N}$ 的 $(n, 0) \leftrightarrow (n, 1)$ 并固定 $\infty$：
    $$\sigma(n, 0) = (n, 1), \qquad \sigma(n, 1) = (n, 0), \qquad \sigma(\infty) = \infty.$$
    对每个基本邻域 $V_N$ 有 $\sigma(V_N) = V_N$，故 $\sigma$ 是 $X$ 的 2 阶自同胚（$\sigma^2 = \mathrm{id}_X$）。因在每个二元集 $\{(n, 0), (n, 1)\}$ 上对称群 $S_2$ 交换，$\sigma$ 与 $G$ 中所有元素交换：$\forall h \in G, \ \sigma \circ h = h \circ \sigma$。

- **第三步：构造等变层 $(E, \pi, a)$**
  - 应用 S3 第 1 步的层商构造（S3 仅使用共同设定，条件在此完全适用），将离散群 $G$ 作用于 $h_X \in \mathcal{C}$，定义层
    $$E := h_X / G \in \mathcal{C}, \qquad q_G: h_X \longrightarrow E.$$
  - 令 $\pi: E \to H = h_*$ 为到终对象的唯一态射。
  - 因 $h_\sigma: h_X \to h_X$ 与 $G$ 的作用交换，复合 $q_G \circ h_\sigma: h_X \to E$ 是 $G$-不变的。由层商 $E = h_X / G$ 的泛性质，$h_\sigma$ 唯一诱导层自同构 $a_\sigma: E \to E$，满足 $a_\sigma \circ q_G = q_G \circ h_\sigma$ 且 $a_\sigma^2 = \mathrm{id}_E$。由于 $H = h_*$ 是终对象，自然有 $\pi \circ a_\sigma = \pi = h_\sigma \circ \pi$，故 $(E, \pi, a)$ 是 $H$ 上的 $\Gamma$-等变对象。

- **第四步：核验单点 $E(*)$ 上的条件成立**
  - 考察单点空间 $* \in \mathsf{Prof}_{\mathcal{U}}$。因为 $*$ 的任何有限覆盖 $\{u_i: U_i \to *\}_{i=1}^m$ 必有某个 $U_{i_0} \neq \varnothing$，取点 $p_0: * \to U_{i_0}$ 即有 $u_{i_0} \circ p_0 = \mathrm{id}_*$（即 $*$ 的任何覆盖都有整体截面）。因此，在层化 $E = (h_X / G)$ 中，每个 $e \in E(*)$ 都由某个点 $x \in h_X(*) = X$ 表示为 $e = q_{G, *}(x) = [x]$，且 $[x_1] = [x_2]$ 当且仅当存在 $h \in G$ 使 $x_2 = h(x_1)$，即 $E(*) = X/G$。
  - 对任意 $e = [x] \in E(*)$：
    - 若 $x = (n, \varepsilon) \in \mathbb{N} \times \{0, 1\}$，则 $\sigma(n, \varepsilon) = (n, 1 - \varepsilon) = g_n(n, \varepsilon)$，其中 $g_n \in G$；故在 $E(*) = X/G$ 中有
      $$a_{\sigma, *}([x]) = [\sigma(x)] = [g_n(x)] = [x].$$
    - 若 $x = \infty$，则 $\sigma(\infty) = \infty = 1_G(\infty)$，故也有 $a_{\sigma, *}([\infty]) = [\infty]$。
  - 综上，对**所有** $e \in E(*)$ 及 $\gamma \in \Gamma = \{1, \sigma\}$，恒有 $a_{\gamma, *}(e) = e$，单点检验条件完全满足！

- **第五步：核验 $E$ 在 $Q = h_*$ 上不可实现**
  - 取测试对象 $U := X \in \mathsf{Prof}_{\mathcal{U}}$ 及截面 $e_0 := q_{G, X}(\mathrm{id}_X) = [\mathrm{id}_X] \in E(X)$。
  - 在 $H(X) = \{*\}$ 中显然有 $h_{\sigma, X}(\pi_X(e_0)) = * = \pi_X(e_0)$。
  - 根据 S3 的可实现性充要判据（$\mathrm{Stab}$），若 $E$ 在 $Q$ 上可实现，则必有 $a_{\sigma, X}(e_0) = e_0$，即在 $E(X) = (h_X / G)(X)$ 中必有
    $$q_{G, X}(\sigma) = a_{\sigma, X}(q_{G, X}(\mathrm{id}_X)) = q_{G, X}(\mathrm{id}_X).$$
  - 然而，由 S3 第 1 步关于层商 $q_G: h_X \to h_X / G$ 核对角的刻画，$q_{G, X}(\sigma) = q_{G, X}(\mathrm{id}_X)$ 当且仅当存在有限覆盖 $\{u_i: U_i \to X\}_{i=1}^k$ 以及有限个群元素 $h_1, \dots, h_k \in G$，使得对每个 $i = 1, \dots, k$，有 $\sigma \circ u_i = h_i \circ \mathrm{id}_X \circ u_i = h_i \circ u_i$。
  - 假设存在这样的有限覆盖与 $h_1, \dots, h_k \in G$。因 $\bigcup_{i=1}^k u_i(U_i) = X$，这要求对每个点 $x \in X$，都存在某个 $i \in \{1, \dots, k\}$ 使 $\sigma(x) = h_i(x)$。但每个 $h_i \in G = \bigoplus_{n \in \mathbb{N}} \langle g_n \rangle$ 的支集 $\mathrm{supp}(h_i) \subset \mathbb{N}$ 是有限集，故并集 $F := \bigcup_{i=1}^k \mathrm{supp}(h_i)$ 仍是 $\mathbb{N}$ 的有限子集。取 $n_0 \in \mathbb{N} \setminus F$ 并考察点 $x_0 := (n_0, 0) \in X$，则对所有 $i = 1, \dots, k$ 都有 $h_i(x_0) = (n_0, 0)$，而 $\sigma(x_0) = (n_0, 1) \neq (n_0, 0)$，矛盾！
  - 因此 $a_{\sigma, X}(e_0) \neq e_0$，违反 S3 的稳定子充要判据，故 $E$ **不在** $Q$ 上可实现。$\blacksquare$

*（注：若附加假设 $E = h_X$ 是可表示层，则对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$，映射 $E(U) = \mathsf{Prof}_{\mathcal{U}}(U, X) \to \prod_{u \in U} E(*)$ 是单射，此时单点 $E(*)$ 上的稳定子条件确实能推出 S3 的全局判据。上述反例之所以成立，正是因为一般层 $E \in \mathcal{C}$ 的截面不一定由单点集 $*$ 上的拉回唯一决定，即 $*$ 不是凝聚拓扑 $\mathsf{Prof}_{\mathcal{U}}$ 的生成元。）*

---

## S5　局部满射的基底检验

### 1. 明确结论

**结论：是（$E$ 必可在 $Q$ 上实现）。**

### 2. 证明

设 $g: B \to Q$ 是局部满射，且拉回对象 $E_B := E \times_Q B$ 作为 $H_B := H \times_Q B$ 上的等变对象（投射 $\pi_B = \pi \times_Q \mathrm{id}_B$，群作用 $a^B_\gamma = a_\gamma \times_Q \mathrm{id}_B$）可在 $B$ 上实现。由于本阶段在共同设定下工作，S3 的全部结果均适用。我们给出两种直接证明：

#### 证法一（通过 S3 的稳定子判据与局部提升）
1. 由 S3 第 2 步的定理，要证 $E$ 在 $Q$ 上可实现，只需验证 $E$ 满足判据（$\mathrm{Stab}$）：对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$，任意 $e \in E(U)$ 及 $\gamma \in \Gamma$，若 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$，则 $a_{\gamma, U}(e) = e$。
2. 任取满足 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$ 的 $U \in \mathsf{Prof}_{\mathcal{U}}$、$e \in E(U)$ 及 $\gamma \in \Gamma$。考察截面
   $$s := q_U(\pi_U(e)) \in Q(U).$$
3. 因为 $g: B \to Q$ 是局部满射，存在 $\mathsf{Prof}_{\mathcal{U}}$ 中的有限覆盖 $\{u_i: U_i \to U\}_{i=1}^n$ 以及截面 $b_i \in B(U_i)$（$i = 1, \dots, n$），使得
   $$g_{U_i}(b_i) = s|_{U_i} = q_{U_i}(\pi_{U_i}(e|_{U_i})) \quad \text{in } Q(U_i).$$
4. 于是对每个 $i = 1, \dots, n$，二元组
   $$\tilde{e}_i := (e|_{U_i}, b_i) \in E(U_i) \times_{Q(U_i)} B(U_i) = E_B(U_i)$$
   是 $E_B$ 在 $U_i$ 上的良定义截面，其到 $H_B(U_i) = H(U_i) \times_{Q(U_i)} B(U_i)$ 的投射为 $\pi_{B, U_i}(\tilde{e}_i) = (\pi_{U_i}(e|_{U_i}), b_i)$。
5. 由 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$ 限制到 $U_i$ 上，得 $h_{\gamma, U_i}(\pi_{U_i}(e|_{U_i})) = \pi_{U_i}(e|_{U_i})$，故
   $$h^B_{\gamma, U_i}(\pi_{B, U_i}(\tilde{e}_i)) = (h_{\gamma, U_i}(\pi_{U_i}(e|_{U_i})), b_i) = (\pi_{U_i}(e|_{U_i}), b_i) = \pi_{B, U_i}(\tilde{e}_i).$$
6. 因为 $E_B$ 在 $B$ 上可实现，应用 S3 第 4 步的相对稳定子判据（$\mathrm{Stab}_B$）之必要性，得在 $E_B(U_i)$ 中有
   $$(a_{\gamma, U_i}(e|_{U_i}), b_i) = a^B_{\gamma, U_i}(\tilde{e}_i) = \tilde{e}_i = (e|_{U_i}, b_i).$$
   比较第一坐标，得对每个 $i = 1, \dots, n$，在 $E(U_i)$ 中有
   $$(a_{\gamma, U}(e))|_{U_i} = a_{\gamma, U_i}(e|_{U_i}) = e|_{U_i}.$$
7. 因 $E$ 是层且 $\{u_i: U_i \to U\}_{i=1}^n$ 是 $U$ 的覆盖，由层的分离性公理得 $a_{\gamma, U}(e) = e \in E(U)$。故 $E$ 满足（$\mathrm{Stab}$），从而必可在 $Q$ 上实现。$\blacksquare$

#### 证法二（通过 S3 典范实现态射的基底拉回相容性）
由 S3 第 3、4 步，$E$ 在 $Q$ 上可实现当且仅当典范态射 $\Phi_E: E \to H \times_Q (E/\Gamma)$ 是层同构；而在沿 $g: B \to Q$ 拉回下，借助典范同构 $(E \times_Q B)/\Gamma \xrightarrow{\sim} (E/\Gamma) \times_Q B$，$\Phi_E \times_Q \mathrm{id}_B$ 与 $E_B$ 在 $B$ 上的典范实现态射 $\Phi_{B, E_B}: E_B \to H_B \times_B (E_B/\Gamma)$ 同构。因 $E_B$ 在 $B$ 上可实现，$\Phi_{B, E_B}$ 是同构，故 $\Phi_E \times_Q \mathrm{id}_B$ 是同构。由于 $g: B \to Q$ 是局部满射，利用局部提升在有限覆盖上检验可知 $\Phi_E$ 本身也是单态射且局部满射，故 $\Phi_E$ 是同构，$E$ 在 $Q$ 上实现。$\blacksquare$

---

## S6　非空基底与全局结论

### 1. 判断结论

**结论：不一定（否）。**
仅假设 $B$ 是非空可表示层且有态射 $g: B \to Q$（不假设局部满射），拉回 $E \times_Q B$ 在 $B$ 上可实现**不一定**反映原对象 $E$ 在 $Q$ 上可实现。

### 2. 完整反例构造与核验

我们构造一个有限离散空间上的显式反例（此时 S2 与 S3 的条件均适用）：

- **群 $\Gamma$ 与空间 $T$**：
  - 取有限群 $\Gamma := \mathbb{Z}/2\mathbb{Z} = \{1, \sigma\}$（$\sigma^2 = 1$）。
  - 取二元离散空间 $T := \{t_1, t_2\} \in \mathsf{Prof}_{\mathcal{U}}$，赋予**平凡** $\Gamma$-作用：$\sigma \cdot t_1 = t_1$，$\sigma \cdot t_2 = t_2$。
  - 于是 $H = h_T$ 上的作用为 $h_\sigma = \mathrm{id}_H$，商空间 $T/\Gamma = \{t_1, t_2\} = T$（$\pi_0 = \mathrm{id}_T$），且由 S3 第 1 步（或直接由 $\mathrm{Hom}(H, Y)^\Gamma = \mathrm{Hom}(H, Y)$），层商为 $Q = H/\Gamma = h_T$，商态射为 $q = \mathrm{id}_{h_T}: H \to Q$。

- **等变对象 $E = h_X \to H$**：
  - 取三元离散空间 $X := \{x_1, x_2^+, x_2^-\} \in \mathsf{Prof}_{\mathcal{U}}$，定义投射 $p_X: X \to T$ 与 $\Gamma$-作用为：
    $$p_X(x_1) = t_1, \quad p_X(x_2^+) = p_X(x_2^-) = t_2; \qquad \sigma \cdot x_1 = x_1, \quad \sigma \cdot x_2^+ = x_2^-, \quad \sigma \cdot x_2^- = x_2^+.$$
    显然 $p_X(\sigma \cdot x) = p_X(x) = \sigma \cdot p_X(x)$，故 $p_X$ 是 $\Gamma$-等变连续映射。
  - 令 $E := h_X \in \mathcal{C}$，$\pi := h_{p_X}: E \to H$，$a_\sigma := h_\sigma: E \to E$。

- **非空可表示基底 $B \to Q$**：
  - 取非空单点空间 $U_0 := \{t_1\} \in \mathsf{Prof}_{\mathcal{U}}$，则 $B := h_{\{t_1\}}$ 是非空可表示层。
  - 取包含映射 $i: \{t_1\} \hookrightarrow \{t_1, t_2\} = T$ 诱导的态射 $g := h_i: B = h_{\{t_1\}} \to Q = h_T$。

- **核验 $E \times_Q B$ 在 $B$ 上可实现，而 $E$ 在 $Q$ 上不可实现**：
  1. **拉回 $E \times_Q B$ 在 $B$ 上可实现**：
     因米田嵌入保持纤维积，有
     $$H_B = H \times_Q B = h_T \times_{h_T} h_{\{t_1\}} \cong h_{\{t_1\}} = B,$$
     $$E_B = E \times_Q B = h_X \times_{h_T} h_{\{t_1\}} \cong h_{p_X^{-1}(t_1)} = h_{\{x_1\}}.$$
     因为 $\sigma \cdot x_1 = x_1$，$\Gamma$ 在 $\{x_1\}$ 上作用平凡，单点集双射 $\{x_1\} \xrightarrow{\sim} \{t_1\}$ 给出 $H_B$ 上的等变同构 $E_B \cong H_B \times_B B$（取 $D_B = B \xrightarrow{\mathrm{id}_B} B$）。故 $E \times_Q B$ 在 $B$ 上**可实现**。
  2. **原对象 $E$ 在 $Q$ 上不可实现**：
     在点 $t_2 \in T$ 处，稳定子为 $\Gamma_{t_2} = \Gamma = \{1, \sigma\}$，而它在纤维 $X_{t_2} = \{x_2^+, x_2^-\}$ 上的作用非平凡（$\sigma \cdot x_2^+ = x_2^- \neq x_2^+$）。由 S2 第 2 步的充要条件（或由 S3 的判据（$\mathrm{Stab}$）应用于 $e = x_2^+ \in E(*) = X$），$E = h_X$ 在 $Q = h_T$ 上**不可实现**。$\blacksquare$

---

### 3. 综合 S1–S6 整理的可实现性检验原则

结合 S1 至 S6 的全部结论，对等变层 $(E, \pi: E \to H, a)$ 是否在层商 $Q = H/\Gamma$ 上可实现，我们整理出以下五条层次分明的检验原则：

| 原则编号 | 检验维度 | 适用前提条件 | 检验方法与结论 | 依据阶段 |
| :--- | :--- | :--- | :--- | :--- |
| **原则 I** | **全局截面稳定子准则（通用充要判据）** | 仅需共同设定（任意 $\Gamma, T, E$） | $E$ 在 $Q$ 上可实现 $\iff \forall U \in \mathsf{Prof}_{\mathcal{U}}, \forall e \in E(U), \forall \gamma \in \Gamma$，有 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e) \Rightarrow a_{\gamma, U}(e) = e$；等价于对每个 $\gamma \in \Gamma$，$a_\gamma$ 在闭不动点集拉回 $E \times_H h_{T^\gamma}$ 上为恒等；也等价于典范态射 $\Phi_E: E \to H \times_Q (E/\Gamma)$ 是同构。 | **S3** |
| **原则 II** | **自由作用无条件下降原则** | $\Gamma$ 在 $T$ 上自由作用（如 S1 中 $\Gamma$ 有限且自由；一般地只要 $\forall \gamma \neq 1, T^\gamma = \varnothing$） | 对所有 $\gamma \neq 1$，闭不动点子空间 $T^\gamma = \varnothing$（故 $h_{\gamma, U}(x) = x$ 仅在 $U = \varnothing$ 时发生，而 $E(\varnothing) = \{*\}$）。因此**任何**等变层 $E \to H$ 均自动满足原则 I 而在 $Q$ 上实现；当 $\Gamma$ 有限时还有 $Q \cong h_{T/\Gamma}$。 | **S1, S3** |
| **原则 III** | **单点/轨道纤维稳定子检验原则** | $E = h_X$ 可表示（如 S2 有限情形，或一般 profinite $\Gamma$-空间 $X \to T$），或更一般地 $E$ 是点分离层（即 $E(U) \hookrightarrow \prod_{u \in U} E(*)$ 单射） | 此时单点检验从“仅必要”升级为**充要**：只需对每个 $T$-轨道选定一个代表元 $t \in \mathcal{R}$，检验稳定子 $\Gamma_t$ 在单点纤维 $E(*)_t$ 上的作用是否平凡。而对**非点分离的一般层 $E$**，单点 $E(*)$ 检验**仅必要不充分**，不可单独作为充分判据。 | **S2, S4** |
| **原则 IV** | **局部满射基底换底检验原则（忠实平坦下降）** | 基底态射 $g: B \to Q$ 是**局部满射**（或有一族基底 $\{g_i: B_i \to Q\}$ 联合局部满射） | 可实现性关于局部满射基底拉回具有**完全反射性**：$E$ 在 $Q$ 上可实现 $\iff E \times_Q B$ 在 $B$ 上可实现。特别地，因为商投射 $q: H = h_T \to Q$ 本身恒为局部满射且 $H$ 可表示，总可以将 $Q$ 上的可实现性归约为可表示基底 $B = H$ 上 $E \times_Q H \to H \times_Q H$ 的可实现性检验。 | **S3, S5** |
| **原则 V** | **非满射基底的单向阻碍原则** | 任意基底态射 $g: B \to Q$（如非空可表示层 $B = h_{U_0} \to Q$，但不要求局部满射） | 由基底拉回相容性，$E$ 可实现 $\Rightarrow E \times_Q B$ 可实现。因此，若在某个测试基底 $B \to Q$ 上 $E \times_Q B$ **不可实现**，则可立即否决 $E$ 的可实现性（单向否决检验）；但若 $g: B \to Q$ 不是局部满射，则 $E \times_Q B$ 可实现**不能**保证 $E$ 全局可实现，必须在覆盖全部轨道的局部满射族上完成检验。 | **S3, S6** |
