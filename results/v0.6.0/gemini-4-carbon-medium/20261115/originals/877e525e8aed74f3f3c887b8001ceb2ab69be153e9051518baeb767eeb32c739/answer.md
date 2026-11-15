## 预备约定与共同性质

在共同设定下，固定 Grothendieck 宇宙 $\mathcal{U} \in \mathcal{V}$ 且 $\mathbb{N} \in \mathcal{U}$。为明确记号并供各阶段援引，先记录以下基本事实：

1. **景与可表示层**：$\mathsf{Prof}_{\mathcal{U}}$ 的对象是 $\mathcal{U}$-小紧 Hausdorff 全不连通空间，态射为连续映射；对 $U \in \mathsf{Prof}_{\mathcal{U}}$，覆盖族是有限指标集 $I$ 上的连续映射族 $\{u_i : U_i \to U\}_{i \in I}$，满足 $\bigcup_{i \in I} u_i(U_i) = U$（当 $U = \varnothing$ 时允许 $I = \varnothing$ 的空覆盖）。
   - 对任意层 $F \in \mathcal{C}$：在 $\varnothing$ 的空覆盖上，等化子条件给出 $F(\varnothing) \cong \{*\}$（单点终对象）；在有限不交并 $U_1 \sqcup U_2$ 的标准二元覆盖上，因 $U_1 \times_{U_1 \sqcup U_2} U_2 = \varnothing$ 且 $F(\varnothing) \cong \{*\}$，得 $F(U_1 \sqcup U_2) \xrightarrow{\sim} F(U_1) \times F(U_2)$。反之，预层 $F$ 属于 $\mathcal{C}$ 当且仅当 $F(\varnothing) \cong \{*\}$、$F$ 保有限不交并为积，且对每个连续满射 $p : U' \twoheadrightarrow U$，$F(U) \to F(U') \rightrightarrows F(U' \times_U U')$ 为等化子（非空有限覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 等价于单满射 $\bigsqcup_{i \in I} U_i \twoheadrightarrow U$）。
   - 对任意 $X \in \mathsf{Prof}_{\mathcal{U}}$，记 $h_X(U) = C(U, X)$ 为连续映射集（因 $U, X$ 均 $\mathcal{U}$-小且 $\mathcal{U} \in \mathcal{V}$，有 $C(U, X)$ 同构于 $\mathcal{U}$ 中元素，故自然属于 $\mathsf{Set}_{\mathcal{V}}$）。由于紧空间到 Hausdorff 空间的连续满射必为闭映射从而是商映射，连续性可沿满射下降，故 $h_X \in \mathcal{C}$（景是次典范的）。由米田引理，函子 $h_{(-)} : \mathsf{Prof}_{\mathcal{U}} \to \mathcal{C}$ 忠实满，保所有在 $\mathsf{Prof}_{\mathcal{U}}$ 中存在的极限（特别是纤维积，因为紧 Hausdorff 全不连通空间的闭子空间与有限积仍紧 Hausdorff 全不连通），且保有限余积（对任意 $Y \in \mathcal{C}$，$\mathrm{Hom}_{\mathcal{C}}(h_{X_1 \sqcup X_2}, Y) \cong Y(X_1 \sqcup X_2) \cong Y(X_1) \times Y(X_2) \cong \mathrm{Hom}_{\mathcal{C}}(h_{X_1}, Y) \times \mathrm{Hom}_{\mathcal{C}}(h_{X_2}, Y)$）。

2. **全不连通紧空间的既开又闭基（Šura-Bura 引理）**：任意 $X \in \mathsf{Prof}_{\mathcal{U}}$ 以既开又闭（clopen）子集为拓扑基。
   *验证*：对 $x \in X$，令 $K_x$ 为包含 $x$ 的全体 clopen 子集之交（闭集，故紧）。若 $K_x = A \sqcup B$ 为两个不交闭子集之并且 $x \in A$，因紧 Hausdorff 空间正规，存在 $X$ 中不交开集 $U \supseteq A, V \supseteq B$。闭集 $X \setminus (U \cup V)$ 与 $K_x$ 不交；由紧性及包含 $x$ 的 clopen 集对有限交封闭，存在 clopen 集 $W \ni x$ 使 $W \subseteq U \cup V$。此时 $W \cap U = W \setminus V$ 在 $X$ 中既开又闭且含 $x$，故 $K_x \subseteq W \cap U \subseteq U$，从而 $B = K_x \cap B = \varnothing$。因此 $K_x$ 连通；由全不连通性得 $K_x = \{x\}$。于是若 $y \neq x$，必存在 clopen 集含 $x$ 而不含 $y$；再用紧性即知 clopen 集构成 $X$ 的拓扑基。

3. **群作用与等变范畴**：$\mathcal{U}$-小离散群 $\Gamma$ 连续左作用于 $T \in \mathsf{Prof}_{\mathcal{U}}$ 等价于群同态 $\Gamma \to \mathrm{Aut}_{\mathsf{Prof}_{\mathcal{U}}}(T)$，$\gamma \mapsto (\gamma \cdot -)$。记 $H = h_T$，$h_\gamma : H \to H$ 为左复合 $x \mapsto \gamma \circ x$。$H$ 上的 $\Gamma$-等变层范畴记为 $\mathbf{Equiv}_\Gamma(H)$：对象为 $(E, \pi : E \to H, \{a_\gamma : E \to E\}_{\gamma \in \Gamma})$，其中 $a_1 = \mathrm{id}_E$，$a_{\gamma_1 \gamma_2} = a_{\gamma_1} \circ a_{\gamma_2}$，$\pi \circ a_\gamma = h_\gamma \circ \pi$；态射 $\varphi : (E, \pi, a) \to (E', \pi', a')$ 为满足 $\pi' \circ \varphi = \pi$ 且 $\varphi \circ a_\gamma = a'_\gamma \circ \varphi$（$\forall \gamma \in \Gamma$）的层态射。
   给定 $\Gamma$-不变层态射 $q : H \to Q$（即 $\forall \gamma \in \Gamma, q \circ h_\gamma = q$）及 $(D, d : D \to Q) \in \mathcal{C}/Q$，纤维积 $H \times_Q D$ 连同第一投影 $\mathrm{pr}_1 : H \times_Q D \to H$ 和作用 $h_\gamma \times_Q \mathrm{id}_D$（因 $q \circ h_\gamma = q$ 而良定）给出 $\mathbf{Equiv}_\Gamma(H)$ 的对象。“$E$ 在 $Q$ 上实现”即存在 $(D, d) \in \mathcal{C}/Q$ 及 $\mathbf{Equiv}_\Gamma(H)$ 中的同构 $E \xrightarrow{\sim} H \times_Q D$。

---

## S1　有限群的自由作用

在本阶段设 $\Gamma$ 有限，且在 $T \in \mathsf{Prof}_{\mathcal{U}}$ 上作用自由（即对任意 $t \in T, \gamma \in \Gamma$，$\gamma \cdot t = t \implies \gamma = 1$）。

### 1. Profinite 轨道空间 $T/\Gamma$ 的构造与验证

令 $T/\Gamma := \{ \Gamma t \mid t \in T \}$ 为轨道集，赋予商映射 $p : T \twoheadrightarrow T/\Gamma$（$t \mapsto \Gamma t$）诱导的商拓扑。
- **$\mathcal{U}$-小性**：$T$ 为 $\mathcal{U}$-小集，其商集 $T/\Gamma$ 亦为 $\mathcal{U}$-小集。
- **既开又闭的商映射与紧性**：$T/\Gamma = p(T)$ 是紧空间 $T$ 的连续像，故紧。对任意 $A \subseteq T$，有 $p^{-1}(p(A)) = \bigcup_{\gamma \in \Gamma} \gamma \cdot A$。因每个 $\gamma \cdot (-)$ 是同胚且 $\Gamma$ 有限，当 $A$ 开（或闭）时 $p^{-1}(p(A))$ 是有限个开集（或闭集）之并，仍开（或闭），故 $p$ 既是开映射又是闭映射。
- **Hausdorff 性与全不连通性**：任取 $T/\Gamma$ 中相异两点 $\bar{x} \neq \bar{y}$，令 $x, y \in T$ 为其代表，则有限轨道 $\Gamma x$ 与 $\Gamma y$ 不交。由预备性质 2（clopen 基），对每对 $x' \in \Gamma x, y' \in \Gamma y$，存在 $T$ 的 clopen 子集 $W_{x', y'}$ 使 $x' \in W_{x', y'}, y' \notin W_{x', y'}$。由于 $\Gamma$ 有限，
  $$W := \bigcup_{x' \in \Gamma x} \bigcap_{y' \in \Gamma y} W_{x', y'}$$
  是 $T$ 的 clopen 子集，满足 $\Gamma x \subseteq W$ 且 $W \cap \Gamma y = \varnothing$。进一步取有限交
  $$V := \bigcap_{\gamma \in \Gamma} \gamma \cdot W.$$
  因 $\Gamma x$ 在 $\Gamma$ 下不变，对每个 $\gamma \in \Gamma$ 都有 $\Gamma x = \gamma(\Gamma x) \subseteq \gamma \cdot W$，故 $\Gamma x \subseteq V \subseteq W$，从而 $V \cap \Gamma y = \varnothing$。同时 $V$ 是有限个 clopen 集之交，故在 $T$ 中既开又闭，且对任意 $\delta \in \Gamma$ 有 $\delta \cdot V = V$，即 $p^{-1}(p(V)) = V$。由商拓扑定义，$p(V)$ 是 $T/\Gamma$ 的 **clopen** 子集，且 $\bar{x} \in p(V), \bar{y} \notin p(V)$。
  由此立即推出：(i) 任意相异两点可由不交开集 $p(V)$ 与 $(T/\Gamma) \setminus p(V)$ 分离，故 $T/\Gamma$ 是 Hausdorff 的；(ii) 任意含至少两点的子集 $C \subseteq T/\Gamma$ 可分解为两个非空相对开闭集 $C \cap p(V)$ 与 $C \setminus p(V)$，故 $T/\Gamma$ 全不连通。

综上，$T/\Gamma \in \mathsf{Prof}_{\mathcal{U}}$，且 $p : T \twoheadrightarrow T/\Gamma$ 是 $\mathsf{Prof}_{\mathcal{U}}$ 中的连续满射。（注：上述 $T/\Gamma \in \mathsf{Prof}_{\mathcal{U}}$ 的论证仅用到 $\Gamma$ 有限，无需作用自由，将在 S2 中直接复用于有限非自由情形。）

### 2. 证明 $h_{T/\Gamma}$ 是层商

记 $Q := h_{T/\Gamma}$，$q := h_p : H \to Q$。因对所有 $\gamma \in \Gamma$ 有 $p \circ \gamma_T = p$，故 $q \circ h_\gamma = q$，即 $q$ 是 $\Gamma$-不变的。需证对任意层 $Y \in \mathcal{C}$，预复合 $-\circ q$ 给出自然双射
$$\mathrm{Hom}_{\mathcal{C}}(Q, Y) \xrightarrow{\;\sim\;} \mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma := \{ f \in \mathrm{Hom}_{\mathcal{C}}(H, Y) \mid \forall \gamma \in \Gamma,\; f \circ h_\gamma = f \}.$$

考虑赋予离散拓扑的有限集 $\Gamma \in \mathsf{Prof}_{\mathcal{U}}$，则 $\Gamma \times T \cong \bigsqcup_{\gamma \in \Gamma} T \in \mathsf{Prof}_{\mathcal{U}}$。构造连续映射
$$\Phi : \Gamma \times T \longrightarrow T \times_{T/\Gamma} T, \qquad (\gamma, t) \longmapsto (\gamma \cdot t, t).$$
- **满射性**：若 $(t_1, t_2) \in T \times_{T/\Gamma} T$，则 $p(t_1) = p(t_2)$，即 $t_1 \in \Gamma t_2$，存在 $\gamma \in \Gamma$ 使 $t_1 = \gamma \cdot t_2$。
- **单射性**（此处使用自由性）：若 $(\gamma_1 \cdot t_1, t_1) = (\gamma_2 \cdot t_2, t_2)$，则 $t_1 = t_2$ 且 $(\gamma_2^{-1}\gamma_1) \cdot t_1 = t_1$，由作用自由得 $\gamma_1 = \gamma_2$。
紧空间到 Hausdorff 空间的连续双射 $\Phi$ 必为同胚，故 $\Phi$ 是 $\mathsf{Prof}_{\mathcal{U}}$ 中的同构。

现在任取 $Y \in \mathcal{C}$。由于 $\{p : T \twoheadrightarrow T/\Gamma\}$ 是单元素覆盖族（当 $T = \varnothing$ 时 $T/\Gamma = \varnothing$，$\{\mathrm{id}_\varnothing\}$ 亦为覆盖），层公理表明
$$Y(T/\Gamma) \xrightarrow{Y(p)} Y(T) \underset{Y(\mathrm{pr}_2)}{\overset{Y(\mathrm{pr}_1)}{\rightrightarrows}} Y(T \times_{T/\Gamma} T)$$
是 $\mathsf{Set}_{\mathcal{V}}$ 中的等化子。后接同构 $Y(\Phi) : Y(T \times_{T/\Gamma} T) \xrightarrow{\sim} Y(\bigsqcup_{\gamma \in \Gamma} T) \xrightarrow{\sim} \prod_{\gamma \in \Gamma} Y(T)$，其第 $\gamma$ 分量上 $\mathrm{pr}_1 \circ \Phi$ 为 $\gamma_T$，$\mathrm{pr}_2 \circ \Phi$ 为 $\mathrm{id}_T$。因此 $y \in Y(T)$ 等化 $Y(\mathrm{pr}_1), Y(\mathrm{pr}_2)$ 当且仅当对所有 $\gamma \in \Gamma$ 有 $Y(\gamma_T)(y) = y$。通过米田自然双射 $\mathrm{Hom}_{\mathcal{C}}(h_X, Y) \cong Y(X)$（将 $f \circ h_\gamma$ 变为 $Y(\gamma_T)(y)$），即得 $-\circ q : \mathrm{Hom}_{\mathcal{C}}(Q, Y) \xrightarrow{\sim} \mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma$，且关于 $Y$ 自然。故 $h_{T/\Gamma}$ 是 $H$ 模 $\Gamma$ 的层商。

### 3. 证明每个等变层 $E \to H$ 都在 $Q = h_{T/\Gamma}$ 上实现

我们先利用自由性与 clopen 基证明：**商映射 $p : T \to T/\Gamma$ 存在连续整体截面 $\sigma : T/\Gamma \to T$（即 $p \circ \sigma = \mathrm{id}_{T/\Gamma}$）**。
- 若 $T = \varnothing$，则 $T/\Gamma = \varnothing$，取 $\sigma = \mathrm{id}_\varnothing$ 即可。
- 若 $T \neq \varnothing$：对每个 $t \in T$，当 $\gamma \in \Gamma \setminus \{1\}$ 时由自由性有 $\gamma \cdot t \neq t$。由预备性质 2，可选取 $T$ 的 clopen 子集 $A_\gamma \ni t$ 使 $\gamma \cdot t \notin A_\gamma$，并令 $B_\gamma := T \setminus A_\gamma$（clopen 且含 $\gamma \cdot t$）。置
  $$W_t := \bigcap_{\gamma \in \Gamma \setminus \{1\}} \bigl(A_\gamma \cap \gamma^{-1}(B_\gamma)\bigr)$$
  （当 $\Gamma = \{1\}$ 时约定空交 $W_t := T$）。因 $\Gamma$ 有限，$W_t$ 是包含 $t$ 的 clopen 子集。断言族 $\{\delta \cdot W_t\}_{\delta \in \Gamma}$ 两两不交：若 $\delta_1 \neq \delta_2$ 而 $z \in (\delta_1 \cdot W_t) \cap (\delta_2 \cdot W_t)$，令 $x = \delta_2^{-1} \cdot z \in W_t$ 及 $\gamma = \delta_1^{-1}\delta_2 \neq 1$，则 $\gamma \cdot x = \delta_1^{-1} \cdot z \in W_t \subseteq A_\gamma$；但另一方面 $x \in W_t \subseteq \gamma^{-1}(B_\gamma)$ 给出 $\gamma \cdot x \in B_\gamma = T \setminus A_\gamma$，矛盾。
  令 $V_t := p(W_t)$。由于 $p^{-1}(V_t) = \bigsqcup_{\delta \in \Gamma} \delta \cdot W_t$ 在 $T$ 中既开又闭，故 $V_t$ 在 $T/\Gamma$ 中既开又闭；且限制 $p|_{W_t} : W_t \to V_t$ 是紧 Hausdorff 空间之间的连续双射（若 $x_1, x_2 \in W_t$ 有 $p(x_1) = p(x_2)$，则 $x_2 = \delta \cdot x_1 \in W_t \cap \delta \cdot W_t$，故 $\delta = 1, x_1 = x_2$），从而有连续逆 $s_t : V_t \to W_t \subseteq T$。
  由 $T/\Gamma$ 紧，开覆盖 $\{V_t\}_{t \in T}$ 有有限子覆盖 $V_{t_1}, \dots, V_{t_m}$。作两两不交的 clopen 加细 $V'_i := V_{t_i} \setminus \bigcup_{j < i} V_{t_j}$（$1 \le i \le m$），则 $T/\Gamma = \bigsqcup_{i=1}^m V'_i$ 为有限 clopen 分划。在每个 $V'_i$ 上令 $\sigma|_{V'_i} := s_{t_i}|_{V'_i}$，即得连续映射 $\sigma : T/\Gamma \to T$，满足 $p \circ \sigma = \mathrm{id}_{T/\Gamma}$。

由此，映射 $(\gamma, \bar{t}) \mapsto \gamma \cdot \sigma(\bar{t}) : \Gamma \times (T/\Gamma) \to T$ 是紧 Hausdorff 空间之间的连续双射（若 $\gamma_1 \cdot \sigma(\bar{t}_1) = \gamma_2 \cdot \sigma(\bar{t}_2)$，作用 $p$ 得 $\bar{t}_1 = \bar{t}_2$，再由自由性得 $\gamma_1 = \gamma_2$；任取 $t \in T$，有 $p(t) = p(\sigma(p(t)))$，故存在 $\gamma$ 使 $t = \gamma \cdot \sigma(p(t))$），因此是 $\Gamma$-等变同胚。其第一分量投影给出连续映射 $\rho : T \to \Gamma$，满足对任意 $t \in T, \delta \in \Gamma$：
$$t = \rho(t) \cdot \sigma(p(t)), \qquad \rho(\delta \cdot t) = \delta \rho(t).$$

现在任给 $(E, \pi, a) \in \mathbf{Equiv}_\Gamma(H)$。利用 $h_\sigma : Q \to H$，定义纤维积层
$$D := E \times_{H, h_\sigma} Q \in \mathcal{C}, \qquad d := \mathrm{pr}_2 : D \longrightarrow Q$$
（作为 $\mathcal{C}$ 中层的有限极限，$D$ 自动是层；对 $U \in \mathsf{Prof}_{\mathcal{U}}$，$D(U) = \{ (e_0, \bar{x}) \in E(U) \times Q(U) \mid \pi_U(e_0) = \sigma \circ \bar{x} \}$）。构造互逆态射 $\varphi : E \to H \times_Q D$ 与 $\psi : H \times_Q D \to E$ 如下：
- 对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$ 和 $e \in E(U)$，记 $x := \pi_U(e) \in C(U, T)$。复合连续映射 $\rho \circ x : U \to \Gamma$ 给出 $U$ 的有限 clopen 分划 $U = \bigsqcup_{\gamma \in \Gamma} U_\gamma$，其中 $U_\gamma := (\rho \circ x)^{-1}(\{\gamma\})$，嵌入记为 $i_\gamma : U_\gamma \hookrightarrow U$。在每个 $U_\gamma$ 上有 $x \circ i_\gamma = \gamma \cdot (\sigma \circ p \circ x \circ i_\gamma)$，于是截面 $e_{0, \gamma} := a_{\gamma^{-1}, U_\gamma}(E(i_\gamma)(e)) \in E(U_\gamma)$ 满足
  $$\pi_{U_\gamma}(e_{0, \gamma}) = h_{\gamma^{-1}, U_\gamma}\bigl(\pi_{U_\gamma}(E(i_\gamma)(e))\bigr) = \gamma^{-1} \cdot (x \circ i_\gamma) = (\sigma \circ p \circ x) \circ i_\gamma.$$
  由层 $E$ 在有限不交并 $U = \bigsqcup_{\gamma \in \Gamma} U_\gamma$ 上的粘合唯一性（$E(U) \xrightarrow{\sim} \prod_{\gamma \in \Gamma} E(U_\gamma)$），族 $(e_{0, \gamma})_{\gamma \in \Gamma}$ 粘合为唯一截面 $e_0 \in E(U)$，且在每个 $U_\gamma$ 上核验即得 $\pi_U(e_0) = \sigma \circ p \circ x$。令
  $$\varphi_U(e) := \bigl(x,\, (e_0, p \circ x)\bigr) \in H(U) \times_{Q(U)} D(U) = (H \times_Q D)(U).$$
- 反之，对 $\bigl(x, (e_0, \bar{x})\bigr) \in (H \times_Q D)(U)$（故 $p \circ x = \bar{x}$ 且 $\pi_U(e_0) = \sigma \circ \bar{x}$），仍取 clopen 分划 $U_\gamma = (\rho \circ x)^{-1}(\{\gamma\})$，将族 $\bigl(a_{\gamma, U_\gamma}(E(i_\gamma)(e_0))\bigr)_{\gamma \in \Gamma}$ 粘合为唯一截面 $\psi_U(x, (e_0, \bar{x})) \in E(U)$。

逐项核验所需性质：
1. **关于 $U$ 的自然性**：对连续映射 $f : U' \to U$ 及 $e \in E(U)$，令 $e' = E(f)(e)$，则 $x' = \pi_{U'}(e') = x \circ f$，从而 $U'_\gamma = (\rho \circ x')^{-1}(\{\gamma\}) = f^{-1}(U_\gamma)$。因 $a_{\gamma^{-1}}$ 是层态射，限制 $f_\gamma : U'_\gamma \to U_\gamma$ 将 $e_{0, \gamma}$ 拉回为 $e'_{0, \gamma}$，由粘合唯一性得 $e'_0 = E(f)(e_0)$，故 $\varphi$（同理 $\psi$）为层态射。
2. **互逆性与保 $H$-投影**：由定义 $\mathrm{pr}_1(\varphi_U(e)) = x = \pi_U(e)$。在每个 $U_\gamma$ 上，$E(i_\gamma)(\psi_U(\varphi_U(e))) = a_{\gamma, U_\gamma}(a_{\gamma^{-1}, U_\gamma}(E(i_\gamma)(e))) = E(i_\gamma)(e)$，故 $\psi_U \circ \varphi_U = \mathrm{id}_{E(U)}$。反之，对 $e = \psi_U(x, (e_0, \bar{x}))$，在 $U_\gamma$ 上有 $\pi_{U_\gamma}(E(i_\gamma)(e)) = \gamma \cdot (\sigma \circ \bar{x} \circ i_\gamma) = \gamma \cdot (\sigma \circ p \circ x \circ i_\gamma) = x \circ i_\gamma$，故 $\pi_U(e) = x$，分划不变，且 $a_{\gamma^{-1}, U_\gamma}(E(i_\gamma)(e)) = E(i_\gamma)(e_0)$，从而 $\varphi_U \circ \psi_U = \mathrm{id}$。
3. **$\Gamma$-等变性**：对 $\delta \in \Gamma$ 和 $e \in E(U)$，$e' := a_{\delta, U}(e)$ 对应的底映射为 $x' = \delta \cdot x$。由 $\rho(\delta \cdot x(u)) = \delta \rho(x(u))$ 知 $U'_{\delta \gamma} = U_\gamma$。在 $U'_{\delta \gamma} = U_\gamma$ 上，
   $$e'_{0, \delta\gamma} = a_{(\delta\gamma)^{-1}, U_\gamma}\bigl(E(i_\gamma)(a_{\delta, U}(e))\bigr) = a_{\gamma^{-1}\delta^{-1}\delta, U_\gamma}(E(i_\gamma)(e)) = e_{0, \gamma},$$
   故粘合后 $e'_0 = e_0$，同时 $p \circ (\delta \cdot x) = p \circ x$。因此 $\varphi_U(a_{\delta, U}(e)) = (\delta \cdot x, (e_0, p \circ x)) = (h_\delta \times_Q \mathrm{id}_D)_U(\varphi_U(e))$。

这证明了 $\varphi : E \xrightarrow{\sim} H \times_Q D$ 是 $\mathbf{Equiv}_\Gamma(H)$ 中的同构，$E$ 在 $Q = h_{T/\Gamma}$ 上实现。$\blacksquare$

---

## S2　有限集合上的纤维分类

在本阶段设 $\Gamma$ 和 $T$ 均有限（赋予离散拓扑，$T \in \mathsf{Prof}_{\mathcal{U}}$），$X$ 为有限 $\Gamma$-集合（$\mathcal{U}$-小，离散拓扑下 $X \in \mathsf{Prof}_{\mathcal{U}}$）且 $f : X \to T$ 为 $\Gamma$-等变映射。设 $R \subseteq T$ 为选定的 $T/\Gamma$-轨道代表集（每条 $\Gamma$-轨道恰选一个代表 $t \in R$），记稳定子 $\Gamma_t := \{ \gamma \in \Gamma \mid \gamma \cdot t = t \} \le \Gamma$。由 S1 第 1 节（该节仅用到 $\Gamma$ 有限），$T/\Gamma \in \mathsf{Prof}_{\mathcal{U}}$ 为有限离散商空间，$Q = h_{T/\Gamma}$，$q = h_p : H \to Q$。

### 1. 有限 $\Gamma$-集合 $X \to T$ 及其等变态射的分类

记 $\mathsf{FinSet}_\Gamma / T$ 为 $T$ 上的有限（$\mathcal{U}$-小）$\Gamma$-集合及保底映射的 $\Gamma$-等变映射构成的范畴；对每个 $t \in R$，记 $\mathsf{FinSet}_{\Gamma_t}$ 为有限（$\mathcal{U}$-小）左 $\Gamma_t$-集合及 $\Gamma_t$-等变映射构成的范畴。

**分类结论**：取代表纤维的函子
$$\Phi : \mathsf{FinSet}_\Gamma / T \longrightarrow \prod_{t \in R} \mathsf{FinSet}_{\Gamma_t}, \qquad (X, f) \longmapsto \bigl(X_t := f^{-1}(\{t\})\bigr)_{t \in R}, \quad \alpha \longmapsto (\alpha|_{X_t})_{t \in R}$$
是**范畴等价**，其拟逆为平衡积（诱导作用）函子
$$\Psi : \prod_{t \in R} \mathsf{FinSet}_{\Gamma_t} \longrightarrow \mathsf{FinSet}_\Gamma / T, \qquad (F_t)_{t \in R} \longmapsto \left(\bigsqcup_{t \in R} \Gamma \times^{\Gamma_t} F_t,\; [\gamma, z] \mapsto \gamma \cdot t\right).$$
具体而言：
- **对象同构类的分类**：$T$ 上的有限 $\Gamma$-集合 $(X, f)$ 在等变同构意义下一一对应于族 $(F_t)_{t \in R}$ 的同构类（其中每个 $F_t$ 是有限 $\Gamma_t$-集合；进一步，每个有限 $\Gamma_t$-集合唯一分解为有限个传递 $\Gamma_t$-集 $\Gamma_t / K$（$K \le \Gamma_t$，按 $\Gamma_t$-共轭分类）的不交并，对应于 $X$ 分解为轨道 $\Gamma / K \to \Gamma / \Gamma_t \cong \Gamma t$）。
- **态射的分类**：对任意 $(X, f), (X', f') \in \mathsf{FinSet}_\Gamma / T$，限制映射给出双射
  $$\mathrm{Hom}_{\mathsf{FinSet}_\Gamma / T}\bigl((X, f), (X', f')\bigr) \xrightarrow{\;\sim\;} \prod_{t \in R} \mathrm{Hom}_{\Gamma_t}(X_t, X'_t),$$
  其逆将 $(\beta_t : X_t \to X'_t)_{t \in R}$ 映为 $\alpha(\gamma \cdot x) := \gamma \cdot \beta_t(x)$（对 $t \in R, x \in X_t, \gamma \in \Gamma$）。

**证明**：
1. **良定性**：对 $t \in R, x \in X_t, h \in \Gamma_t$，有 $f(h \cdot x) = h \cdot f(x) = h \cdot t = t$，故 $X_t$ 在 $\Gamma_t$ 下稳定；等变态射 $\alpha : X \to X'$ 满足 $f'(\alpha(x)) = f(x) = t$，故限制为 $\Gamma_t$-等变映射 $\alpha_t : X_t \to X'_t$。反之，在 $\Gamma \times^{\Gamma_t} F_t := (\Gamma \times F_t) / \bigl((\gamma h, z) \sim (\gamma, h \cdot z),\; h \in \Gamma_t\bigr)$ 上，左作用 $\delta \cdot [\gamma, z] := [\delta\gamma, z]$ 与底映射 $[\gamma, z] \mapsto \gamma \cdot t$（因 $(\gamma h) \cdot t = \gamma \cdot t$）均良定且等变；因 $R, \Gamma, F_t$ 均有限且 $\mathcal{U}$-小，$\Psi((F_t))$ 有限且 $\mathcal{U}$-小。对态射族 $(\beta_t)$，$\Psi((\beta_t))([\gamma, z]) := [\gamma, \beta_t(z)]$ 因 $\beta_t(h \cdot z) = h \cdot \beta_t(z)$ 而良定。
2. **自然同构 $\varepsilon : \Psi \circ \Phi \xrightarrow{\sim} \mathrm{Id}$ 与 $\eta : \mathrm{Id} \xrightarrow{\sim} \Phi \circ \Psi$**：
   - 对 $(X, f)$，定义 $\varepsilon_X : \bigsqcup_{t \in R} \Gamma \times^{\Gamma_t} X_t \to X$ 为 $[\gamma, x] \mapsto \gamma \cdot x$。因 $(\gamma h) \cdot x = \gamma \cdot (h \cdot x)$ 故良定，且显然 $\Gamma$-等变并保到 $T$ 的映射。**满射性**：任取 $y \in X$，$f(y) \in T$ 落在唯一代表 $t \in R$ 的轨道中，即存在 $\gamma \in \Gamma$ 使 $f(y) = \gamma \cdot t$；于是 $x := \gamma^{-1} \cdot y \in X_t$ 且 $\varepsilon_X([\gamma, x]) = y$。**单射性**：若 $x_1 \in X_{t_1}, x_2 \in X_{t_2}$ 满足 $\gamma_1 \cdot x_1 = \gamma_2 \cdot x_2$，作用 $f$ 得 $\gamma_1 \cdot t_1 = \gamma_2 \cdot t_2$；因 $R$ 每条轨道仅含一代表，必有 $t_1 = t_2 =: t$ 且 $h := \gamma_1^{-1}\gamma_2 \in \Gamma_t$，从而 $x_1 = h \cdot x_2$，即 $[\gamma_1, x_1] = [\gamma_1, h \cdot x_2] = [\gamma_1 h, x_2] = [\gamma_2, x_2]$。容易核验 $\varepsilon_X$ 关于 $(X, f)$ 自然。
   - 对 $(F_s)_{s \in R}$ 及固定的 $t \in R$，$\Psi((F_s))$ 在 $t$ 上的纤维由满足 $\gamma \cdot s = t$ 的 $[\gamma, z]$ 组成，这迫使 $s = t$ 且 $\gamma \in \Gamma_t$。映射 $\eta_t : F_t \to (\Psi((F_s)))_t$，$z \mapsto [1, z]$ 以 $[\gamma, z] \mapsto \gamma \cdot z$（$\gamma \in \Gamma_t$）为双侧逆，且 $\Gamma_t$-等变、关于 $(F_s)$ 自然。故 $\Phi$ 与 $\Psi$ 互为拟逆等价。

### 2. $h_X$ 在 $Q = h_{T/\Gamma}$ 上实现的充要条件

这里等变层为 $(h_X, h_f, \{h_{\gamma_X}\}_{\gamma \in \Gamma})$。

**充要条件**：$h_X$ 在 $Q = h_{T/\Gamma}$ 上实现，**当且仅当对每个轨道代表 $t \in R$，稳定子 $\Gamma_t$ 在纤维 $X_t = f^{-1}(\{t\})$ 上的作用是平凡的**（等价地，对所有 $x \in X$ 和 $\gamma \in \Gamma$，$\gamma \cdot f(x) = f(x) \implies \gamma \cdot x = x$）。

**证明**：
- **必要性（$\Longrightarrow$）**：设存在 $(D, d) \in \mathcal{C}/Q$ 及 $\mathbf{Equiv}_\Gamma(H)$ 中的同构 $\varphi : h_X \xrightarrow{\sim} H \times_Q D$。在单点空间 $* \in \mathsf{Prof}_{\mathcal{U}}$ 上取值，将 $h_X(*) = C(*, X)$ 与 $X$ 等同（$x \leftrightarrow c_x$），$H(*)$ 与 $T$ 等同。任取 $t \in R, x \in X_t$ 及 $\gamma \in \Gamma_t$。记 $\varphi_*(c_x) = (c_t, y) \in H(*) \times_{Q(*)} D(*)$（第一分量即 $h_f(c_x) = c_{f(x)} = c_t$）。由 $\varphi$ 的 $\Gamma$-等变性及 $\gamma \cdot t = t$：
  $$\varphi_*(c_{\gamma \cdot x}) = \varphi_*\bigl(h_{\gamma_X, *}(c_x)\bigr) = \bigl(h_{\gamma, *}(c_t), y\bigr) = (c_{\gamma \cdot t}, y) = (c_t, y) = \varphi_*(c_x).$$
  因 $\varphi_*$ 为双射，得 $c_{\gamma \cdot x} = c_x$，即 $\gamma \cdot x = x$。
- **充分性（$\Longleftarrow$）**：设对所有 $t \in R$，$\Gamma_t$ 平凡作用于 $X_t$。先注意这对全体点均成立：对任意 $x \in X$，写 $x = \delta \cdot x_0$（$t \in R, x_0 \in X_t, \delta \in \Gamma$），若 $\gamma \in \Gamma_{f(x)} = \delta \Gamma_t \delta^{-1}$，则 $\delta^{-1}\gamma\delta \in \Gamma_t$ 固定 $x_0$，故 $\gamma \cdot x = \delta \cdot x_0 = x$。
  取有限离散轨道商集 $X/\Gamma \in \mathsf{Prof}_{\mathcal{U}}$，商投影 $p_X : X \twoheadrightarrow X/\Gamma$，诱导映射 $\bar{f} : X/\Gamma \to T/\Gamma$（$\Gamma x \mapsto \Gamma f(x)$）。考查映射
  $$\theta : X \longrightarrow T \times_{T/\Gamma} (X/\Gamma), \qquad x \longmapsto (f(x), \Gamma x),$$
  其中右侧赋予左 $\Gamma$-作用 $\gamma \cdot (s, \bar{x}) := (\gamma \cdot s, \bar{x})$。显然 $\theta$ 保 $T$-投影且 $\Gamma$-等变。
  - **满射**：若 $(s, \Gamma x) \in T \times_{T/\Gamma} (X/\Gamma)$，则 $\Gamma s = \Gamma f(x)$，存在 $\gamma \in \Gamma$ 使 $s = \gamma \cdot f(x) = f(\gamma \cdot x)$，于是 $\theta(\gamma \cdot x) = (s, \Gamma x)$。
  - **单射**：若 $\theta(x_1) = \theta(x_2)$，则 $f(x_1) = f(x_2)$ 且 $\Gamma x_1 = \Gamma x_2$。写 $x_2 = \gamma \cdot x_1$，则 $f(x_1) = f(\gamma \cdot x_1) = \gamma \cdot f(x_1)$，即 $\gamma \in \Gamma_{f(x_1)}$，故 $x_2 = \gamma \cdot x_1 = x_1$。
  作为有限离散空间之间的双射，$\theta$ 是 $\mathsf{Prof}_{\mathcal{U}}$ 中的同构。因 $h_{(-)}$ 保纤维积，令 $D := h_{X/\Gamma}$，$d := h_{\bar{f}} : D \to Q$，则 $h_\theta : h_X \xrightarrow{\sim} h_{T \times_{T/\Gamma} (X/\Gamma)} \cong H \times_Q D$ 给出 $\mathbf{Equiv}_\Gamma(H)$ 中的同构，作用仅改变 $H$ 坐标。

### 3. 可实现对象的自同构群

设 $h_X$ 在 $Q$ 上可实现。由预备性质 1 中米田嵌入 $h_{(-)} : \mathsf{Prof}_{\mathcal{U}} \to \mathcal{C}$ 的忠实满性，层态射 $\varphi : h_X \to h_X$ 唯一形如 $h_\alpha$（$\alpha : X \to X$），且 $h_\alpha$ 保 $H$-投影并 $\Gamma$-等变当且仅当 $\alpha$ 保 $T$-投影并 $\Gamma$-等变。再结合第 1、2 节结果：对每个 $t \in R$，$\Gamma_t$ 在 $X_t$ 上作用平凡，故任意集合映射 $X_t \to X_t$ 皆自动 $\Gamma_t$-等变，从而 $\mathrm{Aut}_{\Gamma_t}(X_t) = \mathrm{Sym}(X_t)$（$X_t$ 上的全对称群，阶为 $|X_t|!$，约定 $|\varnothing|! = 1$）。因此可实现对象的自同构群为
$$\mathrm{Aut}_{\mathbf{Equiv}_\Gamma(H)}(h_X) \;\cong\; \mathrm{Aut}_{\mathsf{FinSet}_\Gamma / T}(X, f) \;\cong\; \prod_{t \in R} \mathrm{Sym}(X_t),$$
其阶为 $\prod_{t \in R} (|X_t|!)$；显式地，元组 $(\sigma_t)_{t \in R} \in \prod_{t \in R} \mathrm{Sym}(X_t)$ 对应的 $X$ 自同构在 $\gamma \cdot x$（$t \in R, x \in X_t, \gamma \in \Gamma$）处取值为 $\gamma \cdot \sigma_t(x)$。$\blacksquare$

---

## S3　一般层的完整下降

本阶段仅使用共同设定：$\Gamma$ 为任意 $\mathcal{U}$-小离散群，连续作用于 $T \in \mathsf{Prof}_{\mathcal{U}}$，$H = h_T$。

### 1. 层化算子与商层 $q : H \to Q$ 的构造及验证

先验证 $\mathsf{Prof}_{\mathcal{U}}$ 上 $\mathsf{Set}_{\mathcal{V}}$-值预层的层化在宇宙 $\mathcal{V}$ 内良定。记 $\mathcal{S}_0 \subset \mathsf{Prof}_{\mathcal{U}}$ 为底层集合恰属于 $\mathcal{U}$ 的对象构成的满子范畴。因每个 $U \in \mathsf{Prof}_{\mathcal{U}}$ 是 $\mathcal{U}$-小集，存在双射 $U \xrightarrow{\sim} U_0 \in \mathcal{U}$，传递拓扑即知每个 $U \in \mathsf{Prof}_{\mathcal{U}}$ 同构于某 $U_0 \in \mathcal{S}_0$。对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$，令 $\mathrm{Cov}_0(U)$ 为形如 $\mathcal{U}_{\mathrm{cov}} = \{u_i : U_i \to U\}_{i < n}$（$n \in \mathbb{N}$，$U_i \in \mathcal{S}_0$）的有限联合满射覆盖全体。因 $\mathcal{U} \in \mathcal{V}$ 且 $\mathcal{S}_0 \in \mathcal{V}$，借任一 $U_0 \xrightarrow{\sim} U$（$U_0 \in \mathcal{S}_0$）可知 $\mathrm{Cov}_0(U)$ 是 $\mathcal{V}$-小集，且 $\mathsf{Prof}_{\mathcal{U}}$ 中 $U$ 的任意有限覆盖皆可被 $\mathrm{Cov}_0(U)$ 中覆盖加细。

对任意预层 $P : \mathsf{Prof}_{\mathcal{U}}^{\mathrm{op}} \to \mathsf{Set}_{\mathcal{V}}$ 和 $\mathcal{U}_{\mathrm{cov}} = \{u_i : U_i \to U\}_{i < n} \in \mathrm{Cov}_0(U)$，记相容族集合为
$$H^0(\mathcal{U}_{\mathrm{cov}}, P) := \mathrm{Eq}\!\left(\prod_{i < n} P(U_i) \rightrightarrows \prod_{i, j < n} P(U_i \times_U U_j)\right) \in \mathsf{Set}_{\mathcal{V}}.$$
若 $\mathcal{V}_{\mathrm{cov}} = \{v_k : V_k \to U\}_{k < m}$ 加细 $\mathcal{U}_{\mathrm{cov}}$，且 $g_k : V_k \to U_{\alpha(k)}$ 与 $h_k : V_k \to U_{\beta(k)}$ 为两组加细态射（即 $u_{\alpha(k)} \circ g_k = v_k = u_{\beta(k)} \circ h_k$），则对任意 $(s_i) \in H^0(\mathcal{U}_{\mathrm{cov}}, P)$，将等式 $s_{\alpha(k)}|_{U_{\alpha(k)} \times_U U_{\beta(k)}} = s_{\beta(k)}|_{U_{\alpha(k)} \times_U U_{\beta(k)}}$ 沿 $(g_k, h_k) : V_k \to U_{\alpha(k)} \times_U U_{\beta(k)}$ 拉回即得 $P(g_k)(s_{\alpha(k)}) = P(h_k)(s_{\beta(k)})$。故诱导映射 $H^0(\mathcal{U}_{\mathrm{cov}}, P) \to H^0(\mathcal{V}_{\mathrm{cov}}, P)$ 不依赖于加细数据的选取。又因任意两覆盖 $\{U_i \to U\}_{i < n}, \{V_k \to U\}_{k < m}$ 有公共纤维积加细（同构替换为 $\mathcal{S}_0$ 中对象后属于 $\mathrm{Cov}_0(U)$），加细预序构成有向偏序，故有向余极限
$$P^+(U) := \varinjlim_{\mathcal{U}_{\mathrm{cov}} \in \mathrm{Cov}_0(U)} H^0(\mathcal{U}_{\mathrm{cov}}, P) \in \mathsf{Set}_{\mathcal{V}}$$
良定。由 Grothendieck 加构造定理（SGA 4, Exposé II, Théorème 3.4；其小性条件由上述 $\mathrm{Cov}_0(U)$ 的 $\mathcal{V}$-小性保证）：
1. $P^+$ 恒为**分离预层**（事实上，若 $\alpha, \beta \in P^+(U)$ 在某有限覆盖 $\{W_r \to U\}_{r < l}$ 上相等，取代表它们的公共覆盖 $\{U_i \to U\}_{i < n}$，则在每个 $W_r \times_U U_i$ 上存在有限覆盖 $\{Z_{rim} \to W_r \times_U U_i\}$ 使代表截面在 $P(Z_{rim})$ 中相等；有限合成族 $\{Z_{rim} \to U\}_{r,i,m}$ 给出 $U$ 的有限覆盖，其上代表相等，故 $\alpha = \beta$），因此典范态射 $P^+ \to (P^+)^+$ 逐对象单射；
2. $P^# := (P^+)^+ \in \mathcal{C}$，且典范态射 $\eta_P : P \to P^#$ 给出包含函子 $\iota : \mathcal{C} \hookrightarrow \mathsf{PSh}(\mathsf{Prof}_{\mathcal{U}}, \mathsf{Set}_{\mathcal{V}})$ 的左伴随 $(-)^# \dashv \iota$（且因有向余极限与有限极限交换，$(-)^#$ 保有限极限）。

**对任意左 $\Gamma$-作用层 $M \in \mathcal{C}$（特别地 $M = H$）构造商层 $M/\Gamma$**：
定义预层商 $M^{\mathrm{pre}}(U) := M(U) / \Gamma$（等价关系为 $m \sim m' \iff \exists \gamma \in \Gamma, \gamma \cdot m = m'$；因 $M(U) \in \mathsf{Set}_{\mathcal{V}}$，有 $M^{\mathrm{pre}}(U) \in \mathsf{Set}_{\mathcal{V}}$；限制映射由 $\Gamma$-作用的自然性诱导），商态射 $q_M^{\mathrm{pre}} : M \to M^{\mathrm{pre}}$。置
$$M/\Gamma := (M^{\mathrm{pre}})^# \in \mathcal{C}, \qquad q_M := \eta_{M^{\mathrm{pre}}} \circ q_M^{\mathrm{pre}} : M \longrightarrow M/\Gamma.$$
特别地，取 $M = H$，令 **$Q := H/\Gamma$，$q := q_H : H \to Q$**。
- **不变性与泛性质**：对每个 $\gamma \in \Gamma$ 和 $x \in H(U)$，$q_H^{\mathrm{pre}}(\gamma \cdot x) = [x] = q_H^{\mathrm{pre}}(x)$，故 $q \circ h_\gamma = q$。对任意层 $Y \in \mathcal{C}$，由伴随 $(-)^# \dashv \iota$ 及集合商的泛性质，复合 $-\circ q$ 给出关于 $Y$ 自然的双射链
  $$\mathrm{Hom}_{\mathcal{C}}(Q, Y) \xrightarrow{-\circ \eta,\;\sim} \mathrm{Hom}_{\mathsf{PSh}}(H^{\mathrm{pre}}, \iota Y) \xrightarrow{-\circ q_H^{\mathrm{pre}},\;\sim} \mathrm{Hom}_{\mathsf{PSh}}(\iota H, \iota Y)^\Gamma = \mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma.$$
- **商层态射 $q_M : M \to M/\Gamma$ 的两个基本局部性质**（供下文反复援引）：
  - **(L1) 局部满射性**：$q_M : M \to M/\Gamma$ 局部满射。*验证*：由 $(-)^+$ 的定义，每个截面都在某有限覆盖上来自原预层；因有限覆盖的有限覆盖合成后仍为有限联合满射覆盖，$M/\Gamma = ((M^{\mathrm{pre}})^+)^+$ 在 $U$ 上的任意截面可在某有限覆盖 $\{U_i \to U\}$ 上提升至 $M^{\mathrm{pre}}(U_i) = M(U_i)/\Gamma$，进而提升至 $M(U_i)$。注意：**层范畴中局部满射必为满态射（epimorphism）**（若 $f_1 \circ u = f_2 \circ u$ 且 $u$ 局部满射，则目标截面局部提升后 $f_1, f_2$ 在有限覆盖上取值相等，由目标层的分离性知全局相等）。
  - **(L2) 局部同轨判据**：对任意 $W \in \mathsf{Prof}_{\mathcal{U}}$ 及 $m_1, m_2 \in M(W)$，$q_{M, W}(m_1) = q_{M, W}(m_2)$ 当且仅当存在有限覆盖 $\{w_k : W_k \to W\}_{k \in K}$ 及元素 $\gamma_k \in \Gamma$（$k \in K$），使得对所有 $k \in K$ 有 $M(w_k)(m_2) = \gamma_k \cdot M(w_k)(m_1)$。*验证*：充分性由 $q_M$ 的 $\Gamma$-不变性及 $M/\Gamma$ 的层分离性立得；反之，若 $q_{M, W}(m_1) = q_{M, W}(m_2)$，因 $(M^{\mathrm{pre}})^+ \hookrightarrow (M^{\mathrm{pre}})^# = M/\Gamma$ 单射，有 $[m_1] = [m_2] \in (M^{\mathrm{pre}})^+(W)$，按定义存在有限覆盖 $\{w_k : W_k \to W\}_{k \in K}$ 使 $[m_1|_{W_k}] = [m_2|_{W_k}] \in M(W_k)/\Gamma$，即存在 $\gamma_k \in \Gamma$ 使 $m_2|_{W_k} = \gamma_k \cdot (m_1|_{W_k})$。

### 2. 任意基底 $u : B \to Q$ 上的分类与不预选 $D$ 的充要判据

为同时完成 $Q$ 上与任意层态射 $u : B \to Q$ 上的分类（取 $B = Q, u = \mathrm{id}_Q$ 即回到 $Q$ 本身），设 $u : B \to Q$ 为 $\mathcal{C}$ 中任意态射。定义 $H_B := H \times_Q B$，配备投影 $q_B := \mathrm{pr}_2 : H_B \to B$ 及左 $\Gamma$-作用 $h_{B, \gamma} := h_\gamma \times_Q \mathrm{id}_B$（满足 $q_B \circ h_{B, \gamma} = q_B$）。记 $\mathbf{Equiv}_\Gamma(H_B)$ 为 $H_B$ 上的 $\Gamma$-等变层范畴；称 $(E', \pi', a') \in \mathbf{Equiv}_\Gamma(H_B)$ **在 $B$ 上实现**，若存在 $(D', d' : D' \to B) \in \mathcal{C}/B$ 及 $\mathbf{Equiv}_\Gamma(H_B)$ 中的同构 $E' \xrightarrow{\sim} H_B \times_B D'$（其中 $\Gamma$ 通过 $h_{B, \gamma} \times_B \mathrm{id}_{D'}$ 仅改变 $H_B$ 坐标）。

**引理 3.1（拉回商恢复引理）**：对任意 $(B, u : B \to Q) \in \mathcal{C}/Q$，第二投影 $q_B = \mathrm{pr}_2 : H_B = H \times_Q B \to B$ 满足：
1. $q_B$ 局部满射，且对任意 $W \in \mathsf{Prof}_{\mathcal{U}}$ 及 $z_1, z_2 \in H_B(W)$，$q_{B, W}(z_1) = q_{B, W}(z_2)$ 当且仅当存在有限覆盖 $\{w_k : W_k \to W\}_{k \in K}$ 及 $\gamma_k \in \Gamma$ 使 $H_B(w_k)(z_2) = h_{B, \gamma_k, W_k}(H_B(w_k)(z_1))$；
2. 由 $q_B$ 诱导的典范态射 $\varepsilon_B : H_B / \Gamma \xrightarrow{\sim} B$ 是 $\mathcal{C}$ 中的同构（即 $B$ 恰为 $H_B$ 模 $\Gamma$ 的层商）。

*证明*：(1) 任取 $b \in B(U)$，因 $q : H \to Q$ 局部满射（性质 (L1)），$u_U(b) \in Q(U)$ 在某有限覆盖 $\{u_i : U_i \to U\}$ 上有提升 $x_i \in H(U_i)$，于是 $(x_i, B(u_i)(b)) \in H_B(U_i)$ 提升 $B(u_i)(b)$，故 $q_B$ 局部满射。若 $z_1 = (x_1, b_1), z_2 = (x_2, b_2) \in H_B(W)$ 满足 $q_{B, W}(z_1) = q_{B, W}(z_2)$，则 $b_1 = b_2 =: b$，从而 $q_W(x_1) = u_W(b) = q_W(x_2)$；对 $q : H \to Q$ 应用 (L2) 得有限覆盖 $\{w_k : W_k \to W\}$ 及 $\gamma_k \in \Gamma$ 使 $x_2|_{W_k} = h_{\gamma_k}(x_1|_{W_k})$，故 $z_2|_{W_k} = (h_{\gamma_k}(x_1|_{W_k}), b|_{W_k}) = h_{B, \gamma_k}(z_1|_{W_k})$。反之显然。
(2) 需证对任意层 $Y \in \mathcal{C}$ 和 $\Gamma$-不变态射 $f : H_B \to Y$，存在唯一 $\bar{f} : B \to Y$ 使 $\bar{f} \circ q_B = f$。唯一性由 $q_B$ 局部满射（故为满态射）保证。下证存在性：先固定任意 $W$ 及满足 $q_{B, W}(z_1) = q_{B, W}(z_2)$ 的 $z_1, z_2 \in H_B(W)$，由 (1) 取覆盖 $\{w_k : W_k \to W\}$ 使 $z_2|_{W_k} = h_{B, \gamma_k}(z_1|_{W_k})$，则由 $f$ 的 $\Gamma$-不变性得 $f_W(z_2)|_{W_k} = f_{W_k}(h_{B, \gamma_k}(z_1|_{W_k})) = f_{W_k}(z_1|_{W_k}) = f_W(z_1)|_{W_k}$，由 $Y$ 的分离性得 $f_W(z_1) = f_W(z_2)$。于是对任意 $U$ 和 $b \in B(U)$，取有限覆盖 $\{u_i : U_i \to U\}$ 及提升 $z_i \in H_B(U_i)$（$q_{B, U_i}(z_i) = b|_{U_i}$）；在重交 $W_{ij} = U_i \times_U U_j$ 上，$z_i|_{W_{ij}}$ 与 $z_j|_{W_{ij}}$ 有相同的 $q_B$-像 $b|_{W_{ij}}$，故 $f_{U_i}(z_i)|_{W_{ij}} = f_{U_j}(z_j)|_{W_{ij}}$，由层公理粘合出唯一的 $\bar{f}_U(b) \in Y(U)$（同理由上述等值性与覆盖选取无关，且关于 $U$ 自然），满足 $\bar{f} \circ q_B = f$。$\square$

现在对任意 $u : B \to Q$，建立伴随函子对
$$G_B = (-)/\Gamma : \mathbf{Equiv}_\Gamma(H_B) \;\rightleftarrows\; \mathcal{C}/B : H_B \times_B (-) = F_B.$$
- 对 $(E', \pi', a') \in \mathbf{Equiv}_\Gamma(H_B)$，复合 $q_B \circ \pi' : E' \to B$ 是 $\Gamma$-不变的（$q_B \circ \pi' \circ a'_\gamma = q_B \circ h_{B, \gamma} \circ \pi' = q_B \circ \pi'$），由第 1 节 $q_{E'} : E' \to E'/\Gamma$ 的泛性质诱导唯一态射 $\overline{\pi'} : E'/\Gamma \to B$ 使 $\overline{\pi'} \circ q_{E'} = q_B \circ \pi'$，置 $G_B(E') := (E'/\Gamma, \overline{\pi'})$；等变态射 $\psi : E'_1 \to E'_2$ 唯一诱导 $\bar{\psi} : E'_1/\Gamma \to E'_2/\Gamma$，因 $q_{E'_1}$ 为满态射而自动与到 $B$ 的映射相容。
- **左伴随性 $G_B \dashv F_B$**：给定 $E' \in \mathbf{Equiv}_\Gamma(H_B)$ 和 $(D', d') \in \mathcal{C}/B$，$\mathbf{Equiv}_\Gamma(H_B)$ 中态射 $\varphi : E' \to H_B \times_B D'$ 的第一分量必为 $\pi'$，第二分量 $\varphi_2 : E' \to D'$ 需满足 $d' \circ \varphi_2 = q_B \circ \pi'$ 且 $\varphi_2 \circ a'_\gamma = \varphi_2$（$\forall \gamma \in \Gamma$）；由 $E'/\Gamma$ 的泛性质及 $q_{E'}$ 为满态射，$\varphi_2$ 唯一对应于 $\mathcal{C}/B$ 中的态射 $\tilde{\varphi}_2 : (E'/\Gamma, \overline{\pi'}) \to (D', d')$。
  - 伴随**单位**为 $\eta_{B, E'} := (\pi', q_{E'}) : E' \to H_B \times_B (E'/\Gamma)$（$\mathbf{Equiv}_\Gamma(H_B)$ 中态射）；
  - 伴随**余单位** $\varepsilon_{B, D'} : (H_B \times_B D')/\Gamma \to D'$ 由第二投影 $\mathrm{pr}_2 : H_B \times_B D' \to D'$ 诱导。注意典范同构 $H_B \times_B D' = (H \times_Q B) \times_B D' \cong H \times_Q D'$ 将 $\mathrm{pr}_2$ 变为 $H \times_Q D' \to D'$（结构映射为 $u \circ d' : D' \to Q$），故直接对 $(D', u \circ d') \in \mathcal{C}/Q$ 应用引理 3.1(2) 知：**对所有 $(D', d') \in \mathcal{C}/B$，余单位 $\varepsilon_{B, D'}$ 是 $\mathcal{C}/B$ 中的同构**，因而函子 **$F_B : \mathcal{C}/B \to \mathbf{Equiv}_\Gamma(H_B)$ 忠实满**！

**定理 3.2（不预选 $D$ 的可实现性充要判据与完整分类）**：设 $u : B \to Q$ 为 $\mathcal{C}$ 中任意态射（特别地，取 $B = Q, u = \mathrm{id}_Q$ 即得 $Q$ 上的结论）。对任意 $(E', \pi', a') \in \mathbf{Equiv}_\Gamma(H_B)$，以下三条等价：
1. $(E', \pi', a')$ 在 $B$ 上可实现；
2. **（典范商单位判据）** 典范态射 $\eta_{B, E'} = (\pi', q_{E'}) : E' \longrightarrow H_B \times_B (E'/\Gamma)$ 是 $\mathcal{C}$ 中的层同构；
3. **（截面稳定子平凡判据）** 对每个 $U \in \mathsf{Prof}_{\mathcal{U}}$、每个截面 $e' \in E'(U)$ 及每个 $\gamma \in \Gamma$，
   $$h_{B, \gamma, U}\bigl(\pi'_U(e')\bigr) = \pi'_U(e') \implies a'_{\gamma, U}(e') = e'$$
   （注意当 $\pi'_U(e') = (x, b) \in H(U) \times_{Q(U)} B(U)$ 时，左端条件即 $h_{\gamma, U}(x) = x$；在 $B = Q$ 时即 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e) \implies a_{\gamma, U}(e) = e$）。

在此条件下，记 $\mathbf{Equiv}_\Gamma^{\mathrm{real}}(H_B) \subseteq \mathbf{Equiv}_\Gamma(H_B)$ 为可实现对象构成的满子范畴，则：
- **所有对象与态射的分类**：伴随对 $F_B = H_B \times_B (-) : \mathcal{C}/B \;\rightleftarrows\; \mathbf{Equiv}_\Gamma^{\mathrm{real}}(H_B) : (-)/\Gamma = G_B$ 是**范畴伴随等价**。特别地，对任意 $(D'_1, d'_1), (D'_2, d'_2) \in \mathcal{C}/B$，映射 $g \mapsto \mathrm{id}_{H_B} \times_B g$ 给出态射双射 $\mathrm{Hom}_{\mathcal{C}/B}(D'_1, D'_2) \xrightarrow{\sim} \mathrm{Hom}_{\mathbf{Equiv}_\Gamma(H_B)}(H_B \times_B D'_1, H_B \times_B D'_2)$；等价地，对可实现对象 $E'_1, E'_2$，取 $\Gamma$-商给出双射 $\mathrm{Hom}_{\mathbf{Equiv}_\Gamma(H_B)}(E'_1, E'_2) \xrightarrow{\sim} \mathrm{Hom}_{\mathcal{C}/B}(E'_1/\Gamma, E'_2/\Gamma)$。
- **单个可实现对象所有实现的分类**：固定 $E' \in \mathbf{Equiv}_\Gamma^{\mathrm{real}}(H_B)$，其全体实现 $(D', d', \varphi : E' \xrightarrow{\sim} H_B \times_B D')$ 及实现间态射（满足 $(\mathrm{id}_{H_B} \times_B g) \circ \varphi_1 = \varphi_2$ 的 $g \in \mathrm{Hom}_{\mathcal{C}/B}(D'_1, D'_2)$）构成可缩群胚：典范实现 $(E'/\Gamma, \overline{\pi'}, \eta_{B, E'})$ 为始（亦终）对象——对任意实现 $(D', d', \varphi)$，存在**唯一**的 $\mathcal{C}/B$-态射 $g : (E'/\Gamma, \overline{\pi'}) \to (D', d')$ 使 $(\mathrm{id}_{H_B} \times_B g) \circ \eta_{B, E'} = \varphi$，即同构 $g = \varepsilon_{B, D'} \circ G_B(\varphi)$。

*定理 3.2 的证明*：
- **(2) $\implies$ (1)**：显然（取 $D' = E'/\Gamma$）。
- **(1) $\implies$ (3)**：设 $\varphi : E' \xrightarrow{\sim} H_B \times_B D'$ 为等变同构。若 $e' \in E'(U)$ 满足 $h_{B, \gamma, U}(\pi'_U(e')) = \pi'_U(e')$，记 $\varphi_U(e') = (\pi'_U(e'), y)$，则 $\varphi_U(a'_{\gamma, U}(e')) = (h_{B, \gamma, U}(\pi'_U(e')), y) = (\pi'_U(e'), y) = \varphi_U(e')$；因 $\varphi_U$ 单射，得 $a'_{\gamma, U}(e') = e'$。
- **(3) $\implies$ (2)**：先证对**任意** $E' \in \mathbf{Equiv}_\Gamma(H_B)$，$\eta_{B, E'} : E' \to H_B \times_B (E'/\Gamma)$ **恒局部满射**：任取 $(z, w) \in H_B(U) \times_{B(U)} (E'/\Gamma)(U)$（故 $q_{B, U}(z) = \overline{\pi'}_U(w)$）。由性质 (L1)，存在有限覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及 $e'_i \in E'(U_i)$ 使 $q_{E', U_i}(e'_i) = w|_{U_i}$。在 $U_i$ 上有 $q_{B, U_i}(\pi'_{U_i}(e'_i)) = \overline{\pi'}_{U_i}(q_{E', U_i}(e'_i)) = \overline{\pi'}_{U_i}(w|_{U_i}) = q_{B, U_i}(z|_{U_i})$。对 $\pi'_{U_i}(e'_i)$ 与 $z|_{U_i}$ 应用引理 3.1(1)，存在有限覆盖 $\{v_{ik} : V_{ik} \to U_i\}_{k \in K_i}$ 及 $\gamma_{ik} \in \Gamma$ 使 $z|_{V_{ik}} = h_{B, \gamma_{ik}}(\pi'_{U_i}(e'_i)|_{V_{ik}}) = \pi'_{V_{ik}}(a'_{\gamma_{ik}}(e'_i|_{V_{ik}}))$。于是 $\tilde{e}'_{ik} := a'_{\gamma_{ik}}(e'_i|_{V_{ik}}) \in E'(V_{ik})$ 在有限合成覆盖 $\{u_i \circ v_{ik} : V_{ik} \to U\}$ 上满足 $\eta_{B, E'}(\tilde{e}'_{ik}) = (z|_{V_{ik}}, w|_{V_{ik}})$，局部满射得证。
  再在条件 (3) 下证 $\eta_{B, E'}$ **逐对象单射**：设 $e'_1, e'_2 \in E'(U)$ 满足 $\eta_{B, E', U}(e'_1) = \eta_{B, E', U}(e'_2)$，即 $\pi'_U(e'_1) = \pi'_U(e'_2)$ 且 $q_{E', U}(e'_1) = q_{E', U}(e'_2)$。对 $q_{E'}$ 应用性质 (L2)，存在有限覆盖 $\{u_k : U_k \to U\}_{k \in K}$ 及 $\gamma_k \in \Gamma$ 使 $e'_2|_{U_k} = a'_{\gamma_k, U_k}(e'_1|_{U_k})$。两边取 $\pi'_{U_k}$ 得
  $$\pi'_{U_k}(e'_1|_{U_k}) = \pi'_{U_k}(e'_2|_{U_k}) = \pi'_{U_k}\bigl(a'_{\gamma_k, U_k}(e'_1|_{U_k})\bigr) = h_{B, \gamma_k, U_k}\bigl(\pi'_{U_k}(e'_1|_{U_k})\bigr).$$
  在 $U_k$ 上对 $e'_1|_{U_k}$ 应用条件 (3)，得 $a'_{\gamma_k, U_k}(e'_1|_{U_k}) = e'_1|_{U_k}$，故 $e'_2|_{U_k} = e'_1|_{U_k}$（$\forall k \in K$），由层 $E'$ 的分离性得 $e'_1 = e'_2$。
  最后，既逐对象单射又局部满射的层态射必为逐对象双射（任意目标截面在有限覆盖上的局部原像在重交上由单射性自动相容，从而粘合为全局原像），故 $\eta_{B, E'}$ 是同构。
- **分类部分的核验**：既然在 $\mathbf{Equiv}_\Gamma^{\mathrm{real}}(H_B)$ 上单位 $\eta_B$ 与余单位 $\varepsilon_B$ 均为自然同构，$G_B \dashv F_B$ 限制为伴随等价。对任意实现 $(D', d', \varphi)$，由伴随双射，满足 $F_B(g) \circ \eta_{B, E'} = \varphi$ 的 $g : G_B(E') \to D'$ 唯一存在且恰为 $\varphi$ 的伴随转置 $\varepsilon_{B, D'} \circ G_B(\varphi)$（两个同构的复合，故为同构）。$\square$

### 3. 与基底拉回的相容性证明

设 $v : B' \to B$ 为 $Q$ 上的任意层态射（即 $u : B \to Q$ 且 $u' = u \circ v : B' \to Q$；取 $B = Q, u = \mathrm{id}_Q$ 即为从 $Q$ 到任意基底 $B' \to Q$ 的拉回）。记：
- 底切片拉回函子 $v^* : \mathcal{C}/B \to \mathcal{C}/B'$，$(D, d) \mapsto (D \times_B B', \mathrm{pr}_2)$；
- 等变层拉回函子 $v^\sharp : \mathbf{Equiv}_\Gamma(H_B) \to \mathbf{Equiv}_\Gamma(H_{B'})$，将 $(E, \pi, a)$ 映为 $E \times_B B'$（关于 $\Gamma$-不变态射 $q_B \circ \pi : E \to B$ 的纤维积），赋予投影 $\pi_{B'} : E \times_B B' \to H_B \times_B B' \cong H_{B'}$（在截面上 $(e, b') \mapsto (x, b')$，其中 $\pi_U(e) = (x, v_U(b'))$）及作用 $a_{B', \gamma} := a_\gamma \times_B \mathrm{id}_{B'}$。

**相容性结论与证明**：
1. **拉回保持可实现性**：若 $E \in \mathbf{Equiv}_\Gamma^{\mathrm{real}}(H_B)$，对 $(e, b') \in (E \times_B B')(U)$（记 $\pi_U(e) = (x, v_U(b'))$），若 $h_{B', \gamma, U}(x, b') = (x, b')$，则 $h_{\gamma, U}(x) = x$，故 $h_{B, \gamma, U}(\pi_U(e)) = \pi_U(e)$，由定理 3.2(3) 得 $a_{\gamma, U}(e) = e$，从而 $a_{B', \gamma, U}(e, b') = (e, b')$。故 $v^\sharp(E) \in \mathbf{Equiv}_\Gamma^{\mathrm{real}}(H_{B'})$。
2. **与实现函子 $F$ 的交换性**：对任意 $(D, d) \in \mathcal{C}/B$，纤维积的标准结合/消去自然同构（在 $U$-截面上将 $(((x, b), y), b')$ 映为 $((x, b'), (y, b'))$，其中 $b = v_U(b') = d_U(y)$，$q_U(x) = u_U(b)$）给出 $\mathbf{Equiv}_\Gamma(H_{B'})$ 中关于 $D$ 自然的同构
   $$\alpha_{v, D} : v^\sharp(F_B(D)) = (H_B \times_B D) \times_B B' \xrightarrow{\;\sim\;} H_{B'} \times_{B'} (D \times_B B') = F_{B'}(v^*(D)).$$
3. **与商函子 $G$ 的交换性**：对**任意** $E \in \mathbf{Equiv}_\Gamma(H_B)$，$\Gamma$-不变态射 $(q_E \circ \mathrm{pr}_1, \mathrm{pr}_2) : E \times_B B' \to (E/\Gamma) \times_B B'$ 诱导 $\mathcal{C}/B'$ 中关于 $E$ 自然的态射
   $$\beta_{v, E} : G_{B'}(v^\sharp(E)) = (E \times_B B')/\Gamma \longrightarrow (E/\Gamma) \times_B B' = v^*(G_B(E)).$$
   我们证明 $\beta_{v, E}$ **恒为同构**：完全仿照引理 3.1(2)，先注意 $q_E \times_B \mathrm{id}_{B'} : E \times_B B' \to (E/\Gamma) \times_B B'$ 局部满射——对 $(w, b') \in ((E/\Gamma) \times_B B')(U)$，由 (L1) 在有限覆盖 $\{u_i : U_i \to U\}$ 上取 $e_i \in E(U_i)$ 使 $q_{E, U_i}(e_i) = w|_{U_i}$，则 $(q_B \circ \pi)_{U_i}(e_i) = \bar{\pi}_{U_i}(w|_{U_i}) = v_{U_i}(b'|_{U_i})$ 已自动成立，故 $(e_i, b'|_{U_i}) \in (E \times_B B')(U_i)$ 给出局部提升；其次，若 $(e_1, b'), (e_2, b') \in (E \times_B B')(W)$ 有相同的 $(q_E \times_B \mathrm{id}_{B'})$-像，则 $q_{E, W}(e_1) = q_{E, W}(e_2)$，由 (L2) 在某有限覆盖 $\{w_k : W_k \to W\}$ 上有 $e_2|_{W_k} = a_{\gamma_k}(e_1|_{W_k})$，即 $(e_2, b')|_{W_k} = a_{B', \gamma_k}((e_1, b')|_{W_k})$。因此任意层 $Y \in \mathcal{C}$ 的任意 $\Gamma$-不变态射 $E \times_B B' \to Y$ 唯一分解过 $(E/\Gamma) \times_B B'$，故 $\beta_{v, E}$ 为同构。
4. **单位与余单位的相容性（伴随等价态射）**：对任意 $E \in \mathbf{Equiv}_\Gamma(H_B)$，在 $U$-截面上直接追踪 $(e, b') \in (E \times_B B')(U)$ 的像即见两端均给出 $((x, b'), (q_{E, U}(e), b')) \in H_{B'}(U) \times_{B'(U)} ((E/\Gamma) \times_B B')(U)$，故交换关系
   $$F_{B'}(\beta_{v, E}) \circ \eta_{B', v^\sharp(E)} = \alpha_{v, G_B(E)} \circ v^\sharp(\eta_{B, E})$$
   严格成立；对偶地，在满态射像上核验即得 $v^*(\varepsilon_{B, D}) \circ \beta_{v, F_B(D)} = \varepsilon_{B', v^*(D)} \circ G_{B'}(\alpha_{v, D})$。特别地，$E$ 的任意实现 $(D, d, \varphi : E \xrightarrow{\sim} F_B(D))$ 拉回后即给出 $v^\sharp(E)$ 的实现 $(v^*(D), \alpha_{v, D} \circ v^\sharp(\varphi))$，且与典范商实现及等变态射分类完全相容。$\blacksquare$

---

## S4　单点上的检验

**判断结论**：**否**（$E$ **不一定**在 $Q$ 上可实现）。

以下在共同设定内给出完整的反例构造并逐项核验所需性质。

### 1. 反例构造

1. **群 $\Gamma$ 与空间 $T$**：
   - 取单点集 $T := \{0\} \in \mathcal{U}$（离散拓扑，$T \in \mathsf{Prof}_{\mathcal{U}}$），代表单点测试对象 $*$。此时 $H = h_T$ 是终层：对任意 $U \in \mathsf{Prof}_{\mathcal{U}}$，$H(U) = C(U, \{0\}) = \{*_U\}$ 为单点集。
   - 取二阶循环群 $\Gamma := \{1, \sigma\}$（$\sigma^2 = 1$，底层取 $\{0, 1\} \in \mathcal{U}$），平凡作用于 $T$。于是 $h_1 = h_\sigma = \mathrm{id}_H$。对任意 $Y \in \mathcal{C}$，$\mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma = \mathrm{Hom}_{\mathcal{C}}(H, Y)$，故由 S3 第 1 节泛性质的唯一性，可直接等同 $Q = H$，$q = \mathrm{id}_H : H \to Q$。
2. **等变层 $(E, \pi, a)$**：
   - 令 $\mathbb{F}_3 := \{0, 1, 2\} \in \mathcal{U}$ 为三元域，赋予离散拓扑，则 $\mathbb{F}_3 \in \mathsf{Prof}_{\mathcal{U}}$。
   - 对每个 $U \in \mathsf{Prof}_{\mathcal{U}}$，记 $\mathrm{Map}(U, \mathbb{F}_3)$ 为全体集合映射构成的 $\mathbb{F}_3$-线性空间（因 $U, \mathbb{F}_3 \in \mathsf{Set}_{\mathcal{V}}$（甚至 $\mathcal{U}$-小），其商集属于 $\mathsf{Set}_{\mathcal{V}}$），$C(U, \mathbb{F}_3) \subseteq \mathrm{Map}(U, \mathbb{F}_3)$ 为连续映射构成的 $\mathbb{F}_3$-线性子空间。定义预层
     $$P(U) := \mathrm{Map}(U, \mathbb{F}_3) / C(U, \mathbb{F}_3),$$
     对连续映射 $f : U' \to U$，因 $h \in C(U, \mathbb{F}_3) \implies h \circ f \in C(U', \mathbb{F}_3)$，拉回 $[g] \mapsto [g \circ f]$ 良定地使 $P$ 成为 $\mathsf{Set}_{\mathcal{V}}$-值预层。
   - 在 $P$ 上定义预层对合自同态 $\tau : P \to P$，$\tau_U([g]) := [-g]$（显然关于 $U$ 自然，且 $\tau \circ \tau = \mathrm{id}_P$）。
   - 应用 S3 第 1 节构造的层化算子（S3 第 1 节仅依赖共同设定，此处完全适用），定义层
     $$E := P^# = (P^+)^+ \in \mathcal{C},$$
     令 $\pi : E \to H$ 为到终层 $H$ 的唯一层态射，定义 $\Gamma$-作用为 $a_1 := \mathrm{id}_E$，$a_\sigma := \tau^# : E \to E$。由层化的函子性，$a_\sigma \circ a_\sigma = (\tau \circ \tau)^# = \mathrm{id}_E$；且因 $H$ 是终层、$h_\sigma = \mathrm{id}_H$，等式 $\pi \circ a_\sigma = \pi = h_\sigma \circ \pi$ 自动成立。故 $(E, \pi, a) \in \mathbf{Equiv}_\Gamma(H)$。

### 2. 性质核验

1. **单点条件在 $E(*)$ 上成立**：
   在单点空间 $* = \{0\} \in \mathcal{S}_0$ 上，任意集合映射 $* \to \mathbb{F}_3$ 皆连续，故 $\mathrm{Map}(*, \mathbb{F}_3) = C(*, \mathbb{F}_3)$，即 $P(*) = \{[0]\}$ 为单元素集。
   考查 $* $ 的任意有限联合满射覆盖 $\mathcal{U}_{\mathrm{cov}} = \{u_i : U_i \to *\}_{i < n} \in \mathrm{Cov}_0(*)$：因 $* \neq \varnothing$，存在某 $i_0 < n$ 及点 $x_0 \in U_{i_0}$。常值映射 $s_0 : * \to U_{i_0}$（$0 \mapsto x_0$）连续且满足 $u_{i_0} \circ s_0 = \mathrm{id}_*$，故单元素平凡覆盖 $\mathcal{U}_{\mathrm{triv}} = \{\mathrm{id}_* : * \to *\}$ 加细 $\mathrm{Cov}_0(*)$ 中的**一切**覆盖（即在有向偏序中共尾）。因此
   $$P^+(*) = H^0(\mathcal{U}_{\mathrm{triv}}, P) = P(*) = \{[0]\},$$
   再次对 $P^+$ 应用同一共尾论证得 $E(*) = (P^+)^+(*) = P^+(*) = \{[0]\}$。于是 $E(*)$ 仅含唯一元素 $e_0$，必有 $a_{\sigma, *}(e_0) = e_0$（且 $a_{1, *}(e_0) = e_0$），故 S4 的假定“对每个 $e \in E(*)$ 及 $\gamma \in \Gamma$，$\gamma \pi(e) = \pi(e) \implies a_\gamma(e) = e$”非空真地成立。

2. **$E$ 不在 $Q$ 上可实现**：
   利用 $\mathbb{N} \in \mathcal{U}$，构造 $\mathbb{N}$ 的单点紧化 $K := \mathbb{N} \cup \{\infty\} \in \mathcal{U}$（在 ZFC 中取 $\infty := \mathbb{N} \notin \mathbb{N}$）：规定 $V \subseteq K$ 为开集当且仅当 $\infty \notin V$，或 $\infty \in V$ 且 $\mathbb{N} \setminus V$ 有限。
   - **验证 $K \in \mathsf{Prof}_{\mathcal{U}}$**：$\varnothing$ 与 $K$ 开，且该族对任意并与有限交封闭；$K$ 的任意开覆盖必有某开集含 $\infty$，其补集有限，故存在有限子覆盖（紧性）；对 $K$ 中任意相异两点 $x \neq y$，必有一点（不妨设 $x$）属于 $\mathbb{N}$，此时单点集 $\{x\}$ 既开（$\infty \notin \{x\}$）又闭（$K \setminus \{x\}$ 含 $\infty$ 且补集有限），故既分离两点（Hausdorff），又将任意含至少两点的子集非平凡分拆为两个相对开集（全不连通）。因此 $K \in \mathsf{Prof}_{\mathcal{U}}$。
   - 取指示映射 $g : K \to \mathbb{F}_3$，定义为 $g(\infty) = 1$ 且对所有 $n \in \mathbb{N}$ 有 $g(n) = 0$。令 $s := \eta_{P, K}([g]) \in E(K)$，其中 $\eta_P : P \to P^# = E$ 为层化典范态射。
   - 断言 **$a_{\sigma, K}(s) \neq s$**：由 $\eta_P$ 的自然性，$a_{\sigma, K}(s) = \tau^#_K(\eta_{P, K}([g])) = \eta_{P, K}(\tau_K([g])) = \eta_{P, K}([-g])$。反设 $\eta_{P, K}([-g]) = \eta_{P, K}([g])$。由 S3 第 1 节性质 1，$P^+ \hookrightarrow (P^+)^+ = E$ 逐对象单射，故 $[-g] = [g] \in P^+(K)$。按 $P^+(K)$ 的定义，存在有限联合满射覆盖 $\{u_i : U_i \to K\}_{i < n}$（因 $K \neq \varnothing$，必有 $n \ge 1$）使对每个 $i < n$ 有 $[-g \circ u_i] = [g \circ u_i] \in P(U_i)$，即 $2(g \circ u_i) \in C(U_i, \mathbb{F}_3)$。因 $2$ 在 $\mathbb{F}_3$ 中可逆（$2 \cdot 2 = 1 \in \mathbb{F}_3$），得 $g \circ u_i \in C(U_i, \mathbb{F}_3)$ 对所有 $i < n$ 成立。令 $U' := \bigsqcup_{i < n} U_i \in \mathsf{Prof}_{\mathcal{U}}$，$u : U' \twoheadrightarrow K$ 为诱导连续满射，则 $g \circ u : U' \to \mathbb{F}_3$ 连续。但紧空间 $U'$ 到 Hausdorff 空间 $K$ 的连续满射 $u$ 必为闭映射从而是商映射，故 $g : K \to \mathbb{F}_3$ 连续。然而 $g^{-1}(\{1\}) = \{\infty\}$ 在 $K$ 中非开（含 $\infty$ 的开集在 $\mathbb{N}$ 中余有限，必非空交 $\mathbb{N}$），矛盾！
   - 在 $K$ 上，$h_{\sigma, K}(\pi_K(s)) = *_K = \pi_K(s)$，但 $a_{\sigma, K}(s) \neq s$。由 S3 定理 3.2(3)（或直接注意：若 $E \cong H \times_Q D = * \times_* D \cong D$ 且作用仅改变 $H = *$ 坐标，则必有 $a_\sigma = \mathrm{id}_E$），知 $E$ **不在 $Q$ 上可实现**。$\blacksquare$

---

## S5　局部满射的基底检验

**判断结论**：**是**（若 $u : B \to Q$ 局部满射，且 $E \times_Q B$ 作为 $H \times_Q B$ 上的等变对象可在 $B$ 上实现，则 $E$ **必可在 $Q$ 上实现**）。

**证明**：
本阶段仅设共同设定及 $u : B \to Q$ 局部满射，S3 定理 3.2 的全部条件在 $Q$ 上与在 $B$ 上均适用。我们要对 $(E, \pi, a) \in \mathbf{Equiv}_\Gamma(H)$ 验证 S3 定理 3.2(3) 在 $Q$ 上的截面稳定子判据。

任取 $U \in \mathsf{Prof}_{\mathcal{U}}$、截面 $e \in E(U)$ 及 $\gamma \in \Gamma$，设
$$h_{\gamma, U}\bigl(\pi_U(e)\bigr) = \pi_U(e).$$
考虑截面 $\bar{q} := q_U(\pi_U(e)) \in Q(U)$。因 $u : B \to Q$ 局部满射，存在 $U$ 的有限联合满射覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及截面族 $b_i \in B(U_i)$（$i \in I$），使得对每个 $i \in I$ 有
$$u_{U_i}(b_i) = Q(u_i)(\bar{q}) = q_{U_i}\bigl(\pi_{U_i}(E(u_i)(e))\bigr).$$
于是对每个 $i \in I$，序对 $e'_i := \bigl(E(u_i)(e), b_i\bigr)$ 属于纤维积 $(E \times_Q B)(U_i)$。计算其在 $H_B(U_i) = H(U_i) \times_{Q(U_i)} B(U_i)$ 中的投影 $\pi_{B, U_i}(e'_i) = \bigl(\pi_{U_i}(E(u_i)(e)), b_i\bigr)$ 在 $h_{B, \gamma, U_i} = h_{\gamma, U_i} \times_Q \mathrm{id}_{B(U_i)}$ 下的像：
$$h_{B, \gamma, U_i}\bigl(\pi_{B, U_i}(e'_i)\bigr) = \Bigl(h_{\gamma, U_i}\bigl(H(u_i)(\pi_U(e))\bigr),\, b_i\Bigr) = \Bigl(H(u_i)\bigl(h_{\gamma, U}(\pi_U(e))\bigr),\, b_i\Bigr) = \Bigl(H(u_i)(\pi_U(e)),\, b_i\Bigr) = \pi_{B, U_i}(e'_i).$$
因为 $E \times_Q B$ 可在 $B$ 上实现，对 $E \times_Q B$ 应用 $B$ 上的 S3 定理 3.2(3)，得对所有 $i \in I$ 有
$$\bigl(E(u_i)(a_{\gamma, U}(e)),\, b_i\bigr) = \bigl(a_{\gamma, U_i}(E(u_i)(e)),\, b_i\bigr) = a_{B, \gamma, U_i}(e'_i) = e'_i = \bigl(E(u_i)(e),\, b_i\bigr).$$
比较第一分量即得对所有 $i \in I$ 有 $E(u_i)(a_{\gamma, U}(e)) = E(u_i)(e)$。由于 $E$ 是层且 $\{u_i : U_i \to U\}_{i \in I}$ 是 $U$ 的覆盖（当 $U = \varnothing$ 时 $E(\varnothing)$ 为单点集亦成立），由层分离公理推出 $a_{\gamma, U}(e) = e$。

再由 $Q$ 上的 S3 定理 3.2(3)，知 $E$ 在 $Q$ 上可实现。$\blacksquare$

*（注：从范畴角度，由 S3 第 3 节相容性，$\eta_{B, E \times_Q B}$ 同构于 $\eta_E$ 沿局部满射 $u : B \to Q$ 的拉回 $\eta_E \times_Q \mathrm{id}_B$，而沿局部满射的拉回保守，同样给出上述结论。）*

---

## S6　非空基底与全局结论

### 1. 非空可表示层拉回的判断与完整反例

**判断结论**：**否**（仅假设 $B$ 是非空可表示层——即 $B \cong h_S$，其中 $S \in \mathsf{Prof}_{\mathcal{U}}$ 且 $S \neq \varnothing$——并有态射 $u : B \to Q$，$E \times_Q B$ 在 $B$ 上可实现**不一定**反映原 $E$ 在 $Q$ 上可实现）。

**完整反例与核验**：
1. **数据选取**（落入有限离散情形，故 S1、S2 结论在此例中均适用）：
   - 取二阶群 $\Gamma := \{1, \sigma\}$（$\sigma^2 = 1$）；
   - 取二点离散空间 $T := \{0, 1\} \in \mathsf{Prof}_{\mathcal{U}}$，赋予**平凡** $\Gamma$-作用（$\sigma \cdot 0 = 0, \sigma \cdot 1 = 1$）。此时商映射 $p = \mathrm{id}_T : T \to T/\Gamma = T$，且对任意 $Y \in \mathcal{C}$ 有 $\mathrm{Hom}_{\mathcal{C}}(h_T, Y)^\Gamma = \mathrm{Hom}_{\mathcal{C}}(h_T, Y)$，故 $Q = H = h_T$，$q = \mathrm{id}_H$。轨道代表集为 $R = \{0, 1\}$，稳定子 $\Gamma_0 = \Gamma_1 = \Gamma$。
   - 取三点离散空间 $X := \{a_0, a_1, b\} \in \mathsf{Prof}_{\mathcal{U}}$（例如取 $\{0, 1, 2\} \in \mathcal{U}$），定义投影 $f : X \to T$ 为 $f(a_0) = f(a_1) = 0$，$f(b) = 1$；定义 $\Gamma$-作用为 $\sigma \cdot a_0 = a_1$，$\sigma \cdot a_1 = a_0$，$\sigma \cdot b = b$。显然 $\sigma^2 = \mathrm{id}_X$ 且 $f(\sigma \cdot x) = f(x) = \sigma \cdot f(x)$。置 $E := h_X$，$\pi := h_f : E \to H$，$a_\gamma := h_{\gamma_X}$。
   - 取单点非空空间 $S := \{1\} \in \mathsf{Prof}_{\mathcal{U}}$（$S \neq \varnothing$），令非空可表示层 $B := h_S$，并取嵌入 $\iota : S = \{1\} \hookrightarrow \{0, 1\} = T$ 诱导的态射 $u := h_\iota : B \to Q = h_T$。
2. **核验原对象 $E$ 不可实现**：
   在轨道代表 $0 \in T$ 的纤维 $X_0 = f^{-1}(\{0\}) = \{a_0, a_1\}$ 上，稳定子 $\Gamma_0 = \Gamma$ 作用非平凡（$\sigma \cdot a_0 = a_1 \neq a_0$）。由 S2 第 2 节充要条件（此处 $\Gamma, T, X$ 均有限，S2 条件成立），$E = h_X$ **不在 $Q$ 上可实现**。
3. **核验拉回对象 $E \times_Q B$ 在 $B$ 上可实现**：
   因 $h_{(-)}$ 保纤维积且 $Q = H = h_T$，有典范同构
   $$H_B = h_T \times_{h_T} h_S \cong h_{T \times_T S} = h_S = B, \qquad E \times_Q B = h_X \times_{h_T} h_S \cong h_{X \times_T S} = h_{\{b\}},$$
   其中单点集 $X \times_T S \cong f^{-1}(\{1\}) = \{b\}$ 上的诱导 $\Gamma$-作用满足 $\sigma \cdot b = b$（平凡作用），且投影 $h_{\{b\}} \to h_S = B$ 为同构（将 $b$ 映为 $1$）。取 $(D', d') := (B, \mathrm{id}_B) \in \mathcal{C}/B$，则 $H_B \times_B D' = B \times_B B \cong B \cong E \times_Q B$，且两边 $\Gamma$-作用均平凡，故 $E \times_Q B$ **在 $B$ 上可实现**。

### 2. 据此前结果整理的可用检验原则

综合 S1–S6 已建立的定理与反例，判断一般等变层 $(E, \pi, a) \in \mathbf{Equiv}_\Gamma(H)$ 是否在层商 $Q = H/\Gamma$ 上可实现，遵循以下多层次检验原则：

1. **底空间作用自由时的免检自动实现原则（据 S1、S3）**：
   - 若 $\Gamma$ 在 $T$ 上的作用**自由**（对所有 $t \in T, \gamma \in \Gamma$，$\gamma \cdot t = t \implies \gamma = 1$；无需假设 $\Gamma$ 有限！），则**任意**等变层 $E \to H$ 必在 $Q$ 上实现。
     *（由 S3 导出：对任意 $U \in \mathsf{Prof}_{\mathcal{U}}, e \in E(U), \gamma \in \Gamma$，若 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$：当 $U = \varnothing$ 时 $E(\varnothing)$ 为单点集故 $a_{\gamma, \varnothing}(e) = e$；当 $U \neq \varnothing$ 时任取一点 $u \in U$，有 $\gamma \cdot (\pi_U(e)(u)) = \pi_U(e)(u)$，由自由性得 $\gamma = 1$，故 $a_{\gamma, U}(e) = e$；应用 S3 定理 3.2(3) 即得可实现。若进一步 $\Gamma$ 有限，则由 S1 知 $Q \cong h_{T/\Gamma}$ 可表示。）*

2. **一般层的内蕴精确判据（据 S3）**：
   当底作用不自由且无额外假设时，有两条等价的充要检验途径：
   - **典范商态射检验**：构造商层 $E/\Gamma$，检验 $\eta_E = (\pi, q_E) : E \to H \times_Q (E/\Gamma)$ 是否逐对象单射（因 S3 已证 $\eta_E$ 恒局部满射，单射即等价于同构）；
   - **全测试对象稳定子检验（不动点轨限制检验）**：对每个 $\gamma \in \Gamma \setminus \{1\}$，记闭子空间 $T^\gamma := \{t \in T \mid \gamma \cdot t = t\} \in \mathsf{Prof}_{\mathcal{U}}$（因 $T$ Hausdorff 故闭），则 $h_{T^\gamma}(U) = \{x \in H(U) \mid h_{\gamma, U}(x) = x\}$；由 S3 定理 3.2(3)，$E$ 可实现当且仅当对每个 $\gamma \in \Gamma \setminus \{1\}$，限制在拉回层 $E \times_H h_{T^\gamma}$ 上的作用 $a_\gamma$ 恒等于恒等态射（即对一切测试对象 $U \in \mathsf{Prof}_{\mathcal{U}}$ 及满足 $\mathrm{im}(\pi_U(e)) \subseteq T^\gamma$ 的截面 $e \in E(U)$ 均有 $a_{\gamma, U}(e) = e$）。

3. **单点纤维检验的适用边界：否定排障与点分离层简化（据 S2、S3、S4）**：
   - **单向排障原则（对任意层 $E$）**：由 S3 定理 3.2(3) 取 $U = *$，单点条件（$\forall e \in E(*), \gamma \in \Gamma,\; \gamma \pi_*(e) = \pi_*(e) \implies a_{\gamma, *}(e) = e$）是可实现的**必要条件**，可用于证伪；但由 S4 知对一般凝聚层它**不充分**。
   - **点分离层（特别是可表示层 $E = h_X$）的充要简化原则**：若层 $E$ 是**点分离的**——即对每个非空 $U \in \mathsf{Prof}_{\mathcal{U}}$，逐点取值映射 $\mathrm{ev}_U : E(U) \to \prod_{u \in U} E(*)$，$e \mapsto (E(\tilde{u})(e))_{u \in U}$（$\tilde{u} : * \to U$ 取值 $u$）为**单射**（例如任意可表示层 $E = h_X$（$X \in \mathsf{Prof}_{\mathcal{U}}$）或其子层，包含 S2 的有限情形）——则**单点检验在 $E(*)$ 上既是必要的也是充分的**，且每条 $T$ 的 $\Gamma$-轨道只需检验一个代表点 $t$ 上的稳定子 $\Gamma_t$！
     *（由 S3 导出：若 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$ 且 $U \neq \varnothing$，对每点 $u \in U$ 沿 $\tilde{u}$ 限制得 $\gamma \pi_*(E(\tilde{u})(e)) = \pi_*(E(\tilde{u})(e))$，由单点条件得 $E(\tilde{u})(a_{\gamma, U}(e)) = a_{\gamma, *}(E(\tilde{u})(e)) = E(\tilde{u})(e)$，再由 $\mathrm{ev}_U$ 单射得 $a_{\gamma, U}(e) = e$；又因 $\Gamma_{\delta \cdot t} = \delta \Gamma_t \delta^{-1}$ 且 $a_{\delta\gamma\delta^{-1}}(a_\delta(e_0)) = a_\delta(a_\gamma(e_0))$，同一轨道上各点的稳定子平凡性等价。）*

4. **基底拉回检验的适用边界：局部满射下降与联合局部满射族（据 S1、S3、S5、S6）**：
   - **任意基底的单向否证原则（据 S3）**：由 S3 第 3 节拉回相容性，对**任意** $u : B \to Q$，$E$ 在 $Q$ 上可实现必推出 $E \times_Q B$ 在 $B$ 上可实现；因此若存在某基底（如某单点基底 $* \to Q$）使拉回不可实现，即可直接判定原 $E$ 不可实现。但由 S6 知，即便 $B = h_S$ 非空可表示，缺少覆盖性时拉回可实现**不能**反推原 $E$ 可实现。
   - **局部满射基底的充要下降原则（据 S5）**：当且仅当基底满足覆盖条件——特别地，若 $u : B \to Q$ **局部满射**（或更一般地，给定联合局部满射族 $\{u_i : B_i \to Q\}_{i \in I}$，即每个 $Q(U)$ 截面都在某有限覆盖 $\{V_k \to U\}$ 上逐片提升至某 $B_{i_k}(V_k)$：照搬 S5 的证明即知各 $E \times_Q B_i$ 在 $B_i$ 上可实现 $\iff E$ 在 $Q$ 上可实现）——基底拉回检验是充要的。
   - **可表示基底局部满射的几何判别**：
     1. 由 S3 性质 (L1)，商态射 $q : H = h_T \to Q$ 自身恒局部满射；故对 $T$ 的任意有限联合满射覆盖 $\{S_j \to T\}_{j=1}^n$（$S_j \in \mathsf{Prof}_{\mathcal{U}}$），可表示基底 $B = h_{\bigsqcup_{j=1}^n S_j} \to H \xrightarrow{q} Q$ 恒局部满射，适用 S5。
     2. 当 $\Gamma$ 有限使 $Q \cong h_{T/\Gamma}$ 可表示时，可表示层态射 $u = h_g : h_S \to h_{T/\Gamma}$（$S \in \mathsf{Prof}_{\mathcal{U}}$）局部满射**当且仅当连续映射 $g : S \to T/\Gamma$ 是满射**（若 $g$ 满，对任意 $\bar{x} : U \to T/\Gamma$，纤维积投影 $U \times_{T/\Gamma} S \twoheadrightarrow U$ 给出单元素覆盖上的提升；反之若 $h_g$ 局部满射，$\mathrm{id}_{T/\Gamma} \in Q(T/\Gamma)$ 在有限覆盖上分解过 $g$，故 $T/\Gamma = \mathrm{im}(g)$）。也就是说，可表示基底 $h_S$ 必须覆盖 $T$ 的**全部** $\Gamma$-轨道（而非如 S6 反例那样仅非空而遗漏带非平凡稳定子的轨道），方能保证忠实反映原对象的可实现性。$\blacksquare$
