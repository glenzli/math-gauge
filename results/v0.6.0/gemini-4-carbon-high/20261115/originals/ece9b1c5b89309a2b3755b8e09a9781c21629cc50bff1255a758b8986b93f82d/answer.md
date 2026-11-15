{}
以下按题目共同设定及各阶段指定条件逐编号完整作答。

---

### 共同设定核验与基础记号

以下基础性质仅依赖题设中的共同设定（$\mathrm{ZFC}$，Grothendieck 宇宙 $\mathcal{U} \in \mathcal{V}$ 且 $\mathbb{N} \in \mathcal{U}$），在全部阶段均适用：

1. **景（Site）与大小性质**：
   记 $\mathbf{Prof}_{\mathcal{U}}$ 为 $\mathcal{U}$-小紧 Hausdorff 全不连通空间与连续映射构成的范畴。对任意 $U, X \in \mathbf{Prof}_{\mathcal{U}}$，记连续映射集为 $\mathrm{Cont}(U, X) := \mathrm{Hom}_{\mathbf{Prof}_{\mathcal{U}}}(U, X)$。由于 $\mathcal{U} \in \mathcal{V}$ 是传递集且对幂集封闭：
   - 每个 $\mathcal{U}$-小拓扑空间均同胚于底集属于 $\mathcal{U}$ 的空间，底集属于 $\mathcal{U}$ 的 profinite 空间全体构成 $\mathcal{U}$ 的子集，从而属于 $\mathcal{V}$；因此 $\mathbf{Prof}_{\mathcal{U}}$ 本质 $\mathcal{V}$-小且局部 $\mathcal{U}$-小（因而 $\mathrm{Cont}(U, X) \in \mathrm{Set}_{\mathcal{V}}$）。
   - $\mathbf{Prof}_{\mathcal{U}}$ 含空空间 $\varnothing$、单点空间 $*$，且对有限余积（拓扑有限不交并 $\coprod_{i \in I} U_i$）与 $\mathcal{U}$-小极限（特别地，纤维积 $U_1 \times_U U_2$）封闭：紧 Hausdorff 全不连通空间的积及闭子空间仍紧、Hausdorff、全不连通且 $\mathcal{U}$-小。
   - 有限联合满射族 $\{u_i : U_i \to U\}_{i \in I}$（$I$ 有限；当 $U = \varnothing$ 时允许 $I = \varnothing$ 空覆盖）构成 Grothendieck 预拓扑：恒等态射 $\{ \mathrm{id}_U \}$ 是覆盖；覆盖沿任意 $f : V \to U$ 的拉回 $\{V \times_U U_i \to V\}_{i \in I}$ 仍是有限联合满射族（当 $U = \varnothing$ 时必有 $V = \varnothing$，空族仍覆盖 $\varnothing$）；有限覆盖的复合仍为有限联合满射族。

2. **层条件的等价刻画与亚典范性（Subcanonicity）**：
   设 $\mathcal{C}$ 为 $\mathbf{Prof}_{\mathcal{U}}$ 上的 $\mathrm{Set}_{\mathcal{V}}$-值层范畴。对预层 $F : \mathbf{Prof}_{\mathcal{U}}^{\mathrm{op}} \to \mathrm{Set}_{\mathcal{V}}$：
   - 空空间 $\varnothing$ 上的空覆盖条件给出 $F(\varnothing) \cong \{*\}$（单元素集）；
   - 二元不交并覆盖 $\{U_1 \hookrightarrow U_1 \sqcup U_2,\, U_2 \hookrightarrow U_1 \sqcup U_2\}$ 的交 $U_1 \times_{U_1 \sqcup U_2} U_2 = \varnothing$，结合 $F(\varnothing) \cong \{*\}$ 及归纳法知：对任意有限指标集 $I$，$F\bigl(\coprod_{i \in I} U_i\bigr) \xrightarrow{\sim} \prod_{i \in I} F(U_i)$；
   - 对非空有限覆盖 $\{u_i : U_i \to U\}_{i \in I}$，令 $\widetilde{U} := \coprod_{i \in I} U_i \xrightarrow{u} U$，则 $\widetilde{U} \times_U \widetilde{U} \cong \coprod_{i,j \in I} (U_i \times_U U_j)$，从而 $F$ 为层当且仅当 $F$ 保持有限余积（变为有限积，含 $F(\varnothing) \cong \{*\}$）且对 $\mathbf{Prof}_{\mathcal{U}}$ 中每个满连续映射 $u : \widetilde{U} \twoheadrightarrow U$，序列
     $$F(U) \xrightarrow{F(u)} F(\widetilde{U}) \underset{F(\mathrm{pr}_2)}{\overset{F(\mathrm{pr}_1)}{\rightrightarrows}} F(\widetilde{U} \times_U \widetilde{U})$$
     在 $\mathrm{Set}_{\mathcal{V}}$ 中是等化子。
   - **可表示预层均为层**：对任意 $X \in \mathbf{Prof}_{\mathcal{U}}$，预层 $h_X(U) := \mathrm{Cont}(U, X)$ 满足 $\mathrm{Cont}(\varnothing, X) = \{!\}$、$\mathrm{Cont}(\coprod_{i \in I} U_i, X) \cong \prod_{i \in I} \mathrm{Cont}(U_i, X)$；又对紧空间 $\widetilde{U}$ 到 Hausdorff 空间 $U$ 的满连续映射 $u : \widetilde{U} \twoheadrightarrow U$，$u$ 是闭映射从而是拓扑商映射，故连续映射 $f : \widetilde{U} \to X$ 唯一分解为 $g \circ u$（$g \in \mathrm{Cont}(U, X)$）当且仅当 $f$ 在 $u$ 的纤维上常值（即 $f \circ \mathrm{pr}_1 = f \circ \mathrm{pr}_2$）。因此 $h_X \in \mathcal{C}$。由米田引理，对任意 $U \in \mathbf{Prof}_{\mathcal{U}}$ 及 $F \in \mathcal{C}$，有自然双射 $\mathrm{Hom}_{\mathcal{C}}(h_U, F) \cong F(U)$；米田嵌入 $h_{(-)} : \mathbf{Prof}_{\mathcal{U}} \to \mathcal{C}$ 忠实满且保持纤维积（因而 $\mathrm{Hom}_{\mathcal{C}}(h_U, h_T) \cong \mathrm{Cont}(U, T) = h_T(U)$，与题设记号一致）。

3. **等变对象与实现的精确表述**：
   离散群 $\Gamma$ 在 $T \in \mathbf{Prof}_{\mathcal{U}}$ 上的左作用给出群同态 $\Gamma \to \mathrm{Aut}_{\mathbf{Prof}_{\mathcal{U}}}(T)$，$\gamma \mapsto \gamma_T$（满足 $1_T = \mathrm{id}_T$，$(\gamma\delta)_T = \gamma_T \circ \delta_T$），诱导 $H = h_T$ 上的左群作用 $h_\gamma := h_{\gamma_T} : H \to H$（在 $U$-截面上为 $h_{\gamma, U}(x) = \gamma_T \circ x$，满足 $h_1 = \mathrm{id}_H$，$h_{\gamma\delta} = h_\gamma \circ h_\delta$）。
   - $H$ 上的**等变对象**是三元组 $(E, \pi, a)$，其中 $E \in \mathcal{C}$，$\pi : E \to H$ 为层态射，$a = \{a_\gamma : E \to E\}_{\gamma \in \Gamma}$ 为左群作用（$a_1 = \mathrm{id}_E$，$a_{\gamma\delta} = a_\gamma \circ a_\delta$）且对一切 $\gamma \in \Gamma$ 满足 $\pi \circ a_\gamma = h_\gamma \circ \pi$。等变态射 $f : (E, \pi, a) \to (E', \pi', a')$ 是满足 $\pi' \circ f = \pi$ 且 $\forall \gamma \in \Gamma,\, f \circ a_\gamma = a'_\gamma \circ f$ 的层态射。记此范畴为 $\mathrm{Equiv}_\Gamma(H)$。
   - 给定 $\Gamma$-不变态射 $q : H \to Q$（即 $\forall \gamma \in \Gamma,\, q \circ h_\gamma = q$），对切片范畴 $\mathcal{C}_{/Q}$ 中任一对象 $(D \xrightarrow{d} Q)$，纤维积 $H \times_Q D$（截面为 $\{(x, y) \in H(U) \times D(U) : q_U(x) = d_U(y)\}$）带有第一投影 $\mathrm{pr}_1 : H \times_Q D \to H$ 及仅改变 $H$ 坐标的 $\Gamma$-作用 $\{h_\gamma \times_Q \mathrm{id}_D\}_{\gamma \in \Gamma}$（因 $q \circ h_\gamma = q$ 良定义，在截面上为 $(x, y) \mapsto (h_{\gamma, U}(x), y)$）。记此实现函子为
     $$q^*_{\mathrm{eq}} : \mathcal{C}_{/Q} \longrightarrow \mathrm{Equiv}_\Gamma(H), \qquad (D \xrightarrow{d} Q) \longmapsto \bigl(H \times_Q D,\, \mathrm{pr}_1,\, \{h_\gamma \times_Q \mathrm{id}_D\}_{\gamma \in \Gamma}\bigr).$$
     等变对象 $(E, \pi, a)$ **在 $Q$ 上实现**是指存在 $(D \xrightarrow{d} Q) \in \mathcal{C}_{/Q}$ 及 $\mathrm{Equiv}_\Gamma(H)$ 中的同构 $\varphi : E \xrightarrow{\sim} q^*_{\mathrm{eq}}(D)$。

---

## S1　有限群的自由作用

本阶段设 $\Gamma$ 为有限群且在 $T \in \mathbf{Prof}_{\mathcal{U}}$ 上自由作用（即对任意 $t \in T$ 与 $\gamma \in \Gamma$，$\gamma t = t \implies \gamma = 1_\Gamma$）。

### 1. Profinite 轨道空间 $T/\Gamma$ 的构造与性质验证

令 $T/\Gamma := \{\Gamma t : t \in T\}$ 为轨道集合，$p : T \to T/\Gamma$，$t \mapsto \Gamma t$ 为自然投射，赋予 $T/\Gamma$ 由 $p$ 诱导的商拓扑。验证 $T/\Gamma \in \mathbf{Prof}_{\mathcal{U}}$：

1. **$\mathcal{U}$-小性**：因 $T$ 是 $\mathcal{U}$-小集且 Grothendieck 宇宙 $\mathcal{U}$ 对幂集与子集封闭，$T/\Gamma \subseteq \mathcal{P}(T)$（连同其商拓扑）也是 $\mathcal{U}$-小的。
2. **紧性**：$T/\Gamma = p(T)$ 是紧空间 $T$ 在连续映射 $p$ 下的像，故紧。
3. **既开又闭集分离相异点（从而 Hausdorff 且全不连通）**：
   先证紧 Hausdorff 全不连通空间 $T$ 中任意相异两点 $x \neq y$ 可由既开又闭（clopen）子集分离。对 $x \in T$，记其拟连通分支 $K_0(x) := \bigcap \{K \subseteq T : x \in K,\; K \text{ 既开又闭}\}$。$K_0(x)$ 是闭集。若 $K_0(x) = A \sqcup B$，其中 $A, B$ 在 $K_0(x)$ 中闭且不交，则 $A, B$ 在紧 Hausdorff（从而正规）空间 $T$ 中闭且不交，存在不交开集 $V_A \supseteq A$、$V_B \supseteq B$。于是 $T \setminus (V_A \cup V_B) \subseteq \bigcup_{K \ni x \text{ clopen}} (T \setminus K)$。由 $T \setminus (V_A \cup V_B)$ 的紧性及含 $x$ 的 clopen 集对有限交封闭，存在某个 clopen 集 $K \ni x$ 使 $K \subseteq V_A \cup V_B$。不妨设 $x \in A$，则 $K \cap V_A = K \setminus V_B$ 在 $T$ 中既开又闭且含 $x$，故 $K_0(x) \subseteq K \cap V_A \subseteq V_A$，迫使 $B = K_0(x) \cap V_B = \varnothing$。因此 $K_0(x)$ 连通；由 $T$ 全不连通知 $K_0(x) = \{x\}$。故对 $y \neq x$，存在 clopen 集 $U_{x,y} \subseteq T$ 使 $x \in U_{x,y}$ 且 $y \notin U_{x,y}$。

   现取 $T/\Gamma$ 中任意两个相异轨道 $O_1 \neq O_2$。因 $\Gamma$ 有限，$O_1, O_2$ 是 $T$ 中不交的有限子集。
   - 对每个 $x \in O_1$，令 $U_x := \bigcap_{y \in O_2} U_{x,y}$（有限交），则 $U_x$ 在 $T$ 中 clopen，$x \in U_x$ 且 $U_x \cap O_2 = \varnothing$；
   - 令 $U := \bigcup_{x \in O_1} U_x$（有限并），则 $U$ 在 $T$ 中 clopen，$O_1 \subseteq U$ 且 $U \cap O_2 = \varnothing$；
   - 令 $W := \bigcup_{\gamma \in \Gamma} \gamma_T(U)$。由于每个 $\gamma_T$ 是同胚且 $\Gamma$ 有限，$W$ 在 $T$ 中仍是 clopen 集，且 $\Gamma$-不变（即 $p^{-1}(p(W)) = W$）。又 $O_1 \subseteq U \subseteq W$，而由 $O_2$ 的 $\Gamma$-不变性知 $\gamma_T(U) \cap O_2 = \gamma_T(U \cap O_2) = \varnothing$，故 $W \cap O_2 = \varnothing$。

   由商拓扑定义，$p^{-1}(p(W)) = W$ 在 $T$ 中既开又闭蕴含 $p(W)$ 在 $T/\Gamma$ 中既开又闭，且 $O_1 \in p(W)$，$O_2 \notin p(W)$。由此立得：
   - $p(W)$ 与 $(T/\Gamma) \setminus p(W)$ 是分离 $O_1$ 与 $O_2$ 的不交开邻域，故 $T/\Gamma$ 是 **Hausdorff** 空间；
   - $T/\Gamma$ 的任何至少含两点的子集 $S$（取其中 $O_1 \neq O_2$）都被分裂为非空相对 clopen 子集 $S \cap p(W)$ 与 $S \setminus p(W)$，故 $T/\Gamma$ **全不连通**。

   综上，$T/\Gamma \in \mathbf{Prof}_{\mathcal{U}}$，且 $p : T \to T/\Gamma$ 是 $\mathbf{Prof}_{\mathcal{U}}$ 中满足 $\forall \gamma \in \Gamma,\, p \circ \gamma_T = p$ 的满连续映射。

### 2. 证明 $Q := h_{T/\Gamma}$ 是层商 $H/\Gamma$

赋予有限群 $\Gamma$ 离散拓扑，则 $\Gamma \in \mathbf{Prof}_{\mathcal{U}}$ 且 $\Gamma \times T \cong \coprod_{\gamma \in \Gamma} T \in \mathbf{Prof}_{\mathcal{U}}$。考察映射
$$\Psi : \Gamma \times T \longrightarrow T \times_{T/\Gamma} T, \qquad (\gamma, t) \longmapsto (\gamma t, t).$$
- 在每个 clopen 分支 $\{\gamma\} \times T \cong T$ 上，$\Psi_\gamma = (\gamma_T, \mathrm{id}_T)$ 连续且满足 $p \circ \gamma_T = p$，故 $\Psi$ 是到 $T \times_{T/\Gamma} T$ 的连续映射；
- 若 $(t', t) \in T \times_{T/\Gamma} T$，则 $p(t') = p(t) \implies \Gamma t' = \Gamma t$，存在 $\gamma \in \Gamma$ 使 $t' = \gamma t$，故 $\Psi$ 满射；
- 若 $(\gamma_1 t_1, t_1) = (\gamma_2 t_2, t_2)$，则 $t_1 = t_2$ 且 $(\gamma_2^{-1}\gamma_1) t_1 = t_1$，由 $\Gamma$ 在 $T$ 上**自由作用**知 $\gamma_1 = \gamma_2$，故 $\Psi$ 单射。
由于 $\Gamma \times T$ 紧而 $T \times_{T/\Gamma} T$ Hausdorff，连续双射 $\Psi$ 是同胚，即 $\mathbf{Prof}_{\mathcal{U}}$ 中的同构。

令 $q := h_p : H \to Q = h_{T/\Gamma}$。由 $p \circ \gamma_T = p$ 知 $q \circ h_\gamma = q$（$\Gamma$-不变）。任取层 $F \in \mathcal{C}$，我们来证明前复合
$$q^* : \mathrm{Hom}_{\mathcal{C}}(Q, F) \longrightarrow \mathrm{Hom}_{\mathcal{C}}(H, F)^\Gamma := \{\beta \in \mathrm{Hom}_{\mathcal{C}}(H, F) : \forall \gamma \in \Gamma,\, \beta \circ h_\gamma = \beta\}$$
是自然双射（即 $h_{T/\Gamma}$ 是 $\Gamma$ 在 $H$ 上作用在层范畴 $\mathcal{C}$ 中的余等化子/上极限，亦即层商）：
- 因 $\{p : T \to T/\Gamma\}$ 是 $\mathbf{Prof}_{\mathcal{U}}$ 中的单元覆盖（即使 $T = \varnothing$ 时 $\varnothing \to \varnothing$ 亦为满射），对层 $F$ 有等化子
  $$F(T/\Gamma) \xrightarrow{F(p)} F(T) \underset{F(\mathrm{pr}_2)}{\overset{F(\mathrm{pr}_1)}{\rightrightarrows}} F(T \times_{T/\Gamma} T).$$
- 复合上同构 $F(\Psi) : F(T \times_{T/\Gamma} T) \xrightarrow{\sim} F\bigl(\coprod_{\gamma \in \Gamma} T\bigr) \xrightarrow{\sim} \prod_{\gamma \in \Gamma} F(T)$，因 $\mathrm{pr}_1 \circ \Psi_\gamma = \gamma_T$ 且 $\mathrm{pr}_2 \circ \Psi_\gamma = \mathrm{id}_T$，截面 $s \in F(T)$ 满足 $F(\mathrm{pr}_1)(s) = F(\mathrm{pr}_2)(s)$ 当且仅当对所有 $\gamma \in \Gamma$ 有 $F(\gamma_T)(s) = s$。故 $F(p) : F(T/\Gamma) \xrightarrow{\sim} F(T)^\Gamma$ 是双射。
- 在米田自然同构 $\mathrm{Hom}_{\mathcal{C}}(h_{T/\Gamma}, F) \cong F(T/\Gamma)$ 与 $\mathrm{Hom}_{\mathcal{C}}(h_T, F) \cong F(T)$（$\beta \mapsto \beta_T(\mathrm{id}_T)$）下，$\beta \circ h_p$ 对应 $F(p)(\alpha_{T/\Gamma}(\mathrm{id}_{T/\Gamma}))$，而 $(\beta \circ h_\gamma)_T(\mathrm{id}_T) = \beta_T(\gamma_T) = \beta_T(H(\gamma_T)(\mathrm{id}_T)) = F(\gamma_T)(\beta_T(\mathrm{id}_T))$，因此 $q^* : \mathrm{Hom}_{\mathcal{C}}(Q, F) \xrightarrow{\sim} \mathrm{Hom}_{\mathcal{C}}(H, F)^\Gamma$ 对一切 $F \in \mathcal{C}$ 自然成立。这证明了 $Q = h_{T/\Gamma}$ 是 $H$ 模 $\Gamma$ 的层商。

### 3. 证明每个等变层 $(E, \pi, a) \in \mathrm{Equiv}_\Gamma(H)$ 都在 $Q = h_{T/\Gamma}$ 上实现

对任意 $U \in \mathbf{Prof}_{\mathcal{U}}$ 及 $g \in Q(U) = \mathrm{Cont}(U, T/\Gamma)$，记纤维积 $\widetilde{U}_g := U \times_{T/\Gamma} T \in \mathbf{Prof}_{\mathcal{U}}$，带投影 $\mathrm{pr}_1 : \widetilde{U}_g \to U$、$\mathrm{pr}_2 : \widetilde{U}_g \to T$ 及左 $\Gamma$-作用 $\gamma_{\widetilde{U}_g}(u, t) := (u, \gamma t)$。定义预层 $D : \mathbf{Prof}_{\mathcal{U}}^{\mathrm{op}} \to \mathrm{Set}_{\mathcal{V}}$ 如下：
$$D(U) := \left\{ (g, s) \;\middle|\; g \in \mathrm{Cont}(U, T/\Gamma),\; s \in E(\widetilde{U}_g) \text{ 满足 } \pi_{\widetilde{U}_g}(s) = \mathrm{pr}_2 \text{ 且 } \forall \gamma \in \Gamma,\; E(\gamma_{\widetilde{U}_g})(s) = a_{\gamma, \widetilde{U}_g}(s) \right\},$$
结构映射 $d_U : D(U) \to Q(U)$ 取为 $d_U(g, s) := g$；对态射 $f : V \to U$，令 $\tilde{f} := f \times_{T/\Gamma} \mathrm{id}_T : \widetilde{V}_{g \circ f} \to \widetilde{U}_g$，因 $\mathrm{pr}_2 \circ \tilde{f} = \mathrm{pr}_2$ 且 $\tilde{f} \circ \gamma_{\widetilde{V}_{g \circ f}} = \gamma_{\widetilde{U}_g} \circ \tilde{f}$，由 $\pi$ 与 $a_\gamma$ 的自然性知 $D(f)(g, s) := (g \circ f,\, E(\tilde{f})(s)) \in D(V)$ 良定义且具函子性（又 $Q(U), E(\widetilde{U}_g) \in \mathrm{Set}_{\mathcal{V}}$，故 $D(U) \in \mathrm{Set}_{\mathcal{V}}$）。

1. **验证 $D \in \mathcal{C}$ 是层**：
   设 $\{u_i : U_i \to U\}_{i \in I}$ 是 $\mathbf{Prof}_{\mathcal{U}}$ 中的覆盖，$\{(g_i, s_i) \in D(U_i)\}_{i \in I}$ 是相容族。
   - 因 $Q = h_{T/\Gamma}$ 是层，$\{g_i\}$ 唯一粘合为 $g \in Q(U)$ 使 $g \circ u_i = g_i$。
   - 将覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 沿 $\mathrm{pr}_1 : \widetilde{U}_g \to U$ 拉回，得 $\widetilde{U}_g$ 的覆盖 $\{\tilde{u}_i : \widetilde{U_i}_{g_i} \to \widetilde{U}_g\}_{i \in I}$，且交满足 $\widetilde{U_i}_{g_i} \times_{\widetilde{U}_g} \widetilde{U_j}_{g_j} \cong (U_i \times_U U_j) \times_{T/\Gamma} T$。于是 $\{s_i \in E(\widetilde{U_i}_{g_i})\}_{i \in I}$ 是层 $E$ 的相容族，唯一粘合为 $s \in E(\widetilde{U}_g)$。
   - 因 $\pi_{\widetilde{U}_g}(s)$ 与 $\mathrm{pr}_2$ 在覆盖 $\{\tilde{u}_i\}$ 上限制相等，由层 $H$ 的分离性得 $\pi_{\widetilde{U}_g}(s) = \mathrm{pr}_2$；同理，利用 $\gamma_{\widetilde{U}_g} \circ \tilde{u}_i = \tilde{u}_i \circ \gamma_{\widetilde{U_i}_{g_i}}$ 知 $E(\gamma_{\widetilde{U}_g})(s)$ 与 $a_{\gamma, \widetilde{U}_g}(s)$ 在覆盖 $\{\tilde{u}_i\}$ 上限制相等，由层 $E$ 的分离性得 $E(\gamma_{\widetilde{U}_g})(s) = a_{\gamma, \widetilde{U}_g}(s)$。故 $(g, s) \in D(U)$ 为唯一粘合，$D$ 是层且 $d : D \to Q$ 是层态射。

2. **构造等变同构 $\Phi : H \times_Q D \xrightarrow{\sim} E$ 及其显式逆 $\Theta$**：
   - **定义 $\Phi$**：对 $(x, (g, s)) \in H(U) \times_{Q(U)} D(U)$，有 $p \circ x = g$，故存在连续截面 $\sigma_x := (\mathrm{id}_U, x) : U \to \widetilde{U}_g$。定义
     $$\Phi_U\bigl(x, (g, s)\bigr) := E(\sigma_x)(s) \in E(U).$$
     $\Phi_U$ 对 $U$ 显然自然。核验 $H$ 上态射性与 $\Gamma$-等变性：
     $$\pi_U\bigl(E(\sigma_x)(s)\bigr) = H(\sigma_x)\bigl(\pi_{\widetilde{U}_g}(s)\bigr) = H(\sigma_x)(\mathrm{pr}_2) = \mathrm{pr}_2 \circ (\mathrm{id}_U, x) = x;$$
     对 $\gamma \in \Gamma$，因 $\sigma_{\gamma_T \circ x} = \gamma_{\widetilde{U}_g} \circ \sigma_x$，有
     $$\Phi_U\bigl(\gamma_T \circ x, (g, s)\bigr) = E(\sigma_x)\bigl(E(\gamma_{\widetilde{U}_g})(s)\bigr) = E(\sigma_x)\bigl(a_{\gamma, \widetilde{U}_g}(s)\bigr) = a_{\gamma, U}\bigl(E(\sigma_x)(s)\bigr) = a_{\gamma, U}\bigl(\Phi_U(x, (g, s))\bigr).$$
   - **定义逆映射 $\Theta_U : E(U) \to H(U) \times_{Q(U)} D(U)$**：对 $e \in E(U)$，令 $x := \pi_U(e) \in H(U)$，$g := p \circ x \in Q(U)$。将步骤 2 中的同胚 $\Psi : \Gamma \times T \xrightarrow{\sim} T \times_{T/\Gamma} T$ 沿 $x : U \to T$ 拉回，得 $\mathbf{Prof}_{\mathcal{U}}$ 中的同构
     $$\Psi_x : \coprod_{\gamma \in \Gamma} U \cong \Gamma \times U \xrightarrow{\;\sim\;} \widetilde{U}_g, \qquad (\gamma, u) \longmapsto (u, \gamma x(u))$$
     （其逆为 $(u, t) \mapsto (\mathrm{pr}_1(\Psi^{-1}(t, x(u))),\, u)$，连续双射）。记第 $\gamma$ 个分支嵌入为 $\Psi_{x, \gamma} : U \to \widetilde{U}_g$，$u \mapsto (u, \gamma x(u))$。由层性质 $E(\widetilde{U}_g) \xrightarrow[\sim]{E(\Psi_x)} \prod_{\gamma \in \Gamma} E(U)$，存在唯一的 $s_e \in E(\widetilde{U}_g)$ 使得对每个 $\gamma \in \Gamma$ 有 $E(\Psi_{x, \gamma})(s_e) = a_{\gamma, U}(e)$。
     验证 $(g, s_e) \in D(U)$：
     - 对每个 $\gamma \in \Gamma$，$H(\Psi_{x, \gamma})(\pi_{\widetilde{U}_g}(s_e)) = \pi_U(a_{\gamma, U}(e)) = \gamma_T \circ x = \mathrm{pr}_2 \circ \Psi_{x, \gamma} = H(\Psi_{x, \gamma})(\mathrm{pr}_2)$，故 $\pi_{\widetilde{U}_g}(s_e) = \mathrm{pr}_2$；
     - 对任意 $\delta, \gamma \in \Gamma$，因 $\delta_{\widetilde{U}_g} \circ \Psi_{x, \gamma} = \Psi_{x, \delta\gamma}$，有
       $$E(\Psi_{x, \gamma})\bigl(E(\delta_{\widetilde{U}_g})(s_e)\bigr) = E(\Psi_{x, \delta\gamma})(s_e) = a_{\delta\gamma, U}(e) = a_{\delta, U}(a_{\gamma, U}(e)) = E(\Psi_{x, \gamma})\bigl(a_{\delta, \widetilde{U}_g}(s_e)\bigr),$$
       由 $E(\Psi_x)$ 为双射得 $E(\delta_{\widetilde{U}_g})(s_e) = a_{\delta, \widetilde{U}_g}(s_e)$。故 $\Theta_U(e) := (x, (g, s_e)) \in H(U) \times_{Q(U)} D(U)$。
   - **互逆验证**：注意到 $\sigma_x = \Psi_{x, 1_\Gamma}$，故 $\Phi_U(\Theta_U(e)) = E(\Psi_{x, 1_\Gamma})(s_e) = a_{1_\Gamma, U}(e) = e$；反之，对 $(x, (g, s)) \in H(U) \times_{Q(U)} D(U)$，令 $e := E(\sigma_x)(s)$，则 $\pi_U(e) = x$，且对任意 $\gamma \in \Gamma$，因 $\Psi_{x, \gamma} = \gamma_{\widetilde{U}_g} \circ \sigma_x$，有
     $$E(\Psi_{x, \gamma})(s) = E(\sigma_x)\bigl(E(\gamma_{\widetilde{U}_g})(s)\bigr) = E(\sigma_x)\bigl(a_{\gamma, \widetilde{U}_g}(s)\bigr) = a_{\gamma, U}\bigl(E(\sigma_x)(s)\bigr) = a_{\gamma, U}(e) = E(\Psi_{x, \gamma})(s_e),$$
     从而 $s = s_e$，即 $\Theta_U(\Phi_U(x, (g, s))) = (x, (g, s))$。

因此 $\Theta = \Phi^{-1} : E \xrightarrow{\sim} H \times_Q D$ 是 $\mathrm{Equiv}_\Gamma(H)$ 中的同构，$E$ 在 $Q = h_{T/\Gamma}$ 上实现。

---

## S2　有限集合上的纤维分类

本阶段设 $\Gamma$ 和 $T$ 均有限，$X$ 为有限 $\Gamma$-集合，$f : X \to T$ 为 $\Gamma$-等变映射。因有限 Hausdorff 空间必离散（且由 $\mathbb{N} \in \mathcal{U}$ 知有限集均 $\mathcal{U}$-小），赋予 $T, X, T/\Gamma$ 离散拓扑后它们均属于 $\mathbf{Prof}_{\mathcal{U}}$，任何集合映射自动连续。记所选 $T/\Gamma$ 的一套轨道代表元集为 $\mathcal{R} \subseteq T$（每个 $T$-轨道恰含唯一 $t \in \mathcal{R}$；若 $T = \varnothing$ 则 $\mathcal{R} = \varnothing$），对 $t \in \mathcal{R}$ 记稳定子 $\Gamma_t := \{\gamma \in \Gamma : \gamma t = t\} \le \Gamma$。

### 1. 有限等变映射 $X \to T$ 及其等变态射的分类

记 $T$ 上有限 $\Gamma$-集合及 $T$ 上 $\Gamma$-等变映射构成的范畴为 $\Gamma\text{-}\mathbf{FinSet}_{/T}$，记各有限 $\Gamma_t$-集合范畴的积范畴为 $\prod_{t \in \mathcal{R}} (\Gamma_t\text{-}\mathbf{FinSet})$。构造一对函子：

- **取纤维函子 $\Phi : \Gamma\text{-}\mathbf{FinSet}_{/T} \to \prod_{t \in \mathcal{R}} (\Gamma_t\text{-}\mathbf{FinSet})$**：
  对 $(X, f)$ 及 $t \in \mathcal{R}$，令 $X_t := f^{-1}(\{t\}) \subseteq X$。因 $X$ 有限，$X_t$ 有限；对 $\sigma \in \Gamma_t$ 及 $x \in X_t$，$f(\sigma x) = \sigma f(x) = \sigma t = t$，故 $X_t$ 为有限 $\Gamma_t$-集合。对态射 $\varphi : (X, f) \to (X', f')$（满足 $f' \circ \varphi = f$ 且 $\Gamma$-等变），限制映射 $\varphi_t := \varphi|_{X_t} : X_t \to X'_t$ 是 $\Gamma_t$-等变映射。令 $\Phi(X, f) := (X_t)_{t \in \mathcal{R}}$，$\Phi(\varphi) := (\varphi_t)_{t \in \mathcal{R}}$。

- **平衡积（诱导）函子 $\Psi : \prod_{t \in \mathcal{R}} (\Gamma_t\text{-}\mathbf{FinSet}) \to \Gamma\text{-}\mathbf{FinSet}_{/T}$**：
  对对象族 $(F_t)_{t \in \mathcal{R}}$，令 $\Gamma \times^{\Gamma_t} F_t := (\Gamma \times F_t)/\!\sim$，其中等价关系定义为 $(\gamma \sigma, z) \sim (\gamma, \sigma z)$（$\forall \gamma \in \Gamma,\, \sigma \in \Gamma_t,\, z \in F_t$；易见此为等价关系），记等价类为 $[\gamma, z]_t$。令
  $$\Psi\bigl((F_t)_{t \in \mathcal{R}}\bigr) := \coprod_{t \in \mathcal{R}} \bigl(\Gamma \times^{\Gamma_t} F_t\bigr),$$
  其上左 $\Gamma$-作用定义为 $\delta \cdot [\gamma, z]_t := [\delta\gamma, z]_t$，到 $T$ 的投影定义为 $f([\gamma, z]_t) := \gamma t$。
  - **良定义与有限性**：若 $(\gamma \sigma, z) \sim (\gamma, \sigma z)$（$\sigma \in \Gamma_t$），则 $[\delta(\gamma\sigma), z]_t = [(\delta\gamma)\sigma, z]_t = [\delta\gamma, \sigma z]_t$ 且 $(\gamma\sigma)t = \gamma(\sigma t) = \gamma t$；又 $f(\delta \cdot [\gamma, z]_t) = (\delta\gamma)t = \delta f([\gamma, z]_t)$，且因 $\mathcal{R}, \Gamma, F_t$ 均有限，$\Psi((F_t))$ 是有限集。
  - 对态射族 $(\alpha_t : F_t \to F'_t)_{t \in \mathcal{R}}$，令 $\Psi((\alpha_t))([\gamma, z]_t) := [\gamma, \alpha_t(z)]_t$（由 $\alpha_t$ 的 $\Gamma_t$-等变性知良定义，且显然保持 $f$ 并 $\Gamma$-等变）。

- **范畴等价验证**：
  - **单位自然同构 $\eta : \mathrm{Id} \xrightarrow{\sim} \Phi \circ \Psi$**：对 $(F_t)_{t \in \mathcal{R}}$ 及固定 $t \in \mathcal{R}$，元素 $[\gamma, z]_{t'} \in \Psi((F_\bullet))$ 落在 $t$ 的纤维上当且仅当 $\gamma t' = t$；因 $\mathcal{R}$ 中不同代表元属于不同轨道，这等价于 $t' = t$ 且 $\gamma \in \Gamma_t$，此时 $[\gamma, z]_t = [1, \gamma z]_t$。故映射 $z \mapsto [1, z]_t$ 给出 $F_t \xrightarrow{\sim} \Phi(\Psi((F_\bullet)))_t$ 的双射（逆为 $[\sigma, z]_t \mapsto \sigma z$，$\sigma \in \Gamma_t$），且对 $\tau \in \Gamma_t$ 有 $\tau \cdot [1, z]_t = [\tau, z]_t = [1, \tau z]_t$，即为自然 $\Gamma_t$-同构。
  - **余单位自然同构 $\varepsilon : \Psi \circ \Phi \xrightarrow{\sim} \mathrm{Id}$**：对 $(X, f)$，定义 $\varepsilon_{(X,f)} : \coprod_{t \in \mathcal{R}} (\Gamma \times^{\Gamma_t} X_t) \to X$ 为 $[\gamma, x]_t \mapsto \gamma x$。若 $\sigma \in \Gamma_t$，则 $(\gamma\sigma)x = \gamma(\sigma x)$，故良定义；显然保持到 $T$ 的映射且 $\Gamma$-等变。
    - 满射性：对任意 $y \in X$，$f(y) \in T$ 落在唯一 $t \in \mathcal{R}$ 的轨道中，取 $\gamma \in \Gamma$ 使 $f(y) = \gamma t$，则 $x := \gamma^{-1}y \in X_t$ 且 $\varepsilon([\gamma, x]_t) = y$；
    - 单射性：若 $\gamma_1 x_1 = \gamma_2 x_2$（$x_i \in X_{t_i}$），作用 $f$ 得 $\gamma_1 t_1 = \gamma_2 t_2 \implies t_1 = t_2 =: t$ 且 $\sigma := \gamma_1^{-1}\gamma_2 \in \Gamma_t$，从而 $x_1 = \sigma x_2$，于是 $[\gamma_2, x_2]_t = [\gamma_1\sigma, x_2]_t = [\gamma_1, \sigma x_2]_t = [\gamma_1, x_1]_t$。

**分类结论**：范畴等价 $\Phi : \Gamma\text{-}\mathbf{FinSet}_{/T} \xrightarrow{\simeq} \prod_{t \in \mathcal{R}} (\Gamma_t\text{-}\mathbf{FinSet})$ 表明：
1. 有限等变对象 $X \to T$ 的同构类与有限 $\Gamma_t$-集合族 $(F_t)_{t \in \mathcal{R}}$ 的同构类族一一对应（显式还原为 $X \cong \coprod_{t \in \mathcal{R}} \Gamma \times^{\Gamma_t} F_t$）；
2. 对任意两个对象 $(X, f), (X', f')$，其等变态射集（以及由米田嵌入忠实满性诱导的 $\mathrm{Equiv}_\Gamma(H)$ 中态射集）自然双射于各代表纤维上的 $\Gamma_t$-等变映射集之积：
   $$\mathrm{Hom}_{\mathrm{Equiv}_\Gamma(H)}(h_X, h_{X'}) \cong \mathrm{Hom}_{\Gamma\text{-}\mathbf{FinSet}_{/T}}(X, X') \xrightarrow{\;\sim\;} \prod_{t \in \mathcal{R}} \mathrm{Hom}_{\Gamma_t}(X_t, X'_t), \qquad \varphi \longmapsto (\varphi|_{X_t})_{t \in \mathcal{R}}.$$

### 2. $h_X$ 在 $Q = h_{T/\Gamma}$ 上实现的充要条件

设 $p : T \to T/\Gamma$ 为轨道投影，$Q = h_{T/\Gamma}$，$q = h_p : H \to Q$。我们证明以下四条等价（其中 (2)、(3) 即为按稳定子给出的充要条件）：
1. $h_X$ 在 $Q = h_{T/\Gamma}$ 上可实现（存在层 $D \xrightarrow{d} Q$ 及 $\mathrm{Equiv}_\Gamma(H)$ 中的同构 $\varphi : h_X \xrightarrow{\sim} H \times_Q D$）；
2. 对每个轨道代表 $t \in \mathcal{R}$，稳定子群 $\Gamma_t$ 在纤维 $X_t = f^{-1}(\{t\})$ 上**作用平凡**（即 $\forall t \in \mathcal{R},\, \forall \sigma \in \Gamma_t,\, \forall x \in X_t,\; \sigma x = x$）；
3. 对每个 $x \in X$，稳定子满足 $\Gamma_x = \Gamma_{f(x)}$（因等变性恒有 $\Gamma_x \subseteq \Gamma_{f(x)}$，这等价于 $\Gamma_{f(x)} \subseteq \Gamma_x$）；
4. 诱导映射 $\theta = (f, p_X) : X \to T \times_{T/\Gamma} (X/\Gamma)$，$x \mapsto (f(x), \Gamma x)$ 是双射（其中 $p_X : X \to X/\Gamma$ 为轨道映射，$X/\Gamma \to T/\Gamma$ 由 $\Gamma x \mapsto \Gamma f(x)$ 给出）。

**证明**：
- **(1) $\implies$ (3)**：设 $\varphi : h_X \xrightarrow{\sim} H \times_Q D$ 是 $\mathrm{Equiv}_\Gamma(H)$ 中的同构。在单点空间 $* \in \mathbf{Prof}_{\mathcal{U}}$ 上取值，利用 $h_X(*) \cong X$ 与 $H(*) \cong T$，得双射 $\varphi_* : X \xrightarrow{\sim} T \times_{Q(*)} D(*)$，形如 $\varphi_*(x) = (f(x), y_x)$（$y_x \in D(*)$），且由等变性有 $\varphi_*(\gamma x) = (\gamma f(x), y_x)$。若 $\gamma \in \Gamma_{f(x)}$，即 $\gamma f(x) = f(x)$，则 $\varphi_*(\gamma x) = (f(x), y_x) = \varphi_*(x)$，由 $\varphi_*$ 单射得 $\gamma x = x$，即 $\gamma \in \Gamma_x$。故 $\Gamma_{f(x)} = \Gamma_x$。
- **(3) $\iff$ (2)**：任意 $x \in X$ 均可写成 $x = \gamma x_0$，其中 $t \in \mathcal{R}$，$x_0 \in X_t$，$\gamma \in \Gamma$。因 $\Gamma_{f(\gamma x_0)} = \Gamma_{\gamma t} = \gamma \Gamma_t \gamma^{-1}$ 且 $\Gamma_{\gamma x_0} = \gamma \Gamma_{x_0} \gamma^{-1}$，故 $\forall x \in X,\, \Gamma_{f(x)} = \Gamma_x$ 当且仅当 $\forall t \in \mathcal{R},\, \forall x_0 \in X_t,\, \Gamma_t = \Gamma_{x_0}$，即每个 $\Gamma_t$ 在 $X_t$ 上作用平凡。
- **(3) $\implies$ (4)**：假设 $\forall x \in X,\, \Gamma_{f(x)} \subseteq \Gamma_x$。显然 $\theta(x) = (f(x), \Gamma x)$ 良定义、保持第一投影 $f$ 且对第二因子平凡的 $\Gamma$-作用等变。
  - 满射性：对任意 $(t', \Gamma x) \in T \times_{T/\Gamma} (X/\Gamma)$，有 $\Gamma t' = \Gamma f(x)$，故存在 $\gamma \in \Gamma$ 使 $t' = \gamma f(x) = f(\gamma x)$，于是 $\theta(\gamma x) = (t', \Gamma x)$；
  - 单射性：若 $\theta(x_1) = \theta(x_2)$，则 $f(x_1) = f(x_2)$ 且 $\Gamma x_1 = \Gamma x_2$，取 $\gamma \in \Gamma$ 使 $x_2 = \gamma x_1$，则 $f(x_1) = f(x_2) = \gamma f(x_1) \implies \gamma \in \Gamma_{f(x_1)} \subseteq \Gamma_{x_1} \implies x_2 = \gamma x_1 = x_1$。
- **(4) $\implies$ (1)**：有限离散集之间的双射 $\theta$ 是 $\mathbf{Prof}_{\mathcal{U}}$ 中的同构。因米田嵌入 $h_{(-)}$ 保持纤维积，取 $D := h_{X/\Gamma} \to h_{T/\Gamma} = Q$，则 $h_\theta : h_X \xrightarrow{\sim} h_{T \times_{T/\Gamma} (X/\Gamma)} \cong H \times_Q h_{X/\Gamma}$ 即为 $\mathrm{Equiv}_\Gamma(H)$ 中的同构。

### 3. 可实现对象的自同构群计算

设 $(X, f)$ 满足上述充要条件（即可实现）。由米田嵌入 $h_{(-)} : \mathbf{Prof}_{\mathcal{U}} \to \mathcal{C}$ 的忠实满性及第 1 步的态射分类，有群同构
$$\mathrm{Aut}_{\mathrm{Equiv}_\Gamma(H)}(h_X) \cong \mathrm{Aut}_{\Gamma\text{-}\mathbf{FinSet}_{/T}}(X) \xrightarrow{\;\sim\;} \prod_{t \in \mathcal{R}} \mathrm{Aut}_{\Gamma_t}(X_t).$$
由于 $h_X$ 可实现，由条件 (2) 知对每个 $t \in \mathcal{R}$，$\Gamma_t$ 在有限集 $X_t$ 上作用平凡，从而 $X_t$ 的**任意**自双射都自动 $\Gamma_t$-等变，即 $\mathrm{Aut}_{\Gamma_t}(X_t) = \mathrm{Sym}(X_t)$（$X_t$ 上的全对称群，阶为 $|X_t|!$）。因此可实现对象的自同构群为
$$\mathrm{Aut}_{\mathrm{Equiv}_\Gamma(H)}(h_X) \cong \mathrm{Aut}_{\Gamma\text{-}\mathbf{FinSet}_{/T}}(X) \cong \prod_{t \in \mathcal{R}} \mathrm{Sym}(X_t) \cong \prod_{t \in \mathcal{R}} S_{|X_t|}.$$

---

## S3　一般层的完整下降

本阶段**只使用共同设定**（$\Gamma$ 为任意 $\mathcal{U}$-小离散群，$T \in \mathbf{Prof}_{\mathcal{U}}$ 任意）。

### 1. 预层层化引理与层商 $Q$ 的构造

**引理 3.1（$\mathbf{Prof}_{\mathcal{U}}$ 上 $\mathrm{Set}_{\mathcal{V}}$-值预层的显式层化）**：对任意预层 $P : \mathbf{Prof}_{\mathcal{U}}^{\mathrm{op}} \to \mathrm{Set}_{\mathcal{V}}$，存在层 $a(P) \in \mathcal{C}$ 及预层态射 $\iota_P : P \to a(P)$ 满足：
- **(泛性质)** 对任意层 $Y \in \mathcal{C}$，前复合 $\iota_P^* : \mathrm{Hom}_{\mathcal{C}}(a(P), Y) \xrightarrow{\sim} \mathrm{Hom}_{\mathrm{PSh}}(P, Y)$ 为自然双射；
- **(局部满射与局部相等刻画)** 对任意 $U \in \mathbf{Prof}_{\mathcal{U}}$：每个 $\xi \in a(P)(U)$ 在某覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 上形如 $\xi|_{U_i} = \iota_{P, U_i}(s_i)$（$s_i \in P(U_i)$）；且两个元素 $s_1, s_2 \in P(U)$ 满足 $\iota_{P, U}(s_1) = \iota_{P, U}(s_2)$ 当且仅当存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 使 $\forall i \in I,\, P(u_i)(s_1) = P(u_i)(s_2)$。

*证明*：分两步构造。
1. **分离化 $P_{\mathrm{sep}}$**：在 $P(U)$ 上定义关系 $s_1 \sim_U s_2 \iff$ 存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 使 $\forall i \in I,\, P(u_i)(s_1) = P(u_i)(s_2)$。由恒等覆盖及覆盖的拉回稳定性（两覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 与 $\{v_j : V_j \to U\}_{j \in J}$ 有公共加细 $\{U_i \times_U V_j \to U\}_{(i,j) \in I \times J}$）知 $\sim_U$ 是与限制映射相容的等价关系。令 $P_{\mathrm{sep}}(U) := P(U)/\!\sim_U \in \mathrm{Set}_{\mathcal{V}}$。则 $P_{\mathrm{sep}}$ 是**分离预层**：若 $[s_1], [s_2] \in P_{\mathrm{sep}}(U)$ 在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 上相等，则对每个 $i$ 存在覆盖 $\{v_{i,j} : V_{i,j} \to U_i\}_{j \in J_i}$ 使 $s_1, s_2$ 在 $P(V_{i,j})$ 中相等；复合覆盖 $\{u_i \circ v_{i,j}\}_{i \in I, j \in J_i}$ 仍为有限联合满射族，故 $[s_1] = [s_2]$。
2. **加号构造 $a(P) := (P_{\mathrm{sep}})^+$**：记 $\mathbf{Prof}_{\mathcal{U}}^{\mathrm{small}}$ 为底集属于 $\mathcal{U}$ 的 profinite 空间全子范畴。如预备核验所述，$\mathbf{Prof}_{\mathcal{U}}$ 中任一有限覆盖均同构于每个成员选自 $\mathbf{Prof}_{\mathcal{U}}^{\mathrm{small}}$（指标集形如 $\{0, \dots, n-1\}$）的覆盖，且 $U$ 的此类小覆盖全体构成集合 $\mathrm{Cov}_{\mathcal{U}}(U) \in \mathcal{V}$。定义 $(P_{\mathrm{sep}})^+(U)$ 为 $\mathrm{Cov}_{\mathcal{U}}(U)$ 中覆盖 $\mathcal{U}_0 = \{u_i : U_i \to U\}_{i \in I}$ 上 $P_{\mathrm{sep}}$ 的相容族 $\bigl(\{[s_i] \in P_{\mathrm{sep}}(U_i)\}_{i \in I}\bigr)$ 模公共加细等价所得的商集；因 $\mathrm{Cov}_{\mathcal{U}}(U) \in \mathcal{V}$ 且各 $P_{\mathrm{sep}}(U_i) \in \mathcal{V}$，有 $a(P)(U) \in \mathrm{Set}_{\mathcal{V}}$（特别地，对 $U = \varnothing$，空覆盖 $I = \varnothing$ 上的唯一空族给出 $a(P)(\varnothing) \cong \{*\}$）。定义 $\iota_{P, U}(s)$ 为恒等覆盖 $\{\mathrm{id}_U\}$ 上的单元素族 $\{[s]\}$。
   - **单射性 $P_{\mathrm{sep}}(U) \hookrightarrow a(P)(U)$**：若 $\{[s_1]\}$ 与 $\{[s_2]\}$ 在某覆盖上相等，由 $P_{\mathrm{sep}}$ 分离性立得 $[s_1] = [s_2]$，这同时证得引理中的局部相等刻画；而 $a(P)(U)$ 的定义直接给出局部满射性。
   - **层公理**：设 $\{\xi_i \in a(P)(U_i)\}_{i \in I}$ 是覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 上的相容族（若两截面 $\xi, \xi' \in a(P)(U)$ 在 $\{u_i\}$ 上限制相等，取公共代表覆盖并在其与 $U_i$ 的纤维积上用 $P_{\mathrm{sep}}$ 的分离性即知 $\xi = \xi'$，故 $a(P)$ 分离）。对每个 $i$ 取代表覆盖 $\{v_{i,j} : V_{i,j} \to U_i\}_{j \in J_i}$（可设 $V_{i,j} \in \mathbf{Prof}_{\mathcal{U}}^{\mathrm{small}}$）上的相容族 $\{[s_{i,j}] \in P_{\mathrm{sep}}(V_{i,j})\}$。因 $\xi_i$ 与 $\xi_{i'}$ 在 $U_i \times_U U_{i'}$ 上相等，且 $P_{\mathrm{sep}} \hookrightarrow a(P)$ 逐对象单射，$[s_{i,j}]$ 与 $[s_{i', j'}]$ 在 $V_{i,j} \times_U V_{i', j'}$ 上已经在 $P_{\mathrm{sep}}$ 中直接相等，从而 $\{[s_{i,j}]\}_{i \in I, j \in J_i}$ 在复合覆盖 $\{u_i \circ v_{i,j}\}$ 上构成相容族，给出粘合元 $\xi \in a(P)(U)$。
   - **泛性质**：给定层 $Y \in \mathcal{C}$ 及预层态射 $\alpha : P \to Y$，因 $Y$ 分离，$\alpha$ 唯一分解过 $P_{\mathrm{sep}} \to Y$；又因 $Y$ 满足覆盖粘合，每个代表相容族 $\{[s_i] \in P_{\mathrm{sep}}(U_i)\}$ 的像 $\{\bar{\alpha}_{U_i}([s_i]) \in Y(U_i)\}$ 在 $Y(U)$ 中唯一粘合且与加细选择无关，给出唯一的层态射 $\tilde{\alpha} : a(P) \to Y$ 使 $\tilde{\alpha} \circ \iota_P = \alpha$。 $\square$

**层 $Q$ 与 $q : H \to Q$ 的构造**：
一般地，对 $\mathcal{C}$ 中任一带左 $\Gamma$-作用 $a = \{a_\gamma\}_{\gamma \in \Gamma}$ 的层 $F$，定义轨道预层 $P_F(U) := F(U)/\Gamma$（限制映射由 $\Gamma$-作用与预层限制交换良定义；因 $F(U) \in \mathrm{Set}_{\mathcal{V}}$，商集 $P_F(U) \in \mathrm{Set}_{\mathcal{V}}$），记其层化为 $F/\Gamma := a(P_F) \in \mathcal{C}$，记复合态射 $q_F : F \twoheadrightarrow P_F \xrightarrow{\iota_{P_F}} F/\Gamma$。
特别取 $F = H$，令
$$Q := H/\Gamma = a(P_H) \in \mathcal{C}, \qquad q := q_H : H \longrightarrow Q.$$
核验所需性质：
1. **$\Gamma$-不变性**：对任意 $U$、$x \in H(U)$ 及 $\gamma \in \Gamma$，$x$ 与 $h_{\gamma, U}(x)$ 在轨道商 $P_H(U) = H(U)/\Gamma$ 中同属一类，故 $q \circ h_\gamma = q$。
2. **泛性质**：对任意层 $Y \in \mathcal{C}$，由引理 3.1 的泛性质及商集泛性质，有自然双射链
   $$\mathrm{Hom}_{\mathcal{C}}(Q, Y) \xrightarrow[\sim]{\iota_{P_H}^*} \mathrm{Hom}_{\mathrm{PSh}}(P_H, Y) \xrightarrow{\;\sim\;} \{\beta \in \mathrm{Hom}_{\mathrm{PSh}}(H, Y) : \forall \gamma \in \Gamma,\, \beta \circ h_\gamma = \beta\} = \mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma,$$
   其复合恰为 $q^* : \alpha \mapsto \alpha \circ q$。
3. **商态射 $q_F : F \to F/\Gamma$ 的两条基本性质**（对任意 $\Gamma$-层 $F$ 成立，下文对 $F = H$ 及 $F = E$ 使用）：
   - **(Q-满)** $q_F : F \to F/\Gamma$ **局部满射**：由引理 3.1，$F/\Gamma(U)$ 中任一截面局部来自 $P_F(U_i) = F(U_i)/\Gamma$，取轨道代表即得 $F(U_i)$ 中的提升。
   - **(Q-核)** 对任意 $z_1, z_2 \in F(U)$，$q_{F, U}(z_1) = q_{F, U}(z_2)$ 当且仅当存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及元素族 $\{\gamma_i \in \Gamma\}_{i \in I}$ 使得对每个 $i \in I$ 有 $z_2|_{U_i} = a_{\gamma_i, U_i}(z_1|_{U_i})$（直接对 $P_F(U) = F(U)/\Gamma$ 应用引理 3.1 的局部相等刻画）。

---

### 2. 不预选 $D$ 的可实现性充要判据

对任意等变对象 $(E, \pi, a) \in \mathrm{Equiv}_\Gamma(H)$，复合态射 $q \circ \pi : E \to Q$ 满足 $(q \circ \pi) \circ a_\gamma = q \circ h_\gamma \circ \pi = q \circ \pi$（$\Gamma$-不变），故由 $E/\Gamma$ 的泛性质诱导唯一层态射 $\bar{\pi} : E/\Gamma \to Q$ 使 $\bar{\pi} \circ q_E = q \circ \pi$，进而给出 $\mathrm{Equiv}_\Gamma(H)$ 中的典范态射
$$\eta_E := (\pi, q_E) : E \longrightarrow H \times_Q (E/\Gamma), \qquad e \longmapsto \bigl(\pi_U(e),\, q_{E, U}(e)\bigr).$$

**定理 3.2（不预选 $D$ 的可实现性充要判据）**：等变对象 $(E, \pi, a) \in \mathrm{Equiv}_\Gamma(H)$ 在 $Q$ 上可实现，当且仅当以下不依赖任何预选 $D$ 的稳定子判据 **(C1)** 成立（亦等价于典范态射判据 **(C2)**）：
- **(C1) 截面稳定子判据**：对每个测试对象 $U \in \mathbf{Prof}_{\mathcal{U}}$、每个截面 $e \in E(U)$ 及每个 $\gamma \in \Gamma$，
  $$h_{\gamma, U}\bigl(\pi_U(e)\bigr) = \pi_U(e) \implies a_{\gamma, U}(e) = e.$$
- **(C2) 典范商纤维积判据**：典范态射 $\eta_E : E \to H \times_Q (E/\Gamma)$ 是层同构（等价地，逐对象单射）。

*证明*：证 **（可实现）$\implies$ (C1) $\implies$ (C2) $\implies$（可实现）**。
1. **（可实现）$\implies$ (C1)**：设存在 $(D \xrightarrow{d} Q) \in \mathcal{C}_{/Q}$ 及 $\mathrm{Equiv}_\Gamma(H)$ 中的同构 $\varphi : E \xrightarrow{\sim} H \times_Q D$。对任意 $U \in \mathbf{Prof}_{\mathcal{U}}$、$e \in E(U)$ 及 $\gamma \in \Gamma$，因 $\varphi$ 在 $H$ 上，可写 $\varphi_U(e) = (\pi_U(e), y)$（$y \in D(U)$）。由等变性知 $\varphi_U(a_{\gamma, U}(e)) = (h_{\gamma, U}(\pi_U(e)),\, y)$。若 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$，则 $\varphi_U(a_{\gamma, U}(e)) = (\pi_U(e), y) = \varphi_U(e)$；因 $\varphi_U$ 是双射，故 $a_{\gamma, U}(e) = e$。
2. **先证对任意 $(E, \pi, a)$，$\eta_E : E \to H \times_Q (E/\Gamma)$ 恒为局部满射**：
   任取 $U \in \mathbf{Prof}_{\mathcal{U}}$ 及截面 $(x, \xi) \in H(U) \times_{Q(U)} (E/\Gamma)(U)$，即 $q_U(x) = \bar{\pi}_U(\xi)$。由性质 (Q-满) 对 $q_E : E \to E/\Gamma$，存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及 $e_i \in E(U_i)$ 使 $q_{E, U_i}(e_i) = \xi|_{U_i}$。于是
   $$q_{U_i}\bigl(\pi_{U_i}(e_i)\bigr) = \bar{\pi}_{U_i}\bigl(q_{E, U_i}(e_i)\bigr) = \bar{\pi}_{U_i}(\xi|_{U_i}) = q_U(x)|_{U_i} = q_{U_i}(x|_{U_i}).$$
   对每个 $i \in I$ 应用 $q : H \to Q$ 的性质 (Q-核)，存在覆盖 $\{v_{i,j} : V_{i,j} \to U_i\}_{j \in J_i}$ 及 $\gamma_{i,j} \in \Gamma$ 使 $x|_{V_{i,j}} = h_{\gamma_{i,j}, V_{i,j}}(\pi_{U_i}(e_i)|_{V_{i,j}})$。令 $e'_{i,j} := a_{\gamma_{i,j}, V_{i,j}}(e_i|_{V_{i,j}}) \in E(V_{i,j})$，则
   $$\pi_{V_{i,j}}(e'_{i,j}) = h_{\gamma_{i,j}, V_{i,j}}\bigl(\pi_{V_{i,j}}(e_i|_{V_{i,j}})\bigr) = x|_{V_{i,j}}, \qquad q_{E, V_{i,j}}(e'_{i,j}) = q_{E, V_{i,j}}(e_i|_{V_{i,j}}) = \xi|_{V_{i,j}},$$
   即 $\eta_{E, V_{i,j}}(e'_{i,j}) = (x, \xi)|_{V_{i,j}}$ 在复合有限覆盖 $\{u_i \circ v_{i,j}\}$ 上提升 $(x, \xi)$。
3. **(C1) $\implies$ (C2)**：设 (C1) 成立。只需证对每个 $U \in \mathbf{Prof}_{\mathcal{U}}$，$\eta_{E, U}$ 单射（局部满射且逐对象单射的层态射必逐对象满射：局部提升在交上由单射性必相容，由层公理粘合为整体原像）。设 $e_1, e_2 \in E(U)$ 满足 $\eta_{E, U}(e_1) = \eta_{E, U}(e_2)$，即 $\pi_U(e_1) = \pi_U(e_2)$ 且 $q_{E, U}(e_1) = q_{E, U}(e_2)$。由 $q_E$ 的性质 (Q-核)，存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及 $\gamma_i \in \Gamma$ 使 $e_2|_{U_i} = a_{\gamma_i, U_i}(e_1|_{U_i})$。两边作用 $\pi_{U_i}$ 并用 $\pi_U(e_1) = \pi_U(e_2)$ 得
   $$\pi_{U_i}(e_1|_{U_i}) = \pi_{U_i}(e_2|_{U_i}) = \pi_{U_i}\bigl(a_{\gamma_i, U_i}(e_1|_{U_i})\bigr) = h_{\gamma_i, U_i}\bigl(\pi_{U_i}(e_1|_{U_i})\bigr).$$
   在测试对象 $U_i$ 上对 $e_1|_{U_i} \in E(U_i)$ 与 $\gamma_i \in \Gamma$ 应用 (C1)，得 $a_{\gamma_i, U_i}(e_1|_{U_i}) = e_1|_{U_i}$，从而对一切 $i \in I$ 有 $e_2|_{U_i} = e_1|_{U_i}$。由层 $E$ 的分离性得 $e_1 = e_2$。故 $\eta_E$ 为层同构。
4. **(C2) $\implies$（可实现）**：因 $q_E \circ a_\gamma = q_E$，$\eta_E : E \to H \times_Q (E/\Gamma)$ 是 $\mathrm{Equiv}_\Gamma(H)$ 中的态射；当 $\eta_E$ 为同构时，取 $(D \to Q) := (E/\Gamma \xrightarrow{\bar{\pi}} Q)$ 即给出 $E$ 在 $Q$ 上的实现。 $\square$

---

### 3. 所有实现及态射的分类

先建立拉回后商性质的关键引理（此引理同时为第 4 步任意基底 $B \to Q$ 的分类奠基）：

**引理 3.3（商性质的基底拉回保持性）**：设 $(B \xrightarrow{b} Q) \in \mathcal{C}_{/Q}$，令 $H_B := H \times_Q B$，带第二投影 $q_B := \mathrm{pr}_2 : H_B \to B$ 及左 $\Gamma$-作用 $h_{B, \gamma} := h_\gamma \times_Q \mathrm{id}_B$。则：
1. $q_B : H_B \to B$ 满足性质 **(Q-满)** 与 **(Q-核)**；
2. 对任意层 $Y \in \mathcal{C}$，前复合 $q_B^* : \mathrm{Hom}_{\mathcal{C}}(B, Y) \xrightarrow{\sim} \mathrm{Hom}_{\mathcal{C}}(H_B, Y)^\Gamma$ 为自然双射（即 $B \cong H_B / \Gamma$）。

*证明*：
1. **(Q-满)**：对任意 $U \in \mathbf{Prof}_{\mathcal{U}}$ 及 $y \in B(U)$，因 $q : H \to Q$ 局部满射，存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及 $x_i \in H(U_i)$ 使 $q_{U_i}(x_i) = b_U(y)|_{U_i} = b_{U_i}(y|_{U_i})$，从而 $(x_i, y|_{U_i}) \in H_B(U_i)$ 满足 $q_{B, U_i}(x_i, y|_{U_i}) = y|_{U_i}$。
   **(Q-核)**：若 $(x_1, y_1), (x_2, y_2) \in H_B(U)$ 满足 $q_{B, U}(x_1, y_1) = q_{B, U}(x_2, y_2)$，则 $y_1 = y_2$ 且 $q_U(x_1) = b_U(y_1) = b_U(y_2) = q_U(x_2)$；由 $q$ 的 (Q-核) 知存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及 $\gamma_i \in \Gamma$ 使 $x_2|_{U_i} = h_{\gamma_i, U_i}(x_1|_{U_i})$，故 $(x_2, y_2)|_{U_i} = h_{B, \gamma_i, U_i}((x_1, y_1)|_{U_i})$。反之显然。
2. 设 $\phi \in \mathrm{Hom}_{\mathcal{C}}(H_B, Y)^\Gamma$（即 $\forall \gamma \in \Gamma,\, \phi \circ h_{B, \gamma} = \phi$）。对任意 $U \in \mathbf{Prof}_{\mathcal{U}}$ 及 $y \in B(U)$，由 (1) 的局部满射性取覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及 $(x_i, y|_{U_i}) \in H_B(U_i)$，令 $z_i := \phi_{U_i}(x_i, y|_{U_i}) \in Y(U_i)$。在重叠 $V = U_i \times_U U_j$ 上，$q_{B, V}(x_i|_V, y|_V) = y|_V = q_{B, V}(x_j|_V, y|_V)$，由 (1) 的 (Q-核) 存在覆盖 $\{w_k : W_k \to V\}_{k \in K}$ 及 $\gamma_k \in \Gamma$ 使 $(x_j, y)|_{W_k} = h_{B, \gamma_k, W_k}((x_i, y)|_{W_k})$；利用 $\phi$ 的 $\Gamma$-不变性得 $z_j|_{W_k} = z_i|_{W_k}$，由层 $Y$ 的分离性知 $z_i|_V = z_j|_V$。再由层 $Y$ 的粘合性，$\{z_i\}$ 唯一粘合为 $f_U(y) \in Y(U)$（同样重叠论证知 $f_U(y)$ 与覆盖及提升选取无关，从而对 $U$ 自然），且唯一满足 $f \circ q_B = \phi$。 $\square$

由此立即得到所有实现及态射的完整分类：

**定理 3.4（可实现对象、实现及态射的分类）**：记 $\mathrm{Real}_Q(H) \subseteq \mathrm{Equiv}_\Gamma(H)$ 为在 $Q$ 上可实现的等变对象构成的全子范畴。
1. **实现函子的忠实满性与范畴等价（分类可实现对象及全部等变态射）**：
   函子 $q^*_{\mathrm{eq}} : \mathcal{C}_{/Q} \to \mathrm{Equiv}_\Gamma(H)$ 是**忠实满**的：对任意 $(D_1 \xrightarrow{d_1} Q), (D_2 \xrightarrow{d_2} Q) \in \mathcal{C}_{/Q}$，映射
   $$q^*_{\mathrm{eq}} : \mathrm{Hom}_{\mathcal{C}_{/Q}}(D_1, D_2) \xrightarrow{\;\sim\;} \mathrm{Hom}_{\mathrm{Equiv}_\Gamma(H)}(H \times_Q D_1,\, H \times_Q D_2), \qquad f \longmapsto \mathrm{id}_H \times_Q f$$
   是双射。从而 $q^*_{\mathrm{eq}}$ 给出范畴等价 $\mathcal{C}_{/Q} \xrightarrow{\simeq} \mathrm{Real}_Q(H)$，其拟逆为商函子 $\mathbf{q}_{!} : (E, \pi, a) \mapsto (E/\Gamma \xrightarrow{\bar{\pi}} Q)$。特别地，可实现对象 $E_1, E_2 \in \mathrm{Real}_Q(H)$ 之间的等变态射集自然双射于 $\mathrm{Hom}_{\mathcal{C}_{/Q}}(E_1/\Gamma, E_2/\Gamma)$（若选定实现 $\varphi_k : E_k \xrightarrow{\sim} q^*_{\mathrm{eq}}(D_k)$，则每个等变态射 $\Phi : E_1 \to E_2$ 唯一形如 $\varphi_2^{-1} \circ (\mathrm{id}_H \times_Q f) \circ \varphi_1$，其中 $f \in \mathrm{Hom}_{\mathcal{C}_{/Q}}(D_1, D_2)$）。
2. **固定对象 $E \in \mathrm{Equiv}_\Gamma(H)$ 的所有实现分类**：
   定义 $E$ 在 $Q$ 上的**实现范畴** $\mathcal{R}_Q(E)$：对象为二元组 $\bigl((D \xrightarrow{d} Q),\, \varphi : E \xrightarrow{\sim} q^*_{\mathrm{eq}}(D)\bigr)$（其中 $(D, d) \in \mathcal{C}_{/Q}$，$\varphi$ 为 $\mathrm{Equiv}_\Gamma(H)$ 中同构），态射 $f : ((D_1, d_1), \varphi_1) \to ((D_2, d_2), \varphi_2)$ 为 $\mathcal{C}_{/Q}$ 中满足 $q^*_{\mathrm{eq}}(f) \circ \varphi_1 = \varphi_2$ 的态射 $f : D_1 \to D_2$。则：
   - 若 $E$ 不满足判据 (C1)，$\mathcal{R}_Q(E) = \varnothing$；
   - 若 $E$ 满足判据 (C1)，$\mathcal{R}_Q(E)$ 是**可缩群胚**（非空，且任意两对象 $((D_1, d_1), \varphi_1)$ 与 $((D_2, d_2), \varphi_2)$ 之间存在**唯一**态射 $f = (q^*_{\mathrm{eq}})^{-1}(\varphi_2 \circ \varphi_1^{-1})$，该态射必为 $\mathcal{C}_{/Q}$ 中同构），具有典范基点对象 $\bigl((E/\Gamma \xrightarrow{\bar{\pi}} Q),\, \eta_E\bigr)$。（若固定某个满足 $q^*_{\mathrm{eq}}(D) \cong E$ 的对象 $(D \to Q) \cong (E/\Gamma \to Q)$，则实现同构 $\varphi : E \xrightarrow{\sim} q^*_{\mathrm{eq}}(D)$ 的全体构成 $\mathrm{Aut}_{\mathcal{C}_{/Q}}(D) \cong \mathrm{Aut}_{\mathrm{Equiv}_\Gamma(H)}(E)$ 的主齐性空间。）

*证明*：对任意 $\Phi \in \mathrm{Hom}_{\mathrm{Equiv}_\Gamma(H)}(H \times_Q D_1, H \times_Q D_2)$，因 $\mathrm{pr}_1 \circ \Phi = \mathrm{pr}_1$，$\Phi$ 由其第二分量 $\phi := \mathrm{pr}_2 \circ \Phi : H \times_Q D_1 \to D_2$ 唯一决定；等变性 $\Phi \circ (h_\gamma \times_Q \mathrm{id}_{D_1}) = (h_\gamma \times_Q \mathrm{id}_{D_2}) \circ \Phi$ 等价于 $\phi \circ (h_\gamma \times_Q \mathrm{id}_{D_1}) = \phi$（$\forall \gamma \in \Gamma$），且 $d_2 \circ \phi = q \circ \mathrm{pr}_1 = d_1 \circ \mathrm{pr}_2$。对 $(D_1 \xrightarrow{d_1} Q)$ 与 $Y = D_2$ 应用引理 3.3(2)，存在唯一的层态射 $f : D_1 \to D_2$ 使 $f \circ \mathrm{pr}_2 = \phi$；又 $d_2 \circ f \circ \mathrm{pr}_2 = d_2 \circ \phi = d_1 \circ \mathrm{pr}_2$，对 $Y = Q$ 再用引理 3.3(2) 的唯一性得 $d_2 \circ f = d_1$，从而 $\Phi = \mathrm{id}_H \times_Q f = q^*_{\mathrm{eq}}(f)$。这证明了 $q^*_{\mathrm{eq}}$ 忠实满。同时对 $D_1 = D$，引理 3.3(2) 表明 $\mathrm{pr}_2 : H \times_Q D \to D$ 具有层商 $(H \times_Q D)/\Gamma$ 的泛性质，给出自然余单位同构 $\varepsilon_D : \mathbf{q}_{!}(q^*_{\mathrm{eq}}(D)) \xrightarrow{\sim} D$；结合定理 3.2 中 $\mathrm{Real}_Q(H)$ 上的单位同构 $\eta_E : E \xrightarrow{\sim} q^*_{\mathrm{eq}}(\mathbf{q}_{!}(E))$，即证得 $\mathcal{C}_{/Q} \simeq \mathrm{Real}_Q(H)$ 及实现范畴 $\mathcal{R}_Q(E)$ 的可缩群胚结论。 $\square$

---

### 4. 任意层 $B \to Q$ 上的相对分类及与基底拉回的相容性

给定任意层态射 $b : B \to Q$。如引理 3.3 记 $H_B := H \times_Q B$、$q_B := \mathrm{pr}_2 : H_B \to B$ 及 $h_{B, \gamma} := h_\gamma \times_Q \mathrm{id}_B$。记 $\mathrm{Equiv}_\Gamma(H_B)$ 为 $H_B$ 上的等变对象范畴：对象为 $(E', \pi', a')$，其中 $\pi' : E' \to H_B$ 且 $\pi' \circ a'_\gamma = h_{B, \gamma} \circ \pi'$；定义 $B$ 上的实现函子为
$$q_{B, \mathrm{eq}}^* : \mathcal{C}_{/B} \longrightarrow \mathrm{Equiv}_\Gamma(H_B), \qquad (D' \xrightarrow{d'} B) \longmapsto \bigl(H_B \times_B D',\, \mathrm{pr}_1,\, \{h_{B, \gamma} \times_B \mathrm{id}_{D'}\}_{\gamma \in \Gamma}\bigr).$$

1. **$B \to Q$ 上的对应分类**：
   在定理 3.2 与定理 3.4 的全部证明中，关于 $q : H \to Q$ 所用到的**仅有**泛性质 $Q \cong H/\Gamma$、性质 (Q-满) 与性质 (Q-核)（以及对任意 $D' \to B$，因 $H_B \times_B D' = (H \times_Q B) \times_B D' \cong H \times_Q D'$，引理 3.3 对复合态射 $D' \to B \to Q$ 直接给出 $\mathrm{pr}_2 : H_B \times_B D' \to D'$ 同样具有商泛性质 $(H_B \times_B D')/\Gamma \cong D'$）。而引理 3.3 已证明 $q_B : H_B \to B$ 完全具备这三条性质！故逐字相同地得到 $B$ 上的完整分类：
   - **相对稳定子判据 (C1$_B$)**：$(E', \pi', a') \in \mathrm{Equiv}_\Gamma(H_B)$ 在 $B$ 上可实现 $\iff$ 对每个 $U \in \mathbf{Prof}_{\mathcal{U}}$、$e' \in E'(U)$、$\gamma \in \Gamma$，由 $h_{B, \gamma, U}(\pi'_U(e')) = \pi'_U(e')$ 可推出 $a'_{\gamma, U}(e') = e'$ $\iff$ 典范态射 $\eta_{B, E'} := (\pi', q_{E'}) : E' \to H_B \times_B (E'/\Gamma)$ 为同构（其中 $\bar{\pi}' : E'/\Gamma \to B$ 由 $\Gamma$-不变态射 $q_B \circ \pi' : E' \to B$ 诱导）。
   - **相对等价与实现分类**：$q_{B, \mathrm{eq}}^* : \mathcal{C}_{/B} \to \mathrm{Equiv}_\Gamma(H_B)$ 忠实满，诱导范畴等价 $\mathcal{C}_{/B} \xrightarrow{\simeq} \mathrm{Real}_B(H_B)$（拟逆为 $\mathbf{q}_{B, !}(E') = (E'/\Gamma \xrightarrow{\bar{\pi}'} B)$）；固定 $E' \in \mathrm{Equiv}_\Gamma(H_B)$ 时，其在 $B$ 上的实现范畴 $\mathcal{R}_B(E')$ 在不可实现时为空，在可实现时是以 $((E'/\Gamma \to B), \eta_{B, E'})$ 为典范对象的可缩群胚。

2. **与基底拉回的相容性证明**：
   更一般地，设 $f : (B' \xrightarrow{b'} Q) \to (B \xrightarrow{b} Q)$ 是 $\mathcal{C}_{/Q}$ 中任意态射（即 $b \circ f = b'$；特别取 $(B, b) = (Q, \mathrm{id}_Q)$、$f = b' : B' \to Q$ 即得从全局基底 $Q$ 到任意基底 $B' \to Q$ 的拉回相容性）。
   - 定义切片拉回 $f^* : \mathcal{C}_{/B} \to \mathcal{C}_{/B'}$，$(D \xrightarrow{d} B) \mapsto (D \times_B B' \xrightarrow{\mathrm{pr}_2} B')$；
   - 注意到规范等变同构 $\alpha_f : H_B \times_B B' = (H \times_Q B) \times_B B' \xrightarrow{\sim} H \times_Q B' = H_{B'}$，对 $(E', \pi', a') \in \mathrm{Equiv}_\Gamma(H_B)$（借由 $q_B \circ \pi' : E' \to B$ 视为 $B$ 上层），定义等变基底拉回 $f^*_{\mathrm{eq}} : \mathrm{Equiv}_\Gamma(H_B) \to \mathrm{Equiv}_\Gamma(H_{B'})$ 为
     $$f^*_{\mathrm{eq}}(E', \pi', a') := \bigl(E' \times_B B',\; \alpha_f \circ (\pi' \times_B \mathrm{id}_{B'}),\, \{a'_\gamma \times_B \mathrm{id}_{B'}\}_{\gamma \in \Gamma}\bigr)$$
     （当 $B = Q$ 时，因 $q_Q = \mathrm{id}_Q$，$E \times_Q B'$ 即题设中以 $q \circ \pi : E \to Q$ 做纤维积所得的拉回对象）。

   核验两重相容性：
   - **实现函子的交换性**：对任意 $(D \xrightarrow{d} B) \in \mathcal{C}_{/B}$，纤维积结合律给出 $\mathrm{Equiv}_\Gamma(H_{B'})$ 中的典范自然同构
     $$\tau_{f, D} : f^*_{\mathrm{eq}}\bigl(q_{B, \mathrm{eq}}^*(D)\bigr) = (H_B \times_B D) \times_B B' \xrightarrow{\;\sim\;} H_{B'} \times_{B'} (D \times_B B') = q_{B', \mathrm{eq}}^*\bigl(f^*(D)\bigr),$$
     在截面上由 $\bigl(((x, y_B), z), y_{B'}\bigr) \mapsto \bigl((x, y_{B'}), (z, y_{B'})\bigr)$（其中 $y_B = f(y_{B'})$）给出，显然保持到 $H_{B'}$ 的投影且 $\Gamma$-等变（两侧 $\Gamma$ 均仅将 $x$ 变为 $h_\gamma(x)$）。特别地，$f^*_{\mathrm{eq}}$ 将 $\mathrm{Real}_B(H_B)$ 映入 $\mathrm{Real}_{B'}(H_{B'})$（**可实现性在任意基底拉回下保持**），并诱导实现群胚之间的函子 $f^*_{\mathcal{R}} : \mathcal{R}_B(E') \to \mathcal{R}_{B'}(f^*_{\mathrm{eq}}(E'))$，$((D, d), \varphi) \mapsto (f^*(D, d),\, \tau_{f, D} \circ f^*_{\mathrm{eq}}(\varphi))$。
   - **典范商拟逆与单位态射的交换性**：对任意 $(E', \pi', a') \in \mathrm{Equiv}_\Gamma(H_B)$，$\Gamma$-不变映射 $(q_{E'} \circ \mathrm{pr}_1, \mathrm{pr}_2) : E' \times_B B' \to (E'/\Gamma) \times_B B'$ 诱导 $\mathcal{C}_{/B'}$ 中的典范态射
     $$\omega_{f, E'} : \mathbf{q}_{B', !}\bigl(f^*_{\mathrm{eq}}(E')\bigr) = (E' \times_B B')/\Gamma \xrightarrow{\;\sim\;} (E'/\Gamma) \times_B B' = f^*\bigl(\mathbf{q}_{B, !}(E')\bigr).$$
     因 $q_{E'} : E' \to E'/\Gamma$ 满足 (Q-满) 与 (Q-核)，与引理 3.3 完全相同的局部提升粘合论证（将引理 3.3 中的 $q : H \to Q$ 换为 $q_{E'} : E' \to E'/\Gamma$，将 $B \to Q$ 换为 $(E'/\Gamma) \times_B B' \to E'/\Gamma$）证明 $q_{E'} \times_B \mathrm{id}_{B'} : E' \times_B B' \to (E'/\Gamma) \times_B B'$ 具有层商 $(E' \times_B B')/\Gamma$ 的泛性质，故 $\omega_{f, E'}$ 恒为 $\mathcal{C}_{/B'}$ 中的同构！在截面上直接核验可知 $\tau_{f, E'/\Gamma} \circ f^*_{\mathrm{eq}}(\eta_{B, E'}) = q_{B', \mathrm{eq}}^*(\omega_{f, E'}) \circ \eta_{B', f^*_{\mathrm{eq}}(E')}$（两侧均将 $(e', y_{B'})$ 映为 $((x, y_{B'}), (q_{E'}(e'), y_{B'}))$，其中 $(x, y_B) = \pi'(e')$）。特别当 $E' \in \mathrm{Real}_B(H_B)$ 时，两个可缩群胚之间的拉回函子 $f^*_{\mathcal{R}} : \mathcal{R}_B(E') \xrightarrow{\simeq} \mathcal{R}_{B'}(f^*_{\mathrm{eq}}(E'))$ 是范畴等价，且将典范实现映为同构于拉回典范实现的对象。

---

## S4　单点上的检验

**判断结论**：**不一定**（$E$ 不必在 $Q$ 上可实现，结论为**否**）。

下面在共同设定下构造完整反例并逐项核验。

### 1. 反例构造

1. **群作用与基底 $H, Q$**：
   取单点空间 $T := * \in \mathbf{Prof}_{\mathcal{U}}$，故 $H = h_*$ 为终对象（对一切 $U \in \mathbf{Prof}_{\mathcal{U}}$，$H(U) = \mathrm{Cont}(U, *) = \{*\}$）。取二阶离散群 $\Gamma := \{1, \sigma\} \cong \mathbb{Z}/2\mathbb{Z}$（有限集，由 $\mathbb{N} \in \mathcal{U}$ 知 $\mathcal{U}$-小），令 $\Gamma$ 在 $T = *$ 上平凡作用，从而 $h_1 = h_\sigma = \mathrm{id}_H$。对任意层 $Y \in \mathcal{C}$，$\mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma = \mathrm{Hom}_{\mathcal{C}}(H, Y)$，故 $(Q, q) := (H, \mathrm{id}_H) = (h_*, \mathrm{id}_{h_*})$ 满足 S3 中层商的泛性质。

2. **紧阿贝尔群 $K$ 与分离预层 $P$**：
   赋予三元群 $\mathbb{Z}/3\mathbb{Z} = \{0, 1, 2\}$ 离散拓扑，令 $K := (\mathbb{Z}/3\mathbb{Z})^{\mathbb{N}}$ 带乘积拓扑及逐点模 $3$ 加法。因 $\mathbb{N} \in \mathcal{U}$ 且 Grothendieck 宇宙对指数封闭，$K$ 是 $\mathcal{U}$-小的；由有限离散空间的乘积紧性（可数 Tychonoff 定理，在 $\mathrm{ZFC}$ 中成立）、Hausdorff 性与全不连通性知 $K \in \mathbf{Prof}_{\mathcal{U}}$。
   对每个 $U \in \mathbf{Prof}_{\mathcal{U}}$，$\mathrm{Cont}(U, K)$ 在逐点加法下构成交换群；定义其子群
   $$\mathrm{Cont}_{\mathrm{fin}}(U, K) := \{ f \in \mathrm{Cont}(U, K) : f(U) \text{ 是 } K \text{ 的有限子集} \}.$$
   （因 $0 \in \mathrm{Cont}_{\mathrm{fin}}(U, K)$，且若 $f(U), g(U)$ 有限则 $(f - g)(U) \subseteq f(U) - g(U)$ 有限，故确为子群；对任意连续映射 $u : V \to U$，$(f \circ u)(V) \subseteq f(U)$ 亦有限，故前复合保持该子群。）定义商预层
   $$P : \mathbf{Prof}_{\mathcal{U}}^{\mathrm{op}} \longrightarrow \mathrm{Set}_{\mathcal{V}}, \qquad P(U) := \mathrm{Cont}(U, K) / \mathrm{Cont}_{\mathrm{fin}}(U, K),$$
   记陪集为 $[f]$。利用 S3 引理 3.1（仅依赖共同设定，此处适用），取层 $E := a(P) \in \mathcal{C}$ 及典范态射 $\iota_P : P \to E$。

3. **$E$ 上的等变结构**：
   在预层 $P$ 上定义左 $\Gamma$-作用：$a^P_1 := \mathrm{id}_P$，$a^P_{\sigma, U}([f]) := [-f]$（因 $(-f)(U) = -f(U)$ 有限性与 $f(U)$ 相同、$-(-f) = f$ 且取负与前复合交换，$a^P_\sigma$ 是对合预层自同构）。由引理 3.1 层化的泛性质，这在 $E = a(P)$ 上唯一诱导左 $\Gamma$-作用 $a = \{a_1 = \mathrm{id}_E,\, a_\sigma\}$ 使 $a_\gamma \circ \iota_P = \iota_P \circ a^P_\gamma$（$\forall \gamma \in \Gamma$）。取到终对象 $H = h_*$ 的唯一态射 $\pi : E \to H$，因 $h_\gamma = \mathrm{id}_H$，自动有 $\pi \circ a_\gamma = \pi = h_\gamma \circ \pi$，故 $(E, \pi, a) \in \mathrm{Equiv}_\Gamma(H)$。

### 2. 核验单点条件成立但 $E$ 在 $Q$ 上不可实现

1. **证明 $P$ 已是分离预层，故 $\iota_{P, U} : P(U) \hookrightarrow E(U)$ 对一切 $U$ 单射**：
   设 $f \in \mathrm{Cont}(U, K)$ 满足 $[f]$ 在某有限联合满射覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 上为零，即对每个 $i \in I$ 有 $f \circ u_i \in \mathrm{Cont}_{\mathrm{fin}}(U_i, K)$，$(f \circ u_i)(U_i)$ 为有限集。因 $\{u_i\}$ 联合满射，有 $U = \bigcup_{i \in I} u_i(U_i)$，从而
   $$f(U) = \bigcup_{i \in I} (f \circ u_i)(U_i)$$
   是有限个有限集的并，仍为有限集！故 $f \in \mathrm{Cont}_{\mathrm{fin}}(U, K)$，即 $[f] = [0] \in P(U)$。由引理 3.1 的局部相等刻画知 $\iota_{P, U} : P(U) \hookrightarrow E(U)$ 对每个 $U \in \mathbf{Prof}_{\mathcal{U}}$ 均为单射（即 $P_{\mathrm{sep}} = P$）。

2. **计算单点截面 $E(*)$ 并核验 S4 条件**：
   - 先看 $P(*)$ 与 $P(\varnothing)$：任何映射 $* \to K$ 的像至多含 $1$ 个元素（有限），任何映射 $\varnothing \to K$ 的像为空集（有限），故 $\mathrm{Cont}(*, K) = \mathrm{Cont}_{\mathrm{fin}}(*, K)$ 且 $\mathrm{Cont}(\varnothing, K) = \mathrm{Cont}_{\mathrm{fin}}(\varnothing, K)$，从而 $P(*) = \{[0]\}$ 与 $P(\varnothing) = \{[0]\}$ 均为单元素集。
   - 证明 $\iota_{P, *} : P(*) \xrightarrow{\sim} E(*)$ 为双射：单射性已证。任取 $\xi \in E(*) = P^+(*)$，设 $\xi$ 由 $*$ 的某有限联合满射覆盖 $\{u_i : U_i \to *\}_{i \in I}$ 上的相容族 $\{x_i \in P(U_i)\}_{i \in I}$ 代表。因 $*$ 非空而 $\{u_i\}$ 联合满射，必存在某 $i_0 \in I$ 使 $U_{i_0} \neq \varnothing$；取一点 $p_0 \in U_{i_0}$ 定义连续截面 $s : * \to U_{i_0}$（满足 $u_{i_0} \circ s = \mathrm{id}_*$），令 $x_0 := P(s)(x_{i_0}) \in P(*)$。对任意 $i \in I$（无论 $U_i$ 是否为空），连续映射 $(\mathrm{id}_{U_i}, s \circ u_i) : U_i \to U_i \times_* U_{i_0}$ 良定义；将相容性条件 $P(\mathrm{pr}_1)(x_i) = P(\mathrm{pr}_2)(x_{i_0})$ 沿 $(\mathrm{id}_{U_i}, s \circ u_i)$ 拉回，立得 $x_i = P(s \circ u_i)(x_{i_0}) = P(u_i)(P(s)(x_{i_0})) = P(u_i)(x_0)$。因此 $\{x_i\}_{i \in I}$ 恰为 $\iota_{P, *}(x_0)$ 在覆盖 $\{u_i\}$ 上的限制，故 $\xi = \iota_{P, *}(x_0)$。
   - 于是 $E(*) \cong P(*) = \{[0]\}$ 只含唯一元素！因此对**每个** $e \in E(*)$ 及 $\gamma \in \Gamma$，恒有 $a_{\gamma, *}(e) = e$，题设单点条件成立。

3. **证明 $E$ 在 $Q$ 上不可实现**：
   考察测试对象 $U = K \in \mathbf{Prof}_{\mathcal{U}}$ 及截面 $e := \iota_{P, K}([\mathrm{id}_K]) \in E(K)$。
   - 一方面，在终对象 $H(K) = \{*\}$ 中显然有 $h_{\sigma, K}(\pi_K(e)) = \pi_K(e)$。
   - 另一方面，$a_{\sigma, K}(e) = \iota_{P, K}(a^P_{\sigma, K}([\mathrm{id}_K])) = \iota_{P, K}([-\mathrm{id}_K])$。由 $\iota_{P, K}$ 的单射性，
     $$a_{\sigma, K}(e) = e \iff [-\mathrm{id}_K] = [\mathrm{id}_K] \in P(K) \iff \mathrm{id}_K - (-\mathrm{id}_K) = 2\,\mathrm{id}_K = -\mathrm{id}_K \in \mathrm{Cont}_{\mathrm{fin}}(K, K)$$
     （因为在特征 $3$ 群 $K = (\mathbb{Z}/3\mathbb{Z})^{\mathbb{N}}$ 中 $2\,\mathrm{id}_K = -\mathrm{id}_K$）。但 $(-\mathrm{id}_K)(K) = K$，而 $|K| = 3^{|\mathbb{N}|}$ 是无穷集，故 $-\mathrm{id}_K \notin \mathrm{Cont}_{\mathrm{fin}}(K, K)$，从而 $a_{\sigma, K}(e) \neq e$！
   由 S3 定理 3.2（本阶段仅用共同设定，定理 3.2 完全适用）的必要性，判据 (C1) 在 $U = K$ 上不成立，故 $E$ 在 $Q$ 上**不可实现**。

---

## S5　局部满射的基底检验

**判断结论**：**必可在 $Q$ 上实现**（结论为**是**）。

**证明**：
本阶段仅使用共同设定，并设 $b : B \to Q$ 为局部满射层态射，且拉回对象 $E_B := E \times_Q B$ 作为 $H_B := H \times_Q B$ 上的等变对象（投影 $\pi_B = \pi \times_Q \mathrm{id}_B$，群作用 $a_{B, \gamma} = a_\gamma \times_Q \mathrm{id}_B$）在 $B$ 上可实现。S3 定理 3.2 及其第 4 步关于任意基底 $B \to Q$ 的相对稳定子判据 (C1$_B$) 仅依赖共同设定，因此在此完全适用。

我们验证 $E$ 满足 S3 定理 3.2 的截面稳定子判据 (C1)：
任取测试对象 $U \in \mathbf{Prof}_{\mathcal{U}}$、截面 $e \in E(U)$ 及 $\gamma \in \Gamma$，假设
$$h_{\gamma, U}\bigl(\pi_U(e)\bigr) = \pi_U(e).$$
需证 $a_{\gamma, U}(e) = e$。
1. 令 $g := q_U(\pi_U(e)) \in Q(U)$。由于 $b : B \to Q$ **局部满射**，按题设定义，存在 $U$ 的某有限联合满射覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 及截面族 $\{y_i \in B(U_i)\}_{i \in I}$，使得对每个 $i \in I$ 有
   $$b_{U_i}(y_i) = Q(u_i)(g) = q_{U_i}\bigl(\pi_{U_i}(e|_{U_i})\bigr).$$
2. 这表明对每个 $i \in I$，二元组
   $$e'_i := (e|_{U_i},\, y_i) \in E(U_i) \times_{Q(U_i)} B(U_i) = E_B(U_i)$$
   构成拉回层 $E_B$ 在 $U_i$ 上的截面，其在 $H_B(U_i) = H(U_i) \times_{Q(U_i)} B(U_i)$ 中的投影为 $\pi_{B, U_i}(e'_i) = (\pi_{U_i}(e|_{U_i}),\, y_i)$。
3. 对 $\pi_{B, U_i}(e'_i)$ 作用 $h_{B, \gamma, U_i} = h_{\gamma, U_i} \times_{Q(U_i)} \mathrm{id}_{B(U_i)}$：由假设 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$ 限制到 $U_i$ 上得 $h_{\gamma, U_i}(\pi_{U_i}(e|_{U_i})) = \pi_{U_i}(e|_{U_i})$，故
   $$h_{B, \gamma, U_i}\bigl(\pi_{B, U_i}(e'_i)\bigr) = \bigl(h_{\gamma, U_i}(\pi_{U_i}(e|_{U_i})),\, y_i\bigr) = \bigl(\pi_{U_i}(e|_{U_i}),\, y_i\bigr) = \pi_{B, U_i}(e'_i).$$
4. 因 $E_B$ 在 $B$ 上可实现，对测试对象 $U_i$、截面 $e'_i \in E_B(U_i)$ 与 $\gamma \in \Gamma$ 应用 S3 第 4 步的相对稳定子判据 (C1$_B$)（必要性），立得
   $$a_{B, \gamma, U_i}(e'_i) = e'_i \quad \text{于 } E_B(U_i).$$
5. 取第一投影 $\mathrm{pr}_1 : E_B = E \times_Q B \to E$，因 $a_{B, \gamma} = a_\gamma \times_Q \mathrm{id}_B$，比较第一坐标得对一切 $i \in I$ 有
   $$\bigl(a_{\gamma, U}(e)\bigr)\big|_{U_i} = a_{\gamma, U_i}(e|_{U_i}) = e|_{U_i} \quad \text{于 } E(U_i).$$
6. 因 $\{u_i : U_i \to U\}_{i \in I}$ 是 $U$ 的覆盖且 $E$ 是层（具分离性），故 $a_{\gamma, U}(e) = e$ 在 $E(U)$ 中成立。

于是 $E$ 满足判据 (C1)。由 S3 定理 3.2（充分性），$E$ 必可在 $Q$ 上实现。 $\square$

---

## S6　非空基底与全局结论

### 1. 判断结论与完整反例核验

**判断结论**：**不一定反映原 $E$ 可实现**（仅假设 $B$ 是非空可表示层且有态射 $B \to Q$ 时，拉回对象 $E \times_Q B$ 在 $B$ 上可实现**不能**保证原 $E$ 在 $Q$ 上可实现，结论为**否**）。

**完整例子与核验**：
1. **构造 $T, \Gamma, H, Q$**：
   取二元离散空间 $T := \{t_0, t_1\} \in \mathbf{Prof}_{\mathcal{U}}$（$t_0 \neq t_1$），二阶离散群 $\Gamma := \{1, \sigma\} \cong \mathbb{Z}/2\mathbb{Z}$ 在 $T$ 上**平凡作用**（$\sigma_T = \mathrm{id}_T$）。记 $H := h_T$，则 $h_\gamma = \mathrm{id}_H$（$\forall \gamma \in \Gamma$）。对任意层 $Y \in \mathcal{C}$ 有 $\mathrm{Hom}_{\mathcal{C}}(H, Y)^\Gamma = \mathrm{Hom}_{\mathcal{C}}(H, Y)$，故 S3 中的层商为 $Q = H = h_T$，商态射为 $q = \mathrm{id}_H : H \to Q$。
2. **构造等变层 $E$**：
   取三元离散空间 $X := \{x_0, x_1^+, x_1^-\} \in \mathbf{Prof}_{\mathcal{U}}$，定义投影 $f : X \to T$ 为
   $$f(x_0) := t_0, \qquad f(x_1^+) := t_1, \qquad f(x_1^-) := t_1,$$
   并定义 $X$ 上的左 $\Gamma$-作用：$1_X := \mathrm{id}_X$，$\sigma_X(x_0) := x_0$，$\sigma_X(x_1^+) := x_1^-$，$\sigma_X(x_1^-) := x_1^+$。显然 $\sigma_X^2 = \mathrm{id}_X$ 且 $f \circ \sigma_X = f = \sigma_T \circ f$。令 $E := h_X \in \mathcal{C}$，$\pi := h_f : E \to H$，$a_\gamma := h_{\gamma_X} : E \to E$，则 $(E, \pi, a) \in \mathrm{Equiv}_\Gamma(H)$。
3. **构造非空可表示基底 $B \to Q$**：
   取单点非空空间 $S := \{t_0\} \in \mathbf{Prof}_{\mathcal{U}}$（$S \neq \varnothing$），令 $B := h_S$。因 $B(*) = \mathrm{Cont}(*, S) \neq \varnothing$（即 $B \not\cong h_\varnothing$），$B$ 是**非空可表示层**。由包含映射 $\iota : S = \{t_0\} \hookrightarrow \{t_0, t_1\} = T$ 诱导层态射 $b := h_\iota : B \to Q = h_T$。
4. **核验拉回 $E \times_Q B$ 在 $B$ 上可实现**：
   因米田嵌入 $h_{(-)}$ 保持纤维积，有典范同构
   $$H_B = h_T \times_{h_T} h_S \cong h_{T \times_T S} \cong h_S = B, \qquad E \times_Q B = h_X \times_{h_T} h_S \cong h_{X \times_T S} = h_{f^{-1}(\{t_0\})} = h_{\{x_0\}}.$$
   由于 $\sigma_X(x_0) = x_0$ 且 $f|_{\{x_0\}} : \{x_0\} \xrightarrow{\sim} \{t_0\} = S$ 是双射，$\pi_B : E \times_Q B \xrightarrow{\sim} H_B$ 是层同构，且两侧 $\Gamma$-作用均为恒等态射。取 $(D' \to B) := (B \xrightarrow{\mathrm{id}_B} B)$，则 $H_B \times_B B \cong H_B \xleftarrow[\sim]{\pi_B} E \times_Q B$ 保持到 $H_B$ 的投影且对恒等 $\Gamma$-作用等变，故 $E \times_Q B$ **在 $B$ 上可实现**。
5. **核验原对象 $E$ 在 $Q$ 上不可实现**：
   取测试对象 $*$ 及截面 $e \in E(*) = \mathrm{Cont}(*, X)$，$e(*) := x_1^+$。则 $\pi_*(e)(*) = f(x_1^+) = t_1$，满足 $h_{\sigma, *}(\pi_*(e)) = \pi_*(e)$；然而 $a_{\sigma, *}(e)(*) = \sigma_X(x_1^+) = x_1^- \neq x_1^+ = e(*)$，即 $a_{\sigma, *}(e) \neq e$。这违反了 S3 定理 3.2（此处在共同设定下完全适用；同时因 $\Gamma, T, X$ 均有限且 $Q = h_T = h_{T/\Gamma}$，亦违反 S2 第 2 步充要条件中代表元 $t_1$ 的稳定子 $\Gamma_{t_1} = \Gamma$ 在纤维 $\{x_1^+, x_1^-\}$ 上作用平凡的要求）的必要条件，故原对象 $E$ **在 $Q$ 上不可实现**。

*(原因剖析：态射 $b : h_{\{t_0\}} \to h_{\{t_0, t_1\}}$ 的像遗漏了轨道点 $t_1$，不是局部满射，从而拉回 $E \times_Q B$ 将 $t_1$ 上破坏可实现性的非平凡稳定子作用完全抹去了。)*

---

### 2. 据此前结果整理的可用检验原则

综合 S1–S6 的正反结果，判断一般等变对象 $(E, \pi, a) \in \mathrm{Equiv}_\Gamma(H)$ 是否在层商 $Q = H/\Gamma$ 上可实现，有以下四类严格有效的检验原则（连同其适用边界）：

1. **全景截面稳定子原则与覆盖约化原则（充要检验，据 S3）**：
   - **主判据**：$E$ 在 $Q$ 上可实现 $\iff$ 对每个 $U \in \mathbf{Prof}_{\mathcal{U}}$、$e \in E(U)$、$\gamma \in \Gamma$，有 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e) \implies a_{\gamma, U}(e) = e$ $\iff$ 典范态射 $\eta_E = (\pi, q_E) : E \to H \times_Q (E/\Gamma)$ 逐对象单射。
   - **共尾覆盖约化**：由层 $E$ 的分离性，若一族测试对象子集 $\mathcal{G} \subseteq \mathrm{Ob}(\mathbf{Prof}_{\mathcal{U}})$ 满足每个 $U \in \mathbf{Prof}_{\mathcal{U}}$ 都承认某个成员选自 $\mathcal{G}$ 的有限覆盖 $\{u_i : U_i \to U\}_{i \in I}$，则只需对所有 $V \in \mathcal{G}$ 检验稳定子条件即可（因 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$ 限制到 $U_i \in \mathcal{G}$ 上推出 $a_{\gamma, U}(e)|_{U_i} = e|_{U_i}$，粘合唯一性即给出 $a_{\gamma, U}(e) = e$）。

2. **底空间自由作用的免检自动下降原则（充分检验，据 S1 与 S3）**：
   - 若有限群 $\Gamma$ 在 $T$ 上自由作用，则由 S1，$Q \cong h_{T/\Gamma}$ 且**任意**等变层 $E \to H$ 自动在 $Q$ 上可实现。
   - 更一般地，对**任意** $\mathcal{U}$-小离散群 $\Gamma$，只要 $\Gamma$ 在 $T$ 上自由作用，由 S3 判据 (C1) 亦知**任意**等变层 $E \to H$ 自动在 $Q = H/\Gamma$ 上可实现：对 $U = \varnothing$，$|E(\varnothing)| = 1$ 故 $a_{\gamma, \varnothing}(e) = e$ 自动成立；对 $U \neq \varnothing$，取一点 $u_0 \in U$，由 $h_{\gamma, U}(\pi_U(e)) = \pi_U(e)$ 得 $\gamma(\pi_U(e)(u_0)) = \pi_U(e)(u_0)$，由自由性知 $\gamma = 1_\Gamma$，从而 $a_{\gamma, U}(e) = a_{1, U}(e) = e$。

3. **单点检验与轨道代表纤维检验原则（区分一般层与可表示层，据 S2、S3、S4）**：
   - **对一般层仅作证伪（必要非充分，据 S3、S4）**：单点 $U = *$ 上的稳定子条件（$\forall e \in E(*),\, \forall \gamma \in \Gamma,\; \gamma\pi_*(e) = \pi_*(e) \implies a_{\gamma, *}(e) = e$）是可实现性的**必要条件**，故一旦在 $E(*)$ 上找到反例点即可直接**证伪**可实现性；但由 S4 知，因无穷 profinite 空间上的层截面未必由单点取值决定，单点检验对一般层**不能用于确证**可实现性。
   - **对可表示等变层为充要检验（据 S2、S3）**：若 $E \cong h_X$ 可表示（$X \in \mathbf{Prof}_{\mathcal{U}}$，$\pi = h_f$，$a_\gamma = h_{\gamma_X}$），则单点 $U = *$ 上的稳定子检验（即 $\forall x \in X,\, \Gamma_{f(x)} \subseteq \Gamma_x$）**既是必要的也是充分的**：对任意 $U \in \mathbf{Prof}_{\mathcal{U}}$ 及 $e \in \mathrm{Cont}(U, X)$，若 $\gamma_T \circ f \circ e = f \circ e$，则对每个点 $u \in U$ 有 $\gamma f(e(u)) = f(e(u))$，由单点条件得 $\gamma e(u) = e(u)$（$\forall u \in U$），即映射 $\gamma_X \circ e = e$，从而满足 S3 判据 (C1)。特别当 $\Gamma, T, X$ 均有限时（据 S2），只需对 $T/\Gamma$ 的每个轨道任选一个代表元 $t \in \mathcal{R}$，检验稳定子群 $\Gamma_t$ 在单条纤维 $f^{-1}(\{t\})$ 上作用平凡即可。

4. **基底拉回检验原则：任意基底证伪与局部满射基底确证（据 S3、S5、S6）**：
   - **任意基底拉回的证伪原则（据 S3）**：由 S3 第 4 步，可实现性在**任意**层态射 $b : B \to Q$ 拉回下保持；故只要找到某个 $B \to Q$ 使 $E \times_Q B$ 在 $B$ 上不可实现，即可确证原 $E$ 不可实现。但由 S6 反例知，一般非空可表示层 $B = h_S \to Q$ 上的拉回可实现**不足以**反推原 $E$ 可实现。
   - **局部满射基底（及有限联合局部满射族）的充要检验原则（据 S3、S5）**：当 $b : B \to Q$ **局部满射**时，$E$ 在 $Q$ 上可实现 $\iff E \times_Q B$ 在 $B$ 上可实现。实用推论包括：
     1. **有限分片基底检验**：若有限族态射 $\{b_k : B_k \to Q\}_{k=1}^m$ **联合局部满射**（即对任意 $U$ 及 $g \in Q(U)$，存在覆盖 $\{u_i : U_i \to U\}_{i \in I}$ 使每个 $g|_{U_i}$ 可提升到某个 $B_{k(i)}(U_i)$），则 $E$ 在 $Q$ 上可实现 $\iff$ 对每个 $k \in \{1, \dots, m\}$，$E \times_Q B_k$ 在 $B_k$ 上可实现（直接将 S5 证明第 2–5 步对各指标 $i$ 分别在 $E \times_Q B_{k(i)}$ 中实施即可粘合得 $a_{\gamma, U}(e) = e$）。
     2. **可表示基底满射判据与单轨道特例**：当 $Q \cong h_Z$ 可表示时（例如 $\Gamma$ 有限时 $Z = T/\Gamma$），可表示基底态射 $h_\beta : h_S \to h_Z$（$\beta \in \mathrm{Cont}(S, Z)$）局部满射当且仅当连续映射 $\beta : S \to Z$ **满射**（若 $\beta$ 满射，对 $g \in \mathrm{Cont}(U, Z)$ 拉回得单元覆盖 $\{U \times_Z S \to U\}$ 及提升 $\mathrm{pr}_2$；反之对 $\mathrm{id}_Z \in h_Z(Z)$ 局部提升即得 $Z = \beta(S)$）。特别当 $Q \cong h_*$ 时，**任意**非空可表示层 $B = h_S$（$S \neq \varnothing$）到 $Q \cong h_*$ 的唯一态射自动满足映射 $S \twoheadrightarrow *$ 满射从而局部满射，唯有在此类局部满射情形下非空可表示基底才充要反映原 $E$ 的可实现性。
