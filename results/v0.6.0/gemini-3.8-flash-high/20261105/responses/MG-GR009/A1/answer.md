# 群作用下降、稳定子与基底检验

---

## S1　有限群的自由作用

### 1. 轨道空间 $T/\Gamma$ 的构造与性质验证
设 $T \in \mathrm{Prof}_U$，$\Gamma$ 为有限群且在 $T$ 上连续自由作用。
- **空间定义**：令 $T/\Gamma$ 为拓扑商空间，商映射为 $p: T \to T/\Gamma$。
- **紧 Hausdorff 性**：
  轨道等价关系为 $R = \{ (t, \gamma t) \mid t \in T, \gamma \in \Gamma \} = \bigcup_{\gamma \in \Gamma} \mathrm{graph}(\gamma) \subseteq T \times T$。因为每个 $\gamma: T \to T$ 是同胚且 $T$ 是 Hausdorff 空间，每个图 $\mathrm{graph}(\gamma)$ 均为闭集；由于 $\Gamma$ 有限，有限个闭集的并 $R$ 仍为 $T \times T$ 中的闭集。由点集拓扑标准定理，紧 Hausdorff 空间关于闭等价关系的商空间必为紧 Hausdorff 空间。
- **全不连通性**：
  对任意 $t \in T$，由于 $\Gamma$ 作用自由，有限点集 $\{\gamma t\}_{\gamma \in \Gamma}$ 两两互异。在 Stone 空间 $T$ 中，存在互不相交的闭开邻域族 $U_\gamma \ni \gamma t$。令 $U = \bigcap_{\gamma \in \Gamma} \gamma^{-1}(U_\gamma)$，则 $U$ 为包含 $t$ 的闭开集，且族 $\{\gamma U\}_{\gamma \in \Gamma}$ 两两不交。商映射满足 $p^{-1}(p(U)) = \coprod_{\gamma \in \Gamma} \gamma U$，故 $p(U)$ 在 $T/\Gamma$ 中为闭开集，且限制映射 $p|_U: U \to p(U)$ 是同胚。由此可知 $p(U)$ 具有全不连通基，故 $T/\Gamma$ 为全不连通空间。
- **结论**：$T/\Gamma \in \mathrm{Prof}_U$。

### 2. 证明 $h_{T/\Gamma}$ 是层商
需证 $h_p: h_T \to h_{T/\Gamma}$ 是等价关系对 $\coprod_{\gamma \in \Gamma} h_T \rightrightarrows h_T$ 在层范畴 $\mathcal{C}$ 中的余等化子（层商）。
- **局部满射性（层满射）**：
  对任一测试对象 $U \in \mathrm{Prof}_U$ 及截面 $f \in h_{T/\Gamma}(U) = C(U, T/\Gamma)$，考虑拓扑拉回 $U \times_{T/\Gamma} T$。由于 $p$ 是紧 Hausdorff 空间之间的连续满射，投影 $p_U: U \times_{T/\Gamma} T \to U$ 也是连续满射，故单元素族 $\{p_U: U \times_{T/\Gamma} T \to U\}$ 构成 $U$ 在 $\mathrm{Prof}_U$ 上的覆盖。另一投影 $\tilde{f}: U \times_{T/\Gamma} T \to T$ 连续且满足 $p \circ \tilde{f} = f \circ p_U$，即在覆盖上给出了 $f$ 的提升。因此 $h_p$ 为局部满射（层的满态射）。
- **核对（Kernel pair）计算**：
  由于 Yoneda 嵌入保所有极限，核对为 $h_T \times_{h_{T/\Gamma}} h_T \cong h_{T \times_{T/\Gamma} T}$。因为 $\Gamma$ 有限且自由，映射
  $$ \theta: T \times \Gamma \longrightarrow T \times_{T/\Gamma} T, \quad (t, \gamma) \longmapsto (t, \gamma t) $$
  是紧 Hausdorff 空间之间的连续双射，从而为同胚。取可表示层得
  $$ h_T \times_{h_{T/\Gamma}} h_T \cong h_{T \times \Gamma} \cong \coprod_{\gamma \in \Gamma} h_T $$
  在此同构下，两个投影映射分别对应恒等映射 $\mathrm{id}_{h_T}$ 与群作用 $h_\gamma$。
- **层商结论**：
  在 Grothendieck topos 中，每个满态射都是其核对的余等化子。因此 $h_{T/\Gamma}$ 是 $\coprod_{\gamma \in \Gamma} h_T \rightrightarrows h_T$ 的余等化子，即层商。

### 3. 证明每个等变层在商上实现
设 $(E, \pi, a)$ 为 $H = h_T$ 上的等变层。
- 满态射 $h_p: H \to h_{T/\Gamma}$ 在 topos 中是有效下降态射（effective descent morphism）。
- 沿 $h_p$ 的下降数据是同构 $\alpha: \mathrm{pr}_1^* E \xrightarrow{\sim} \mathrm{pr}_2^* E$ 在 $H \times_{h_{T/\Gamma}} H$ 上满足余圈条件。
- 依据核对同构 $H \times_{h_{T/\Gamma}} H \cong \coprod_{\gamma \in \Gamma} H$，给出一个下降数据严格等价于给出族 $(a_\gamma: E \to E)_{\gamma \in \Gamma}$ 满足 $\pi a_\gamma = h_\gamma \pi$ 且 $a_{\gamma_1 \gamma_2} = a_{\gamma_1} a_{\gamma_2}$，这正是 $E$ 上的 $\Gamma$-等变结构。
- 由有效下降理论，函子 $D \mapsto H \times_{h_{T/\Gamma}} D$ 构成 $\mathcal{C}_{/h_{T/\Gamma}}$ 到 $H$ 上等变层范畴的范畴等价，其拟逆由层商 $E \mapsto E/\Gamma$ 给出。
- 因此，对每个等变层 $E$，均有 $E \cong H \times_{h_{T/\Gamma}} (E/\Gamma)$，且群作用仅作用在 $H$ 坐标上。

---

## S2　有限集合上的纤维分类

### 1. 分类有限等变对象 $X \to T$ 及其等变态射
设 $\Gamma$ 和 $T$ 均有限，$T = \coprod_{i \in I} \mathcal{O}_i$ 为轨道的有限无交并，选代表元 $t_i \in \mathcal{O}_i$，稳定子为 $\Gamma_{t_i} \le \Gamma$。
- **对象的分类**：
  对任意有限 $\Gamma$-集合 $X$ 及等变映射 $\pi: X \to T$，$X = \coprod_{i \in I} \pi^{-1}(\mathcal{O}_i)$。每个纤维 $X_{t_i} = \pi^{-1}(t_i)$ 具有诱导的 $\Gamma_{t_i}$ 作用，为有限 $\Gamma_{t_i}$-集合。
  反之，给定有限 $\Gamma_{t_i}$-集合族 $(S_i)_{i \in I}$，定义诱导集合
  $$ X = \coprod_{i \in I} \left( \Gamma \times^{\Gamma_{t_i}} S_i \right) $$
  配备典范投影到 $\coprod_{i \in I} \Gamma/\Gamma_{t_i} \cong T$，构成了逆向构造。这给出了范畴等价：
  $$ \mathbf{FinSet}_\Gamma / T \xrightarrow{\sim} \prod_{i \in I} \mathbf{FinSet}_{\Gamma_{t_i}}, \quad (X \to T) \longmapsto (X_{t_i})_{i \in I} $$
- **态射的分类**：
  若 $\phi: X \to Y$ 为 $T$ 上的等变态射，则 $\phi$ 保持纤维，其限制 $\phi_{t_i}: X_{t_i} \to Y_{t_i}$ 为 $\Gamma_{t_i}$-等变映射。由诱导表示的伴随性，等变态射集完全由纤维上的态射决定：
  $$ \mathrm{Hom}_{\Gamma / T}(X, Y) \cong \prod_{i \in I} \mathrm{Hom}_{\Gamma_{t_i}}(X_{t_i}, Y_{t_i}) $$

### 2. $h_X$ 在 $Q = h_{T/\Gamma}$ 上实现的充要条件
- **结论**：$h_X$ 在 $Q$ 上可实现当且仅当：**对每个代表元 $t_i$（等价于对所有 $t \in T$），稳定子 $\Gamma_{t_i}$ 在纤维 $X_{t_i}$ 上的作用是平凡的**。
- **必要性**：
  若 $h_X \cong H \times_Q D$，对任一点 $t \in T$，其稳定子 $\Gamma_t$ 满足 $\gamma t = t$。在积层 $H \times_Q D$ 的纤维 $\{t\} \times D_{q(t)}$ 上，群元素 $\gamma \in \Gamma_t$ 作用为 $(\gamma t, d) = (t, d)$，即恒等作用。因此 $\Gamma_t$ 在 $X_t$ 上的作用必平凡。
- **充分性**：
  若每个 $\Gamma_{t_i}$ 平凡作用于 $X_{t_i}$，则作为 $\Gamma$-集合有
  $$ \Gamma \times^{\Gamma_{t_i}} X_{t_i} \cong (\Gamma/\Gamma_{t_i}) \times X_{t_i} \cong \mathcal{O}_i \times X_{t_i} $$
  取 $D_i = h_{X_{t_i}}$ 为点上的常值层，令 $D = \coprod_{i \in I} D_i \in \mathcal{C}_{/Q}$。则
  $$ H \times_Q D \cong \coprod_{i \in I} (h_{\mathcal{O}_i} \times D_i) \cong \coprod_{i \in I} h_{\mathcal{O}_i \times X_{t_i}} \cong h_X $$
  群作用仅由 $H$ 坐标承担，故 $h_X$ 在 $Q$ 上可实现。

### 3. 可实现对象的自同构群
设 $X$ 可实现，每个 $X_{t_i}$ 上的 $\Gamma_{t_i}$ 作用平凡。
- 任意等变映射 $\phi_{t_i}: X_{t_i} \to X_{t_i}$ 自动为等变的，故 $\mathrm{Aut}_{\Gamma_{t_i}}(X_{t_i}) = \mathrm{Aut}_{\mathbf{Set}}(X_{t_i}) \cong \mathfrak{S}(X_{t_i})$（纤维 $X_{t_i}$ 上的全对称群）。
- 因此，自同构群为：
  $$ \mathrm{Aut}_{\Gamma / T}(X) \cong \prod_{i \in I} \mathfrak{S}(X_{t_i}) \cong \prod_{i \in I} S_{n_i} $$
  其中 $n_i = |X_{t_i}|$ 为代表元 $t_i$ 处纤维的基数。

---

## S3　一般层的完整下降

### 1. 层 $Q$ 与不变态射 $q: H \to Q$ 的构造与普适性质
- **构造**：
  定义预层商 $P \in \mathrm{PSh}(\mathrm{Prof}_U)$：对任一 $U \in \mathrm{Prof}_U$，$P(U) = H(U) / \Gamma = C(U, T) / \Gamma$（截面集关于 $\Gamma$ 作用的轨道集）。
  令 $a: \mathrm{PSh}(\mathrm{Prof}_U) \to \mathrm{Sh}(\mathrm{Prof}_U) = \mathcal{C}$ 为层化函子。
  定义层 $Q = a(P)$，不变态射 $q: H \to Q$ 为典范合成 $H \xrightarrow{\eta} P \to a(P) = Q$。
- **不变性与普适性**：
  在预层水平，$H \to P$ 显然是 $\Gamma$-不变的，故 $q \circ h_\gamma = q$ 对所有 $\gamma \in \Gamma$ 成立。
  对任一 $Y \in \mathcal{C}$，由层化函子与包含函子的伴随性：
  $$ \mathrm{Hom}_\mathcal{C}(Q, Y) = \mathrm{Hom}_\mathcal{C}(a(P), Y) \cong \mathrm{Hom}_{\mathrm{PSh}}(P, Y) $$
  由预层轨道商的普适性，自然同构于 $\Gamma$-不变态射集 $\mathrm{Hom}_{\mathrm{PSh}}(H, Y)^\Gamma = \mathrm{Hom}_\mathcal{C}(H, Y)^\Gamma$。

### 2. 不预选 $D$ 的可实现性充要判据
设 $(E, \pi, a)$ 为 $H$ 上的等变层。
- **典范态射构造**：
  构造层商 $E/\Gamma = a(U \mapsto E(U)/\Gamma)$。由 $\pi$ 的等变性，诱导唯一态射 $\bar{\pi}: E/\Gamma \to Q$。
  由纤维积的普适性质，态射 $\pi: E \to H$ 与商态射 $p_E: E \to E/\Gamma$ 诱导唯一的等变态射：
  $$ \Phi_E: E \longrightarrow H \times_Q (E/\Gamma) $$
- **充要判据（典范态射同构）**：
  $E$ 在 $Q$ 上可实现当且仅当 **典范态射 $\Phi_E$ 是层的同构**。
- **等价的群层稳定子判据**：
  定义 $H$ 上的稳定子群层 $\mathrm{Stab} \le H \times \underline{\Gamma}$：对 $U \in \mathrm{Prof}_U$，
  $$ \mathrm{Stab}(U) = \{ (f, \gamma) \in C(U, T) \times C(U, \Gamma) \mid \gamma \cdot f = f \} $$
  则 $\Phi_E$ 为同构当且仅当 **$\mathrm{Stab}$ 在 $E$ 上的诱导作用是平凡的**（即对每个测试对象 $U$，恒等固定截面 $f$ 的群截面 $\gamma$ 必恒等固定其纤维截面 $s \in \pi^{-1}(f)$）。

### 3. 所有实现及态射的分类
- 令 $\mathbf{Real}(H/Q)$ 为可实现等变层的全子范畴，$\mathcal{C}_{/Q}$ 为 $Q$ 上的切片范畴。
- 构造函子：
  $$ q^*: \mathcal{C}_{/Q} \longrightarrow \mathbf{Real}(H/Q), \quad (D \to Q) \longmapsto (H \times_Q D \to H) $$
  $$ (-)/\Gamma: \mathbf{Real}(H/Q) \longrightarrow \mathcal{C}_{/Q}, \quad (E \to H) \longmapsto (E/\Gamma \to Q) $$
- 由于 topos 中的余极限是泛的（与拉回交换），对任意 $D \in \mathcal{C}_{/Q}$，有典范同构 $(H \times_Q D)/\Gamma \cong (H/\Gamma) \times_Q D \cong Q \times_Q D \cong D$。
- 对任意 $E \in \mathbf{Real}(H/Q)$，伴随余单位即为同构 $\Phi_E: E \xrightarrow{\sim} H \times_Q (E/\Gamma)$。
- 因此，$q^*$ 与 $(-)/\Gamma$ 构成范畴等价：
  $$ \mathbf{Real}(H/Q) \simeq \mathcal{C}_{/Q} $$
  等变态射集严格自然双射于切片范畴中的态射集：$\mathrm{Hom}_{\mathbf{Real}}(E_1, E_2) \cong \mathrm{Hom}_{\mathcal{C}_{/Q}}(E_1/\Gamma, E_2/\Gamma)$。

### 4. 任意基底 $B \to Q$ 的对应分类与拉回相容性
- 对任一态射 $p: B \to Q$，令 $H_B = H \times_Q B$。由 $q \circ h_\gamma = q$，$H_B$ 继承 $\Gamma$-作用 $h_\gamma \times \mathrm{id}_B$。
- 由余极限与拉回交换，商层为 $H_B/\Gamma \cong (H/\Gamma) \times_Q B \cong B$。
- 同理，$H_B$ 上可实现等变层范畴等价于 $\mathcal{C}_{/B}$：
  $$ \mathbf{Real}(H_B/B) \simeq \mathcal{C}_{/B}, \quad D_B \longmapsto H_B \times_B D_B $$
- **与基底拉回的相容性**：
  对任意 $f: B' \to B \in \mathcal{C}_{/Q}$，拉回函子 $f^*: \mathcal{C}_{/B} \to \mathcal{C}_{/B'}$ 与等变拉回函子 $f_H^*: \mathbf{Real}(H_B/B) \to \mathbf{Real}(H_{B'}/B')$ 满足典范自然同构：
  $$ f_H^*(H_B \times_B D_B) = (H_B \times_B D_B) \times_B B' \cong H_{B'} \times_{B'} f^*(D_B) $$
  且商函子亦满足 $(E_B \times_B B')/\Gamma \cong (E_B/\Gamma) \times_B B' = f^*(E_B/\Gamma)$，满足伪函子一致性条件。

---

## S4　单点上的检验

### 1. 结论
**否**（$E$ 不必在 $Q$ 上可实现）。

### 2. 完整核验反例
- **共同设定实例化**：
  - 令 $T = *$（单点空间，终对象），$\Gamma = \mathbb{Z}/2\mathbb{Z} = \{1, \sigma\}$。
  - $\Gamma$ 在 $T$ 上的作用为唯一可能的作用（平凡作用）。
  - $H = h_* = 1$（终层），$Q = H/\Gamma = 1$，$q = \mathrm{id}_1$。
  - 在此设定下，若等变层 $E$ 在 $Q=1$ 上可实现，由于 $H \times_Q D = 1 \times_1 D \cong D$ 上的群作用为 $h_\sigma \times \mathrm{id}_D = \mathrm{id}_D$，则 $E$ 上的群作用必为恒等作用 $a_\sigma = \mathrm{id}_E$。
- **层与群作用构造**：
  - 取 $S = \{0, 1\}^\mathbb{N}$ 为 Cantor 空间（$S \in \mathrm{Prof}_U$），取无不动点的连续对合：
    $$ \tau: S \longrightarrow S, \quad \tau(x_1, x_2, \dots) = (1 - x_1, x_2, \dots) $$
  - 考虑可表示层 $h_S$ 以及离散集 $|S|$ 对应的常值层 $\underline{|S|}$。典范单态射 $\iota: \underline{|S|} \hookrightarrow h_S$ 将局部常值映射包含入连续映射。
  - 在层范畴 $\mathcal{C}$ 中取商层（推出层）：
    $$ K = h_S / \underline{|S|} = h_S \cup_{\underline{|S|}} 1 $$
  - 由于 $\tau$ 是连续同胚且保持局部常值性，$\tau$ 诱导自同构 $\theta: K \to K$，满足 $\theta^2 = \mathrm{id}_K$。
  - 取 $E = K$，$\pi: E \to 1$ 为唯一态射，定义群作用 $a_1 = \mathrm{id}_K, a_\sigma = \theta$。
- **核验题设条件在单点 $*$ 上成立**：
  - 计算单点上的截面集 $E(*)$：
    在单点 $*$ 上，$\underline{|S|}(*) = |S| = h_S(*)$。由于在 $*$ 上的预层推出集为 $|S| \cup_{|S|} 1 = 1$，且单点的覆盖族必包含非空空间，直接计算知层化后 $K(*) = \{*\}$ 仅含单一元素 $e_0$。
  - 对这唯一的 $e_0 \in E(*)$，显然 $\pi(e_0) = *$，$\sigma \pi(e_0) = \pi(e_0)$。
  - 由于 $E(*)$ 是单元素集，自映射 $a_\sigma$ 必固定该唯一点，即 $a_\sigma(e_0) = e_0$。
  - 因此题设条件“对每个 $e \in E(*)$ 及 $\gamma \in \Gamma$，$\gamma \pi(e) = \pi(e) \implies a_\gamma(e) = e$”**完全成立**。
- **核验 $E$ 在 $Q$ 上不可实现**：
  - 检验截面空间 $S$ 上的作用：考虑恒等映射截面 $\mathrm{id}_S \in h_S(S)$ 在 $K(S)$ 中的像 $[\mathrm{id}_S]$。
  - 群作用作用其上给出 $\theta([\mathrm{id}_S]) = [\tau]$。
  - 若 $\theta([\mathrm{id}_S]) = [\mathrm{id}_S]$，则存在 $S$ 的有限开覆盖 $\{U_i \to S\}_{i=1}^n$，使得在每个 $U_i$ 上，要么 $\tau|_{U_i} = \mathrm{id}_S|_{U_i}$，要么两者的像均为有限集。
  - 但因 $\tau$ 全局无不动点，前者对非空开集不可能成立；又因 $S$ 为无限集，必有某个 $U_i$ 的像为无限集，后者亦不可能成立。
  - 故在 $K(S)$ 中 $[\tau] \neq [\mathrm{id}_S]$，从而 $a_\sigma = \theta \neq \mathrm{id}_E$。
  - 综上，$E$ 在 $Q=1$ 上**不可实现**。

---

## S5　局部满射的基底检验

### 1. 结论
**是**（$E$ 必可在 $Q$ 上实现）。

### 2. 论证
1. **态射性质转化**：
   按题设定义，“局部满射”指对每个测试对象的目标截面都在有限覆盖上有提升，在 Grothendieck topos $\mathcal{C}$ 中，这精确等价于态射 $p: B \to Q$ 为**满态射（epimorphism）**。
2. **切片范畴中的保守性**：
   在任意 Grothendieck topos 中，满态射 $p: B \to Q$ 的拉回函子
   $$ p^*: \mathcal{C}_{/Q} \longrightarrow \mathcal{C}_{/B}, \quad X \longmapsto X \times_Q B $$
   是**保守函子（conservative functor）**，即若 $f$ 为 $\mathcal{C}_{/Q}$ 中的态射且 $p^*(f)$ 为同构，则 $f$ 本身必为同构。
3. **典范下降态射的拉回**：
   由 S3，等变层 $E$ 在 $Q$ 上可实现当且仅当典范态射 $\Phi_E: E \to H \times_Q (E/\Gamma)$ 是同构。
   考虑拉回对象 $E_B = E \times_Q B$ 与 $H_B = H \times_Q B$。由 topos 中余极限的泛性质（与拉回交换）：
   $$ E_B/\Gamma = (E \times_Q B)/\Gamma \cong (E/\Gamma) \times_Q B = p^*(E/\Gamma) $$
   因此，拉回对象 $E_B$ 对应的典范态射 $\Phi_{E_B}$ 恰好是 $\Phi_E$ 沿 $p$ 的拉回：
   $$ \Phi_{E_B} \cong p^*(\Phi_E): E \times_Q B \longrightarrow (H \times_Q (E/\Gamma)) \times_Q B $$
4. **同构反映**：
   题设给出 $E \times_Q B$ 作为 $H \times_Q B$ 上的等变对象可在 $B$ 上实现，由 S3 的判据，$\Phi_{E_B} \cong p^*(\Phi_E)$ 是同构。
   由拉回函子 $p^*$ 的保守性，$\Phi_E$ 本身必须是 $\mathcal{C}$ 中的同构。
5. **结论**：
   由 S3，典范同构 $\Phi_E$ 蕴含 $E$ 在 $Q$ 上可实现（实现对象即为 $E/\Gamma$）。

---

## S6　非空基底与全局结论

### 1. 结论
**否**（拉回后可实现不一定反映原 $E$ 可实现）。

### 2. 完整反例
- **设定**：
  取 $T = \{t_1, t_2\}$ 为双点离散空间（$T \in \mathrm{Prof}_U$），$\Gamma = \mathbb{Z}/2\mathbb{Z} = \{1, \sigma\}$ 在 $T$ 上的作用为平凡作用。
  可表示层为 $H = h_{\{t_1, t_2\}} = 1 \amalg 1$，商层亦为 $Q = H/\Gamma = 1 \amalg 1$。
- **基底选取**：
  取 $B = h_* = 1$（单点可表示层，$B \neq \emptyset$），态射 $B \to Q$ 取为包含入第一个连通分支的态射 $i_1: 1 \hookrightarrow 1 \amalg 1 = Q$。
- **等变层构造**：
  令 $E_1 = 1$，配备平凡 $\Gamma$-作用；令 $E_2 = \{0, 1\} = 1 \amalg 1$，配备非平凡交换作用（$\sigma$ 交换 $0$ 和 $1$）。
  令 $E = E_1 \amalg E_2$，投影 $\pi: E \to H$ 将 $E_1$ 打到 $t_1$ 分支，$E_2$ 打到 $t_2$ 分支。显然 $\pi$ 等变。
- **拉回核验**：
  由于 $B$ 映射至第一个分支，拉回 $E \times_Q B \cong E_1 = 1$，相应的 $H \times_Q B \cong 1$。
  在 $E \times_Q B$ 上，$\Gamma$ 的作用是平凡的，故 $E \times_Q B$ 在 $B$ 上**完全可实现**（由 $D_B = 1$ 实现）。
- **全局不可实现核验**：
  然而原层 $E$ 在分支 $t_2$ 上的纤维为 $E_2$，其上的稳定子 $\Gamma_{t_2} = \Gamma$ 具有非平凡作用。由 S2（或 S3 典范态射计算），$\Phi_E$ 在第二个分支上不是同构，故原层 $E$ 在 $Q$ 上**不可实现**。
  因此拉回可实现不能反映全局可实现。

---

### 3. 可用的检验原则整理

综合阶段 S1 至 S6 的论证与结论，整理出层范畴中等变对象下降与基底检验的系统准则：

```
                    ┌──────────────────────────────────────┐
                    │      等变层 E -> H 在 Q 上的实现检验      │
                    └──────────────────┬───────────────────┘
                                       │
        ┌──────────────────────────────┴──────────────────────────────┐
        ▼                                                             ▼
【整体性下降判据 (S3)】                                      【自由与离散特化 (S1, S2)】
Φ_E: E ≅ H ×_Q (E/Γ) ⇔ Stab 平凡作用于 E                     Γ 有限自由 ──► 自动全可实现 (S1)
                                                            有限离散集 ──► 纤维单点检验充分 (S2)
        │
        ▼
【基底检验与转移准则 (S5, S6)】
B -> Q 局部满射 (S5) ──► 保守反映：拉回可实现 ⇔ 全局可实现
B -> Q 非满射 (S6)   ──► 存在盲区：局域实现 ⇏ 全局实现
单点截面检验 (S4)   ──► 拓扑盲区：无法分离高阶截面，不可行
```

1. **局部满射的充分反映原则（Epimorphism Principle, S5）**：
   基底变换 $B \to Q$ 能完全反映可实现性的充要条件是其为层范畴中的满态射（局部满射）。此时拉回函子保守，局部实现等价于全局实现。
2. **非满射基底的局限原则（Sub-object Incompleteness, S6）**：
   可表示性与非空性无法替代满射性。若测试基底在 $Q$ 上的像为真子对象，拉回检验仅能反映被覆盖轨道上的行为，对未覆盖轨道上的非平凡稳定子完全钝感。
3. **单点检验与截面分离的适用边界（Evaluation Boundary, S2 vs S4）**：
   - 在有限集合与离散层情形（S2），由于截面完全由点分离，单点检验 $\Gamma_t \curvearrowright X_t$ 是充分且必要的。
   - 在一般的 profinite 空间及一般层情形（S4），拓扑推出与有限型覆盖会导致存在不能由单点截面 $E(*)$ 探测的高阶截面，单点稳定子检验会产生“假阴性”，因而是不充分的。
4. **自由作用的下降无障碍原则（Free Descent, S1）**：
   有限群在 profinite 空间上的自由连续作用诱导有限平展覆盖 $T \to T/\Gamma$。此时核对同构于平凡群胚，稳定子群层平凡，所有等变层皆可自动完全下降。
5. **典范同构的内在判据（Intrinsic Descent Criterion, S3）**：
   无需猜测下降对象 $D$，检验可实现性的普适内在充要条件是典范态射 $\Phi_E: E \to H \times_Q (E/\Gamma)$ 为同构，其等价微观形式是稳定子群层 $\mathrm{Stab} \le H \times \underline{\Gamma}$ 在 $E$ 上平凡作用。
