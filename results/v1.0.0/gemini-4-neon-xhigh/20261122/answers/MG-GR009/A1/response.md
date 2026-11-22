以下按共同设定及 **S1–S6** 逐阶段作答。为避免符号冲突，下文统一用 $S, S', S_i, T_j$ 表示 $\mathbf{Prof}_U$ 中的测试对象，$U \in V$ 仅表示给定的 Grothendieck 宇宙；$*$ 表示单点空间（亦表示终层 $h_*$），$\emptyset$ 表示空空间（亦表示始层 $h_\emptyset$）。对于态射 $u : S' \to S$ 与截面 $s \in F(S)$，简记 $s|_{S'} := F(u)(s)$。

---

## 预备事实（仅用共同设定）

先建立后续各阶段共用的站点与层论基础，确保所有援引的标准定理均说明其适用条件：

1. **$V$-小站点结构与有限极限/余积**。每个对象 $(X,\tau)\in\mathbf{Prof}_U$ 满足 $X\in U$、$\tau\subset \mathcal{P}(X)\in U$，故 $(X,\tau)\in U$；每个连续映射亦属于 $U$。由 $U\in V$ 且 $V$ 为 Grothendieck 宇宙，$\mathcal{P}(U)\in V$，因此 $\mathbf{Prof}_U$ 是 **$V$-小范畴**。在 ZFC 下，$\mathbf{Prof}_U$ 具有全部有限极限（由遗忘函子到 $\mathbf{Top}$ 创建：有限个紧 Hausdorff 全不连通空间的积及连续映射的等化子作为闭子空间仍属于 $\mathbf{Prof}_U$）及有限余积（有限不交并，空余积为 $\emptyset$），且拉回对有限余积分配。有限联合满射族（空空间含空覆盖）满足同构封闭、拉回稳定（拉回在底层集合上计算）与复合封闭，构成 $\mathbf{Prof}_U$ 上的 Grothendieck 前拓扑，生成 Grothendieck 拓扑 $J$。
2. **层条件的等价刻画与次典范性**。预层 $F : \mathbf{Prof}_U^{\mathrm{op}} \to \mathbf{Set}_V$ 是层当且仅当：
   - (i) $F(\emptyset)\cong *$（对应 $\emptyset$ 的空覆盖）；
   - (ii) $F(S_1\sqcup S_2)\xrightarrow{\sim} F(S_1)\times F(S_2)$（对应覆盖 $\{S_1\hookrightarrow S_1\sqcup S_2,\ S_2\hookrightarrow S_1\sqcup S_2\}$）；
   - (iii) 对每个连续满射 $p: S'\twoheadrightarrow S$，序列 $F(S)\to F(S')\rightrightarrows F(S'\times_S S')$ 是等化子。
   
   （由 $\{p_i:S_i\to S\}_{i=1}^n$ 合并为单满射 $\bigsqcup_{i=1}^n S_i\twoheadrightarrow S$ 及 $( \bigsqcup S_i)\times_S(\bigsqcup S_j)\cong \bigsqcup_{i,j}(S_i\times_S S_j)$ 立得二者等价。）

   对任意 $T\in\mathbf{Prof}_U$，可表示预层 $h_T(S)=C(S,T)$ 显然满足 (i)(ii)；对任意连续满射 $p:S'\twoheadrightarrow S$，因 $S'$ 紧且 $S$ Hausdorff，$p$ 是闭满射从而是拓扑商映射，故连续映射 $S'\to T$ 唯一分解过 $p$ 当且仅当其在 $S'\times_S S'$ 上等化两投影。由此 $h_T$ 是层，站点次典范；由 Yoneda 引理（适用于局部 $V$-小范畴 $\mathbf{Prof}_U$），嵌入 $h:\mathbf{Prof}_U\hookrightarrow \mathcal{C}$ 忠实满且保持全部已有极限（特别地保持有限极限）。
3. **层化函子**。因为 $(\mathbf{Prof}_U, J)$ 是 $V$-小站点，且 $V$ 为 Grothendieck 宇宙故 $\mathbf{Set}_V$ 具有全部 $V$-小极限与余极限且 $V$-小滤过余极限与有限极限交换，标准的 Grothendieck 加构造 $P\mapsto P^+$（其中 $P^+(S)=\varinjlim_{\mathcal{R}\in J(S)^{\mathrm{op}}}\mathrm{Hom}_{\mathbf{PSh}}(\mathcal{R},P)$，且由有限联合满射族 $\{p_i:S_i\to S\}_{i=1}^n$ 生成的筛 $\mathcal{R}$ 满足 $\mathrm{Hom}_{\mathbf{PSh}}(\mathcal{R},P)\cong \mathrm{Eq}(\prod_i P(S_i)\rightrightarrows\prod_{i,j}P(S_i\times_S S_j))$）给出层化函子 $a=(-)^{++}:\mathbf{PSh}_V(\mathbf{Prof}_U)\to\mathcal{C}$。$a$ 是包含函子 $\mathcal{C}\hookrightarrow\mathbf{PSh}_V(\mathbf{Prof}_U)$ 的左伴随，且保持有限极限。特别地，若预层 $P$ 是**分离的**（对每个覆盖 $\{S_i\to S\}$ 含 $\emptyset$ 的空覆盖，限制映射 $P(S)\to\prod_i P(S_i)$ 单射），则 $P^+\cong a(P)$ 已是层，且单位 $\eta_P : P\to P^+$ 逐对象单射。
4. **群作用与等变层记号**。记 $\mathcal{C}^\Gamma_{/H}$ 为 $H$ 上 $\Gamma$-等变层 $(E,\pi,a)$ 及 $H$ 上等变态射组成的范畴。离散群 $\Gamma$ 作用在 $T\in\mathbf{Prof}_U$ 上是指群同态 $\Gamma\to\mathrm{Aut}_{\mathbf{Prof}_U}(T)=\mathrm{Homeo}(T)$。

---

## S1　有限群的自由作用

本阶段附加条件：$\Gamma$ 有限，且在 $T\in\mathbf{Prof}_U$ 上自由作用。

### 1. Profinite 轨道空间 $T/\Gamma$ 的构造与验证

令 $T/\Gamma$ 为 $T$ 在 $\Gamma$ 作用下的轨道集合，赋予商映射 $\pi_T : T \twoheadrightarrow T/\Gamma$ 诱导的商拓扑（$W\subset T/\Gamma$ 开当且仅当 $\pi_T^{-1}(W)$ 在 $T$ 中开）。验证 $T/\Gamma \in \mathbf{Prof}_U$：

- **$U$-小性**：$T/\Gamma$ 可视作 $\mathcal{P}(T)$ 的子集（每个轨道是 $T$ 的子集），由 $T\in U$ 得 $\mathcal{P}(T)\in U$，故 $T/\Gamma\in U$，其拓扑属于 $\mathcal{P}(\mathcal{P}(T/\Gamma))\in U$。
- **紧性**：$T$ 紧且 $\pi_T$ 连续满射，故 $T/\Gamma$ 紧。
- **$\pi_T$ 既是开映射又是闭映射**：对任意子集 $A\subset T$，$\pi_T^{-1}(\pi_T(A))=\bigcup_{\gamma\in\Gamma}\gamma(A)$。因为每个 $\gamma\in\Gamma$ 是同胚且 $\Gamma$ **有限**，若 $A$ 开（或闭），则该有限并仍开（或闭），由商拓扑定义 $\pi_T(A)$ 开（或闭）。
- **引理（紧 Hausdorff 全不连通空间的闭开基）**：对紧 Hausdorff 全不连通空间 $T$ 中任意一点 $x$ 及开邻域 $O\ni x$，存在闭开邻域 $W$ 满足 $x\in W\subset O$。
  - *证明*：令 $\mathcal{F}$ 为 $x$ 的所有闭开邻域族，$Q_x:=\bigcap_{C\in\mathcal{F}} C$。$\mathcal{F}$ 非空（$T\in\mathcal{F}$）且对有限交封闭。断言 $Q_x$ 连通：若 $Q_x=A\sqcup B$ 其中 $A,B$ 在闭集 $Q_x$ 中闭（因而在 $T$ 中闭）且 $x\in A$，因紧 Hausdorff 空间 $T$ 正规，存在不交开集 $O_1\supset A, O_2\supset B$；于是 $\bigcap_{C\in\mathcal{F}}(C\setminus(O_1\cup O_2))=\emptyset$，由 $T$ 的紧性与 $\mathcal{F}$ 的有限交封闭性，存在 $C\in\mathcal{F}$ 使得 $C\subset O_1\cup O_2$。此时 $C\cap O_1=C\setminus O_2$ 是含 $x$ 的闭开集，故 $C\cap O_1\in\mathcal{F}$，推出 $Q_x\subset O_1$，从而 $B=\emptyset$。因 $T$ 全不连通，故 $Q_x=\{x\}$。再由 $\bigcap_{C\in\mathcal{F}}(C\setminus O)=\emptyset$ 及紧性即得某个 $W\in\mathcal{F}$ 满足 $W\subset O$。$\square$
- **Hausdorff 性与全不连通性（一并由闭开分离证得）**：任取两个不同轨道 $\Gamma x \neq \Gamma y$（若 $T=\emptyset$ 则空成立）。对每对 $(\gamma_1,\gamma_2)\in\Gamma\times\Gamma$，有 $\gamma_1 x\neq \gamma_2 y$，由上述引理存在闭开集 $W_{\gamma_1,\gamma_2}\subset T$ 使得 $\gamma_1 x\in W_{\gamma_1,\gamma_2}$ 且 $\gamma_2 y\notin W_{\gamma_1,\gamma_2}$。令
  $$W_0 := \bigcap_{\gamma_1,\gamma_2\in\Gamma}\gamma_1^{-1}(W_{\gamma_1,\gamma_2}), \qquad W := \bigcup_{\gamma\in\Gamma}\gamma(W_0).$$
  因 $\Gamma$ 有限且以同胚作用，$W_0$ 与 $W$ 均为 $T$ 中的**闭开集**；显然 $W$ 是 $\Gamma$-不变的，包含 $\Gamma x$，且对任意 $\gamma_1,\gamma_2\in\Gamma$ 有 $\gamma_1(W_0)\subset W_{\gamma_1,\gamma_2}\not\ni \gamma_2 y$，故 $W\cap \Gamma y=\emptyset$。因 $\pi_T^{-1}(\pi_T(W))=W$ 闭开，故 $\pi_T(W)$ 是 $T/\Gamma$ 中包含 $\Gamma x$ 且不含 $\Gamma y$ 的闭开集。于是 $\pi_T(W)$ 与 $(T/\Gamma)\setminus\pi_T(W)$ 既是分离 $\Gamma x,\Gamma y$ 的不交开邻域（证明 Hausdorff 性），又表明任意两点不能同属一个连通分支（证明全不连通性）。

因此 $T/\Gamma \in \mathbf{Prof}_U$。

### 2. 证明 $h_{T/\Gamma}$ 是层商

令 $Q := h_{T/\Gamma}$，$q := h_{\pi_T} : H = h_T \to Q$。由 $\pi_T\circ\gamma=\pi_T$ 得 $q\circ h_\gamma = q$（$\forall\gamma\in\Gamma$）。我们证明对任意层 $Y\in\mathcal{C}$，预复合 $q^*$ 给出自然双射 $\mathrm{Hom}_{\mathcal{C}}(Q,Y)\xrightarrow{\sim}\mathrm{Hom}_{\mathcal{C}}(H,Y)^\Gamma$。

- 由 Yoneda 引理，对任意层 $Y\in\mathcal{C}$，有自然同构 $\mathrm{Hom}_{\mathcal{C}}(h_{T/\Gamma},Y)\cong Y(T/\Gamma)$ 及 $\mathrm{Hom}_{\mathcal{C}}(h_T,Y)^\Gamma\cong Y(T)^\Gamma := \{y\in Y(T)\mid \forall\gamma\in\Gamma,\ Y(\gamma)(y)=y\}$，且 $q^*$ 对应于 $Y(\pi_T): Y(T/\Gamma)\to Y(T)$。
- 因 $\pi_T:T\twoheadrightarrow T/\Gamma$ 是 $\mathbf{Prof}_U$ 中的连续满射（单元素覆盖），$Y$ 的层条件给出等化子序列：
  $$Y(T/\Gamma) \xrightarrow{\ Y(\pi_T)\ } Y(T) \underset{Y(\mathrm{pr}_2)}{\overset{Y(\mathrm{pr}_1)}{\rightrightarrows}} Y(T\times_{T/\Gamma} T).$$
- 考虑有限不交并上的连续映射
  $$\Phi_T : \bigsqcup_{\gamma\in\Gamma} T \longrightarrow T\times_{T/\Gamma} T, \qquad (\gamma,t)\longmapsto (\gamma t, t).$$
  因 $\Gamma$ 有限，$\bigsqcup_{\gamma\in\Gamma} T\in\mathbf{Prof}_U$。对任意 $(t_1,t_2)\in T\times_{T/\Gamma} T$，有 $\pi_T(t_1)=\pi_T(t_2)$，故存在 $\gamma\in\Gamma$ 使 $t_1=\gamma t_2$；又因作用**自由**，此 $\gamma$ 唯一。因此 $\Phi_T$ 是紧 Hausdorff 空间之间的连续双射，从而是同胚（$\mathbf{Prof}_U$ 中的同构）。
- 由 $Y$ 是层且 $\Gamma$ 有限，有同构 $Y(T\times_{T/\Gamma} T)\xrightarrow[\sim]{Y(\Phi_T)} Y\bigl(\bigsqcup_{\gamma\in\Gamma} T\bigr)\cong \prod_{\gamma\in\Gamma} Y(T)$，在此同构下 $Y(\mathrm{pr}_1)$ 对应 $y\mapsto (Y(\gamma)(y))_{\gamma\in\Gamma}$，而 $Y(\mathrm{pr}_2)$ 对应 $y\mapsto (y)_{\gamma\in\Gamma}$。

因此 $Y(\mathrm{pr}_1), Y(\mathrm{pr}_2)$ 的等化子恰好是 $Y(T)^\Gamma$，即 $Y(\pi_T): Y(T/\Gamma)\xrightarrow{\sim} Y(T)^\Gamma$ 为自然双射。故 $h_{T/\Gamma}$ 是 $H$ 的层商。

### 3. 证明每个等变层 $E \to H$ 都在 $Q = h_{T/\Gamma}$ 上实现

任取等变层 $(E,\pi,a)\in\mathcal{C}^\Gamma_{/H}$。直接构造层 $D\to Q$ 如下：

对每个 $S\in\mathbf{Prof}_U$ 与每个 $f\in Q(S)=C(S,T/\Gamma)$，令 $S_T := S\times_{T/\Gamma} T\in\mathbf{Prof}_U$，配两投影 $p_S:S_T\to S$ 和 $\tilde{f}:S_T\to T$，以及自由 $\Gamma$-作用 $\mathrm{id}_S\times \gamma : S_T\to S_T$。定义
$$D_f(S) := \bigl\{\, e\in E(S_T) \ \big|\ \pi_{S_T}(e)=\tilde{f}\ \text{且}\ \forall\gamma\in\Gamma,\ E(\mathrm{id}_S\times\gamma)(e)=a_{\gamma,S_T}(e)\,\bigr\},$$
并令 $D(S) := \bigsqcup_{f\in Q(S)} D_f(S)$，配映射 $p_S^D : D(S)\to Q(S)$，$(f,e)\mapsto f$。（因 $Q(S)\in U\subset V$ 且 $E(S_T)\in V$，有 $D(S)\in V$。）

- **预层结构**：对态射 $u:S'\to S$，诱导出 $\Gamma$-等变映射 $u\times\mathrm{id}_T : S'_T \to S_T$（对 $f'=f\circ u$），满足 $\tilde{f}\circ(u\times\mathrm{id}_T)=\widetilde{f'}$，故拉回 $E(u\times\mathrm{id}_T)$ 将 $D_f(S)$ 映入 $D_{f\circ u}(S')$，使 $D$ 成为预层且 $p^D: D\to Q$ 为预层态射。
- **$D$ 是层**：设 $\{u_i:S_i\to S\}_{i=1}^n$ 是有限联合满射族。因 $Q=h_{T/\Gamma}$ 是层，只需固定 $f\in Q(S)$（记 $f_i=f\circ u_i$）检验 $D_f(S)\to\prod_i D_{f_i}(S_i)\rightrightarrows\prod_{i,j} D_{f_{ij}}(S_i\times_S S_j)$ 为等化子。由于 $\{u_i\times\mathrm{id}_T: (S_i)_T\to S_T\}_{i=1}^n$ 仍是有限联合满射族（覆盖在拉回下稳定），且两两纤维积为 $(S_i\times_S S_j)_T$，由 $E$ 是层可知相容族 $(e_i\in E((S_i)_T))$ 唯一黏合为 $e\in E(S_T)$。再由 $H$ 与 $E$ 的层分离性，$\pi(e)=\tilde{f}$ 及 $E(\mathrm{id}_S\times\gamma)(e)=a_\gamma(e)$ 当且仅当它们在每个 $(S_i)_T$ 上成立。故 $D\in\mathcal{C}$。
- **构造等变同构 $\Theta : H\times_Q D \xrightarrow{\sim} E$**：
  对任意 $S\in\mathbf{Prof}_U$，$(H\times_Q D)(S)$ 的元素是 $(g, (f, e))$，其中 $g\in C(S,T)$，$f=\pi_T\circ g\in Q(S)$，$e\in D_f(S)\subset E(S_T)$。注意 $(\mathrm{id}_S, g): S\to S_T$ 是 $p_S:S_T\to S$ 的截面，定义
  $$\Theta_S : (H\times_Q D)(S) \longrightarrow E(S), \qquad (g, (\pi_T\circ g, e)) \longmapsto E(\mathrm{id}_S, g)(e).$$
  - *自然性*：由 $E$ 的函子性及 $(u\times\mathrm{id}_T)\circ(\mathrm{id}_{S'}, g\circ u)=(\mathrm{id}_S, g)\circ u$ 立得 $\Theta$ 是层态射。
  - *在 $H$ 上*：$\pi_S(E(\mathrm{id}_S, g)(e))=H(\mathrm{id}_S, g)(\pi_{S_T}(e))=H(\mathrm{id}_S, g)(\tilde{f})=\tilde{f}\circ(\mathrm{id}_S,g)=g$。
  - *$\Gamma$-等变性*：对 $\delta\in\Gamma$，注意 $(\mathrm{id}_S, h_\delta(g))=(\mathrm{id}_S\times\delta)\circ(\mathrm{id}_S, g)$ 且 $\pi_T\circ h_\delta(g)=\pi_T\circ g=f$，于是
    $$\Theta_S\bigl(h_\delta(g),(f,e)\bigr)=E(\mathrm{id}_S, g)\bigl(E(\mathrm{id}_S\times\delta)(e)\bigr)=E(\mathrm{id}_S, g)\bigl(a_{\delta,S_T}(e)\bigr)=a_{\delta,S}\bigl(\Theta_S(g,(f,e))\bigr).$$
  - *逐对象双射（从而为层同构）*：固定 $g\in C(S,T)$，令 $f=\pi_T\circ g$。构造映射
    $$\alpha_g : \bigsqcup_{\gamma\in\Gamma} S \longrightarrow S_T = S\times_{T/\Gamma} T, \qquad (\gamma, s)\longmapsto (s,\ \gamma\cdot g(s)).$$
    因 $\Gamma$ 有限，$\bigsqcup_{\gamma\in\Gamma} S\in\mathbf{Prof}_U$，且 $\alpha_g$ 连续。对任意 $(s,t)\in S_T$，由 $\pi_T(t)=\pi_T(g(s))$ 及 $\Gamma$ 在 $T$ 上**自由**，存在唯一 $\gamma\in\Gamma$ 使 $t=\gamma\cdot g(s)$，故 $\alpha_g$ 是紧 Hausdorff 空间间连续双射，从而是同胚。因为 $E$ 是层且 $\Gamma$ 有限，
    $$E(S_T)\xrightarrow[\sim]{\ E(\alpha_g)\ } E\Bigl(\bigsqcup_{\gamma\in\Gamma} S\Bigr)\cong \prod_{\gamma\in\Gamma} E(S), \qquad e \longmapsto (e_\gamma)_{\gamma\in\Gamma},$$
    其中 $e_\gamma = E(\mathrm{id}_S, h_\gamma(g))(e)$。在此对应下：
    - $\pi_{S_T}(e)=\tilde{f} \iff \forall\gamma\in\Gamma,\ \pi_S(e_\gamma)=h_\gamma(g)$；
    - $\forall\delta\in\Gamma,\ E(\mathrm{id}_S\times\delta)(e)=a_\delta(e) \iff \forall\delta,\gamma\in\Gamma,\ e_{\delta\gamma}=a_\delta(e_\gamma) \iff \forall\gamma\in\Gamma,\ e_\gamma=a_\gamma(e_1)$。
    
    若 $e_\gamma=a_\gamma(e_1)$ 且 $\pi_S(e_1)=g$，则自动有 $\pi_S(e_\gamma)=\pi_S(a_\gamma(e_1))=h_\gamma(g)$。因此对每个 $g\in H(S)$，映射 $(g,(\pi_T\circ g, e))\mapsto e_1=\Theta_S(g,(\pi_T\circ g, e))$ 在纤维 $\{g\}\times D_{\pi_T\circ g}(S)$ 与 $\pi_S^{-1}(g)\subset E(S)$ 之间建立双射。对 $g\in H(S)$ 求并，即得 $\Theta_S$ 双射。

由此 $E\cong H\times_Q D$ 作为 $H$ 上等变层，故每个等变层 $E\to H$ 都在 $h_{T/\Gamma}$ 上实现。$\square$

---

## S2　有限集合上的纤维分类

本阶段附加条件：$\Gamma$ 与 $T$ 均有限（视 $T$ 为有限离散空间，$T\in\mathbf{Prof}_U$），$X$ 为有限 $\Gamma$-集合（视作有限离散空间 $X\in\mathbf{Prof}_U$）且 $p:X\to T$ 等变；在每个 $T$-轨道中选定代表 $t$，记代表集为 $I\subset T$，稳定子为 $\Gamma_t:=\{\gamma\in\Gamma\mid \gamma t=t\}$；$Q=h_{T/\Gamma}$。

（注：由 $T$ 有限离散，$h_T\cong\coprod_{t'\in T} *$、$h_{T/\Gamma}\cong\coprod_{t\in I} *$，故对任意层 $Y\in\mathcal{C}$，$\mathrm{Hom}_{\mathcal{C}}(h_T,Y)^\Gamma\cong\mathrm{Map}(T,Y(*))^\Gamma\cong\mathrm{Map}(T/\Gamma,Y(*))\cong\mathrm{Hom}_{\mathcal{C}}(h_{T/\Gamma},Y)$，因此 $Q=h_{T/\Gamma}$ 确为 $H=h_T$ 的层商。）

### 1. $X \to T$ 及其等变态射的分类

记 $\mathbf{FinSet}^\Gamma_{/T}$ 为有限等变映射 $p:X\to T$ 及 $T$ 上 $\Gamma$-等变映射构成的范畴，记 $\mathbf{FinSet}^{\Gamma_t}$ 为有限 $\Gamma_t$-集合及 $\Gamma_t$-等变映射构成的范畴。定义纤维函子
$$\Phi : \mathbf{FinSet}^\Gamma_{/T} \longrightarrow \prod_{t\in I}\mathbf{FinSet}^{\Gamma_t}, \qquad (X\xrightarrow{p} T) \longmapsto (X_t)_{t\in I},\quad f\longmapsto (f|_{X_t})_{t\in I},$$
其中 $X_t := p^{-1}(t)$ 赋予限制的 $\Gamma_t$-作用。

**结论**：$\Phi$ 是范畴等价。
- **准逆函子 $\Psi$**：给定 $(F_t)_{t\in I}\in\prod_{t\in I}\mathbf{FinSet}^{\Gamma_t}$，定义
  $$\Psi\bigl((F_t)_{t\in I}\bigr) := \bigsqcup_{t\in I}\bigl(\Gamma\times_{\Gamma_t} F_t\bigr),$$
  其中 $\Gamma\times_{\Gamma_t} F_t := (\Gamma\times F_t)/\!\sim$（$(\gamma h, y)\sim(\gamma, h\cdot y)$，$\forall \gamma\in\Gamma, h\in\Gamma_t, y\in F_t$），配左 $\Gamma$-作用 $\gamma'\cdot[\gamma,y]=[\gamma'\gamma,y]$ 及 $\Gamma$-等变映射 $p([\gamma,y])=\gamma t\in T$（因 $h\in\Gamma_t$ 固定 $t$ 故良定义）。因 $\Gamma, I, F_t$ 均有限，$\Psi((F_t))$ 有限。对态射 $(g_t:F_t\to F'_t)_{t\in I}$，令 $\Psi((g_t))([\gamma,y])=[\gamma,g_t(y)]$，由 $g_t$ 的 $\Gamma_t$-等变性知其良定义且在 $T$ 上 $\Gamma$-等变。
- **验证 $\Phi\circ\Psi\cong\mathrm{Id}$**：因为不同 $t,t'\in I$ 位于不相交的 $\Gamma$-轨道，$\Psi((F_{t'}))$ 在 $t$ 上的纤维仅来自 $t$ 项中满足 $\gamma t=t$ 即 $\gamma\in\Gamma_t$ 的元素 $[\gamma,y]=[1,\gamma y]$，故 $y\mapsto [1,y]$ 给出自然 $\Gamma_t$-等变双射 $F_t\xrightarrow{\sim}\Psi((F_{t'}))_t$。
- **验证 $\Psi\circ\Phi\cong\mathrm{Id}$**：对 $(X\xrightarrow{p} T)$ 定义自然 $\Gamma$-等变 $T$-映射
  $$\varepsilon_X : \bigsqcup_{t\in I}(\Gamma\times_{\Gamma_t} X_t)\longrightarrow X, \qquad [\gamma, x]\longmapsto \gamma\cdot x.$$
  它是双射：
  - *满射*：对任意 $x\in X$，$p(x)$ 落在唯一 $t\in I$ 的轨道中，即 $p(x)=\gamma t$（$\gamma\in\Gamma$），则 $\gamma^{-1}x\in X_t$ 且 $\varepsilon_X([\gamma,\gamma^{-1}x])=x$。
  - *单射*：若 $\gamma_1 x_1=\gamma_2 x_2$（$x_1\in X_{t_1}, x_2\in X_{t_2}$），施加 $p$ 得 $\gamma_1 t_1=\gamma_2 t_2$，故 $t_1=t_2=:t$ 且 $h:=\gamma_2^{-1}\gamma_1\in\Gamma_t$；于是 $h x_1=x_2$，从而 $[\gamma_1,x_1]=[\gamma_2 h,x_1]=[\gamma_2,hx_1]=[\gamma_2,x_2]$。

**具体分类结果**：
- **对象同构类**：$X\to T$ 在 $T$ 上 $\Gamma$-等变同构意义下由有限 $\Gamma_t$-集合族 $(X_t)_{t\in I}$ 的同构类唯一决定；进一步，每个有限 $\Gamma_t$-集合 $X_t$ 唯一（在置换直和项及子群共轭意义下）分解为有限个传递轨道 $\bigsqcup_j (\Gamma_t/K_{t,j})$（$K_{t,j}\le \Gamma_t$）。
- **态射集**：$\mathrm{Hom}_{\mathbf{FinSet}^\Gamma_{/T}}(X,X')\cong\prod_{t\in I}\mathrm{Hom}_{\Gamma_t}(X_t,X'_t)$（显式对应为 $f\mapsto (f|_{X_t})_{t\in I}$，逆对应将 $(g_t)$ 映至 $\gamma x\mapsto \gamma g_t(x)$，$x\in X_t$）。
- 由 Yoneda 嵌入 $h:\mathbf{Prof}_U\hookrightarrow\mathcal{C}$ 忠实满，可表示等变层 $h_X\to h_T$ 及其在 $H$ 上的等变层态射具有完全相同的分类。

### 2. $h_X$ 在 $Q = h_{T/\Gamma}$ 上实现的充要条件

**命题**：$h_X$ 可在 $Q=h_{T/\Gamma}$ 上实现，**当且仅当**对每个代表 $t\in I$，稳定子 $\Gamma_t$ 在纤维 $X_t$ 上的作用都是**平凡的**（等价地，对所有 $x\in X$ 及 $\gamma\in\Gamma$，$\gamma p(x)=p(x)\implies \gamma x=x$）。

- **必要性（$\implies$）**：设存在层 $D\to Q$ 及 $H$ 上等变同构 $\theta: h_X\xrightarrow{\sim} H\times_Q D$。在单点 $*$ 上取值，得 $T$ 上 $\Gamma$-等变双射 $\theta_* : X=h_X(*)\xrightarrow{\sim} T\times_{T/\Gamma} D(*)$，其中 $\Gamma$ 在右侧作用为 $\gamma\cdot(t',d)=(\gamma t', d)$。对任意 $t\in I$、$x\in X_t$ 及 $\gamma\in\Gamma_t$，因 $\theta$ 在 $H$ 上，可写 $\theta_*(x)=(t,d)$。于是
  $$\theta_*(\gamma x)=\gamma\cdot(t,d)=(\gamma t, d)=(t,d)=\theta_*(x).$$
  由 $\theta_*$ 单射得 $\gamma x=x$，故 $\Gamma_t$ 平凡作用于 $X_t$。
- **充分性（$\Longleftarrow$）**：设对每个 $t\in I$，$\Gamma_t$ 平凡作用于 $X_t$。令有限离散集合 $Y := \bigsqcup_{t\in I} X_t$（自然同构于轨道集 $X/\Gamma$），配映射 $Y\to T/\Gamma$ 将 $X_t$ 映至轨道 $[t]$，取 $D := h_Y \to h_{T/\Gamma}=Q$。
  因 $\Gamma_t$ 平凡作用于 $X_t$，映射 $\Gamma\times_{\Gamma_t} X_t \to (\Gamma/\Gamma_t)\times X_t$，$[\gamma, x]\mapsto (\gamma\Gamma_t, x)$ 是良定义的 $\Gamma$-等变双射（右侧 $\Gamma$ 仅改变第一坐标 $\Gamma/\Gamma_t\cong\Gamma t$）。对 $t\in I$ 求不交并并与 $\varepsilon_X^{-1}$ 复合，得到 $T$ 上 $\Gamma$-等变双射
  $$X \xrightarrow{\ \sim\ } \bigsqcup_{t\in I}\bigl(\Gamma t\times X_t\bigr) \cong T\times_{T/\Gamma} Y$$
  （其中 $\Gamma$ 仅改变 $T$ 坐标）。因为 $h:\mathbf{Prof}_U\to\mathcal{C}$ 保持有限极限（纤维积），即得 $H$ 上等变层同构 $h_X\xrightarrow{\sim} h_T\times_{h_{T/\Gamma}} h_Y = H\times_Q D$。

### 3. 可实现对象的自同构群

设 $h_X$ 可在 $Q=h_{T/\Gamma}$ 上实现，则对每个 $t\in I$，$\Gamma_t$ 平凡作用于 $X_t$，故 $X_t$ 的任意双射都自动 $\Gamma_t$-等变，即 $\mathrm{Aut}_{\Gamma_t}(X_t)=\mathrm{Sym}(X_t)\cong S_{|X_t|}$。结合 Yoneda 嵌入忠实满与分类等价 $\Phi$：
$$\mathrm{Aut}_{\mathcal{C}^\Gamma_{/H}}(h_X) \cong \mathrm{Aut}_{\mathbf{FinSet}^\Gamma_{/T}}(X) \cong \prod_{t\in I}\mathrm{Aut}_{\Gamma_t}(X_t) = \prod_{t\in I}\mathrm{Sym}(X_t) \cong \prod_{t\in I} S_{|X_t|}$$
（群阶为 $\prod_{t\in I}(|X_t|!)$；若某 $X_t=\emptyset$ 或 $T=\emptyset$，约定 $S_0=\{1\}$ 及空积为 $\{1\}$，公式仍成立）。

此外，若 $h_X\cong H\times_Q D$，由 $Q=\coprod_{t\in I}*$ 可分解 $D=\coprod_{t\in I} D_t$，则 $H\times_Q D\cong \coprod_{t\in I}\coprod_{t'\in\Gamma t} D_t$ 与 $h_X\cong\coprod_{t'\in T} h_{X_{t'}}$ 在 $H=\coprod_{t'\in T}*$ 上同构迫使 $D_t\cong h_{X_t}$，故 $D\cong h_Y$ 且 $\mathrm{Aut}_{\mathcal{C}_{/Q}}(D)\cong\prod_{t\in I}\mathrm{Aut}_{\mathcal{C}}(h_{X_t})\cong\prod_{t\in I}\mathrm{Sym}(X_t)$ 与 $\mathrm{Aut}_{\mathcal{C}^\Gamma_{/H}}(h_X)$ 典范同构。$\square$

---

## S3　一般层的完整下降

本阶段仅用共同设定（$\Gamma$ 为任意 $U$-小离散群，$T\in\mathbf{Prof}_U$ 为任意 profinite 空间）。

### 1. 层商引理与有效满态射引理

先建立两个对所有带 $\Gamma$-作用的层通用的基本引理：

**引理 3.1（一般层商的构造与核对）**。设 $X\in\mathcal{C}$ 带有左 $\Gamma$-作用 $(a_\gamma : X\to X)_{\gamma\in\Gamma}$。对每个 $S\in\mathbf{Prof}_U$，定义子集 $R_X(S)\subset X(S)\times X(S)$ 为：$(x_1,x_2)\in R_X(S)$ 当且仅当存在有限联合满射族 $\{u_i:S_i\to S\}_{i=1}^n$ 及 $\gamma_1,\dots,\gamma_n\in\Gamma$，使得
$$\forall i=1,\dots,n,\qquad x_1|_{S_i} = a_{\gamma_i, S_i}(x_2|_{S_i}).$$
（当 $S=\emptyset$ 时取空覆盖 $n=0$，故 $R_X(\emptyset)=X(\emptyset)\times X(\emptyset)=\{(*,*)\}$。）则：
1. $R_X$ 是 $X\times X$ 的子层，且每个 $R_X(S)$ 是 $X(S)$ 上的等价关系；
2. 商预层 $X_{\mathrm{sep}}(S):= X(S)/R_X(S)$ 是**分离预层**；
3. 令 $X/\Gamma := (X_{\mathrm{sep}})^+ \cong a(X_{\mathrm{sep}})\in\mathcal{C}$，并令 $r_X : X \to X_{\mathrm{sep}} \xrightarrow{\eta} X/\Gamma$ 为复合态射，则：
   - (a) $r_X$ 是 $\Gamma$-不变且**局部满射**的；
   - (b) 对任意层 $Y\in\mathcal{C}$，预复合给出自然双射 $r_X^* : \mathrm{Hom}_{\mathcal{C}}(X/\Gamma, Y)\xrightarrow{\sim}\mathrm{Hom}_{\mathcal{C}}(X, Y)^\Gamma$；
   - (c) 作为 $X\times X$ 的子层，$X\times_{X/\Gamma} X = R_X$。

*证明*：
1. 覆盖在拉回下稳定，故 $R_X$ 是子预层；覆盖在复合下稳定（且 $R_X(\emptyset)=\{(*,*)\}$），故若 $(x_1,x_2)$ 在某有限联合满射族上局部属于 $R_X$，则其本身属于 $R_X$，即 $R_X$ 是子层。自反性取 $\{\mathrm{id}_S\}$ 与 $\gamma=1$；对称性取 $\gamma_i^{-1}$；传递性取两覆盖的纤维积 $\{S_i\times_S S'_j\to S\}$ 与 $\gamma_i\delta_j$。
2. 对 $S=\emptyset$，$X_{\mathrm{sep}}(\emptyset)=\{*\}$ 对空覆盖分离。若 $[x_1],[x_2]\in X_{\mathrm{sep}}(S)$ 在有限联合满射族 $\{T_j\to S\}$ 上一致，则 $(x_1|_{T_j},x_2|_{T_j})\in R_X(T_j)$ 对所有 $j$ 成立；因 $R_X$ 是子层，得 $(x_1,x_2)\in R_X(S)$，即 $[x_1]=[x_2]$。故 $X_{\mathrm{sep}}$ 分离。
3. 依预备事实 3（Grothendieck 层化定理，适用于 $V$-小站点 $\mathbf{Prof}_U$），因 $X_{\mathrm{sep}}$ 分离，$X/\Gamma=(X_{\mathrm{sep}})^+$ 已是层且 $\eta: X_{\mathrm{sep}}\to X/\Gamma$ 逐对象单射。
   - (a) 因 $(a_\gamma(x), x)\in R_X(S)$（取 $\{\mathrm{id}_S\}$ 与 $\gamma$），故 $r_X\circ a_\gamma=r_X$。对任意 $\xi\in (X/\Gamma)(S)=(X_{\mathrm{sep}})^+(S)$，按加构造定义，存在有限联合满射族 $\{S_i\to S\}$ 及相容族 $(c_i\in X_{\mathrm{sep}}(S_i))$ 使 $\xi|_{S_i}=\eta_{S_i}(c_i)$；任取 $c_i$ 在 $X(S_i)$ 中的代表 $x_i$，即有 $r_X(x_i)=\xi|_{S_i}$，故 $r_X$ 局部满射。
   - (b) 由层化伴随与商预层泛性质，$\mathrm{Hom}_{\mathcal{C}}(X/\Gamma,Y)\cong\mathrm{Hom}_{\mathbf{PSh}}(X_{\mathrm{sep}},Y)\cong\{f\in\mathrm{Hom}_{\mathcal{C}}(X,Y)\mid \forall S,\ \forall(x_1,x_2)\in R_X(S),\ f_S(x_1)=f_S(x_2)\}$。若 $f$ 等化 $R_X$，取 $(a_\gamma(x),x)\in R_X(S)$ 即得 $f$ 是 $\Gamma$-不变的；反之若 $f$ 是 $\Gamma$-不变的且 $(x_1,x_2)\in R_X(S)$ 由 $\{S_i\to S\}$ 和 $\gamma_i$ 见证，则在每个 $S_i$ 上 $f(x_1)|_{S_i}=f(a_{\gamma_i}(x_2|_{S_i}))=f(x_2)|_{S_i}$，由 $Y$ 是层得 $f(x_1)=f(x_2)$。故右端恰为 $\mathrm{Hom}_{\mathcal{C}}(X,Y)^\Gamma$。
   - (c) 因 $\eta_S : X_{\mathrm{sep}}(S)\hookrightarrow (X/\Gamma)(S)$ 单射，对任意 $x_1,x_2\in X(S)$，$r_{X,S}(x_1)=r_{X,S}(x_2)\iff [x_1]=[x_2]\text{ in }X_{\mathrm{sep}}(S)\iff (x_1,x_2)\in R_X(S)$。$\square$

**引理 3.2（局部满射为有效满态射）**。设 $p: X\to Z$ 是 $\mathcal{C}$ 中的局部满射。则：
- (a) $p$ 是 $\mathcal{C}$ 中的满态射；
- (b) $p$ 是其核对 $X\times_Z X \rightrightarrows X$ 在 $\mathcal{C}$ 中的余等化子（即 $f:X\to Y$ 唯一分解过 $p$ 当且仅当 $f\circ\mathrm{pr}_1=f\circ\mathrm{pr}_2$）；
- (c) 若 $p$ 同时逐对象单射，则 $p$ 是同构。

*证明*：(a) 若 $g_1\circ p=g_2\circ p : X\to Y$，对任意 $z\in Z(S)$ 在局部满射覆盖 $\{S_i\to S\}$ 上取提升 $x_i\in X(S_i)$，得 $g_1(z)|_{S_i}=g_1(p(x_i))=g_2(p(x_i))=g_2(z)|_{S_i}$，由 $Y$ 是层得 $g_1(z)=g_2(z)$。
(b) 唯一性由 (a) 给出。若 $f:X\to Y$ 满足 $f\circ\mathrm{pr}_1=f\circ\mathrm{pr}_2$，对任意 $z\in Z(S)$，取有限联合满射族 $\{u_i:S_i\to S\}$ 与提升 $x_i\in X(S_i)$ 使 $p(x_i)=z|_{S_i}$。在 $S_i\times_S S_j$ 上有 $p(x_i|_{S_i\times_S S_j})=z|_{S_i\times_S S_j}=p(x_j|_{S_i\times_S S_j})$，故 $(x_i|_{S_i\times_S S_j}, x_j|_{S_i\times_S S_j})\in (X\times_Z X)(S_i\times_S S_j)$，从而 $f(x_i)|_{S_i\times_S S_j}=f(x_j)|_{S_i\times_S S_j}$。由 $Y$ 是层，存在唯一 $g_S(z)\in Y(S)$ 使 $g_S(z)|_{S_i}=f(x_i)$。对两组覆盖与提升取纤维积加细并用 $f\circ\mathrm{pr}_1=f\circ\mathrm{pr}_2$ 与 $Y$ 的分离性知 $g_S(z)$ 与选取无关，由此即得自然态射 $g:Z\to Y$ 满足 $g\circ p=f$。
(c) 若 $p$ 逐对象单射，则 $X\times_Z X=\Delta_X$，对 $\mathrm{id}_X:X\to X$ 用 (b) 得 $g:Z\to X$ 使 $g\circ p=\mathrm{id}_X$，再由 $p\circ g\circ p=p$ 及 (a) 得 $p\circ g=\mathrm{id}_Z$。$\square$

---

### 2. 层商 $Q$ 与 $q:H\to Q$ 的构造

对带 $\Gamma$-作用的层 $H=h_T$ 应用**引理 3.1**，令
$$Q := H/\Gamma = (H_{\mathrm{sep}})^+, \qquad q := r_H : H \longrightarrow Q.$$
则 $q$ 是 $\Gamma$-不变且局部满射的，对每个 $Y\in\mathcal{C}$ 有自然双射 $q^* : \mathrm{Hom}_{\mathcal{C}}(Q,Y)\xrightarrow{\sim}\mathrm{Hom}_{\mathcal{C}}(H,Y)^\Gamma$，且核对为 $H\times_Q H = R_H$。

---

### 3. 任意层 $u: B\to Q$ 上的商结构与拉回对象

对任意层态射 $u: B\to Q$（特别地取 $B=Q, u=\mathrm{id}_Q$ 即回到 $Q$ 本身），定义
$$H_B := H\times_Q B, \qquad q_B := \mathrm{pr}_2 : H_B \longrightarrow B, \qquad h^B_\gamma := (h_\gamma, \mathrm{id}_B) : H_B \longrightarrow H_B\quad(\gamma\in\Gamma).$$
显然 $q_B$ 是 $\Gamma$-不变的。验证以下两条关键性质：

- **(P1) $q_B : H_B\to B$ 是局部满射**：对任意 $b\in B(S)$，因 $q:H\to Q$ 局部满射，对 $u_S(b)\in Q(S)$ 存在有限联合满射族 $\{S_i\to S\}$ 与 $x_i\in H(S_i)$ 使 $q(x_i)=u(b)|_{S_i}=u(b|_{S_i})$，则 $(x_i, b|_{S_i})\in H_B(S_i)$ 为 $b|_{S_i}$ 的提升。
- **(P2) $H_B\times_B H_B = R_{H_B}$**：对任意 $((x_1,b_1),(x_2,b_2))\in H_B(S)\times H_B(S)$（故 $q(x_k)=u(b_k)$）：
  - 若 $b_1=b_2$，则 $q(x_1)=q(x_2)$，即 $(x_1,x_2)\in (H\times_Q H)(S)=R_H(S)$，存在有限联合满射族 $\{S_i\to S\}$ 与 $\gamma_i\in\Gamma$ 使 $x_1|_{S_i}=h_{\gamma_i}(x_2|_{S_i})$，从而 $(x_1,b_1)|_{S_i}=h^B_{\gamma_i}((x_2,b_2)|_{S_i})$，故属 $R_{H_B}(S)$。
  - 反之，若存在有限联合满射族 $\{S_i\to S\}$ 与 $\gamma_i\in\Gamma$ 使 $(x_1,b_1)|_{S_i}=(h_{\gamma_i}(x_2|_{S_i}), b_2|_{S_i})$，则 $b_1|_{S_i}=b_2|_{S_i}$ 对所有 $i$ 成立，由 $B$ 是层得 $b_1=b_2$，即属于 $(H_B\times_B H_B)(S)$。

结合 (P1)(P2) 与引理 3.2(b)，$q_B : H_B\to B$ 也是层商 $H_B/\Gamma$。

记 $\mathcal{C}^\Gamma_{/H_B}$ 为 $H_B$ 上 $\Gamma$-等变层 $(E_B,\pi_B,a^B)$（满足 $\pi_B\circ a^B_\gamma = h^B_\gamma\circ\pi_B$）及其在 $H_B$ 上等变态射构成的范畴。定义拉回函子
$$q_B^* : \mathcal{C}_{/B} \longrightarrow \mathcal{C}^\Gamma_{/H_B}, \qquad (D_B\xrightarrow{p_B} B) \longmapsto \bigl(H_B\times_B D_B,\ \mathrm{pr}_1,\ (h^B_\gamma, \mathrm{id}_{D_B})\bigr).$$
称 $E_B\in\mathcal{C}^\Gamma_{/H_B}$ **在 $B$ 上可实现**，是指其落在 $q_B^*$ 的本质像中（即存在 $D_B\to B$ 及 $\mathcal{C}^\Gamma_{/H_B}$ 中的同构 $E_B\cong q_B^*(D_B)$）。记所有在 $B$ 上可实现的等变层构成的满子范畴为 $\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B}\subset \mathcal{C}^\Gamma_{/H_B}$。当 $B=Q, u=\mathrm{id}_Q$ 时，$H_Q=H, q_Q=q$，即得原范畴 $\mathcal{C}^{\Gamma,\mathrm{real}}_{/H}\subset \mathcal{C}^\Gamma_{/H}$。

---

### 4. 不预选 $D$ 的可实现性充要判据与实现/态射的完整分类（统一对任意 $B\to Q$ 与 $Q$ 成立）

**定理 3.3（一般完整下降与分类定理）**。对任意层态射 $u:B\to Q$（特别地取 $B=Q, u=\mathrm{id}_Q$）：

1. **（不预选 $D_B$ 的可实现性充要判据）** 对象 $(E_B,\pi_B,a^B)\in\mathcal{C}^\Gamma_{/H_B}$ 在 $B$ 上可实现，**当且仅当**它满足如下稳定子平凡条件 $(\star_B)$：
   $$(\star_B) \qquad \forall S\in\mathbf{Prof}_U,\ \forall e\in E_B(S),\ \forall \gamma\in\Gamma:\quad h^B_\gamma(\pi_{B,S}(e)) = \pi_{B,S}(e) \implies a^B_{\gamma,S}(e) = e.$$
   *（等价的内在无元素表述：记不动点层 $H_B^\gamma := \mathrm{Eq}(h^B_\gamma,\mathrm{id}_{H_B})\cong h_{T^\gamma}\times_Q B$，其中 $T^\gamma=\{t\in T\mid \gamma t=t\}\in\mathbf{Prof}_U$ 为闭子空间；则 $(\star_B)$ 等价于：对每个 $\gamma\in\Gamma$，作用 $a^B_\gamma$ 限制在 $E_B\times_{H_B} H_B^\gamma$ 上等于恒等态射。特别当 $B=Q$ 时，判据 $(\star)$ 为：$\forall S\in\mathbf{Prof}_U,\ \forall e\in E(S),\ \forall\gamma\in\Gamma,\ h_\gamma(\pi_S(e))=\pi_S(e)\implies a_{\gamma,S}(e)=e$，即对每个 $\gamma\in\Gamma$，$a_\gamma|_{E\times_H h_{T^\gamma}}=\mathrm{id}$。）*
2. **（分类所有可实现对象与态射）** 函子
   $$q_B^* : \mathcal{C}_{/B} \xrightarrow{\ \sim\ } \mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B}, \qquad (D_B\to B)\longmapsto H_B\times_B D_B$$
   是**范畴等价**，其显式准逆为层商函子
   $$(-)/\Gamma : \mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B} \xrightarrow{\ \sim\ } \mathcal{C}_{/B}, \qquad (E_B,\pi_B,a^B)\longmapsto (E_B/\Gamma \xrightarrow{p_{E_B}} B),$$
   其中 $p_{E_B}: E_B/\Gamma\to B$ 是 $\Gamma$-不变态射 $q_B\circ\pi_B : E_B\to B$ 经 $r_{E_B}: E_B\to E_B/\Gamma$ 的唯一分解。
3. **（单个对象的全部实现之分类）** 对固定的 $E_B\in\mathcal{C}^\Gamma_{/H_B}$，定义其在 $B$ 上的**实现范畴** $\mathrm{Real}_B(E_B)$：对象为二元组 $(D_B\to B,\ \theta: E_B\xrightarrow{\sim} q_B^* D_B)$（$\theta$ 为 $\mathcal{C}^\Gamma_{/H_B}$ 中同构），态射 $(D_B,\theta)\to (D'_B,\theta')$ 为 $\mathcal{C}_{/B}$ 中满足 $q_B^*(g)\circ\theta=\theta'$ 的态射 $g:D_B\to D'_B$。则：
   - 若 $(\star_B)$ 不成立，$\mathrm{Real}_B(E_B)$ 为空；
   - 若 $(\star_B)$ 成立，$\mathrm{Real}_B(E_B)$ 是**可缩群胚**：任意两个实现之间存在唯一同构，且每个实现均与典范实现 $(E_B/\Gamma,\ \psi_{E_B}=(\pi_B, r_{E_B}))$ 唯一同构。
   - 对任意两可实现对象 $E_B\cong q_B^* D_B$、$E'_B\cong q_B^* D'_B$，态射集通过 $q_B^*$ 自然双射：$\mathrm{Hom}_{\mathcal{C}_{/B}}(D_B,D'_B)\xrightarrow{\sim}\mathrm{Hom}_{\mathcal{C}^\Gamma_{/H_B}}(E_B,E'_B)$。

*证明*：

**步骤 A：证明对任意 $(D_B\xrightarrow{p_B} B)\in\mathcal{C}_{/B}$，$\mathrm{pr}_2 : H_B\times_B D_B \to D_B$ 是层商 $(H_B\times_B D_B)/\Gamma$，从而 $q_B^*$ 忠实满且 $((-)/\Gamma)\circ q_B^*\cong\mathrm{Id}_{\mathcal{C}_{/B}}$。**

因 $\mathrm{pr}_2: H_B\times_B D_B\to D_B$ 是局部满射 $q_B:H_B\to B$ 沿 $p_B$ 的拉回，故 $\mathrm{pr}_2$ 也是局部满射（同 (P1) 的论证）。与 (P2) 完全平行地，利用 $H_B\times_B H_B=R_{H_B}$ 与 $D_B$ 是层，直接检验得核对满足
$$(H_B\times_B D_B)\times_{D_B}(H_B\times_B D_B) = R_{H_B\times_B D_B}.$$
由引理 3.2(b)，对任意层 $Y\in\mathcal{C}$，态射 $f:H_B\times_B D_B\to Y$ 唯一分解过 $\mathrm{pr}_2$ 当且仅当 $f$ 等化 $R_{H_B\times_B D_B}$；而如引理 3.1(b) 的证明，这恰等价于 $f$ 是 $\Gamma$-不变的。因此 $\mathrm{pr}_2$ 满足 $(H_B\times_B D_B)/\Gamma$ 的泛性质，诱导 $\mathcal{C}_{/B}$ 中的自然同构 $\varepsilon_{D_B} : (q_B^* D_B)/\Gamma \xrightarrow{\sim} D_B$。

由此证 $q_B^*$ 忠实满：
- *忠实*：若 $g,g':D_1\to D_2$ 在 $B$ 上满足 $q_B^*(g)=q_B^*(g')$，与 $\mathrm{pr}_2:H_B\times_B D_2\to D_2$ 复合得 $g\circ\mathrm{pr}_2=g'\circ\mathrm{pr}_2: H_B\times_B D_1\to D_2$；由 $\mathrm{pr}_2$ 局部满射（引理 3.2(a)）得 $g=g'$。
- *满*：任取 $\phi\in\mathrm{Hom}_{\mathcal{C}^\Gamma_{/H_B}}(H_B\times_B D_1, H_B\times_B D_2)$。因 $\mathrm{pr}_2\circ\phi : H_B\times_B D_1\to D_2$ 是 $\Gamma$-不变的，由 $\mathrm{pr}_2$ 的层商泛性质存在唯一 $g:D_1\to D_2$ 使 $g\circ\mathrm{pr}_2=\mathrm{pr}_2\circ\phi$。又 $p_2\circ g\circ\mathrm{pr}_2=p_2\circ\mathrm{pr}_2\circ\phi=q_B\circ\mathrm{pr}_1\circ\phi=q_B\circ\mathrm{pr}_1=p_1\circ\mathrm{pr}_2$，由 $\mathrm{pr}_2$ 满态射得 $p_2\circ g=p_1$，即 $g\in\mathrm{Hom}_{\mathcal{C}_{/B}}(D_1,D_2)$；比较两分量即见 $q_B^*(g)=\phi$。

**步骤 B：证明判据 $(\star_B)$ 的必要性与充分性，以及 $q_B^*\circ((-)/\Gamma)\cong\mathrm{Id}_{\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B}}$。**

- *必要性*：若存在 $\mathcal{C}^\Gamma_{/H_B}$ 中同构 $\theta: E_B\xrightarrow{\sim} H_B\times_B D_B$，则对任意 $e\in E_B(S)$ 及 $\gamma\in\Gamma$，写 $\theta_S(e)=(z, d)$（必有 $z=\pi_{B,S}(e)$）。若 $h^B_\gamma(z)=z$，则 $\theta_S(a^B_\gamma(e))=(h^B_\gamma(z), d)=(z, d)=\theta_S(e)$，因 $\theta_S$ 单射得 $a^B_\gamma(e)=e$，即 $(\star_B)$ 成立。
- *充分性*：设 $(E_B,\pi_B,a^B)\in\mathcal{C}^\Gamma_{/H_B}$ 满足 $(\star_B)$。由引理 3.1 构造层商 $D_B := E_B/\Gamma$ 及局部满射 $r:=r_{E_B}: E_B\to D_B$（核对 $E_B\times_{D_B} E_B = R_{E_B}$）。因 $q_B\circ\pi_B : E_B\to B$ 是 $\Gamma$-不变的，唯一分解为 $p_{E_B}\circ r$（$p_{E_B}: D_B\to B$）。由此得到 $\mathcal{C}^\Gamma_{/H_B}$ 中的典范自然态射
  $$\psi_{E_B} := (\pi_B, r) : E_B \longrightarrow H_B\times_B D_B = q_B^*(E_B/\Gamma).$$
  （显然 $\mathrm{pr}_1\circ\psi_{E_B}=\pi_B$ 且 $\psi_{E_B}\circ a^B_\gamma=(h^B_\gamma\circ\pi_B, r)=(h^B_\gamma,\mathrm{id}_{D_B})\circ\psi_{E_B}$。）检验 $\psi_{E_B}$ 既逐对象单射又局部满射：
  - *逐对象单射*：设 $e_1,e_2\in E_B(S)$ 满足 $\psi_{E_B,S}(e_1)=\psi_{E_B,S}(e_2)$，即 $\pi_B(e_1)=\pi_B(e_2)$ 且 $r(e_1)=r(e_2)$。由 $E_B\times_{D_B} E_B=R_{E_B}$，存在有限联合满射族 $\{S_i\to S\}$ 与 $\gamma_i\in\Gamma$ 使 $e_1|_{S_i}=a^B_{\gamma_i}(e_2|_{S_i})$。施加 $\pi_B$ 得
    $$\pi_B(e_2|_{S_i}) = \pi_B(e_1|_{S_i}) = \pi_B(a^B_{\gamma_i}(e_2|_{S_i})) = h^B_{\gamma_i}(\pi_B(e_2|_{S_i})).$$
    应用 $(\star_B)$ 得 $a^B_{\gamma_i}(e_2|_{S_i})=e_2|_{S_i}$，从而 $e_1|_{S_i}=e_2|_{S_i}$ 对所有 $i$ 成立。由 $E_B$ 是层得 $e_1=e_2$。
  - *局部满射*（此步甚至无需 $(\star_B)$）：任取 $(z, d)\in (H_B\times_B D_B)(S)$，故 $q_B(z)=p_{E_B}(d)$。因 $r:E_B\to D_B$ 局部满射，存在有限联合满射族 $\{u_i:S_i\to S\}_{i=1}^n$ 与 $e_i\in E_B(S_i)$ 使 $r(e_i)=d|_{S_i}$。在每个 $S_i$ 上有 $q_B(z|_{S_i})=p_{E_B}(d|_{S_i})=p_{E_B}(r(e_i))=q_B(\pi_B(e_i))$，故 $(z|_{S_i}, \pi_B(e_i))\in (H_B\times_B H_B)(S_i)=R_{H_B}(S_i)$（由 (P2)）。于是对每个 $i$ 存在有限联合满射族 $\{v_{ij}:S_{ij}\to S_i\}_{j=1}^{m_i}$ 与 $\gamma_{ij}\in\Gamma$ 使 $z|_{S_{ij}}=h^B_{\gamma_{ij}}(\pi_B(e_i|_{S_{ij}}))$。令 $e'_{ij}:=a^B_{\gamma_{ij}}(e_i|_{S_{ij}})\in E_B(S_{ij})$，则
    $$\pi_B(e'_{ij}) = h^B_{\gamma_{ij}}(\pi_B(e_i|_{S_{ij}})) = z|_{S_{ij}}, \qquad r(e'_{ij}) = r(e_i|_{S_{ij}}) = d|_{S_{ij}},$$
    即 $\psi_{E_B}(e'_{ij})=(z,d)|_{S_{ij}}$ 成立在有限联合满射族 $\{u_i\circ v_{ij}:S_{ij}\to S\}_{i,j}$ 上。

  由引理 3.2(c)，$\psi_{E_B}$ 是 $\mathcal{C}$ 中同构，其逆自动在 $H_B$ 上且 $\Gamma$-等变，故 $\psi_{E_B}$ 是 $\mathcal{C}^\Gamma_{/H_B}$ 中自然同构。

由此 1 与 2 均证毕；3 由 $q_B^* : \mathcal{C}_{/B}\xrightarrow{\sim}\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B}$ 的范畴等价性（特别地忠实满）即得。$\square$

---

### 5. 与基底拉回的相容性

设 $f: B'\to B$ 是 $\mathcal{C}_{/Q}$ 中的任意态射（即满足 $u'=u\circ f: B'\to Q$，特别包含 $B'=B\xrightarrow{u} Q$）。令 $f_H := \mathrm{id}_H\times_Q f : H_{B'}\to H_B$，其在拉回方框中给出 $\Gamma$-等变同构 $H_{B'}\cong H_B\times_B B'$。定义拉回函子：
- $f^* : \mathcal{C}_{/B} \to \mathcal{C}_{/B'}$，$D_B \mapsto D_B\times_B B'$；
- $f_H^* : \mathcal{C}^\Gamma_{/H_B} \to \mathcal{C}^\Gamma_{/H_{B'}}$，$E_B \mapsto E_B\times_{H_B} H_{B'} \cong E_B\times_B B'$（配投影 $\pi_{B'}=(\pi_B,\mathrm{id}_{B'})$ 与 $\Gamma$-作用 $(a^B_\gamma,\mathrm{id}_{B'})$）。

**命题 3.4（与基底拉回相容）**：
1. $f_H^*$ 将 $\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B}$ 映入 $\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_{B'}}$（既可由 $(\star_B)\implies(\star_{B'})$ 直接看出，亦由下述同构即得）。
2. 图表
   $$\begin{array}{ccc}
   \mathcal{C}_{/B} & \xrightarrow[\sim]{\ q_B^*\ } & \mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B} \\
   \Big\downarrow f^* & & \Big\downarrow f_H^* \\
   \mathcal{C}_{/B'} & \xrightarrow[\sim]{\ q_{B'}^*\ } & \mathcal{C}^{\Gamma,\mathrm{real}}_{/H_{B'}}
   \end{array}$$
   在典范自然同构 $\alpha_f : f_H^*\circ q_B^* \xrightarrow{\sim} q_{B'}^*\circ f^*$ 下交换；且该自然同构与态射复合 $B''\xrightarrow{g} B'\xrightarrow{f} B$ 及恒等态射 $\mathrm{id}_B$ 相干（即 $q_{(-)}^*$ 构成 $\mathcal{C}_{/Q}$ 上纤维范畴的等价）。
3. 相应地，在准逆 $(-)/\Gamma$ 上存在典范自然同构 $\beta_f : ((-)/\Gamma)\circ f_H^* \xrightarrow{\sim} f^*\circ ((-)/\Gamma)$（对可实现对象 $E_B\in\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B}$，$(E_B\times_B B')/\Gamma \cong (E_B/\Gamma)\times_B B'$ 在 $\mathcal{C}_{/B'}$ 中自然同构）。

*证明*：
对任意 $(D_B\to B)\in\mathcal{C}_{/B}$，利用纤维积的粘贴/结合律，在任意测试对象 $S\in\mathbf{Prof}_U$ 上定义
$$\alpha_{f, D_B, S} : \bigl((H_B\times_B D_B)\times_{H_B} H_{B'}\bigr)(S) \xrightarrow{\ \sim\ } \bigl(H_{B'}\times_{B'}(D_B\times_B B')\bigr)(S)$$
为 $(( (x,b), d), (x,b')) \longmapsto ((x,b'), (d,b'))$（其中 $b=f(b')$ 且 $q(x)=u(b)=u'(b')$）。显然该映射关于 $S$ 与 $D_B$ 均自然、逐对象双射（逆映射送 $((x,b'),(d,b'))$ 至 $(((x,f(b')),d),(x,b'))$）、保持 $H_{B'}$-坐标 $(x,b')$，且与 $\Gamma$-作用（仅将 $x$ 变为 $h_\gamma(x)$）交换。因此 $\alpha_f : f_H^*\circ q_B^*\xrightarrow{\sim} q_{B'}^*\circ f^*$ 是自然同构。

相干性：对 $B''\xrightarrow{g} B'\xrightarrow{f} B$，在 $S$-截面上将 $\alpha_f$ 与 $\alpha_g$ 复合与直接施加 $\alpha_{f\circ g}$ 均在纤维积标准结合同构下把 $(((x,b),d),(x,b''))$ 映至 $((x,b''),(d,b''))$；对 $f=\mathrm{id}_B$ 显然对应恒等自然变换。

对准逆 $(-)/\Gamma$：对任意 $E_B\in\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B}$，$\Gamma$-不变态射 $(r_{E_B}\circ\mathrm{pr}_1,\mathrm{pr}_2): E_B\times_B B'\to (E_B/\Gamma)\times_B B'$ 由层商泛性质唯一诱导 $\mathcal{C}_{/B'}$ 中态射 $\beta_{f,E_B} : (f_H^* E_B)/\Gamma \to f^*(E_B/\Gamma)$。直接核验各分量即知 $q_{B'}^*(\beta_{f,E_B})\circ \psi_{f_H^* E_B} = \alpha_{f, E_B/\Gamma}\circ f_H^*(\psi_{E_B})$。因 $\psi_{f_H^* E_B}, f_H^*(\psi_{E_B}), \alpha_{f,E_B/\Gamma}$ 均为同构，故 $q_{B'}^*(\beta_{f,E_B})$ 是同构；再由定理 3.3 中 $q_{B'}^*$ 忠实满，得 $\beta_{f,E_B}$ 为自然同构。$\square$

---

## S4　单点上的检验

**判断结论**：**否**（满足单点条件并不必推出 $E$ 可在 $Q$ 上实现）。

### 完整反例构造与核验

1. **群、空间与基底**：
   取有限离散群 $\Gamma := \mathbb{Z}/2 = \{1, \tau\}$（因 $\mathbb{N}\in U$，$\Gamma\in U$），取单点空间 $T := *\in\mathbf{Prof}_U$，赋以平凡 $\Gamma$-作用。
   则 $H = h_* = *$ 为终层，且 $Q = H/\Gamma = *$（显然 $\mathrm{Hom}_{\mathcal{C}}(*,Y)=Y(*)=\mathrm{Hom}_{\mathcal{C}}(*,Y)^\Gamma$）。
   对任意层 $D\to Q=*$，有 $H\times_Q D\cong D$ 且其上 $\Gamma$-作用为**平凡作用**。因此 $H=*$ 上的等变层 $(E,\pi,a)$（即任意层 $E\in\mathcal{C}$ 配对合 $a_\tau: E\to E$）可在 $Q=*$ 上实现，**当且仅当** $a_\tau = \mathrm{id}_E$（亦与 S3 的判据 $(\star)$ 一致，因为 S3 仅用共同设定，此处适用）。

2. **层 $E$ 与对合 $a_\tau$ 的构造**：
   - 令 $K := (\mathbb{Z}/3)^{\mathbb{N}}$，赋予离散三元群 $\mathbb{Z}/3=\{0,1,2\}$ 的可数积拓扑。因 $\mathbb{N}\in U$ 且 $\mathbb{Z}/3\in U$，由 Grothendieck 宇宙对 $U$-小族乘积封闭得 $K\in U$。按 Tychonoff 定理（在 ZFC 下适用，因每个因子 $\mathbb{Z}/3$ 紧），$K$ 紧；作为 Hausdorff 全不连通空间的积，$K$ 是 Hausdorff 且全不连通的（任两不同序列在某分量 $n$ 处不同，投影 $\mathrm{pr}_n:K\to\mathbb{Z}/3$ 给出分离它们的闭开集）。故 $K\in\mathbf{Prof}_U$，且 $K$ 是**无限**紧拓扑 Abel 群。
   - 记 $K_{\mathrm{disc}}$ 为同一底层 Abel 群 $K$ 赋予**离散拓扑**。对每个 $S\in\mathbf{Prof}_U$，每个连续映射 $S\to K_{\mathrm{disc}}$ 都是连续映射 $S\to K$，且形成 $C(S,K)$ 的子群。定义预层 $P_0 : \mathbf{Prof}_U^{\mathrm{op}}\to\mathbf{Set}_V$ 为商群：
     $$P_0(S) := C(S,K) / C(S,K_{\mathrm{disc}})$$
     （因 $C(S,K)\in U\subset V$，故 $P_0(S)\in V$；预复合连续映射保持 $C(-,K_{\mathrm{disc}})$，故 $P_0$ 为良定义预层）。
   - **验证 $P_0$ 是分离预层**：
     对 $S=\emptyset$，$C(\emptyset,K)=C(\emptyset,K_{\mathrm{disc}})=\{*\}$，故 $P_0(\emptyset)=\{0\}$，对空覆盖分离。
     对任意有限联合满射族 $\{u_i:S_i\to S\}_{i=1}^n$（$S\neq\emptyset$ 时 $n\ge 1$），若 $[f],[g]\in P_0(S)$ 满足 $[f\circ u_i]=[g\circ u_i]$（$\forall i$），则令 $h:=f-g\in C(S,K)$，有 $h\circ u_i\in C(S_i,K_{\mathrm{disc}})$（$\forall i$）。合并得连续满射 $u: S':=\bigsqcup_{i=1}^n S_i \twoheadrightarrow S$，于是 $h\circ u: S'\to K_{\mathrm{disc}}$ 连续。因 $S'$ 紧且 $S$ Hausdorff，$u$ 是闭满射从而是商映射，故 $h:S\to K_{\mathrm{disc}}$ 连续，即 $[f]=[g]$ in $P_0(S)$。因此 $P_0$ 分离。
   - **定义 $E$ 与 $\Gamma$-作用**：令 $E := (P_0)^+ \cong a(P_0)\in\mathcal{C}$ 为 $P_0$ 的层化（由预备事实 3，$P_0$ 分离故 $E$ 是层且单位 $\eta_S : P_0(S)\hookrightarrow E(S)$ 逐对象单射）。取反映射 $f\mapsto -f$ 保持 $C(S,K_{\mathrm{disc}})$，诱导预层对合 $\tau_0 : P_0\to P_0$（$[f]\mapsto [-f]$），经层化函子得层对合 $a_\tau := a(\tau_0) : E\to E$（满足 $a_\tau^2=\mathrm{id}_E$ 及 $a_{\tau,S}\circ\eta_S = \eta_S\circ\tau_{0,S}$）。取 $\pi:E\to *$ 为唯一态射，构成 $H=*$ 上的等变层。

3. **核验单点条件成立**：
   证明 $E(*) = \{0\}$。由预备事实 3，$E(*)=(P_0)^+(*)=\varinjlim_{\mathcal{R}\in J(*)^{\mathrm{op}}}\mathrm{Hom}_{\mathbf{PSh}}(\mathcal{R},P_0)$。任一覆盖筛 $\mathcal{R}\in J(*)$ 都包含由某个有限联合满射族 $\{S_i\to *\}_{i=1}^n$ 生成的子筛，故 $E(*)$ 的每个元素都由某个有限联合满射族 $\{S_i\to *\}_{i=1}^n$ 上的相容族 $([f_i]\in P_0(S_i))_{i=1}^n$ 代表，其中相容性为：
   $$\forall i,j,\qquad [f_i\circ\mathrm{pr}_1] = [f_j\circ\mathrm{pr}_2] \quad\text{in } P_0(S_i\times S_j).$$
   对每个 $i\in\{1,\dots,n\}$：
   - 若 $S_i=\emptyset$，则 $P_0(S_i)=\{0\}$，必有 $[f_i]=0$；
   - 若 $S_i\neq\emptyset$，任取一点 $y_0\in S_i$。由 $i=j$ 的相容性，映射 $S_i\times S_i\to K_{\mathrm{disc}}$，$(x,y)\mapsto f_i(x)-f_i(y)$ 连续。预复合连续映射 $S_i\to S_i\times S_i$，$x\mapsto (x,y_0)$，知 $x\mapsto f_i(x)-f_i(y_0)$ 连续映入 $K_{\mathrm{disc}}$；加上常值映射 $f_i(y_0)\in C(S_i,K_{\mathrm{disc}})$，得 $f_i\in C(S_i,K_{\mathrm{disc}})$，即 $[f_i]=0$ in $P_0(S_i)$。

   因此一切相容族均恒为 $0$，从而 $E(*)=\{0\}$。于是对每个 $e\in E(*)$（仅有 $e=0$）与每个 $\gamma\in\Gamma$，均有 $a_\gamma(e)=0=e$，S4 的单点条件成立。

4. **核验 $E$ 在 $Q=*$ 上不可实现**：
   取测试对象 $S = K\in\mathbf{Prof}_U$ 与恒等映射 $\mathrm{id}_K\in C(K,K)$。在 $K=(\mathbb{Z}/3)^{\mathbb{N}}$ 中有
   $$\mathrm{id}_K - (-\mathrm{id}_K) = 2\cdot\mathrm{id}_K = -\mathrm{id}_K.$$
   若 $-\mathrm{id}_K\in C(K,K_{\mathrm{disc}})$，因 $K$ 紧，其像 $(-\mathrm{id}_K)(K)=K$ 在离散空间 $K_{\mathrm{disc}}$ 中紧，迫使 $K$ 有限，与 $K=(\mathbb{Z}/3)^{\mathbb{N}}$ 无限矛盾！故在 $P_0(K)$ 中有 $[\mathrm{id}_K]\neq [-\mathrm{id}_K]=\tau_{0,K}([\mathrm{id}_K])$。

   令 $e := \eta_K([\mathrm{id}_K])\in E(K)$。由 $\eta_K: P_0(K)\hookrightarrow E(K)$ 单射，得
   $$a_{\tau,K}(e) = a_{\tau,K}(\eta_K([\mathrm{id}_K])) = \eta_K(\tau_{0,K}([\mathrm{id}_K])) \neq \eta_K([\mathrm{id}_K]) = e.$$
   从而 $a_\tau\neq\mathrm{id}_E$，故 $E$ **不可在 $Q=*$ 上实现**。$\square$

---

## S5　局部满射的基底检验

**判断结论**：**是**（$E$ 必可在 $Q$ 上实现）。

### 证明

设 $u : B \to Q$ 局部满射，且 $E_B := E\times_Q B \cong E\times_H H_B$（其中 $H_B=H\times_Q B$，$\pi_B=(\pi,\mathrm{id}_B):E_B\to H_B$，$h^B_\gamma=(h_\gamma,\mathrm{id}_B)$，$a^B_\gamma=(a_\gamma,\mathrm{id}_B)$）作为 $H_B$ 上的等变对象可在 $B$ 上实现。

因为 **S3 的定理 3.3** 仅依赖共同设定，此处完全适用：
1. 由 $E_B$ 在 $B$ 上可实现，应用定理 3.3(1) 的必要性（亦可直接由 $E_B\cong H_B\times_B D_B$ 立即验得），$E_B$ 满足条件 $(\star_B)$：对任意 $S'\in\mathbf{Prof}_U$、$\tilde{e}\in E_B(S')$、$\gamma\in\Gamma$，若 $h^B_\gamma(\pi_B(\tilde{e}))=\pi_B(\tilde{e})$，则 $a^B_\gamma(\tilde{e})=\tilde{e}$。
2. 下面检验 $E$ 满足定理 3.3(1) 在 $Q$ 上的充要判据 $(\star)$：任取 $S\in\mathbf{Prof}_U$、$e\in E(S)$ 与 $\gamma\in\Gamma$，假设 $h_\gamma(\pi_S(e))=\pi_S(e)$。
   - 若 $S=\emptyset$，因 $E(\emptyset)=\{*\}$，立得 $a_{\gamma,\emptyset}(e)=e$。
   - 一般地，令 $x := q_S(\pi_S(e))\in Q(S)$。因 $u:B\to Q$ 局部满射，存在有限联合满射族 $\{p_i:S_i\to S\}_{i=1}^n$ 及截面 $b_i\in B(S_i)$，使得
     $$\forall i=1,\dots,n,\qquad u_{S_i}(b_i) = x|_{S_i} = q_{S_i}(\pi_{S_i}(e|_{S_i})).$$
   - 对每个 $i$，由上式得偶对 $\tilde{e}_i := (e|_{S_i}, b_i)\in (E\times_Q B)(S_i)=E_B(S_i)$。计算得
     $$h^B_\gamma(\pi_B(\tilde{e}_i)) = h^B_\gamma(\pi(e|_{S_i}), b_i) = \bigl(h_\gamma(\pi(e))|_{S_i},\ b_i\bigr) = (\pi(e|_{S_i}), b_i) = \pi_B(\tilde{e}_i).$$
   - 对 $\tilde{e}_i\in E_B(S_i)$ 应用 $(\star_B)$，得到
     $$(a_\gamma(e|_{S_i}), b_i) = a^B_\gamma(\tilde{e}_i) = \tilde{e}_i = (e|_{S_i}, b_i) \quad \text{in } E_B(S_i).$$
     取第一分量即得 $a_\gamma(e)|_{S_i} = a_\gamma(e|_{S_i}) = e|_{S_i}$ 对一切 $i=1,\dots,n$ 成立。
   - 因为 $\{p_i:S_i\to S\}_{i=1}^n$ 是覆盖且 $E$ 是层，从而 $a_{\gamma,S}(e)=e$。

因此 $E$ 满足 $(\star)$。由 S3 的定理 3.3(1) 的充分性，$E$ 必可在 $Q$ 上实现。$\square$

---

## S6　非空基底与全局结论

### 1. 判断结论

**否**（仅假设 $B$ 是非空可表示层且有 $B\to Q$，拉回 $E\times_Q B$ 在 $B$ 上可实现**不一定**反映原 $E$ 在 $Q$ 上可实现；即使进一步要求 $B(*)\to Q(*)$ 在点集上是双射，仍不一定反映）。

### 2. 完整反例

#### 反例 A（最简有限反例：遗漏带非平凡稳定子的轨道）

- 取 $\Gamma := \mathbb{Z}/2 = \{1,\tau\}$，$T := \{t_1, t_2\}$（二元离散空间，$T\in\mathbf{Prof}_U$），$\Gamma$ 在 $T$ 上**平凡**作用。此时 $\Gamma, T$ 均有限，由 S2 知 $Q = h_{T/\Gamma} = h_T = h_{\{t_1\}}\sqcup h_{\{t_2\}}$，$q = \mathrm{id}_{h_T}$。
- 取有限离散空间 $X := \{t_1\}\sqcup(\{t_2\}\times\mathbb{Z}/2)\in\mathbf{Prof}_U$，映射 $p:X\to T$ 送 $t_1\mapsto t_1$、$(t_2,g)\mapsto t_2$；令 $\Gamma$ 固定 $t_1$，并在 $\{t_2\}\times\mathbb{Z}/2$ 上作左平移 $\tau\cdot(t_2,g)=(t_2,\tau g)$。令 $E := h_X$，$\pi := h_p : E\to H$，$a_\gamma := h_\gamma$。
- 取 $B := h_{\{t_1\}} = *$（显然是非空可表示层），$u := h_\iota : B\to Q=h_T$ 由包含 $\iota:\{t_1\}\hookrightarrow T$ 诱导。
- **核验拉回在 $B$ 上可实现**：因 $h:\mathbf{Prof}_U\to\mathcal{C}$ 保持有限极限，
  $$H_B = H\times_Q B \cong h_{T\times_T\{t_1\}} = h_{\{t_1\}} = B, \qquad E_B = E\times_Q B \cong h_{X\times_T\{t_1\}} = h_{\{t_1\}} = B,$$
  且 $\Gamma$ 在 $H_B$ 与 $E_B$ 上均平凡作用。于是 $E_B\cong H_B\times_B B$ 等变同构，故 $E_B$ 在 $B$ 上可实现（取 $D_B=B$）。
- **核验 $E$ 在 $Q$ 上不可实现**：在轨道 $t_2$ 处稳定子 $\Gamma_{t_2}=\mathbb{Z}/2$ 非平凡作用于纤维 $X_{t_2}=\{t_2\}\times\mathbb{Z}/2$（具体地，取 $e=(t_2,1)\in X=E(*)$，有 $\tau\pi(e)=t_2=\pi(e)$ 而 $a_\tau(e)=(t_2,\tau)\neq e$）。因 $\Gamma,T,X$ 有限，由 S2（或 S3），$E$ 在 $Q$ 上不可实现。

#### 反例 B（加强反例：即使 $B(*)\to Q(*)$ 是双射，非局部满射仍不反映可实现性）

为说明问题不仅在于“漏点”，给出 $B$ 非空可表示且 $B(*)\to Q(*)$ 为**双射**的反例：
- 沿用 S4 中的 $K=(\mathbb{Z}/3)^{\mathbb{N}}\in\mathbf{Prof}_U$，令 $K_{\mathrm{disc}}$ 为其底层离散群（$U$-小）。取 $U$-小离散群 $\Gamma := K_{\mathrm{disc}}\times(\mathbb{Z}/2)$（记 $\mathbb{Z}/2=\{1,\tau\}$），作用于 $T:=K$ 为 $(k,\varepsilon)\cdot x := k+x$（每个群元是紧群 $K$ 上的平移同胚）。
- **计算 $Q = H/\Gamma$**：按 S3 的引理 3.1，对 $x_1,x_2\in H(S)=C(S,K)$，$(x_1,x_2)\in R_H(S)$ 当且仅当存在有限联合满射族 $\{u_i:S_i\to S\}$ 与 $k_i\in K_{\mathrm{disc}}$ 使 $(x_1-x_2)\circ u_i\equiv k_i$。合并得商映射 $u:\bigsqcup_i S_i\twoheadrightarrow S$，可见 $(x_1,x_2)\in R_H(S)\iff x_1-x_2\in C(S,K_{\mathrm{disc}})$（反之若 $x_1-x_2\in C(S,K_{\mathrm{disc}})$，由 $S$ 紧知其取有限个值，对应有限闭开划分覆盖）。因此 $H_{\mathrm{sep}}(S)=C(S,K)/C(S,K_{\mathrm{disc}})=P_0(S)$ 正是 S4 的分离预层，故 $Q=(P_0)^+$。由 S4 的核验，$Q(*)=\{0\}$ 是单点集，而 $q_K(\mathrm{id}_K)=\eta_K([\mathrm{id}_K])\neq 0_K$ in $Q(K)$（这里 $0_S:=Q(S\to *)(0)\in Q(S)$）。
- **取基底**：令 $B := h_* = *$（非空可表示），$u : B\to Q$ 选出 $0\in Q(*)$。显然 $u_* : B(*)\to Q(*)$ 是**双射**。
- **构造 $E$**：对每个 $S\in\mathbf{Prof}_U$，定义预层 $F_{\mathrm{pre}}(S) := (Q(S)\times\mathbb{Z}/2)/\!\sim_S$，其中仅将 $(0_S, 1)\sim_S (0_S, \tau)$ 黏合；限制映射 $[y,\varepsilon]\mapsto [y|_{S'},\varepsilon]$ 良定义（因 $0_S|_{S'}=0_{S'}$），投影 $p_{\mathrm{pre}}([y,\varepsilon]):=y$ 到 $Q$ 与对合 $\sigma_{\mathrm{pre}}([y,\varepsilon]):=[y,\tau\varepsilon]$ 均良定义且自然。
  - *检验 $F_{\mathrm{pre}}$ 分离*：$F_{\mathrm{pre}}(\emptyset)$ 为单点（因 $Q(\emptyset)=\{0_\emptyset\}$）。若 $[y_1,\varepsilon_1],[y_2,\varepsilon_2]\in F_{\mathrm{pre}}(S)$ 在有限联合满射族 $\{S_i\to S\}$ 上一致，施加 $p_{\mathrm{pre}}$ 并用 $Q$ 是层得 $y_1=y_2=:y$；若 $\varepsilon_1\neq\varepsilon_2$，则每个 $S_i$ 上必有 $y|_{S_i}=0_{S_i}$，再用 $Q$ 是层得 $y=0_S$，故 $[y,\varepsilon_1]=[0_S,\varepsilon_1]=[0_S,\varepsilon_2]=[y,\varepsilon_2]$。
  - 令 $F := (F_{\mathrm{pre}})^+\cong a(F_{\mathrm{pre}})\in\mathcal{C}$，$p_F:=a(p_{\mathrm{pre}}):F\to Q$，$\sigma:=a(\sigma_{\mathrm{pre}}):F\to F$。由 $F_{\mathrm{pre}}$ 分离，单位 $\eta^F_S: F_{\mathrm{pre}}(S)\hookrightarrow F(S)$ 逐对象单射。
  - 对每个 $S\in\mathbf{Prof}_U$，$(F_{\mathrm{pre}}\times_Q *)(S)=\{[0_S,1]\}$ 为单点，故 $F_{\mathrm{pre}}\times_Q *\cong *$；因层化 $a$ 保持有限极限（预备事实 3），得 $F\times_Q *\cong a(F_{\mathrm{pre}}\times_Q *)\cong *$。
  - 定义 $E := H\times_Q F$，$\pi := \mathrm{pr}_1 : E\to H$，配 $\Gamma=K_{\mathrm{disc}}\times(\mathbb{Z}/2)$-作用 $a_{(k,\varepsilon)}(x,w):=(h_k(x),\ \sigma^\varepsilon(w))$（由 $q(h_k(x))=q(x)=p_F(w)=p_F(\sigma^\varepsilon(w))$ 良定义，且 $\pi\circ a_{(k,\varepsilon)}=h_{(k,\varepsilon)}\circ\pi$）。
- **核验拉回在 $B=*$ 上可实现**：
  $$E\times_Q * = (H\times_Q F)\times_Q * \cong (H\times_Q *)\times_*(F\times_Q *) \cong H_B\times_* *,$$
  其中 $\mathbb{Z}/2$ 在 $F\times_Q *=*$ 上平凡作用，$K_{\mathrm{disc}}$ 仅作用于 $H_B$，故 $E\times_Q *$ 在 $B=*$ 上可实现（取 $D_*=*$）。
- **核验 $E$ 在 $Q$ 上不可实现**：取 $S=K$，$x:=\mathrm{id}_K\in H(K)$，$y:=q_K(x)\in Q(K)$（由上 $y\neq 0_K$），$w:=\eta^F_K([y,1])\in F(K)$，则 $e:=(x,w)\in E(K)$。取 $\gamma=(0,\tau)\in\Gamma$，有 $h_\gamma(\pi(e))=h_{(0,\tau)}(x)=x=\pi(e)$，而因 $y\neq 0_K$ 及 $\eta^F_K$ 单射，$a_\gamma(e)=(x,\eta^F_K([y,\tau]))\neq (x,\eta^F_K([y,1]))=e$。由 S3 的定理 3.3(1)，$E$ 在 $Q$ 上不可实现。

---

### 3. 据此前结果整理的可用检验原则

综合 S1–S6，整理出判断等变层 $(E,\pi,a)\in\mathcal{C}^\Gamma_{/H}$ 在 $Q=H/\Gamma$ 上可实现性的完整检验原则体系（下述所有补充命题均给出完整证明）：

#### 原则 1：内在稳定子与固定点轨迹原则（源自 S3、推广 S1）
- **通用充要判据（S3）**：$E$ 在 $Q$ 上可实现 $\iff$ 对一切 $S\in\mathbf{Prof}_U$、$e\in E(S)$、$\gamma\in\Gamma$，$h_\gamma(\pi_S(e))=\pi_S(e)\implies a_{\gamma,S}(e)=e$；等价地，对每个 $\gamma\in\Gamma\setminus\{1\}$，$a_\gamma$ 限制在 $E\times_H h_{T^\gamma}$ 上为恒等态射。
- **任意自由作用自动可实现（S1 的无有限性推广）**：只要 $\Gamma$ 在 $T$ 上**自由**（不要求 $\Gamma$ 有限！），对所有 $\gamma\neq 1$ 有 $T^\gamma=\emptyset$，从而 $h_{T^\gamma}=\emptyset$，$(\star)$ 自动成立（仅在 $S=\emptyset$ 上有截面，此时 $E(\emptyset)=\{*\}$），因此**每个**等变层 $E\to H$ 都在 $Q$ 上可实现，且 $\mathcal{C}_{/Q}\simeq\mathcal{C}^\Gamma_{/H}$。
- **约化到极不连通测试空间**：在 ZFC 下，对任意 $S\in\mathbf{Prof}_U$，离散化集合 $|S|_{\mathrm{disc}}$ 的 Stone–Čech 紧化 $\beta(|S|_{\mathrm{disc}})\subset\mathcal{P}(\mathcal{P}(|S|))\in U$ 是极不连通的 profinite 空间（属于 $\mathbf{Prof}_U$），且存在典范连续满射 $\beta(|S|_{\mathrm{disc}})\twoheadrightarrow S$。由 $E$ 是层，检验 $(\star)$ 只需在所有极不连通 profinite 空间 $S\in\mathbf{Extr}_U$（或 $\{\beta(X)\mid X\in U\}$）上进行。

#### 原则 2：单点检验的适用边界（源自 S2、S4）
- **反面警示（S4）**：对一般层 $E$，仅检验单点截面 $e\in E(*)$ 的稳定子条件**不充分**。
- **具体层单点原则（推广 S2）**：若层 $E$ 是**具体的（由点分离的）**，即对每个 $S\in\mathbf{Prof}_U$，求值映射
  $$\mathrm{ev}_S : E(S) \longrightarrow \mathrm{Map}(|S|, E(*)), \qquad e\longmapsto \bigl(s\mapsto E(s)(e)\bigr)$$
  是单射（特别地，当 $E=h_X$ 为任意可表示层，或可表示层的子层时总成立），则**单点条件已充要**：
  > 对具体层 $E$，$E$ 在 $Q$ 上可实现 $\iff$ 对每个 $e_0\in E(*)$ 及 $\gamma\in\Gamma$，$\gamma\pi(e_0)=\pi(e_0)\implies a_\gamma(e_0)=e_0$。
  - *证明*：必要性显然。反之，设 $e\in E(S)$ 满足 $h_\gamma(\pi(e))=\pi(e)$。对每一点 $s:*\to S$，记 $e_s:=E(s)(e)\in E(*)$，则 $\gamma\pi(e_s)=\pi(e_s)$，由假设 $a_\gamma(e_s)=e_s$，即 $E(s)(a_\gamma(e))=E(s)(e)$ 对所有 $s\in|S|$ 成立；因 $\mathrm{ev}_S$ 单射，得 $a_\gamma(e)=e$，故 $(\star)$ 成立，由 S3 知 $E$ 可实现。$\square$

#### 原则 3：局部满射与族基底下降原则（源自 S3、S5）
- **单基底局部满射原则（S5）**：若 $u:B\to Q$ 局部满射，则 $E$ 在 $Q$ 上可实现 $\iff$ $E\times_Q B$ 在 $B$ 上可实现（且按 S3，此时 $E/\Gamma\in\mathcal{C}_{/Q}$ 与 $(E\times_Q B)/\Gamma\in\mathcal{C}_{/B}$ 满足 $(E/\Gamma)\times_Q B\cong (E\times_Q B)/\Gamma$）。
- **联合局部满射族原则**：设 $\{u_i:B_i\to Q\}_{i\in I}$ 是 $V$-小族态射，且**联合局部满射**（即对任意 $S\in\mathbf{Prof}_U$ 与 $x\in Q(S)$，存在有限联合满射覆盖 $\{S_j\to S\}_{j=1}^n$、指标 $i_j\in I$ 与 $b_j\in B_{i_j}(S_j)$ 使 $u_{i_j}(b_j)=x|_{S_j}$）。则 $E$ 在 $Q$ 上可实现 $\iff$ 对每个 $i\in I$，$E\times_Q B_i$ 在 $B_i$ 上可实现。
  - *证明*：完全仿照 S5，只需在局部提升 $x=q(\pi(e))$ 时用 $b_j\in B_{i_j}(S_j)$ 构造 $(e|_{S_j},b_j)\in(E\times_Q B_{i_j})(S_j)$ 并应用 $(\star_{B_{i_j}})$，再用 $E$ 的层性即得 $a_\gamma(e)=e$。$\square$

#### 原则 4：任意基底 $B\to Q$ 反映全部等变层可实现性的精确充要条件（综合 S3、S5、S6）

记 $u:B\to Q$ 的**层像**为子层 $I\hookrightarrow Q$：对每个 $S\in\mathbf{Prof}_U$，
$$I(S) := \bigl\{\, x\in Q(S)\ \big|\ \exists\text{ 有限联合满射 }\{S_i\to S\}_{i=1}^n\text{ 及 } b_i\in B(S_i)\text{ 使 } u_{S_i}(b_i)=x|_{S_i}\,\bigr\}.$$
（因覆盖拉回稳定且复合封闭，$I$ 是 $Q$ 的子层，且 $u$ 分解为局部满射 $B\to I$ 复合单态射 $I\hookrightarrow Q$。）

**定理 6.1（精确基底反映判据）**。对给定态射 $u:B\to Q$，以下两条件等价：
1. 对**每个**等变层 $E\in\mathcal{C}^\Gamma_{/H}$，只要 $E\times_Q B$ 在 $B$ 上可实现，必有 $E$ 在 $Q$ 上可实现；
2. 对每个 $\gamma\in\Gamma\setminus\{1\}$，拉回 $B\times_Q h_{T^\gamma}\to h_{T^\gamma}$ 是局部满射（等价地，复合态射 $h_{T^\gamma}\xrightarrow{\iota_\gamma} H\xrightarrow{q} Q$ 分解过层像 $I\hookrightarrow Q$）。

*证明*：
- **$(2)\implies (1)$**：设 $E\times_Q B$ 在 $B$ 上可实现。任取 $S\in\mathbf{Prof}_U$、$e\in E(S)$ 及 $\gamma\in\Gamma$ 满足 $h_\gamma(\pi(e))=\pi(e)$。若 $\gamma=1$ 则 $a_1(e)=e$；若 $\gamma\neq 1$，则 $\pi(e)\in h_{T^\gamma}(S)$。由 (2)，对 $\pi(e)$ 存在有限联合满射族 $\{S_i\to S\}$ 与 $b_i\in B(S_i)$ 使 $u(b_i)=q(\pi(e|_{S_i}))$。于是 $(e|_{S_i},b_i)\in(E\times_Q B)(S_i)$ 满足 $h^B_\gamma$-不动条件，由 $(\star_B)$ 得 $a_\gamma(e|_{S_i})=e|_{S_i}$；由 $E$ 是层得 $a_\gamma(e)=e$。按 S3，$E$ 在 $Q$ 上可实现。
- **$(1)\implies (2)$**：用反证法。设存在 $\gamma_0\in\Gamma\setminus\{1\}$ 使得 $q\circ\iota_{\gamma_0}: h_{T^{\gamma_0}}\to Q$ 不分解过 $I\hookrightarrow Q$（注：对 $h_{T^{\gamma_0}}\to Q$ 而言，由 Yoneda 引理，$q\circ\iota_{\gamma_0}$ 分解过 $I$ 当且仅当 $(q\circ\iota_{\gamma_0})(\mathrm{id}_{T^{\gamma_0}})\in I(T^{\gamma_0})$，而后者恰等价于 $B\times_Q h_{T^{\gamma_0}}\to h_{T^{\gamma_0}}$ 局部满射）。
  令 $U_{\mathrm{im}} := H\times_Q I \hookrightarrow H$，因 $q\circ h_\gamma=q$，$U_{\mathrm{im}}$ 是 $\Gamma$-不变子层。
  定义预层 $E_{\mathrm{pre}}(S) := (\Gamma\times H(S))/\!\sim_S$，其中 $(\delta_1,x_1)\sim_S(\delta_2,x_2)$ 当且仅当 $(\delta_1,x_1)=(\delta_2,x_2)$ 或 $x_1=x_2\in U_{\mathrm{im}}(S)$；配投影 $\pi_{\mathrm{pre}}([\delta,x]):=x$ 与 $\Gamma$-作用 $a^{\mathrm{pre}}_\gamma([\delta,x]):=[\gamma\delta, h_\gamma(x)]$（因 $U_{\mathrm{im}}$ 是 $\Gamma$-不变子层故良定义且自然）。定义两截面态射 $s_1^{\mathrm{pre}}, s_{\gamma_0}^{\mathrm{pre}} : H\rightrightarrows E_{\mathrm{pre}}$，$x\mapsto [1,x]$ 与 $x\mapsto [\gamma_0,x]$。
  - 对每个 $S\in\mathbf{Prof}_U$：若 $S=\emptyset$，$H(\emptyset)=U_{\mathrm{im}}(\emptyset)=\{*\}$；若 $S\neq\emptyset$，因 $1\neq\gamma_0$，有 $[1,x]=[\gamma_0,x]\iff x\in U_{\mathrm{im}}(S)$。故预层等化子 $\mathrm{Eq}(s_1^{\mathrm{pre}}, s_{\gamma_0}^{\mathrm{pre}})=U_{\mathrm{im}}$。
  - 又对每个 $S\in\mathbf{Prof}_U$，$(E_{\mathrm{pre}}\times_H U_{\mathrm{im}})(S)\xrightarrow{\pi_{\mathrm{pre}}} U_{\mathrm{im}}(S)$ 是双射（逆为 $x\mapsto [1,x]$），故 $E_{\mathrm{pre}}\times_H U_{\mathrm{im}}\xrightarrow{\sim} U_{\mathrm{im}}$ 为预层等变同构。
  
  施加层化函子 $a$（预备事实 3：$a$ 保持有限极限且 $a(H)=H, a(U_{\mathrm{im}})=U_{\mathrm{im}}$），令 $E:=a(E_{\mathrm{pre}})$、$\pi:=a(\pi_{\mathrm{pre}})$、$a_\gamma:=a(a^{\mathrm{pre}}_\gamma)$、$s_1:=a(s_1^{\mathrm{pre}})$、$s_{\gamma_0}:=a(s_{\gamma_0}^{\mathrm{pre}})$。则：
  1. $E\times_H U_{\mathrm{im}}\cong a(E_{\mathrm{pre}}\times_H U_{\mathrm{im}})\xrightarrow{\sim} U_{\mathrm{im}}$ 等变同构；因 $u:B\to Q$ 分解过 $I$，故
     $$E\times_Q B \cong (E\times_Q I)\times_I B = (E\times_H U_{\mathrm{im}})\times_I B \cong U_{\mathrm{im}}\times_I B \cong H\times_Q B = H_B,$$
     从而 $E\times_Q B$ 在 $B$ 上可实现（取 $D_B=B$）。
  2. 另一方面，$\mathrm{Eq}(s_1, s_{\gamma_0}: H\rightrightarrows E)\cong a(U_{\mathrm{im}})=U_{\mathrm{im}}$，且由 $a^{\mathrm{pre}}_{\gamma_0}\circ s_1^{\mathrm{pre}}=s_{\gamma_0}^{\mathrm{pre}}\circ h_{\gamma_0}$ 得 $a_{\gamma_0}\circ s_1=s_{\gamma_0}\circ h_{\gamma_0}$。取截面 $e := (s_1\circ\iota_{\gamma_0})_{T^{\gamma_0}}(\mathrm{id}_{T^{\gamma_0}})\in E(T^{\gamma_0})$，则 $\pi(e)=\iota_{\gamma_0}$ 为 $h_{\gamma_0}$-不动，且 $a_{\gamma_0}(e)$ 对应 $a_{\gamma_0}\circ s_1\circ\iota_{\gamma_0}=s_{\gamma_0}\circ\iota_{\gamma_0}$。若 $E$ 在 $Q$ 上可实现，则由 $(\star)$ 必有 $s_{\gamma_0}\circ\iota_{\gamma_0}=s_1\circ\iota_{\gamma_0}$，迫使 $\iota_{\gamma_0}: h_{T^{\gamma_0}}\to H$ 分解过 $\mathrm{Eq}(s_1,s_{\gamma_0})=U_{\mathrm{im}}=H\times_Q I$，从而 $q\circ\iota_{\gamma_0}$ 分解过 $I\hookrightarrow Q$，矛盾！$\square$

#### 原则 5：可表示商与有限群情形的显式推论
- **有限群（不要求自由）的可表示商**：当 $\Gamma$ 有限时，S1 中证明 $T/\Gamma\in\mathbf{Prof}_U$ 的论证完全未用到自由性；且连续映射 $\Phi_T:\bigsqcup_{\gamma\in\Gamma} T\twoheadrightarrow T\times_{T/\Gamma} T$ 仍是连续满射（覆盖），对任意层 $Y$ 给出单射 $Y(\Phi_T):Y(T\times_{T/\Gamma} T)\hookrightarrow\prod_{\gamma\in\Gamma} Y(T)$，从而 $Y(T/\Gamma)\xrightarrow{\sim} Y(T)^\Gamma$ 仍成立，即 $Q=h_{T/\Gamma}$ 总成立。
- **可表示基底 $B=h_S\xrightarrow{h_f} Q=h_{\overline{T}}$ 的几何检验**：当 $Q=h_{\overline{T}}$ 可表示（例如 $\Gamma$ 有限时 $\overline{T}=T/\Gamma$）且 $B=h_S$ 可表示时，态射 $u=h_f: h_S\to h_{\overline{T}}$（对应连续映射 $f:S\to\overline{T}$）：
  - 局部满射 $\iff$ $f:S\to\overline{T}$ 是满射（此时必定反映可实现性）；
  - 按定理 6.1，反映全部等变层 $E$ 的可实现性 $\iff$ 像 $f(S)\subset\overline{T}$ 包含所有带非平凡稳定子的轨道，即 $f(S)\supset \bigcup_{\gamma\in\Gamma\setminus\{1\}} \overline{q}(T^\gamma)$（其中 $\overline{q}:T\to\overline{T}$ 对应 $q$）；
  - 特别地，当 $Q=*$ 时（例如 $T$ 有限且 $\Gamma$ 传递作用在 $T$ 上），任意非空可表示层 $B=h_S$ 均存在点 $*\to S$ 给出 $B\to *$ 的截面，故 $B\to *$ 必局部满射，从而必然反映可实现性。$\square$