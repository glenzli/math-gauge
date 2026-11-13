以下在 ZFC 下逐阶段作答。先就共同设定中贯穿全篇的若干基本事实作一简短预备验证，随后按 S1–S6 交付。

---

### 共同设定的基本预备事实

1. **$\mathrm{Prof}_U$ 中的极限、有限余积与 Grothendieck 拓扑 $J$**：
   - 因 $U$ 为 Grothendieck 宇宙，对有限个 $X_i \in \mathrm{Prof}_U$（下层集合在 $U$ 中），积 $\prod_i X_i$、不交并 $\bigsqcup_i X_i$ 及闭子空间仍在 $U$ 中；由于紧 Hausdorff 全不连通空间对任意积、有限不交并及闭子空间封闭，拉回 $X \times_Z Y = \{(x,y)\in X\times Y : f(x)=g(y)\}$（作为闭子空间，因 $Z$ Hausdorff 故对角线闭）及有限余积（含初对象 $\emptyset$）在 $\mathrm{Prof}_U$ 中存在。
   - 有限联合满射族（含 $\emptyset$ 上的空覆盖族 $\emptyset$）满足单位元（单态射族 $\{\mathrm{id}_S\}$）、拉回稳定性（若 $\{U_i\to S\}$ 有限联合满射且 $W\to S$ 连续，则 $\{W\times_S U_i\to W\}$ 在集合论拉回上仍有限联合满射）及复合封闭性，故构成 Grothendieck 前拓扑，生成拓扑 $J$：筛 $R\in J(S)$ 当且仅当 $R$ 包含某个有限联合满射族 $\{U_i\to S\}_{i\in I}$。
   - **空空间上的层值**：对任意层 $F\in\mathcal{C}$，因 $\emptyset$ 容许空覆盖族 $I=\emptyset$，层条件给出 $F(\emptyset) \xrightarrow{\sim} \prod_{i\in\emptyset} F(U_i) = \{*\}$（单点集）。
   - **单点 $*$ 上的覆盖筛**：对任意有限联合满射族 $\{p_i:U_i\to *\}_{i\in I}$，必有 $I\neq\emptyset$ 且存在 $i_0\in I$ 使 $U_{i_0}\neq\emptyset$。任取 $u\in U_{i_0}$，常映射 $c_u:*\to U_{i_0}$ 连续，故 $\mathrm{id}_*=p_{i_0}\circ c_u$ 属于该族生成的筛。于是 $J(*)$ 中唯一的覆盖筛是极大筛 $R_{\max}(*)$。

2. **可表示预层 $h_T$ 是层（$J$ 为子典范拓扑）**：
   - 设 $T\in\mathrm{Prof}_U$。若 $S=\emptyset$，对空覆盖或全空覆盖，$h_T(\emptyset)=\{*\}$ 与匹配族集合（均含唯一元）自然双射。
   - 若 $S\neq\emptyset$ 且 $\{p_i:U_i\to S\}_{i=1}^n$ 有限联合满射（$n\ge 1$），令 $V=\bigsqcup_{i=1}^n U_i\in\mathrm{Prof}_U$，$p=\bigsqcup p_i:V\to S$。因有限个紧空间之并 $V$ 紧，且 $S$ Hausdorff，标准定理（紧空间到 Hausdorff 空间的连续映射为闭映射）在此适用，故 $p$ 为闭满射，从而是拓扑商映射。一族匹配映射 $f_i:U_i\to T$（在 $U_i\times_S U_j$ 上相等）等价于连续映射 $f:V\to T$ 在 $p$ 的纤维上取常值；由商拓扑泛性质，$f$ 唯一分解为连续映射 $\bar{f}:S\to T$。故 $h_T\in\mathcal{C}$。
   - $\mathrm{Prof}_U$ 的对象（取在 $U$ 中实现的代表元，或骨架）构成集合 $\subseteq U\in V$，故 $\mathrm{Prof}_U$ 是 $V$-小局部 $U$-小（从而局部 $V$-小）站点，Yoneda 引理对 $h_T$ 与 $\mathcal{C}$ 适用。且 $h:\mathrm{Prof}_U\to\mathcal{C}$ 保极限。

3. **$\mathcal{C}$ 中的层化存在性与基本性质**：
   - 因 $\mathrm{Prof}_U$ 是 $V$-小站点且 $V$ 为 Grothendieck 宇宙（故 $\mathrm{Set}_V$ $V$-完备且 $V$-余完备），标准加构造 $P\mapsto P^+$ 及层化 $(-)^{++}:\mathrm{PSh}_V(\mathrm{Prof}_U)\to\mathcal{C}$ 存在，为包含函子 $\mathcal{C}\hookrightarrow\mathrm{PSh}_V(\mathrm{Prof}_U)$ 的左伴随。
   - 对任意 $P\in\mathrm{PSh}_V(\mathrm{Prof}_U)$：因 $J(*)=\{R_{\max}(*)\}$ 且 $\mathrm{Match}(R_{\max}(*),P)\cong P(*)$，有 $P^{++}(*)\cong P^+(*)\cong P(*)$。又 $P^+$ 恒为分离预层，故 $P^+(S)\hookrightarrow P^{++}(S)$ 单；从而 $\eta^{++}_S(x)=\eta^{++}_S(y)$（$x,y\in P(S)$）当且仅当存在有限联合满射族 $\{S_i\to S\}$ 使 $x|_{S_i}=y|_{S_i}\in P(S_i)$，且 $P\to P^{++}$ 局部满射（对任 $z\in P^{++}(S)$，由 $P^{++}$ 与 $P^+$ 作为沿 $J(S)$ 的滤过余极限的定义，取两层覆盖族复合即得有限覆盖 $\{S_k\to S\}$ 与 $x_k\in P(S_k)$ 使 $\eta^{++}(x_k)=z|_{S_k}$）。

---

## S1　有限群的自由作用

在本阶段，$\Gamma$ 为有限群并在 $T\in\mathrm{Prof}_U$ 上自由作用。

### 1. 构造 profinite 轨道空间 $T/\Gamma$
令 $T/\Gamma$ 为商集合 $\{\Gamma t : t\in T\}$ 配商拓扑，商映射 $p:T\to T/\Gamma$。
- **$U$-小性**：$T/\Gamma\subseteq \mathcal{P}(T)$，且商拓扑 $\subseteq\mathcal{P}(T/\Gamma)$；由宇宙 $U$ 对幂集和子集封闭，$T/\Gamma$ 及其拓扑均属于 $U$。
- **紧致性**：$T/\Gamma=p(T)$ 为紧空间 $T$ 的连续像，故准紧。
- **Hausdorff 性**：等价关系 $R=\{(t,\gamma t):t\in T,\gamma\in\Gamma\}=\bigcup_{\gamma\in\Gamma}\mathrm{Graph}(\gamma)\subseteq T\times T$。因 $T$ Hausdorff，对角线 $\Delta_T\subseteq T\times T$ 闭，故每个 $\mathrm{Graph}(\gamma)=(\gamma\times\mathrm{id}_T)^{-1}(\Delta_T)$ 闭；又 $\Gamma$ **有限**，故 $R$ 作为有限个闭集之并而闭。同时对任意开集 $W\subseteq T$，$p^{-1}(p(W))=\bigcup_{\gamma\in\Gamma}\gamma(W)$ 开，故 $p$ 是开商映射。若 $x\neq y\in T/\Gamma$，取 $t\in p^{-1}(x),\, s\in p^{-1}(y)$，则 $(t,s)\notin R$，故存在开集 $U_1\ni t,\,U_2\ni s$ 使 $(U_1\times U_2)\cap R=\emptyset$；从而 $p(U_1),p(U_2)$ 是 $x,y$ 的不相交开邻域。故 $T/\Gamma$ 是紧 Hausdorff 空间。
- **全不连通性**：先证紧 Hausdorff 全不连通空间 $T$ 中任意两点 $u\neq v$ 可被闭开集分离（标准结论“紧 Hausdorff 空间中准连通分支等于连通分支”在此适用，自含论证如下：设 $K(u)$ 为含 $u$ 的全部闭开集之交，则 $K(u)$ 闭从而紧。若 $K(u)=K_1\sqcup K_2$ 为非空闭分解，因紧 Hausdorff 空间正规，存在不相交开集 $V_1\supseteq K_1,\,V_2\supseteq K_2$。由紧性，$K(u)\subseteq V_1\cup V_2$ 蕴含存在含 $u$ 的闭开集 $C\subseteq V_1\cup V_2$；但 $C\cap V_1$ 与 $C\cap V_2$ 在 $C$ 中闭开从而在 $T$ 中闭开，含 $u$ 的那一个必含 $K(u)$，与 $K_1,K_2\neq\emptyset$ 矛盾。故 $K(u)$ 连通，由 $T$ 全不连通得 $K(u)=\{u\}$）。
  现取 $x\neq y\in T/\Gamma$ 及 $t\in p^{-1}(x),\,s\in p^{-1}(y)$。轨道 $\Gamma t$ 与 $\Gamma s$ 有限且不相交。对每个 $u\in\Gamma t$ 及 $v\in\Gamma s$ 取闭开集 $C_{u,v}\ni u$ 使 $v\notin C_{u,v}$；由 $\Gamma s,\Gamma t$ 有限，令 $W_0=\bigcup_{u\in\Gamma t}\bigcap_{v\in\Gamma s} C_{u,v}$，则 $W_0$ 在 $T$ 中闭开，满足 $\Gamma t\subseteq W_0$ 且 $W_0\cap\Gamma s=\emptyset$。再令
  $$W:=\bigcap_{\gamma\in\Gamma}\gamma(W_0).$$
  因 $\Gamma$ **有限**且每个 $\gamma$ 是同胚，$W$ 在 $T$ 中闭开；对每 $\gamma\in\Gamma$，$\gamma(\Gamma t)=\Gamma t\subseteq\gamma(W_0)$ 且 $\gamma(W_0)\cap\Gamma s=\gamma(W_0\cap\Gamma s)=\emptyset$（且 $1\in\Gamma$），故 $\Gamma t\subseteq W$ 且 $W\cap\Gamma s=\emptyset$。又显然 $W$ 是 $\Gamma$-不变的，故 $p^{-1}(p(W))=W$ 闭开，从而 $p(W)$ 在 $T/\Gamma$ 中闭开且分离 $x$ 与 $y$。因此 $T/\Gamma$ 的任意连通子集至多含一点，即全不连通。

综上，$T/\Gamma\in\mathrm{Prof}_U$。

### 2. 证明 $h_{T/\Gamma}$ 是层商
记 $Q=h_{T/\Gamma}$，不变态射 $q=h_p:H=h_T\to Q$。
- 首先，$p:T\to T/\Gamma$ 连续满射，故单元素族 $\{p:T\to T/\Gamma\}$ 是 $\mathrm{Prof}_U$ 中的 $J$-覆盖。
- 其次，考虑连续映射
  $$\Phi:\Gamma\times T\longrightarrow T\times_{T/\Gamma} T,\qquad (\gamma,t)\longmapsto (t,\gamma t).$$
  因 $p(\gamma t)=p(t)$，该映射良定义；按定义 $T/\Gamma$ 的每个纤维都是一条 $\Gamma$-轨道，故 $\Phi$ 满射；若 $(t_1,\gamma_1 t_1)=(t_2,\gamma_2 t_2)$，则 $t_1=t_2=:t$ 且 $\gamma_2^{-1}\gamma_1 t=t$，由 $\Gamma$ 在 $T$ 上**自由**得 $\gamma_1=\gamma_2$，故 $\Phi$ 单射。又 $\Gamma$ 有限离散、$T$ 紧故 $\Gamma\times T$ 紧，而 $T\times_{T/\Gamma}T\subseteq T\times T$ Hausdorff，适用紧到 Hausdorff 连续双射即同胚定理，$\Phi$ 为 $\mathrm{Prof}_U$ 中的同胚。
- 设 $Y\in\mathcal{C}$ 为任意层。对覆盖 $\{p:T\to T/\Gamma\}$ 的层条件给出等化子图
  $$Y(T/\Gamma)\xrightarrow{\;p^*\;} Y(T)\underset{\mathrm{pr}_2^*}{\overset{\mathrm{pr}_1^*}{\rightrightarrows}} Y(T\times_{T/\Gamma}T).$$
  利用同胚 $\Phi:\bigsqcup_{\gamma\in\Gamma}T\xrightarrow{\sim} T\times_{T/\Gamma}T$ 与层条件（有限不交并 $\bigsqcup_{\gamma\in\Gamma}T$ 的各分支构成两两交为空的覆盖，且 $Y(\emptyset)=\{*\}$），有 $Y(T\times_{T/\Gamma}T)\cong \prod_{\gamma\in\Gamma}Y(T)$，其下 $\mathrm{pr}_1^*(y)=(y)_{\gamma\in\Gamma}$ 而 $\mathrm{pr}_2^*(y)=(\gamma^* y)_{\gamma\in\Gamma}$。因此 $p^*$ 诱导自然双射
  $$Y(T/\Gamma)\xrightarrow{\;\sim\;} Y(T)^\Gamma:=\{y\in Y(T):\forall\gamma\in\Gamma,\,\gamma^*y=y\}.$$
  由 Yoneda 引理（$h_{T/\Gamma},h_T\in\mathcal{C}$ 且 $\mathrm{Prof}_U$ 局部 $V$-小），$\mathrm{Hom}_{\mathcal{C}}(Q,Y)\cong Y(T/\Gamma)$，$\mathrm{Hom}_{\mathcal{C}}(H,Y)\cong Y(T)$，且预复合 $h_\gamma$ 对应 $\gamma^*$、预复合 $q=h_p$ 对应 $p^*$。故 $q^*:\mathrm{Hom}_{\mathcal{C}}(Q,Y)\xrightarrow{\sim}\mathrm{Hom}_{\mathcal{C}}(H,Y)^\Gamma$ 对 $Y\in\mathcal{C}$ 自然成立，即 $Q=h_{T/\Gamma}$ 是层商 $H/\Gamma$。

### 3. 证明每个等变层 $E\to H$ 都在 $Q=h_{T/\Gamma}$ 上实现
先证 $p:T\to T/\Gamma$ 存在全局连续截面 $s:T/\Gamma\to T$（对 $T=\emptyset$，取空截面即成；下设 $T\neq\emptyset$）：
- 对每 $t\in T$ 与每 $\gamma\in\Gamma\setminus\{1\}$，由自由性 $\gamma t\neq t$。因 $T$ Profinite（前述论证已证任意两点可被闭开集分离），取不相交闭开集 $A_\gamma\ni t,\,B_\gamma\ni\gamma t$，令 $W_\gamma=A_\gamma\cap\gamma^{-1}(B_\gamma)$（含 $t$ 闭开，且 $\gamma(W_\gamma)\cap W_\gamma=\emptyset$）。因 $\Gamma$ **有限**，$U_t:=\bigcap_{\gamma\neq 1}W_\gamma$ 是 $t$ 的闭开邻域，且 $\{\gamma(U_t)\}_{\gamma\in\Gamma}$ 两两不相交（若 $\gamma_1 U_t\cap\gamma_2 U_t\neq\emptyset$ 且 $\gamma_1\neq\gamma_2$，则 $\gamma_2^{-1}\gamma_1 U_t\cap U_t\neq\emptyset$ 矛盾）。
- $p(U_t)$ 在 $T/\Gamma$ 中既开（$p$ 开映射）又闭（$p^{-1}(p(U_t))=\bigsqcup_{\gamma\in\Gamma}\gamma U_t$ 闭），故闭开；$p|_{U_t}:U_t\to p(U_t)$ 是从紧集 $U_t$ 到 Hausdorff 空间 $p(U_t)$ 的连续双射，故为同胚。
- 由 $T/\Gamma$ 紧，取有限子覆盖 $p(U_{t_1}),\dots,p(U_{t_m})$，令 $V_k:=p(U_{t_k})\setminus\bigcup_{j<k}p(U_{t_j})$，得 $T/\Gamma=\bigsqcup_{k=1}^m V_k$ 的有限闭开划分。在 $V_k$ 上定义为 $(p|_{U_{t_k}})^{-1}|_{V_k}$ 即粘合成全局连续截面 $s:T/\Gamma\to T$。
- 由此 $T=\bigsqcup_{\gamma\in\Gamma}\gamma(s(T/\Gamma))$，且 $\Psi:\Gamma\times(T/\Gamma)\to T,\,(\gamma,x)\mapsto\gamma\cdot s(x)$ 是 $\Gamma$-等变同胚（在 $T/\Gamma$ 上）。

现给定任意等变层 $(E,\pi,(a_\gamma)_{\gamma\in\Gamma})$ over $H$。令
$$D:=E\times_{H,h_s} Q$$
为 $\pi:E\to H$ 沿 $h_s:Q\to H$ 的拉回（伴随第二投影 $p_D=\mathrm{pr}_2:D\to Q$）。对任意 $S\in\mathrm{Prof}_U$，
$$D(S)=\{(e,x)\in E(S)\times Q(S):\pi_S(e)=s\circ x\}.$$
构造映射 $\Theta_S:(H\times_Q D)(S)\to E(S)$ 如下：
- 任取 $(h,(e,x))\in(H\times_Q D)(S)$，有 $h:S\to T$、$x:S\to T/\Gamma$、$e\in E(S)$ 满足 $p\circ h=x$ 与 $\pi_S(e)=s\circ x$。
- 利用 $\Psi^{-1}\circ h:S\to\Gamma\times(T/\Gamma)$，第一分量是连续映射 $S\to\Gamma$（$\Gamma$ 离散），故 $S$ 分解为有限闭开划分 $S=\bigsqcup_{\gamma\in\Gamma}S_\gamma$，其中 $S_\gamma=\{u\in S:h(u)=\gamma\cdot s(x(u))\}$。在 $S_\gamma$ 上有 $h|_{S_\gamma}=h_\gamma(s\circ x|_{S_\gamma})=h_\gamma(\pi_{S_\gamma}(e|_{S_\gamma}))$。
- 令 $e'_\gamma:=a_\gamma(e|_{S_\gamma})\in E(S_\gamma)$。因 $\{S_\gamma\hookrightarrow S\}_{\gamma\in\Gamma}$ 是有限联合满射覆盖且两两纤维积 $S_{\gamma_1}\times_S S_{\gamma_2}=\emptyset$（$\gamma_1\neq\gamma_2$），而 $E(\emptyset)=\{*\}$，故 $(e'_\gamma)_{\gamma\in\Gamma}$ 自动满足层匹配条件，唯一粘合为 $\Theta_S(h,(e,x))\in E(S)$。

验证性质：
1. **自然性与在 $H$ 上**：划分 $S=\bigsqcup_{\gamma\in\Gamma}S_\gamma$ 对连续映射 $S'\to S$ 拉回相容，故 $\Theta:H\times_Q D\to E$ 是 $\mathcal{C}$ 中态射。在每块 $S_\gamma$ 上 $\pi(e'_\gamma)=\pi(a_\gamma(e|_{S_\gamma}))=h_\gamma(\pi(e|_{S_\gamma}))=h_\gamma(s\circ x|_{S_\gamma})=h|_{S_\gamma}$，由 $H$ 是层得 $\pi\circ\Theta=\mathrm{pr}_1$。
2. **$\Gamma$-等变性**：对 $\delta\in\Gamma$，$H\times_Q D$ 上的作用将 $(h,(e,x))$ 映至 $(h_\delta(h),(e,x))$，对应 $S$ 的划分中 $S_\gamma$ 变为 $\delta(h)$-坐标处于 $\delta\gamma$ 块（即 $S'_{\delta\gamma}=S_\gamma$），在该块上像为 $a_{\delta\gamma}(e|_{S_\gamma})=a_\delta(a_\gamma(e|_{S_\gamma}))=a_\delta(e'_\gamma)=a_\delta(\Theta_S(h,(e,x)))|_{S_\gamma}$；由层性得 $\Theta\circ(h_\delta\times_Q\mathrm{id}_D)=a_\delta\circ\Theta$。
3. **双射（同构）**：对任意 $e\in E(S)$，记 $h=\pi_S(e):S\to T$，按 $\Psi^{-1}\circ h$ 得闭开划分 $S=\bigsqcup_{\gamma\in\Gamma}S_\gamma$，使 $h|_{S_\gamma}=h_\gamma(s\circ p\circ h|_{S_\gamma})$。令 $\tilde{e}_\gamma:=a_{\gamma^{-1}}(e|_{S_\gamma})$，则 $\pi(\tilde{e}_\gamma)=h_{\gamma^{-1}}(h|_{S_\gamma})=s\circ (p\circ h|_{S_\gamma})$，故 $(h|_{S_\gamma},(\tilde{e}_\gamma,p\circ h|_{S_\gamma}))\in (H\times_Q D)(S_\gamma)$。因两两交为空且 $(H\times_Q D)(\emptyset)=\{*\}$，粘合得 $\Xi_S(e)\in(H\times_Q D)(S)$。在每个 $S_\gamma$ 上 $\Theta\circ\Xi$ 与 $\Xi\circ\Theta$ 皆为恒等，由层性它们互为逆。

因此 $E\cong H\times_Q D$ 作为 $H$ 上的等变层实现（顺带可见 $D\cong E/\Gamma$）。

---

## S2　有限集合上的纤维分类

在本阶段，$\Gamma$ 和 $T$ 均为有限集，$X$ 为有限 $\Gamma$-集合配等变映射 $\pi:X\to T$；选定 $T$ 的 $\Gamma$-轨道代表元集合 $R\subseteq T$，记 $t\in R$ 的稳定子为 $\Gamma_t=\{\gamma\in\Gamma:\gamma t=t\}$。

### 1. $X\to T$ 及其等变态射的分类
将有等变映射 $X\to T$ 的有限 $\Gamma$-集合及 $T$ 上 $\Gamma$-等变映射构成的范畴记为 $\mathrm{FinSet}^\Gamma_{/T}$。
构造函子
$$\Phi:\mathrm{FinSet}^\Gamma_{/T}\longrightarrow \prod_{t\in R}\mathrm{FinSet}^{\Gamma_t},\qquad (X\xrightarrow{\pi} T)\longmapsto (X_t:=\pi^{-1}(t))_{t\in R},$$
其中 $\Gamma_t$ 固定 $t$，故 $\Gamma$-作用限制为 $\Gamma_t$ 在纤维 $X_t$ 上的作用；等变态射 $f:X\to X'$ 在 $T$ 上保纤维，故限制为 $\Gamma_t$-等变映射族 $(f|_{X_t}:X_t\to X'_t)_{t\in R}$。

构造准逆函子 $\Psi:\prod_{t\in R}\mathrm{FinSet}^{\Gamma_t}\to\mathrm{FinSet}^\Gamma_{/T}$：对 $(F_t)_{t\in R}$，令
$$\Psi((F_t)_{t\in R}):=\bigsqcup_{t\in R}\Gamma\times_{\Gamma_t} F_t,\qquad \Gamma\times_{\Gamma_t} F_t:=(\Gamma\times F_t)/{\sim},\quad (\gamma\sigma,x)\sim(\gamma,\sigma x)\ (\sigma\in\Gamma_t),$$
$\Gamma$-作用为 $\delta\cdot[\gamma,x]_t=[\delta\gamma,x]_t$，映射 $\pi:\Psi((F_t))\to T$ 为 $\pi([\gamma,x]_t)=\gamma t$（良定义且 $\Gamma$-等变；因 $\Gamma$ 和各 $F_t,R$ 有限，该集合有限）。对 $\Gamma_t$-等变映射族 $(g_t:F_t\to F'_t)_{t\in R}$，定义 $\Psi((g_t))([\gamma,x]_t)=[\gamma,g_t(x)]_t$。

**验证 $\Phi,\Psi$ 互为准逆等价**：
- 对 $(X\xrightarrow{\pi}T)$，映射 $\varepsilon_X:\bigsqcup_{t\in R}\Gamma\times_{\Gamma_t}X_t\to X$， $[\gamma,x]_t\mapsto\gamma\cdot x$：
  - 良定义：若 $\sigma\in\Gamma_t$，则 $(\gamma\sigma)\cdot x=\gamma\cdot(\sigma x)$；显然 $\Gamma$-等变且在 $T$ 上（$\pi(\gamma x)=\gamma\pi(x)=\gamma t$）。
  - 单射：若 $\gamma_1 x_1=\gamma_2 x_2$（$x_i\in X_{t_i}$），作用 $\pi$ 得 $\gamma_1 t_1=\gamma_2 t_2$，因 $R$ 对每条轨道仅取一代表元，故 $t_1=t_2=:t$ 且 $\sigma:=\gamma_2^{-1}\gamma_1\in\Gamma_t$，于是 $[\gamma_1,x_1]_t=[\gamma_2\sigma,x_1]_t=[\gamma_2,\sigma x_1]_t=[\gamma_2,x_2]_t$。
  - 满射：对任 $y\in X$，$\pi(y)=\gamma t$（唯一 $t\in R$，某 $\gamma\in\Gamma$），则 $\gamma^{-1}y\in X_t$ 且 $y=\varepsilon_X([\gamma,\gamma^{-1}y]_t)$。
- 对 $(F_t)_{t\in R}$，$\Psi((F_t))$ 在 $t\in R$ 处的纤维由满足 $\gamma s=t$ 的 $[\gamma,x]_s$ 组成，这迫使 $s=t$ 且 $\gamma\in\Gamma_t$，此时 $[\gamma,x]_t=[1,\gamma x]_t$；故 $\eta_{(F_t)}:F_t\xrightarrow{\sim}\Psi((F_t))_t$，$x\mapsto[1,x]_t$ 是 $\Gamma_t$-等变双射。
- $\varepsilon,\eta$ 显然自然。

因此 $\mathrm{FinSet}^\Gamma_{/T}\simeq \prod_{t\in R}\mathrm{FinSet}^{\Gamma_t}$。进一步，每个有限 $\Gamma_t$-集合 $X_t$ 可唯一（至多差重排与子群共轭）分解为 $\Gamma_t$-轨道的不交并 $X_t\cong\bigsqcup_{i=1}^{k_t}\Gamma_t/K_{t,i}$（$K_{t,i}\le\Gamma_t$ 在 $\Gamma_t$-共轭意义下唯一），且轨道间 $\Gamma_t$-等变态射为 $\mathrm{Hom}_{\Gamma_t}(\Gamma_t/K,\Gamma_t/L)\cong\{gL\in\Gamma_t/L:g^{-1}Kg\le L\}$。由此完整分类了全部对象与等变态射。

### 2. $h_X$ 在 $Q=h_{T/\Gamma}$ 上实现的充要条件
注意 $T,T/\Gamma,X\in\mathrm{Prof}_U$（赋予离散拓扑）。

**充要条件**：$h_X$ 可在 $Q=h_{T/\Gamma}$ 上实现，**当且仅当**对每个代表元 $t\in R$，$\Gamma_t$ 在纤维 $X_t$ 上作用**平凡**（等价地：对所有 $x\in X$ 与 $\gamma\in\Gamma$，$\gamma\pi(x)=\pi(x)\implies \gamma x=x$）。

**证明**：
- **($\Rightarrow$) 必要性**：设存在层 $D\xrightarrow{p_D} Q$ 及 $H=h_T$ 上的 $\Gamma$-等变层同构 $\varphi:h_X\xrightarrow{\sim} H\times_Q D$（$\Gamma$ 仅改变 $H$ 坐标）。在点 $*$ 处求截面（层范畴的拉回逐截面对齐）：
  $$X=h_X(*)\xrightarrow{\;\sim\;} (H\times_Q D)(*)=T\times_{T/\Gamma} D(*)$$
  为 $T$ 上的 $\Gamma$-等变双射，其中 $\Gamma$ 仅作用于 $T$ 坐标。对每个 $t\in R$ 取 $t$ 上的纤维，得 $\Gamma_t$-等变双射
  $$X_t\xrightarrow{\;\sim\;} \{t\}\times D(*)_{[t]},$$
  其中 $D(*)_{[t]}$ 是 $D(*)\to T/\Gamma$ 在轨道 $[t]=p(t)$ 上的纤维。因 $\Gamma_t$ 固定 $t$ 且不影响 $D(*)$ 坐标，$\Gamma_t$ 在 $\{t\}\times D(*)_{[t]}$ 上作用平凡，故 $\Gamma_t$ 在 $X_t$ 上作用平凡。
- **($\Leftarrow$) 充分性**：设对每 $t\in R$，$\Gamma_t$ 在 $X_t$ 上作用平凡。则 $\Gamma\times_{\Gamma_t}X_t=(\Gamma/\Gamma_t)\times X_t\cong (\Gamma\cdot t)\times X_t$（$\Gamma$ 仅作用于第一因子）。令有限离散空间 $Y:=\bigsqcup_{t\in R}X_t\in\mathrm{Prof}_U$，配连续映射 $\bar{p}:Y\to T/\Gamma$ 将 $X_t$ 映至 $[t]$。则在 $\mathrm{Prof}_U$ 中有 $T$ 上的 $\Gamma$-等变同胚
  $$X\cong \bigsqcup_{t\in R}(\Gamma\cdot t)\times X_t\cong T\times_{T/\Gamma} Y$$
  （$\Gamma$ 仅作用于 $T$ 坐标）。由于 $h:\mathrm{Prof}_U\to\mathcal{C}$ 保拉回且将等变映射映为等变层态射，取 $D:=h_Y\xrightarrow{h_{\bar{p}}} Q$ 即得 $\mathcal{C}^\Gamma_{/H}$ 中同构 $h_X\cong H\times_Q D$。

### 3. 可实现对象的自同构群
设 $h_X$ 可在 $Q$ 上实现（即 $\Gamma_t$ 在每个 $X_t$ 上平凡作用）。
1. **在 $\mathcal{C}^\Gamma_{/H}$ 中的自同构群**：由 Yoneda 引理（$h_X,h_T\in\mathcal{C}$），$h$ 在 $\mathrm{Prof}_U$ 上全忠实，且等变态射对应等变映射，故
   $$\mathrm{Aut}_{\mathcal{C}^\Gamma_{/H}}(h_X)\cong \mathrm{Aut}_{\mathrm{FinSet}^\Gamma_{/T}}(X).$$
   由前述等价 $\mathrm{FinSet}^\Gamma_{/T}\simeq\prod_{t\in R}\mathrm{FinSet}^{\Gamma_t}$ 及 $\Gamma_t$ 平凡作用，得
   $$\mathrm{Aut}_{\mathcal{C}^\Gamma_{/H}}(h_X)\cong \prod_{t\in R}\mathrm{Aut}_{\Gamma_t}(X_t)=\prod_{t\in R}\mathrm{Sym}(X_t)\cong \prod_{t\in R} S_{|X_t|}$$
   （若 $T=\emptyset$ 即 $R=\emptyset$，空积为平凡群 $\{1\}$）。
2. **实现对象 $D\to Q$ 在 $\mathcal{C}_{/Q}$ 中的自同构群**：对任意实现 $D\xrightarrow{p_D} Q$（即 $h_X\cong H\times_Q D$），因 $Q=h_{T/\Gamma}\cong\bigsqcup_{t\in R}*$，层 $D$ 分解为 $D\cong\bigsqcup_{t\in R} D_t$（其中 $D_t=D\times_{Q,h_{[t]}} *$）。将同构 $h_X\cong H\times_Q D$ 沿单点包含 $h_t:*\to H=h_T$ 拉回，左边得到 $h_{\pi^{-1}(t)}=h_{X_t}$，右边得到 $(*\times_H H)\times_Q D\cong *\times_{h_{[t]},Q} D=D_t$，故 $D\cong\bigsqcup_{t\in R} h_{X_t}=h_Y$ 在 $Q$ 上唯一确定（至多差 $Q$ 上唯一同构）。从而在 $\mathcal{C}_{/Q}$ 中的自同构群同样为
   $$\mathrm{Aut}_{\mathcal{C}_{/Q}}(D)\cong \prod_{t\in R}\mathrm{Aut}_{\mathcal{C}}(h_{X_t})\cong \prod_{t\in R}\mathrm{Sym}(X_t)\cong \prod_{t\in R} S_{|X_t|}.$$

---

## S3　一般层的完整下降

本阶段仅使用共同设定（$\Gamma$ 为任意 $U$-小离散群，$T\in\mathrm{Prof}_U$，$H=h_T$）。

### 1. 构造层 $Q$ 及不变态射 $q:H\to Q$
定义预层 $Q^{\mathrm{pre}}:\mathrm{Prof}_U^{\mathrm{op}}\to\mathrm{Set}_V$ 为
$$Q^{\mathrm{pre}}(S):=H(S)/\Gamma=\mathrm{Hom}_{\mathrm{Prof}_U}(S,T)/\Gamma$$
（由 $H(S),\Gamma\in U\subset V$，商集仍在 $U\subset V$ 中），配自然满射 $H\to Q^{\mathrm{pre}}$。令
$$Q:=(Q^{\mathrm{pre}})^{++}\in\mathcal{C}$$
为其层化，令 $q:H\to Q$ 为复合 $H\to Q^{\mathrm{pre}}\xrightarrow{\eta^{++}} Q$。
- **$\Gamma$-不变性**：对每 $\gamma\in\Gamma$ 及 $f\in H(S)$，$f$ 与 $h_\gamma(f)$ 在 $Q^{\mathrm{pre}}(S)=H(S)/\Gamma$ 中同属一轨道，故 $q\circ h_\gamma=q$。
- **泛性质**：对任意层 $Y\in\mathcal{C}$，由层化伴随以及商集（预层余等化子）的泛性质，自然成立：
  $$\mathrm{Hom}_{\mathcal{C}}(Q,Y)\xrightarrow{\;\sim\;}\mathrm{Hom}_{\mathrm{PSh}}(Q^{\mathrm{pre}},Y)\xrightarrow{\;\sim\;}\{\alpha\in\mathrm{Hom}_{\mathrm{PSh}}(H,Y):\forall\gamma\in\Gamma,\,\alpha\circ h_\gamma=\alpha\}=\mathrm{Hom}_{\mathcal{C}}(H,Y)^\Gamma,$$
  该复合恰为预复合 $q^*(\beta)=\beta\circ q$。

由预备事实第 3 条，对层商 $q:H\to Q$（以及对任意带有 $\Gamma$-作用的层 $E$ 同样构造的层商 $r:E\to E/\Gamma:=(E^{\mathrm{pre}}/\Gamma)^{++}$）立即有两个基本性质：
- **(P1) 局部满射性**：$q$ 与 $r$ 皆在 $\mathcal{C}$ 中局部满射（对 $S\in\mathrm{Prof}_U$ 及目标截面，总可在某有限覆盖 $\{S_i\to S\}$ 上逐片提升至 $H(S_i)$ 或 $E(S_i)$）。
- **(P2) 等价判别**：对 $x_1,x_2\in H(S)$（或 $E(S)$），$q(x_1)=q(x_2)$（或 $r(x_1)=r(x_2)$）当且仅当存在有限覆盖 $\{S_i\to S\}_{i\in I}$ 及 $\gamma_i\in\Gamma$，使得 $x_2|_{S_i}=\gamma_i\cdot(x_1|_{S_i})$ 对所有 $i\in I$ 成立。

### 2. 不预选 $D$ 的可实现性充要判据
设 $(E,\pi,a)\in\mathcal{C}^\Gamma_{/H}$。令 $r:E\to E/\Gamma$ 为其层商。因 $\pi\circ a_\gamma=h_\gamma\circ\pi$，有 $q\circ\pi\circ a_\gamma=q\circ h_\gamma\circ\pi=q\circ\pi$，由 $E/\Gamma$ 泛性质得唯一态射 $\bar{\pi}:E/\Gamma\to Q$ 使 $\bar{\pi}\circ r=q\circ\pi$。由此诱导到拉回的典范比较态射
$$\theta_E:=(\pi,r):E\longrightarrow H\times_Q (E/\Gamma).$$
注意 $\mathrm{pr}_1\circ\theta_E=\pi$ 且 $\theta_E\circ a_\gamma=(\pi\circ a_\gamma,r\circ a_\gamma)=(h_\gamma\circ\pi,r)=(h_\gamma\times_Q\mathrm{id}_{E/\Gamma})\circ\theta_E$，故 $\theta_E$ 是 $\mathcal{C}^\Gamma_{/H}$ 中态射。

**关键引理**：对任意 $(D\xrightarrow{p_D} Q)\in\mathcal{C}_{/Q}$，第二投影 $\mathrm{pr}_2:H\times_Q D\to D$（伴随 $\Gamma$-作用 $h_\gamma\times_Q\mathrm{id}_D$）是 $\mathcal{C}$ 中的层商 $(H\times_Q D)/\Gamma$。
*证明*：$\mathrm{pr}_2$ 明显 $\Gamma$-不变。任取层 $Y\in\mathcal{C}$ 与 $\Gamma$-不变态射 $g:H\times_Q D\to Y$。
- *唯一性*：$\mathrm{pr}_2$ 作为局部满射态射 $q:H\to Q$ 的拉回仍局部满射（对 $d\in D(S)$，由 (P1) 将 $p_D(d)\in Q(S)$ 局部提升为 $h_i\in H(S_i)$，即得 $(h_i,d|_{S_i})\in(H\times_Q D)(S_i)$ 映至 $d|_{S_i}$），而局部满射态射在层范畴 $\mathcal{C}$ 中是满态射（epimorphism：若 $\bar{g}_1\circ\mathrm{pr}_2=\bar{g}_2\circ\mathrm{pr}_2$，则在局部提升处 $\bar{g}_1(d)|_{S_i}=\bar{g}_2(d)|_{S_i}$，由 $Y$ 为层得 $\bar{g}_1=\bar{g}_2$）。
- *存在性*：对 $d\in D(S)$，取有限覆盖 $\{S_i\to S\}$ 及 $h_i\in H(S_i)$ 使 $q(h_i)=p_D(d)|_{S_i}$，令 $y_i:=g_{S_i}(h_i,d|_{S_i})\in Y(S_i)$。在交 $S_{ij}=S_i\times_S S_j$ 上，由 $q(h_i|_{S_{ij}})=p_D(d)|_{S_{ij}}=q(h_j|_{S_{ij}})$ 与 (P2)，存在有限覆盖 $\{W_k\to S_{ij}\}$ 及 $\gamma_k\in\Gamma$ 使 $h_j|_{W_k}=h_{\gamma_k}(h_i|_{W_k})$，从而 $(h_j|_{W_k},d|_{W_k})=(h_{\gamma_k}\times_Q\mathrm{id}_D)(h_i|_{W_k},d|_{W_k})$。由 $g$ 的 $\Gamma$-不变性，$y_j|_{W_k}=y_i|_{W_k}$；由 $Y$ 的层性得 $y_i|_{S_{ij}}=y_j|_{S_{ij}}$，再粘合即得 $\bar{g}_S(d)\in Y(S)$。同理（取共同加细覆盖 $S_i\times_S S'_j$）$\bar{g}_S(d)$ 与覆盖及提升选取无关、对 $S$ 自然，且在 $(h,d)\in(H\times_Q D)(S)$ 处取平凡覆盖即见 $\bar{g}\circ\mathrm{pr}_2=g$。$\square$

**定理（不预选 $D$ 的可实现性判据）**：对任意 $(E,\pi,a)\in\mathcal{C}^\Gamma_{/H}$，以下五条件等价：
1. $E$ 可在 $Q$ 上实现（存在 $D\to Q$ 使 $E\cong H\times_Q D$ 于 $\mathcal{C}^\Gamma_{/H}$）；
2. $\theta_E:E\to H\times_Q (E/\Gamma)$ 是同构；
3. $\theta_E:E\to H\times_Q (E/\Gamma)$ 是单态射（即对任意 $S\in\mathrm{Prof}_U$，$\theta_{E,S}$ 为单射）；
4. **（全部测试对象上的稳定子平凡条件）** 对所有 $S\in\mathrm{Prof}_U$、$e\in E(S)$ 与 $\gamma\in\Gamma$，均有
   $$h_\gamma(\pi(e))=\pi(e)\implies a_\gamma(e)=e;$$
5. 对每 $\gamma\in\Gamma$，记不动点闭子空间 $T^\gamma:=\{t\in T:\gamma t=t\}\in\mathrm{Prof}_U$，则 $a_\gamma$ 在拉回 $E\times_H h_{T^\gamma}$ 上作用为恒等态射。

*证明*：
- **(1)$\Rightarrow$(2)**：若 $\varphi:E\xrightarrow{\sim} H\times_Q D$ 为 $\mathcal{C}^\Gamma_{/H}$ 中同构，由关键引理 $(H\times_Q D)/\Gamma\cong D$（通过 $\mathrm{pr}_2$）。函子 $(-) /\Gamma$ 将 $\varphi$ 映为同构 $\bar{\varphi}:E/\Gamma\xrightarrow{\sim} D$（且覆盖 $Q$ 上的投影），从而将 $\theta_E=(\pi,r)$ 共轭为 $(\mathrm{pr}_1,\mathrm{pr}_2)=\mathrm{id}_{H\times_Q D}$；故 $\theta_E$ 为同构。
- **(2)$\Rightarrow$(1)**：直接取 $D=E/\Gamma\xrightarrow{\bar{\pi}}Q$，因 $\theta_E$ 在 $\mathcal{C}^\Gamma_{/H}$ 中。
- **(2)$\Rightarrow$(3)**：显然。
- **(3)$\Rightarrow$(2)**：只需证明 **$\theta_E$ 对任意 $(E,\pi,a)$ 恒为局部满射**（在层范畴中单态射 + 局部满射 $\Rightarrow$ 逐截面双射，即同构）。事实上，任取 $(h,\bar{e})\in(H\times_Q(E/\Gamma))(S)$，故 $q(h)=\bar{\pi}(\bar{e})$。由 (P1) 在某有限覆盖 $\{S_i\to S\}$ 上将 $\bar{e}|_{S_i}$ 提升为 $e_i\in E(S_i)$（$r(e_i)=\bar{e}|_{S_i}$）。于是 $q(\pi(e_i))=\bar{\pi}(r(e_i))=\bar{\pi}(\bar{e}|_{S_i})=q(h|_{S_i})$。再由 (P2) 对每个 $i$ 取有限覆盖 $\{S_{i,j}\to S_i\}$ 及 $\gamma_{i,j}\in\Gamma$ 使 $h|_{S_{i,j}}=h_{\gamma_{i,j}}(\pi(e_i|_{S_{i,j}}))$。令 $e'_{i,j}:=a_{\gamma_{i,j}}(e_i|_{S_{i,j}})\in E(S_{i,j})$，则
  $$\theta_E(e'_{i,j})=(\pi(e'_{i,j}),r(e'_{i,j}))=(h_{\gamma_{i,j}}(\pi(e_i|_{S_{i,j}})),r(e_i|_{S_{i,j}}))=(h,\bar{e})|_{S_{i,j}}.$$
  复合族 $\{S_{i,j}\to S\}$ 仍为有限联合满射覆盖。若 $\theta_E$ 又为单态射，则相邻交上这些局部提升必相等，由 $E$ 是层粘合出全局唯一原像，故 $\theta_E$ 是同构！
- **(3)$\Rightarrow$(4)**：若 $e\in E(S)$ 与 $\gamma\in\Gamma$ 满足 $h_\gamma(\pi(e))=\pi(e)$，则 $\theta_E(a_\gamma(e))=(h_\gamma(\pi(e)),r(a_\gamma(e)))=(\pi(e),r(e))=\theta_E(e)$，由 $\theta_E$ 单得 $a_\gamma(e)=e$。
- **(4)$\Rightarrow$(3)**：设 $\theta_E(e_1)=\theta_E(e_2)$（$e_1,e_2\in E(S)$），即 $\pi(e_1)=\pi(e_2)$ 且 $r(e_1)=r(e_2)$。由 (P2) 存在有限覆盖 $\{S_i\to S\}$ 及 $\gamma_i\in\Gamma$ 使 $e_2|_{S_i}=a_{\gamma_i}(e_1|_{S_i})$。作用 $\pi$ 得 $h_{\gamma_i}(\pi(e_1|_{S_i}))=\pi(e_2|_{S_i})=\pi(e_1|_{S_i})$。由 (4) 应用于 $S_i$，得 $e_2|_{S_i}=a_{\gamma_i}(e_1|_{S_i})=e_1|_{S_i}$；因 $E$ 为层，故 $e_1=e_2$。
- **(4)$\Leftrightarrow$(5)**：$T^\gamma$ 在 $T$ 中闭（因 $T$ Hausdorff），故 $T^\gamma\in\mathrm{Prof}_U$ 且 $h_{T^\gamma}(S)=\{f\in H(S):h_\gamma(f)=f\}$，因此 $(E\times_H h_{T^\gamma})(S)=\{e\in E(S):h_\gamma(\pi(e))=\pi(e)\}$。$\square$

### 3. 所有实现及态射的分类
定义函子 $q^*:\mathcal{C}_{/Q}\to\mathcal{C}^\Gamma_{/H}$，$(D\xrightarrow{p_D} Q)\mapsto (H\times_Q D,\mathrm{pr}_1,h_\bullet\times_Q\mathrm{id}_D)$，态射 $u:D_1\to D_2$ 映为 $\mathrm{id}_H\times_Q u$。

**$q^*$ 全忠实**：取 $D_1,D_2\in\mathcal{C}_{/Q}$ 与 $f\in\mathrm{Hom}_{\mathcal{C}^\Gamma_{/H}}(q^* D_1,q^* D_2)$。记 $g=\mathrm{pr}_2\circ f:H\times_Q D_1\to D_2$。因 $f$ $\Gamma$-等变，$g\circ(h_\gamma\times_Q\mathrm{id}_{D_1})=\mathrm{pr}_2\circ(h_\gamma\times_Q\mathrm{id}_{D_2})\circ f=g$，即 $g$ 是 $\Gamma$-不变的。由关键引理，$g$ 唯一通过 $\mathrm{pr}_2:H\times_Q D_1\to D_1$ 分解为 $\bar{g}:D_1\to D_2$ 使 $\bar{g}\circ\mathrm{pr}_2=g$。又 $p_{D_2}\circ\bar{g}\circ\mathrm{pr}_2=p_{D_2}\circ\mathrm{pr}_2\circ f=q\circ\mathrm{pr}_1\circ f=q\circ\mathrm{pr}_1=p_{D_1}\circ\mathrm{pr}_2$，而 $\mathrm{pr}_2$ 为满态射，故 $p_{D_2}\circ\bar{g}=p_{D_1}$，即 $\bar{g}\in\mathrm{Hom}_{\mathcal{C}_{/Q}}(D_1,D_2)$。检验 $\mathrm{id}_H\times_Q\bar{g}=f$（第一分量为 $\mathrm{pr}_1=\mathrm{pr}_1\circ f$，第二分量为 $\bar{g}\circ\mathrm{pr}_2=\mathrm{pr}_2\circ f$），且 $\overline{\mathrm{pr}_2\circ(\mathrm{id}_H\times_Q u)}=u$（由 $\mathrm{pr}_2$ 满态射）。故 $\mathrm{Hom}_{\mathcal{C}_{/Q}}(D_1,D_2)\xrightarrow{\sim}\mathrm{Hom}_{\mathcal{C}^\Gamma_{/H}}(q^* D_1,q^* D_2)$。

因此，记 $\mathcal{C}^{\Gamma,\mathrm{real}}_{/H}\subseteq\mathcal{C}^\Gamma_{/H}$ 为由满足判据 (2)–(5) 的对象组成的满子范畴，则
$$q^*:\mathcal{C}_{/Q}\xrightarrow{\;\sim\;}\mathcal{C}^{\Gamma,\mathrm{real}}_{/H}$$
是**范畴等价**，其准逆函子为 $(E,\pi,a)\mapsto (E/\Gamma\xrightarrow{\bar{\pi}} Q)$。故每个可实现对象的实现 $D\to Q$ 在 $\mathcal{C}_{/Q}$ 中在唯一同构意义下唯一（即 $E/\Gamma\xrightarrow{\bar{\pi}} Q$），且实现对象间的等变态射双射于 $\mathcal{C}_{/Q}$ 中态射。

### 4. 对任意层 $u:B\to Q$ 的对应分类及基底拉回相容性
对任意层 $u:B\to Q$（$B\in\mathcal{C}$）：
- 记 $H_B:=H\times_Q B$，投影 $q_B:=\mathrm{pr}_2:H_B\to B$，群作用 $h^B_\gamma:=h_\gamma\times_Q\mathrm{id}_B$。
- **关键事实**：将前述关键引理取 $D=B$，即知 $q_B:H_B\to B$ 恰为层商 $H_B/\Gamma$。且对任意 $(D'\xrightarrow{p'} B)\in\mathcal{C}_{/B}$，记 $p_Q:=u\circ p':D'\to Q$，有自然同构 $H_B\times_B D'\cong H\times_Q D'$，再次应用关键引理得 $\mathrm{pr}_2:H_B\times_B D'\to D'$ 亦为层商 $(H_B\times_B D')/\Gamma$。
- 对 $H_B$ 上的等变层 $(F,\pi_F,a^F)\in\mathcal{C}^\Gamma_{/H_B}$（即 $\pi_F:F\to H_B$，$\pi_F\circ a^F_\gamma=h^B_\gamma\circ\pi_F$），令 $r_F:F\to F/\Gamma$ 为其层商，并由 $q_B\circ\pi_F$ 的 $\Gamma$-不变性得唯一态射 $\bar{\pi}_F:F/\Gamma\to B$ 与比较态射 $\theta_F=(\pi_F,r_F):F\to H_B\times_B(F/\Gamma)$。
- 与 $Q$ 上完全相同的论证给出：
  1. $\theta_F$ 恒局部满射（对 $((h,b),\bar{y})\in (H_B\times_B(F/\Gamma))(S)$，局部将 $\bar{y}$ 提升为 $y_i\in F(S_i)$，因 $q_B(\pi_F(y_i))=b|_{S_i}$，故 $\pi_F(y_i)=(h'_i,b|_{S_i})$ 满足 $q(h'_i)=u(b|_{S_i})=q(h|_{S_i})$；再局部取 $\gamma_{i,j}$ 使 $h_{\gamma_{i,j}}(h'_i|_{S_{i,j}})=h|_{S_{i,j}}$ 并用 $a^F_{\gamma_{i,j}}$ 修正 $y_i$ 即可）。
  2. $F$ 在 $B$ 上可实现 $\iff \theta_F$ 同构 $\iff \theta_F$ 单态射 $\iff \forall S\in\mathrm{Prof}_U,\,\forall y\in F(S),\,\forall\gamma\in\Gamma,\ h^B_\gamma(\pi_F(y))=\pi_F(y)\implies a^F_\gamma(y)=y$。
  3. 函子 $q_B^*:\mathcal{C}_{/B}\to\mathcal{C}^\Gamma_{/H_B}$，$D'\mapsto (H_B\times_B D',\mathrm{pr}_1,h^B_\bullet\times_B\mathrm{id}_{D'})$ 全忠实，并诱导范畴等价
     $$q_B^*:\mathcal{C}_{/B}\xrightarrow{\;\sim\;}\mathcal{C}^{\Gamma,\mathrm{real}}_{/H_B},$$
     准逆为 $F\mapsto (F/\Gamma\xrightarrow{\bar{\pi}_F} B)$。

**与基底拉回的相容性**：设 $f:B'\to B$ 为 $Q$ 上的态射（取 $B=Q,\,f=u$ 即得沿 $B\to Q$ 本身的拉回）。
- 定义拉回函子 $f^*:\mathcal{C}_{/B}\to\mathcal{C}_{/B'}$，$D'\mapsto D'\times_B B'$；以及等变拉回函子 $f^*_{\mathrm{eq}}:\mathcal{C}^\Gamma_{/H_B}\to\mathcal{C}^\Gamma_{/H_{B'}}$，将 $(F,\pi_F,a^F)$ 映为
  $$F\times_B B'\cong F\times_{H_B} H_{B'}\quad (\text{因 } H_{B'}=H_B\times_B B'),$$
  配结构态射 $\pi_F\times_B\mathrm{id}_{B'}:F\times_B B'\to H_{B'}$ 与 $\Gamma$-作用 $a^F_\gamma\times_B\mathrm{id}_{B'}$。
- **相容性 1（实现函子的交换性）**：对 $D'\in\mathcal{C}_{/B}$，拉回结合律给出 $\mathcal{C}^\Gamma_{/H_{B'}}$ 中自然同构
  $$f^*_{\mathrm{eq}}(q_B^*(D'))=(H_B\times_B D')\times_B B'\cong (H_B\times_B B')\times_{B'}(D'\times_B B')=q_{B'}^*(f^*(D')).$$
  特例地，$f^*_{\mathrm{eq}}$ 将可实现对象映为可实现对象，从而在全范畴与等价子范畴上均自然交换。
- **相容性 2（层商与比较态射 $\theta$ 的相容性）**：对**任意** $F\in\mathcal{C}^\Gamma_{/H_B}$，自然态射 $r_F\times_B\mathrm{id}_{B'}:F\times_B B'\to (F/\Gamma)\times_B B'$ 是层商 $(F\times_B B')/\Gamma$。
  *验证*：它是 $\Gamma$-不变的。任取层 $Y\in\mathcal{C}$ 及 $\Gamma$-不变态射 $g:F\times_B B'\to Y$。因 $r_F\times_B\mathrm{id}_{B'}$ 是局部满射 $r_F$ 的拉回故局部满射（且从而为满态射），分解若存在必唯一。对 $(\bar{y},b')\in ((F/\Gamma)\times_B B')(S)$，在有限覆盖 $\{S_i\to S\}$ 上将 $\bar{y}$ 提升为 $y_i\in F(S_i)$，则 $q_B(\pi_F(y_i))=\bar{\pi}_F(\bar{y}|_{S_i})=f(b'|_{S_i})$，得截面 $(y_i,b'|_{S_i})\in(F\times_B B')(S_i)$ 及 $z_i:=g(y_i,b'|_{S_i})\in Y(S_i)$。在 $S_{ij}=S_i\times_S S_j$ 上 $r_F(y_i|_{S_{ij}})=r_F(y_j|_{S_{ij}})$，由 (P2) 存在有限覆盖 $\{W_k\to S_{ij}\}$ 及 $\gamma_k\in\Gamma$ 使 $y_j|_{W_k}=a^F_{\gamma_k}(y_i|_{W_k})$，故 $(y_j|_{W_k},b'|_{W_k})=(a^F_{\gamma_k}\times_B\mathrm{id}_{B'})(y_i|_{W_k},b'|_{W_k})$；由 $g$ $\Gamma$-不变及 $Y$ 是层，得 $z_i|_{S_{ij}}=z_j|_{S_{ij}}$，粘合出 $\bar{g}(\bar{y},b')\in Y(S)$（且同样与选取无关、自然、满足 $\bar{g}\circ(r_F\times_B\mathrm{id}_{B'})=g$）。
  因此，自然同构 $(F\times_B B')/\Gamma\cong (F/\Gamma)\times_B B'$（在 $B'$ 上）成立，且在此同构及 $H_{B'}\times_{B'}((F/\Gamma)\times_B B')\cong (H_B\times_B(F/\Gamma))\times_B B'$ 下，比较态射满足
  $$\theta_{F\times_B B'}\cong \theta_F\times_B\mathrm{id}_{B'}.$$

---

## S4　单点上的检验

**结论：否（不一定可在 $Q$ 上实现）。**

### 完整反例与核验
取 $\Gamma=\mathbb{Z}/2\mathbb{Z}=\{1,\sigma\}$，$T=\{*\}$（$\Gamma$ 平凡作用）。则 $H=h_*=*$（终层），$Q=H/\Gamma=*$。

1. **构造 profinite 空间 $A\in\mathrm{Prof}_U$**：
   令 $A:=(\mathbb{Z}/3\mathbb{Z})^{\mathbb{N}}$（$\mathbb{Z}/3\mathbb{Z}=\{0,1,2\}$ 配离散拓扑，$A$ 配乘积拓扑）。
   - **$U$-小性**：因假设 $\mathbb{N}\in U$ 且 $U$ 为 Grothendieck 宇宙，故 $\{0,1,2\}\in\mathbb{N}\in U$（$U$ 传递），从而 $A=\{0,1,2\}^{\mathbb{N}}\in U$，且其拓扑 $\subseteq\mathcal{P}(A)\in U$。
   - **Profinite 性**：每个因子 $\{0,1,2\}$ 有限离散故紧 Hausdorff 全不连通；Tychonoff 定理（在 ZFC 下适用于任意紧空间之积）给出 $A$ 紧，紧 Hausdorff 空间的积仍 Hausdorff，且任意相异两点在某分量 $n\in\mathbb{N}$ 不同，对应的闭开柱集 $\mathrm{pr}_n^{-1}(x_n)$ 分离之，故 $A$ 全不连通。即 $A\in\mathrm{Prof}_U$。

2. **构造层 $E$ 与等变结构**：
   对任意 $S\in\mathrm{Prof}_U$，定义
   $$\underline{A_{\mathrm{disc}}}(S):=\{f\in h_A(S): f(S)\text{ 有限}\}=\{f\in h_A(S): f\text{ 局部常值}\}$$
   （若 $f$ 局部常值，由 $S$ 紧即得像集有限；反之若 $f$ 连续且像集 $F\subseteq A$ 有限，因 $A$ Hausdorff 故每点闭，从而每个纤维 $f^{-1}(a)=S\setminus\bigcup_{b\in F\setminus\{a\}}f^{-1}(b)$ 闭开，即局部常值）。
   显然 $\underline{A_{\mathrm{disc}}}$ 是 $h_A$ 的子预层（$f(S)$ 有限 $\Rightarrow (f\circ g)(S')$ 有限）。而且它是层：若 $\{p_i:S_i\to S\}_{i\in I}$ 为有限联合满射覆盖，匹配族 $f_i\in\underline{A_{\mathrm{disc}}}(S_i)\subseteq h_A(S_i)$ 在 $h_A$ 中唯一粘合为 $f\in h_A(S)$，且 $f(S)=\bigcup_{i\in I}f_i(S_i)$ 为有限个有限集之并仍有限，故 $f\in\underline{A_{\mathrm{disc}}}(S)$。

   定义商预层 $P(S):=h_A(S)/\underline{A_{\mathrm{disc}}}(S)$，并取层化 $E:=P^{++}\in\mathcal{C}$。
   - **验证 $P$ 已是分离预层**：设 $[f_1],[f_2]\in P(S)$ 在有限联合满射覆盖 $\{p_i:S_i\to S\}_{i\in I}$ 上相等，即 $(f_1-f_2)\circ p_i\in\underline{A_{\mathrm{disc}}}(S_i)$。则 $(f_1-f_2)(S)=\bigcup_{i\in I}(f_1-f_2)(p_i(S_i))$ 为有限个有限集之并，故有限；从而 $f_1-f_2\in\underline{A_{\mathrm{disc}}}(S)$，即 $[f_1]=[f_2]\in P(S)$。因 $P$ 分离，自然映射 $\eta_S:P(S)\to E(S)$ 对所有 $S\in\mathrm{Prof}_U$ **单射**。
   - **定义 $\pi$ 与 $\Gamma$-作用**：$\pi:E\to H=*$ 为到终层的唯一态射。映射 $\iota:A\to A,\,x\mapsto -x$ 连续且群自同构，保有限像映射集合 $\underline{A_{\mathrm{disc}}}(S)$，故诱导 $P$ 上的对合 $P\to P$；由层化函子性诱导 $E$ 上的对合 $a_\sigma:E\to E$（$a_\sigma^2=\mathrm{id}_E$，$a_1=\mathrm{id}_E$，自动满足 $\pi\circ a_\gamma=h_\gamma\circ\pi$）。

3. **核验单点条件成立**：
   由预备事实第 3 条，$E(*)=P^{++}(*)\cong P(*)=h_A(*)/\underline{A_{\mathrm{disc}}}(*)=A/A=\{0\}$。因此对 $E(*)$ 的唯一元素 $e=0$ 及所有 $\gamma\in\Gamma$，$\gamma\pi(e)=\pi(e)$ 恒蕴含 $a_\gamma(e)=e$。

4. **核验 $E$ 不可在 $Q=*$ 上实现**：
   取测试对象 $S=A\in\mathrm{Prof}_U$ 与截面 $e:=\eta_A([\mathrm{id}_A])\in E(A)$。有 $h_\sigma(\pi(e))=*=\pi(e)$。但 $a_\sigma(e)=\eta_A([-\mathrm{id}_A])$。若 $a_\sigma(e)=e$，因 $\eta_A:P(A)\to E(A)$ 单射，必有 $[\mathrm{id}_A]=[-\mathrm{id}_A]\in P(A)$，即
   $$\mathrm{id}_A-(-\mathrm{id}_A)=2\,\mathrm{id}_A=-\mathrm{id}_A\in\underline{A_{\mathrm{disc}}}(A)$$
   （在 $\mathbb{Z}/3\mathbb{Z}$ 中 $2=-1$），这意味着 $(-\mathrm{id}_A)(A)=A$ 为有限集，与 $|A|=3^{\aleph_0}$ 无穷矛盾！故 $a_\sigma(e)\neq e$。由 S3 可实现性判据 (4)（或直接因若 $E\cong *\times_* D$ 则 $\sigma$ 必在 $E$ 上作用平凡），$E$ **不能**在 $Q$ 上实现。

---

## S5　局部满射的基底检验

**结论：是（$E$ 必可在 $Q$ 上实现）。**

### 证明（两种等价视角）

#### 证法一：直接验证 S3 判据
由 S3 可实现性判据 (4)，欲证 $E$ 在 $Q$ 上可实现，只需对任意 $S\in\mathrm{Prof}_U$、$e\in E(S)$ 与 $\gamma\in\Gamma$ 满足 $h_\gamma(\pi(e))=\pi(e)$，证明 $a_\gamma(e)=e$。
- 若 $S=\emptyset$，则 $E(\emptyset)=\{*\}$，故 $a_\gamma(e)=e$ 自动成立。
- 设 $S\neq\emptyset$，考虑截面 $q(\pi(e))\in Q(S)$。因 $u:B\to Q$ **局部满射**，按题设定义，存在有限联合满射覆盖 $\{p_i:S_i\to S\}_{i\in I}$ 及截面 $b_i\in B(S_i)$，使得对每 $i\in I$ 有
  $$u_{S_i}(b_i)=q(\pi(e))|_{S_i}=q(\pi(e|_{S_i})).$$
- 由拉回在层范畴中逐截面计算，$(e|_{S_i},b_i)$ 构成 $(E\times_Q B)(S_i)$ 的截面（此处 $E\to Q$ 为 $q\circ\pi$）。在结构态射 $\pi_B=\pi\times_Q\mathrm{id}_B:E\times_Q B\to H_B=H\times_Q B$ 与群作用 $h^B_\gamma=h_\gamma\times_Q\mathrm{id}_B$、$a^B_\gamma=a_\gamma\times_Q\mathrm{id}_B$ 下，有
  $$h^B_\gamma(\pi_B(e|_{S_i},b_i))=(h_\gamma(\pi(e|_{S_i})),b_i)=(\pi(e|_{S_i}),b_i)=\pi_B(e|_{S_i},b_i).$$
- 因 $E\times_Q B$ 作为 $H_B$ 上的等变对象可在 $B$ 上实现，由 S3 对 $B\to Q$ 建立的可实现性判据，得
  $$(a_\gamma(e|_{S_i}),b_i)=a^B_\gamma(e|_{S_i},b_i)=(e|_{S_i},b_i)\in (E\times_Q B)(S_i).$$
- 取第一分量即得 $a_\gamma(e)|_{S_i}=a_\gamma(e|_{S_i})=e|_{S_i}\in E(S_i)$ 对一切 $i\in I$ 成立。
- 因 $E$ 是层且 $\{p_i:S_i\to S\}_{i\in I}$ 是覆盖，由层的分离性得 $a_\gamma(e)=e$。

由 S3 判据，$E$ 必可在 $Q$ 上实现。

#### 证法二：通过 S3 基底拉回相容性（结构解释）
由 S3 构造与相容性，$\theta_{E\times_Q B}\cong\theta_E\times_Q\mathrm{id}_B$。因 $E\times_Q B$ 在 $B$ 上可实现，由 S3 对 $B$ 的判据 $\theta_E\times_Q\mathrm{id}_B$ 是同构（特别地为单态射）。因为 $B\to Q$ 局部满射，对任意使 $\theta_E(e_1)=\theta_E(e_2)$ 的截面 $e_1,e_2\in E(S)$，总可在某有限覆盖 $\{S_i\to S\}$ 上将 $q\pi(e_1)=q\pi(e_2)$ 提升至 $b_i\in B(S_i)$，从而 $(e_1|_{S_i},b_i)$ 与 $(e_2|_{S_i},b_i)$ 在 $\theta_E\times_Q\mathrm{id}_B$ 下同像故相等，进而 $e_1|_{S_i}=e_2|_{S_i}$，由层性得 $e_1=e_2$。于是 $\theta_E$ 为单态射，由 S3 判据即同构，故 $E$ 在 $Q$ 上可实现。

---

## S6　非空基底与全局结论

**结论：否（仅假设 $B$ 是非空可表示层且有 $B\to Q$，拉回后可实现并不必反映原 $E$ 可实现）。**

### 1. 完整反例

#### 反例 A（有限极简例子：未覆盖全部点/轨道）
取 $\Gamma=\mathbb{Z}/2\mathbb{Z}=\{1,\sigma\}$，$T=\{t_1,t_2\}$（离散两点集）配平凡 $\Gamma$-作用，则 $H=h_T$，$Q=h_{T/\Gamma}=h_T$（$q=\mathrm{id}_H$）。
- 取 $B=h_{\{*\}}=*$（非空可表示层），$u:B\to Q$ 为选定 $t_1$ 的态射 $h_{t_1}$。
- 取有限 $\Gamma$-集 $X=\{x_1,y_1,y_2\}$，等变映射 $\pi:X\to T$ 定义为 $\pi(x_1)=t_1$、$\pi(y_1)=\pi(y_2)=t_2$，$\sigma$ 固定 $x_1$ 并对换 $y_1\leftrightarrow y_2$。令 $E=h_X$（带诱导等变结构）。
- **拉回后可实现**：因 $h$ 保拉回，$H_B=H\times_Q B\cong h_{\{*\}}=*$，$E\times_Q B\cong h_{\{x_1\}}=*$（$\Gamma$ 作用平凡），故 $E\times_Q B\cong H_B\times_B B$ 在 $B$ 上可实现（取 $D'=B$）。
- **原对象不可实现**：在 $t_2$ 上 $\Gamma_{t_2}=\Gamma$ 在 $X_{t_2}=\{y_1,y_2\}$ 上非平凡作用，由 S2 判据（或直接看 $y_1\in E(*)$ 满足 $\sigma\pi(y_1)=\pi(y_1)$ 而 $a_\sigma(y_1)=y_2\neq y_1$），$E$ 不可在 $Q$ 上实现。

#### 反例 B（加强例子：即使 $B(*)\to Q(*)$ 满射仍不反映可实现性）
下面的完整例子表明，即便补充要求 $u(*):B(*)\to Q(*)$ 满射（即 $B$ 击中 $Q$ 的每一个“点/轨道”），只要 $B\to Q$ 非局部满射，拉回可实现仍不必反映原 $E$ 可实现。

1. **底空间与群**：
   令 $T=\alpha\mathbb{N}=\mathbb{N}\cup\{\infty\}$ 为离散 $\mathbb{N}$ 的单点紧化（含 $\infty$ 的开集为余有限集，不含 $\infty$ 的任意子集开）。因 $\mathbb{N}\in U$，故 $\alpha\mathbb{N}\in\mathrm{Prof}_U$。
   令 $\tilde{\Gamma}=\mathfrak{S}_{<\omega}(\mathbb{N})\times\mathbb{Z}/2\mathbb{Z}$，其中 $\mathfrak{S}_{<\omega}(\mathbb{N})$ 为 $\mathbb{N}$ 上有限支集置换群（每元固定 $\infty$，因仅变动有限个点故在 $\alpha\mathbb{N}$ 上为同胚），而 $\mathbb{Z}/2\mathbb{Z}=\{1,\sigma\}$ 在 $T$ 上作用平凡。因 $\mathfrak{S}_{<\omega}(\mathbb{N})\subseteq\bigcup_{n\in\mathbb{N}}\mathrm{Sym}(\{0,\dots,n\})\in U$，故 $\tilde{\Gamma}\in U$。
   记 $H=h_T$，$Q=(H/\tilde{\Gamma})^+$。由预备事实第 3 条，$Q(*)\cong Q^{\mathrm{pre}}(*)=T/\tilde{\Gamma}=\{[\mathbb{N}],[\infty]\}$（共两条轨道：$\mathbb{N}=\tilde{\Gamma}\cdot 0$ 与 $\{\infty\}$）。

2. **非空可表示基底 $B\to Q$**：
   取 $B:=h_{\{0,1\}}$（$\{0,1\}$ 离散非空，故 $B$ 为非空可表示层）。由 Yoneda 引理，$\mathrm{Hom}_{\mathcal{C}}(h_{\{0,1\}},Q)\cong Q(\{0,1\})\cong Q(*)\times Q(*)$（因为 $\{0\}\sqcup\{1\}$ 是 $\{0,1\}$ 的两两不交覆盖），取对应于 $(q(0),q(\infty))$ 的态射 $u:B\to Q$。特别地，$u(*):B(*)=\{0,1\}\to Q(*)$ 为双射。显式地，对任意 $c\in B(S)$，令 $S_k=c^{-1}(k)$（$S=S_0\sqcup S_1$ 闭开分解），则 $u_S(c)|_{S_0}=q(\mathrm{const}_0|_{S_0})$ 且 $u_S(c)|_{S_1}=q(\mathrm{const}_\infty|_{S_1})$。

3. **等变层 $E$ 的构造与核验**：
   记 $H_{\mathrm{fin}}(S):=\{f\in h_T(S):f(S)\text{ 有限}\}$。同 S4 验证可知 $H_{\mathrm{fin}}\subseteq H$ 是 $\tilde{\Gamma}$-不变子层。定义预层
   $$P(S):=(H(S)\times\{+1,-1\})/{\sim},\qquad (f,+1)\sim(f,-1)\iff f\in H_{\mathrm{fin}}(S),$$
   并取层化 $E:=P^{++}\in\mathcal{C}$。
   - **$P$ 是分离预层**：若 $[f_1,\epsilon_1],[f_2,\epsilon_2]\in P(S)$ 在有限覆盖 $\{p_i:S_i\to S\}_{i\in I}$ 上相等，则由 $P\to H,\,[f,\epsilon]\mapsto f$ 及 $H$ 是层得 $f_1=f_2=:f$；若 $\epsilon_1\neq\epsilon_2$，则每块上 $f(p_i(S_i))$ 有限，故 $f(S)=\bigcup_{i\in I}f(p_i(S_i))$ 有限，即 $f\in H_{\mathrm{fin}}(S)$ 而 $[f,\epsilon_1]=[f,\epsilon_2]\in P(S)$。故 $\eta_S:P(S)\hookrightarrow E(S)$ 恒**单射**。
   - **$\pi$ 与 $\tilde{\Gamma}$-作用**：$P\to H,\,[f,\epsilon]\mapsto f$ 层化为 $\pi:E\to H$；$P$ 上的 $\tilde{\Gamma}$-作用 $(\gamma,1)\cdot[f,\epsilon]=[\gamma\circ f,\epsilon]$、$(1,\sigma)\cdot[f,\epsilon]=[f,-\epsilon]$（良定义，因 $\gamma$ 保持像集有限性）层化为 $E$ 上的 $\tilde{\Gamma}$-作用，满足 $\pi\circ a_{(\gamma,\tau)}=h_{(\gamma,\tau)}\circ\pi$。
   - **验证 $E\times_Q B$ 可在 $B$ 上实现**：
     先证 $\mathrm{pr}_1:H\times_Q B\to H$ 通过 $H_{\mathrm{fin}}\hookrightarrow H$ 分解。对任意 $(f,c)\in (H\times_Q B)(S)$，分解 $S=S_0\sqcup S_1$（$S_k=c^{-1}(k)$）。
     - 在 $S_0$ 上，$q(f|_{S_0})=q(\mathrm{const}_0|_{S_0})$，由 S3 的 (P2) 存在有限覆盖 $\{W_j\to S_0\}_{j\in J}$ 及 $(\gamma_j,\tau_j)\in\tilde{\Gamma}$ 使 $f|_{W_j}=\mathrm{const}_{\gamma_j(0)}$，故 $f(S_0)=\{\gamma_j(0):j\in J\}$ 有限。
     - 在 $S_1$ 上，$q(f|_{S_1})=q(\mathrm{const}_\infty|_{S_1})$，同理由 $\tilde{\Gamma}$ 固定 $\infty$ 得局部常值等于 $\infty$，故 $f(S_1)\subseteq\{\infty\}$ 有限。
     因此 $f(S)=f(S_0)\cup f(S_1)$ 有限，即 $f\in H_{\mathrm{fin}}(S)$。
     次证 $\pi$ 限制为同构 $E\times_H H_{\mathrm{fin}}\xrightarrow{\sim} H_{\mathrm{fin}}$：对 $f\in H_{\mathrm{fin}}(S)$ 令 $\iota_S(f):=\eta_S([f,+1])\in E(S)$，给出截面 $\iota:H_{\mathrm{fin}}\to E\times_H H_{\mathrm{fin}}$。反之若 $e\in E(S)$ 满足 $\pi(e)=f\in H_{\mathrm{fin}}(S)$，因 $E=P^{++}$ 可在某有限覆盖 $\{S_i\to S\}$ 上把 $e|_{S_i}$ 写为 $\eta_{S_i}([f_i,\epsilon_i])$；此时 $f_i=\pi(e|_{S_i})=f|_{S_i}\in H_{\mathrm{fin}}(S_i)$，故 $[f_i,\epsilon_i]=[f|_{S_i},+1]$，即 $e|_{S_i}=\iota(f)|_{S_i}$；由 $E$ 是层得 $e=\iota(f)$。且在 $H_{\mathrm{fin}}$ 上 $(1,\sigma)$ 平凡作用，$(\gamma,1)$ 仅按 $\gamma$ 作用。
     从而在 $\mathcal{C}^{\tilde{\Gamma}}_{/H_B}$ 中
     $$E\times_Q B\cong E\times_H(H\times_Q B)\cong (E\times_H H_{\mathrm{fin}})\times_{H_{\mathrm{fin}}}(H\times_Q B)\cong H\times_Q B\cong H_B\times_B B,$$
     即 $E\times_Q B$ 可在 $B$ 上实现（取 $D'=B$）。
   - **验证原 $E$ 不可在 $Q$ 上实现**：
     取 $S=\alpha\mathbb{N}\in\mathrm{Prof}_U$ 及 $e:=\eta_{\alpha\mathbb{N}}([\mathrm{id}_{\alpha\mathbb{N}},+1])\in E(\alpha\mathbb{N})$。因 $\sigma$ 在 $T$ 上作用平凡，$h_{(1,\sigma)}(\pi(e))=\pi(e)$；但 $a_{(1,\sigma)}(e)=\eta_{\alpha\mathbb{N}}([\mathrm{id}_{\alpha\mathbb{N}},-1])\neq e$（因 $\eta_{\alpha\mathbb{N}}$ 单射且 $\mathrm{id}_{\alpha\mathbb{N}}(\alpha\mathbb{N})=\alpha\mathbb{N}$ 无穷，故 $\mathrm{id}_{\alpha\mathbb{N}}\notin H_{\mathrm{fin}}(\alpha\mathbb{N})$）。由 S3 判据，$E$ **不能**在 $Q$ 上实现。

---

### 2. 据此前结果整理的可用检验原则

综合 S1–S6 的定理与反例，可归纳以下五条判别与检验原则：

1. **自由作用的自动下降原则（源自 S1 与 S3）**：
   - 若 $\Gamma$ 有限且在 $T$ 上自由作用，由 S1 知 $Q=h_{T/\Gamma}$（甚至 $T\cong\Gamma\times(T/\Gamma)$），**任何**等变层 $E\to H$ 自动在 $Q$ 上可实现，无需额外检验。
   - 更一般地（任意 $U$-小离散群 $\Gamma$），若 $\Gamma$ 在 $T$ 上自由作用（对一切 $\gamma\neq 1$，$T^\gamma=\emptyset$），则对任何非空 $S\in\mathrm{Prof}_U$ 与 $e\in E(S)$，$h_\gamma(\pi(e))=\pi(e)$ 必迫使 $\gamma=1$（而 $S=\emptyset$ 时 $E(\emptyset)=\{*\}$ 平凡），故由 S3 判据 (4) 一切等变层 $E\to H$ 亦自动在 $Q=(H/\Gamma)^+$ 上可实现。

2. **内蕴稳定子与比较态射判据（源自 S3）**：
   - 不预先猜测 $D$，直接构造层商 $r:E\to E/\Gamma$ 与比较态射 $\theta_E=(\pi,r):E\to H\times_Q(E/\Gamma)$。因 $\theta_E$ 恒局部满射，可实现性等价于 $\theta_E$ 为单态射，且恰好当实现存在时 $D\cong E/\Gamma$ 为唯一实现。
   - 在截面与不动点层面上，等价于对所有 $S\in\mathrm{Prof}_U$、$e\in E(S)$ 与 $\gamma\in\Gamma$，稳定子方程 $h_\gamma(\pi(e))=\pi(e)$ 均推出 $a_\gamma(e)=e$；即对所有 $\gamma\in\Gamma$，$a_\gamma$ 在 $E\times_H h_{T^\gamma}$ 上恒等。

3. **单点检验（$S=*$）的适用边界（源自 S2 与 S4）**：
   - 由 S4，对一般层 $E\in\mathcal{C}$，仅在单点 $*$ 上检验 $h_\gamma(\pi(e))=\pi(e)\implies a_\gamma(e)=e$ **不足以**保证全局可实现（因无穷 profinite 空间不由有限个点覆盖，层在无穷紧空间上的截面不被 $*$ 上截面确定）。
   - **可用情形（S2 的推广）**：若层 $E$ **被点分离**（即对任意 $S\in\mathrm{Prof}_U$，限制映射 $E(S)\to\prod_{s\in S}E(*)$ 单射——例如所有可表示层 $E=h_X$（含 S2 中的有限集）及其子层），则由逐点检验（对每条轨道代表 $t\in T$，$\Gamma_t$ 在纤维 $E(*)_t$ 上平凡作用）**充要地**推出全局可实现性：因若 $e\in E(S)$ 满足 $h_\gamma(\pi(e))=\pi(e)$，则对每点 $s:*\to S$ 有 $\gamma\pi(e|_s)=\pi(e|_s)$ 从而 $a_\gamma(e)|_s=a_\gamma(e|_s)=e|_s$，再由点分离性即得 $a_\gamma(e)=e$。

4. **局部满射基底与联合局部满射族下降原则（源自 S5 与 S3）**：
   - **单基底检验（S5）**：给定任意局部满射态射 $B\to Q$，$E$ 在 $Q$ 上可实现当且仅当 $E\times_Q B$ 在 $B$ 上可实现。
   - **一族基底检验**：若有一族态射 $\{u_i:B_i\to Q\}_{i\in I}$（$I\in V$）**联合局部满射**（即 $\bigsqcup_{i\in I}B_i\to Q$ 局部满射：对任意 $S\in\mathrm{Prof}_U$ 与截面 $x\in Q(S)$，存在有限覆盖 $\{S_k\to S\}$ 使每片 $x|_{S_k}$ 提升至某 $B_{i_k}(S_k)$），则 $E$ 在 $Q$ 上可实现当且仅当对所有 $i\in I$，$E\times_Q B_i$ 皆在 $B_i$ 上可实现。
   - **典范可表示检验基底 $B=H\xrightarrow{q} Q$**：由 S3 的 (P1)，$q:H\to Q$ 恒局部满射且 $H=h_T$ 可表示。因此可实现性等价于拉回 $E\times_Q H$ 作为 $H\times_Q H$（$\Gamma$ 仅作用于第一因子）上的等变层可在第二因子 $H$ 上实现；在 S1/S2（或一般 $Q\cong h_{T/\Gamma}$ 可表示的情形）下，可表示基底 $h_S\to h_{T/\Gamma}$ 局部满射当且仅当连续映射 $S\to T/\Gamma$ 满射（因充分性由 $\{S\to T/\Gamma\}$ 即单元素覆盖给出，必要性由将 $\mathrm{id}_{T/\Gamma}$ 局部提升到 $S$ 给出）。

5. **非局部满射基底的失效警示（源自 S6）**：
   - 若 $B\to Q$ 未被验证为局部满射，即使 $B$ 非空可表示、甚至在 $*$ 上满射（$B(*)\to Q(*)$ 满射），在 $B$ 上的可实现性也**不能**导出原对象在 $Q$ 上的可实现性（反例 A、B）；必须核验局部满射性或补齐未覆盖的测试对象与稳定子支集。
