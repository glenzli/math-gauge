{}
### 一、审阅结论总览

针对数学正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1046-L1084) 中**“节点域加细”定义**（`#h-eddd1f2d0a9d3528` (i) 及按 `@h-ced8c7236326e104` 删除不可达子节点）与该情形下**“网络加细保持外延等价”**（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1095-L1178) 命题 `#h-012f4ba72aeb3f20` 的节点域加细分支），所给 Lean 源码采用**构造层**与**关系层**双轨并行的实现（全部既有定理均无 `sorry` 且通过 Lean 4.29.1 内核检查）：

- **构造层**：[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean)（配合 [network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean)），由分划数据 `NodePartitionData` 构造删点前网络表达 `P.presentation` 与删点后有限算子网络 `P.network := P.presentation.prune`，并证得外延算子相等 `P.network_extensional_eq`。
- **关系层**：[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)，在两个给定有限算子网络间定义结构 `NodeDomainRefinement N N'`（并封装进 `NetworkRefinement`），证明局部等价保持定理 `refinement_preserves_local_equivalence` 与网络表示保持定理 `refinement_preserves_representation`。

**总体判定：实现未能完全准确、完整地覆盖目标数学范围。** 具体体现为四方面不足：
1. **关系层定义失真（过宽/欠约束）**：`NodeDomainRefinement.choice_projection` 仅对**实际输入域的输出像** $f'_v(U'^{\mathrm{eff}}_v)$ 施加后继相容约束，对节点完整输出像中未被入口轨迹到达的点 $f'_v(U'_v)\setminus f'_v(U'^{\mathrm{eff}}_v)$ 完全失控，导致存在满足 `NodeDomainRefinement N N'` 但违背正文边域公式、非关联边不变性、终止域公式乃至破坏无环性的反例。
2. **构造层与关系层完全断连**：两文件互不导入，既未证明构造出的 `P.network` 满足 `NodeDomainRefinement N P.network`，也无法在现行定义下把关系层对象唯一归约为构造层的重编号同构类。
3. **正文集合层域公式缺失显式刻画与证明**：构造层绕过底层算子转移图而直接用路由函数 `entry`/`choice` 编码，删点前结构 `FiniteNetworkPresentation` 未定义边域/入口片/终止域；除 `local_op_eq_restrict` 和删点前自环路由引理 `self_loop_choice_iff` 外，正文中入口片、四类边域及删点前后终止域的集合等式均未作为定理写出。
4. **结论封装与对象空间 $\mathcal{X}_{\mathrm{net}}$ 衔接不完整**：未将节点域加细及外延等价保持通过编号编码提升到网络对象空间 `NetworkObject X bot`（$\mathcal{X}_{\mathrm{net}}$），`RefinementRule` 与 `NetworkRefinement` 脱钩；同时缺少对 `FiniteOperatorNetwork.ExtensionalEquivalent`、求值深度 $\ell(\mathcal N')=\ell(\mathcal N)$ 及带状态值轨迹 `TerminalTrajectoryFrom` 对应的显式封装。

---

### 二、数学定义、前提、构造与结论的逐项核对

#### 1. 前提、目标节点与有限非空分划数据
- **数学正文**（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1046-L1058)、[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1075-L1076)）：设 $\mathcal N$ 为算子网络，选定节点 $\beta\in V$，将 $U_\beta=\operatorname{dom}(f_\beta)$ 替换为有限非空分划 $U_\beta=\bigsqcup_{a=1}^q U_{\beta,a}$，并为每个子节点取 $f_{\beta,a}\in\mathcal X_{\mathrm{op}}$，满足 $\operatorname{dom}(f_{\beta,a})=U_{\beta,a}$ 且 $f_{\beta,a}\equiv_{U_{\beta,a}} f_\beta$（正文明指出 $f_{\beta,a}=f_\beta|_{U_{\beta,a}}$）。
- **Lean 对应与评价（准确）**：
  - 构造层 `NodePartitionData`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L12-L21)）与关系层 `NodeDomainRefinement` 前半部分（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L76-L89)）均以 `target : V`、`Fin count`（`0 < count`）、非空性 `nonempty`、两两互斥 `disjoint`、覆盖 `cover : (⋃ a, piece a) = N.node_dom target`、定义域等式 `local_domain` 与局部逐点一致 `local_eq` / `local_equiv` 刻画该组前提。
  - 由于算子网络要求 $\operatorname{dom}(f_\beta)\neq\emptyset$（`node_dom_nonempty`），分划块数 $q\ge 1$（`0 < count`）自动成立，用 `Fin count` 索引 $\{1,\ldots,q\}$ 不损失一般性；同时给出 `target : V` 也自动排除空网络 $\bot_{\mathrm{net}}$（$V=\emptyset, U=\emptyset$），并由无冗余节点条件 `N.node_reachable target` 隐含保证 $U\neq\emptyset$，符合正文对 $\equiv_U$ 默认 $U\neq\emptyset$ 的约定（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L314-L316)）。
  - 构造层通过 `local_op_eq_restrict`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L31-L40)）显式证明了 `P.local_op a = restrict_operator (N.node_op target) (P.piece a)`，准确对应正文“$f_{\beta,a}$ 正是 $f_\beta|_{U_{\beta,a}}$”。

#### 2. 节点替换与不可达子节点删除（`@h-ced8c7236326e104`）
- **数学正文**（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1060)、[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1083)、[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L168-L194)）：先用 $\{\beta_a\}_{a=1}^q$ 替换 $\beta$，若加细后产生不被任何输入轨迹经过的子节点，则按引理 `#h-ced8c7236326e104` 删除这些不可达节点及其关联边，保留其余局域算子、转移域和入口片。
- **Lean 对应与评价（节点集与局域算子层面准确）**：
  - 构造层以 `Label := {v : V // v ≠ target} ⊕ Fin P.count`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L42)）为删点前节点集，再通过 `FiniteNetworkPresentation.prune`（[network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L71-L110)）限制到子类型 `{v : P.Label // P.presentation.Reached v}`，并通过 `prune_choice` 将指向不可达节点的后继转为 `.stop`。
  - 关系层通过单射 `source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)`、`old_node_present`（原网络中每个 $\gamma\neq\beta$ 均可达，加细后仍可达故必保留）、`piece_node_present_iff_reached`（子节点 $\beta_a$ 保留当且仅当满足实际到达条件 `NodePieceReached N target piece a`）以及算子相容字段 `old_node_op_compat`、`piece_node_op_compat`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L51-L56)、[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L90-L102)）刻画删点后的节点集与节点算子，允许 $V'$ 采用任意同构重命名标签，这一设计在节点与局域算子层面是准确的。

#### 3. 入口输入片规则
- **数学正文**（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1060)、[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1075)）：若 $\beta$ 为入口节点，子节点入口片取 $U_\beta^{\mathrm{in}}\cap U_{\beta,a}$，其他入口片 $U_\gamma^{\mathrm{in}}$（$\gamma\neq\beta$）保持不变，空入口片省略。
- **Lean 对应与评价（语义隐含唯一但缺显式集合定理）**：
  - 构造层令 `entry x := P.lift_label (N.entry x) x.val`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L221)）。由于 $N.\mathrm{entry}(x)=\beta \implies x\in U_\beta$，`piece_at_unique` 保证 `P.network.entry_domain` 恰好给出 $U_\beta^{\mathrm{in}}\cap U_{\beta,a}$ 与不变的 $U_\gamma^{\mathrm{in}}$。
  - 关系层仅要求 `same_input_domain : N'.U = N.U` 与 `entry_projection`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L103-L106)）。之所以这已隐含唯一确定 `N'.entry`（进而确定 `N'.entry_domain`），是因为 $U$ 中每一点均为实际入口输入：`N'.entry_mem x` 强制当投影为 `target` 时 $x\in \mathrm{piece}\ a$，再由 `piece_disjoint` 与 `source_injective` 唯一锁定子节点标签。
  - **不足**：两文件均未将 `entry_domain` 的两条集合等式证明为显式定理。

#### 4. 四类边域交集公式与终止域公式
- **数学正文**（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1060-L1075)、[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1118-L1134)）：
  - 删点前对 $\gamma,\delta\neq\beta$：
    $$D'_{\gamma\to\beta_a}=D_{\gamma\to\beta}\cap U_{\beta,a},\quad D'_{\beta_a\to\gamma}=D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a}),$$
    $$D'_{\beta_a\to\beta_b}=D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b},\quad D'_{\gamma\to\delta}=D_{\gamma\to\delta},$$
    终止域由出边补集确定，满足 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$ 及 $T'_\gamma=T_\gamma$。
  - 按 `#h-ced8c7236326e104` 删除不可达子节点 $V'\setminus R$ 后，**保留节点之间的完整边域 $D'_{\eta\to\xi}$（$\eta,\xi\in R$）原样保留**（包括在未被 $U$ 中轨迹访问的输出点 $f'_\eta(U'_\eta)\setminus f'_\eta(U'^{\mathrm{eff}}_\eta)$ 上），而保留节点的终止域扩大为 $T_\eta^{\mathcal T_R}=f'_\eta(U'_\eta)\setminus\bigcup_{\xi\in\mathrm{Succ}'(\eta)\cap R} D'_{\eta\to\xi}\supseteq T'_\eta$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L184-L193)）。
- **Lean 对应与评价（关系层存在实质性偏差，构造层缺少显式定理）**：
  - **构造层**：`P.choice`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L111-L112)）与 `prune_choice`（[network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L35-L40)）诱导出的 `P.network.edge_domain` 与 `P.network.terminal_domain` 在数学上**确实满足**上述全部公式，但源码中仅证明了删点前自环路由等价式 `self_loop_choice_iff`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L119-L152)），其余入边、出边、非关联边、集合级自环边域及终止域等式均未证明，且 `FiniteNetworkPresentation` 未提供 `to_transition_graph` / `edge_domain` / `terminal_domain` 接口。
  - **关系层**：`NodeDomainRefinement.choice_projection`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L107-L111)）仅要求对 `z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v`（有效输出像）满足投影相容，**未对 `z ∈ N'.node_image v \ ((N'.node_op v).func '' N'.node_actual_input_domain v)` 作任何约束**，因此**不蕴含**正文的任何一条完整边域或终止域公式（详见第三节缺陷一及反例）。

#### 5. “网络加细保持外延等价”的证明与结论对应（`#h-012f4ba72aeb3f20`）
- **数学正文**（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1095-L1135)、[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1161-L1178)）：对每个 $x\in U$，将原终止轨迹 $\tau_x=((\gamma_1,y_1),\ldots,(\gamma_r,y_r))$ 中每次 $\gamma_s=\beta$ 按 $y_s\in U_{\beta,a_s}$ 重标为 $\beta_{a_s}$，证明新轨迹合法终止、长度仍为 $r\le\ell(\mathcal N)$、输出仍为 $y_{r+1}$；再由 `#h-ced8c7236326e104` 删去冗余节点后轨迹与输出不变，故 $\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}$（并在 $U$ 外均取 $\bot$，与全域等式 $\phi_{\mathcal N'}=\phi_{\mathcal N}$ 及外延等价 $\mathcal N'\sim_{\mathrm{op}}\mathcal N$ 一致，见 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L823-L838)）。
- **Lean 对应与评价**：
  - **构造层**严格遵循正文“先重着色轨迹 `colour_path`（`coloured_terminal`、`coloured_eval`），再经 `prune` 删去不可达节点保持路径与求值（`network_path_labels`、`network_path_projection`、`prune_eval`）”的两步结构，最终证得全域算子相等 `network_extensional_eq : P.network.extensional_operator = N.extensional_operator`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258-L269)）。
  - **关系层**反向从 $N'$ 的终止节点路径出发，沿有效输入域归纳投影回 $N$（`terminal_projection`），由确定性路径唯一性 `terminal_path_unique` 得 `path_projection`，再由 `eval_projected` 证得正文原式 `refinement_preserves_local_equivalence : LocalEquivalent N'.extensional_operator N.extensional_operator N.U`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L397)）及 `refinement_preserves_representation`（`#L404-L419`）。
  - **不足**：两层各自只陈述了一种等价结论形式，均未导出已定义的 `FiniteOperatorNetwork.ExtensionalEquivalent`（[effective_equivalence.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/effective_equivalence.lean#L1181-L1184)）或提升至 `NetworkObject.ExtensionalEquivalent`（[network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L220-L221)），亦未显式证明求值深度等式 $\ell(\mathcal N')=\ell(\mathcal N)$。

---

### 三、不足之处的具体数学影响、可复核反例与修复方向

#### 不足 1（核心定义缺陷）：`NodeDomainRefinement.choice_projection` 在非有效输出像上失控

- **问题根源**：在 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L107-L111) 中，作者注意到删去不可达子节点 $\beta_b$ 会使未到达输出点 $z\in f'_v(U'_v)\cap U_{\beta,b}$ 处的路由从 `.next (.inr b)` 变为 `.stop`，因而将 `choice_projection` 的前提直接收缩为 `z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v`（而非像同文件 `AlgebraicRefinement` 第 168–174 行那样约束整个 `N'.node_image v`）。但这把所有 $z\in f'_v(U'_v)\setminus f'_v(U'^{\mathrm{eff}}_v)$ 上的路由选择完全放空。
- **具体数学影响**：
  1. **违背边域与终止域定义（产生伪加细）**：即便分划后**所有子节点均可达、没有任何冗余节点被删除**，`NodeDomainRefinement N N'` 仍允许 $N'$ 在 $f'_v(U'_v)\setminus f'_v(U'^{\mathrm{eff}}_v)$ 上凭空捏造原网络不存在的边、删除原网络在可达节点间已有的边（参见正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1403) 习题 `#h-171f4e850e8f1c36` 关于有限算子网络存在未被入口轨迹使用的边的专门讨论），从而同时违背正文四条边域公式、非关联边不变性以及终止域不变性。
  2. **破坏无环算子网络类 $\mathcal X_{\mathrm{net}}^{\mathrm{dag}}$ 的封闭性**：按正文定义，无环网络（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1290-L1308)）经节点域加细后必仍无环（因 $\beta$ 无自环时子节点间无边，其余新边投影均为原图边）。但现行 `NodeDomainRefinement` 允许把无边无环网络“加细”为含有自环闭路甚至在未到达点上具有无限不终止求值轨迹的有环网络。
  3. **破坏对象空间 $\mathcal X_{\mathrm{net}}$ 中加细结果的唯一性**：`NetworkObject` 按完整 `PresentationData` 判等（[network_identity.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_identity.lean#L15-L45) 明确包含未到达输出上的 `edge_domain`）。现行定义下，同一原网络、同一分划与同一节点重编号可对应多个不同的 `NetworkObject`。
  4. **结构字段悬空**：在 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L177-L233) 的全部证明中，`part_count_pos`、`piece_nonempty`、`piece_disjoint`、`piece_cover`、`source_injective`、`old_node_present`、`piece_node_present_iff_reached` 七个字段从未被调用。

- **可复核反例（已在 Lean 4.29.1 内核中形式化核验）**：
  取底集 $\mathcal X=\{0,1,2,3,4\}$（吸收元 $\bot=0$），输入域 $U=\{1,3,4\}$。
  - **原网络 $\mathcal N$**：节点集 $V=\{\gamma,\beta\}$（目标节点 `target = β`），**无任何边**（`N.choice _ _ = .stop`，故对所有 $\eta,\xi$ 有 $D_{\eta\to\xi}=\emptyset$，底层图为无环图）。局域算子取域限制恒等算子：
    $$f_\gamma=\mathrm{id}_{\mathcal X}\big|_{\{1,2\}}\quad(U_\gamma=\{1,2\}),\qquad f_\beta=\mathrm{id}_{\mathcal X}\big|_{\{2,3,4\}}\quad(U_\beta=\{2,3,4\}).$$
    入口映射取 $1\mapsto\gamma$，$3\mapsto\beta$，$4\mapsto\beta$（即 $U_\gamma^{\mathrm{in}}=\{1\}$，$U_\beta^{\mathrm{in}}=\{3,4\}$）。易核对每个输入一步终止（`depth_bound = 1`），$\gamma,\beta$ 均被经过，构成合法 `FiniteOperatorNetwork`，且 $\gamma$ 的实际输入域为 $U_\gamma^{\mathrm{eff}}=\{1\}$，故 $2\in f_\gamma(U_\gamma)\setminus f_\gamma(U_\gamma^{\mathrm{eff}})$。
  - **对 $\beta$ 的非平凡二分划（$q=2$）**：取 $U_{\beta,0}=\{2,3\}$，$U_{\beta,1}=\{4\}$，$f_{\beta,0}=\mathrm{id}|_{\{2,3\}}$，$f_{\beta,1}=\mathrm{id}|_{\{4\}}$。由于入口输入 $3\in U_{\beta,0}$、$4\in U_{\beta,1}$ 一步经过 $\beta$，两片均满足 `NodePieceReached`，**不产生任何冗余子节点**。按正文定义，加细网络应当**仍然无边**（所有 $D'_{\eta\to\xi}=\emptyset$，且 $T'_\gamma=T_\gamma=\{1,2\}$）。
  - **伪加细网络 $\mathcal N'_{\mathrm{loop}}$ 与 $\mathcal N'_{\mathrm{in}}$**：取 $V'=\{0,1,2\}$，双射 `source` 为 $0\mapsto\mathrm{inl}\,\gamma$、$1\mapsto\mathrm{inr}\,0$、$2\mapsto\mathrm{inr}\,1$；输入域仍为 $U=\{1,3,4\}$，节点算子依次为 $f_\gamma,f_{\beta,0},f_{\beta,1}$，入口为 $1\mapsto 0,3\mapsto 1,4\mapsto 2$。
    - **变体 A（$\mathcal N'_{\mathrm{loop}}$）**：令 `choice 0 2 = .next 0`，其余全取 `.stop`。
      1. `FiniteOperatorNetwork` 合法性：当 $y=2\in\operatorname{dom}(f'_0)$ 时 $f'_0(2)=2\in\{1,2\}=\operatorname{dom}(f'_0)$，满足 `choice_next_mem`；而 $U=\{1,3,4\}$ 上的输出为 $1,3,4\neq 2$，各输入仍在一步内 `.stop` 终止并访问全部节点 $0,1,2$。
      2. 满足 `NodeDomainRefinement N N'_loop` 全部字段：因 `N'_loop.node_actual_input_domain 0 = {1}`，有效输出像仅为 $\{1\}$，在 $z=1$ 处两侧均为 `.stop`，而 $z=2\notin\{1\}$ 使 `choice_projection` 前件为假而空真成立。
      3. **数学违背**：$D'_{0\to 0}=\{2\}\neq\emptyset=D_{\gamma\to\gamma}$（违背“不与 $\beta$ 关联的边保持不变”）；$T'_0=\{1\}\neq\{1,2\}=T_\gamma$（违背“未被替换节点的终止域不变”）；且无环网络 $\mathcal N$ 被“加细”出了自环闭路 $0\to 0$（状态 $(0,2)$ 产生无限循环轨迹）。
    - **变体 B（$\mathcal N'_{\mathrm{in}}$）**：仅将上面改为 `choice 0 2 = .next 1`（因 $2\in\{2,3\}=\operatorname{dom}(f'_1)$，`choice_next_mem` 及 `NodeDomainRefinement` 同样全部满足）。此时 $D'_{0\to 1}=\{2\}\neq\emptyset=D_{\gamma\to\beta}\cap U_{\beta,0}$，直接证伪正文入边交集公式 $D'_{\gamma\to\beta_a}=D_{\gamma\to\beta}\cap U_{\beta,a}$。

- **修复方向**：
  直接采用正文证明（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1118-L1123)）给出的**统一边域交集定律**替换 `choice_projection`。记 $\pi := \text{node\_domain\_projection}\ \text{target}\ \text{source}$，将字段改为对保留节点集 $V'$ 上的全体边域成立：
  ```lean
  edge_domain_eq :
    ∀ v w : V',
      N'.edge_domain v w =
        N.edge_domain (node_domain_projection target source v)
          (node_domain_projection target source w) ∩
          N'.node_image v ∩ N'.node_dom w
  ```
  （若用 `choice` 表述，等价于：`∀ v : V', ∀ z ∈ N'.node_image v, ∀ w : V', N'.choice v z = .next w ↔ N.choice (π v) z = .next (π w) ∧ z ∈ N'.node_dom w`。）
  **修复有效性论证**：
  - 对任意保留节点对 $(v,w)\in V'\times V'$，分 $(\mathrm{inl}\,\gamma,\mathrm{inl}\,\delta)$、$(\mathrm{inl}\,\gamma,\mathrm{inr}\,a)$、$(\mathrm{inr}\,a,\mathrm{inl}\,\delta)$、$(\mathrm{inr}\,a,\mathrm{inr}\,b)$ 四种情形展开 `N'.node_image v` 与 `N'.node_dom w`，结合 $D_{\eta\to\xi}\subseteq f_\eta(U_\eta)\cap U_\xi$，该式逐字还原正文的全部四条边域公式；
  - 若 $z\in\mathrm{node\_image}_{N'}(v)$ 在原网络中满足 `N.choice (π v) z = .next target` 且落入某个**不可达（已被删除）**的分划片 $U_{\beta,b}$，因 $V'$ 中不存在满足 `source w = .inr b` 的节点 $w$，且其余分划片与 $U_{\beta,b}$ 互斥，对所有 $w\in V'$ 均有 $z\notin\mathrm{edge\_domain}_{N'}(v,w)$，从而自动强制 `N'.choice v z = .stop`，精确刻画 `#h-ced8c7236326e104` 删去关联边后的终止域扩张；
  - 对实际输入 $x\in U$，沿原网络终止路径 `N.path_terminal x` 归纳时，每一步到达的目标分划片均由当前前缀见证 `NodePieceReached`，故由 `old_node_present` 与 `piece_node_present_iff_reached` 必在 $V'$ 中存在对应后继节点 $w$，再由 `edge_domain_eq` 推出原有效层上的 `choice_projection` 与完整路径投影定理 `path_projection` 依然成立。

#### 不足 2：构造层与关系层缺乏双向桥接定理

- **数学影响**：[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 构造的 `P.network` 无法直接调用 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean) 中针对 `NetworkRefinement` 证明的定理（如 `refinement_preserves_representation`）；反之，关系层也未证明满足加细公理的网络本质上就是构造层所得网络（至多差一个节点重编号）。
- **修复方向**：
  1. **正向实例化桥接**：证明对任意 `P : NodePartitionData N target`（及任意双射 `e : {v // P.presentation.Reached v} ≃ W`），`P.network`（及 `P.network.relabel e`）满足修复后的 `NodeDomainRefinement N _`。
  2. **反向唯一性/完备性刻画**：在采用上述 `edge_domain_eq` 修复不足 1 后，从 `h : NodeDomainRefinement N N'` 提取 `P : NodePartitionData N h.target`，由 `source_injective`、`old_node_present` 与 `piece_node_present_iff_reached` 构造唯一双射 `e : {v // P.presentation.Reached v} ≃ V'`，证明 `(P.network.relabel e).presentation_data = N'.presentation_data`。

#### 不足 3：删点前转移图接口及正文集合层域公式缺失

- **数学影响**：正文的节点域加细定义及 `#h-012f4ba72aeb3f20` 的证明核心建立在集合层的入口片、四类边域与终止域公式（如 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$）之上。源码在 `FiniteNetworkPresentation` 中未定义转移图结构与域集合访问器，在 `domain_refinement_construction.lean` 中也未导出 `P.network` 的 `entry_domain`、四类 `edge_domain` 与删点前后 `terminal_domain` 集合等式，下游若需按正文使用节点域加细后的具体边域或终止域（如结合路径矩阵界或有效约化），缺乏直接可用的引理接口。
- **修复方向**：在 [network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean) 中为 `FiniteNetworkPresentation` 补充 `to_transition_graph`、`entry_domain`、`edge_domain`、`terminal_domain` 及其在 `prune` 下的诱导子图关系（对保留节点 `u, v`，`N.prune.edge_domain u v = N.edge_domain u.val v.val`；`N.prune.terminal_domain u ⊇ N.terminal_domain u.val`），并在 [domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 中补齐入口片（2 式）、边域（4 式）与删点前终止域 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$、$T'_\gamma=T_\gamma$ 的显式定理。

#### 不足 4：外延等价结论封装、求值深度与网络对象空间 $\mathcal X_{\mathrm{net}}$ 层衔接不完整

- **数学影响**：
  1. 正文将算子网络置于编号对象空间 $\mathcal X_{\mathrm{net}}$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L296-L301) 明确指出域加细先用不交并作标签时，作为对象空间元素使用须再经编号编码 `#h-b2fb8267687c8372`），且允许加细规则族 $R$ 是 $\mathcal X_{\mathrm{net}}$ 上允许的一步加细子关系（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/source.md#L1085-L1094)）。而 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L423-L443) 中 `RefinementRule α := α → α → Prop` 是毫无约束的任意二元关系，`NodeDomainRefinement` / `NetworkRefinement` 未通过 `NonemptyOperatorNetwork.encode`（[network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L63-L72)）提升到 `NetworkObject X bot`，因而无法在 `NetworkObject` 层推导“沿允许规则 $R$ 加细保持 `NetworkObject.ExtensionalEquivalent` 与算子表示”。
  2. 构造层仅将统一长度界设为宽松存储界 `N.depth_bound`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L225)），两文件均未显式写出求值深度保持 $\ell(\mathcal N')=\ell(\mathcal N)$（`evaluation_depth` 相等）以及底层转移图带状态值轨迹 `TerminalTrajectoryFrom`（[transition_trajectories.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/transition_trajectories.lean#L198-L205)）层面的重标对应；此外，`network_refinement.lean` 未封装 `FiniteOperatorNetwork.ExtensionalEquivalent N' N` 与全域算子等式 `N'.extensional_operator = N.extensional_operator`，`domain_refinement_construction.lean` 也未封装 `LocalEquivalent` 与 `ExtensionalEquivalent`。
- **修复方向**：
  - 由 `same_input_domain` 与 `refinement_preserves_local_equivalence` 直接补齐 `ExtensionalEquivalent N' N` 及 `N'.extensional_operator = N.extensional_operator`（构造层同理）；
  - 由路径长度逐点不变（`network_path_projection` / `path_projection`）仿照 `relabel_evaluation_depth`（[network_relabeling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_relabeling.lean#L218-L226)）补齐 `evaluation_depth` 相等定理，并结合 `terminal_path_iff_graph_trajectory` 导出状态轨迹对应；
  - 利用 `N.node_reachable target` 提取 `N.U.Nonempty`，在 `NetworkObject X bot` 上定义允许的一步加细谓词（要求两非空网络对象的代表元满足修复后的 `Nonempty (NetworkRefinement ...)`），限制允许规则 `R` 为其子关系，并导出 `NetworkObject.ExtensionalEquivalent` 保持定理。

---

### 四、源码已证明的结论与需要补充的内容对照清单

#### （一）源码已证明的结论

1. **冗余节点删除基础设施**（[network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean)）：
   - `FiniteNetworkPresentation.prune`（`#L76-L110`）：满足有限算子网络前三条条件的数据删去不可达节点后构成合法的 `FiniteOperatorNetwork`；
   - `prune_path_labels`（`#L114-L116`）、`prune_eval`（`#L127-L129`）、`prune_extensional_operator_eq`（`#L133-L141`）：删去不可达节点保持每个输入的路径节点序列、终端求值结果与吸收元补全后的全域外延算子（对应引理 `#h-ced8c7236326e104` 的求值保持核心）。
2. **构造层节点域加细与外延相等**（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean)）：
   - `NodePartitionData.local_op_eq_restrict`（`#L31-L40`）：子节点算子唯一确定为域限制算子 $f_\beta|_{U_{\beta,a}}$；
   - `mem_piece_at`、`piece_at_unique`、`lift_mem_dom`、`lift_apply`、`choice_next_mem`（`#L50-L92`、`#L154-L165`）：目标节点定义域内唯一选中所属分划片，且提升路由保持局部求值与后继定义域合法性；
   - `self_loop_choice_iff`（`#L119-L152`）：删点前子节点间自环路由 `.inr a → .inr b` 在源片输出像上当且仅当落入原自环边域 $D_{\beta\to\beta}$ 与目标片 $U_{\beta,b}$；
   - `coloured_terminal`、`coloured_eval`（`#L184-L205`）：原终止节点路径按当前输入重着色后仍是删点前表达的合法终止路径，且路径链求值不变；
   - `presentation` 与 `network`（`#L208-L235`）：构造删点前 `FiniteNetworkPresentation` 与删点后有限算子网络 `P.network`；
   - `network_path_labels`、`network_path_projection`（`#L241-L252`）：`P.network` 的路径恰为原路径的重着色，投影回 $V$ 后恢复原路径（从而逐点路径长度不变）；
   - `network_extensional_eq`（`#L258-L269`）：`P.network.extensional_operator = N.extensional_operator`（全域外延算子相等）。
3. **关系层节点域加细与局部等价/表示保持**（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)）：
   - `NodeDomainRefinement.node_eval_eq`（`#L184-L193`）：$N'$ 各节点在自身定义域上的作用与投影节点在 $N$ 中的作用逐点相等；
   - `NodeDomainRefinement.terminal_projection`、`path_projection`、`eval_projected`（`#L195-L231`）：在现行 `NodeDomainRefinement` 假设下，$N'$ 从有效输入域出发的终止路径投影为 $N$ 的终止路径，对任意输入 $x\in N'.U$ 有 `(N'.path_of x).map h.projection = N.path_of x'` 且链求值相等；
   - `NetworkRefinement.path_eval_eq`（`#L354-L369`）、`refinement_preserves_local_equivalence`（`#L377-L397`）、`refinement_preserves_representation`（`#L404-L419`）：满足 `NetworkRefinement N N'`（含 `.node_domain` 分支）时，`LocalEquivalent N'.extensional_operator N.extensional_operator N.U` 成立，且若 $N$ 表示 $\varphi$ 则 $N'$ 也表示 $\varphi$。

#### （二）需要补充或修正的内容

1. **修正 `NodeDomainRefinement` 的路由公理**（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR01/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L107-L111)）：将仅作用于有效输出像的 `choice_projection` 加强为全输出像上的统一边域交集等式 `N'.edge_domain v w = N.edge_domain (π v) (π w) ∩ N'.node_image v ∩ N'.node_dom w`，并据此重证有效层 `choice_projection` 与 `terminal_projection`，排除未到达输出点上的伪边与伪环反例。
2. **补充构造层与关系层的双向桥接定理**：证明 `NodePartitionData.network`（及其重编号网络）满足修正后的 `NodeDomainRefinement`；反之证明任意满足修正后 `NodeDomainRefinement N N'` 的 `N'` 与对应 `P.network` 差唯一节点双射且具有相同的 `PresentationData`。
3. **补充删点前转移图接口及集合层入口片、四类边域、终止域恒等式**：为 `FiniteNetworkPresentation` 增加转移图域集合定义及 `prune` 前后边域保留/终止域包含定理；显式证明节点域加细下 $U'^{\mathrm{in}}_{\beta_a}=U^{\mathrm{in}}_\beta\cap U_{\beta,a}$、$U'^{\mathrm{in}}_\gamma=U^{\mathrm{in}}_\gamma$、四类边域公式（入边、出边、自环集合等式、非关联边不变）以及删点前 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$、$T'_\gamma=T_\gamma$ 与删点后终止域刻画。
4. **补齐求值深度、状态轨迹、外延等价谓词与 `NetworkObject` 层提升**：
   - 显式导出 `FiniteOperatorNetwork.ExtensionalEquivalent`（两侧）与 `N'.extensional_operator = N.extensional_operator`（关系层）；
   - 证明求值深度等式 `evaluation_depth` 不变（对应正文 $r'\le\ell(\mathcal N)$ 及长度保持）与带状态值轨迹 `TerminalTrajectoryFrom` 的重标对应；
   - 通过 `NonemptyOperatorNetwork.encode` 将节点域加细提升至编号网络对象空间 `NetworkObject X bot`（$\mathcal X_{\mathrm{net}}$），收紧 `RefinementRule (NetworkObject X bot)` 的允许性约束，并证明允许加细步保持 `NetworkObject.ExtensionalEquivalent`。
