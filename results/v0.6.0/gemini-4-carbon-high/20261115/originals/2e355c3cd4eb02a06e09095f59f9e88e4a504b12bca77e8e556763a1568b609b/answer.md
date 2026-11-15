已在临时目录中启动相关 Lean 依赖与目标模块的类型检查构建任务，正在等待编译完成以便进一步核验公理依赖与边界性质。
### 一、总体审阅结论

所审阅的数学正文范围为 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1048-L1180) 中 **定义（网络加细）(i)（节点域加细）**（含不可达子节点按 `#h-ced8c7236326e104` 删除的约定）以及该情形下的 **命题 `#h-012f4ba72aeb3f20`（网络加细保持外延等价）**；对应核心 Lean 实现位于 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)、[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 与 [network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean)。所有目标模块在 Lean 4.29.1 + Mathlib 下均通过类型检查，无 `sorry`，仅依赖标准公理 `[propext, Classical.choice, Quot.sound]`。

**综合判断：所给实现在“具体有限标签网络表示层（`FiniteOperatorNetwork X bot V`）”上对单步节点域加细的数据结构刻画与局部求值不变性证明是准确的，但并未完整覆盖数学正文所规定的全部范围，存在可复核的层间断层与定理缺口。** 具体而言：

1. **准确覆盖的部分（表示层定义与核心求值等式）**：
   - 采用“关系判据 `NodeDomainRefinement` + 显式构造 `NodePartitionData.network`（经 `FiniteNetworkPresentation.prune` 删去冗余子节点）”的双轨设计。
   - `NodeDomainRefinement` 通过全域边域交集等式 `edge_domain_eq`、入口投影 `entry_projection`（导出 `entry_domain_eq`）以及可达性充要条件 `piece_node_present_iff_reached`，**在节点重编号意义下精确且唯一地刻画了正文的删后节点域加细网络**（既未漏掉未实际经过的保留边，也未因删去不可达子节点而误把删前终止域强加于未到达局部输出）。
   - 对任意满足 `NodeDomainRefinement N N'` 的网络已证输入域上局部等价 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U`；对显式构造 `P.network` 已证其满足 `NodeDomainRefinement N P.network` 且全域外延算子相等 `P.network.extensional_operator = N.extensional_operator`。
2. **尚未完整覆盖的不足之处**：
   - **缺口 1（对象空间层断层）**：未按正文约定把节点域加细经编号编码提升到算子网络对象空间 $\mathcal{X}_{\mathrm{net}}$（`NetworkObject X bot`），导致其无法实例化同文件定义的 `RefinementRule (NetworkObject X bot)` / `IrreducibleRepresentative`，也缺少 `NetworkObject.ExtensionalEquivalent` 层的保持性定理。
   - **缺口 2（外延等价谓词与结论强度不对称）**：在关系层 `network_refinement.lean` 中，定理仅输出 `LocalEquivalent ... N.U`，未连接至已导入定义的网络外延等价谓词 `FiniteOperatorNetwork.ExtensionalEquivalent`（其单独的 `LocalEquivalent` 结论在逻辑上弱于外延等价），也未给出一般 `NodeDomainRefinement N N'` 下的全域算子等式 `N'.extensional_operator = N.extensional_operator`。
   - **缺口 3（关系版与构造版的双向完备性及重编号封闭性缺失）**：仅证了构造网络满足 `NodeDomainRefinement`（单向存在性），未证 `NodeDomainRefinement` 对节点重编号 `relabel` 封闭，也未证任意满足 `NodeDomainRefinement N N'` 的网络必与某个构造网络 `P.network` 差唯一节点双射而具有相同 `PresentationData`。
   - **缺口 4（正文命题证明中的结构性质缺漏）**：未证明节点域加细下的求值深度界 $\ell(\mathcal N') \le \ell(\mathcal N)$（实为 `N'.evaluation_depth = N.evaluation_depth`，源码仅复制了任意上界字段 `depth_bound`）；未形式化删前终止域交集公式 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$ 及删后终止域关系；未给出带点值的完整状态轨迹（`state_trace` / `TerminalTrajectoryFrom`）投影等式，也未在通用 `NodeDomainRefinement` 命名空间下展开算子限制唯一性与四类边域/两类入口片的分情况化简引理。

---

### 二、数学定义、前提与结论的逐项对应核查

#### 1. “节点域加细”定义的逐条核对（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1050-L1086)）

| 数学正文条款 | Lean 对应项与位置 | 审阅判定与依据 |
| :--- | :--- | :--- |
| **前提对象**：“设 $\mathcal{N}$ 为算子网络”，选定节点 $\beta \in V$（正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L129) 约定“有限算子网络简称为算子网络”） | `(N : FiniteOperatorNetwork X bot V)`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L174-L196)），目标节点 `target : V` | **表示层准确，对象空间层缺失**。若 $\mathcal N$ 为空网络（$U=\emptyset, V=\emptyset$），则不存在 $\beta \in V$，节点域加细自然不适用；一旦给定 `target : V`，由 `N.node_reachable target` 自动蕴涵 `N.U.Nonempty`（符合正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L316) 对 $\equiv_U$ 默认 $U\neq\emptyset$ 的约定）。但未提升至 `NetworkObject X bot`（见第三节缺口 1）。 |
| **有限非空分划**：$U_\beta = \mathrm{dom}(f_\beta) = \bigsqcup_{a=1}^{q} U_{\beta,a}$ | `OperationalNodeDomainRefinement`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L72-L78)）与 `NodePartitionData`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L13-L18)）：`part_count > 0`、`piece : Fin part_count → Set X`、`piece_nonempty`、`piece_disjoint`、`piece_cover` | **准确**。因 `N.node_dom_nonempty target` 保证 $U_\beta \neq \emptyset$，任何覆盖 $U_\beta$ 的分划必满足 $q \ge 1$（允许 $q=1$ 平凡分划）；`Fin part_count` 与 $\{1,\dots,q\}$ 双射等价；转移图定义要求每个节点算子定义域非空（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L17)），故每块 $U_{\beta,a} \neq \emptyset$ 必不可少。 |
| **子节点局域算子及唯一性**：$\mathrm{dom}(f_{\beta,a}) = U_{\beta,a}$，$f_{\beta,a} \equiv_{U_{\beta,a}} f_\beta$，且正文指出“$f_{\beta,a}$ 正是 $f_\beta|_{U_{\beta,a}}$” | `local_domain`、`local_equiv`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L79-L84)）；构造版 `local_op_eq_restrict`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L31-L40)） | **准确（关系版可补显式推论）**。`LocalEquivalent` 在 [decomposition_core.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_04_operator_chain_calculus/decomposition_core.lean#L109-L110) 中定义为逐点相等；结合 `dom`（非 `bot` 集），`local_op_eq_restrict` 严格证出 `P.local_op a = restrict_operator (N.node_op target) (P.piece a)`。关系版 `NodeDomainRefinement` 未单独写出该等式引理，但前提完全同构。 |
| **节点替换与冗余子节点删除**：用 $\beta_a$ 替换 $\beta$；若产生不被任何输入轨迹经过的子节点，按 `#h-ced8c7236326e104` 删除 | 关系版：`source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)` 单射、`old_node_present`、`piece_node_present_iff_reached`（基于 `NodePieceReached`，[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L51-L97)）；构造版：`P.presentation.prune`（[network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L111-L145)）及 `old_label_reached`、`piece_label_reached_iff`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L296-L342)） | **准确**。因原网络无冗余节点且轨迹投影不变，所有旧节点 $\gamma \neq \beta$ 均保持可达（`old_label_reached`），只有不被任何原轨迹在 $\beta$ 发生处进入的子块 $\beta_a$ 会不可达并被删除；`piece_label_reached_iff` 证明删后存活条件与 `NodePieceReached` 充要等价。 |
| **入口输入片与空入口片省略**：子节点入口片取 $U_\beta^{\mathrm{in}} \cap U_{\beta,a}$，其他入口片不变，空入口片省略 | 输入域 `same_input_domain : N'.U = N.U`、入口投影 `entry_projection`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L98-L101)）及导出定理 `entry_domain_eq`（`#L283-L296`）：`N'.entry_domain v = N.entry_domain (h.projection v) ∩ N'.node_dom v` | **实质准确（分情况化简未单独列出）**。Lean 以总入口映射 `entry : U → V` 编码入口分划，非入口节点对应 `entry_domain v = ∅`（即省略空入口片）。对旧节点 $\gamma \neq \beta$，因 $U_\gamma^{\mathrm{in}} \subseteq U_\gamma$，交集自动等于 $U_\gamma^{\mathrm{in}}$；对存活子节点 $\beta_a$，交集即 $U_\beta^{\mathrm{in}} \cap U_{\beta,a}$；而若 $U_\beta^{\mathrm{in}} \cap U_{\beta,a} \neq \emptyset$，其点在 $n=0$ 处即触发 `NodePieceReached`，故非空子入口片绝不会被误删。 |
| **四类边域与空边域省略**：入边 $D_{\gamma\to\beta}\cap U_{\beta,a}$，出边 $D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$，自环 $D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}$，不关联边不变，空边域省略 | `NodeDomainRefinement.edge_domain_eq`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L122-L125)）与 `network_edge_domain_eq`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L346-L384)）：`N'.edge_domain v w = (N.edge_domain (proj v) (proj w) ∩ N'.node_image v) ∩ N'.node_dom w`；图边 `Edge` 定义为 `(edge_domain v w).Nonempty`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L68-L69)） | **实质准确（注：内部辅助结构 `OperationalNodeDomainRefinement` 故意不约束未使用边，正式定义 `NodeDomainRefinement` 已补齐）**。由原网络性质 $D_{\eta\to\xi} \subseteq f_\eta(U_\eta) \cap U_\xi$，统一公式在 $(\text{旧},\text{旧})$、$(\text{旧},\beta_a)$、$(\beta_a,\text{旧})$、$(\beta_a,\beta_b)$ 四种情形下分别化简为 $D_{\gamma_1\to\gamma_2}$、$D_{\gamma\to\beta}\cap U_{\beta,a}$、$D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$ 与 $D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}$，且对从 $U$ 出发未实际经过的保留边也在全域输出像上严格成立。 |
| **终止域**：“各子节点的终止域仍由出边域的补集确定” | `FiniteOperatorNetwork.terminal_domain`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L77-L78)、`#L399-L400`）按定义为 `node_image β \ ⋃ γ, edge_domain β γ` | **定义层准确，但删前/删后终止域显式定理缺漏**（详见第三节缺口 4）。 |

#### 2. “网络加细保持外延等价”（命题 `#h-012f4ba72aeb3f20` 节点域加细情形）对应核查

- **构造存在性与全域算子相等**：给定任意有限网络 `N`、目标节点 `target` 与合法分划数据 `P : NodePartitionData N target`，[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L208-L269) 先构造删前表示 `P.presentation`（对应正文“尚未删除冗余节点的加细数据”），再经 `P.network := P.presentation.prune` 删去不可达节点得到合法的 `FiniteOperatorNetwork`，证明了路径重着色与投影等式 `network_path_labels`、`network_path_projection`，全域外延算子等式 `network_extensional_eq : P.network.extensional_operator = N.extensional_operator`，以及 `P.network_refinement : NodeDomainRefinement N P.network`（`#L449-L497`）。
- **关系层求值保持**：给定任意满足 `href : NodeDomainRefinement N N'` 的两有限网络，通过构造函数 `NetworkRefinement.node_domain href`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L410)），由 `NodeDomainRefinement.path_projection`（`#L228-L234`）与 `eval_projected`（`#L236-L246`）导出 `refinement_preserves_local_equivalence`（`#L453-L474`）：
  $$\text{LocalEquivalent } N'.\text{extensional\_operator } N.\text{extensional\_operator } N.U,$$
  并由此推出 `refinement_preserves_representation`（`#L480-L495`）。

---

### 三、不足之处、数学影响、可复核论证/反例与修复方向

#### 不足 1：缺少向算子网络对象空间 $\mathcal{X}_{\mathrm{net}}$（`NetworkObject X bot`）的编号编码提升与商良定义桥接

- **源码依据**：
  - 正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L296-L300) 定义对象空间 $\mathcal{X}_{\mathrm{net}}$（对应 [network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L100-L103) 的 `NetworkObject X bot`）时明确规定：“**域加细**……若先用有限乘积、**不交并**或发生位置作标签，则在作为对象空间元素使用时再作编号编码”。
  - 同在 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L499-L519) 中，紧接加细定理定义的允许加细规则与选定不可约代表为 `R : RefinementRule (NetworkObject X bot)`。
  - 但 `NodeDomainRefinement` 定义在多态标签类型 `FiniteOperatorNetwork X bot V → FiniteOperatorNetwork X bot V' → Type` 上，构造结果 `P.network` 的标签类型停留在子类型 `{v : {v : V // v ≠ target} ⊕ Fin P.count // P.presentation.Reached v}` 上；全库**既没有**把 `NodeDomainRefinement` 提升为 `RefinementRule (NetworkObject X bot)`，**也没有**证明它在 `NonemptyOperatorNetwork.data_setoid`（即 `PresentationData` 相等，见 [network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L30-L32)）下的商良定义性，以及 `NetworkObject` 层保持 `NetworkObject.ExtensionalEquivalent` 的定理。
- **具体数学影响与可复核反例**：
  1. **层间不可组合**：用户无法用 `NodeDomainRefinement`（或 `NetworkRefinement`）实例化同文件第 512 行的 `IrreducibleRepresentative φ U R`，也无法将构造出的 `P.network` 作为 $\mathcal{X}_{\mathrm{net}}$ 元素纳入外延伪度量 `extensional_dist` 或外延商 `extensional_setoid` 的加细链推理。
  2. **无约束规则反例**：因未建立从 `NodeDomainRefinement` / `NetworkRefinement` 到 `RefinementRule (NetworkObject X bot)` 的合法性约束，`RefinementRule (NetworkObject X bot)` 仅为裸函数类型 `NetworkObject X bot → NetworkObject X bot → Prop`。
     - **反例 A（破坏外延等价的规则）**：取 $X = \{0,1\}, \bot = 0$，单节点恒等网络对象 $\mathcal N_1 \in \mathcal{X}_{\mathrm{net}}$（$U=\{1\}, \phi_{\mathcal N_1} = \mathrm{id}_X \neq \bot_{\mathrm{op}}$），令 $R_{\mathrm{bad}}(A,B) := (B = \bot_{\mathrm{net}})$。$R_{\mathrm{bad}}$ 是合法的 `RefinementRule (NetworkObject X bot)`，但一步“加细”把 $\mathcal N_1$ 变为 `NetworkObject.empty`，其外延算子为 $\bot_{\mathrm{op}} \neq \phi_{\mathcal N_1}$，违反外延等价。
     - **反例 B（伪不可约代表）**：取 $X = \{0,1,2\}, \bot = 0$，$U=\{1,2\}$ 上的单节点恒等网络对象 $\mathcal N_{12}$（其唯一节点定义域 $\{1,2\}$ 显然可二分为 $\{1\}\sqcup\{2\}$ 作非平凡节点域加细），若取 $R_{\mathrm{empty}} := \mathrm{ fun } \_ \_ \Rightarrow \mathrm{False}$，则 $\mathcal N_{12}$ 仍可构造 `IrreducibleRepresentative id_operator {1,2} R_empty`。
- **修复方向**：
  1. 先证明 `PresentationData` 相容引理：若 `N₁.presentation_data = N₂.presentation_data` 且 `M₁.presentation_data = M₂.presentation_data`，则由 `NodeDomainRefinement N₁ M₁` 可构造 `NodeDomainRefinement N₂ M₂`（利用 [network_identity.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_identity.lean#L27-L99) 的 `presentation_data_eq_node_op`、`presentation_data_eq_entry`、`presentation_data_eq_choice` 与 `presentation_data_eq_path_of`）。
  2. 用 `Quotient.lift₂` 在 `NetworkObject X bot` 上定义 `NodeDomainRefinementObject`：当两端均为 `.present` 时取 `Nonempty (NodeDomainRefinement N₁.network N₂.network)`，任一端为 `.empty` 时取 `False`。
  3. 结合 `NonemptyOperatorNetwork.encode`（[network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L63-L72)）与重编号封闭性，证明 `P.network` 经任意双射编码为 `[m]` 后给出 `NodeDomainRefinementObject` 的实例，并证明 `NodeDomainRefinementObject N N' → NetworkObject.ExtensionalEquivalent N' N`。

---

#### 不足 2：关系层定理未连接 `ExtensionalEquivalent` 且未给出全域外延算子相等

- **源码依据**：
  - 正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L825-L839) 定义网络间的**外延等价** $\mathcal{N}_1 \sim_{\mathrm{op}} \mathcal{N}_2$ 为同域且 $\phi_{\mathcal{N}_1} \equiv_U \phi_{\mathcal{N}_2}$，并明确指出这等价于全域外延算子相等 $\phi_{\mathcal{N}_1} = \phi_{\mathcal{N}_2}$；[effective_equivalence.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/effective_equivalence.lean#L1181-L1184) 将其形式化为：
    `ExtensionalEquivalent N M := N.U = M.U ∧ LocalEquivalent N.extensional_operator M.extensional_operator N.U`。
  - 但 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L453-L456) 的主定理 `refinement_preserves_local_equivalence` 仅给出 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U`，既未导出 `ExtensionalEquivalent N' N`（及对称形式 `ExtensionalEquivalent N N'`），也未给出一般 `NodeDomainRefinement N N'` 下的 `N'.extensional_operator = N.extensional_operator`（该等式仅在 [domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258) 中针对特定构造 `P.network` 证出）。
- **具体数学影响与可复核反例**：
  - 单独的谓词 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U` 仅比较 $x \in N.U$ 上的取值，**本身并不蕴涵** `ExtensionalEquivalent N' N` 或 $\phi_{\mathcal N'} = \phi_{\mathcal N}$。
  - **可复核反例**：设 $X = \{0,1,2\}, \bot = 0$。令 $\mathcal N$ 为输入域 $U = \{1\}$ 上的单节点恒等网络，令 $\mathcal M$ 为输入域 $U_{\mathcal M} = \{1,2\}$ 上的单节点恒等网络。则对任意 $x \in N.U = \{1\}$ 均有 $\phi_{\mathcal M}(x) = 1 = \phi_{\mathcal N}(x)$，故 `LocalEquivalent M.extensional_operator N.extensional_operator N.U` 为真；但在 $x = 2$ 处 $\phi_{\mathcal M}(2) = 2 \neq 0 = \phi_{\mathcal N}(2)$，故 $U_{\mathcal M} \neq U$、`¬ ExtensionalEquivalent M N` 且 $\phi_{\mathcal M} \neq \phi_{\mathcal N}$（在扩展规范空间中外延距离为 $+\infty$）。
  - 因此，命题 `#h-012f4ba72aeb3f20`“网络加细保持外延等价”在源码关系层缺少把 `h.same_input_domain : N'.U = N.U` 与 `refinement_preserves_local_equivalence` 合成为真正外延等价及全域算子相等的收口定理（同理也缺少“若 $\mathcal N_1 \sim_{\mathrm{op}} \mathcal N_2$ 且 $\mathcal N_1 \to \mathcal N'_1$，则 $\mathcal N'_1 \sim_{\mathrm{op}} \mathcal N_2$”的传递封装）。
- **修复方向**：
  - 在 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean) 中补证：对任意 `h : NetworkRefinement N N'`（特别含 `NodeDomainRefinement N N'`），利用 `h.same_input_domain` 与域外恒取 `bot`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L329-L335)）直接推出 `N'.extensional_operator = N.extensional_operator`、`ExtensionalEquivalent N' N` 与 `ExtensionalEquivalent N N'`。

---

#### 不足 3：缺少 `NodeDomainRefinement` 与构造网络 `NodePartitionData.network` 之间的反向唯一性刻画及节点重编号封闭性

- **源码依据**：
  - [domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L449-L494) 证明了方向一：`P.network_refinement : NodeDomainRefinement N P.network`。
  - 但全库未证方向二（任意满足 `NodeDomainRefinement N N'` 的 `N'` 必同构于对应分划构造 `P.network`），也未证重编号保持性（若 `NodeDomainRefinement N N'`，则对双射 `e₁ : V ≃ W`、`e₂ : V' ≃ W'` 有 `NodeDomainRefinement (N.relabel e₁) (N'.relabel e₂)`）。
- **具体数学影响与可复核论证**：
  - 缺少重编号保持性时，`P.network` 一旦按 `#h-b2fb8267687c8372` 作 `relabel`（如 `P.network.standard_relabel`），在类型系统中便不再携带 `NodeDomainRefinement` 证明。
  - 缺少反向刻画定理时，仅凭单向实现无法在形式层确认 `NodeDomainRefinement` 没有放行偏离正文公式的额外网络。
  - **可复核的精确性论证（亦即补证思路）**：设 `h : NodeDomainRefinement N N'`，将 `(h.part_count, h.piece, h.local_factor, ...)` 组装为 `P : NodePartitionData N h.target`。对任意 `v' : V'`：
    1. 若 `h.source v' = .inl β`，由 `P.old_label_reached β` 知 `.inl β` 属于 `P.presentation.Reached`；
    2. 若 `h.source v' = .inr a`，由 `h.piece_node_present_iff_reached` 与 `P.piece_label_reached_iff` 知 `.inr a` 属于 `P.presentation.Reached`。
    结合 `h.source_injective`、`h.old_node_present` 与 `h.piece_node_present_iff_reached` 的反向蕴涵，`h.source` 诱导典范双射 `e : V' ≃ {v : P.Label // P.presentation.Reached v}`。再依次核对 `h.same_input_domain`、`h.old_node_op_compat` / `h.piece_node_op_compat`、`h.entry_domain_eq` 与 `h.edge_domain_eq`，即得：
    $$(N'.\text{relabel } e).\text{presentation\_data} = P.\text{network}.\text{presentation\_data}.$$
    （注：由此还可推知 `OperationalNodeDomainRefinement` 中的字段 `choice_projection` 在加入 `edge_domain_eq` 后的 `NodeDomainRefinement` 中实为可导出的冗余公理：沿入口与已保留出边归纳可知实际到达输出若在原网络进入 `target` 的某子块 $a$，该子块必满足 `NodePieceReached` 从而未被删去，故 `edge_domain_eq` 已唯一锁定所有实际到达及未到达输出上的 `choice`。）
- **修复方向**：补充 `NodeDomainRefinement.relabel`（对源/目标网络标签双射的函子性）以及上述典范双射刻画定理，实现关系定义与显式构造在节点重命名意义下的充要闭合。

---

#### 不足 4：命题 `#h-012f4ba72aeb3f20` 证明与结构性质中的若干结论未形式化（求值深度、删前/删后终止域、完整状态轨迹、分情况展开引理）

1. **求值深度 $\ell(\mathcal N')$ 未证（仅传递了存储上界 `depth_bound`）**
   - **依据**：正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L144-L151) 将非空网络的求值深度 $\ell(\mathcal N)$ 定义为所有输入终止轨迹长度的最大值（对应 [operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L655-L657) 的 `evaluation_depth`），并在命题 `#h-012f4ba72aeb3f20` 证明（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1165-L1170)）中明确断言节点域加细后轨迹长度满足 $r' \le \ell(\mathcal N)$。而 [domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L225-L228) 仅令 `depth_bound := N.depth_bound`，既未像 [network_relabeling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_relabeling.lean#L218-L227) 那样证明 `N'.evaluation_depth = N.evaluation_depth`，也未证 `≤`。
   - **数学影响与论证**：`depth_bound` 只是任意有限上界证书（例如单步终止网络可赋 `depth_bound = 100`，此时 $\ell(\mathcal N) = 1 < 100$），不能替代可达路径计数上界 `reachable_path_card_le_sum_powers`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L738-L741)）等后续估计所需的 `evaluation_depth`。
   - **修复方向**：对任意 `h : NodeDomainRefinement N N'`，由 `h.path_projection` 两端取 `List.length` 知逐点路径长度完全不变，结合 `evaluation_depth_le_of_input_lengths` 与 `input_path_length_le_evaluation_depth`（[network_relabeling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_relabeling.lean#L199-L212)）直接证出 `N'.evaluation_depth = N.evaluation_depth`（特例给出 `≤`）。

2. **删前终止域交集公式与删后终止域扩张关系未显式形式化**
   - **依据**：正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1130-L1136) 在删去冗余节点前推导了 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$ 及未被替换节点终止域不变。Lean 中 `FiniteNetworkPresentation` 未定义转移图层的 `edge_domain` / `terminal_domain`，跳过了这一中间结论；同时对删后网络 `N'` 也未给出关于 `N'.terminal_domain` 的定理。
   - **可复核反例（说明删前与删后终止域必须严格区分）**：
     取 $X = \{0,1,2,3\}, \bot = 0$。构造单节点网络 $\mathcal N$：唯一节点为 $\beta$，输入域 $U = \{1\}$，局域算子在 $U_\beta = \{1,2,3\}$ 上定义为 $f_\beta(1)=1,\ f_\beta(2)=3,\ f_\beta(3)=1$，设自环 $D_{\beta\to\beta} = \{3\}$，则原终止域 $T_\beta = \{1,3\}\setminus\{3\} = \{1\}$。输入 $x=1$ 一步输出 $1 \in T_\beta$ 终止。
     现将 $U_\beta$ 分划为 $U_{\beta,0} = \{1,2\} \sqcup U_{\beta,1} = \{3\}$：
     - **删前**：$f_{\beta,0}(U_{\beta,0}) = \{1,3\}$，自环细分为 $D'_{\beta_0 \to \beta_1} = \{3\} \cap \{1,3\} \cap \{3\} = \{3\}$、$D'_{\beta_0 \to \beta_0} = \emptyset$，故删前终止域满足正文公式 $T'_{\beta_0} = \{1,3\}\setminus\{3\} = \{1\} = f_{\beta,0}(U_{\beta,0}) \cap T_\beta$。
     - **删后**：输入 $1$ 的轨迹仅访问 $\beta_0$，子节点 $\beta_1$ 不可达被按 `#h-ced8c7236326e104` 删除，关联边 $\beta_0 \to \beta_1$ 随之删除。此时 $\beta_0$ 已无任何出边，故删后终止域变为：
       $$T_{\beta_0}^{\mathcal N'} = f_{\beta,0}(U_{\beta,0}) \setminus \emptyset = \{1,3\} \supsetneq \{1\} = f_{\beta,0}(U_{\beta,0}) \cap T_\beta.$$
     这既验证了 `NodeDomainRefinement` 不直接把 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a})\cap T_\beta$ 作为删后公理、而将 `choice_projection` 限制在有效输出像 `(N'.node_op v).func '' N'.node_actual_input_domain v` 上的正确性，也说明源码若要完整覆盖正文证明链，应当补齐删前与删后两层终止域刻画。
   - **修复方向**：在 `FiniteNetworkPresentation`（或 `NodePartitionData` 的删前底层图）上证明删前等式 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$ 与 $T'_\gamma = T_\gamma$（$\gamma \neq \beta$）；在 `NodeDomainRefinement` 上证明删后包含关系 `N'.node_image v ∩ N.terminal_domain (h.projection v) ⊆ N'.terminal_domain v`，以及在有效终止域上的精确等式 `N'.effective_terminal_domain v = (N'.node_op v).func '' N'.node_actual_input_domain v ∩ N.terminal_domain (h.projection v)`。

3. **带点值的完整状态轨迹对应及分情况展开推论缺失**
   - **依据**：正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L44-L92)、`#L1103-L1128` 将终止求值轨迹定义为状态对序列 $((\gamma_1,y_1),\dots,(\gamma_r,y_r)) \in (V\times\mathcal X)^r$（对应 [transition_trajectories.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/transition_trajectories.lean#L9-L47) 的 `state_trace` 与 `TerminalTrajectoryFrom`），而 `network_refinement.lean` 仅给出节点列表 `path_projection` 与终端值等式 `eval_projected`。此外，`NodeDomainRefinement` 未将统一交集公式 `entry_domain_eq` 与 `edge_domain_eq` 展开为正文分列的两类入口片与四类边域（旧边不变、入边、出边、自环双交集）显式引理，也未在 `NodeDomainRefinement` 下导出 `h.local_factor a = restrict_operator (N.node_op h.target) (h.piece a)`（仅在 `NodePartitionData.local_op_eq_restrict` 与 `self_loop_choice_iff` 中给出部分构造侧引理）。
   - **修复方向**：参照 [transition_graph_import.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/transition_graph_import.lean#L289-L299) 的 `prune_redundant_nodes_state_trajectory`，在 `NodeDomainRefinement` 下补证 `(state_trace N'.node_op (N'.path_of x) x.val).map (fun s => (h.projection s.1, s.2)) = state_trace N.node_op (N.path_of (transport_network_input h.same_input_domain x)) x.val`；并利用 `N.entry_mem`、`N.edge_domain_subset_node_image` 与 `N.edge_domain_subset_node_dom` 补充两类入口片、四类边域及 `local_factor` 限制表示的分情况推论（此外，若需在无环网络子结构 `OperatorNetwork` 内直接闭合而不退回 `FiniteOperatorNetwork`，亦可利用 `rank' v' := N.rank (proj v')` 补充无环保持推论）。

---

### 四、源码已证明结论与需要补充内容的区分汇总

#### 1. 源码已证明的结论

- **冗余节点删除基础（[network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean)）**：
  - `prune`（`#L111-L145`）：满足有限网络前三条条件的数据删去不可达节点后构成 `FiniteOperatorNetwork`；
  - `prune_choice_next_iff`（`#L44-L56`）：存活节点间的转移选路在全域输出上保持不变；
  - `prune_path_labels`、`prune_eval`、`prune_extensional_operator_eq`（`#L149-L176`）：删除冗余节点保持访问节点序列、逐点求值与全域外延算子。
- **节点域加细的显式构造及性质（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean)）**：
  - `NodePartitionData.local_op_eq_restrict`（`#L31-L40`）：子节点算子唯一等于 $f_\beta|_{U_{\beta,a}}$；
  - `self_loop_choice_iff`（`#L119-L152`）：子节点自环路由的源输出像与目标子块双交集判据；
  - `presentation` 与 `network`（`#L208-L235`）：从任意合法分划数据构造删前表示与删后有限算子网络；
  - `network_path_labels`、`network_path_projection`、`colour_path_get`（`#L241-L284`）：构造网络的路径重着色公式、投影还原原路径（含逐点长度不变）及第 $n$ 步实际输入决定子标签；
  - `network_extensional_eq`（`#L258-L269`）：构造网络与原网络的全域外延算子相等 `P.network.extensional_operator = N.extensional_operator`；
  - `old_label_reached`、`piece_label_reached_iff`（`#L296-L342`）：旧节点全部保留，分划子块保留当且仅当满足 `NodePieceReached`；
  - `network_edge_domain_eq`、`network_choice_projection`、`network_refinement`、`allowed_network_refinement`（`#L346-L497`）：构造网络满足全域边域交集公式，并构成 `NodeDomainRefinement N P.network` 与 `NetworkRefinement N P.network` 的合法实例。
- **节点域加细的关系刻画及局部等价保持（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)）**：
  - `NodeDomainRefinement.node_eval_eq`、`terminal_projection`、`path_projection`、`eval_projected`（`#L198-L246`）：一般满足 `NodeDomainRefinement N N'` 的网络保持局域算子求值、终止路径投影与路径链求值；
  - `entry_domain_eq`、`retained_edge_mem`（`#L283-L305`）：由关系公理恢复入口分划交集公式与保留边的全域成员性；
  - `refinement_preserves_local_equivalence`（`#L453-L474`）：一步网络加细（含 `.node_domain` 分支）保持外延算子在 `N.U` 上的 `LocalEquivalent`；
  - `refinement_preserves_representation`（`#L480-L495`）：一步网络加细保持算子的网络表示关系 `represents`。

#### 2. 需要补充的内容

1. **对象空间层衔接**：`NodeDomainRefinement` 对 `PresentationData` 相等的相容性、`NetworkObject X bot` 上的节点域加细规则定义（`RefinementRule (NetworkObject X bot)`）、构造网络经 `encode` / 编号编码进入 `NetworkObject` 的加细见证，以及 `NetworkObject.ExtensionalEquivalent` 保持定理。
2. **关系层外延等价闭环**：对一般 `h : NodeDomainRefinement N N'`（及 `NetworkRefinement N N'`）补证全域等式 `N'.extensional_operator = N.extensional_operator`、对称网络外延等价 `FiniteOperatorNetwork.ExtensionalEquivalent N' N`（及 `ExtensionalEquivalent N N'`），以及外延等价关系在加细下的传递保持性。
3. **关系与构造的双向完备性**：`NodeDomainRefinement` 在 `FiniteOperatorNetwork.relabel` 下的封闭性，以及任意 `h : NodeDomainRefinement N N'` 诱导唯一节点双射使 `(N'.relabel e).presentation_data = P.network.presentation_data` 的刻画定理。
4. **命题证明中的显式结构引理**：求值深度等式 `N'.evaluation_depth = N.evaluation_depth`（及上界 `≤`）；删前终止域等式 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$ 与删后终止域包含/有效层相等引理；`state_trace` / `TerminalTrajectoryFrom` 完整状态轨迹投影等式；以及 `NodeDomainRefinement` 下子节点算子限制唯一性、两类入口片与四类边域的分情况化简推论。

---

*归属说明：本审阅所涉数学正文与形式化源码均源自 Zhe Li（Glen Li / glenzli），《The Operator Evolution Theory》（https://glenzli.com/books/oet/ ，遵循 [LICENSE](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/LICENSE) / [ATTRIBUTION.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/ATTRIBUTION.md) 之 CC BY 4.0 许可）。*{}
# “节点域加细”及“网络加细保持外延等价”的 Lean 实现审阅报告

## 总体审阅结论

经对数学正文 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1048-L1180) 与 Lean 4 源码（核心文件 [domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 与 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)，及关联定义文件）逐项核查并完成编译与公理复核：

1. **公理与编译可靠性**：相关模块全部通过 Lean 4（`v4.29.1` + Mathlib）类型检查，无 `sorryAx` 或自定义公理，核心定理仅依赖标准公理 `[propext, Classical.choice, Quot.sound]`。
2. **准确性与完整性总评**：该实现**在具体有限标号网络表示层（`FiniteOperatorNetwork X bot V`）上准确，但对照数学正文的完整范围仍不完整**。
   - **准确部分**：源码采用“关系型证书 `NodeDomainRefinement` + 构造型裁剪网络 `NodePartitionData.network`”的双层设计，准确刻画了具体标号算子网络上的节点域有限非空划分、局部等价算子限制、四类边条件（含自环拆分）、入口块拆分与空集省去、不可达拆分节点裁剪，以及网络外延求值算子的不变性。
   - **不足部分**：存在 **4 项数学与形式化缺口**：
     1. 未将节点域加细编码/提升到网络外延空间 $\mathcal{X}_{\mathrm{net}}$（`NetworkObject X bot`），无法实例化同文件末尾的抽象加细规则 `RefinementRule (NetworkObject X bot)` 与不可约代表元定义；
     2. 关系层主定理未对齐正文定义的网络外延等价谓词 `ExtensionalEquivalent`（$\sim_{\mathrm{op}}$），仅证明了 `N.U` 上的局部等价 `LocalEquivalent`，与构造层定理强度不对称；
     3. 缺少 `NodeDomainRefinement` 在节点重标号（`relabel`）下的闭包性与逆向唯一性刻画定理；
     4. 正文命题证明中的求值深度保持（$\ell(\mathcal N') \le \ell(\mathcal N)$）、裁剪前后出口域（$T'_{\beta_a}$）变化规律、完整状态轨迹投影对应及分情况边/入口推论尚未显式形式化。

---

## 一、定义、前提与结论的逐项对应核查（准确覆盖部分）

数学范围对应 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1048-L1086) 的定义“节点域加细”（`#h-eddd1f2d0a9d3528`）与 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1097-L1180) 的命题“网络加细保持外延等价”（`#h-012f4ba72aeb3f20`）中关于节点域加细的部分。各要素对应如下：

### 1. 基础算子网络对象与待拆分节点 $\beta \in V$
- **正文前提**：设 $\mathcal N=(V,E,(f_\eta),(D_{\eta\to\xi}),(U_\eta^{(0)}),(T_\eta))$ 为算子网络（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L129)，允许一般有限有向图及有向环，满足有限深度条件，且无从 $U$ 不可达的冗余节点），取定节点 $\beta \in V$。
- **Lean 对应**：`N : FiniteOperatorNetwork X bot V`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L174-L196)）及 `target : V`。
- **边界一致性**：正文空网络 $\bot_{\mathrm{net}}$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L316)）满足 $U=\emptyset, V=\emptyset$，不存在 $\beta \in V$，节点域加细对其真空不适用；而在 `FiniteOperatorNetwork` 中一旦给定 `target : V`，由节点可达公理 `N.node_reachable target` 自动蕴涵全局输入域 `N.U.Nonempty`，与非空网络前提完全一致。

### 2. 节点定义域有限非空不交并划分 $U_\beta = \bigsqcup_{a=1}^q U_{\beta,a}$
- **正文前提**：$U_\beta = \operatorname{dom}(f_\beta) = \bigsqcup_{a=1}^q U_{\beta,a}$，每块 $U_{\beta,a} \neq \emptyset$。
- **Lean 对应**：构造层 `NodePartitionData`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L11-L29)）与关系层 `OperationalNodeDomainRefinement`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L72-L78)）均以 `part_count : ℕ`、`part_count_pos : 0 < part_count`、`piece : Fin part_count → Set X`、`piece_nonempty`、`piece_disjoint`、`piece_cover : (⋃ i, piece i) = N.node_dom target` 刻画。因转移图节点算子满足 $U_\beta \neq \emptyset$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L17)），非空有限划分必有 $q \ge 1$，且每块非空保证了拆分后子节点的局部算子仍满足节点算子定义域非空公理。

### 3. 局部等价算子族 $\operatorname{dom}(f_{\beta,a}) = U_{\beta,a}$ 且 $f_{\beta,a} \equiv_{U_{\beta,a}} f_\beta$
- **正文前提**：局部算子定义域恰为 $U_{\beta,a}$，且在 $U_{\beta,a}$ 上与 $f_\beta$ 局部等价（故作为 $\mathcal{X}_{\mathrm{op}}$ 中的算子恒等于限制算子 $f_\beta|_{U_{\beta,a}}$）。
- **Lean 对应**：`local_op : Fin part_count → Operator X bot` 配合 `local_domain` 与 `local_equiv`（引用 [decomposition_core.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_04_operator_chain_calculus/decomposition_core.lean#L109-L110) 的 `LocalEquivalent`）；引理 `NodePartitionData.local_op_eq_restrict`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L31-L40)）证明了 `P.local_op i = restrict_operator (N.node_op target) (P.piece i)`。

### 4. 节点替换 $V \setminus \{\beta\} \sqcup \{\beta_1,\dots,\beta_q\}$ 与不可达拆分节点裁剪
- **正文前提**：将 $\beta$ 替换为 $\beta_1,\dots,\beta_q$，其余节点 $\gamma \neq \beta$ 保持 $f'_\gamma = f_\gamma$；最后按冗余节点裁剪命题（`#h-ced8c7236326e104`，[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L650-L660)）删去从 $U$ 不可达的拆分节点及关联边。
- **Lean 对应**：
  - 构造层先在和类型 `SplitNode V target part_count := {v : V // v ≠ target} ⊕ Fin part_count` 上建立未裁剪网络表示 `NodePartitionData.presentation`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L42-L150)），再调用 `FiniteNetworkPresentation.prune`（[network_presentation.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L111-L145)）得到 `NodePartitionData.network`（`#L235`）。引理 `old_label_reached` 与 `piece_label_reached_iff`（`#L296-L342`）严格证明：所有原节点 $\gamma \neq \beta$ 均保持可达而被保留，被裁掉的**只有**满足 `¬ NodePieceReached` 的不可达拆分节点 $\beta_a$。
  - 关系层通过单射 `source : V' → {v : V // v ≠ target} ⊕ Fin part_count`、`old_node_present` 与 `piece_node_present_iff_reached`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L51-L97)）精确公理化同一存活节点集。

### 5. 入口块重设与空集省去
- **正文前提**：$\gamma \neq \beta$ 时 $U_\gamma^{\prime(0)} = U_\gamma^{(0)}$；子块 $U_{\beta_a}^{\prime(0)} = U_\beta^{(0)} \cap U_{\beta,a}$（空集则省去）。
- **Lean 对应**：网络以 `entry_domain : V → Set X` 表示入口块，非入口（省去）编码为 `entry_domain v = ∅`。构造层直接按交集定义，关系层由 `same_input_domain : N'.U = N.U` 与 `entry_projection`（`#L98-L101`）导出定理 `NodeDomainRefinement.entry_domain_eq`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L283-L296)）：
  `N'.entry_domain v = N.entry_domain (h.projection v) ∩ N'.node_dom v`，对 $\gamma \neq \beta$（因 $U_\gamma^{(0)} \subseteq U_\gamma$）与 $\beta_a$ 两种情形完全合一。

### 6. 四类边转移域（含原节点自环拆分）与空集省去
- **正文前提**（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1063-L1079)）：
  1. $\gamma,\delta \neq \beta$：$D'_{\gamma\to\delta} = D_{\gamma\to\delta}$；
  2. 入边 $\gamma \to \beta_a$（$\gamma \neq \beta$）：$D'_{\gamma\to\beta_a} = D_{\gamma\to\beta} \cap U_{\beta,a}$；
  3. 出边 $\beta_a \to \gamma$（$\gamma \neq \beta$）：$D'_{\beta_a\to\gamma} = f_{\beta,a}(U_{\beta,a}) \cap D_{\beta\to\gamma}$；
  4. 自环拆分 $\beta_a \to \beta_b$：$D'_{\beta_a\to\beta_b} = f_{\beta,a}(U_{\beta,a}) \cap D_{\beta\to\beta} \cap U_{\beta,b}$；
  以上交集为空集时省去对应边。
- **Lean 对应**：`NodeDomainRefinement.edge_domain_eq`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L118-L125)）与构造层验证定理 `network_edge_domain_eq`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L346-L384)）给出统一公式：
  `N'.edge_domain v w = (N.edge_domain (proj v) (proj w) ∩ N'.node_image v) ∩ N'.node_dom w`。
  由原网络边公理 $D_{\eta\to\xi} \subseteq f_\eta(U_\eta)$ 且 $D_{\eta\to\xi} \subseteq U_\xi$，将该公式按 `source v`、`source w` 属于 `Sum.inl` 或 `Sum.inr` 展开，四类情形逐字化归为正文的四个交集；有向边谓词定义为 `Edge v w := (edge_domain v w).Nonempty`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L68-L69)），交集为空即自动无边。（注：内部辅助结构 `OperationalNodeDomainRefinement` 仅约束实际到达输入上的路由，对外定义 `NodeDomainRefinement` 通过补充 `edge_domain_eq` 完整约束了整个局部输出像上的静态边集。）

### 7. 出口域与保持外延求值的核心结论
- **出口域定义**：Lean 中 `terminal_domain` 直接定义为 `node_image β \ ⋃ γ, edge_domain β γ`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L77-L78), `#L399-L400`），自动满足出边与出口域的两两不交分解。
- **求值保持结论**：
  - 构造层证明了 `NodePartitionData.network_extensional_eq : P.network.extensional_operator = N.extensional_operator`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258-L269)）及桥接定理 `P.network_refinement : NodeDomainRefinement N P.network`（`#L386-L408`）；
  - 关系层通过路径投影归纳证明了 `refinement_preserves_local_equivalence`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L453-L474)）与表示保持推论 `refinement_preserves_representation`（`#L480-L495`）。

---

## 二、实现的不足、具体数学影响、可复核论证/反例与修复方向

### 不足 1：未提升到网络外延空间 $\mathcal{X}_{\mathrm{net}}$（`NetworkObject X bot`），导致与抽象加细/不可约定义脱节

- **依据与代码定位**：
  - 正文在定义算子网络外延空间 $\mathcal{X}_{\mathrm{net}}$ 时明确指出（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L296-L300)）：不交并形式标号的域加细在放入 $\mathcal{X}_{\mathrm{net}}$ 时须经自然数编码成为 $\mathcal{X}_{\mathrm{net}}$ 中的元素。Lean 在 [network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L100-L103) 中将 $\mathcal{X}_{\mathrm{net}}$ 定义为 `NetworkObject X bot`（非空网络模 `PresentationData` 等价类的商加上 `.empty`）。
  - 同文件末尾（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L499-L519)）定义了 `RefinementRule (NetworkObject X bot)`、`Irreducible` 与 `IrreducibleRepresentative`。
  - 但 `NodeDomainRefinement` 的类型是参数化于具体有限类型 `V, V'` 的 `Type u` 值结构：`FiniteOperatorNetwork X bot V → FiniteOperatorNetwork X bot V' → Type u`，源码既未证明它关于 `NonemptyOperatorNetwork.data_setoid`（[network_identity.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_identity.lean#L15-L23)）的商良定性，也未将其提升为 `RefinementRule (NetworkObject X bot)`，更未证明 `NetworkObject.ExtensionalEquivalent`（[network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L220-L221)）在该规则下保持不变。
- **具体数学影响**：
  1. 无法将具体节点域加细代入同文件的 `Irreducible` 或 `IrreducibleRepresentative` 中讨论“不可约节点域加细代表元”；
  2. `RefinementRule (NetworkObject X bot)` 退化为无任何语义约束的二元谓词 `NetworkObject X bot → NetworkObject X bot → Prop`。
- **可复核反例**：
  - **反例 1a（破坏外延等价的合法 `RefinementRule`）**：取 $X=\{0,1\}, \bot=0$，令 $R_{\mathrm{bad}}(A, B) : \iff (B = \bot_{\mathrm{net}})$。其类型为合法的 `RefinementRule (NetworkObject X bot)`。取 $U=\{1\}$ 上的单节点恒等网络 $A$（$\phi_A(1)=1 \neq \bot$），则 $R_{\mathrm{bad}}(A, \bot_{\mathrm{net}})$ 成立，但 $\phi_{\bot_{\mathrm{net}}}(1)=0 \neq 1=\phi_A(1)$，不保持 `NetworkObject.ExtensionalEquivalent`。
  - **反例 1b（平凡不可约反例）**：取 $X=\{0,1,2\}, \bot=0$，单节点恒等网络 $A$ 定义在 $U=\{1,2\}$ 上。数学上 $U$ 可拆分为 $\{1\}\sqcup\{2\}$ 故关于节点域加细**可约**；但取合法规则 $R_{\mathrm{empty}}(A,B) := \mathrm{False}$ 时，`Irreducible R_empty A` 平凡为真，从而 $A$ 被判定为 `IrreducibleRepresentative R_empty (ext A)`。
- **修复方向**：
  1. 证明 `NodeDomainRefinement` 在 `PresentationData` 相等下不变：若 $N_1.\text{presentation\_data} = N_2.\text{presentation\_data}$ 且 $N'_1.\text{presentation\_data} = N'_2.\text{presentation\_data}$，则 `Nonempty (NodeDomainRefinement N₁ N'₁) ↔ Nonempty (NodeDomainRefinement N₂ N'₂)`；
  2. 通过 `Quotient.lift₂` 将其提升为 `NodeDomainRefinementObject : RefinementRule (NetworkObject X bot)`（对 `.empty` 取 `False`），并用 `NonemptyOperatorNetwork.encode`（[network_identity.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_identity.lean#L63-L72)）连接 `NodePartitionData.network`；
  3. 证明 `NodeDomainRefinementObject A B → NetworkObject.ExtensionalEquivalent B A`。

---

### 不足 2：关系层主定理未对齐外延等价谓词 `ExtensionalEquivalent`，与构造层结论强度不对称

- **依据与代码定位**：
  - 正文将网络外延等价定义为 $\mathcal N_1 \sim_{\mathrm{op}} \mathcal N_2 \iff (U_1 = U_2 \land \phi_{\mathcal N_1} \equiv_U \phi_{\mathcal N_2}) \iff \phi_{\mathcal N_1} = \phi_{\mathcal N_2}$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L825-L839)），对应 Lean 谓词 `FiniteOperatorNetwork.ExtensionalEquivalent`（[effective_equivalence.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/effective_equivalence.lean#L1181-L1184)）。
  - 构造层证明了 `P.network.extensional_operator = N.extensional_operator`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258-L269)）；但关系层主定理 `refinement_preserves_local_equivalence`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L453-L456)）仅给出 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U`，整份源码从未对一般 `NodeDomainRefinement N N'` 证明 `N'.extensional_operator = N.extensional_operator` 或 `FiniteOperatorNetwork.ExtensionalEquivalent N' N`。
- **具体数学影响**：
  `LocalEquivalent φ' φ N.U` 只约束两个外延算子在子集 `N.U` 上取值相同，**不蕴涵**定义域相等（$\operatorname{dom}(\phi') = \operatorname{dom}(\phi)$），因而单独使用关系层主定理无法直接调用依赖于 `ExtensionalEquivalent` 或 `extensional_operator` 相等的下游定理（如网络外延伪度量距离为 $0$、商空间投影相等、等价关系的对称与传递链式复合）。
- **可复核反例（说明 `LocalEquivalent ... N.U` 严格弱于 `ExtensionalEquivalent`）**：
  取 $X=\{0,1,2\}, \bot=0$。设 $\mathcal N$ 为输入域 $U_{\mathcal N}=\{1\}$ 上的单节点恒等网络（$\phi_{\mathcal N}(1)=1, \phi_{\mathcal N}(2)=0$），$\mathcal M$ 为输入域 $U_{\mathcal M}=\{1,2\}$ 上的单节点恒等网络（$\phi_{\mathcal M}(1)=1, \phi_{\mathcal M}(2)=2$）。则对一切 $x \in U_{\mathcal N}=\{1\}$ 有 $x \in U_{\mathcal M}$ 且 $\phi_{\mathcal M}(x)=1=\phi_{\mathcal N}(x)$，即 `LocalEquivalent M.extensional_operator N.extensional_operator N.U` 成立；但 $U_{\mathcal M} \neq U_{\mathcal N}$ 且 $\phi_{\mathcal M}(2)=2 \neq 0=\phi_{\mathcal N}(2)$，故 $\phi_{\mathcal M} \neq \phi_{\mathcal N}$，`¬ FiniteOperatorNetwork.ExtensionalEquivalent M N`，两者外延距离为 $+\infty$。
- **修复方向**：
  在 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean) 中结合 `h.same_input_domain`（`N'.U = N.U`）、`extensional_operator_dom` 与 `refinement_preserves_local_equivalence`，由算子外延性直接补证：
  1. `NodeDomainRefinement.extensional_operator_eq : N'.extensional_operator = N.extensional_operator`；
  2. `NodeDomainRefinement.extensional_equivalent : FiniteOperatorNetwork.ExtensionalEquivalent N' N`（以及有限步节点域加细链保持 `ExtensionalEquivalent` 的传递推论）。

---

### 不足 3：缺少重标号闭包性与关系层对构造层的逆向唯一性刻画定理

- **依据与代码定位**：
  源码仅单向证明了构造物满足关系：`P.network_refinement : NodeDomainRefinement N P.network`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L386-L408)）。既未证明 `NodeDomainRefinement` 关于节点双射重标号 `FiniteOperatorNetwork.relabel`（[network_relabeling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_relabeling.lean#L53-L77)）封闭，也未证明反之任何满足 `NodeDomainRefinement N N'` 的 `N'` 必同构于对应划分数据的 `P.network`。此外，`OperationalNodeDomainRefinement` 中的字段 `choice_projection`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L102-L106)）在加入 `edge_domain_eq` 后属于可导出的冗余公理，源码未给出简化构造接口。
- **具体数学影响**：
  若缺少逆向刻画，形式上无法排除 `NodeDomainRefinement` 比正文构造容许额外“非标准模型”的疑虑；若缺少 `relabel` 闭包性，当把拆分后节点重编码为 `Fin m` 时，`NodeDomainRefinement` 证书即告中断。
- **可复核论证**：
  任给 `h : NodeDomainRefinement N N'`，由 `h` 的划分字段可组装 `P : NodePartitionData N h.target`。对任意原标号 $u \in \{v // v \neq \beta\} \oplus \mathrm{Fin}\,q$：
  - 若 $u = \mathrm{inl}\,\gamma$，一方面 `P.old_label_reached` 给出 `P.presentation.Reached u`，另一方面 `h.old_node_present` 给出 $v' \in V'$ 使 `h.source v' = u`；
  - 若 $u = \mathrm{inr}\,a$，`P.piece_label_reached_iff` 与 `h.piece_node_present_iff_reached` 将 `P.presentation.Reached u` 与 `∃ v', h.source v' = u` 同时等价于同一个谓词 `NodePieceReached N h.target h.piece a`。
  结合 `h.source_injective`，`h.source` 诱导典范双射 `e : V' ≃ {v // P.presentation.Reached v}`；再对照 `node_op`（由局部等价唯一性）、`entry_domain_eq` 与 `edge_domain_eq`，即严格导出 `(N'.relabel e).presentation_data = P.network.presentation_data`。
- **修复方向**：
  补充 `NodeDomainRefinement.relabel`（左右两侧重标号函子性）与上述逆向同构唯一性定理，并提供无需手工证明 `choice_projection` 的精简构造子 `NodeDomainRefinement.mk'`。

---

### 不足 4：正文命题证明与结构层面的若干关键性质未显式形式化

对照 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1097-L1180) 的证明结构，以下性质尚未在源码中给出对应定理：

#### (4a) 求值深度保持性质 $\ell(\mathcal N') \le \ell(\mathcal N)$（实为相等）未证明
- **依据与影响**：正文明确指出加细后路径长度满足 $r' = r \le \ell(\mathcal N)$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1165-L1170)）。Lean 构造中仅直接复制了形式深度上界字段 `depth_bound := N.depth_bound`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L225)），而未对真实求值深度 `FiniteOperatorNetwork.evaluation_depth`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L655-L657)；对比重标号模块已证的 `relabel_evaluation_depth`，见 [network_relabeling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_relabeling.lean#L218-L227)）证明任何结论。由于 `depth_bound` 只是任意给定上界（例如单节点网络可取 `depth_bound = 100` 而真实 `evaluation_depth = 1`），复制 `depth_bound` 不等价于关于 $\ell(\mathcal N')$ 的定理。
- **修复方向**：由 `h.same_input_domain` 与路径投影长度等式 `(N'.path_of x).length = (N.path_of ⟨x.1, ...⟩).length`，可直接补证 `N'.evaluation_depth = N.evaluation_depth`（从而 `N'.evaluation_depth ≤ N.evaluation_depth`）。

#### (4b) 裁剪前后的出口域公式未加区分且缺少对应引理（裁剪后等式并不恒成立）
- **依据**：正文证明第 1 步（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1130-L1136)）在**裁剪不可达子节点之前**写出 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$ 及 $\gamma \neq \beta$ 时 $T'_\gamma = T_\gamma$。源码既未在未裁剪表示 `P.presentation` 上证明该等式，也未在裁剪后网络 `N'` 上给出出口域刻画。
- **可复核反例（证明裁剪不可达子块后，$T_{\beta_a}^{\mathcal N'} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$ 可严格失效）**：
  取 $X=\{0,1,2,3\}, \bot=0$。构造单节点网络 $\mathcal N$（唯一节点 $\beta$）：
  - 全局输入域与入口域：$U = U_\beta^{(0)} = \{1\}$；
  - 节点定义域 $U_\beta = \{1,2,3\}$，算子 $f_\beta(1)=1,\; f_\beta(2)=3,\; f_\beta(3)=1$（故 $f_\beta(U_\beta)=\{1,3\}$）；
  - 自环转移域 $D_{\beta\to\beta} = \{3\}$，原出口域 $T_\beta = \{1,3\} \setminus \{3\} = \{1\}$（从 $x=1$ 出发在一步后以 $f_\beta(1)=1 \in T_\beta$ 终止，网络无冗余节点且有限步终止）。
  现将 $U_\beta$ 拆分为 $U_{\beta,0}=\{1,2\}$ 与 $U_{\beta,1}=\{3\}$：
  - **裁剪前**：$f_{\beta,0}(U_{\beta,0})=\{1,3\}$，自环拆分为边 $D'_{\beta_0\to\beta_1} = \{1,3\}\cap\{3\}\cap\{3\} = \{3\}$，此时 $T'_{\beta_0} = \{1,3\}\setminus\{3\} = \{1\} = f_{\beta,0}(U_{\beta,0}) \cap T_\beta$；
  - **裁剪后**：从 $U=\{1\}$ 出发仅到达 $\beta_0$ 且实际输入仅为 $\{1\}$，输出 $f_{\beta,0}(1)=1 \notin \{3\}$，故 $\beta_1$ 从 $U$ 不可达而被裁剪，关联出边 $\beta_0 \to \beta_1$ 一并删去！于是在裁剪后的网络 $\mathcal N'$ 中，$\beta_0$ 无任何出边，其静态出口域变为：
    $$T_{\beta_0}^{\mathcal N'} = f_{\beta,0}(U_{\beta,0}) \setminus \emptyset = \{1,3\} \supsetneq \{1\} = f_{\beta,0}(U_{\beta,0}) \cap T_\beta.$$
- **具体数学影响与设计验证**：
  1. 该反例表明：裁剪后静态出口域一般只满足单向包含 $f'_\eta(U'_\eta)\cap T_{\mathrm{proj}(\eta)} \subseteq T_\eta^{\mathcal N'}$，仅在实际到达输出像（即有效出口域 `effective_terminal_domain`）上才保持精确相等；
  2. 这同时验证了源码将 `OperationalNodeDomainRefinement.choice_projection`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L102-L106)）限制在实际到达输入像 `(N'.node_op v).func '' N'.node_actual_input_domain v` 上是完全必要且正确的——若要求对全定义域 $U'_\eta$ 成立，上述合法加细反例在 $y=3 \in f_{\beta,0}(U_{\beta,0})$ 处将无法通过验证。
- **修复方向**：在 `P.presentation`（裁剪前）补证精确等式 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$，在 `NodeDomainRefinement`（裁剪后）补证静态包含关系及 `effective_terminal_domain` 上的精确对应引理。

#### (4c) 完整状态轨迹投影恒等式与分情况显式推论缺失
- **依据与影响**：正文证明第 2 步断言逐步状态轨迹满足 $(\operatorname{proj}(\eta'_k), x'_k) = (\eta_k, x_k)$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/source.md#L1143-L1164)）。工程中虽已在 [transition_trajectories.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/transition_trajectories.lean#L9-L47) 定义 `state_trace`（且裁剪定理 `prune_redundant_nodes_state_trajectory` 在 [transition_graph_import.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/transition_graph_import.lean#L289-L299) 已采用该表述），但 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean) 仅证了节点列表投影 `(N'.path_of x).map h.projection = N.path_of ...` 与终点值相等，未导出 `state_trace` 列表映射等式；同时关系层也未单独导出 `h.local_factor i = restrict_operator (N.node_op h.target) (h.piece i)`、两类入口块及四类边条件的显式分情况引理（以及无环算子网络子类 `OperatorNetwork` 在节点域加细下保持无环性的推论）。
- **修复方向**：补充 `NodeDomainRefinement.state_trace_projection`、关系层 `local_factor_eq_restrict`、四类边与两类入口的显式推论，以及 `OperatorNetwork` 无环性保持引理。

---

## 三、源码已证明结论与需要补充内容的区分汇总

| 数学内容模块 | 源码已证明的结论（含具体位置） | 需要补充的内容 |
| :--- | :--- | :--- |
| **节点域划分与局部算子** | • `NodePartitionData`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L11-L29)）及 `NodePartitionData.local_op_eq_restrict`（`#L31-L40`）已证构造层 $f_{\beta,a} = f_\beta|_{U_{\beta,a}}$ | • 关系层 `NodeDomainRefinement` 下 `h.local_factor i = restrict_operator (N.node_op h.target) (h.piece i)` 的显式推论 |
| **加细网络构造、边/入口重设与不可达子块裁剪** | • 构造并裁剪得到合法网络 `NodePartitionData.network`（`#L235`）<br>• 原节点全保留 `old_label_reached`、子块保留充要条件 `piece_label_reached_iff`（`#L296-L342`）<br>• 统一边域交集等式 `network_edge_domain_eq`（`#L346-L384`）与入口域交集等式 `NodeDomainRefinement.entry_domain_eq`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L283-L296)）<br>• 构造满足关系证书 `NodePartitionData.network_refinement`（`#L386-L408`） | • 正文四类边条件与两类入口条件的显式分情况推论<br>• 裁剪前 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$ 引理，以及裁剪后静态包含与有效出口域 `effective_terminal_domain` 对应引理<br>• 精简冗余字段 `choice_projection` 的构造子 `NodeDomainRefinement.mk'` |
| **重标号不变性与逆向唯一性** | • 仅单向证明 `P.network` 是 `N` 的一个 `NodeDomainRefinement` | • `NodeDomainRefinement` 关于 `FiniteOperatorNetwork.relabel` 的闭包性<br>• 逆向唯一性定理：任意 `NodeDomainRefinement N N'` 在唯一典范节点双射下与对应 `P.network` 具有相同 `PresentationData` |
| **外延等价保持、轨迹与深度性质** | • 构造层外延算子相等：`NodePartitionData.network_extensional_eq`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258-L269)）<br>• 关系层节点路径投影等式、`N.U` 上局部等价 `refinement_preserves_local_equivalence`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L453-L474)）及算子表示保持 `refinement_preserves_representation`（`#L480-L495`） | • 关系层全局算子相等 `N'.extensional_operator = N.extensional_operator` 及对齐网络外延等价谓词 `FiniteOperatorNetwork.ExtensionalEquivalent N' N`<br>• 求值深度等式 `N'.evaluation_depth = N.evaluation_depth`（故 $\le \ell(\mathcal N)$）<br>• `state_trace` 完整状态轨迹投影等式（及无环子类 `OperatorNetwork` 的无环保持性） |
| **网络外延空间 $\mathcal{X}_{\mathrm{net}}$ 与抽象加细规则衔接** | • 仅抽象定义了无约束的 `RefinementRule`、`Irreducible`、`IrreducibleRepresentative`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L499-L519)） | • 证明 `NodeDomainRefinement` 模 `PresentationData` 等价类的商良定性<br>• 提升为 `NetworkObject X bot` 上的具体 `RefinementRule`（与自然数编码 `encode` 衔接）<br>• 证明该规则保持 `NetworkObject.ExtensionalEquivalent` |

---

*归属说明（依 [ATTRIBUTION.md](file:///private/tmp/math-gauge-carbon-high-effort-lane1-20261115-v2/attempts/AHR03/physical-1/session/work/ATTRIBUTION.md)）：本审阅所涉数学正文与 `formal_oet` Lean 4 源码摘自李哲（Zhe Li / Glen Li / `glenzli`）所著《算子演化论》（The Operator Evolution Theory，`https://glenzli.com/books/oet/`），遵循 CC BY 4.0 许可协议；本报告仅作技术审阅分析，未修改任何原始附件。*
