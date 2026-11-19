### 总体判定

所给 Lean 实现对数学正文中**“节点域加细”定义**（`#h-eddd1f2d0a9d3528`）及该情形下**“网络加细保持外延等价”**（`#h-012f4ba72aeb3f20`）的覆盖**不完全准确且不完整**。

代码将该范围拆分为两条**互不导入、彼此独立**的实现路径：
1. **关系式定义与等价性证明**：[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L73-L112) 定义二元关系结构 `FiniteOperatorNetwork.NodeDomainRefinement N N'`，并在 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L420) 中证明外延算子在输入域 `N.U` 上局部等价及网络表示保持。
2. **构造式实现与等价性证明**：[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L12-L270) 从分划数据 `NodePartitionData N target` 出发构造并剪枝得到具体网络 `P.network`，直接证明全域外延算子相等 `P.network.extensional_operator = N.extensional_operator`。

**核心审阅结论如下：**
- **构造侧的求值与外延保持已完整证明**：`P.network` 的构造在数学上忠实实现了正文的节点域加细及冗余子节点删除，且全域外延算子相等已严格证明；但四类新边域（除剪枝前的自环路由外）、入口片和终止域的集合交集公式，以及“仅不可达子节点被删、原非目标节点全部保留”均未在源码中写出验证定理。
- **关系侧定义 `NodeDomainRefinement` 存在实质性欠约束（定义不准确）**：`choice_projection` 字段仅对**节点实际输入域的输出像** `(N'.node_op v).func '' N'.node_actual_input_domain v` 施加投影约束，而对节点定义域内未被初始输入轨迹实际到达的输出 `N'.node_image v \ (N'.node_op v).func '' N'.node_actual_input_domain v` 完全放空。这导致 `NodeDomainRefinement` 允许目标网络 `N'` 无中生有伪造自环/有向环，或删改与被加细节点 $\beta$ 完全不关联的原有边域，违背正文的边域定义与冗余删除引理 `#h-ced8c7236326e104`。
- **双轨桥接与对象空间提升缺失（覆盖不完整）**：源码既未证明构造出的 `P.network` 满足 `NodeDomainRefinement N P.network`，也未将节点域加细提升到编号网络对象空间 `NetworkObject X bot`（$\mathcal{X}_{\mathrm{net}}$），导致其无法直接接入同文件定义的不可约代表接口 `IrreducibleRepresentative`（要求 `RefinementRule (NetworkObject X bot)`）。

---

### 一、逐项数学对照与依据说明

对照正文 `#h-eddd1f2d0a9d3528`（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1046-L1084)）与命题 `#h-012f4ba72aeb3f20`（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1095-L1178)）的各项条款：

#### 1. 前提对象、目标节点与有限非空分划（准确覆盖）
- **数学正文**：给定算子网络 $\mathcal{N}$，选定节点 $\beta \in V$，将 $U_\beta = \operatorname{dom}(f_\beta)$ 替换为有限非空分划 $U_\beta = \bigsqcup_{a=1}^q U_{\beta,a}$（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1046-L1051)）。
- **实现对应**：
  - 空网络 $\bot_{\mathrm{net}}$ 的节点集 $V = \emptyset$（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L129-L130)），不存在可选节点 $\beta$，故不适用节点域加细；而在 `FiniteOperatorNetwork X bot V` 中，一旦给定 `target : V`，由无冗余节点公理 `node_reachable`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L195-L196)）自动保证 $U \neq \emptyset$，与正文“凡使用 $\equiv_U$ 均默认 $U \neq \emptyset$”（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L316)）完全一致。
  - `NodeDomainRefinement` 的 `part_count_pos : 0 < part_count`、`piece_nonempty`、`piece_disjoint`、`piece_cover`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L77-L83)）与 `NodePartitionData` 的同名字段（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L13-L18)）精确对应 $q \ge 1$ 及非空两两不交覆盖 $U_\beta$（各分块非空也确保新子节点满足转移图定义域非空条件 `node_dom_nonempty`）。

#### 2. 子节点局域算子与域限制唯一性（准确覆盖）
- **数学正文**：每个子节点取 $f_{\beta,a} \in \mathcal{X}_{\mathrm{op}}$，满足 $\operatorname{dom}(f_{\beta,a}) = U_{\beta,a}$ 且 $f_{\beta,a} \equiv_{U_{\beta,a}} f_\beta$，并指出 $f_{\beta,a} = f_\beta|_{U_{\beta,a}}$；其余节点局域算子不变（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1052-L1058)、[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1075)）。
- **实现对应**：
  - 关系侧通过 `local_domain`、`local_equiv`、`old_node_op_compat`、`piece_node_op_compat`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L84-L102)）逐项对应，并导出求值一致引理 `node_eval_eq`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L184-L193)）。
  - 构造侧通过 `local_domain`、`local_eq`（与 [decomposition_core.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_04_operator_chain_calculus/decomposition_core.lean#L109-L110) 的 `LocalEquivalent` 定义一致）给出，并在 `local_op_eq_restrict`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L31-L41)）中证明了 $f_{\beta,a} = f_\beta|_{U_{\beta,a}}$。

#### 3. 节点集替换与不可达子节点删除（语义正确，但构造侧缺显式刻画引理）
- **数学正文**：用 $\beta_a$ 替换 $\beta$；若产生不被任何输入轨迹经过的子节点，按引理 `#h-ced8c7236326e104` 删除（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1060)、[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1083)）。
- **实现对应**：
  - 关系侧通过 `source_injective`、`old_node_present` 与 `piece_node_present_iff_reached`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L90-L97)）明确规定：`V'` 精确双射于“全部原非目标节点 `{β : V // β ≠ target}`”与“满足 `NodePieceReached N target piece a` 的可达分划片子节点”的不交并。
  - 构造侧令 `P.network := P.presentation.prune`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L235)），利用通用剪枝 [network_presentation.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L70-L110) 保留 `Reached` 节点。由原网络的 `N.node_reachable`，每个 `.inl ⟨γ, hγ⟩`（$\gamma \neq \beta$）必被保留，且 `.inr a` 被保留当且仅当 `NodePieceReached N target P.piece a`；故数学上只删除不可达子节点，但源码**未证明**这两条节点保留性质。

#### 4. 入口节点与入口输入片细分（隐式唯一确定，但缺导出引理）
- **数学正文**：若 $\beta$ 为入口节点，子节点入口片取 $U_\beta^{\mathrm{in}} \cap U_{\beta,a}$，其他入口片保持不变，空入口片省略（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1060-L1075)）。
- **实现对应**：
  - 在 `NodeDomainRefinement` 中，尽管仅要求 `same_input_domain : N'.U = N.U` 与 `entry_projection`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L103-L106)），但结合有限网络自带的 `N'.entry_mem`、`piece_node_op_compat`、`local_domain`、`piece_disjoint` 及 `source_injective`，**在数学上已唯一确定 `N'.entry` 并严格推出**：
    - 当 `source β' = .inl β` 时，`N'.entry_domain β' = N.entry_domain β.val`；
    - 当 `source β' = .inr a` 时，`N'.entry_domain β' = N.entry_domain target ∩ piece a`（若该交集非空，取其中一点 $x$ 即知 $a$ 在第 $0$ 步可达，故非空子入口片绝不会被剪枝遗漏）。
  - 构造侧 `entry := fun x => P.lift_label (N.entry x) x.val`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L221)）同样实现该分配，但两侧源码均未将上述 `entry_domain` 集合等式证成定理。

#### 5. 四类新边域与终止域公式（关系侧存在实质漏约束；构造侧缺剪枝后验证引理）
- **数学正文**：明确规定入边 $D'_{\gamma\to\beta_a}=D_{\gamma\to\beta}\cap U_{\beta,a}$、出边 $D'_{\beta_a\to\gamma}=D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$（$\gamma\neq\beta$）、自环细分 $D'_{\beta_a\to\beta_b}=D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}$，**不与 $\beta$ 关联的边保持不变**（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1060-L1075)）；随后按引理 `#h-ced8c7236326e104` 删除不可达子节点及关联边时，取诱导边集 $E_R = E' \cap (R \times R)$ 并**保留其余转移域**（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L168-L193)）。
  注意在整章体系中，有限算子网络的边域 $D_{\eta\to\xi}$ 定义在完整节点输出像 $f_\eta(U_\eta)$ 上，允许包含未被初始输入域 $U$ 的求值轨迹实际经过的边或输出点（参见正文有效约化 [source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L630-L663)、习题 `#h-171f4e850e8f1c36` [source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1403)，以及 [network_identity.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_identity.lean#L41-L45) 关于原始网络数据 `PresentationData` 的说明）。
- **实现偏差**：
  - **关系侧 `NodeDomainRefinement`（不准确）**：[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L107-L111) 的 `choice_projection` 仅要求：
    ```lean
    ∀ (v : V') (z : X), z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v →
      map_output_choice (node_domain_projection target source) (N'.choice v z) =
        N.choice (node_domain_projection target source v) z
    ```
    作者注释 `-- Pruning may change choices at outputs never reached from the source` 指出了真实原因：若 $z \in f'_v(U'_v) \setminus f'_v(U_v^{\prime\,\mathrm{eff}})$ 在原网络中进入 $\beta$ 的某个**不可达子分块** $U_{\beta,c}$，剪枝会将该转移改为 `.stop`，此时简单投影等式不再成立。但实现并未刻画“仅当目标落入被删子分块时转为 `.stop`，指向保留节点的转移不变”，而是直接把约束域缩减到有效输出像 `(N'.node_op v).func '' N'.node_actual_input_domain v`，导致在 `N'.node_image v \ (N'.node_op v).func '' N'.node_actual_input_domain v` 上 `N'.choice` 完全失控（详见第二节反例）。
  - **构造侧 `NodePartitionData`（实现正确但验证不完整）**：`P.choice`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L111-L112)）配合 `prune_choice`（[network_presentation.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L35-L40)）确实只在目标落入不可达分块时转为 `.stop`，精确保留了所有保留节点间的四类边域公式；但源码只证明了剪枝前自环路由等价式 `self_loop_choice_iff`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L119-L152)），未证明剪枝后 `P.network.edge_domain`（含入边、出边、自环、不关联边）与 `terminal_domain` 的交集公式。

#### 6. 命题 `#h-012f4ba72aeb3f20`（网络加细保持外延等价）与对象空间接口
- **数学正文**：若 $\mathcal{N}'$ 由 $\mathcal{N}$ 经一次节点域加细得到，则 $\phi_{\mathcal{N}'} \equiv_U \phi_{\mathcal{N}}$（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1095-L1098)）；在同输入域 $U$ 上，正文定义外延等价 $\mathcal{N}_1 \sim_{\mathrm{op}} \mathcal{N}_2$ 为 $\phi_{\mathcal{N}_1} \equiv_U \phi_{\mathcal{N}_2}$，并指出因域外均取 $\bot$，等价于全域算子相等 $\phi_{\mathcal{N}_1} = \phi_{\mathcal{N}_2}$（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L395-L399)、[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L825-L837)）。
- **实现对应**：
  - 关系侧证明了路径投影等式 `NodeDomainRefinement.path_projection`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L214-L220)）、局部等价保持 `refinement_preserves_local_equivalence`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L398)）以及表示保持 `refinement_preserves_representation`（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L404-L420)）。由于 `U` 上的求值轨迹每一步都落在 `node_actual_input_domain` 内，`NodeDomainRefinement` 作为正文条件的**弱化前提**仍足以推出 $\phi_{\mathcal{N}'} \equiv_U \phi_{\mathcal{N}}$，因此该蕴含定理本身在逻辑上成立。
  - 构造侧证明了路径重着色与投影等式 `network_path_labels`、`network_path_projection` 及全域算子等式 `network_extensional_eq : P.network.extensional_operator = N.extensional_operator`（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L241-L270)）。
  - **缺失环节**：
    1. 关系侧未将 `same_input_domain` 与 `refinement_preserves_local_equivalence` 封装为同章定义的 `FiniteOperatorNetwork.ExtensionalEquivalent`（[effective_equivalence.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/effective_equivalence.lean#L1181-L1184)）或全域算子相等；构造侧未导出 `LocalEquivalent` 或 `ExtensionalEquivalent`；两侧均未显式导出正文证明中给出的求值深度保持/上界 `evaluation_depth`（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1163-L1168)）。
    2. 源码未证明构造网络 `P.network` 满足关系 `NodeDomainRefinement N P.network`。
    3. 同文件在 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L423-L443) 中将 `IrreducibleRepresentative` 定义在 `RefinementRule (NetworkObject X bot)` 上，与正文在编号网络对象空间 $\mathcal{X}_{\mathrm{net}}$ 上定义加细规则与外延商（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L300)、[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1085-L1093)）一致；但 `NodeDomainRefinement` 跨不同顶点类型 `V` 与 `V'`，并未通过 [network_relabeling.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_relabeling.lean#L53-L77) 和 [network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L63-L110) 提升为 `NetworkObject X bot` 上的二元关系及 `NetworkObject.ExtensionalEquivalent` 保持定理。

---

### 二、不足之处的具体数学影响、可复核反例与修复方向

#### 1. 具体数学影响

1. **违反四类边域公式与无环性保持（破坏 $\mathcal{X}_{\mathrm{net}}^{\mathrm{dag}}$ 封闭性）**：
   按正文定义，对无环算子网络 $\mathcal{N} \in \mathcal{X}_{\mathrm{net}}^{\mathrm{dag}}$（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1290-L1308)）作任意节点域加细，由于原网络中 $\beta$ 无自环（$D_{\beta\to\beta}=\emptyset$）且任何新边投影后均为原图中的边，加细结果 $\mathcal{N}'$ **必然仍无环**。但在 `NodeDomainRefinement` 下，即便所有子节点均可达（不触发任何节点删除），`N'` 仍可在非实际到达输出点上凭空添加自环或有向环，使无环网络“加细”出含环且在非入口状态上无限不终止的网络。
2. **篡改与被加细节点 $\beta$ 不关联的边域**：
   当原网络存在满足 $U_\gamma^{\mathrm{eff}} \subsetneq U_\gamma$ 的其他节点 $\gamma, \delta \neq \beta$ 时，`NodeDomainRefinement` 允许直接删去或改接 $\gamma \to \delta$ 在 $f_\gamma(U_\gamma) \setminus f_\gamma(U_\gamma^{\mathrm{eff}})$ 上的转移域，直接违背正文“不与 $\beta$ 关联的边和其他入口输入片保持不变”（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1075)）。
3. **污染对象空间相等判定与不可约性 `Irreducible`**：
   在 [network_identity.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_identity.lean#L15-L24) 与 [network_extensional_space.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L114-L121) 中，`NetworkObject` 的相等性由完整 `PresentationData`（含全 `node_image` 上的 `edge_domain`）决定。由于 `NodeDomainRefinement` 未固定非有效输出上的 `edge_domain`，同一组 `(N, target, piece)` 可对应多个不同的 `NetworkObject`；甚至取 $q = 1$（未作任何实质分划）时，仅改动 $U_\beta \setminus U_\beta^{\mathrm{eff}}$ 上的边域即可在同一节点集上产生 $N \neq N'$ 的“一步节点域加细”，破坏不可约性判据与关系侧—构造侧的唯一对应。

#### 2. 可复核反例

以下两个有限反例均可按 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L73-L112) 的逐字段定义直接核验（其中底空间均取 $X = \mathrm{Fin}\,4 = \{0,1,2,3\}$，吸收元 $\bot = 0$，记 $f_{\mathrm{all}} = \mathrm{id}_X$，其定义域为 $\operatorname{dom}(f_{\mathrm{all}}) = \{1,2,3\}$）：

##### 反例 A：原网络无任何边且无需删点，但 `NodeDomainRefinement` 允许伪造非空自环
- **原网络 $\mathcal{N}$**（类型 `FiniteOperatorNetwork (Fin 4) 0 Unit`）：
  - 输入域 $U = \{1, 2\}$，唯一节点 $V = \{()\}$，局域算子 $f_{()} = f_{\mathrm{all}}$（故 $U_{()} = \{1,2,3\}$）；
  - 入口映射将 $1, 2$ 均送入 $()$，`choice _ _ = .stop`，终止路径恒为 `[()]`（深度界 $1$）。
  - 此时 $\mathcal{N}$ **没有任何边**（`N.edge_domain () () = ∅`），是无环算子网络。
- **分划数据与网络 $\mathcal{N}'$**（类型 `FiniteOperatorNetwork (Fin 4) 0 (Fin 2)`）：
  - 对 `target = ()` 取 $q = 2$ 分划：$U_0 = \{1\}$，$U_1 = \{2, 3\}$，局域算子 $f_0 = f_{\mathrm{all}}|_{\{1\}}$，$f_1 = f_{\mathrm{all}}|_{\{2,3\}}$；
  - 入口映射：`entry 1 = 0`，`entry 2 = 1`；路径 `path_of 1 = [0]`，`path_of 2 = [1]`。两个子节点 $0, 1$ 均被 $U = \{1,2\}$ 中的输入访问，**无冗余子节点产生**。
  - 令 $\mathcal{N}'$ 的路由函数为：
    $$\mathrm{choice}'(v, z) = \begin{cases} \mathrm{next}\ 1, & v = 1 \land z = 3, \\ \mathrm{stop}, & \text{其他情形}. \end{cases}$$
- **逐项复核**：
  1. `N'` 是合法的 `FiniteOperatorNetwork`：当 $v=1, y \in \{2,3\}$ 且 $f_1(y)=3$ 时，$3 \in \{2,3\} = \operatorname{dom}(f_1)$，满足 `choice_next_mem`；而对 $x \in U = \{1,2\}$，输出仅为 $1$ 或 $2$（不等于 $3$），故 `path_terminal` 在 `[0]`、`[1]` 处均以 `.stop` 一步终止。
  2. `NodeDomainRefinement N N'` 的全部字段成立：取 `source = Sum.inr`，两分块分别由 $x=1$ 与 $x=2$ 在第 $0$ 步见证 `NodePieceReached`；在 $\mathcal{N}'$ 中实际输入域为 $U'_0{}^{\mathrm{eff}}=\{1\}$、$U'_1{}^{\mathrm{eff}}=\{2\}$，对应实际输出像仅为 $\{1\}$ 与 $\{2\}$，其上 `choice'` 均取 `.stop`，与 `N.choice () z = .stop` 完全一致，故 `choice_projection` 成立。
  3. **违背正文定义**：按正文自环细分公式（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1070-L1073)），应有
     $$D'_{1\to 1} = D_{()\to ()} \cap f_1(U_1) \cap U_1 = \emptyset,$$
     然而在 $\mathcal{N}'$ 中 $3 = f_1(3) \in \text{`N'.node\_image 1`}$ 且 $\mathrm{choice}'(1, 3) = \mathrm{next}\ 1$，故 `3 ∈ N'.edge_domain 1 1`（`N'.to_transition_graph.Edge 1 1` 成立），无环网络被伪造出了自环边，且状态 $(1,3)$ 产生无限循环求值。

##### 反例 B：`NodeDomainRefinement` 允许删改与目标节点 $\beta$ 完全不关联的原有边域
- **原网络 $\mathcal{N}_B$**（顶点集 $V = \mathrm{Fin}\,3 = \{0,1,2\}$，输入域 $U = \{1,2\}$）：
  - 三个节点局域算子均取 $f_{\mathrm{all}}$（定义域 $\{1,2,3\}$）；`entry 1 = 0`，`entry 2 = 1`；
  - 路由：当 $v = 1$ 且 $z \in \{2, 3\}$ 时 `choice 1 z = .next 2`，其余均为 `.stop`；路径为 `path_of 1 = [0]`，`path_of 2 = [1, 2]`（三个节点均可达）。此时边 $1 \to 2$ 的转移域为 $D_{1\to 2} = \{2, 3\}$。
- **对节点 `target = 0` 作域加细构造 $\mathcal{N}'_B$**：
  - 将 $U_0 = \{1,2,3\}$ 分划为 $\{1\} \sqcup \{2,3\}$，其中 $\{1\}$ 被 $x=1$ 访问而保留为节点 $0$（算子改为 $f_{\mathrm{all}}|_{\{1\}}$），$\{2,3\}$ 未在节点 $0$ 处被访问而按规则删去；旧节点 $1, 2 \neq 0$ 保留且算子仍为 $f_{\mathrm{all}}$。
  - 在 $\mathcal{N}'_B$ 中将节点 $1$ 的路由改为：**仅当 $z = 2$ 时 `choice' 1 z = .next 2`**（在 $z = 3$ 处改为 `.stop`）。
- **逐项复核**：节点 $1$ 的实际输入域仅为 $U'_1{}^{\mathrm{eff}} = \{2\}$，故 `choice_projection` 在 $v = 1$ 时只检查 $z = 2$，`NodeDomainRefinement N_B N'_B` 成立；但节点 $1, 2$ 均不等于被加细节点 `target = 0`，其边域却从 $D_{1\to 2} = \{2,3\}$ 变成了 $D'_{1\to 2} = \{2\} \neq D_{1\to 2}$，直接违背正文“不与 $\beta$ 关联的边保持不变”。

#### 3. 修复方向

1. **用全输出像上的统一边域公理替换 `NodeDomainRefinement.choice_projection`**：
   将 [network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L108-L111) 的 `choice_projection` 替换为与正文证明统一交集式（[source.md](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/source.md#L1118-L1123)）一致的边域相容条件：
   ```lean
   edge_compat :
     ∀ (v w : V'),
       N'.edge_domain v w =
         N.edge_domain (node_domain_projection target source v)
             (node_domain_projection target source w) ∩
           N'.node_image v ∩ N'.node_dom w
   ```
   （等价路由表述为：`∀ (v w : V') (z : X), z ∈ N'.node_image v → (N'.choice v z = .next w ↔ N.choice (proj v) z = .next (proj w) ∧ z ∈ N'.node_dom w)`。）
   - **准确性**：对保留节点分四种情形代入 `N'.node_image v` 与 `N'.node_dom w`（结合原网络 $D_{\eta\to\xi} \subseteq f_\eta(U_\eta) \cap U_\xi$），上式自动退化为正文全部四条边域公式（不关联边 $D_{\gamma\to\delta}$、入边 $D_{\gamma\to\beta}\cap U_{\beta,a}$、出边 $D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$、自环 $D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}$）；同时，若非有效输出 $z \in f'_v(U'_v)$ 在原网络中指向不可达分块 $U_{\beta,c}$（在 `V'` 中无对应节点且与其他分块互斥），则对任意 $w \in V'$ 右侧均不成立，迫使 `N'.choice v z = .stop`，精确刻画引理 `#h-ced8c7236326e104` 剪枝后的终止域扩张。
   - **无循环恢复等价性证明**：对任意 $x \in N'.U$，沿原网络终止路径 `N.path_terminal x₀` 对步数 $k$ 归纳提升路径：当原路径第 $k+1$ 步进入 `target` 时，中间点落入唯一分块 `piece b` 本身就是 `NodePieceReached N target piece b` 的定义见证，由 `piece_node_present_iff_reached` 取得对应子节点 $w' \in V'$，再由 `edge_compat` 唯一推出 `N'.choice v' z = .next w'`，最后由 `terminal_path_unique` 直接得到 `path_projection` 与 `refinement_preserves_local_equivalence`。
2. **补齐关系层与构造层的双向桥接及结构引理**：
   - 在构造与关系模块之间证明健全性与唯一性桥接：`P.network` 满足修正后的 `NodeDomainRefinement`（原弱化版亦满足），且任一满足修正后 `NodeDomainRefinement` 的 `N'` 与 `P.network` 在节点双射 `FiniteOperatorNetwork.relabel` 下具有完全相同的 `PresentationData`。
   - 显式补齐 `P.presentation.Reached (.inl β)`、`P.presentation.Reached (.inr a) ↔ NodePieceReached`、以及 `entry_domain`、四类剪枝后 `edge_domain` 和 `terminal_domain` 的集合等式定理。
3. **补齐外延等价封装与 `NetworkObject` 层提升**：
   - 显式导出 `FiniteOperatorNetwork.ExtensionalEquivalent N' N`、全域等式 `N'.extensional_operator = N.extensional_operator` 及深度等式 `N'.evaluation_depth = N.evaluation_depth`。
   - 利用 `NonemptyOperatorNetwork` 商提升，在 `NetworkObject X bot` 上定义一步节点域加细关系（`empty` 无加细后继；两个 `nonempty` 对象满足该关系当且仅当其底层编号网络满足修正后的 `NodeDomainRefinement`），证明其对 `PresentationData` 良定义且保持 `NetworkObject.ExtensionalEquivalent`，从而无缝对接 `RefinementRule (NetworkObject X bot)` 与 `IrreducibleRepresentative`。

---

### 三、源码已证明结论与需补充内容区分清单

#### A. 源码已证明的结论
1. **构造侧（[domain_refinement_construction.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean)）**：
   - `NodePartitionData.local_op_eq_restrict`（[L31-L41](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L31-L41)）：子域定义域与局部等价条件唯一确定子节点算子为 $f_\beta|_{U_{\beta,a}}$。
   - `NodePartitionData.self_loop_choice_iff`（[L119-L152](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L119-L152)）：剪枝前子节点输出像上的自环路由等价于落入 $D_{\beta\to\beta} \cap U_{\beta,b}$。
   - `NodePartitionData.presentation` 与 `NodePartitionData.network`（[L208-L235](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L208-L235)）：从分划数据构造满足全部有限网络公理（含有限节点集、单值路由、统一深度界 `N.depth_bound` 与剪枝后无冗余节点）的加细网络 `P.network`。
   - `network_path_labels`、`network_path_projection`、`network_extensional_eq`（[L241-L270](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L241-L270)）：剪枝后网络保留重着色路径，投影回原网络恢复原终止路径，且全域外延算子相等 `P.network.extensional_operator = N.extensional_operator`。
2. **关系侧（[network_refinement.lean](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)）**：
   - `NodeDomainRefinement.node_eval_eq`、`terminal_projection`、`path_projection`、`eval_projected`（[L184-L232](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L184-L232)）：在关系假设下，每个源输入的终止路径经节点投影等于原路径，且链式求值结果一致。
   - `refinement_preserves_local_equivalence` 与 `refinement_preserves_representation`（[L377-L420](file:///private/tmp/math-gauge-carbon-medium-exact-input-20261114-v3/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L420)）：满足 `NetworkRefinement N N'`（含 `.node_domain` 分支）时，外延算子在 `N.U` 上局部等价（$\phi_{\mathcal{N}'}\equiv_U \phi_{\mathcal{N}}$），且对算子 $\varphi$ 的网络表示性质保持不变。

#### B. 需要修正或补充的内容
1. **关系定义的精确化修正**：将 `NodeDomainRefinement.choice_projection` 强化为全 `N'.node_image v` 上的边域相容公理 `edge_compat`，排除非有效输出上伪造边、伪造环或删改无关边的反例，并在修正后重证 `path_projection`。
2. **正文集合公式与剪枝节点范围的显式核验引理**：
   - 补充证明 `P.presentation.Reached (.inl β)`（旧非目标节点永不被删）及 `P.presentation.Reached (.inr a) ↔ NodePieceReached N target P.piece a`；
   - 补充证明 `entry_domain` 的两类公式（$U_\gamma^{\mathrm{in}}$ 与 $U_\beta^{\mathrm{in}} \cap U_{\beta,a}$）以及剪枝后 `edge_domain` 的四类交集公式和 `terminal_domain` 公式。
3. **构造与关系的双向桥接定理**：补充证明构造网络 `P.network` 满足修正后的 `NodeDomainRefinement N P.network`，且修正后的 `NodeDomainRefinement` 在节点重标号意义下唯一对应于 `P.network`。
4. **外延等价谓词与 `NetworkObject` 对象空间层封装**：补充导出 `FiniteOperatorNetwork.ExtensionalEquivalent`、关系侧全域外延算子相等、求值深度等式 `evaluation_depth`，并将节点域加细关系及其外延等价保持定理提升至 `NetworkObject X bot`，以闭合与 `RefinementRule (NetworkObject X bot)` / `IrreducibleRepresentative` 的类型接口。
