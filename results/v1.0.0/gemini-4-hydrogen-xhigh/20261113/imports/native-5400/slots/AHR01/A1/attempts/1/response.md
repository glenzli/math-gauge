{}
### 总体判断

对 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md) 中**“节点域加细”**（锚点 `h-eddd1f2d0a9d3528`）及该情形下**“网络加细保持外延等价”**（命题 `#h-012f4ba72aeb3f20`）的 Lean 实现（主要分布于 [domain_refinement_construction.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 与 [network_refinement.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)）审阅如下：

- **结论**：源码**准确覆盖了外延保持的核心方向（构造性实例与充分性证明）**，但**并未完整、准确地覆盖“节点域加细”的数学定义与理论闭环**。最主要的问题有三项：
  1. **关系式定义过弱（实质性偏差）**：[NodeDomainRefinement](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L73-L111) 的 `choice_projection` 仅在 `(N'.node_op v).func '' N'.node_actual_input_domain v`（实际输入域的像）上约束转移选择，而在局部输出像 `N'.node_image v` 的其余部分完全不约束，从而允许在未触及的局部输出上任意增删边或改动终止域，严格弱于正文定义的转移域交集与 `@h-ced8c7236326e104` 删除冗余节点准则。
  2. **两条实现路线彼此脱节**：[domain_refinement_construction.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 构造的 `P.network` 未证明满足 `NodeDomainRefinement N P.network`，二者也未建立唯一性/重标同构桥接。
  3. **显式刻画引理与外延等价封装不完整**：正文中各分情形的入口片、边域（入边/出边/自环/无关边）及终止域 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$（及删冗余后的 $T^{\mathcal T_R}$）公式未作为显式引理全部证出；同时 `network_refinement.lean` 仅证出 `LocalEquivalent` 而未封装 `ExtensionalEquivalent`、全空间算子相等、`NetworkObject` 层等价以及证明中的路径长度界 $r' \le \ell(\mathcal N)$。

> 注：本次审阅按要求未修改工作区文件或提交 Lean 代码；此外工作区未预先构建 `.olean` 产物，本审阅基于逐行源码与数学推演完成，未对整个 `formal_oet` 包执行增量编译。

---

### 一、“节点域加细”定义的逐项对照审查

正文节点域加细定义见 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L1046-L1083)，Lean 侧分“构造路线”（`NodePartitionData` + `P.network`）与“关系路线”（`NodeDomainRefinement`）两套表达：

#### 1. 构造路线：[domain_refinement_construction.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean)

| 正文要素 | Lean 实现对应 | 覆盖评估 |
|---|---|---|
| 目标节点 $\beta$ 与 $U_\beta=\mathrm{dom}(f_\beta)$ 的有限非空分划 $\bigsqcup_{a=1}^q U_{\beta,a}$ | [NodePartitionData](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L12-L18)：`target`, `count`, `count_pos : 0 < count`, `piece`, `nonempty`, `disjoint`, `cover` | **完全对应**（注：允许 $q=1$，与正文允许规则族 $R$ 另加限定相协调，见 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L1085-L1094)） |
| 子节点局域算子 $\mathrm{dom}(f_{\beta,a})=U_{\beta,a}$ 且 $f_{\beta,a}\equiv_{U_{\beta,a}} f_\beta$（即 $f_\beta\vert_{U_{\beta,a}}$） | [local_op / local_domain / local_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L19-L21) 与 [local_op_eq_restrict](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L31-L32) | **完全对应**，且额外显式证出了 `P.local_op a = restrict_operator (N.node_op target) (P.piece a)` |
| 节点替换 $\beta \mapsto \{\beta_a\}$ 与入口输入片分割 $U'^{\mathrm{in}}_{\beta_a}=U_\beta^{\mathrm{in}}\cap U_{\beta,a}$ | [Label / projection / lift_label](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L42-L64) 与 `presentation` | **语义构造正确**（通过 `lift_label (N.entry x) x` 选出唯一分划片），但未单独陈述 `entry_domain` 等式引理 |
| 转移域细分（入边/出边/自环/无关边）与终止域 | [P.choice](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L111-L112) 通过 `map_output_choice (fun w => P.lift_label w z)` 构造；[self_loop_choice_iff](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L119-L122) 验证了删冗余前自环情形 | **构造本身准确，但引理不完备**：仅显式证了删冗余前的 `self_loop_choice_iff`，其余三类边域及终止域 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$、删冗余后的 `P.network.edge_domain` / `P.network.terminal_domain` 均未单独陈述 |
| 按 `@h-ced8c7236326e104` 删去不被输入轨迹经过的冗余子节点（且空入口片/空边域省略） | [P.network := P.presentation.prune](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L235) 调用 [network_presentation.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L35-L71) 的 `Reached` 与 `prune_choice` | **完全对应**（Lean 中用全函数 `edge_domain / entry_domain` 取空集 `∅` 统一编码正文“空片/空边域省略”，且 `prune_choice` 精确地将指向未到达节点的转移转为 `.stop`） |

#### 2. 关系路线：[NodeDomainRefinement](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L73-L111)

- **精确对应的部分**：
  - 分划数据（`target`, `part_count`, `part_count_pos`, `piece`, `piece_nonempty`, `piece_disjoint`, `piece_cover`）与局域算子约束（`local_factor`, `local_domain`, `local_equiv`）与正文完全匹配。
  - 节点替换与按 `@h-ced8c7236326e104` 删除冗余子节点的集合对应（`source`, `source_injective`, `old_node_present`, `piece_node_present_iff_reached`）及节点算子相容性（`old_node_op_compat`, `piece_node_op_compat`）精确表达了 $V'$ 同构于“非目标旧节点 $\sqcup$ 至少被某条输入轨迹实际访问过的分划片 $\beta_a$”（借助 [NodePieceReached](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L51-L56)）。注：非目标节点 $\gamma\neq \beta$ 不会因分划而变成不可达，故 `old_node_present` 成立。
  - 入口条件 `same_input_domain : N'.U = N.U` 与 `entry_projection`（结合网络入口点必落在对应 `node_dom` 中以及 `piece_disjoint`）**在数学上隐含**了正文的入口片公式 $U'^{\mathrm{in}}_{\beta_a}=U_\beta^{\mathrm{in}}\cap U_{\beta,a}$ 与 $U'^{\mathrm{in}}_\gamma=U_\gamma^{\mathrm{in}}$（但未导出为显式引理）。
- **关键不足之处**：
  - [choice_projection](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L107-L111) 仅要求：
    $$z \in (N'.\mathrm{node\_op}\,v).\mathrm{func}''\,N'.\mathrm{node\_actual\_input\_domain}\,v \implies \mathrm{map\_output\_choice}\;\mathrm{projection}\;(N'.\mathrm{choice}\,v\,z) = N.\mathrm{choice}\;(\mathrm{projection}\,v)\;z.$$
    它在 $N'.\mathrm{node\_image}\,v \setminus (N'.\mathrm{node\_op}\,v).\mathrm{func}''\,N'.\mathrm{node\_actual\_input\_domain}\,v$ 上**没有任何约束**，与正文在完整局部输出像 $f'_\eta(U'_\eta)$ 上通过集合交定义转移域 $D'_{\gamma\to\beta_a},D'_{\beta_a\to\gamma},D'_{\beta_a\to\beta_b},D'_{\gamma\to\delta}$ 及终止域 $T'$ 不等价（详见第四节反例）。

---

### 二、“网络加细保持外延等价”（`#h-012f4ba72aeb3f20`）的逐项对照审查

正文命题与证明见 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L1095-L1178)，外延等价定义见 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L823-L837)。

| 正文证明与结论要素 | Lean 侧对应实现 | 覆盖评估 |
|---|---|---|
| 1. 轨迹对应：每步若在 $\beta$ 则按分划唯一落入 $\beta_{a_s}$，转移后继与中间状态一致 | 构造侧：[network_path_labels](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L241-L242)、[network_path_projection](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L249-L250)<br>关系侧：[node_eval_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L184)、[terminal_projection](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L195-L197)、[path_projection](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L214-L216)、[eval_projected](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L222-L225) | **实质完全证明** |
| 2. 终止域分解 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$（删冗余前） | 构造侧通过 `P.choice` 隐含；关系侧因 `choice_projection` 仅限实际输入像而**不可证** | **缺失显式定理（关系侧需先修定义）** |
| 3. 路径长度界 $r' \le \ell(\mathcal N)$（实际上 $r' = r$） | 从 `path_projection` / `network_path_projection`（`List.map ... = N.path_of ...`）直接可得长度相等，但**未显式陈述路径长度或 `evaluation_depth` 引理** | **差一步显式封装** |
| 4. 按 `@h-ced8c7236326e104` 删除冗余节点后外延算子保持不变 | 构造侧：`P.network := P.presentation.prune` 复用 [prune_extensional_operator_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean)，直接在 [network_extensional_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258) 证得 `P.network.extensional_operator = N.extensional_operator` | **构造侧完整覆盖**；关系侧直接把删冗余后性质编码进了 `NodeDomainRefinement` |
| 5. 结论 $\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}$（与 $U'=U$、外延等价 $\mathcal N'\sim_{\mathrm{op}}\mathcal N$、网络表示保持） | 构造侧：[network_extensional_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258)<br>关系侧：[same_input_domain](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L339)、[path_eval_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L354)、[refinement_preserves_local_equivalence](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L380)、[refinement_preserves_representation](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L404-L409) | **核心结论已证**，但关系侧缺少 `ExtensionalEquivalent N' N`（[effective_equivalence.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/effective_equivalence.lean#L1181-L1184)）、`N'.extensional_operator = N.extensional_operator` 及 `NetworkObject.ExtensionalEquivalent`（[network_extensional_space.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L220-L221)）封装 |

---

### 三、核心不足分析、可复核反例与修复方向

#### 不足 1（最关键）：`NodeDomainRefinement.choice_projection` 仅在 `node_actual_input_domain` 像上约束，偏离正文定义

- **成因诊断**：如 [network_refinement.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L107-L111) 注释 `-- Pruning may change choices at outputs never reached from the source.` 所解释，作者为了回避对“输出 $z\in f'_\eta(U'_\eta)$ 是否指向已被 `@h-ced8c7236326e104` 删除的 $\beta_b$”作分情况讨论，干脆把 `choice_projection` 缩小到实际输入域的像 `(N'.node_op v).func '' N'.node_actual_input_domain v`（在此范围外推不到被删节点）。
- **数学影响**：
  1. 虽然现有的轨迹/外延等价保持定理（[refinement_preserves_local_equivalence](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L380)）依然有效，但 `NodeDomainRefinement` **作为对 `#h-eddd1f2d0a9d3528` 的形式化定义是过宽（不忠实）的**——它暗中把“仅更改未实际到达的局部输出转移域”（属于**有效等价**层的冗余边扰动，而非节点域加细操作）也归入了节点域加细。
  2. 无法从 `NodeDomainRefinement` 反推正文节点域加细的基本结构等式（包括边域交集公式 $D'_{\gamma\to\beta_a} = D_{\gamma\to\beta}\cap U_{\beta,a}$、$D'_{\beta_a\to\gamma}=D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$、自环公式、以及删冗余前后终止域公式），也不能保证给定 $\mathcal N$、目标节点 $\beta$ 和分划 $\{U_{\beta,a}\}$ 时加细结果 $\mathcal N'$ 在节点重标号意义下唯一。
  3. 对下游使用加细规则族 $R$ 比较受限数据 $L/K/N$（正文 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L1085-L1094) 明确提及“节点域加细在 L/K/N 受限数据上需要满足的比较条件”）或研究非外延性质（例如转移图边集/有效结构比较）时，会纳入非规范构造的伪加细网络。

- **可复核反例（无自环、无删节、非平凡二分划 $q=2$、严格 DAG）**：
  - 令状态集 $X = \{\bot, 1, 2, 3\}$（$\bot$ 为吸收元），节点集 $V = \{0, 1\}$，输入域 $U = \{1, 3\}$。
  - 原网络 $\mathcal N$：
    - 节点 $0, 1$ 的局域算子均取 $\mathrm{dom}(f_0)=\mathrm{dom}(f_1)=\{1, 2, 3\}$，并在 $\{1,2,3\}$ 上恒等（域外取 $\bot$），故 $f_0(U_0)=f_1(U_1)=\{1,2,3\}$。
    - 入口分配：$U_0^{\mathrm{in}}=\{1,3\}$，$U_1^{\mathrm{in}}=\emptyset$（即 `N.entry` 将 $1,3$ 均送入 $0$）。
    - 转移选择：`N.choice 0 1 = .next 1`，`N.choice 0 3 = .next 1`，`N.choice 0 2 = .stop`；`N.choice 1 z = .stop`（对所有 $z$）。于是 $D_{0\to 1}=\{1,3\}$，$T_0=\{2\}$，$T_1=\{1,2,3\}$。
    - 检验 $\mathcal N$：无圈 DAG（唯一边 $0\to 1$）；对输入 $1, 3 \in U$ 轨迹均为 $[0,1]$，故 $0,1$ 均被到达，且节点 $0$ 的实际输入域为 $\{1,3\}$（其像不含 $2$）。
  - 对目标节点 `target = 1` 取非平凡二分划（$q=2$）：$U_{1,0}=\{1,2\}$，$U_{1,1}=\{3\}$，子节点算子取限制 $f_{1,a}=f_1\vert_{U_{1,a}}$。输入 $1,3$ 分别在节点 $1$ 处以 $1\in U_{1,0}$ 与 $3\in U_{1,1}$ 被到达，故**无节点被 `@h-ced8c7236326e104` 删除**。
    - 按正文 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L1061-L1065)，唯一的规范加细 $\mathcal N'$ 必须满足：$D'_{0\to (1,0)} = D_{0\to 1}\cap U_{1,0} = \{1\}$，$D'_{0\to (1,1)} = D_{0\to 1}\cap U_{1,1} = \{3\}$，$T'_0 = \{2\}$。
    - 现构造扰动网络 $\mathcal N''$：节点、算子、入口完全同 $\mathcal N'$，仅在节点 $0$ 的输出 $2\in f_0(U_0)\cap U_{1,0}$ 上将 `N''.choice 0 2` 由 `.stop` 改为 `.next (1, 0)`。
  - 核对结果：
    - $\mathcal N''$ 仍满足有限算子网络全部公理（严格 DAG，无环，转移域 $\{1,2\}\subseteq f_0(U_0)\cap U_{1,0}$ 合法，全部节点均从 $U$ 可达）。
    - 由于 $N''.\mathrm{node\_actual\_input\_domain}\;0 = \{1,3\}$，其像 $\{1,3\}$ 不含 $2$，因此 `NodeDomainRefinement N N''` 的**所有字段**（包括 `choice_projection`）**全部成立**。
    - 然而 $\mathcal N''$ 的边域与终止域为 $D''_{0\to (1,0)}=\{1,2\}\neq \{1\}=D_{0\to 1}\cap U_{1,0}$ 且 $T''_0=\emptyset\neq \{2\}$，**不是正文定义的节点域加细**。

- **修复方向**：
  将 `NodeDomainRefinement.choice_projection` 的全称量词从 `(N'.node_op v).func '' N'.node_actual_input_domain v` 扩大到**完整局部输出像 `z ∈ N'.node_image v`**（即 `(N'.node_op v).func '' N'.node_dom v`），并显式反映 `@h-ced8c7236326e104` 删去未到达子节点后的确定规则（与 [prune_choice](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean#L35-L40) 一致）：
  - 若 `N.choice (projection v) z = .stop`，则 `N'.choice v z = .stop`；
  - 若 `N.choice (projection v) z = .next w` 且 `w ≠ target`，则 `N'.choice v z = .next w'`（其中 `source w' = .inl ⟨w, hw⟩`）；
  - 若 `N.choice (projection v) z = .next target`（此时因 $z\in N.\mathrm{node\_image}\;(\mathrm{projection}\;v)$ 且在 $D_{\cdot\to\beta}\subseteq U_\beta$ 内，由 `piece_cover` 与 `piece_disjoint` 存在唯一 `b` 使 `z ∈ piece b`）：
    - 若 `∃ w' : V', source w' = .inr b`（即 `NodePieceReached N target piece b`），则 `N'.choice v z = .next w'`；
    - 若 `¬ ∃ w' : V', source w' = .inr b`（该子节点因不被任何输入轨迹经过而被删除），则 `N'.choice v z = .stop`。

  这样修复后，既**严格允许** `@h-ced8c7236326e104` 删除未到达节点对未触及输出造成 `.next ↦ .stop` 吸收（使 `P.network` 能够自然满足 `NodeDomainRefinement`），又**完全禁止**上面反例中的任意加边/删边扰动。

---

#### 不足 2：构造实现（`P.network`）与关系定义（`NodeDomainRefinement`）尚未打通

- **现状**：[domain_refinement_construction.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 构造了 `P.network` 并单独证明 `network_extensional_eq`；[network_refinement.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean) 则未导入前者，两者之间没有任何等价性/实现关系定理。
- **修复方向**：
  1. 在加强 `choice_projection` 后，补充构造性证明：`def NodePartitionData.to_refinement : NodeDomainRefinement N P.network`（以及 `NetworkRefinement.node_domain`）。
  2. 反向补充唯一性引理：任何满足 `h : NodeDomainRefinement N N'` 的 `N'`，都可通过诱导的 `NodePartitionData` 在节点重标号（`FiniteOperatorNetwork.relabel`）意义下同构于 `P.network`（从而在 `PresentationData` 意义下完全一致）。

---

#### 不足 3：正文中结构公式引理与结论封装尚有缺口

1. **入口片、边域（全部四类）与终止域交集公式未全面引理化**：
   - 在 [domain_refinement_construction.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 中，仅见删冗余前针对 `P.choice` 的自环引理 [self_loop_choice_iff](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L119-L122)。建议补全删冗余前 `P.presentation` 及删冗余后 `P.network`（与强化后的 `NodeDomainRefinement`）上的：
     - `entry_domain` 公式：$U'^{\mathrm{in}}_{\beta_a}=U_\beta^{\mathrm{in}}\cap U_{\beta,a}$，$U'^{\mathrm{in}}_\gamma=U_\gamma^{\mathrm{in}}$；
     - 四类 `edge_domain` 公式（入边、出边、自环、无关边，删冗余后说明指向已删 `¬ NodePieceReached` 片的边域变为 `∅`）；
     - `terminal_domain` 公式（删冗余前 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$、$T'_\gamma=T_\gamma$；删冗余后并入原本指向已删 $\beta_b$ 的部分，对应 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L188-L193) 的 $T_\eta^{\mathcal T_R}$）。
2. **`#h-012f4ba72aeb3f20` 在关系侧及 `NetworkObject` 层面的封装缺口**：
   - 关系侧已证 [refinement_preserves_local_equivalence](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L380)（即 $\phi_{\mathcal N'}\equiv_U \phi_{\mathcal N}$），但虽然该文件导入了 [effective_equivalence.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/effective_equivalence.lean)，却未打包给出 `ExtensionalEquivalent N' N`（见 [ExtensionalEquivalent](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/effective_equivalence.lean#L1181-L1184)）或全空间算子等式 `N'.extensional_operator = N.extensional_operator`（与正文 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L834-L837)“局部等价等价于外延算子相等”对应）。
   - 正文证明中显式给出了节点域加细的路径长度界 $r'\le \ell(\mathcal N)$（[source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/source.md#L1161-L1168)），Lean 已证 `(path_of x).map projection = N.path_of ...`，补充一行 `(path_of x).length = (N.path_of ...).length` 及节点域加细下 `N'.evaluation_depth ≤ N.evaluation_depth` 即可完整覆盖证明步骤。
   - [network_refinement.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L423-L437) 末尾将不可约代表 `IrreducibleRepresentative` 定义在 `RefinementRule (NetworkObject X bot)` 上，但前面只定义了 `FiniteOperatorNetwork` 上的 `NodeDomainRefinement`/`NetworkRefinement`，尚未提供向 `NetworkObject` 的提升以及 [NetworkObject.ExtensionalEquivalent](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_extensional_space.lean#L220-L221) 的保持定理。

---

### 四、源码已证明结论 vs 待补充/修复内容对照表

| 分类 | 具体条目 | 所在位置 / 状态 |
|---|---|---|
| **源码已准确构造并证明** | 有限非空分划数据结构与局限域算子即限制算子 $f_{\beta,a}=f_\beta\vert_{U_{\beta,a}}$ | `NodePartitionData`、[local_op_eq_restrict](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L12-L32) |
| **源码已准确构造并证明** | 删去未到达子节点前的自环转移刻画 | [self_loop_choice_iff](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L119-L122) |
| **源码已准确构造并证明** | 构造加细网络 `P.network`（含 `@h-ced8c7236326e104` 删除冗余节点）的轨迹投影与外延算子精确相等 $\phi_{\mathcal N'}=\phi_{\mathcal N}$ | [network_path_labels](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L241-L242)、[network_path_projection](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L249-L250)、[network_extensional_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258) |
| **源码已证明（但前提 `NodeDomainRefinement` 过弱）** | 关系公理下节点局部求值相等、终止路径投影、完整输入轨迹投影、链求值一致、`LocalEquivalent N'.extensional_operator N.extensional_operator N.U`、网络表示保持 | [node_eval_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L184)、[terminal_projection](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L195-L197)、[path_projection](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L214-L216)、[eval_projected](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L222-L225)、[path_eval_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L354)、[refinement_preserves_local_equivalence](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L380)、[refinement_preserves_representation](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L404-L409) |
| **需要修复** | 将 `NodeDomainRefinement.choice_projection` 从 `node_actual_input_domain` 像强化为覆盖全 `N'.node_image v` 的逐情形后删冗余转移律 | [network_refinement.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L107-L111) |
| **需要补充** | 构造 `P.network` 满足 `NodeDomainRefinement N P.network` 及其反向重标号唯一性定理 | 需桥接 [domain_refinement_construction.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean) 与 [network_refinement.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean) |
| **需要补充** | 入口片、其余三类边域（及删冗余后全部四类边域）与终止域 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$（及删冗余后并入关系）的显式引理 | 构造侧与（修复后的）关系侧均未显式证出 |
| **需要补充** | 路径长度/深度界 `N'.evaluation_depth ≤ N.evaluation_depth`（$r' \le \ell(\mathcal N)$），以及关系侧 `ExtensionalEquivalent N' N`、全空间算子相等与 `NetworkObject` 层等价封装 | [network_refinement.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR01/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L377-L437) |
