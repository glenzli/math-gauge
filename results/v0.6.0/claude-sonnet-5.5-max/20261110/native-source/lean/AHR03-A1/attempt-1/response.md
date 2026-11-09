## 审阅结论

**就“节点域加细”及“加细保持外延等价”而言，附件的 Lean 实现准确且完整。**

- 正文定义的每条规则在源码里都有对应声明，且都已证明。这些规则是：分划与局域算子、子节点替换、入口片、入边/出边/自环/无关边、终止域、删除未被经过的子节点。
- 命题 φ_{N'} ≡_U φ_N 的前提与结论也都有对应声明并已证明。
- 我没有找到数学缺口或反例。
- 只有几处“接口/打包/桥接”层面的未陈述项，见 §4，不改变命题真值。
- 其中最值得注意的一处：关系 `NodeDomainRefinement` 带了一个正文没有的字段 `choice_projection`。它是其余教材数据的可推导后果，所以无害，但属于可加固的接口瑕疵。我在附件之外的临时文件里机器验证了这一推导。

**缩写**（均在 `formal_oet/vol_01/ch_05_operator_networks/`）：
- NR = `network_refinement.lean`
- DRC = `domain_refinement_construction.lean`
- ON = `operator_network.lean`
- NP = `network_presentation.lean`
- EE = `effective_equivalence.lean`
- π = `node_domain_projection`

## 0. 审阅与验证方式

- 对照 `source.md` 的“网络加细 (i)”、引理 #h-ced8c7236326e104（删除冗余节点）、命题 #h-012f4ba72aeb3f20 及其证明，通读了上述五个文件中的相关声明。
- `lake build` 通过。`network_presentation`、`network_refinement`、`domain_refinement_construction` 单独重编译无 warning。
- 全库 grep 无 `sorry/admit/axiom/native_decide`。
- 对 §3 所列主要定理做 `#print axioms`，只依赖 `propext / Classical.choice / Quot.sound`。
- 附件之外的临时 Lean 文件，全部编译通过，附件未改动：
  - (a) 由 `edge_domain_eq` 推出正文的四类边域公式。
  - (b) 由 `NetworkRefinement` 推出 `ExtensionalEquivalent N' N`、`N'.extensional_operator = N.extensional_operator`，以及编号编码后的 `NetworkObject.ExtensionalEquivalent`。
  - (c) 去掉 `choice_projection` 字段，仅用其余字段推出它（§4-1）。
  - (d) 非空性：任意网络任意节点都有平凡分划；`Fin 3` 上恒等单节点网络分成 {1}、{2} 的真实分裂例，两块都被到达，`network_extensional_eq` 可用。
- Python 仿真：按正文原文公式，对 15000 个随机小网络做节点域加细，包含自环、多块、未被到达块被删除。条件 (i)–(iv)、出边互斥、转移域包含关系、轨迹长度与输出全部保持。

## 1. 正文定义 ↔ Lean 对象

| 正文 | Lean | 核对 |
|---|---|---|
| 有限算子网络 (i)–(iv) | `FiniteOperatorNetwork` (ON:174)：`entry/entry_mem`；`choice`；`TerminalPathFrom` (ON:148) + `path_of/depth_bound`；`node_reachable` | (i) 函数式 `entry` 自动给出不交覆盖，空入口片即非入口节点。(ii) 出边互斥由 `choice` 是函数得到（ON:426）。(iii) 统一有限终止。(iv) 无冗余。 |
| 转移域、终止域 | `edge_domain` (ON:391)、`terminal_domain` (ON:399) | 边域 = 像 ∩ {choice = next γ}，含于像与 U_γ (ON:407, 416)。终止域 = 像 ∖ ⋃边域，等价于 `choice = stop` (EE:851)。 |
| 外延算子 | `extensional_operator` (ON:329)、`dom_extensional_operator_eq` (ON:341) | 一致。 |
| 有限非空分划 U_β = ⊔U_{β,a} | `NodePartitionData` (DRC:12)：`count_pos/nonempty/disjoint/cover`；关系侧 `OperationalNodeDomainRefinement` (NR:68) 的同名字段 | `cover` 取 `N.node_dom target = dom f_β`，是全域而非有效域，与正文一致。 |
| f_{β,a}：dom = U_{β,a}，≡ f_β | `local_op/local_domain/local_eq`；`local_op_eq_restrict` (DRC:31) | 证明了正文括注 f_{β,a} = f_β\|U_{β,a}。 |
| 用 β_a 替换 β | `Label := {v // v≠target} ⊕ Fin count` (DRC:42)、`node_op` (DRC:72)；关系侧 `source`、`source_injective`、`old_node_present` | 命名与实现无关，由 `source` 单射保证。 |
| 入口片 U^in_β ∩ U_{β,a}，其余入口片不变 | `presentation.entry := lift_label (N.entry x) x` (DRC:221)；关系侧 `entry_projection`，导出 `entry_domain_eq` (NR:283)：`N'.entry_domain v = N.entry_domain (π v) ∩ N'.node_dom v` | 两种情形都覆盖。 |
| 入边、出边、自环、无关边 | 构造 `choice` (DRC:111)：按当前输出点所在分块选后继。关系侧 `edge_domain_eq` (NR:122)。构造的 `network_edge_domain_eq` (DRC:346)、`self_loop_choice_iff` (DRC:119) | 单一公式 `(N.edge_domain (π v) (π w) ∩ N'.node_image v) ∩ N'.node_dom w` 推出四类正文公式（(a) 已验证）。 |
| 子节点终止域 = 出边域补集 | 由 `terminal_domain` 的定义直接成立 | ✓ |
| 删除不被经过的子节点 | `prune` (NP:111)、`Reached` (NP:106)；关系侧 `piece_node_present_iff_reached` + `NodePieceReached` (NR:51)；构造的 `piece_label_reached_iff` (DRC:310)、`old_label_reached` (DRC:296) | 旧节点全部保留，分块当且仅当有一次实际发生的输入落入其中。`prune_choice_next_iff` (NP:44) 保证保留边在整个定义域上不变。 |
| 命题 φ_{N'} ≡_U φ_N | 构造层 `network_extensional_eq` (DRC:258)；关系层 `refinement_preserves_local_equivalence` (NR:453)、`refinement_preserves_representation` (NR:480)；连接 `network_refinement` (DRC:449)、`allowed_network_refinement` (DRC:496) | 见 §2。 |

## 2. 前提、结论与证明路线

**前提**
- “N 为算子网络、β 为其节点”对应 `N : FiniteOperatorNetwork X bot V` 与 `target : V`。
- 分划、局域算子、定义域等式、局部等价对应 `NodePartitionData` 的字段。它们的用法：
  - `cover` 与 `disjoint` 用于唯一选块（`mem_piece_at` DRC:50、`piece_at_unique` DRC:55）。
  - `nonempty` 用于子节点定义域非空。
  - `local_eq` 用于逐步输出不变（`lift_apply` DRC:85）。
- 正文约定 U ≠ ∅，Lean 不需要。U = ∅ 时网络无节点，无 `target` 可选，命题空成立。

**结论**
- 正文 ≡_U 对应 `LocalEquivalent N'.ext N.ext N.U`。
- 因为 `N'.U = N.U`（构造中为 `rfl`），且两个算子在域外都是 ⊥，实际得到算子相等。构造层直接证明了这一点（DRC:258）。

**构造层证明路线**（与正文平行）：
- `colour_path` (DRC:168) 沿原轨迹，用每次发生的实际当前输入选分块（`colour_path_get` DRC:272）。因此同一节点的不同次发生可落入不同子节点，这正是正文自环段落强调的点。
- `coloured_terminal` (DRC:184)：新轨迹合法且为终止轨迹。
- `coloured_eval` (DRC:197)：输出不变。
- `network_path_projection` (DRC:249)：路径长度不变，所以统一长度界不变。
- `prune_eval` (NP:162)：删除冗余节点后求值保持。

**关系层证明路线**（把 N' 投影回 N）：
- `node_eval_eq` (NR:198)：x ∈ N'.node_dom v 时，f'_v x = f_{π v} x。
- `terminal_projection` (NR:209) 与 `path_projection` (NR:228)：N' 的入口终止路径经 π 投影后是 N 的终止路径。再由 `terminal_path_unique`（`network_routing.lean:14`）与 N 的 `path_of` 等同。
- `eval_projected` (NR:236) 与 `path_eval_eq` (NR:428)：输出相等。
- 汇总得 `refinement_preserves_local_equivalence`。

## 3. 源码已证明的结论

- 构造 `NodePartitionData.network` 是一个同输入域的 `FiniteOperatorNetwork`，即 (i)–(iv) 全部成立。
- 构造的外延算子等于 N 的外延算子，轨迹长度不变。
- 构造满足关系 `NodeDomainRefinement`，包括：
  - 全域边域公式（含自环、含未被使用的边）。
  - 入口公式。
  - 未被到达分块被删除、已被到达分块被保留。
  - 旧节点全部保留。
- 对任意满足该关系的 N'，外延局部等价，并保持“表示 φ”。
- 因 `network_extensional_eq` 给出算子相等，且 `represents` 保持，正文的外延等价在构造层完全覆盖。

## 4. 需要补充或可加固的内容（均不影响命题真值）

**4-1. `choice_projection` 是教材数据的可推导后果（接口瑕疵，无数学影响）**

- 该字段在 NR:103–106，只要求在 N' 的实际像上成立。
- 必须限于实际像，而不能加强到整个像。反例（手算）：
  - 设 α：dom{1,2}，1↦10，2↦11。β：dom{10,11}，恒等。U = {1}，α→β 的转移域为 {10,11}。
  - 把 β 分成 {10}、{11}。块 {11} 未被到达，被删除。
  - 于是 N' 中点 11 是 α 的终止点，而 N 中 11 仍转入 β。11 属于 α 的像，却不属于实际像。
  - 这与引理 #h-ced8c7236326e104 一致：删除后终止域变大。
- 可推导性：去掉该字段、保留 `edge_domain_eq`、`old_node_present`、`piece_node_present_iff_reached`（反向）、`*_op_compat`、`piece_cover`、`entry_projection`，仍可证出它（临时 Lean，已通过）。推导三步：
  - (a) 若 N'.choice v z = next w，则 z ∈ N'.edge_domain v w，由 `edge_domain_eq` 得 N.choice (π v) z = next (π w)。
  - (b) 若 N'.choice v z = stop 而 N.choice (π v) z = next u：
    - u ≠ β 时，由 `old_node_present` 取旧标签，得 N'.choice v z ≠ stop，矛盾。
    - u = β 时，z 属于唯一分块 b。z 是 N 的一次实际发生输入，故 `NodePieceReached b`，于是标签存在，同样矛盾。
  - (c) 前向不变量：沿 N' 的终止路径，每次发生的当前输入都属于 N 中 π v 的实际输入域。起点由 `entry_projection`，步进由 (a) 加 `next_output_mem_node_actual_input_domain` (EE:432)。
- 同样，去掉该字段后的数据组仍能得到 `refinement_preserves_local_equivalence`，因为它们可组装回完整的 `NodeDomainRefinement`。
- 修复建议：删去该字段，改为定理，或在文档中标明它是推导后果。
- 相关说明：偏离教材的只有这一个字段。`OperationalNodeDomainRefinement` 的注释说它“弱于教材”，这在逻辑强度上成立：教材 ⇒ 它，反之不然。

**4-2. 关系层的 `edge_domain_eq` 等字段未被保持外延的证明使用**

- 保持外延的证明只用到：`node_eval_eq`、`entry_projection`、`choice_projection`、`same_input_domain`。
- `edge_domain_eq`、`piece_cover` 等字段的作用是唯一确定“加细结果”这个对象。`NetworkObject` 的 `presentation_data` 包含全域边域，所以未被使用的边也会改变对象。
- 因此这些字段是必要的，只是与外延保持无关。

**4-3. 结论打包与对象空间层面的衔接**

- 没有现成的 `NetworkRefinement → FiniteOperatorNetwork.ExtensionalEquivalent N' N`。
- 没有现成的算子相等版本，也没有现成的 `NetworkObject.ExtensionalEquivalent (nonempty (encode N' _)) (nonempty (encode N _))`。
- 三者均已在临时文件一行或短证推出：用 `same_input_domain`、`dom_extensional_operator_eq` 与 `encode_extensional_operator`。建议加为三条小引理。

**4-4. 教材四类边域公式只以统一形式陈述**

- 逐类显式引理（入边、出边、自环、无关边）可由 `edge_domain_eq` 与 `edge_domain_subset_node_image/dom` 直接得到，我已验证。可作为可选的显式引理。

**4-5. 未形式化项，本命题不需要**

- “关系 ⇒ 与构造同构”。数学上应成立：`source` 与存在性字段决定标签集，其余字段决定各节点算子、入口与边域，像之外的 `choice` 值无关紧要。我没有证明它。
- 正文证明中提到的 T'_{β_a} = f_{β,a}(U_{β,a}) ∩ T_β（删除前）。
- ℓ(N') = ℓ(N)。由 `network_path_projection` 一步可得，但未陈述。

**4-6. 范围外**

- 规则族 R、不可约代表（`RefinementRule` 是抽象别名）、多步加细、L/K/N 比较条件，都没有与 `NetworkRefinement` 衔接。
- q = 1 的平凡分划在 Lean 与正文中都允许。

## 5. 边界提醒

- 节点域加细一般不保持有效等价。正文注 #h-e7bf88d54855ca9f 里单节点网络与“两个入口节点”网络，正是 U = {a,b} 的一次 {a}、{b} 分划。所以命题只能说外延，不能说路径或标记表达。
- 未被到达的块被删除后，目标节点的并域可能小于 U_β，外延不变。

---
**核对状态说明**
- 4-1 的反例是手算，未机器验证。
- 4-5 的同构、算法加细、其他章节我没有审阅（题面范围外）。
- 过程中唯一被拒的命令是在 `$TMPDIR` 下建临时目录；我改用工程内的 `audit_scratch/` 目录，不影响结论。