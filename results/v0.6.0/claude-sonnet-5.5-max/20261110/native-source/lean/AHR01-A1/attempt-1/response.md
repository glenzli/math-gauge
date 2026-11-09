## 审阅结论

**命题层面（#h-012f4ba72aeb3f20，节点域加细情形）：源码已准确、完整地证明，且比正文更强。**
- 构造型：`NodePartitionData.network_extensional_eq`（`domain_refinement_construction.lean:258`）证明 `P.network.extensional_operator = N.extensional_operator`。这是全空间的算子相等，强于正文的 `≡_U`。
- 关系型：`refinement_preserves_local_equivalence`（`network_refinement.lean:377`）和 `refinement_preserves_representation`（:404）。
- `lake build formal_oet` 通过。关键定理的 `#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorry`。

**定义层面（#h-eddd1f2d0a9d3528 (i)）：不完全准确、不完整。** 这不影响命题的真假，但影响 API 能否被宣称与正文定义一一对应。
1. 构造型实现与正文一致，但正文的入口片、边域公式没有写成定理，只有自环的 `self_loop_choice_iff` 例外。
2. 关系型 `NodeDomainRefinement` 严格弱于正文定义。`NetworkRefinement.node_domain` 用的正是这个版本，下文有可复核反例。
3. 源码从未证明构造满足关系型。两个模块互不 `import`，全库也没有任何文件同时引用 `NodePartitionData` 与 `NodeDomainRefinement`。

## 一、正文要素与 Lean 的逐项对应

| 正文要素 | 构造型 `NodePartitionData` | 关系型 `NodeDomainRefinement` | 状态 |
|---|---|---|---|
| 被加细节点 β | `target`（:12） | `target` | 对应 |
| 有限非空分划，块非空 | `count_pos, piece, nonempty, disjoint, cover = N.node_dom target` | 同名字段 | 对应 |
| `f_{β,a}`：dom = `U_{β,a}`，与 `f_β` 局部等价 | `local_op, local_domain, local_eq`；`local_op_eq_restrict`（:31）证明 `f_{β,a} = f_β|U_{β,a}` | `local_factor, local_domain, local_equiv` | 已证 |
| 新节点集 (V∖β)⊔{β_a} | `Label`、`lift_label`（:64） | `source, source_injective` | 对应 |
| 删去未被经过的子节点 | `presentation.prune`（`Reached`） | `old_node_present`、`piece_node_present_iff_reached`（`NodePieceReached`，:51） | 构造型隐含；关系型为字段；二者之间无证明 |
| 入口片 `U^in∩U_{β,a}` | `entry := lift_label (N.entry x) x` | `entry_projection` | 公式未陈述 |
| 入边/出边域 | `choice`（:111） | `choice_projection`（仅实际输出，:108） | 公式未陈述 |
| 自环 `D∩f(U_a)∩U_b` | `self_loop_choice_iff`（:119） | — | 已证（仅此一条） |
| 终止域 = 出边域补集 | `choice = stop` | — | 隐含 |
| N′ 是有限算子网络、统一长度界、同一输入域 | `presentation`（:208）各字段、`depth_bound := N.depth_bound`、`prune` | 假设 N′ 已是网络，`same_input_domain` | 构造型已证 |
| 命题 `φ_{N′} ≡_U φ_N` | `network_extensional_eq` | `refinement_preserves_local_equivalence` | 已证 |

## 二、源码已证明的结论

- **轨迹重着色（构造型）。**
  - `colour_path` 按每次出现时的当前输入，把 β 换成 `β_{piece_at(输入)}`；同一路径上不同次出现可选不同子节点。
  - `coloured_terminal` 证明重着色后仍是终止轨迹，`coloured_eval` 证明输出不变。
  - `network_path_projection`（:249）证明路径长度不变。
  - `choice_next_mem` 证明路由合法。
- **关系型的证明链。** 它只用到算子逐点一致（`node_eval_eq`）和实际输出上的路由相容（`choice_projection`）。依次得到 `terminal_projection`、`terminal_path_unique`、`path_projection` 和 `eval_projected`，最后给出 `NetworkRefinement.path_eval_eq` 与 `refinement_preserves_local_equivalence`。
- **未被使用的字段。** `piece_nonempty/disjoint/cover`、`source_injective`、`old_node_present`、`piece_node_present_iff_reached`、`part_count_pos` 在全库任何证明里都没有被使用。关系型定理其实是对任何"投影模拟"的 N′ 成立的更一般结果。

## 三、需要补充的内容

以下 S1、S2、S3 是宣称"与正文定义一一对应"所必需的，S4 是建议。除 S3 的反例用 Lean 核验外，其余补充我在附件之外的草稿中用 Lean 证明并编译通过，未改动附件。

**S1 桥接引理缺失。**
- 需要补：`NodePartitionData.toRefinement : NodeDomainRefinement N P.network`。
- 影响：没有它，`NetworkRefinement` 层的结论（如 `refinement_preserves_representation`）无法用于正文的那个加细操作，关系型对真实加细是否空洞也无从判断。
- 我已证明它成立，因此不空洞。证明要点如下：
  - `old_node_present`：非 target 标签在着色下不变，而 `N.node_reachable` 给出它出现在某条路径上。
  - `piece_node_present_iff_reached`：`inr a ∈ colour_path p y ↔ ∃ n, p[n]=target ∧ piece_at(前缀求值)=a`。前缀输入属于 `node_dom target`，由 `terminal_path_prefix_input_mem` 给出，所以 `piece_at = a ↔ ∈ piece a`。
  - `choice_projection`（关键）：
    - 设 z 是节点 v 的实际输出，y 是对应的实际输入。由 `network_path_projection`，有 `N.path_of x = pref.map π ++ π v :: suffix.map π`。再用"前缀求值相等"得 y = N 沿投影前缀的求值。
    - 若 `N.choice (π v) z = stop`，则两侧路由都是 stop。
    - 若为 `next u`，`terminal_path_suffix_of_next_at_prefix` 说明 u 紧随 `π v`，所以着色路径中出现 `lift u z`，它是 `Reached` 的，`prune_choice` 不会把该边改成 stop，投影后为 `next u`。

**S2 显式公式未成定理。** 对保留节点，我证明了：
```lean
entry_domain ⟨inl β⟩   = N.entry_domain β
entry_domain ⟨inr a⟩   = N.entry_domain target ∩ P.piece a
edge_domain ⟨inl γ⟩ ⟨inl δ⟩ = N.edge_domain γ δ
edge_domain ⟨inl γ⟩ ⟨inr a⟩ = N.edge_domain γ target ∩ P.piece a
edge_domain ⟨inr a⟩ ⟨inl δ⟩ = N.edge_domain target δ ∩ (P.local_op a).func '' P.piece a
edge_domain ⟨inr a⟩ ⟨inr b⟩ = N.edge_domain target target ∩ (P.local_op a).func '' P.piece a ∩ P.piece b
```
- 这几条与正文公式逐字一致；入边那条用到 `D_{γ→β} ⊆ U_β`，所以 `piece_at z = a ↔ z ∈ U_{β,a}`。
- 另有：旧节点全部保留（`Reached (inl β)`），子节点保留当且仅当 `NodePieceReached`。
- 终止域在删除后只有 `T′ ⊇ f_{β,a}(U_{β,a}) ∩ T_β`，等号仅在删除前成立。正文的证明也是"先考察尚未删除冗余节点的数据"。
- 反映这一点的例子（手算，未用 Lean 核验）：X={0,1,2,3}，f:1↦1, 2↦3, 3↦3，U={1}，自环 D={3}，分划 {1,2}、{3}。删除前 T′_a={1}，删除后 T′_a={1,3}。
- 影响：没有这些定理，就无法在 Lean 里对照检查 `P.network` 是否正是正文的 N′。后续章节（有效边域、矩阵证书沿加细边传递等）依赖这些公式。

**S3 关系型严格弱于正文定义（反例）。** `choice_projection` 只约束"实际输出"（删除冗余后必须如此），因此在从未产生的输出点上，N′ 的边域和终止域可以任意。
- 反例数据：X=Fin 4，⊥=0，单节点 β，f=id（dom={1,2,3}），U={1}。
  - N：choice 恒为 stop，无边。
  - N′：只把输出 2、3 处的路由改为 `next β`，即自环，转移域 {2,3}。
  - N′ 在正文意义下合法：{2,3} ⊆ f(U_β)∩U_β；输入 1 的轨迹仍是 (β,1) 且 1 在终止域 {1} 内；该自环从不被走。
- 在 Lean 中我构造了 `NodeDomainRefinement N N′`（q=1，piece={1,2,3}，其余字段平凡；`choice_projection` 只需检查实际输出 1，两边都是 stop）。
- 按正文，N 的任何节点域加细都没有边，因为每个 `D′` 都含因子 `D_{β→β}=∅`。我也在 Lean 里证明了 `∀ P v w, P.network.edge_domain v w = ∅`，而 `2 ∈ N′.edge_domain β β`。
- 所以 N′ 属于关系型，却不是正文的任何一次节点域加细，哪怕允许重命名。
- 影响：
  - 命题仍然真，因为关系型是更一般的模拟关系。
  - 但它不能当作"一步加细"的定义。若用它定义规则族 R，平凡分划下 N→N′ 这种仅改动未使用路由的扰动也算加细，会改变"不可约代表"的含义，也与 `NetworkObject` 按 `presentation_data`（含 `edge_domain`）区分对象的做法冲突。
  - 目前 `IrreducibleRepresentative` 对 R 是抽象的，故源码内暂无误用，属潜在风险。
- 修复方向：
  - 要么把加细定义为 `∃ P e, (N′.relabel e).presentation_data = P.network.presentation_data`，这样命题可由 `presentation_data_eq_extensional_operator`、`relabel_extensional_operator` 和 `network_extensional_eq` 直接得到。
  - 要么在关系型里加入 S2 的公式。
  - 保留现有弱关系，但改名为"行为模拟"，并修正 `NodeDomainRefinement` 的文档（现写 "domain intersections in the text"，与字段不符）。

**S4 建议补充（均为形式或附带结论，不影响命题）。**
- `NetworkRefinement` 结论可封装为 `FiniteOperatorNetwork.ExtensionalEquivalent`，对象层可借 `encode_extensional_operator` 得到 `NetworkObject.ExtensionalEquivalent`。目前源码没有用这两个定义。
- 求值深度 `P.network.evaluation_depth = N.evaluation_depth`：我已证明，由 `network_path_projection` 逐输入长度相等得到。
- `trivialPartition` 证明对任意节点都存在分划（分划不会空缺）。

## 四、不构成缺陷的设计

- `choice_projection` 限于实际输出：删除冗余子节点会改变从未产生的输出上的路由，所以这是必要的弱化，反例与 S3 的具体论证已给出。
- 构造型结论是算子相等而不只是 `≡_U`，两者在域外都取 ⊥，故强于正文。
- `count_pos` 冗余，因为 `node_dom_nonempty` 已蕴含它。
- 不要求显式假设 U 非空：加细节点存在，则 V 非空，故 U 非空。

## 五、核验记录

- 工程内：`lake build formal_oet` 成功；对 `refinement_preserves_local_equivalence`、`refinement_preserves_representation`、`network_extensional_eq`、`network_path_projection`、`self_loop_choice_iff` 运行 `#print axioms`，仅有标准公理。
- 工程外草稿（`import` 附件模块，均以标准公理编译通过）：
  - `toRefinement`（S1）。
  - 公式引理：入口片 2 条，边域 4 条（S2）。
  - `network_evaluation_depth`、`trivialPartition`（S4）。
  - 反例 `exN`、`exN'`、`exRef` 及 `exN_all_refined_edges_empty`（S3）。
- 未审阅代数加细及其他章节。