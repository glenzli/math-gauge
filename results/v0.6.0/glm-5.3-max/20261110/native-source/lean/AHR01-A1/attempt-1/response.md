# 审阅报告：《节点域加细》定义与该情形下《网络加细保持外延等价》的 Lean 实现

## 一、审阅范围与对象

**数学正文**（`source.md`，"网络加细与不可约代表"一节）：

1. "定义（网络加细）**(i)（节点域加细）**"的全部条款：有限非空分划、子节点局域算子（含"即 $f_\beta|_{U_{\beta,a}}$"的末句）、子节点替换、入口片 $U_\beta^{\mathrm{in}}\cap U_{\beta,a}$、入边/出边/自环三类边域交集公式、无关节边与入口片不变、空片省略、终止域由出边域补集确定，以及末段"加细后删去不被轨迹经过的子节点"。
2. "命题 **#h-012f4ba72aeb3f20（网络加细保持外延等价）**"的**节点域加细情形**，含其证明的每个步骤（逐位换子节点、自环、终止域交集、长度界、删冗余、外延相等）。

**Lean 实现分两层**（相互独立、互不 import，见 §六 G3）：

- **关系版** `formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean`：把"N′ 由 N 经一次节点域加细得到"抽象为给定网络间的局部相容性结构 `NodeDomainRefinement`，结论定理 `refinement_preserves_local_equivalence`。
- **构造版** `formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean`：从分划数据 `NodePartitionData` 按正文条款逐字段构造加细网络（含剪除冗余子节点），结论定理 `network_extensional_eq`。

**支撑层**（用于解释对象，非结论审阅对象）：`operator_network.lean`（`FiniteOperatorNetwork`、`TerminalPathFrom`、`node_dom/edge_domain/terminal_domain`、外延算子）、`effective_equivalence.lean`（节点实际输入域及其封闭性）、`network_presentation.lean`（`prune`＝正文"删去冗余节点"引理的机制）、`network_routing.lean`（`terminal_path_unique`）、`decomposition_core.lean`（`LocalEquivalent`、`restrict_operator`）。

**边界**（按题意不作审阅）：代数加细（`AlgebraicRefinement`、`algebraic_refinement_construction.lean`）、允许规则与不可约代表（`network_refinement.lean:423–446` 的 `RefinementRule/ Irreducible / IrreducibleRepresentative`）、前缀扩展、无循环展开；`NetworkRefinement` 归纳（`network_refinement.lean:333`）的两个分支中只审 `node_domain` 分支。

## 二、可复核性核验（先行，因为下文所有"已证明"断言依赖它）

我在本工程内执行了四项检查，全部通过：

1. **整库构建**：`lake build` —— "Build completed successfully (0 jobs)"，即全部 26 个模块的构建产物与当前源码一致。
2. **源码级重新 elaborate**：`lake env lean` 逐一重跑 `network_refinement.lean`、`domain_refinement_construction.lean` 及五个被实质引用的支撑文件（`effective_equivalence / network_presentation / operator_network / decomposition_core / network_routing`）—— 全部零诊断（无 error、无 warning）。
3. **证明空洞扫描**：在 `formal_oet` 全树 `Grep \b(sorry|sorryAx|admit|native_decide)\b|^axiom\b` —— **零命中**。
4. **公理审计**：对 22 个关键定理 `#print axioms` —— 全部仅依赖 `[propext, Classical.choice, Quot.sound]`（`chain_eval_nodes_core_append` 甚至零公理依赖）。**无 `sorryAx`、无自定义公理。**

因此，下文引用的每个定理名都是"源码已证明"，不是陈述性占位。

## 三、《节点域加细》定义逐条对应与判定

正文用边域集合 $D_{\beta\to\gamma}$ 表述，Lean 的 `FiniteOperatorNetwork` 用选择函数表述、边域为导出集（`operator_network.lean:391`：`edge_domain β γ = {z ∈ node_image β : choice β z = next γ}`；终止域恒为补集 `:399`）。这是两层之间的忠实翻译（二者互相确定）。逐条对照：

| # | 正文条款 | Lean 载体（关系版 `network_refinement.lean` / 构造版 `domain_refinement_construction.lean`） | 判定 |
|---|---|---|---|
| 1 | $U_\beta=\mathrm{dom}(f_\beta)$ 换为有限非空分划 $U_\beta=\bigsqcup_{a=1}^q U_{\beta,a}$ | 字段 `part_count/part_count_pos/piece/piece_nonempty/piece_disjoint/piece_cover`（`:77–83`）；构造版 `:13–18`。$U_\beta$ 即 `N.node_dom target`，且 `node_dom = dom f_β`（`operator_network.lean:367,375`）。并＋两两不交＋各片非空＝分划；`part_count_pos` 给 $q\ge1$ | ✅ 完整 |
| 2 | $f_{\beta,a}\in\mathcal X_{\mathrm{op}}$，$\mathrm{dom}(f_{\beta,a})=U_{\beta,a}$，$f_{\beta,a}\equiv_{U_{\beta,a}}f_\beta$ | `local_factor/local_domain/local_equiv`（`:84–89`）；构造版 `:19–21`（`local_eq` 为逐点等式，即 `LocalEquivalent`） | ✅ 完整 |
| 2′ | 末句"$f_{\beta,a}$ 正是 $f_\beta\|_{U_{\beta,a}}$（子域同值、域外皆 ⊥）" | 构造版显式定理 `local_op_eq_restrict`（`:31`）；关系版可导：同域＋片上逐点相等 ⇒ 两算子处处相等（域外双方均 ⊥，由 `dom` 的定义） | ✅（关系版为可导而非命名） |
| 3 | 用子节点 $\beta_a$ 替换 $\beta$；其他节点与局域算子不变 | `source : V' → ({β // β ≠ target} ⊕ Fin part_count)`（`:90`）＋`source_injective`（`:91`，无标签合并）＋`old_node_present`（`:92–93`）＋`old_node_op_compat/piece_node_op_compat`（`:97–102`，**算子相等**而非仅等价）；构造版 `Label`（`:42`）＋`node_op`（`:72`） | ✅ 完整（由此 V′ 恰为"旧节点去 target"⊔"子节点"，见 §四论证） |
| 4 | 删去不被任何轨迹经过的子节点（结果网络） | 关系版：`piece_node_present_iff_reached`（`:94–96`），判据 `NodePieceReached`（`:51`）＝"某存储路径在 target 位置的当前输入落入该片"；构造版：`presentation`（`:208`）→`network := prune`（`:235`），`prune` 即正文删冗余引理的机制（`network_presentation.lean:76`，配套 `prune_eval:127`、`prune_extensional_operator_eq:133`） | ✅ 完整（剪除判据与正文"轨迹经过"逐位一致，论证见 §四） |
| 5 | 若 $\beta$ 入口：子节点入口片 $=U_\beta^{\mathrm{in}}\cap U_{\beta,a}$（空省略） | `entry_projection`（`:104–106`）＋网络公理 `entry_mem`＋分片不交 ⟹ 入口子节点被**强制**为包含该输入的唯一片；非 target 入口原样保留（投影还原）。构造版 `entry := lift_label (N.entry x) x`（`:221`）＋`lift_mem_dom`（`:76`） | ✅（逐点编码，集合级等价；未命名引理 → G5） |
| 6 | 入边 $D'_{\gamma\to\beta_a}=D_{\gamma\to\beta}\cap U_{\beta,a}$ | 关系版：`choice_projection`（`:108–111`，限实际输出）＋`choice_next_mem`＋`piece_disjoint` ⟹ 目的子节点＝含该输出的片（论证见 §四）；构造版：`choice := map_output_choice (lift_label · z) (N.choice (projection ·) z)`（`:111`）——目的标签按**输出**落片提升 | ✅（结构级实现；无命名集合等式 → G1） |
| 7 | 出边 $D'_{\beta_a\to\gamma}=D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$ | 子节点处的选择镜像 $\beta$ 处的选择（关系版 `choice_projection`；构造版 `choice`）；"∩ $f_{\beta,a}(U_{\beta,a})$"由 `edge_domain` 只计入 `node_image (inr a)`（＝ $f_{\beta,a}(U_{\beta,a})$）自动成立 | ✅（同上 → G1） |
| 8 | 自环 $D'_{\beta_a\to\beta_b}=D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}$ | 构造版**显式定理** `self_loop_choice_iff`（`:119`）：在 $z\in f_{\beta,a}(U_{\beta,a})$ 前提下，`choice (inr a) z = next (inr b) ↔ z ∈ D_{β→β} ∧ z ∈ U_{β,b}`；关系版在实际输出处由 `choice_projection`＋`choice_next_mem`覆盖 | ✅（三类边域公式中唯一有显式定理者） |
| 9 | 不与 $\beta$ 关联的边、其他入口片不变 | 构造版由 `choice/entry` 定义统一给出（非 target 目的地与入口原样保留）；关系版 `entry_projection`（入口全域）＋`choice_projection`（实际输出） | ✅ |
| 10 | 空入口片、空边域省略 | choice 编码下边域是导出集，空集自然省略；剪除后指向已删节点的选择改 `stop`（`prune_choice`，`network_presentation.lean`）——与正文"删除节点及其关联边、终止域由补集确定"一致 | ✅（结构性成立） |
| 11 | 各子节点终止域仍由出边域补集确定 | 结构性：`terminal_domain := node_image \ ⋃ edge_domain`（`operator_network.lean:399`）对一切 `FiniteOperatorNetwork` 成立。正文证明中导出的 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$ **未命名**（可导，→ G1） | 部分✅ |
| 12 | 加细不改变输入域 $U$ | `same_input_domain : N'.U = N.U`（`:103`）；构造版 `presentation.U := N.U`（`:208`） | ✅ |

关于读法的一点说明：条款 1 的"非空分划"按"每个分片非空"读（Lean 两侧均如此要求）。即便按宽松读法（允许空片），空片对应的子节点定义域为空、必然被剪除，丢弃空片后最终网络完全相同，故两种读法下覆盖面不变。

## 四、命题与证明步骤逐条对应

**命题陈述**：正文为 $\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}$。Lean：

- 关系版：`refinement_preserves_local_equivalence`（`network_refinement.lean:377`）：`NetworkRefinement N N' → LocalEquivalent N'.extensional_operator N.extensional_operator N.U`，其中 `LocalEquivalent ϕ ψ U := ∀ x ∈ U, ϕ.func x = ψ.func x`（`decomposition_core.lean:109`），`same_input_domain` 使两侧同域。由于两侧外延算子在 $U$ 外均补 ⊥（`extensional_operator`，`operator_network.lean:329`），该局部等价等价于算子相等。
- 构造版以**更强形式**陈述：`network_extensional_eq`（`:258`）：`P.network.extensional_operator = N.extensional_operator`（逐点分 $x\in U$／$x\notin U$ 两情形）。

正文证明步骤与 Lean 引理的对应：

| 正文证明步骤 | Lean 对应 |
|---|---|
| 每当 $\gamma_s=\beta$，由子域分划**唯一**选出 $a_s$（$y_s\in U_{\beta,a_s}$）；不同次经过 $\beta$ 不必选同一子节点 | 构造版 `piece_at`（`:46`）＋`mem_piece_at`（`:50`）＋`piece_at_unique`（`:55`）；逐位重着色 `colour_path`（`:168`）按**当前输入**取片，天然允许不同次取不同子节点 |
| $f'_{\gamma'_s}(y_s)=f_{\gamma_s}(y_s)=y_{s+1}$（子域上取值相同） | 构造版 `lift_apply`（`:85`）；关系版 `node_eval_eq`（`:184`，对全部 V′ 节点） |
| 入口片细分保证 $(\gamma'_1,y_1)$ 是唯一入口状态 | 构造版 `presentation.entry/entry_mem`（`:221–222`）；关系版 `entry_projection`＋网络公理 `entry_mem`（推导见下） |
| $y_{s+1}\in D_{\gamma_s\to\gamma_{s+1}}\cap f'(U')\cap U'=D'_{\gamma'\to\gamma'}$（含自环：下一步进入 $\beta_{a_{s+1}}$） | 构造版 `coloured_terminal`（`:184`）的 `next` 分支（`choice` 的提升定义＋`choice_next_mem`，`:154`；自环公式 `self_loop_choice_iff :119`）；关系版反向投影 `terminal_projection`（`:195`，由 `choice_projection` 导出） |
| $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$，新轨迹仍在末节点终止、终止输出不变 | `coloured_terminal` 的 `stop` 分支（终止输出处的选择保持 `stop`） |
| 长度仍为 $r$；统一长度界 $r'\le\ell(\mathcal N)$ | `colour_path_length`（`:172`）；`presentation.path_length_le_depth`（`:228`，取 `depth_bound := N.depth_bound`，即用原界的有效上界） |
| 新数据满足网络公理（入口、后继唯一、有限性、无冗余） | `presentation`（`:208`）逐字段核验 `FiniteNetworkPresentation` 全部义务；`prune`（`network_presentation.lean:76`）给出 `FiniteOperatorNetwork`（含 `node_reachable`） |
| 删冗余后轨迹与输出不变 ⟹ $\phi_{\mathcal N'}(x)=y_{r+1}=\phi_{\mathcal N}(x)$ | 构造版：`network_path_labels`（`:241`）＋`coloured_eval`（`:197`）＋`network_extensional_eq`（`:258`）。关系版：`eval_projected`（`:222`）＋`path_projection`（`:214`，唯一性由确定性后继 `terminal_path_unique`，`network_routing.lean:14`）＋`path_eval_eq`（`:354`）＋`refinement_preserves_local_equivalence`（`:377`） |

**两条支撑论证**（可复核，是上述"强制/唯一"判定的依据）：

- **入口子节点被强制为含 $x$ 的片**：`entry_projection` 给 `proj(N′.entry x) = N.entry x`。若该值为 target，则 `N′.entry x` 的 `source` 只能是 `inr a`（`inl` 投影为 `β ≠ target`）；于是 `N′.node_op` 于该节点＝`local_factor a`（`piece_node_op_compat`），`entry_mem` 给 $x\in\mathrm{dom}= U_{\beta,a}$；`piece_disjoint` 使 $a$ 唯一。故入口片作为集合恰为 $U^{\mathrm{in}}_\beta\cap U_{\beta,a}$。构造版的对应物是 `lift_label (N.entry x) x`＋`mem_piece_at`。
- **边域目的子节点被强制为含输出 $z$ 的片**：`choice_projection` 把（实际输出 $z$ 处的）`N′.choice` 投影为 `N.choice`；若原选择为 `next β`，则 `N′` 选择 `next β_a`（某 $a$），网络公理 `choice_next_mem` 给 $z\in\mathrm{dom}(\beta_a)=U_{\beta,a}$，不交性使 $a$ 唯一。构造版的对应物是 `choice` 的 `lift_label w z`＋`mem_piece_at`/`choice_next_mem`（并保证提升仅在 $z\in\mathrm{dom}$ 的合法点上取到真片）。

**关系版弱化不损失覆盖的论证**（针对 `choice_projection` 只约束实际输出，`:107` 有源码自注"Pruning may change choices at outputs never reached from the source"）：外延算子只依赖存储轨迹；存储轨迹的每一状态都属于相应节点的**实际输入域**——这正是 `effective_equivalence.lean` 已证明的两条封闭性：`entry_mem_node_actual_input_domain`（`:405`）与 `next_output_mem_node_actual_input_domain`（`:432`）。因此轨迹行使的每个选择都落在受限集合 $(N'.node\_op\ v).func''$ 实际输入域内，非实际输出处的选择差异对 $\phi$ 不可见。正文的构造在这些点上规定为交集公式、剪除后指向已删子节点的选择改 stop，与该弱化版本在轨迹层不可区分。

## 五、总判定

1. **准确性：通过。** 定义 12 项条款与命题（含证明全部步骤）在两层实现中逐条有对应载体，未发现任何歪曲、遗漏前提或加强结论式的偷换；结论形式（$\equiv_U$ ↔ `LocalEquivalent`／更强者算子相等）与正文一致。
2. **完整性（就命题所需数学内容）：通过。** "N′ 由 N 经一次节点域加细得到 ⟹ 外延等价"这一命题本身被**构造版**按正文流程完整实现（构造 → 公理核验 → 剪除 → 外延相等），并被**关系版**以一般充分条件形式再证一次。剪除判据、自环、逐位换片、"不同次可选不同子节点"、终止输出不变、长度不变均有对应引理。
3. 存在若干**陈述层/桥接层**缺口（§六 G1–G5），均**不影响**命题的正确性与覆盖性；其中 G3 值得优先补充。

## 六、不足：数学影响、可复核论证与修复方向

**G1（陈述缺口）｜非自环边域公式与终止域公式未命名为集合等式。**
构造版只有自环有显式定理（`self_loop_choice_iff`）；$D'_{\gamma\to\beta_a}=D_{\gamma\to\beta}\cap U_{\beta,a}$、$D'_{\beta_a\to\gamma}=D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$ 与 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$ 未作为独立命题出现。
**数学影响**：对本命题零影响（它们是 `choice`/`edge_domain`/`terminal_domain` 定义的一步展开）。**可复核论证**：在 choice 编码下 $\mathrm{edge\_domain}(\gamma')(\beta_a)=\{z\in f_\gamma(U_\gamma): \mathrm{choice}_\beta z=\mathrm{next}\,\beta \wedge z\in U_{\beta,a}\}$——其中"落片正确"由 `choice_next_mem`＋`piece_disjoint` 保证；$T'_{\beta_a}=\{z\in f_{\beta,a}(U_{\beta,a}):\mathrm{choice}_\beta z=\mathrm{stop}\}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$（$T_\beta=\{z\in f_\beta(U_\beta):\mathrm{stop}\}$，且 $f_{\beta,a}(U_{\beta,a})\subseteq f_\beta(U_\beta)$ 由 `local_eq`）。**修复方向**：在构造版补三条 `edge_domain`/`terminal_domain` 等式引理（各约 5–15 行，用 `self_loop_choice_iff` 同款论证）。

**G2（设计说明，非缺陷）｜关系版 `choice_projection` 限"实际输出"。**
即非实际输出处 N′ 的选择可与正文规定不同。**论证其不损失覆盖**：见 §四末段——存储轨迹只在实际输出处行使选择（`entry_mem_node_actual_input_domain`/`next_output_mem_node_actual_input_domain`），故对 $\phi_{N'}$ 无影响。**修复方向（若要字面覆盖）**：如 G1 在构造版陈述全集等式即可；关系版维持现状是合理的（源码注释已自述该取舍）。

**G3（桥接缺口，建议优先补充）｜构造版与关系版无形式桥接；关系版无任何实例。**
grep 证据：`NodeDomainRefinement` 仅出现于 `network_refinement.lean`（结构 `:73`、命名空间 `:177–233`、构造子 `:336`）；`NodePartitionData` 仅出现于 `domain_refinement_construction.lean`。全库不存在任何 `NodeDomainRefinement` 的构造实例。
**数学影响**：命题本身不受影响（正文口径的结论已由构造版直证）；但"关系版"目前缺非空性形式证据（可能被质疑为空谈），且两条形式化互不引用、不可互相校验。**修复方向**：补桥接定理 `NodePartitionData.network_extensional_eq` 可由 `P.network ⊨ NodeDomainRefinement N P.network` 重建。字段映射均有现成引理支撑：`source := Subtype.val`（单射）；`old_node_present` 由 `N.node_reachable`＋重着色对 `inl` 的保留；`piece_node_present_iff_reached` 由 `colour_path` 逐位＋`mem_piece_at`；`choice_projection` 在实际输出处成立（剪除只改"指向未达片"的选择，而实际输出的目的地必达，否则该子节点已被该轨迹经过）。估计 60–120 行。

**G4（可选）｜求值深度等式 $\ell(\mathcal N')=\ell(\mathcal N)$ 未陈述。**
构造版已有逐路径长度不变（`colour_path_length`）与深度界继承（`:225, :228`）；正文同段以 $r'\le\ell(\mathcal N)$ 说明统一长度界，非本命题所需。如后续章节需要，可仿 `relabel_evaluation_depth` 风格补一条等式引理。

**G5（可选）｜若干"保持不变"集合级陈述未命名。**
旧节点入口片＝原片、子节点入口片＝$U^{\mathrm{in}}_\beta\cap U_{\beta,a}$、旧节点间边不变、子节点域⊆原节点域（构造版有 `node_domain_subset_original :94`，关系版无对应命名）——均可由现有字段一步导出（推导见 §四）。建议补命名引理以提高自含性；对本命题无影响。

**未发现需要"反例"级别的错误**：所有被审定理均通过编译与公理审计，且逐条对照未发现形式化陈述与正文语义的偏差，故无数学反例可给；上述缺口的"可复核论证"已逐条附上。

## 七、源码已证明结论 vs 待补充内容

**已证明**（编译＋公理审计通过；行号见 §三、§四）：

- 关系版：`NodeDomainRefinement.node_eval_eq`（`:184`）、`.terminal_projection`（`:195`）、`.path_projection`（`:214`）、`.eval_projected`（`:222`）；`NetworkRefinement.same_input_domain`（`:339`）、`.old_input`（`:347`）、`.path_eval_eq`（`:354`，node_domain 分支）；`refinement_preserves_local_equivalence`（`:377`）；`refinement_preserves_representation`（`:404`，超出正文命题的顺延：加细传播网络表示）。
- 构造版：`local_op_eq_restrict`（`:31`）、`mem_piece_at`（`:50`）、`piece_at_unique`（`:55`）、`projection_lift`（`:68`）、`lift_mem_dom`（`:76`）、`lift_apply`（`:85`）、`node_domain_subset_original`（`:94`）、`self_loop_choice_iff`（`:119`）、`choice_next_mem`（`:154`）、`colour_path` 及其长度/投影引理（`:168/172/178`）、`coloured_terminal`（`:184`）、`coloured_eval`（`:197`）、`presentation`（`:208`）、`network`（`:235`）、`network_path_labels`（`:241`）、`network_path_projection`（`:249`）、`network_extensional_eq`（`:258`）。
- 支撑层（本审阅引用者）：`terminal_path_unique`（`network_routing.lean:14`）、`entry_mem_node_actual_input_domain` 与 `next_output_mem_node_actual_input_domain`（`effective_equivalence.lean:405/432`）、`prune/prune_eval/prune_extensional_operator_eq`（`network_presentation.lean:76/127/133`）、`extensional_apply_eq_chain_eval_path`（`operator_network.lean:534`）、`dom_restrict_operator_eq`（`decomposition_core.lean:65`）。

**待补充**（不在源码中，按优先级）：

1. G3 桥接定理＋关系版构造实例（约 60–120 行）；
2. G1 三条边域/终止域集合等式引理（各 5–15 行）；
3. G5 若干"保持不变"命名引理；
4. G4 求值深度等式（如后续章节需要）。

## 八、复核指引

在本工程目录内依次执行（预期结果如 §二）：

```bash
lake build                                   # 0 jobs / success
lake env lean formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean            # 无输出
lake env lean formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean # 无输出
# 公理审计：新建临时文件，import 上述两模块后对下列名称 #print axioms：
#   FiniteOperatorNetwork.refinement_preserves_local_equivalence
#   FiniteOperatorNetwork.NodeDomainRefinement.{node_eval_eq,terminal_projection,path_projection,eval_projected}
#   NodePartitionData.{network_extensional_eq,self_loop_choice_iff,coloured_terminal,coloured_eval}
# 预期：仅 [propext, Classical.choice, Quot.sound]
```

**一句话结论**：所给实现以"关系版＋构造版"双层方式准确覆盖了《节点域加细》定义的全部条款与该情形下《网络加细保持外延等价》命题及其证明的每个步骤，全部相关定理经编译与公理审计确认为已证明；缺口仅存在于陈述层与两版本之间的桥接（G1–G5），其中建议优先补 G3（构造实例/桥接），它们不影响命题的正确性与数学覆盖面。