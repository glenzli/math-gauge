## 审阅结论

**结论：** 节点域加细保持外延等价这一命题，在 Lean 中的实现准确、完整，而且已经过机器检查。"节点域加细"这个定义有两个版本：
- **构造版**（`NodePartitionData` → `presentation` → `prune`，下记为 `P.network`）逐项、精确地实现了正文定义。
- **关系版** `NodeDomainRefinement` 同样挂着"定义（网络加细，节点域加细）"的锚点，但它比正文定义严格更宽。源码也没有证明构造出的网络满足这个关系。

这两点都不影响外延等价结论的成立和覆盖范围。但关系版不能当作正文定义，用来推导表示层的性质。

**核查方式：**
- 在给定工程中，两个相关模块 `lake build` 成功。
- 对下列定理执行 `#print axioms`，结果只有 `propext, Classical.choice, Quot.sound`，没有 `sorryAx`：`refinement_preserves_local_equivalence`、`refinement_preserves_representation`、`NodeDomainRefinement.path_projection`、`NodeDomainRefinement.eval_projected`、`NodePartitionData.network_extensional_eq`、`network_path_projection`、`self_loop_choice_iff`、`local_op_eq_restrict`、`FiniteNetworkPresentation.prune_extensional_operator_eq`。
- 下文标"草稿已验证"的结论，是我在工作目录的临时文件 `scratch_review/` 中用 Lean 证明的，同样只依赖上述三个公理。这些文件不属于附件，也不作为提交内容。

## 一、定义逐项对照

| 正文条款 | 构造版 `domain_refinement_construction.lean` | 关系版 `network_refinement.lean:73` | 判断 |
|---|---|---|---|
| $U_\beta$ 的有限非空分划 | `count, count_pos, piece, nonempty, disjoint, cover`（`cover` 为等式，等于 `N.node_dom target`） | `part_count … piece_cover` | 一致。`count_pos` 可由节点域非空和 `cover` 推出，冗余但无害 |
| $\mathrm{dom} f_{\beta,a}=U_{\beta,a}$，且 $f_{\beta,a}\equiv_{U_{\beta,a}} f_\beta$ | `local_domain, local_eq`；`local_op_eq_restrict`（:31）证明 $f_{\beta,a}=f_\beta|_{U_{\beta,a}}$，对应正文的说明 | `local_domain, local_equiv` | 一致 |
| 用子节点 $\beta_a$ 替换 $\beta$ | 标签 `{v // v ≠ β} ⊕ Fin q` 与 `node_op` | `source`（单射）、`old/piece_node_op_compat` | 一致 |
| 入口片取 $U^{in}_\beta\cap U_{\beta,a}$，其余入口片不变 | `entry x := lift_label (N.entry x) x` | `entry_projection`；再由 `N'.entry_mem` 与 `local_domain`，入口被迫落到含 $x$ 的子片 | 一致。构造版的入口片公式源码未单独陈述，草稿已验证（见第五节） |
| 入边 $D_{\gamma\to\beta}\cap U_{\beta,a}$；出边 $D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$；自环取三重交；其余边不变 | `choice v z := map (lift_label · z) (N.choice (π v) z)`（:111）。源码只陈述了自环 `self_loop_choice_iff`（:119），以及 `choice_next_mem`（新边域含于目标节点定义域） | 只在实际产生的输出上约束：`choice_projection`（:108） | 构造版一致：草稿验证了剪枝后保留节点满足全部四类公式。关系版过宽，见第三节 |
| 空入口片、空边域省略；终止域取补 | Lean 中边就是由 `choice` 导出的非空域，终止域按定义是输出像减去出边域之并，自动吻合 | 同左 | 一致 |
| 删除未被经过的子节点（引理 h-ced8c7236326e104） | `network := presentation.prune`。`prune_choice` 把去往被删节点的转移改成 `stop`，等价于删除关联边、终止域相应扩大；另有 `prune_path_labels`、`prune_eval`、`prune_extensional_operator_eq` | `piece_node_present_iff_reached`：某次经过 β 时当前输入落在该片；`old_node_present` | 一致 |

## 二、命题（节点域加细情形）逐项对照

正文结论为 $\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}$。源码给出两条互相独立的证明。

**路线 A（构造版）**，与正文证明 (i) 逐步对应：

| 正文证明步骤 | 源码中的定理 |
|---|---|
| 着色轨迹 $((\gamma'_s,y_s))$ 合法，并在末节点终止 | `coloured_terminal`（:184） |
| 终止输出仍为 $y_{r+1}$ | `coloured_eval`（:197） |
| 入口分划、确定后继、统一长度界 | `presentation`（:208），其中 `depth_bound := N.depth_bound` |
| 引用剪枝引理 | `prune` |
| 轨迹逐点对应，长度不变 | `network_path_labels`、`network_path_projection` |
| 结论 | `network_extensional_eq`（:258）：两者外延算子相等。这比 $\equiv_U$ 更强，因为两边在 $U$ 外都取 ⊥ |

**路线 B（关系版）**：

- `node_eval_eq` → `terminal_projection`：沿 $\mathcal N'$ 的实际轨迹归纳，投影后得到 $\mathcal N$ 的终止路径。
- `path_projection`：借 `terminal_path_unique`。
- `eval_projected` → `NetworkRefinement.path_eval_eq`。
- `refinement_preserves_local_equivalence`（:377）：`LocalEquivalent N'.extensional_operator N.extensional_operator N.U`，与正文结论形式完全一致。
- 推论 `refinement_preserves_representation`。

**前提不暗含结论**：关系版的字段都是单步规律，包括节点算子、入口投影、单步后继投影。完整轨迹的对应是归纳推出的，不是作为字段假设的。

**附注（不是缺陷）**：路线 B 的证明只用到 7 个字段：`old_node_op_compat, piece_node_op_compat, local_domain, local_equiv, same_input_domain, entry_projection, choice_projection`。下列字段都没有用到：`part_count_pos, piece_nonempty, piece_disjoint, piece_cover, source_injective, old_node_present, piece_node_present_iff_reached`。

因此，外延结论对更一般的"沿实际轨迹投影一致"的 $\mathcal N'$ 都成立。分划性质的作用是保证 $\mathcal N'$ 能被良定地构造出来，构造版中的 `mem_piece_at`、`piece_at_unique`、`lift_mem_dom` 就依赖它们。

## 三、不足 1：关系版 `NodeDomainRefinement` 比正文定义严格更宽

问题出在 `choice_projection`：它只对 `N'.node_actual_input_domain v` 的像施加约束。节点输出像中从未被实际产生的点，路由可以任意设置，只要 $\mathcal N'$ 仍是合法网络。

**反例（可手算复核，草稿已用 Lean 验证）。** 取 $\mathcal X=\{\bot,1,2\}$（Lean 中用 `Fin 3`，⊥ 为 0）。

原网络 $\mathcal N$，节点为 β、γ：
- $f_\beta=\mathrm{id}$，$U_\beta=\{1,2\}$；$f_\gamma$ 交换 1 和 2，$U_\gamma=\{1,2\}$。
- $U=U^{in}_\beta=\{1\}$。
- 只有一条边 β→γ，$D_{\beta\to\gamma}=\{1\}$；γ 没有出边。
- 输入 1 的轨迹为 $(\beta,1)\to(\gamma,1)\to 2$，在 2 处终止。$\mathcal N$ 无环，且两个节点都被经过。

网络 $\mathcal N_2$，节点为 $\beta_1$、γ：
- $\beta_1$ 是 β 的平凡加细：$q=1$，$U_{\beta,1}=U_\beta$，$f_{\beta,1}=f_\beta$。
- 其余与 $\mathcal N$ 相同，只额外让 γ 把输出 1 送回 $\beta_1$：$D_{\gamma\to\beta_1}=\{1\}$。由于 $1\in f_\gamma(U_\gamma)\cap U_{\beta,1}$，转移图条件满足；γ 只有这一条出边，互斥条件自动成立。
- 输入 1 的轨迹不变：$(\beta_1,1)\to(\gamma,1)\to 2$，而 $2\notin D_{\gamma\to\beta_1}$，于是终止。所以 $\mathcal N_2$ 是合法的有限算子网络。

关系 `NodeDomainRefinement N N₂` 成立：
- 取目标为 β，$q=1$，`source` 把 $\beta_1$ 映到 `inr 0`、把 γ 映到 `inl γ`。
- γ 的实际输入域是 $\{1\}$，实际输出是 $\{2\}$，两网在 2 处都终止。
- $\beta_1$ 的实际输出是 $\{1\}$，两网都转入 γ。
- `choice_projection` 不检查从未产生的输出 $1\in f_\gamma(U_\gamma)$。

但 $\mathcal N_2$ 不是 $\mathcal N$ 的任何一次节点域加细结果，任何重标号下也不是：
- 正文加细的每条新边都投影为一条旧边，边域含于旧边域：$D'_{u\to w}\subseteq D_{\pi u\to\pi w}$。四类公式逐条可见；剪枝只删边，不会增边。
- 所以 $\mathcal N$ 无环时，它的任何正文加细也无环：新图中的有向闭路会投影成旧图中的闭途径。
- 而 $\mathcal N_2$ 中 $\beta_1\to\gamma\to\beta_1$ 是有向闭路，而且 $D_{\gamma\to\beta}=\emptyset$。

草稿中验证的 Lean 陈述：
- `rel : NodeDomainRefinement N N2`
- `(N2.edge_domain true false).Nonempty`
- `N.edge_domain true false = ∅`
- `(N2.edge_domain false true).Nonempty`

**数学影响：**
- 外延层面没有影响：假设更宽，定理反而更强，$\mathcal N_2$ 也确实与 $\mathcal N$ 外延相等。
- 表示层面有影响，`NetworkRefinement N N'` 不能代表"一步节点域加细"：
  - 加细结果不再在重标号意义下唯一，其表示数据和 $\mathcal X_{\mathrm{net}}$ 对象身份都不确定。
  - 正文成立的结构性质不再能继承，例如"新边投影为旧边且边域包含"、"无环网络的加细仍无环"。
  - 用作加细规则族时，后继集合会多出非正文网络。不过"是否存在后继"不受影响：由关系可以抽出分划数据，再用构造得到一个正文后继。
- 关系版 docstring 写的 "local laws for the domain intersections in the text" 也言过其实：正文的交集公式只在实际输出上得到体现。

**修复方向：**
- (a) 推荐把正文定义锚定到构造：
  `IsNodeDomainRefinement N N' := ∃ β (P : NodePartitionData N β) (e : {v // P.presentation.Reached v} ≃ V'), N' = P.network.relabel e`。
  外延等价可由 `network_extensional_eq` 与 `relabel_extensional_operator` 立即得到。关系版则保留为充分条件，并改写 docstring：它刻画的是"正文加细，再在从未产生的输出上任意修改路由"。
- (b) 如果要让关系版本身成为精确定义，就把 `choice_projection` 换成在整个输出像上、带剪枝的精确条款。对 $z\in$ `N'.node_image v`：
  - 若 $\mathcal N$ 在 $z$ 处给 `stop`，则 $\mathcal N'$ 也给 `stop`。
  - 若 $\mathcal N$ 给 `next w`：当存在 $u$ 使 `source u` $=\lambda(w,z)$ 时，$\mathcal N'$ 给 `next u`；否则给 `stop`。这里 $\lambda(w,z)=$ `inl w`（$w\neq\beta$），$\lambda(\beta,z)=$ `inr a`（$z\in U_{\beta,a}$）。

  不能简单地把现有 `choice_projection` 的量词范围扩大到整个输出像，否则连正文加细本身都不满足。例子：$U=\{1\}$，γ 为入口，$f_\gamma=f_\beta=\mathrm{id}|_{\{1,2\}}$，$D_{\gamma\to\beta}=\{1,2\}$；取分划 $\{1\}\sqcup\{2\}$，子节点 $\beta_{\{2\}}$ 从未被经过而被删除。剪枝后 γ 在输出 2 处终止，而 $\mathcal N$ 在 2 处给 `next β`。

  现有证明只用到实际输出，所以这样加强后证明无需改动。

## 四、不足 2：构造版与关系版之间没有桥接定理

源码中两者各自证明了外延等价，但没有证明构造出的网络满足关系版。这个桥接事实成立，草稿已验证：

```lean
noncomputable def to_refinement (P : NodePartitionData N target) :
    NodeDomainRefinement N P.network
-- 由此 refinement_preserves_local_equivalence (.node_domain (to_refinement P)) 也覆盖构造版
```

证明要点（`source := Subtype.val`，其余数据直接取自 `P`）：
- **`old_node_present`**：由 $\mathcal N$ 的无冗余条件取一个经过 γ 的输入；着色路径中 γ 的这次发生被标为 `inl γ`，因此它被保留。
- **`piece_node_present_iff_reached`**：
  - `inr a` 出现在着色路径中，当且仅当存在位置 $n$ 使路径第 $n$ 位是 β，且该处当前输入的 `piece_at` 等于 $a$。
  - 再用 `terminal_path_prefix_input_mem` 得到当前输入属于 $U_\beta$。
  - 最后用 `mem_piece_at` 与 `piece_at_unique`，把条件换成"当前输入属于 $U_{\beta,a}$"。
- **`choice_projection`**：
  - 设 $z$ 是 $v$ 处的实际输出，且 $\mathcal N$ 在 $z$ 处给 `next w`。
  - 用 `prune_path_labels` 把剪枝后路径的分解搬回未剪枝的着色路径。
  - 由 `terminal_path_suffix_of_next_at_prefix`，提升后的标签 $\lambda(w,z)$ 正是该路径上的下一个标签，因而属于 `Reached`，`prune_choice` 不会把它改成 `stop`。
  - 投影后即得 `next w`；`stop` 情形是平凡的。

## 五、正文证明中的中间结论，源码未显式陈述

这些都不是主结论的缺口，但正文证明用到了它们：

1. **边域与入口片公式**：源码只陈述了自环情形。草稿验证了剪枝后保留节点上的全部公式：
   - 入边：`edge_domain (inl γ) (inr a) = N.edge_domain γ β ∩ piece a`
   - 出边：`edge_domain (inr a) (inl γ) = N.edge_domain β γ ∩ (local_op a) '' piece a`
   - 自环三重交公式
   - 不涉及 β 的边：`edge_domain (inl γ) (inl δ) = N.edge_domain γ δ`
   - 入口片：`entry_domain (inr a) = N.entry_domain β ∩ piece a`，`entry_domain (inl γ) = N.entry_domain γ`
2. **终止域公式**：剪枝前 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$；剪枝后等于它再并上"去往被删子节点"的那些输出。在 Lean 编码中，这可由上述边域公式按补集定义推出，但源码没有写出。
3. **长度界 $r'\le\ell(\mathcal N)$**：源码只有存储的界 `depth_bound := N.depth_bound` 和逐点路径投影。草稿验证了更强的 `P.network.evaluation_depth = N.evaluation_depth`。
4. **旧节点不会被剪掉**：正文证明中隐含这一点，即桥接里的 `old_node_present`。
5. **打包形式**：以下结论都可由现有引理一两行得到，但源码未写出：
   - `FiniteOperatorNetwork.ExtensionalEquivalent N' N`（同一输入域且局部等价）
   - 任意重标号后，或编号编码进入 $\mathcal X_{\mathrm{net}}$ 后，外延算子仍相等。

   所需引理为 `same_input_domain`、`relabel_extensional_operator`、`NonemptyOperatorNetwork.encode_extensional_operator`。

## 六、汇总

**源码已证明（机器检查，无 sorry）：**
- 构造版：
  - `local_op_eq_restrict`、`self_loop_choice_iff`、`choice_next_mem`
  - `presentation`（全部网络义务）
  - `coloured_terminal`、`coloured_eval`
  - 剪枝引理三件：`prune_path_labels`、`prune_eval`、`prune_extensional_operator_eq`
  - `network_path_labels`、`network_path_projection`
  - **`network_extensional_eq`**：外延算子相等
- 关系版：
  - `node_eval_eq`、`terminal_projection`、`path_projection`、`eval_projected`、`path_eval_eq`
  - **`refinement_preserves_local_equivalence`**、`refinement_preserves_representation`

**需要补充：**
1. 修正或重新定位关系版定义：反例见第三节，修复方案为 (a) 或 (b)，并同步修改 docstring。
2. 加入桥接定理 `to_refinement`（第四节）。
3. 显式陈述第五节的边域、入口片、终止域公式，求值深度相等，以及打包形式。

前两项属于定义层面的准确性问题；第三项是对正文证明细节的补全。三项都不改变以下结论：在节点域加细情形下，"网络加细保持外延等价"已被完整证明。