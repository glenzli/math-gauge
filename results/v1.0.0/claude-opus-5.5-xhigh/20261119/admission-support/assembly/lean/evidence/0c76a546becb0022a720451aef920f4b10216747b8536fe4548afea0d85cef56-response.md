## 结论

在题目限定的范围内，即正文 (i) 节点域加细的定义，以及命题 #h-012f4ba72aeb3f20 的节点域加细情形，**这份 Lean 实现准确且完整，没有发现数学上的缺口**。

具体有三点：

- **定义：** 有两种编码，与正文逐项一致。一种是构造型的 `NodePartitionData`，另一种是关系型的 `NodeDomainRefinement`。
- **命题：** 有两条相互独立的证明，都已完成：
  - 实际构造出的网络（含剪枝）外延算子**全等**。这比正文要求的 $\equiv_U$ 更强。
  - 任何满足 `NodeDomainRefinement` 的 $\mathcal N'$ 在 $U$ 上与原网络局部等价。
- **编译：** 模块 `lake build` 成功。关键定理用 `#print axioms` 检查，只依赖 `propext`、`Classical.choice`、`Quot.sound`。全库检索没有 `sorry`、`admit` 或自定义 `axiom`。

不足之处都在形式化层面：有一个冗余字段、"精确性"没有写成定理、缺少最终打包。详见第五节。

---

## 一、定义逐项对照（正文 (i)）

| 正文条款 | Lean 中的对应 |
|---|---|
| 被细分的节点 $\beta$ | 构造里是 `target` 参数；关系里是 `target` 字段 |
| 有限非空分划 $U_\beta=\bigsqcup_a U_{\beta,a}$ | `count`、`count_pos`、`piece : Fin count → Set X`、`nonempty`、`disjoint`、`cover : ⋃ piece = N.node_dom target` |
| $f_{\beta,a}$ 满足 $\mathrm{dom}=U_{\beta,a}$ 且 $f_{\beta,a}\equiv_{U_{\beta,a}}f_\beta$ | `local_op`、`local_domain`、`local_eq`；正文附注"$f_{\beta,a}=f_\beta|_{U_{\beta,a}}$"由 `local_op_eq_restrict` 证明 |
| 用子节点 $\beta_a$ 替换 $\beta$ | 标签 `Label = {v // v ≠ target} ⊕ Fin count`；关系侧为单射的 `source`，加上 `old_node_op_compat` / `piece_node_op_compat` |
| 子节点入口片取 $U^{\rm in}_\beta\cap U_{\beta,a}$，其余入口片不变 | 构造里 `entry := lift_label (N.entry x) x`；关系侧由 `entry_projection` 推出 `NodeDomainRefinement.entry_domain_eq`：$\mathrm{entry}'(v)=\mathrm{entry}(\pi v)\cap U'_v$。对旧节点这就是"不变"，对子节点就是 $U^{\rm in}_\beta\cap U_{\beta,a}$ |
| 入边、出边、自环的新边域，其余边不变 | 构造的 `choice` 写作 `map_output_choice (lift_label · z) (N.choice (π v) z)`。剪枝前的自环双交由 `self_loop_choice_iff` 给出，剪枝后的统一公式由 `network_edge_domain_eq` 给出；关系侧是字段 `edge_domain_eq` |
| 空入口片、空边省略；终止域取出边域的补集 | Lean 里边就是非空的 `edge_domain`，入口节点就是 `entry_domain` 非空的节点，`terminal_domain` 本身定义为补集，因此自动成立 |
| 按 #h-ced8c7236326e104 删除冗余子节点 | `presentation.prune`、`prune_choice`；`old_label_reached` 证明旧节点全部保留，`piece_label_reached_iff` 证明子节点保留当且仅当 `NodePieceReached` |

统一边域公式是 $D'_{v\to w}=(D_{\pi v\to\pi w}\cap f'_v(U'_v))\cap U'_w$。利用 $D\subseteq f(U)\cap U_{\rm tgt}$，它对四类边分别化简为：

- 旧节点 → 旧节点：保持不变。
- $\gamma\to\beta_a$：$D_{\gamma\to\beta}\cap U_{\beta,a}$。
- $\beta_a\to\gamma$：$D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$。
- $\beta_a\to\beta_b$：正文的双交 $D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}$。

因此正文的全部边域规则都被准确编码。

## 二、命题对照

**正文：** 若 $\mathcal N'$ 由 $\mathcal N$ 经一次节点域加细（含剪枝）得到，则 $\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}$。

**Lean 中有两条证明：**

- **构造层：** `NodePartitionData.network_extensional_eq : P.network.extensional_operator = N.extensional_operator`。前提恰好是正文的加细数据，结论比 $\equiv_U$ 更强。
- **关系层：** `refinement_preserves_local_equivalence (h : NetworkRefinement N N')` 的 `.node_domain` 分支，结论是 `LocalEquivalent N'.ext N.ext N.U`，其中 $U$ 相同由 `same_input_domain` 给出。两层之间由 `network_refinement : NodeDomainRefinement N P.network` 和 `allowed_network_refinement` 连接，所以关系层的前提是可满足的，不是空真。

正文默认 $U\neq\emptyset$；Lean 不需要这个前提。若 $U=\emptyset$，网络没有节点，也就不存在可加细的节点，结论平凡。

## 三、证明结构对照

| 正文证明步骤 | Lean 中的对应 |
|---|---|
| 每次经过 $\beta$ 时，按当前输入唯一选出 $a_s$ | `colour_path`，借助 `piece_at` / `piece_at_unique`；`colour_path_get` 证明第 $n$ 位使用的正是原路径在该位的当前输入 |
| 新轨迹合法且在末节点终止，输出不变 | `coloured_terminal`、`coloured_eval` |
| 轨迹长度不变 | `colour_path_length`、`network_path_projection` |
| 入口唯一、出边互斥、边域落入目标定义域、节点域非空、统一长度界 | 入口唯一和出边互斥由函数型的 `entry` / `choice` 自动保证；其余由 `choice_next_mem`、`node_dom_nonempty`、`depth_bound := N.depth_bound` 给出 |
| 剪枝后求值不变 | `prune_path_labels`、`prune_eval` |
| 关系层 | `node_eval_eq`、`terminal_projection`、`path_projection`、`eval_projected`、`path_eval_eq` |

## 四、边界情形核查

1. **分块非空。** Lean 要求每块非空（`nonempty`）。正文的转移图要求节点定义域非空，所以两者一致。即使允许空块，空块对应的子节点不可达，剪枝后结果相同，只差标签。`count_pos` 可由 $U_\beta\neq\emptyset$ 和覆盖条件推出，冗余但无害。
2. **输出像之外的 `choice` 值。** `piece_at` 在 $U_\beta$ 外的默认值只会出现在输出像之外。进入 `target` 的输出由 `choice_next_mem` 保证落在 $U_\beta$ 内。这些值不属于 `PresentationData`，不影响网络对象。
3. **自环。** 不同次经过 $\beta$ 可以选中不同的子节点，`self_loop_choice_iff` 和 `colour_path` 正确处理了这一点。入口节点同时带入边的情形也正确，因为入口与后继是相互独立的数据。
4. **剪枝会扩大旧节点的终止域。** Lean 与正文一致。例子：
   - 底空间 $\mathcal X=\{\bot,a,b,1,2\}$，入口片 $U=\{a\}$。
   - 节点 $\gamma$：入口片 $\{a\}$，$f_\gamma(a)=1$，$f_\gamma(b)=2$，$U_\gamma=\{a,b\}$，$D_{\gamma\to\beta}=\{1,2\}$。
   - 节点 $\beta$：$f_\beta=\mathrm{id}$，$U_\beta=\{1,2\}$，无出边。
   
   把 $U_\beta$ 分为 $\{1\},\{2\}$ 后，$\beta_2$ 不可达而被删除，于是 $T'_\gamma=\{2\}\supsetneq T_\gamma=\emptyset$，但外延不变。Lean 用 `prune_choice` 把指向已删节点的 `next` 改为 `stop`，`edge_domain_eq` 也只约束保留下来的节点对。这与 #h-ced8c7236326e104 中的 $T^{\mathcal T_R}\supseteq T^{\mathcal T}$ 一致；正文从未声称旧节点的终止域不变。
5. **$q=1$。** 正文和 Lean 都允许，此时加细只是重编号。这只与不可约性有关，不在本题范围内。

## 五、已证明的结论与需要补充的内容

**源码已证明：**
- 构造本身：`presentation`、`network`。
- 外延全等：`network_extensional_eq`。
- 路径重着色与投影：`network_path_labels`、`network_path_projection`。
- 节点保留情况：`old_label_reached`、`piece_label_reached_iff`。
- 边域与自环公式：剪枝后的 `network_edge_domain_eq`，剪枝前的 `self_loop_choice_iff`。
- 实际路由兼容：`network_choice_projection`。
- 构造满足关系：`network_refinement`；入口片交集公式：`entry_domain_eq`。
- 关系层保持定理：`refinement_preserves_local_equivalence`、`refinement_preserves_representation`。

**需要补充（都不构成数学缺口）：**

**(S1) 冗余字段 `choice_projection`。** 这个字段不在正文定义里，关系层的证明却依赖它，而完全没有用到正文意义上的 `edge_domain_eq`。数学上它是冗余的，可以从正文字段推出：

- 对 $x\in U$，沿原路径 $(\beta_k,y_k)$ 归纳。设 $\mathcal N'$ 中的状态 $(v_k,y_k)$ 满足 $\pi v_k=\beta_k$ 且 $y_k\in U'_{v_k}$。
- 由 `node_eval_eq`，$z=f'_{v_k}(y_k)=f_{\beta_k}(y_k)$。
- **原网络在 $z$ 终止时：** 若 $\mathcal N'$ 有某条边 $v_k\to w$ 含 $z$，由 `edge_domain_eq` 得 $z\in D_{\beta_k\to\pi w}$，矛盾。所以 $\mathcal N'$ 也终止。
- **原网络进入 $\gamma$ 时：** 先取 $\mathcal N'$ 中投影为 $\gamma$ 的节点 $w$：
  - 若 $\gamma\neq\beta$，用 `old_node_present` 取 $w$。
  - 若 $\gamma=\beta$，$z$ 属于唯一的块 $a$；$(x,k+1)$ 见证了 `NodePieceReached a`，再由 `piece_node_present_iff_reached` 取 $w$。
  
  于是 $z\in f'_{v_k}(U'_{v_k})\cap U'_w$，由 `edge_domain_eq` 得 $z\in D'_{v_k\to w}$，即 $\mathcal N'$ 的 `choice` 为 `next w`。
- **起点：** 由 `entry_projection` 和 `entry_mem` 给出。
- **收尾：** 由终止路径的唯一性，$\mathcal N'$ 的路径投影后就是原路径，`choice_projection` 随之成立。

我在临时目录写了一份草稿验证这一推导，没有改动附件：`lift_path_aux`、`path_projection_textbook`、`extensional_eq_textbook` 全程不使用 `choice_projection`，编译通过，只依赖三个标准公理。

**影响：** 若有人独立构造出满足正文条款的 $\mathcal N'$，现有关系层定理在使用前要先补证 `choice_projection`。
**修复：** 把上述引理加入库中，把 `choice_projection` 改成由它导出的定理，或从 `NodeDomainRefinement` 中移除这个字段。

**(S2) 关系的"精确性"没有写成定理。** 文档字符串称 `NodeDomainRefinement` 为 "exact relation"。从数学上看确实如此：各字段决定了节点集（旧节点加上可达的块）、局域算子、$U$、入口和全部边域，因而在重编号意义下决定了 `PresentationData`。但库里没有一条定理断言"满足该关系的 $\mathcal N'$ 经某个双射 $V'\simeq$ 可达标签后，与 `P.network` 的表示数据相同"。证明命题本身不需要它；若要把这个关系视为"加细的结果"，就需要补上。

**(S3) 缺少最终打包。** 两个推论都是一两行的事，但源码里都没有：
- `ExtensionalEquivalent N N'`：由 `same_input_domain` 加局部等价即得，我在草稿中已验证。
- 对象层的等价：经 `encode` 后得到 `NetworkObject.ExtensionalEquivalent`，由 `encode_extensional_operator` 加 `network_extensional_eq` 即得。

**(S4) 正文证明里的中间结论没有形式化。** 这两条不是命题的结论：
- $\ell(\mathcal N')=\ell(\mathcal N)$：可由 `network_path_projection` 配合 `evaluation_depth_le_of_input_lengths` 推出。
- 剪枝前的 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$：Lean 通过 `choice` 绕开了这一步。

**(S5) 范围之外。** `RefinementRule (NetworkObject X bot)` 没有用 `NetworkRefinement` 实例化，不可约代表与加细关系之间也没有连接。

## 六、复核方法

- 执行 `lake build formal_oet.vol_01.ch_05_operator_networks.domain_refinement_construction`，应构建成功。
- 对 `network_extensional_eq`、`network_refinement`、`refinement_preserves_local_equivalence`、`entry_domain_eq`、`network_edge_domain_eq` 执行 `#print axioms`，应只出现 `[propext, Classical.choice, Quot.sound]`。
- 全库检索 `sorry`、`admit`、`axiom`，应无结果。