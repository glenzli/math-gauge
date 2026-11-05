### 审阅结论概述

附件数学正文中的**“节点域加细”**定义及**“网络加细保持外延等价”**定理（命题 #h-012f4ba72aeb3f20）在 Lean 代码库中得到了实质性且严谨的形式化实现。实现采用了**“双轨并行”**架构：
1. **构造轨**（`domain_refinement_construction.lean`）：给定网络 $N$ 与分划数据 $P$，显式构造出未剪枝展示网络 `P.presentation`，经可达性剪枝生成具体加细网络 `P.network`，并机检证明了全域算子恒等定理 `network_extensional_eq : P.network.extensional_operator = N.extensional_operator`；
2. **关系轨**（`network_refinement.lean`）：定义了抽象加细关系结构体 `NodeDomainRefinement`，并机检证明了关系型保持定理 `refinement_preserves_local_equivalence`。

**总体判断**：所给实现**高度准确地覆盖了核心动力学求值与外延算子不变性**，关键定理证明完备且无假定缺陷；但在**数学范围的完全覆盖与架构闭环**上仍有明确不足：构造轨与关系轨**未建立闭环连接**、边域与终止域的**集合论公式刻画不完整**、关系型定义对**非可达态转移存在结构放宽**，以及缺少向标准编号对象空间 $\mathcal{X}_{\mathrm{net}}$ 的升格包装。

---

### 一、 定义与核心定理的逐项对应分析

#### 1. “节点域加细”定义各要素的实现对齐
* **定义域有限非空分划** ($U_\beta = \bigsqcup_{a=1}^q U_{\beta, a}$)：
  * `domain_refinement_construction.lean` 中的 `NodePartitionData` 严格包含了 `count : ℕ`、`count_pos : 0 < count`、`piece : Fin count → Set X`、`nonempty`、`disjoint` 与 `cover`。
  * `network_refinement.lean` 中的 `NodeDomainRefinement` 同样包含上述分划公理。完全准确对应。
* **子节点局域算子** ($f_{\beta, a} \in \mathcal{X}_{\mathrm{op}}, \operatorname{dom}(f_{\beta, a}) = U_{\beta, a}, f_{\beta, a} \equiv_{U_{\beta, a}} f_\beta$)：
  * 构造轨声明 `local_op`、`local_domain` 与 `local_eq`，并给出了定理 `local_op_eq_restrict : P.local_op a = restrict_operator (N.node_op target) (P.piece a)`，与正文“二者在子域上取值相同，在域外都取 $\bot$”的说明完全一致。
  * 关系轨声明 `local_factor`、`local_domain` 与 `local_equiv`。完全准确对应。
* **节点替换与标签映射** ($\beta \mapsto \{\beta_a\}$)：
  * 构造轨使用不交和标签 `P.Label := {v : V // v ≠ target} ⊕ Fin P.count`。
  * 关系轨使用单射 `source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)`。完全准确对应。
* **入口输入片细分** ($U_{\beta, a}^{\mathrm{in}} = U_\beta^{\mathrm{in}} \cap U_{\beta, a}$)：
  * 构造轨通过 `lift_label` 与 `piece_at` 实现：若原入口为目标节点，则依据当前输入点 $x$ 所在的唯一分块分配到对应的子节点 `.inr (P.piece_at x)`。
  * 关系轨通过 `entry_projection` 及节点的类型良构性（`entry_mem`）保证输入严格落在分块交集中。
* **边域转移规则**：
  * 构造轨中通过统一确定性选择函数 `P.choice` 配合 `lift_label` 实现。源码给出了自环双交集定理 `self_loop_choice_iff`。
* **删除冗余节点**：
  * 构造轨通过 `P.presentation.prune`，依据 `Reached (v : V) : Prop := ∃ x : N.U, v ∈ N.path_of x` 精确删除了未被任何输入轨迹访问的节点；
  * 关系轨通过 `piece_node_present_iff_reached` 要求子节点存在当且仅当其分块被实际轨迹到达。

#### 2. “网络加细保持外延等价”的实现对齐
* **构造轨定理**：
  * 源码结论：`theorem network_extensional_eq : P.network.extensional_operator = N.extensional_operator`
  * 前提：仅需原网络为合法的 `FiniteOperatorNetwork` 且给定合法的 `NodePartitionData`。
  * 对应性：证明经由 `colour_path`（按当前点值提升轨迹）、`coloured_terminal`（提升后仍为终止路径）、`coloured_eval`（求值一致）以及 `FiniteNetworkPresentation.prune_eval`（剪枝保持求值）。结论直接证明了算子在全空间的严格相等（`=`），强于正文的限制域局部等价（$\equiv_U$）。
* **关系轨定理**：
  * 源码结论：`theorem refinement_preserves_local_equivalence (h : NetworkRefinement N N') : LocalEquivalent N'.extensional_operator N.extensional_operator N.U`
  * 对应性：在假设 `NodeDomainRefinement N N'` 的前提下，通过 `terminal_projection`（新路径投影为原路径）与 `terminal_path_unique` 建立轨迹的唯一对应，证出在输入域 $U$ 上的局部等价，形式同构于正文命题 #h-012f4ba72aeb3f20。

---

### 二、 不足之处、具体数学影响与修复方向

#### 不足 1：构造轨与关系轨未建立连接定理（双轨断联）
* **具体表现**：
  `domain_refinement_construction.lean` 完成了从分划数据 $P$ 到网络 `P.network` 的具体构造；而 `network_refinement.lean` 将 `NodeDomainRefinement` 嵌入为归纳类型 `NetworkRefinement` 的分支。然而，**两模块完全互不引用，源码中没有任何定理证明 `P.network` 满足 `NodeDomainRefinement N P.network`**。
* **数学与工程影响**：
  1. **抽象关系无实例验证**：`NodeDomainRefinement` 在代码库中是无任何构造实例的“空载”结构体，无法确认其所有字段在实际剪枝网络中不存在互相矛盾。
  2. **规则系统无法使用具体加细**：后文的允许加细规则 `RefinementRule` 及不可约代表 `IrreducibleRepresentative` 均建立在抽象加细关系上。用户通过 `NodePartitionData` 构造出的加细网络无法直接作为实例进入加细规则体系。
* **修复方向**：
  构建从构造数据到关系类型的桥梁定理：
  ```lean
  def NodePartitionData.toNodeDomainRefinement
      (P : NodePartitionData N target) : NodeDomainRefinement N P.network
  ```
  利用 `P.presentation.Reached` 的性质逐项回填 `old_node_present`、`piece_node_present_iff_reached` 与 `choice_projection`。

#### 不足 2：底层边域与终止域的集合论公式未完整定理化
* **具体表现**：
  正文定义明确给出了三类边域的交集公式与终止域补集公式：
  $$D'_{\gamma \to \beta_a} = D_{\gamma \to \beta} \cap U_{\beta, a}, \quad D'_{\beta_a \to \gamma} = D_{\beta \to \gamma} \cap f_{\beta, a}(U_{\beta, a}), \quad T'_{\beta_a} = f_{\beta, a}(U_{\beta, a}) \cap T_\beta$$
  Lean 源码中：
  1. 仅在 `self_loop_choice_iff` 中对自环边证明了双交集等价性；
  2. 入边公式 $D'_{\gamma \to \beta_a}$ 与出边公式 $D'_{\beta_a \to \gamma}$ 仅隐式包含在 `P.choice` 的分支代码中，**未提取为显式的集合相等或等价命题**；
  3. 终止域补集截断公式 $T'_{\beta_a}$ **在整个源码中完全缺失**，源码直接通过 `OutputChoice.stop` 的保持绕过了终止域的集合论计算。
* **数学影响**：
  正文的许多下游性质（如转移图谱、不可约性判据、单步零化截断）依赖显式集合形式的 $D'$ 与 $T'$。若无法从转移图 `OperatorTransitionGraph` 层面直接调用这些集合等式，将导致图结构分析层与网络执行层的割裂。
* **修复方向**：
  在 `domain_refinement_construction.lean` 中补充针对未剪枝转移图 `to_transition_graph` 的引理：
  - 入边：`P.presentation.to_transition_graph.edge_domain (.inl γ) (.inr a) = N.edge_domain γ.val target ∩ P.piece a`
  - 出边：`P.presentation.to_transition_graph.edge_domain (.inr a) (.inl γ) = N.edge_domain target γ.val ∩ (P.local_op a).func '' P.piece a`
  - 终止域：`P.presentation.to_transition_graph.terminal_domain (.inr a) = (P.local_op a).func '' P.piece a ∩ N.terminal_domain target`

#### 不足 3：关系定义中边选择条件的局部放宽（对非可达态欠约束）
* **具体表现**：
  在 `NodeDomainRefinement` 中，边选择约束为：
  ```lean
  choice_projection :
    ∀ (v : V') (z : X), z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v →
      map_output_choice (node_domain_projection target source) (N'.choice v z) =
        N.choice (node_domain_projection target source v) z
  ```
  该前提局限在 `node_actual_input_domain` 的像集内。
* **论证与数学影响**：
  正文对边域的细分是针对算子定义域全局静态给出的（在剪枝前边域对所有 $x \in U_\beta$ 均有效）。
  而在 `NodeDomainRefinement` 中，若节点 $v$ 的定义域中存在未被任何输入实际访问的点 $y_0$，则对于 $z_0 = (N'.node\_op\ v).func\ y_0$，关系并未约束 `N'.choice v z_0`。甚至允许 $N'$ 在 $z_0$ 处发生违背正文边域公式的跳转（只要该点不属于实际轨迹输入）。
  这表明 `NodeDomainRefinement` 属于**弱化的外延行为代理公理**，而非正文图结构变换的刚性代数刻画。

#### 不足 4：未实现向标准规范对象空间 $\mathcal{X}_{\mathrm{net}}$ 的编号升格
* **具体表现**：
  正文约定：网络进入对象空间 $\mathcal{X}_{\mathrm{net}}$ 前须进行编号编码（对应于节点标签为 `Fin n` 的 `NetworkObject`）。
  源码中 `P.network` 的节点类型为复合子类型 `{v : P.Label // P.presentation.Reached v}`，源码缺乏将加细后的具体网络重标（relabel）并打包为 `NetworkObject` 的封装定理，导致节点加细运算无法作为 $\mathcal{X}_{\mathrm{net}}$ 上的内部算子闭环使用。

---

### 三、 源码已证明结论与需要补充的内容清单

| 范畴 | 数学正文结论 | 源码已证明结论 | 需补充的内容 |
| :--- | :--- | :--- | :--- |
| **定义：分划与局域算子** | $U_\beta = \bigsqcup U_{\beta, a}$，且 $f_{\beta, a} = f_\beta\|_{U_{\beta, a}}$ | `NodePartitionData`；`local_op_eq_restrict` | 无需补充（完全覆盖） |
| **定义：入边与出边公式** | $D'_{\gamma \to \beta_a} = D \cap U_{\beta, a}$；$D'_{\beta_a \to \gamma} = D \cap f(U)$ | 仅实现函数 `P.choice`，无独立定理 | 需补充两类边域关于集合交集的充要判定引理 |
| **定义：自环边域公式** | $D'_{\beta_a \to \beta_b} = D_{\beta \to \beta} \cap f(U_{\beta, a}) \cap U_{\beta, b}$ | `self_loop_choice_iff` | 无需补充（完全覆盖） |
| **定义：终止域补集公式** | $T'_{\beta_a} = f_{\beta, a}(U_{\beta, a}) \cap T_\beta$ | 无（仅通过 `.stop` 转移代数保持） | 需补充集合论意义上的终止域恒等式定理 |
| **定义：冗余节点剪枝** | 删去未被输入轨迹经过的节点 | `FiniteNetworkPresentation.prune` | 无需补充（完全覆盖） |
| **命题：加细保持外延（构造）** | $\phi_{\mathcal{N}'} \equiv_U \phi_{\mathcal{N}}$ | `network_extensional_eq`（严格算子相等） | 无需补充（完全覆盖且更强） |
| **命题：加细保持外延（关系）** | $\mathcal{N} \to \mathcal{N}' \implies \phi_{\mathcal{N}'} \equiv_U \phi_{\mathcal{N}}$ | `refinement_preserves_local_equivalence` | 无需补充（完全覆盖） |
| **架构：构造与关系闭环** | 具体的构造网络是抽象加细关系的实例 | 无（双轨断开） | 需补充 `P.toNodeDomainRefinement` 桥接定理 |
| **架构：对象空间编号提升** | 加细作为对象空间 $\mathcal{X}_{\mathrm{net}}$ 内部操作 | 仅定义了抽象 `RefinementRule (NetworkObject ...)` | 需补充由 `P.network` 向标准 `NetworkObject` 的重标提升 |
