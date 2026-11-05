### 审阅结论

附件数学正文中关于**“节点域加细”**（定义 [#h-eddd1f2d0a9d3528(i)](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/source.md#L1050-L1066)）以及该情形下**“网络加细保持外延等价”**（命题 [#h-012f4ba72aeb3f20](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/source.md#L1097-L1134)）的 Lean 实现是**准确且完整**的。

该实现采用了“**关系规约保持定理** + **构造性显式实现**”的双层架构：
1. **关系规约层**（[`network_refinement.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean)）：将数学定义抽象为有限算子网络间的加细谓词 [`NodeDomainRefinement`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L118-L125)，并严格证明了只要网络满足该加细关系，其外延算子在输入域上必保持局部等价（[`refinement_preserves_local_equivalence`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L453-L474)）；
2. **构造实现层**（[`domain_refinement_construction.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean)）：针对任意给定的有限算子网络与节点分划数据 [`NodePartitionData`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L12-L23)，具体构造出加细且剪去不可达节点后的新网络 [`network`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L235)，并证明该具体网络无条件满足加细关系规范 [`network_refinement`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L449-L494)，且其全局外延算子与原网络完全相等（[`network_extensional_eq`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258-L267)）。

---

### 一、逐项对应说明：定义、前提与结论的映射

#### 1. 节点域加细定义的逐项对应

| 数学正文定义条目（定义 #h-eddd1f2d0a9d3528(i)） | Lean 实现载体与对应字段 / 定理 | 语义对应性说明 |
| :--- | :--- | :--- |
| **底层网络对象**：设 $\mathcal{N}$ 为有限算子网络 | [`FiniteOperatorNetwork X bot V`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L42-L61) | 包含有限节点集、输入域 $U$、入口分配、局域算子、确定性单值路由、有限深度界及无冗余节点公理。 |
| **定义域分划**：将节点 $\beta$ 的定义域替换为有限非空分划 $U_\beta = \bigsqcup_{a=1}^q U_{\beta, a}$ | [`OperationalNodeDomainRefinement`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L68-L77) 的 `target`、`part_count` ($q > 0$)、`piece`、`piece_nonempty`、`piece_disjoint`、`piece_cover` | 严格对应：分划块由 `Fin part_count` 索引，非空、两两不交且并集等于原节点域 $\operatorname{dom}(f_\beta)$。 |
| **子节点局域算子**：$\operatorname{dom}(f_{\beta, a}) = U_{\beta, a}$ 且 $f_{\beta, a} \equiv_{U_{\beta, a}} f_\beta$ | [`OperationalNodeDomainRefinement`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L78-L83) 的 `local_factor`、`local_domain`、`local_equiv`；构造层引理 [`local_op_eq_restrict`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L30-L40) | 形式化精确表述了域限制及逐点相等，构造层进一步证明了 $f_{\beta, a} = f_\beta \vert_{U_{\beta, a}}$。 |
| **节点集替换与可达性剪枝**：以子节点 $\beta_a$ 替换 $\beta$；加细后若产生不被任何输入轨迹经过的子节点，按规则删除 | [`OperationalNodeDomainRefinement`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L84-L95) 的 `source`、`source_injective`、`old_node_present`、`piece_node_present_iff_reached`；构造层 [`presentation.prune`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L235) 及其定理 [`piece_label_reached_iff`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L318-L343) | 关系层规定未替换节点全部保留（原网络无冗余节点），新子节点保留**当且仅当**其实际被某条入口求值轨迹访问（[`NodePieceReached`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L48-L54)）；构造层通过拓扑剪枝完全落实该条件。 |
| **入口输入片细分**：若 $\beta$ 为入口节点，子节点入口片为 $U_\beta^{\mathrm{in}} \cap U_{\beta, a}$，其余不变 | 关系层定理 [`entry_domain_eq`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L283-L297)（证明 $N'.\text{entry\_domain } v = N.\text{entry\_domain } (\pi v) \cap N'.\text{node\_dom } v$）；构造层 `entry` 提升定义 | 严格等价：对于未受影响节点交集保持不变，对于子节点 $\beta_a$ 自动与 $U_{\beta, a}$ 取交。 |
| **边域定义**：<br>1. 入边：$D'_{\gamma \to \beta_a} = D_{\gamma \to \beta} \cap U_{\beta, a}$<br>2. 出边：$D'_{\beta_a \to \gamma} = D_{\beta \to \gamma} \cap f_{\beta, a}(U_{\beta, a})$<br>3. 自环：$D'_{\beta_a \to \beta_b} = D_{\beta \to \beta} \cap f_{\beta, a}(U_{\beta, a}) \cap U_{\beta, b}$<br>4. 其余边保持不变 | [`NodeDomainRefinement.edge_domain_eq`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L121-L125) 的统一交集公式：<br>$\forall v, w \in V', N'.\text{edge\_domain } v\ w = (N.\text{edge\_domain } (\pi v)\ (\pi w) \cap N'.\text{node\_image } v) \cap N'.\text{node\_dom } w$；构造层定理 [`network_edge_domain_eq`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L346-L380) | **代数统一化**：因为旧边域本来就包含在源节点输出像与目标节点定义域内，该统一交集公式对入边自动交上 $U_{\beta, a}$，对出边自动交上 $f_{\beta, a}(U_{\beta, a})$，对自环同时交上二者，对无关节点则保持不变。数学逻辑与分情况公式完全等价。 |
| **终止域补集确定**：$T'_{\beta_a} = f_{\beta, a}(U_{\beta, a}) \cap T_\beta$，其余不变 | 路由字段 `choice`（[`OutputChoice`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L15-L21)）及规约条件 `choice_projection`；构造层引理 [`network_choice_projection`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L383-L440) | 在确定性算子网络中，终止域就是输出像中选择 `OutputChoice.stop` 的点集，对应出边域的补集。路由投影条件确保了实际到达的像点终止状态严格同调。 |

#### 2. 前提与结论的对应

- **数学命题前提**：$\mathcal{N}'$ 由 $\mathcal{N}$ 经一次节点域加细得到。
  - **Lean 关系层对应**：[`h : NetworkRefinement N N'`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L407-L413)（在分支 `NetworkRefinement.node_domain href` 中）；
  - **Lean 构造层对应**：由原网络 $N$ 和分划数据 $P$ 产出的 `P.network` 直接实例化了该关系（[`allowed_network_refinement`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L496-L498)）。
- **数学命题结论**：$\phi_{\mathcal{N}'} \equiv_U \phi_{\mathcal{N}}$。
  - **Lean 关系层对应**：[`refinement_preserves_local_equivalence`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L453-L474) 证明了 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U`；
  - **Lean 构造层对应**：[`network_extensional_eq`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258-L267) 证明了更强的全局外延算子相等 `P.network.extensional_operator = N.extensional_operator`（在输入域 $U$ 外二者均恒等于 $\bot$）。

---

### 二、源码已证明的结论与需要补充的内容

#### 1. 源码已证明的结论

1. **路径投影唯一性与求值等价**：
   - 证明了加细网络 $N'$ 中任意输入的终止求值路径经节点投影 $\pi$ 映射后，恰为原网络 $N$ 对应的终止求值路径（[`path_projection`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L228-L234)）；
   - 证明了沿加细路径的复合求值与沿投影路径的复合求值逐点相等（[`eval_projected`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L236-L245)）；
   - 证明了外延算子在输入域 $U$ 上的局部等价性（[`refinement_preserves_local_equivalence`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L453-L474)），以及算子表示性质的保持（[`refinement_preserves_representation`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L480-L494)）。
2. **加细算子网络的构造存在性与公理满足性**：
   - 给定任意有限算子网络 $N$ 与分划数据 $P$，源码显式构造了预网络 [`presentation`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L211-L233) 并通过不可达剪枝获得 `P.network`，证明其满足 `FiniteOperatorNetwork` 的全部结构公理；
   - 证明了构造网络的每条路径是原路径的染色提升（[`network_path_labels`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L244-L247)），原路径长度不变且投影复原（[`network_path_projection`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L251-L254)）；
   - 证明了构造网络严格符合加细关系 [`network_refinement`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L449-L494)；
   - 证明了加细后网络的全局外延算子与原网络全局严格相等（[`network_extensional_eq`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L258-L267)）。
3. **求值步数与深度不变性**：
   - 证明了加细后每个输入的求值轨迹节点数与原网络严格相同（[`colour_path_length`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean#L162-L166)），因此原求值深度界在加细网络中依然有效且紧致不变（$r' = r \le \ell(\mathcal{N})$）。

#### 2. 需要补充的内容（若在更广泛理论语境下考察）

虽然对于审阅范围（节点域加细定义及其外延等价保持）的数学内容而言，源码已做到了严格证明与自洽闭环，但若将其置于整章后续理论发展中，以下外延性质属于源码中未直接定理化、需要作为后续模块补充的内容：

1. **多步加细链的传递闭包与不可约代表存在性**：
   - 源码在 [`network_refinement.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L498-L515) 中定义了允许加细规则 [`RefinementRule`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L498)、不可约性 [`Irreducible`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L502) 以及选定不可约代表结构 [`IrreducibleRepresentative`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean#L509-L515)；
   - 但数学正文提到的“从反复加细得到不可约代表还需要终止证书；三类常用的充分条件见 @h-2498621c42325300”，以及有限次节点域加细可达关系的多步复合传递定理，尚未在此处构建多步归纳闭包。
2. **DAG 拓扑秩的显式提升**：
   - 源码将节点域加细建立在统一深度界网络 [`FiniteOperatorNetwork`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L42-L61) 之上（允许包含有向环，只要轨迹有限终止）；
   - 若特化到带有拓扑秩字段 `rank` 的无环算子网络 [`OperatorNetwork`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR03-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L253-L277)，虽然节点域加细不增加跨节点的逆向边从而数学上保持无环性，但源码尚未显式构造拓扑秩提升函数 `rank' (v' : V') := rank (projection v')` 并证明其严格降秩性质。
3. **与局域退化数据（Lipschitz / co-Lipschitz / 零化半径）的协同传递**：
   - 数学正文指出加细规则族 $R$ 可指定节点域加细在 $L/K/N$ 受限数据上的比较条件。这部分矩阵指标（利用域缩小单调性）的直接绑定留给了专门的算子局部退化章节，未内嵌在纯拓扑路由的 `NodeDomainRefinement` 中。

---

### 三、审阅小结

综上所述，所给 Lean 实现不存在数学遗漏或语义偏差：
- 节点域分划、子节点算子限制、入边/出边/自环边域的统一交集刻画、可达性剪枝及终止域逻辑，均被严格形式化；
- 在关系规范与构造实现两个层面上，均完整证明了节点域加细保持外延算子在 $U$ 上等价（以及全局相等）；
- 核心结论与数学正文对应严密，已证明内容构成了完整的形式化闭环。
