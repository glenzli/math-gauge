**结论：就附件中的“节点域加细”定义及其外延保持命题而言，所给实现准确、完整地覆盖了该数学范围，未发现实质性缺口。** 这一判断需要合看加细关系、实际构造和删冗余节点三个部分；其中较弱的 `OperationalNodeDomainRefinement` 单独并不等于正文定义。

1. **分划与子节点算子准确对应。**

   [NodePartitionData](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 用 `count_pos`、`nonempty`、`disjoint`、`cover` 表达有限非空分划，覆盖的是原节点的**完整定义域**。

   `local_domain` 要求子算子定义域恰等于分块；`local_eq` 要求块内逐点相等。`local_op_eq_restrict` 进一步证明子算子就是原算子的限制：块内相同，块外均为吸收元。这与正文一致，也没有误将逐点相等弱化成规范零距。

2. **节点身份、入口片与删除条件得到完整表达。**

   构造采用标签
   \[
   (V\setminus\{\beta\})\sqcup\operatorname{Fin}(q),
   \]
   区分原有节点和各子节点。关系中的 `source_injective` 排除额外复制，`old_node_present` 保留所有未替换节点。

   [entry_domain_eq](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:283) 已证明
   \[
   U_v^{\mathrm{in}\prime}
   =U_{\pi(v)}^{\mathrm{in}}\cap U'_v.
   \]
   对子节点，这正是正文的入口交集；对原有节点，由原入口片包含于节点域，恢复原入口片。空入口片作为空集表示，不产生入口输入。

   `piece_node_present_iff_reached` 判断子节点是否保留，依据的是原轨迹中**任意一次发生的当前输入**，而非只看初始输入。因此也覆盖从其他节点进入、经过回边后再次进入等情形。

3. **全部边域公式均被约束，包括未实际使用的边和自环。**

   正式关系 [NodeDomainRefinement](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:118) 增加了完整边域等式：
   \[
   D'_{v\to w}
   =D_{\pi(v)\to\pi(w)}
     \cap f'_v(U'_v)\cap U'_w.
   \]
   利用原边域包含于源输出像和目标定义域，可逐项化为：

   | 保留节点之间的边 | 等式化简结果 |
   |---|---|
   | 原节点 \(\gamma\to\delta\) | \(D_{\gamma\to\delta}\) |
   | 入边 \(\gamma\to\beta_a\) | \(D_{\gamma\to\beta}\cap U_{\beta,a}\) |
   | 出边 \(\beta_a\to\gamma\) | \(D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})\) |
   | 自环拆分 \(\beta_a\to\beta_b\) | \(D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}\) |

   这里 \(\gamma,\delta\ne\beta\)。等式适用于完整局域像中的所有点，没有“必须实际经过”的限制；原本不存在的边也不能凭空出现。空边域通过“边当且仅当边域非空”的表示约定省略。

   [network_edge_domain_eq](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:346) 已证明实际构造满足该等式。因而不能仅因辅助关系中的 `choice_projection` 只管实际输出，就判定正式实现遗漏未使用边。

4. **从分划数据到合法有限网络的构造已经完成。**

   [colour_path 与 presentation](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:167) 实现了正文证明中的逐次替换。

   对原轨迹的发生 \((\gamma_s,y_s)\)，若 \(\gamma_s=\beta\)，就按当前的 \(y_s\) 唯一选择分块。每一步满足
   \[
   f'_{\gamma'_s}(y_s)=f_{\gamma_s}(y_s)=y_{s+1}.
   \]
   `coloured_terminal` 证明所得序列确为终止路径，`colour_path_length` 证明长度不变，`coloured_eval` 证明输出相同。随后 `presentation` 构造有限节点、合法入口、合法后继和统一终止界。

   因此，实现没有把“加细结果已是合法网络”作为唯一入口而略去存在性证明。它使用 `FiniteOperatorNetwork`，不要求无环，也不要求路径中节点互异。

5. **删冗余节点与终止域的处理符合正文。**

   [prune](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:105) 仅保留实际路径出现的标签，保留其完整局域算子，并删除指向被删标签的转移。`prune_choice_next_iff` 保证存活节点之间的完整边域保持；`prune_path_labels`、`prune_eval` 和 `prune_extensional_operator_eq` 分别保证路径标签、输出与外延算子保持。

   必须注意正文明确先讨论**删除前**的数据。此时
   \[
   T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta.
   \]
   删除不可达子节点后，保留节点的完整终止域可能扩大：原来指向被删节点的某些输出，现在没有后继。这与正文的删节点规则一致。这样的输出不会实际产生，否则其目标节点就会被轨迹访问，不可能被删除。

   因而，删除后的 `choice_projection` 只要求在实际输出上成立是恰当的；要求它在整个局域像上成立反而可能排除正文允许的结果。

6. **外延保持既有一般关系证明，也有构造结果的直接证明。**

   一般证明通过 `node_eval_eq`、`terminal_projection`、`path_projection`、`eval_projected` 推导路径求值相同，最后得到 [refinement_preserves_local_equivalence](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:453)。完整路径对应和最终输出相等均是证明所得，并非结构字段预先假设的结论。

   对具体构造，[network_extensional_eq](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:258) 已直接证明更强的全域算子等式
   \[
   \phi_{P.\mathrm{network}}=\phi_N.
   \]
   [network_refinement](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:449) 又证明该构造确实属于正式加细关系，并通过 `allowed_network_refinement` 接入一般定理。构造与抽象接口之间的衔接已经完成。

源码已证明上述核心内容，无须补充新的数学前提。可补充的主要是便于调用的推论封装：例如对任意节点域加细单独陈述全域算子相等、实际求值深度相等。前者由共同输入域、域内等价及域外均取吸收元得到；后者由逐输入路径投影等式取长度，再取最大值得到。附件没有为这些一般形式另设专门定理，但这不构成本题命题的覆盖缺口。

我使用配置的 Lean 4.29.1 编译了相关入口文件及其依赖，共 26 个模块，均通过；所检查的核心构造和外延保持定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。附件源码未修改。上述审阅结论仅针对所附版本的节点域情形。

原著与实现来源：Zhe Li（Glen Li / glenzli），[ORCID](https://orcid.org/0009-0006-6536-3453)，[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[公开仓库](https://gitlab.com/glenzli/oet-public)，许可为 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。