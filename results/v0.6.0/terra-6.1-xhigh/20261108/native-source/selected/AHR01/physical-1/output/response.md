**结论：外延保持的核心结论已有证明，但“节点域加细”的关系定义没有准确刻画正文要求的全部网络数据，因此不能认为实现已完整、精确地覆盖该数学范围。** 具体构造采用了正文的分划和重新路由方式，并直接证明其输出网络与原网络的外延算子相等；另一个抽象关系 `NodeDomainRefinement` 则允许在未被实际求值访问的输出上改变边域，范围比正文的加细更宽。源码还没有把这两种表述连接起来。

以下只讨论节点域加细及其外延保持结论。

1. **分划与局域算子对应正确。**  
   [domain_refinement_construction.lean](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 的 `NodePartitionData` 用正整数 `count`、非空且两两不交的 `piece`、覆盖等式，以及 `local_domain`、`local_eq`，表达正文要求的有限非空分划和局部一致性。`local_op_eq_restrict` 已证明每个子节点算子就是原算子在该分块上的限制：分块内相等，分块外二者都取吸收元。

2. **具体构造的路由机制与正文一致，但边域公式的完整对应尚未逐项证明。**  
   对输出 \(z\)，构造先读取原节点的后继选择；若后继是被拆节点，就用 `piece_at z` 选择包含 \(z\) 的唯一分块。于是，在删点之前，按定义展开应得到正文的入口、入边、出边和自环交集公式。例如自环应满足
   \[
   D'_{\beta_a\to\beta_b}
   =D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})
     \cap U_{\beta,b}.
   \]
   源码中的 `self_loop_choice_iff` 已证明这一公式的路由核心：对属于源子节点输出像的 \(z\)，选择 \(\beta_b\) 当且仅当 \(z\) 属于原自环域及目标分块。

   不过，附件中没有找到覆盖**所有入口片、各类边域和终止域**的完整等式定理。尤其应区分删点前后：删去不可达子节点及其关联边后，保留节点上原来指向被删节点、但从入口永不实际使用的输出会变成终止输出。因此，删点前的终止域公式不能不加说明地直接用于删点后的网络。

3. **具体构造已经证明外延保持。**  
   `colour_path` 对原轨迹中每次出现的目标节点，按该次实际输入选择分块；同一节点回访时可以选择不同子节点。`coloured_terminal` 和 `coloured_eval` 分别证明重新标记后的轨迹仍终止、求值不变。构造先生成有限网络表示，再删除不可达节点。

   最终的 `network_path_projection` 已证明每个输入的新路径投影回原路径；`network_extensional_eq` 已证明
   \[
   \phi_{P.\mathrm{network}}=\phi_{\mathcal N}
   \]
   作为完整算子相等。这比正文在共同输入域 \(U\) 上的局部等价更强，也包括 \(U\) 外双方都取 \(\bot\) 的情形。该证明适用于附件中 `NodePartitionData` 所描述的任意目标节点和合法分划，包括自环与重复访问。

4. **抽象加细关系过宽：有具体反例。**  
   [network_refinement.lean](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:73) 中，`choice_projection` 只约束新节点的**实际输入域所产生的输出**。正文的交集公式则规定整个节点输出像上的边域，包括从入口未曾到达的输出。

   取四个互异点 \(X=\{\bot,a,b,c\}\)，原网络有节点 \(t,s\)，输入域 \(U=\{a\}\)，入口为 \(t\)：

   - \(t\) 是恒等算子在 \(\{a,b,c\}\) 上的限制；\(s\) 是恒等算子在 \(\{a,b\}\) 上的限制。
   - 原网络唯一边为 \(t\to s\)，边域 \(\{a\}\)；其余输出终止。输入 \(a\) 的路径为 \(t,s\)，两个节点均可达。
   - 将 \(t\) 分为 \(\{a,b\}\) 和 \(\{c\}\)，并删去不曾到达的 \(\{c\}\) 子节点。保留子节点记为 \(t'\)。
   - 令另一个候选网络与上述结果相同，但把 \(t'\to s\) 的边域改为 \(\{a,b\}\)。

   这个候选网络仍是有限算子网络，实际路径仍只有 \(a:t'\to s\)。它满足 `NodeDomainRefinement`：分划、局域算子、节点对应和保留条件均成立；实际输出只有 \(a\)，所以 `choice_projection` 也成立。然而正文公式要求
   \[
   D'_{t'\to s}
   =D_{t\to s}\cap f_{t'}(\{a,b\})
   =\{a\},
   \]
   而候选网络的边域为 \(\{a,b\}\)。两个网络的外延仍相同，但它多了一条在 \(b\) 上的转移，并改变了表示层数据。因此，抽象关系证明的外延保持是有效的较宽结论，不能把它的前提直接解释为“恰好由正文的节点域加细得到”。

5. **两个已证明结论与缺失桥接应分开看。**  
   对任意满足抽象 `NetworkRefinement` 的网络对，`refinement_preserves_local_equivalence` 已证明共同输入域上的逐点相等；`refinement_preserves_representation` 已证明表示关系保持。其节点域分支通过路径投影与逐步求值证明，不能从上面的反例推出该结论有误。

   但在所给源码中，没有找到定理证明：任意 `NodePartitionData` 构造并剪枝所得的 `P.network`，满足 `NodeDomainRefinement N P.network`；也没有找到把正文各项交集公式与该关系证明为等价的桥接。具体构造的外延定理独立成立，但抽象关系的名称和字段本身不足以证明它精确实现了正文定义。

修复方向是：以**删点前的网络数据**或其逐项入口片、边域等式定义正文的加细，再明确应用不可达节点删除；随后证明该构造满足精确定义，并推出现有的外延保持定理。若希望保留目前较宽的 `NodeDomainRefinement`，宜把它表述为“实际轨迹保持”的关系，并另证正文加细蕴含该关系，而不将两者等同。

本次结论依据附件正文与源码审阅；未在此重新编译 Lean 工程，也未修改附件。

资料来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[ORCID](https://orcid.org/0009-0006-6536-3453)，[公开源码](https://gitlab.com/glenzli/oet-public)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。