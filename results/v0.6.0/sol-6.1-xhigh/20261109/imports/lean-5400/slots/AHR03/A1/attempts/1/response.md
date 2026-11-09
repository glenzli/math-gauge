**结论：就本题限定的“节点域加细”及其“保持外延等价”而言，所给实现准确、完整，没有发现实质性的数学缺口。**这一判断需要同时考察加细关系、具体构造及删除冗余节点的实现。

我使用附件指定的 Lean 4.29.1 重编译了 `domain_refinement_construction.lean` 及其 23 个附件依赖模块，全部通过。以下逐项说明数学对应；编译结果本身不能替代这些核对。

1. **分划与局域算子的条件完整对应。**

   [NodePartitionData](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 用 `count`、`count_pos`、`piece`、`nonempty`、`disjoint`、`cover` 编码有限、非空、两两不交且覆盖原节点**完整定义域**的分划。它允许 \(q=1\)，也允许部分胞从未被入口求值访问，均符合正文。

   `local_domain` 要求子算子的定义域恰好是对应胞；`local_eq` 要求胞上逐点相等。`local_op_eq_restrict` 进一步证明子算子就是原节点算子的限制：胞内取值相同，胞外因不属于定义域而只能取 \(\bot\)。这里的 `LocalEquivalent` 是函数值相等，不是伪度量零距。

2. **节点替换、入口细分与节点身份均得到约束。**

   `source` 把新节点标为“未替换的旧节点”或“某个分划胞”，其单射性排除了重复复制；`old_node_present` 保证所有其他旧节点保留；`piece_node_present_iff_reached` 精确规定哪些子节点在删除后存在。

   入口条件也不只是保持入口投影。[entry_domain_eq](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:283) 已证明
   \[
   U_v^{\mathrm{in}\prime}
   =U_{\pi(v)}^{\mathrm{in}}\cap U'_v.
   \]
   因此，子节点入口片正是正文要求的交集；其他旧节点的入口片保持原样。空片仍可用空集合编码，入口节点集合由非空入口片识别即可。

3. **完整边域公式覆盖了全部四种情况，包括未使用边与自环。**

   正式关系 `NodeDomainRefinement.edge_domain_eq` 要求，对每对保留节点，
   \[
   D'_{v\to w}
   =D_{\pi(v)\to\pi(w)}\cap f'_v(U'_v)\cap U'_w.
   \]
   [network_edge_domain_eq](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:346) 已为具体构造证明这一公式。

   利用原边域包含源输出像与目标定义域，它分别化为：

   | 边的类型 | 得到的边域 |
   |---|---|
   | 其他旧节点之间 | 原边域不变 |
   | 旧节点进入子节点 \(a\) | \(D_{\gamma\to\beta}\cap U_{\beta,a}\) |
   | 子节点 \(a\) 离开至旧节点 | \(D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})\) |
   | 原自环细分为 \(a\to b\) | \(D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}\) |

   这些等式施加于**完整局域输出像**，没有把未被入口轨迹使用的边擅自删掉。空边域通过“边当且仅当边域非空”的既有定义省略。

   辅助结构 `OperationalNodeDomainRefinement` 单独不足以表达上述全部结构要求；附件明确区分了它与正式关系，并由正式关系增加完整边域约束。这不是实际实现的遗漏。

4. **重复经过节点时，确实按每次的当前输入选择胞。**

   `colour_path` 在处理下一位置时，先更新当前点值，再选择对应标签；`colour_path_get` 精确表明，第 \(n\) 位使用原路径前 \(n\) 步求值所得的当前输入。

   因而它没有把一次初始选胞固定用于该节点的所有后续发生。同一节点回访、原自环转入不同子节点等情形都已覆盖。

   `coloured_terminal` 证明重标记后的路径仍是合法的**终止路径**；`coloured_eval` 证明终止输出相同；`colour_path_length` 证明长度不变。因此 `presentation` 从原网络与分划数据实际构造出了统一有限终止的数据，没有额外假设加细结果已经满足终止性。

5. **冗余节点删除符合正文，而且正确处理了终止域变化。**

   构造明确取 `network := presentation.prune`。[prune](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:111) 保留实际路径经过的标签及其完整局域算子，删除其余标签和关联边。

   `old_label_reached` 证明其他旧节点全部保留；`piece_label_reached_iff` 证明子节点保留恰好等价于原轨迹某次以该胞内的点进入目标节点。`prune_path_labels`、`prune_eval` 则保证实际路径与输出保持。

   这里须区分删除前后：正文中的
   \[
   T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta
   \]
   是**删除冗余节点前**的公式。删除指向不可达子节点的边后，保留节点在某些未使用输出处的终止域可能扩大。源码的 `prune_choice` 正确允许这种变化；实际发生的后继不会被删去。因此，只在实际输出上要求 `choice_projection` 是合理的，并未削弱保留边域的完整交集要求。

6. **外延保持既有一般证明，也有具体构造证明。**

   一般关系的证明链为：
   `node_eval_eq` → `terminal_projection` → `path_projection`，并结合 `eval_projected` 得到 `NetworkRefinement.path_eval_eq`，最后由 [refinement_preserves_local_equivalence](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:453) 得到正文要求的
   \[
   \phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}.
   \]
   完整路径对应和最终输出相等都是推导结果，没有被存成加细关系的前提。

   更关键的是，`NodePartitionData.network_refinement` 已证明实际构造满足正式关系；[network_extensional_eq](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:258) 还直接证明了更强的全域算子等式：
   \[
   \phi_{\mathcal N'}=\phi_{\mathcal N}.
   \]
   域内由逐步求值一致得到，域外双方均补为 \(\bot\)。`refinement_preserves_representation` 另已证明原网络表示的算子在加细后仍被表示。

本范围没有需要修复的数学问题。需区别于直接声明的是：源码没有单列“求值深度完全相等”或“删除前终止域交集公式”的命名定理。前者可由已证明的逐输入路径长度相等推出；后者可由删除前的选择规则、分划覆盖及终止域定义推出。若希望把它们直接作为 Lean 接口使用，可以补充这些引理；所请求的构造合法性与外延保持结论已经证明。

原文与实现归 Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[ORCID](https://orcid.org/0009-0006-6536-3453)，[源码库](https://gitlab.com/glenzli/oet-public)，许可为 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。本审阅仅针对所附历史版本，未修改附件。