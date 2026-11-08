结论：**就正文所述的一次节点域加细而言，所给 Lean 实现准确覆盖了数学范围**，包括节点重复经过、自环、未被入口求值使用的边，以及加细后删除不可达子节点的情形。具体构造已经证明外延算子相等；对一般的加细关系，源码证明了正文所要求的公共输入域上的局部等价。

需要区分的是：源码没有单独封装“任意满足关系的结果与规范构造按节点重命名同构”这一双向刻画，也没有把一般关系下的局部等价另写成全域算子相等定理。这些是可补充的接口与刻画，不影响下面说明的数学覆盖。

逐项对应如下。

1. **分划与局域算子。** [NodePartitionData](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 用正整数 `count`、非空且两两不交的 `piece`、以及并集等于原节点域，表达正文的有限非空分划；`local_domain` 和 `local_eq` 分别表达子节点的定义域和局部等价。`local_op_eq_restrict` 进一步证明这些条件决定的就是原算子的域限制：域内相同，域外均为吸收元。

2. **入口、普通边与自环。** 加细节点标签由未受影响的旧标签和分块标签组成。`lift_label` 根据**当前输入**选择分块，故同一轨迹多次经过原节点时可以选到不同子节点。一般关系的 `entry_domain_eq` 推出入口片正是原入口片与新节点域的交；[network_edge_domain_eq](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:346) 对每对保留节点给出
   \[
   D'_{v\to w}
   =D_{\pi(v)\to\pi(w)}\cap f'_v(U'_v)\cap U'_w.
   \]
   对普通入边、出边，由原边域的包含关系可化为正文各自的公式；对自环，两次交集同时保留，正是正文的双重细分公式。这个等式作用于完整局域输出像，因而也约束未被入口轨迹使用、但两端均保留的边。

3. **删除不可达子节点。** 构造先建立包含全部分块的 `presentation`，再调用 `prune`。[piece_label_reached_iff](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:310) 证明子节点恰在原轨迹的某次节点发生进入该分块时保留；`old_label_reached` 证明其他旧节点仍保留。删除与所删节点关联的边后，某个保留节点在**未实际到达的输出**上的终止域可能扩大，这是正文删点操作允许的结果。源码因而只要求实际到达输出上的路由投影保持，同时要求保留节点之间的完整边域满足交集公式。

4. **终止、路径和外延。** `coloured_terminal` 按每次发生的当前输入给原路径重新标记，证明构造出的路径仍合法终止；路径长度不变，原统一长度界仍可使用。`network_path_projection` 证明删点后的路径投影恰为原路径；[network_extensional_eq](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:258) 直接证明具体构造的**全域外延算子相等**，包括输入域外均取吸收元。

5. **一般关系及正文结论。** [NodeDomainRefinement](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:118) 除上述分划、算子和完整边域条件外，还记录保留标签、入口投影和实际路由投影。源码证明具体构造满足该关系；对任意持有该关系的两网，`path_projection` 和 `eval_projected` 进而支持 [refinement_preserves_local_equivalence](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:453)，得到正文的 \(\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}\)。

关于尚未单独证明的关系刻画，可以按以下方式复核：关系中的标签单射、全部未替换节点存在、以及“分块标签存在当且仅当该分块被原轨迹到达”，确定了结果节点与规范构造保留节点之间的双射；局域算子兼容、入口交集公式和完整边域交集公式随后确定相同的网络数据。因此，按一次加细的结构数据理解，该关系没有遗漏正文允许的分划，也没有仅凭实际路径相等而放任其他保留边变化。若要让 Lean 用户直接调用这一结论，可补充相应的节点重命名同构定理。一般关系下的全域算子相等也可由已证明的输入域相等、域上局部等价及域外取 \(\bot\) 补充得到。

我使用附件指定的 Lean 4.29.1 环境，从源码重新检查了 `domain_refinement_construction.lean` 及其 23 个本地依赖，均通过；没有修改附件。

数学正文来源：Zhe Li（Glen Li／glenzli），[*The Operator Evolution Theory*](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。