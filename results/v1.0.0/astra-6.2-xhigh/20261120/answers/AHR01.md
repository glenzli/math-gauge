**具体构造符合正文，节点域加细保持外延等价的结论已经证明。覆盖不完整之处在于 `NodeDomainRefinement`：用它判断两个给定网络之间是否构成正文所说的一步加细，会接受额外的网络。** 原因是正文规定了完整局域输出像上的边域，而该关系只检查实际轨迹产生的输出。两份目标文件均已用 Lean 4.29.1 编译通过。

### 具体构造与正文的逐项对应

1. **分划与局域算子。** `NodePartitionData` 用 `Fin count`、`count_pos`、`nonempty`、`disjoint` 和 `cover` 表示整个节点域 \(U_\beta\) 的有限非空分划。`local_domain` 给出每个子算子的精确定义域，`local_eq` 给出片内逐点相等。片外的值由定义域条件强制为 \(\bot\)，源码据此证明了全算子等式 `local_op_eq_restrict`。`mem_piece_at` 和 `piece_at_unique` 保证每次进入 \(\beta\) 时都由**当次输入**唯一选片。 [分划与限制算子](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12)

2. **入口、边域与终止域。** 记 \(A_a=U_{\beta,a}\)、\(Y_a=f_{\beta,a}(A_a)\)。删点前，`presentation.entry` 按初始输入提升旧入口，故子节点入口片恰为 \(U_\beta^{\mathrm{in}}\cap A_a\)，其余入口片照旧。`choice` 在当前输出 \(z\) 上查询旧后继，若后继是 \(\beta\)，就按 \(z\) 选目标片。结合 `edge_domain` 本身要求 \(z\) 属于源节点的完整输出像，可以逐项得到
   \[
   \begin{aligned}
   D'_{\gamma\to\beta_a}&=D_{\gamma\to\beta}\cap A_a,\\
   D'_{\beta_a\to\gamma}&=D_{\beta\to\gamma}\cap Y_a,\\
   D'_{\beta_a\to\beta_b}&=D_{\beta\to\beta}\cap Y_a\cap A_b .
   \end{aligned}
   \]
   前两式中 \(\gamma\ne\beta\)。两端均为未拆节点时，边域就是旧边域。空集不产生入口或边；在 \(Y_a\) 内对全部出边域取补，得到删点前的 \(T'_{\beta_a}=Y_a\cap T_\beta\)。这些是从定义可推出的集合等式。源码显式证明的 `self_loop_choice_iff` 是第三式在前提 \(z\in Y_a\) 下的逐点路由等价。 [构造中的后继选择](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:111) · [网络边域的定义](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean:218)

3. **轨迹、删点与外延。** `colour_path` 每走一步就更新当前点，因此同一条路径多次访问 \(\beta\) 时可以进入不同子片。`coloured_terminal`、`coloured_eval` 和 `colour_path_length` 分别证明新路径合法终止、终止值相等、长度相等，原统一长度界仍适用。随后 `prune` 只保留实际路径经过的标签，保留两端都留下的边，把指向已删节点的选择改为 `stop`。因此删点后完整终止域可能扩大，实际轨迹和输出则由 `prune_path_labels`、`prune_eval` 保证。最终的 `network_path_projection` 恢复每个输入的旧路径，`network_extensional_eq` 直接证明构造所得网络与旧网络在**整个 \(X\)** 上的外延算子相等，域外两侧均取 \(\bot\)。 [路径与外延证明](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:167) · [删点实现](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:71)

### 抽象关系的缺口与反例

`NodeDomainRefinement` 正确约束了标签和算子。`source_injective`、`old_node_present`、`piece_node_present_iff_reached` 要求每个未拆节点恰有一个副本，子片恰在某次旧轨迹以该片中的点进入目标节点时保留。`same_input_domain`、`entry_projection` 加上入口必须落入节点域和分划互斥性，也足以确定入口片。缺口在 `choice_projection` 的量词。它只对
\[
z\in f'_v\bigl(U_v^{\prime\,\mathrm{eff}}\bigr)
\]
要求新旧选择投影相符。一个点可以属于完整局域输出像 \(f'_v(U'_v)\)，却从未由入口轨迹在 \(v\) 产生。即使一条边的两端都保留，该字段也可能允许删掉这条边。 [抽象关系的字段](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:73)

**反例。** 取 \(X=\{\bot,a,b,c\}\)，原网络只有入口节点 \(\beta\)，入口片为 \(U=\{a,b\}\)。令
\[
f_\beta(a)=f_\beta(b)=a,\qquad f_\beta(c)=b,\qquad f_\beta(\bot)=\bot,
\]
并设唯一边为自环，边域 \(D_{\beta\to\beta}=\{b\}\)。这条边合法，因为 \(f_\beta(c)=b\) 且 \(b\in U_\beta\)。两个入口输入都输出 \(a\)，均一步终止。

将 \(U_\beta\) 分为 \(A=\{a,c\}\) 和 \(B=\{b\}\)，取对应限制算子。两个子节点分别由入口输入 \(a,b\) 访问，均须保留。正文要求
\[
D'_{A\to B}=\{b\}\cap f_\beta(A)\cap B=\{b\}.
\]
现在取一个候选网络，使用上述子节点、算子和入口片，令两个节点一律 `stop`。它满足抽象关系的各字段，尤其两个节点实际产生的输出都只有 \(a\)，旧网络在 \(a\) 上也选择 `stop`。但候选网络的 \(D'_{A\to B}=\varnothing\)，节点 \(A\) 的终止域也由应有的 \(\{a\}\) 变成了 \(\{a,b\}\)。两端都可达，正文的删点规则无法删去这条边。这个反例中，外延等价确实成立，失真发生在加细所要求的网络数据上。

### 已证结论与修复方向

对给定的抽象见证，`terminal_projection` 使用实际输出上的路由相容性，`path_projection` 再用确定性得到旧路径，`eval_projected` 用逐步算子相等得到相同终值。因此 `refinement_preserves_local_equivalence` 的节点域分支有效，`refinement_preserves_representation` 也成立。路径相等和外延相等都是推出来的。对于规范构造，前述 `network_extensional_eq` 已经独立证明了更强的全域等式。 [抽象路径证明](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:195) · [外延保持定理](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:377)

要使抽象关系精确刻画正文，可以保留现有标签、分划和入口字段，并对**每对保留节点** \(v,w\) 要求完整边域等式
\[
D'_{v\to w}
=D_{\pi(v)\to\pi(w)}\cap f'_v(U'_v)\cap U'_w .
\]
这同时覆盖入边、出边、自环和未关联边。对已删目标，关联边随之删除，其原边域中的输出可转为终止。直接把现有 `choice_projection` 的量词扩大到完整输出像，会错误排除这种合法删点。

附件还缺少连接两种实现的定理。可先证明具体构造中“子标签被 `Reached` 保留”等价于原网络上的 `NodePieceReached`，再证明 `P.network` 满足上述精确关系。若要得到双向刻画，还可证明任一满足该关系的候选网络经相应标签重命名后，与规范构造具有相同的 `presentation_data`。

正文来源为 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*，以上判断针对所附版本。 [正文定义](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR01/physical-1/work/source.md:1048) · [作品主页](https://glenzli.com/books/oet/) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)