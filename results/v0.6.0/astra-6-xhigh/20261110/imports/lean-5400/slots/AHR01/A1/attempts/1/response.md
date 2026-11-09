**结论：外延保持的实质结论已有正确的构造性证明，但 `NodeDomainRefinement` 并未精确表达正文的节点域加细。** 它允许修改未被实际求值使用的边域，范围严格大于正文规定的操作。因此，不能将“定义与实现已完整对应”作为整体评价；也不能说附件只假设了加细结果、没有实现构造。

以下仅审阅节点域加细。反例针对形式化关系的准确性，不反驳正文的外延保持命题。

1. **分划、局域算子与入口的对应是正确的。**

   [NodePartitionData](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 和 `NodeDomainRefinement` 都记录了：

   | 正文要求 | Lean 对应 |
   |---|---|
   | 有限非空分划 | 正整数 `count`／`part_count`，以 `Fin` 编号 |
   | 各片非空、两两不交、覆盖完整节点定义域 | `nonempty`、`disjoint`、`cover` 等字段 |
   | 子算子定义域恰为分片 | `local_domain` |
   | 子域上逐点等于原算子 | `local_eq`／`local_equiv` |

   这里分划的是完整 `node_dom target`，不是实际输入域；与正文一致。局部等价也是函数值相等，而非伪度量零距。

   `local_op_eq_restrict` 已证明子算子就是原算子的限制：片内由局部等价确定，片外由定义域等式强制取 `bot`。

   具体构造的入口由 `lift_label` 按当前输入选择分片，得到正文要求的入口交集。抽象关系虽然只写 `entry_projection`，但结合 `entry_mem`、分片互斥和 `source_injective`，也能推出准确的入口片公式；这里不存在同样的欠约束。

2. **具体构造正确处理边域、自环、重复访问和剪枝，并已证明外延相等。**

   [NodePartitionData.choice](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:111) 在完整节点输出像上继承原选择，再按输出点选择目标分片。设剪枝前网络为 \(\widehat N\)，标签投影为 \(\pi\)。展开定义可得统一边域公式
   \[
   \widehat D_{\eta\to\xi}
   =
   D_{\pi(\eta)\to\pi(\xi)}
   \cap\widehat f_\eta(\widehat U_\eta)
   \cap\widehat U_\xi .
   \]
   它分别给出正文的入边、出边、自环公式，以及不关联原目标节点的边保持不变。

   尤其是 `self_loop_choice_iff` 已明确证明：在源子节点输出像内，进入目标子节点，当且仅当输出属于原自环边域且属于目标分片。因此它确实包含自环所需的两重限制。

   `colour_path` 每次访问目标节点时，都根据**该次当前输入**重新选片；不会把原节点的所有发生固定分配给同一个子节点。源码随后证明：

   - `coloured_terminal`：染色后的路径合法且终止；
   - `coloured_eval`：终止输出相等；
   - `colour_path_length`：路径长度不变；
   - `presentation`：构造有限节点、合法入口与转移、统一终止界等全部数据，仅暂缺无冗余条件。

   [FiniteNetworkPresentation.prune](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:76) 再删除未经过的节点及其关联边，保留其余节点的完整局域算子。它并非把所有节点限制到实际输入域。`prune_path_labels`、`prune_eval` 和 `prune_extensional_operator_eq` 已证明剪枝保持路径与输出。

   最终，[network_extensional_eq](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:258) 已证明
   \[
   \phi_{P.\mathrm{network}}=\phi_N,
   \]
   比正文仅写在 \(U\) 上局部等价更强。该构造适用于任意所给合法有限分划，允许原网络有自环和节点回访。

3. **实质偏差在抽象关系的 `choice_projection`：它只约束实际输出。**

   [该字段](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:108) 的前提是
   \[
   z\in f'_v(U_v^{\mathrm{eff},N'}),
   \]
   而不是完整的 \(f'_v(U'_v)\)。

   因而，在节点完整输出像内、但从网络输入域从未实际产生的点上，关系允许额外增删或改变路由。正文则规定完整边域的交集公式；剪枝只允许删除不可达节点及其关联边，不能任意修改两个保留节点之间的边。

   一个四点反例即可验证这种差别。取
   \[
   X=\{\bot,a,b,c\},\qquad U=\{a,b\}.
   \]
   原网络只有节点 \(\beta\)，局域算子为恒等算子，定义域为 \(\{a,b,c\}\)，入口片为 \(U\)，没有边。两个输入都一步终止。

   分划为
   \[
   C_0=\{a,c\},\qquad C_1=\{b\},
   \]
   子算子分别取恒等算子在两片上的限制。令新网入口为 \(a\mapsto\beta_0\)、\(b\mapsto\beta_1\)，并额外添加自环
   \[
   D'_{\beta_0\to\beta_0}=\{c\},
   \]
   其余输出均停止。

   逐项核对如下：

   - 两个子节点都被入口输入访问，无节点需要删除。
   - 自环合法：\(c\) 同时属于源输出像和目标定义域。
   - 输入 \(a,b\) 仍各自一步终止，统一长度界为 \(1\)。
   - 实际输入域分别为 \(\{a\}\)、\(\{b\}\)，实际输出也分别为这两个集合；这些输出上的选择均为 `stop`，满足 `choice_projection`。
   - 标签取 `source β₀ = inr 0`、`source β₁ = inr 1`，其余分划、算子、入口及分片可达性字段全部满足。

   所以它满足现有 `NodeDomainRefinement`。但正文要求
   \[
   D'_{\beta_0\to\beta_0}
   =D_{\beta\to\beta}\cap f_{\beta,0}(C_0)\cap C_0
   =\varnothing,
   \]
   与实际的 \(\{c\}\) 矛盾。相应终止域也从正文要求的 \(\{a,c\}\) 变成了 \(\{a\}\)。

   这不是输出像之外的无关总化：从合法但入口不可达的状态 \((\beta_0,c)\) 出发，新转移图会循环，而原图一步终止。有限网络只要求入口输入统一终止，因此反例仍是合法有限网络。若需规范空间背景，可取正常异点距离为 \(1\)、正常点到 \(\bot\) 距离为 \(+\infty\) 的单分量扩展度量。

4. **这一偏差不使已有外延保持证明失效。**

   抽象关系的证明链确实推导了结论：
   \[
   \texttt{node\_eval\_eq}
   \longrightarrow
   \texttt{terminal\_projection}
   \longrightarrow
   \texttt{path\_projection}
   \longrightarrow
   \texttt{path\_eval\_eq}.
   \]
   其中路径对应通过 `terminal_path_unique` 得到，并未作为完整轨迹等式预先假设。

   [refinement_preserves_local_equivalence](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:377) 因而正确证明现有关系下的局部等价；同域及域外统一取 `bot` 又足以推出全域算子相等。反例中的两网也确实外延相同。

   数学影响是：**该关系足以保证外延，却不能保证网络数据正是正文指定的加细结果。** 附件的 `PresentationData` 保留完整边域，因此上述差别也不会被网络对象的数据相等关系忽略。

5. **需要补充的是规格约束与接口对应，而非重做外延证明。**

   建议对所有保留的新节点 \(v,w\) 加入完整边域条件
   \[
   D^{N'}_{v\to w}
   =
   D^N_{\pi(v)\to\pi(w)}
   \cap f^{N'}_v(U^{N'}_v)
   \cap U^{N'}_w .
   \]
   它统一覆盖正文各类边域，并适用于剪枝后的保留节点对。

   不能简单把现有 `choice_projection` 的前提扩大到整个 `node_image`：合法剪枝可能删除一个目标子节点，使某些未实际使用输出上的 `next` 变成 `stop`。完整的保留边域公式能准确表达这种情况。

   附件还没有提供以下接口对应定理：

   - 从 `NodePartitionData` 的具体构造得到 `NodeDomainRefinement N P.network`；目前构造与抽象关系各有独立证明。
   - 对加强后的关系，证明它与正文构造所得完整数据相符，至多差相应标签重命名。

   可配套补充入口公式、统一边域公式，以及剪枝前的终止域交集公式。这些是具体构造可由现有定义推导的性质；自环对应已有显式引理。须注意，剪枝后终止域可能扩大，不能无条件沿用剪枝前的终止域等式。

本次进行了源码审阅及上述有限反例的枚举核对，未另行运行 Lean 编译，也未修改附件或新增 Lean 源码。

审阅对象为 Zhe Li（Glen Li / glenzli）的 [The Operator Evolution Theory](https://glenzli.com/books/oet/) 附件版本，许可为 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。