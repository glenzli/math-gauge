**结论：具体构造正确，外延保持已经证明，但 `NodeDomainRefinement` 作为两个给定网络之间的关系，严格宽于正文的“节点域加细”。** 差别在于，正文规定了保留节点之间的完整边域，Lean 的关系只检查入口轨迹实际产生的输出。这个差别会改变网络的边域和终止域，即使外延算子完全相同。 [正文定义与命题](../work/source.md#h-eddd1f2d0a9d3528)

### 定义与构造的对应

1. **分划、局域算子和入口相符。** `NodePartitionData` 和 `NodeDomainRefinement` 都用正数 \(q\) 与 `Fin q` 表示有限分划，要求各块非空、两两不交，并覆盖被拆节点的**整个定义域**。各子算子的定义域恰为对应分块，且在块上逐点等于旧算子。源码的 `local_op_eq_restrict` 进一步证明了子算子等于域限制算子，因为块外两者都取 \(\bot\)。构造按入口点所属的唯一分块选择子节点。关系里的 `entry_projection` 配合入口合法性、子节点定义域和分块互斥性，也能推出子入口片恰为 \(U_\beta^{\mathrm{in}}\cap U_{\beta,a}\)，其余入口片保持。 [分划与限制算子](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) · [关系字段](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:73)

2. **具体构造实现了完整边域和删点规则。** 记删点前的新标签投影为 \(\pi\)，节点域为 \(U_v^*\)，完整局域输出像为 \(I_v^*=f_v^*(U_v^*)\)。展开 `NodePartitionData.choice` 可得
   \[
   D^*_{v\to w}
   =D_{\pi(v)\to\pi(w)}\cap I_v^*\cap U_w^*.
   \]
   理由是新源节点的输出也是旧源节点的输出。旧选择若指向 \(\pi(w)\)，新选择就按该输出点所在的唯一目标分块决定是否进入 \(w\)。这个公式分别给出正文的入边、出边、自环双重交集以及未关联边保持。源码显式证明了自环的 `self_loop_choice_iff` 和后继域合法性，一般交集公式可由定义推出。删点前，终止域为 \(I_v^*\cap T_{\pi(v)}\)。`prune_choice` 只把指向被删节点的选择改为停止，因此保留节点之间的边域完整保留，原先流向被删节点的输出并入源节点的终止域。 [路由与自环](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:111) · [删点规则](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:35)

### 源码已经证明的外延结论

- **对具体构造**，`coloured_terminal` 按终止轨迹归纳，每次访问被拆节点时都用该次调用的当前输入选块，因此覆盖自环和重复访问。`colour_path_length` 保持每个输入的轨迹长度，原统一长度界继续适用。构造随后删除未访问的标签，`network_path_projection` 证明删点后的路径逐标签投影回原路径。`network_extensional_eq` 直接证明了全域算子相等，包含 \(U\) 内求值相同和 \(U\) 外两侧均取 \(\bot\)。 [轨迹与外延等式](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:184)
- **对给定网络的关系**，`terminal_projection` 逐步投影实际的继续或停止选择，`path_projection` 用终止路径唯一性识别原路径，`eval_projected` 再用局域算子在节点域上的一致性证明求值相同。节点域分支由此得到 `refinement_preserves_local_equivalence`，源码也证明了 `refinement_preserves_representation`。共同输入域由 `same_input_domain` 给出，因此该局部等价已经足以推出外延算子相等。 [路径投影证明](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:184) · [保持定理](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:377)

### 关系的缺口、反例与修复

`choice_projection` 只量化 \((N'.\mathrm{node\_op}\ v)(N'.\mathrm{node\_actual\_input\_domain}\ v)\)。节点可达只表示它被某条轨迹访问过，其完整输出像仍可能含有从未由入口求值产生的点。现有字段因而允许改动这些点上的路由，包括删掉两个保留节点之间的边，或改变未拆节点之间的边域。 [实际输出上的关系条件](/private/tmp/math-gauge-sol62-xhigh-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:103)

**反例。** 取 \(X=\{\bot,a,b,c,d\}\)、全局输入域 \(U=\{a\}\)。原网只有节点 \(\beta\)，其局域算子固定 \(\bot,a,b,c\)，并把 \(d\) 映到 \(c\)。自环边域取 \(\{b,c\}\)。唯一入口轨迹在 \(a\) 一步终止，故原网满足统一有限终止和无冗余节点条件。将节点域分成 \(A=\{a,b,d\}\)、\(B=\{c\}\)，子算子取相应限制。

- 按正文，删点前 \(\beta_A\to\beta_A\) 的边域为 \(\{b\}\)，\(\beta_A\to\beta_B\) 的边域为 \(\{c\}\)。只有 \(\beta_A\) 被访问。删去 \(\beta_B\) 后，\(\{b\}\) 自环仍在，\(\beta_A\) 的终止域为 \(\{a,c\}\)。
- 另取同一单节点、同一局域算子和入口、所有输出都停止的网络。它满足现有 `NodeDomainRefinement`：恰好保留被命中的块 \(A\)，唯一需要核对的实际输出 \(a\) 在两网都停止。但它删掉了正文要求保留的 \(\{b\}\) 自环，终止域变为 \(\{a,b,c\}\)。原网只有一个可拆节点，保留子算子的定义域又强制其分块为 \(A\)，所以换用其他分划见证也无法得到这个结果。

**修复方向。** 在给定网络的关系中，对每一对**保留**标签要求完整边域等于上述交集，再由补集确定终止域。直接把 `choice_projection` 的量化范围扩大到完整输出像会排除合法删点：反例中的 \(c\) 原来继续，正确删点后应当停止。还应补上构造与关系的连接定理：由 `network_path_labels` 和逐位置的当前输入证明，子标签被保留当且仅当 `NodePieceReached`，再核对入口片与完整边域。反过来，满足这些条件的给定网络在对应标签下具有与构造相同的节点算子、入口片和边域。这样即可复用现有外延证明，并精确刻画正文的加细结果。

已用 Lean 4.29.1 编译两个相关模块及其导入依赖，并核查上述关键定理的公理依赖，未发现 `sorryAx`。

审阅依据为 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory* 附件版本。 [ORCID](https://orcid.org/0009-0006-6536-3453) · [作品主页](https://glenzli.com/books/oet/) · [公开仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)