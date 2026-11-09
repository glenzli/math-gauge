结论：**节点域加细的具体构造及其外延保持证明覆盖了正文的操作；但 `NodeDomainRefinement` 关系比正文定义更宽，因而整个实现不能判为准确、完整的定义刻画。** 此外，附件尚未把具体构造连接到该关系接口。下面仅审阅节点域加细。

逐项对应如下：

| 正文要求 | 实现及判断 |
|---|---|
| 对节点的完整定义域作有限非空分划 | [`NodePartitionData`](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 的 `count_pos`、`nonempty`、`disjoint`、`cover` 准确编码这些条件。分划对象确为 `N.node_dom target`。 |
| 子算子的定义域恰为分块，并在其中与原算子相同 | `local_domain`、`local_eq` 对应准确。`local_op_eq_restrict` 进一步证明子算子全域上等于限制算子，包含域外取 `bot` 的要求。 |
| 入口片按输入所在分块细分 | 构造中的 `entry := fun x => P.lift_label (N.entry x) x.val`，结合 `piece_at_unique`，给出正文的入口片交集；其他入口片保持。 |
| 入边、出边、自环按交集公式细分 | 构造中的 `choice` 根据旧后继及**当前输出点**选择目标分块。结合边域定义，可以推出正文全部交集公式；其中自环路由另有 `self_loop_choice_iff` 的显式证明。 |
| 同一节点多次发生时，可进入不同子节点 | `colour_path` 每一步都更新当前点，再调用 `lift_label`，因此正确覆盖回访、自环以及不同次发生进入不同分块的情形。 |
| 加细数据仍满足有限网络条件 | `presentation` 实际构造有限节点族、合法入口和后继、终止路径与统一长度界。`colour_path_length` 证明长度保持，不依赖无环性。 |
| 删除不可达子节点并保持求值 | `network := P.presentation.prune`；[`prune`](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:76) 保留可达节点的完整局域算子，只删除不可达节点及关联转移，并证明路径标签和输出保持。 |
| 外延等价 | `P.network_extensional_eq` 直接证明完整外延算子相等，已经包括域外取 `bot`，强于只陈述在 \(U\) 上局部等价。 |

这里“边域公式可以推出”的具体依据是：在删冗余前，对任意新标签 \(\eta,\xi\)，记标签投影为 \(\pi\)，新局域算子的定义域、输出像为 \(U'_\eta,I'_\eta\)，构造满足
\[
D'_{\eta\to\xi}
=
D_{\pi(\eta)\to\pi(\xi)}
\cap I'_\eta\cap U'_\xi.
\]
对未分裂节点，相应交集因原边域的包含条件而冗余；对分裂源、分裂目标及两者同时分裂，分别得到正文的出边、入边、自环公式。这些一般集合等式尚未逐项封装成定理，但构造定义支持它们。

主要不足出现在关系定义的 [`choice_projection`](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:108)。它仅要求在
\[
z\in f'_v\bigl(U_v^{\mathrm{eff},N'}\bigr)
\]
时保持路由投影。正文的交集规则则规定完整局域输出像上的边域，包括从入口求值不会使用的输出。**删冗余允许删除不可达节点及关联边，不允许任意改动两个保留节点之间的未使用边域。**

下面给出一个无需删除任何节点的反例。

取
\[
X=\{\bot,a,b,c\},\qquad U=\{a,b,c\}.
\]
原网络有两个节点 \(\beta,\gamma\)，局域算子都为恒等算子，无边，入口片分别为
\[
U_\beta^{\mathrm{in}}=\{a,b\},\qquad
U_\gamma^{\mathrm{in}}=\{c\}.
\]
这是所有输入均一步终止、所有节点均可达的有限网络。

将 \(\beta\) 的定义域分成
\[
U_{\beta,1}=\{a\},\qquad U_{\beta,2}=\{b,c\},
\]
子算子取对应的恒等算子限制。候选新网络的入口分配为
\[
a\mapsto\beta_1,\quad b\mapsto\beta_2,\quad c\mapsto\gamma.
\]
再额外加入一条边
\[
D'_{\beta_2\to\gamma}=\{c\},
\]
其余输出均终止。

这个候选满足 `NodeDomainRefinement` 的所有条件：

- 分划、局域算子、标签对应及入口投影均符合字段要求；两个分块都被原轨迹使用。
- 新网络的实际节点输入域依次为 \(\{a\},\{b\},\{c\}\)，实际输出处的路由全部为 `stop`，故 `choice_projection` 成立。
- 新增边合法，因为 \(c\in f_{\beta,2}(U_{\beta,2})\cap U_\gamma\)。所有入口路径仍长为一，三个节点均可达。

但正文要求
\[
D'_{\beta_2\to\gamma}
=D_{\beta\to\gamma}\cap f_{\beta,2}(U_{\beta,2})
=\varnothing,
\]
与候选的 \(\{c\}\) 矛盾。所有节点均被保留，因此删冗余无法解释这一差异。即使更换所选分划，原网络所有边域皆空，正文操作也不可能新增这条边。

该反例仍保持外延相等；它说明的是**关系定义接受了正文不允许的表示变换**。例如，候选中 \(\beta_2\) 的终止域由 \(\{b,c\}\) 变为 \(\{b\}\)。因此，依赖完整边域、终止域或编号网络数据的后续论断，不能仅凭这个关系就认定变化严格来自正文的节点域加细。上述有限模型的条件已作枚举核对。

外延保持证明本身没有因此失效。源码通过 `node_eval_eq`、`terminal_projection`、`path_projection` 和 `eval_projected`，从局部算子及实际路由条件推导路径、求值保持，**没有把待证的完整路径对应直接作为字段假设**。`refinement_preserves_local_equivalence` 对当前较宽的关系仍成立；`refinement_preserves_representation` 随之成立。同域且域外均取 `bot`，也足以进一步推出完整算子相等。

还需区分两项补充工作：

1. **修正关系的数学范围。** 可以要求所有保留节点对都满足上述完整边域交集等式；或者把关系定义为“精确的删冗余前构造，再作可达节点裁剪”。不能简单把 `choice_projection` 的前提扩大到整个局域输出像，因为合法裁剪会把指向已删除子节点的选择改为 `stop`，并可能扩大保留节点的终止域。

2. **连接构造与关系接口。** 附件未给出由任意 `P : NodePartitionData N target` 构造 `NodeDomainRefinement N P.network` 的见证。标签保留条件、`NodePieceReached` 与裁剪可达性的对应，都应在此连接中证明。这个接口缺口不影响 `P.network_extensional_eq` 已独立给出的构造结论。至于“当前关系必然满足正文全部边域公式”，则被上述反例否定，不能仅靠补证明解决。

本次为源码与数学语义审阅，辅以有限模型枚举，未进行 Lean 编译验证；未修改附件或新增 Lean 源码。

材料来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。