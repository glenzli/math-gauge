**构造性的外延保持结论已覆盖正文的节点域加细情形；但 `NodeDomainRefinement` 没有精确刻画正文定义，因此整套接口尚不能判为完全对应。** 主要问题是：该关系允许修改未被实际求值使用的边域，而正文要求这些边域也按指定公式保留。

以下仅审阅节点域加细。

具体构造见 [domain_refinement_construction.lean](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/max/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12)，关系与通用保持定理见 [network_refinement.lean](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/max/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:73)。

| 正文要求 | 实现及判断 |
|---|---|
| 对完整节点域作有限非空分划 | `count_pos`、`nonempty`、`disjoint`、`cover` 完整对应。被分划的是 `node_dom target`，包含尚未实际调用的部分。 |
| 子算子定义域恰为分划胞，且在胞内与原算子相同 | `local_domain`、`local_eq` 完整对应；`local_op_eq_restrict` 已证明整个子算子等于原算子的域限制。 |
| 替换节点并细分入口片 | `Label` 保留其他节点、加入分划胞标签；入口使用 `lift_label (N.entry x) x`。结合分划唯一性和 `entry_mem`，得到正文的入口交集公式。 |
| 按交集公式细分入边、出边及自环 | **具体构造正确。** `choice` 保留原后继选择，并按当前输出所在胞选择目标子节点。`self_loop_choice_iff` 的源输出像假设与右侧目标胞条件，共同实现自环的三重交集。**抽象关系则约束不足，详见下文。** |
| 允许回访同一节点，每次按当时输入选胞 | `colour_path` 每一步更新当前点值，再调用 `lift_label`；没有无环或“一节点只访问一次”的限制。 |
| 保证统一有限终止，再删冗余节点 | `coloured_terminal` 证明重标后的路径合法终止；`colour_path_length` 证明长度不变。`presentation` 由此构造终止证书，随后 `prune` 构造无冗余的有限网络。 |
| 加细后外延相同 | `NodePartitionData.network_extensional_eq` 已证明删冗余后的**全域算子相等**，包含域外取 `bot` 的部分。 |

此处 `LocalEquivalent` 是逐点相等，因此外延保持无需额外的度量分离性或 L/K/N 假设。

**`NodeDomainRefinement` 的不足在于只约束实际输出上的路由。**

其 `choice_projection` 仅适用于
\[
z\in f'_{v}\bigl(U_{v}^{\prime,\mathrm{eff}}\bigr),
\]
而正文的边域公式作用于完整节点输出像
\[
f'_v(U'_v).
\]
这两个集合可以严格不同。正文也明确保留未被入口轨迹使用的转移域；删冗余只允许删除未访问节点及其关联边。

下面给出一个**所有节点均保留**的反例，排除删冗余造成差异的解释。

取
\[
X=\{\bot,a,b,c\},\qquad U=\{a,b\}.
\]
原网络有两个节点 \(\beta,\gamma\)，局域算子均为恒等算子，定义域均为 \(\{a,b,c\}\)。两个输入均从 \(\beta\) 进入，唯一边域为
\[
D_{\beta\to\gamma}=\{b,c\}.
\]
其他边域为空。

加细 \(\beta\)，取
\[
A_1=\{a,c\},\qquad A_2=\{b\},
\]
子算子为相应的恒等限制。构造候选网络 \(N'\)：入口分别为 \(\beta_1,\beta_2\)，且**仅保留**
\[
D'_{\beta_2\to\gamma}=\{b\},
\]
令 \(\beta_1\) 没有出边。

| 输入 | 原网络路径 | 候选网络路径 | 两侧输出 |
|---|---|---|---|
| \(a\) | \((\beta)\) | \((\beta_1)\) | \(a\) |
| \(b\) | \((\beta,\gamma)\) | \((\beta_2,\gamma)\) | \(b\) |

两网都具有统一长度界 \(2\)，各自所有节点均被实际访问。候选网络的实际节点输入域分别为
\[
U_{\beta_1}^{\prime,\mathrm{eff}}=\{a\},\quad
U_{\beta_2}^{\prime,\mathrm{eff}}=\{b\},\quad
U_{\gamma}^{\prime,\mathrm{eff}}=\{b\}.
\]

以自然标签映射作为 `source`，`NodeDomainRefinement` 的所有字段都能满足：

- 两个分划胞均由原轨迹到达，满足 `piece_node_present_iff_reached`；
- 局域算子及入口投影符合要求；
- 在实际输出 \(a,b\) 上，后继选择投影与原网完全一致。

但是正文要求
\[
D'_{\beta_1\to\gamma}
=D_{\beta\to\gamma}\cap f_{\beta_1}(A_1)
=\{b,c\}\cap\{a,c\}
=\{c\},
\]
候选网络却将它设为空。两个端点均实际可达，这条边不能因删冗余而被删除。

因此，**满足 `NodeDomainRefinement` 并不保证候选网络就是所给分划对应的正文加细结果。** 数学影响包括完整边域和终止域可能改变：本例中候选节点 \(\beta_1\) 的终止域是 \(\{a,c\}\)，正文构造要求的是 \(\{a\}\)。两网外延仍相同，所以这不是现有外延保持定理的反例。

**现有证明的地位与需要补充的内容应分别看待。**

已证明的内容包括：

- 任意 `NodePartitionData` 所构造的网络具有合法终止路径，并在删冗余后保持全域外延算子相等。
- 对给定的 `NodeDomainRefinement` 证书，`terminal_projection`、`path_projection`、`eval_projected` 从路由与局域相等条件推导路径及求值对应；完整路径对应并非假设字段。
- 通用的 `refinement_preserves_local_equivalence` 和 `refinement_preserves_representation` 在其声明前提下成立。

尚需补充的是：

1. **精确的结构关系。** 对任意两个保留节点 \(v,w\)，要求完整边域满足
   \[
   D'_{v\to w}
   =
   D_{\pi(v)\to\pi(w)}
   \cap f'_v(U'_v)
   \cap U'_w.
   \]
   该式统一覆盖普通入边、出边、自环和无关边，并允许删除通往已删节点的边。也可以保留现关系作为求值保持证书，另设严格对应正文的加细关系。

2. **构造与关系的衔接。** 附件没有证明 `P.network` 满足 `NodeDomainRefinement N P.network`，也没有把正文的完整结构条件与该构造正式连接起来。这是接口完整性问题；构造自身的外延证明已直接完成。

3. **集合公式的显式对应。** 入口、一般边域以及终止域的完整集合等式尚未逐项封装为 Lean 定理；其中自环已有相应的条件式证明。终止域的
   \[
   T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta
   \]
   应注明用于**删冗余前**：删点后，保留节点的终止域可在未使用输出上扩大。[`prune`](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/max/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:76) 的这种行为符合正文。

复编译两个目标文件的依赖闭包，共 24 个模块，全部通过。未修改附件，也未新增 Lean 源码。

所引 OET 材料出自 Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，许可为 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。上述反例与评议为本次审阅补充。