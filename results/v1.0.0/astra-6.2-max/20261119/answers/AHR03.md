**附件完整覆盖了正文规定的一次节点域加细，以及该情形下的外延等价命题。** 给定原网络、目标节点、分划和各片算子，Lean 构造了删去不可达子节点后的有限网络，证明它满足 `NodeDomainRefinement`，并直接证明其外延算子与原网络在整个 \(\mathcal X\) 上相等。对任意满足该加细关系的网络，通用定理也证明了正文所写的 \(\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}\)。我用 Lean 4.29.1 重新编译了相关模块及依赖。 [正文定义](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/source.md:1050) · [正文命题](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/source.md:1097)

### 定义与构造的逐项对应

1. **分划和局域算子。** `NodePartitionData` 用正数 `count` 和 `Fin count` 编号各片，要求每片非空、两两不交、并集恰为目标节点的**整个**定义域 \(U_\beta\)。记各片为 \(S_a\)。`local_domain` 要求 \(\operatorname{dom}(f_a)=S_a\)，`local_eq` 要求 \(f_a(x)=f_\beta(x)\) 对每个 \(x\in S_a\) 成立。由于算子定义域恰由取值非 \(\bot\) 的点组成，片外 \(f_a\) 必取 \(\bot\)。源码据此证明了算子等式 `local_op_eq_restrict`，即 \(f_a=f_\beta|_{S_a}\)。正文的非空输入域约定也满足，因为对所选目标调用 `N.node_reachable` 就给出一个 \(x\in U\)。 [分划与限制算子](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12)

2. **节点和入口。** 构造先采用标签 \((V\setminus\{\beta\})\sqcup\mathrm{Fin}(q)\)。记 \(\pi\) 为投回原节点的映射。`mem_piece_at` 和 `piece_at_unique` 保证每个合法输入选中其唯一所属片。新入口由原入口和当前初始点共同决定。对任意保留节点 \(v\)，源码证明了
   \[
   U_v^{\prime\,\mathrm{in}}=U_{\pi v}^{\mathrm{in}}\cap U'_v.
   \]
   因此子节点得到正文的入口交集，其他节点继承原入口片。空交集表示没有初始输入从该节点进入，该节点仍可经入边到达。 [入口片等式](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:283)

3. **全部边域，包括未使用的边。** 记 \(I'_v=f'_v(U'_v)\) 为完整局部像。`NodeDomainRefinement.edge_domain_eq` 要求对每一对保留标签都有
   \[
   D'_{v\to w}=D_{\pi v\to\pi w}\cap I'_v\cap U'_w.
   \]
   这在抽象关系中是字段，对实际构造则是已证明的 `network_edge_domain_eq`。利用原边域包含于原源像和原目标域，四种情形逐项化简如下。空边域按网络的定义省略。 [精确关系](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:118) · [构造的边域证明](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:346)

   | 新边的端点，其中 \(\gamma,\delta\ne\beta\) | 新边域 |
   |---|---|
   | \(\gamma\to\delta\) | \(D_{\gamma\to\delta}\) |
   | \(\gamma\to\beta_a\) | \(D_{\gamma\to\beta}\cap S_a\) |
   | \(\beta_a\to\gamma\) | \(D_{\beta\to\gamma}\cap f_a(S_a)\) |
   | \(\beta_a\to\beta_b\) | \(D_{\beta\to\beta}\cap f_a(S_a)\cap S_b\) |

4. **删去冗余子节点。** `piece_label_reached_iff` 证明，子节点 \(a\) 被保留，当且仅当某个原输入轨迹在某次经过 \(\beta\) 时，执行该节点**之前的当前点**落入 \(S_a\)。这个判据涵盖同一轨迹对 \(\beta\) 的多次访问。`old_label_reached` 证明其他旧节点全部保留。抽象关系中的 `source_injective`、`old_node_present` 和 `piece_node_present_iff_reached` 又使候选网络的标签与这批保留标签一一对应。最后，`network_refinement` 和 `allowed_network_refinement` 把实际构造接入了通用定理所用的一步加细关系。 [可达性判据](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:296) · [构造与关系的连接](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:449)

### 外延保持是怎样证明的

`colour_path` 每一步都用该步的当前输入选标签，`lift_apply` 给出该点的新旧局域输出相等。因此即使连续经过原自环，两次也可以选中不同子节点。`coloured_terminal` 证明所得序列确为终止路径，`coloured_eval` 证明终端输出相等。构造沿用原统一长度界。删点后的 `network_path_projection` 进一步给出每个输入的新路径投影恰为原路径，故实际长度逐点相等，取最大值也得到相同的求值深度。`network_extensional_eq` 在 \(U\) 内用上述求值等式，在 \(U\) 外用两侧均取 \(\bot\)，得到全域算子等式。 [路径构造与归纳证明](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:168) · [删点后的路径与算子等式](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:241)

对任意加细见证，通用证明使用 `choice_projection` 在**实际产生的局部输出**上投影停止或后继决定，再由终止路径唯一性得到 `path_projection`，结合 `eval_projected` 推出 `refinement_preserves_local_equivalence`。这个证明只需实际路由相容。定义本身还通过上述 `edge_domain_eq` 约束完整边域。实际构造分别证明了这两项，路径对应和外延相等都是结论。 [通用路径投影](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:209) · [通用外延保持定理](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:428)

### 终止域公式的适用阶段

正文证明中的 \(T^0_v=I'_v\cap T_{\pi v}\) 适用于**删点前**。它可由构造的 `choice` 直接推出，因为旧选择为 `stop` 时新选择也为 `stop`，旧选择为 `next` 时新选择仍有对应后继。若要在 Lean 中逐式引用这条集合等式，可在未删点的 `presentation` 上补一个专名引理。删点后若保留标签集为 \(R\)，完整终止域是 \(I'_v\setminus\bigcup_{w\in R}D^0_{v\to w}\)，可能严格扩大。一般删点代码已给出这个按保留后继取补集的公式。 [正文中的删点前公式](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/source.md:1130) · [删点后的终止域](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/transition_graph_import.lean:247)

一个有限例子可以同时检验终止域和未使用边。取 \(\mathcal X=\{\bot,a,b,c,d\}\)，唯一节点的算子把 \(b\) 送到 \(c\)，其余点固定。入口片为 \(\{a\}\)，自环域为 \(\{c,d\}\)，故唯一入口轨迹在 \(a\) 一步终止。把节点域分成 \(A=\{a,b,d\}\) 与 \(B=\{c\}\)。删点前 \(A\to A\) 的边域是 \(\{d\}\)，\(A\to B\) 的边域是 \(\{c\}\)。删去不可达的 \(B\) 后，\(A\) 的完整终止域从 \(\{a\}\) 增为 \(\{a,c\}\)，而自环 \(\{d\}\) 仍须保留。若把该自环也删掉，入口求值仍相同，却违反精确边域等式。这说明了源码中两种量化范围各自的作用，也说明删点前终止域引理的单独封装属于表述层面的补充。

数学正文与所审 Lean 实现出自 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*，以上判断针对附件版本。 [作品主页](https://glenzli.com/books/oet/) · [ORCID](https://orcid.org/0009-0006-6536-3453) · [公开仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)