**外延等价命题成立。** 从分划数据出发的 `NodePartitionData.network` 实现了正文的节点域加细，并证明了剪枝后的全域外延算子相等。缺口在于给定两个网络时使用的 `NodeDomainRefinement N N'`。这个关系比正文定义宽，允许改动两个保留节点之间从未被入口轨迹使用的非空边域。两个目标文件及其本地依赖均已通过 Lean 4.29.1 编译检查。[正文定义](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/source.md:1048) · [正文命题](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/source.md:1095)

### 逐项核对

1. **分划、局域算子与入口均对应正文。** 两套实现都要求正数个非空、两两不交的分片，其并集等于目标节点的整个 `node_dom`。每个子算子的定义域恰为本片，在片上与原算子逐点相等，片外因定义域条件只能取 \(\bot\)。构造中的 `local_op_eq_restrict` 显式证明了限制算子等式。入口由 `lift_label (N.entry x) x` 给出，因此子节点入口片恰为原入口片与本片之交，其他入口片沿用原值，空入口片是入口函数的空纤维。在关系版中，`entry_projection`、`entry_mem` 和分片唯一性也强制这些入口等式。选定目标节点后，原网的 `node_reachable` 已保证输入域非空。[分划与限制算子](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) · [关系字段](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:73)

2. **规范构造在完整局域输出像上实现了四类边域。** 记 \(\pi v\) 为新标签对应的旧节点，\(S_v\) 为新节点定义域，\(Y_v=f'_v(S_v)\)。剪枝前，对 \(z\in Y_v\)，`choice` 先取旧节点在 \(z\) 的选择。若旧后继是被拆节点，`choice_next_mem` 保证 \(z\) 属于其定义域，`piece_at_unique` 再唯一确定目的分片。因此按 `edge_domain` 的定义有
   \[
   D^0_{v\to w}=D_{\pi v\to\pi w}\cap Y_v\cap S_w. \tag{1}
   \]
   对入边，这给出与目的分片取交。对出边，这给出与源分片输出像取交。原自环同时取这两个交。两端均为未拆节点时，原边域本已包含于相应的像和域，故所得边域就是原边域。只有非空边域构成边。源码的 `self_loop_choice_iff` 显式证明了在源分片输出像上的自环判据。统一集合等式 (1) 以及剪枝前的终止域公式 \(T^0_v=Y_v\cap T_{\pi v}\) 可由这些定义推出，附件没有把它们逐项列为集合等式定理。[构造的路由与自环引理](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:111) · [有限网络的边域定义](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean:213)

3. **剪枝保留节点之间的完整边域。** `colour_path` 在每次经过目标节点时按该次的当前输入选片，因而允许回访时进入不同子节点。`Reached` 按这些着色后的入口路径保留标签。未拆旧节点都有原轨迹见证，分片节点则恰在某次目标节点的当前输入落入该片时保留。关系版的 `source_injective`、`old_node_present` 和 `piece_node_present_iff_reached` 正确表达了这个标签条件。规范构造的 `prune_choice` 仅将指向已删除目的节点的选择改为 `stop`。故 (1) 对任意两个保留端点仍成立。若 \(R\) 为保留标签集，最终终止域为 \(Y_v\setminus\bigcup_{w\in R}D^0_{v\to w}\)，可能比剪枝前大。[按当前输入选片](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:168) · [剪枝规则](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:35)

4. **两条外延证明均有实质内容。** 构造版的 `coloured_terminal` 和 `coloured_eval` 证明新轨迹合法、终止且输出相等。`network_path_projection` 在剪枝后恢复每个输入的原路径，因此逐输入长度相等，原统一长度界仍适用。`network_extensional_eq` 结合域外两侧均取 \(\bot\)，直接证明 \(\phi_{P.\mathrm{network}}=\phi_N\)。关系版则由 `node_eval_eq`、实际轨迹上的 `terminal_projection` 和终止路径唯一性推出 `path_projection`，再由 `eval_projected` 推出 `refinement_preserves_local_equivalence`。其直接结论是 \(U\) 上逐点相等，配合 `same_input_domain` 就得到正文的外延等价，也可推出全域算子相等。[构造版全域等式](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:258) · [关系版路径证明](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:195) · [关系版局部等价定理](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:377)

### 关系过宽的有限反例

`choice_projection` 只在 \(z\in f'_v(U_v^{\prime\mathrm{eff}})\) 上检查后继。这个集合可以严格小于完整局域输出像 \(Y_v\)。而网络的 `PresentationData` 保留完整 `edge_domain`，所以两者之间的差异会改变正文所定义的网络数据。[后继条件](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:108) · [网络原始数据](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_identity.lean:15)

取 \(X=\{\bot,1,2,3\}\)，入口域 \(U=\{1,2\}\)。原网只有入口节点 \(\beta\)，令
\[
f(\bot)=\bot,\qquad f(1)=f(2)=1,\qquad f(3)=2,\qquad
D_{\beta\to\beta}=\{2\}.
\]
两个入口输入都在一步后输出 \(1\) 并终止。将节点域分为 \(A=\{1,3\}\) 和 \(B=\{2\}\)，子算子取相应限制。正文要求保留
\[
D^0_{A\to B}=\{2\}\cap f(A)\cap B=\{2\}.
\]
两个子节点分别由入口输入 \(1,2\) 访问，都能通过剪枝。

现在取候选网络 \(N'\)，入口和子算子完全按上述分划设置，所有后继选择一律为 `stop`。两个分片都有 `NodePieceReached` 见证，标签和局域算子字段均满足要求。两个子节点的实际输出像都是 \(\{1\}\)，而旧选择在 \(1\) 也为 `stop`，所以 `choice_projection` 成立。于是 `NodeDomainRefinement N N'` 可以成立，但候选网的 \(D'_{A\to B}=\varnothing\)。从合法局域状态 \((A,3)\) 出发，正文构造会把 \(2\) 送入 \(B\)，最终输出 \(1\)；候选网在 \(A\) 直接输出 \(2\)。这个差异改变了边域和终止域，同时保留了每个入口输入的输出。

### 修复方向

在关系版中，对**每一对保留节点**要求其完整 `edge_domain` 满足 (1)，即可排除反例，并由补集确定最终终止域。直接把 `choice_projection` 的检查范围扩大到整个 \(Y_v\) 会过强。仍取上例，仅将入口域改为 \(\{1\}\)，此时 \(B\) 确应删除。在 \(A\) 的局域输出 \(2\) 上，旧选择为 `next β`，合法剪枝后的选择却是 `stop`。按保留端点比较边域恰好容许这项变化。

附件还可补上构造与关系之间的桥接定理，证明每份 `NodePartitionData` 生成的 `P.network` 满足修订后的关系。若要让该关系精确判定“由一次节点域加细得到”，可进一步证明满足关系的任意 \(N'\) 经与 `source` 相容的重编号后，与相应 `P.network` 的 `presentation_data` 相等。现有源码已经独立证明规范构造的外延结论，尚缺的是这项对完整网络数据的刻画。

正文及附带形式化取自 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*。[作品主页](https://glenzli.com/books/oet/) · [ORCID](https://orcid.org/0009-0006-6536-3453) · [公开仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)