**结论：附件准确、完整地覆盖了节点域加细及其保持外延等价的数学内容。** Lean 既从任意合法分划构造加细网络，也对任意满足 `NodeDomainRefinement` 的网络证明外延保持。可以补列删除前的边域、终止域等式，以及一般加细关系的几个推论。相关模块已通过 Lean 4.29.1 检查，主要构造和定理的公理依赖只有 `propext`、`Classical.choice`、`Quot.sound`。 [正文定义](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/source.md:1050) · [正文命题](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/source.md:1097)

### 定义逐项核对

| 正文要求 | Lean 对应及依据 |
|---|---|
| 分划被选节点的完整定义域 | `NodePartitionData` 用 `Fin count` 编号，要求块数为正、每块非空、两两不交，且并集等于 `N.node_dom target`。因此未被实际调用的定义域部分也参加分划。 |
| 子算子的定义域恰为该块，且逐点沿用原算子 | `local_domain` 与 `local_eq` 分别给出这两项。`local_op_eq_restrict` 进一步证明子算子等于原算子的限制，因为块外两者均取 `bot`。 |
| 保留其他节点，删除恰好未被访问的子节点 | `source_injective` 与 `old_node_present` 使每个未拆节点恰有一个对应标签，其局域算子由 `old_node_op_compat` 固定。`piece_node_present_iff_reached` 用原轨迹的**前缀求值**判定子节点是否保留，因而同一原节点的多次访问按各次当前输入分别选块。`piece_label_reached_iff` 证明构造确实实现这一判据。 |
| 入口、边域和自环按交集细分 | `entry_domain_eq` 给出精确入口片，`edge_domain_eq` 给出所有保留节点对上的精确边域，`network_edge_domain_eq` 证明构造满足该字段。空片和空边域分别对应无入口和无边。 |

具体地，记 \(\pi\) 为新标签到原标签的投影，\(U'_v\) 为新节点域，\(Y_v=f'_v(U'_v)\) 为其完整输出像。两条等式为
\[
U_v^{\prime\mathrm{in}}=U_{\pi(v)}^{\mathrm{in}}\cap U'_v,
\qquad
D'_{v\to w}=D_{\pi(v)\to\pi(w)}\cap Y_v\cap U'_w.
\]
原边域已包含于原源像和原目标域，所以只有目标被拆时只需截目标域，只有源被拆时只需截源像，原自环则两边都截。两端都未拆时得到原边域。这里的 \(Y_v\) 取完整局域像，因此定律也约束从未被入口轨迹使用的保留边。 [分划和限制算子](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) · [关系字段](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:68) · [入口等式](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:283) · [构造的边域等式](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:346)

### 删除前后的终止域

源码直接定义了删除前的路由 `NodePartitionData.choice`。旧选择为 `stop` 时仍停止，旧选择为 `next` 时按输出点选取目标标签。对完整源像中的输出，这给出删除前所有候选节点对的同一边域交集式。对每个原后继，把它的所有候选目标域取并，得到其原节点域；因此取出边域并集的补集便得 \(T_v^{\mathrm{删前}}=Y_v\cap T_{\pi(v)}\)。这也解释了正文为何在**删除前**得到未拆节点的终止域等式。源码单列了删除后的保留边等式，删除前的全边域和终止域公式可补作独立引理。 [正文的证明阶段](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/source.md:1101) · [删除前路由](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:111) · [删除时的路由](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:35)

一个有限例子可以核对这一区别。取 \(X=\{\bot,a,b\}\)，节点 \(\gamma,\beta\) 均用恒等算子，唯一边 \(\gamma\to\beta\) 的域为 \(\{a,b\}\)。输入域取 \(\{a\}\)，从 \(\gamma\) 进入。将 \(\beta\) 拆成 \(\{a\}\)、\(\{b\}\) 两块后，只有前一块被访问。删除后一块使 \(\gamma\) 的终止域从空集扩大为 \(\{b\}\)，而输入 \(a\) 的轨迹及输出照旧。若再让 \(b\) 作为初始输入直接进入 \(\beta\)，两块都会保留。此时 \(\gamma\to\beta_b\) 的边域 \(\{b\}\) 虽从未被实际使用，删掉它仍会违反精确边域等式。这个变体说明了为什么仅核对实际路由不足以核对定义。

### 外延保持与可补列的结论

- **源码已证明构造结果的全局算子相等。** `colour_path` 按每一步的当前输入改标，`coloured_terminal` 证明改标后的轨迹合法终止，`coloured_eval` 证明沿轨迹求值得到同一输出。构造沿用原统一长度界，`prune` 保留每条实际轨迹。`network_refinement` 将该构造接入严格加细关系，`network_extensional_eq` 直接证明 \(\phi_{\mathcal N'}=\phi_{\mathcal N}\)，包括域外两侧均取 \(\bot\) 的情形。该证明允许回访与自环。 [构造及其外延等式](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:168) · [严格关系见证](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:449)
- **源码已证明一般关系上的命题原式。** 对任意 `NodeDomainRefinement`，`path_projection` 由入口、实际路由投影和终止路径唯一性推出，`eval_projected` 由各节点在合法当前输入上的逐点相等推出。合起来得到 `refinement_preserves_local_equivalence` 的节点域分支，即 \(\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}\)。同域字段与此结论可直接封装为 `ExtensionalEquivalent`，再用域外补全可得一般关系上的全局算子等式。逐输入路径等长也推出实际求值深度相等。这些一般形式可单列为推论。 [路径投影与求值](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:198) · [保持局部等价](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:453)
- **可补一个从正文静态数据导出 `choice_projection` 的引理。** 一般关系把它存作字段，构造已证明该字段。对任意满足其余精确规则的候选网，沿原轨迹逐次选新标签。每个选中的子节点都有该次访问作保留见证，相邻两步的输出属于边域交集。若原末步的输出在候选网还能继续，精确边域公式就会给出一条包含该输出的原出边，与原轨迹终止矛盾。故改标后的轨迹就是候选网的唯一实际轨迹，实际输出上的 `choice_projection` 随之成立。这说明该字段可由正文规则推出，补列引理可让调用者直接使用这些规则构造见证。 [实际路由投影的构造证明](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:387)

审阅依据为 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory* 附件版本，CC BY 4.0。 [ORCID](https://orcid.org/0009-0006-6536-3453) · [作品主页](https://glenzli.com/books/oet/) · [公开仓库](https://gitlab.com/glenzli/oet-public) · [许可](https://creativecommons.org/licenses/by/4.0/)