**结论**　具体构造 `NodePartitionData.network` 实现了正文的节点域加细，并已证明加细前后外延算子相等。给定两张网络时，`NodeDomainRefinement` 的条件过宽。它允许改动保留节点之间、实际轨迹未用到的边域。因此，外延保持的结论已经覆盖正文情形，但关系定义尚未精确刻画正文的一步加细。[正文定义](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/source.md:1048) · [正文命题](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/source.md:1095)

### 具体构造如何对应正文

1. **分划与局域算子。** `NodePartitionData` 用 `Fin count` 给出有限正数个非空、两两不交的子域，覆盖目标节点的完整定义域。`local_domain` 和 `local_eq` 分别规定子算子的精确定义域和域内取值。`local_op_eq_restrict` 进一步证明子算子就是原算子的限制，因为两者在子域外均取 \(\bot\)。其他节点沿用原局域算子。[分划与限制算子](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12)

2. **入口片与边域。** 记 \(\pi(\eta)\) 为新标签 \(\eta\) 对应的原节点，\(A_\eta=\operatorname{dom}(f'_\eta)\)，\(I_\eta=f'_\eta(A_\eta)\)。构造用初始输入 \(x\) 选入口标签，故入口片是 \(U^{\mathrm{in}}_{\pi(\eta)}\cap A_\eta\)，其中非入口节点的原入口片视为空集。边域满足统一公式
   \[
   D'_{\eta\to\xi}
   =D_{\pi(\eta)\to\pi(\xi)}\cap I_\eta\cap A_\xi .
   \tag{1}
   \]
   这是由源码定义可推出的等式。对 \(z\in I_\eta\)，局域算子相容性保证 \(z\) 也在原节点的输出像内。新路由选择 \(\xi\)，恰当且仅当原路由选择 \(\pi(\xi)\)，且 \(z\in A_\xi\)。当目标是被拆节点时，后一条件由分划唯一确定子节点。式 (1) 因而给出正文的入边、出边和自环交集公式，也保留所有非关联边。`self_loop_choice_iff` 显式证明了其中的自环路由条件。删点前，原路由的 `stop` 原样传递，故终止域为 \(I_\eta\cap T_{\pi(\eta)}\)。[路由与自环引理](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:111)

3. **终止、回访与删点。** `colour_path` 在每次经过目标节点时按当时的输入点选块，因此包含同一节点多次回访、先后进入不同子块的情况。`coloured_terminal` 和 `coloured_eval` 证明所得轨迹合法且终止输出相同。逐输入路径长度相等，原统一长度界仍适用，实际最大求值深度也相等。`prune` 恰保留这些轨迹经过的标签，删除通向被删标签的边。式 (1) 在所有保留节点对上仍成立，即使对应边从未被实际走过。[路径重标与构造](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:168) · [删点实现](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:71)

### 关系定义的缺口与反例

`NodeDomainRefinement` 已记录分划、局域算子、保留标签及同一输入域。它的 `entry_projection` 联合入口合法性、分划互斥性和 `source` 的单射性，足以推出入口片公式。缺口在 `choice_projection`：它只约束新节点**实际输入域的像**上的后继选择，式 (1) 则约束**完整局域输出像**上的边域。[关系字段](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:73)

取 \(X=\{\bot,a,b,c\}\)，全网输入域 \(U=\{a,b,c\}\)。原网有两节点 \(\gamma,\beta\)，局域算子分别是恒等算子在 \(\{a,c\}\)、\(\{b,c\}\) 上的限制。入口把 \(a\) 送入 \(\gamma\)，把 \(b,c\) 送入 \(\beta\)。唯一的边为 \(\gamma\to\beta\)，边域是 \(\{c\}\)。三个输入都一步终止，因为 \(\gamma\) 实际只收到 \(a\)。

将 \(\beta\) 拆成 \(\{b\}\) 和 \(\{c\}\) 两块。两个子节点均可达，正文要求保留边 \(\gamma\to\beta_c\)，其边域为 \(\{c\}\)。另取一个具有相同节点算子和入口的网络 \(M\)，令所有输出都终止。此时 `choice_projection` 在三个节点分别只检查 \(a,b,c\)，两侧都返回 `stop`，其余关系字段也成立。但 \(M\) 的这条边域为空，\(\gamma\) 的终止域由正文结果的 \(\{a\}\) 变成了 \(\{a,c\}\)。若改拆 \(\gamma\)，又必须保留定义域为 \(\{b,c\}\) 的原 \(\beta\)，而 \(M\) 的三个节点域均与它不同。这给出了关系接受、正文定义排除的一对网络。

### 已证明的结论与修复方向

- `NodePartitionData.network_extensional_eq` 对实际构造直接证明了全域算子相等。对给定的关系见证，`path_projection` 由入口和实际后继条件推出路径对应，`eval_projected` 给出逐步求值相等，最终 `refinement_preserves_local_equivalence` 证明正文要求的 \(\equiv_U\)。目标节点可达保证 \(U\) 非空，两网外延算子的定义域均为同一个 \(U\)。同域和逐点相等也足以推出 `FiniteOperatorNetwork.ExtensionalEquivalent`。[构造的外延等式](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:258) · [关系的路径与求值证明](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:195) · [局部等价定理](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:377)
- **应在关系中要求式 (1) 对所有保留节点对成立，并补上构造与该关系的对应定理。** 先证明构造保留子块当且仅当 `NodePieceReached` 成立，再用 `source` 给出的单一标签双射对齐两网。逐项比较局域算子、入口片和边域，即可证明满足补强关系的网络恰是相应构造经标签对应后的结果。直接把现有 `choice_projection` 的量词扩大到 `node_image` 会过强。例如把反例的 \(U\) 改为 \(\{a,b\}\)，则 \(\beta_c\) 应被删除，\(\gamma\) 的完整输出像仍含 \(c\)，而新路由在 \(c\) 上应当终止。式 (1) 恰好允许这种删点效果。[正文删点规则](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR01/physical-1/work/source.md:168)

两个相关模块及其依赖已用 Lean 4.29.1 编译通过。反例的关系见证与边域差异也已用 Lean 核验。

附件来源为 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*。[ORCID](https://orcid.org/0009-0006-6536-3453) · [官方页面](https://glenzli.com/books/oet/) · [源码仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)