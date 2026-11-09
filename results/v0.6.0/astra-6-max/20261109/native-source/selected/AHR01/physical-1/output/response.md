**结论：具体构造已经给出了通用的节点域加细及外延保持证明；但 `NodeDomainRefinement` 关系比正文定义更宽，不能将整套实现判为准确、完整的对应。** 主要不足是：它只约束实际使用的输出上的路由，允许修改正文要求保留的其他边域。这个问题不推翻已有的外延等价定理，但影响“什么算作一次节点域加细”的准确性。

以下仅审阅附件的节点域加细部分。

**1. 分划、局域算子和具体构造基本对应正确。**

正文的[节点域加细定义](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR01/physical-1/work/source.md:1048)，在 [NodePartitionData 及其构造](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 中有以下对应：

| 数学要求 | 实现与判断 |
|---|---|
| 将整个节点定义域作有限非空分划 | `count_pos`、`Fin count`、`nonempty`、`disjoint`、`cover` 完整表达；分划的是 `node_dom target`，并未误换成实际输入域。 |
| 子算子定义域恰为分片，且在片内与原算子相同 | `local_domain`、`local_eq` 准确表达。`local_op_eq_restrict` 进一步证明子算子就是原算子的域限制。 |
| 入口片按当前输入所属分片细分 | `presentation.entry` 使用 `lift_label (N.entry x) x.val`；`mem_piece_at` 与 `piece_at_unique` 保证选中唯一正确分片。 |
| 入边、出边及自环按交集公式细分 | `choice` 对原后继使用当前输出 `z` 重新选择目标标签，符合这些公式。自环另有 `self_loop_choice_iff`。 |
| 同一节点可反复经过，每次可能进入不同分片 | `colour_path` 每一步按当时的输入重新选片；没有无环或节点不重复假设。 |
| 新数据仍统一有限终止 | `coloured_terminal` 证明重标记路径仍合法终止；`colour_path_length` 证明长度不变；`presentation` 使用原来的 `depth_bound`。 |
| 删除不可达子节点 | `network := presentation.prune` 按实际轨迹删除节点，并保留剩余局域算子。 |
| 外延保持 | `network_extensional_eq` 直接证明删冗余后的**全域算子相等**，强于仅在共同输入域上的局部等价。 |

这里不需要额外的 Lip、co-Lip 或规范族分离假设：正文的局部等价和这里的 `LocalEquivalent` 都是逐点相等，相关结论是结构性的。

为核对路由，记删冗余前的新标签投影为 \(\pi\)，新节点域为 \(A_v\)，输出像为 \(B_v=f'_v(A_v)\)。展开构造的 `choice`，可得统一公式

\[
D^{\mathrm{pre}}_{v\to w}
=
D_{\pi(v)\to\pi(w)}\cap B_v\cap A_w.
\]

它分别化为正文的入边、出边、自环公式；两个端点均未替换时，额外两个交集由原边域的包含条件消去。自环定理中的前提
\(z\in f_{\beta,a}(U_{\beta,a})\)，正好提供公式中的源输出像条件，没有漏掉这一项。

同样，删冗余前有

\[
U^{\mathrm{in,pre}}_v=U^{\mathrm{in}}_{\pi(v)}\cap A_v,
\qquad
T^{\mathrm{pre}}_v=B_v\cap T_{\pi(v)}.
\]

这些是对源码定义展开后的数学核对；附件没有把所有集合等式统一封装成对应的 Lean 定理，不能把它们全部列为源码中已有的命名结论。

**2. 实质性不足在 `NodeDomainRefinement.choice_projection`：它未完整表达正文的边域规则。**

[该字段](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:108) 仅要求

\[
\pi_*(\operatorname{choice}'(v,z))
=
\operatorname{choice}(\pi(v),z)
\quad
\text{当 }z\in f'_v(U_v^{\mathrm{eff}\prime}).
\]

这里是**实际输入域的输出像**，可能严格小于整个局域输出像 \(f'_v(A_v)\)。

正文却规定完整边域，包括从入口求值时没有使用的部分。节点都可达，并不意味着每个局域输入或每条边都被使用。因此，这个字段允许在未实际使用的局域输出上新增、删除或改接边。

下面的四点反例可以逐项复核，而且不涉及删冗余。

取
\[
X=\{\bot,a,b,c\},\qquad U=\{a,b\},
\]
四点互异。原网络只有节点 \(\beta\)，局域算子为恒等算子，入口片为 \(U\)，没有边。两个输入均一步终止。

将其节点域分为
\[
A_0=\{a,c\},\qquad A_1=\{b\},
\]
子算子取恒等算子在各片上的限制。构造候选新网络：

| 数据 | 值 |
|---|---|
| 节点 | \(\beta_0,\beta_1\) |
| 入口 | \(a\) 进入 \(\beta_0\)，\(b\) 进入 \(\beta_1\) |
| 唯一边 | \(\beta_0\to\beta_0\)，边域为 \(\{c\}\) |
| 其他输出选择 | 全部终止 |

它满足当前 `NodeDomainRefinement` 的全部条件：

- 分划与局域算子条件成立；令 `source βₐ = Sum.inr a`，得到单射。原网没有其他节点，相关旧节点条件为空。
- 两个分片都满足 `NodePieceReached`，分别由原输入 \(a,b\) 见证；两个新节点也都实际可达。
- 新网实际输入域分别为 \(\{a\}\)、\(\{b\}\)，对应输出选择均为 `stop`，所以 `choice_projection` 成立。
- 新增自环的输出 \(c\) 属于目标节点域 \(\{a,c\}\)，满足转移合法性。
- 两条入口轨迹仍分别只有一个节点，统一长度界为 \(1\)。从 \((\beta_0,c)\) 出发可以循环，但 \(c\notin U\)，不违反有限网络对入口输入的终止要求。

然而正文要求

\[
D'_{\beta_0\to\beta_0}
=
D_{\beta\to\beta}\cap A_0\cap A_0
=
\varnothing,
\]
候选新网却取 \(\{c\}\)。所以它**满足 Lean 的加细关系，却不是正文允许的节点域加细结果**。两个子节点都可达，不能用删冗余解释这一差异。

两网的外延算子仍相同：在 \(a,b\) 上恒等，在其余点上取 \(\bot\)。因此反例针对的是定义的准确性，而非外延保持结论。它也说明当前关系可以把无边图变成含自环的图，超出了正文规定的表示变换。

若需附加规范背景，可取正常点间的离散距离、正常点到 \(\bot\) 的距离为 \(+\infty\)。

**3. 已有外延保持证明是真正的推导，不是把结论当作前提。**

`NodeDomainRefinement` 中没有存储外延相等或完整路径相等。源码的证明顺序是：

1. `node_eval_eq`：合法新节点输入上的输出等于对应原节点输出。
2. `terminal_projection`：利用实际输出上的路由相容性，将新终止路径投影为原终止路径。
3. `path_projection`：利用 `terminal_path_unique`，证明该投影恰为同一输入的原路径。
4. `eval_projected`、`NetworkRefinement.path_eval_eq`：证明路径求值相等。
5. [refinement_preserves_local_equivalence](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:377)：得到共同输入域上的局部等价；随后 `refinement_preserves_representation` 保持网络表示。

所以，对当前较宽关系，外延保持定理有充分依据。它证明的是一个范围更广的充分条件；证明成立并不能反过来保证该关系精确刻画正文定义。

还应区分两种接口：

- 关系型定理以已经合法的 `N`、`N' : FiniteOperatorNetwork` 为参数，本身不负责构造 `N'`。
- `NodePartitionData.presentation` 和 `network` 确实从分划及局域算子数据构造新网络，并证明其合法性与外延相等。

因此，不能将附件评价为“只假设加细结果存在，没有实际构造”。

**4. 删冗余处理正确，但修复关系时不能简单扩大 `choice_projection` 的量词。**

[prune 的实现](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR01/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:76) 保留可达节点的整个局域算子，只将指向已删除节点的选择改为 `stop`。它证明了路径标签及求值保持。

这意味着：

- 两个保留节点之间的边域应完全保持删前数据；
- 指向被删除节点的边消失；
- 保留节点的终止域可能扩大。

故正文中的
\[
T^{\mathrm{pre}}_{\beta_a}
=f_{\beta,a}(A_a)\cap T_\beta
\]
是**删冗余前**的公式，不能无条件套用到删后网络。正文证明已经明确作了这个阶段区分。

也因此，直接要求整个 `N'.node_image` 上的选择投影都与原选择相等，会错误排除合法剪枝：原选择可能指向已经删除的子节点。当前字段的放宽有合理动机，但放宽到了允许任意改动其他未使用边的程度。

**5. 修复方向与尚需补充的内容。**

建议将准确的节点域加细关系建立在**保留端点的完整边域等式**上。沿用当前节点对应及局域算子条件，要求对所有保留节点 \(v,w\)：

\[
\boxed{
D'_{v\to w}
=
D_{\pi(v)\to\pi(w)}
\cap f'_v(\operatorname{dom}f'_v)
\cap\operatorname{dom}f'_w
}
\]

这既覆盖三类交集公式及不关联边不变，也兼容删除不可达节点。当前的实际输出路由相容性可以作为由此推出的辅助结论。

另外，附件尚未给出将 `NodePartitionData.network` 接入 `NodeDomainRefinement` 的桥接定理。应补充：

- 构造结果满足修正后的精确加细关系；
- 保留子节点恰好对应 `NodePieceReached`，其他旧节点全部保留；
- 入口、完整边域及删前／删后终止域的对应公式。

也可以把精确关系定义为：经过标签重命名后，结果的原始 `presentation_data` 与规范构造相同。比较原始数据比要求整个 Lean 结构相等更合适，因为终止界、证明见证及局域输出像外的选择不属于正文网络数据。

这些属于定义和接口的补充。**具体构造已经证明的 `network_extensional_eq` 不需要被否定或重新解释为未完成。**

本次采用源码静态审阅，并对上述四点反例作了有限枚举核验；未重新运行 Lean 编译，未修改附件或新增 Lean 源码。

材料来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。判断仅针对所附版本。