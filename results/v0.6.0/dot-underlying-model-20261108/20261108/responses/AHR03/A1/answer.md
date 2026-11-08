# 审阅结论

在本题限定的范围内，所给实现准确、完整地覆盖了正文的节点域加细，以及该加细在删除冗余节点后保持外延等价的结论。这里必须同时看 `network_refinement.lean` 和 `domain_refinement_construction.lean`，不能只看辅助关系 `OperationalNodeDomainRefinement`，也不能把删点前的终止域等式误套到删点后。

我用附件提供的 `lean-local`，按导入依赖顺序检查并编译了 `domain_refinement_construction.lean` 及其 23 个附件内依赖文件，全部通过。所检查附件 Lean 源文件中未发现 `sorry`、`admit` 或自定义 `axiom`。下文的数学覆盖判断另依据实际定义和证明内容，不仅依据编译成功。

## 1. 分划与子节点算子

`NodePartitionData` 的字段逐项对应正文：

- `count`、`count_pos`、`piece : Fin count → Set X` 给出有限、至少含一片的分划；`nonempty` 要求每片非空。
- `disjoint`、`cover` 要求片两两不交，且并集恰为原节点的**完整定义域** `N.node_dom target`，不是入口片或实际发生域。
- `local_domain` 要求子算子的定义域恰为该片；`local_eq` 要求其在该片上与原算子逐点相等。

这里 `dom φ = {x | φ.func x ≠ bot}`，`LocalEquivalent` 是函数值相等，不是伪度量零距。因此片外子算子必取 `bot`，没有把“局部相等”误当作全域相等。`local_op_eq_restrict` 已证明

\[
f_{\beta,a}=f_\beta|_{U_{\beta,a}}.
\]

一般关系 `NodeDomainRefinement` 继承的对应字段表达同一要求。实现没有添加原算子单射、子片输出像互斥、网络无环等正文不要求的前提。

## 2. 节点标签与冗余子节点

构造首先使用标签

\[
\{v\in V:v\ne\beta\}\sqcup\operatorname{Fin}(q),
\]

即保留其他节点、用子片标签替换目标节点。随后 `presentation.prune` 只保留被入口终止轨迹经过的标签，保留这些节点的完整局域算子，并删除涉及被删标签的边；这不是将所有局域算子限制到实际发生域的“有效约化”。

`old_label_reached` 证明每个未替换旧节点仍被经过。`piece_label_reached_iff` 证明子片保留当且仅当原轨迹某次经过目标节点时，其当前输入落在该片中。其右端 `NodePieceReached` 使用路径中的位置以及该位置之前的链求值，故不是只检查初始输入是否落在子片中。

关系中的 `source_injective`、`old_node_present` 和 `piece_node_present_iff_reached` 因而恰好描述删点后的标签集合。特别是它没有要求所有分片均保留，没有漏掉正文允许的不可达子片删除，也不能任意删掉仍被经过的子片。

## 3. 入口片和全部保留边

`entry_projection` 配合入口合法性、分片互斥性及标签单射性，推出已证明的 `NodeDomainRefinement.entry_domain_eq`：

\[
U_v^{\prime\mathrm{in}}=U_{\pi(v)}^{\mathrm{in}}\cap U'_v.
\]

旧节点的定义域未变，因此它们的入口片不变；子节点入口片正是原目标入口片与子域的交。入口节点可由非空入口片恢复，空片不产生入口节点。

关键是正式关系 `NodeDomainRefinement` 额外要求

\[
D'_{v\to w}
 =D_{\pi(v)\to\pi(w)}\cap f'_v(U'_v)\cap U'_w
\tag{*}
\]

对**每一对保留标签**成立。`network_edge_domain_eq` 已对实际构造证明这个等式，`retained_edge_mem` 则给出了其中的保留方向。这不是仅对实际求值经过的边点成立。

由原边域包含于源像和目标域，(*) 分别化为：

1. 两端都是未替换旧节点：原边域不变。
2. 旧节点到子节点：\(D_{\gamma\to\beta}\cap U_{\beta,a}\)。
3. 子节点到旧节点：\(D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})\)。
4. 两端都是子节点：\(D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}\)。

这正是正文四种情形，尤其覆盖了自环的源片与目标片同时细分。`self_loop_choice_iff` 还直接证明了对应的路由性质。空边以空边域表示，实际 `Edge` 定义要求边域非空，符合正文省略空边的约定。

`OperationalNodeDomainRefinement` 的确只约束实际发生输出上的路由，单独使用会太弱；但正式关系继承它并加入了 (*)，而构造证明了正式关系，故这个辅助定义不是本实现的覆盖漏洞。

## 4. 自环、重复发生与统一终止

`lift_label v x` 按**当前点**选择子片；`colour_path` 的递归形式为

\[
(v::p,x)\longmapsto
\operatorname{lift\_label}(v,x)::
\operatorname{colour\_path}(p,f_v(x)).
\]

因此同一原节点在不同位置可以被染成不同子节点，既允许自环，也允许经过其他节点后回访目标节点，不把原节点一次性固定映到某个子片。

具体证明链为：

- `mem_piece_at`、`piece_at_unique`：当前输入属于唯一子片；
- `lift_mem_dom`、`lift_apply`：提升后的状态合法，局部输出与原来相同；
- `choice_next_mem`：新后继仍满足目标定义域条件；
- `coloured_terminal`：原终止轨迹变成新终止轨迹；
- `coloured_eval`：该轨迹的最终输出相同；
- `colour_path_length`：轨迹长度不变。

`presentation` 据此构造 `FiniteNetworkPresentation`，继承原 `depth_bound`，证明所有输入共用这个长度界。它没有把“加细后已是有限网络”当作待证结论的替代前提。`prune` 再补足无冗余节点条件，得到真正的 `FiniteOperatorNetwork`。

`network_path_labels` 和 `network_path_projection` 证明删点后路径仍是原路径的逐发生染色，并且投影恢复原路径。故逐输入长度相等；正文以实际路径最大长度定义的求值深度也相等。这不要求结构中任意存储的上界字段必须是最小上界。

## 5. 删除前后的终止域必须区别

正文先在**尚未删冗余节点**的数据上证明

\[
T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta,
\]

其他旧节点终止域不变。这由全部子片覆盖原域以及全部新边交集公式得到：原输出若应进入目标节点，就进入包含该输出的唯一子片；原输出若应终止，新路由也终止。

源码通过 `choice` 对原 `stop/next` 的提升和 `coloured_terminal` 实现这一论证，没有必须依赖上述集合等式作为单独命名引理。删点后，`prune_choice` 把指向被删节点的选择改为 `stop`；保留节点之间的全部边仍由 `prune_choice_next_iff` 保持。`prune_path_labels`、`prune_eval` 和 `prune_extensional_operator_eq` 已证明实际轨迹和输出不变。

所以 `choice_projection` 只要求在实际发生输出上成立是正确的。不能把它加强为删点后整个局域像上的原路由保持，也不能要求删点后仍满足上述原终止域交集等式。

一个可复核的例子说明这个区别。取

\[
X=\{\bot,0,1,2\},\qquad
f(\bot)=\bot,\quad f(0)=0,\quad f(1)=2,\quad f(2)=0.
\]

原网只有一个节点 \(\beta\)，节点域为 \(\{0,1,2\}\)，入口域为 \(U=\{0\}\)，自环边域为 \(\{2\}\)。唯一入口轨迹在一次调用后输出 0 并终止，节点可达，统一长度界为 1，因此是合法有限网络。

分为 \(A=\{0,1\}\)、\(B=\{2\}\)。删点前有边 \(A\to B\)，域为 \(\{2\}\)，且 \(T_A=\{0\}\)。但 B 不被任何入口轨迹经过，必须删除。删点后 A 没有出边，终止域为 \(\{0,2\}\)，而原终止域与 A 的输出像之交仍为 \(\{0\}\)。两网在唯一入口输入 0 上输出完全相同。

这不是实现或正文的反例，而是对“删点后完整终止域仍不变”这一过强要求的反例。相反，若取单片分划而擅自删去原来未实际使用的自环，只有操作性条件可能允许它，正式关系的 (*) 会排除它。可见“删除不可达节点”和“删除未使用的保留边”在源码中有正确区分。

## 6. 外延结论与证明边界

源码提供了两条闭合的证明路线：

- 一般关系路线：`NodeDomainRefinement.terminal_projection`、`path_projection`、`eval_projected` 推出 `NetworkRefinement.path_eval_eq`，再由 `refinement_preserves_local_equivalence` 得到正文所需的
  \(\phi_{N'}\equiv_{N.U}\phi_N\)。
- 构造路线：对任意 `NodePartitionData`，构造 `P.network`，由染色求值和剪枝保持求值得到 `network_extensional_eq`。它证明全域算子相等，比只在 U 上局部等价更强；域外双方均取吸收元。

`network_refinement` 把构造结果装入精确的 `NodeDomainRefinement`，`allowed_network_refinement` 再装入 `NetworkRefinement.node_domain`。因此不仅证明了“如果提供一个合适证书，则输出相同”，还证明了正文给定的任意合法分划数据确实产生这种证书及有限网络。路由相容字段没有掩盖未完成的存在性证明。

需要区别的是：本文上面按四类边展开 (*)、写出删点前终止域集合等式、以及由逐输入长度相等读出最大实际深度相等，是对已有源码的数学解释或直接推论；相关文件不一定为每个展开式各自提供独立命名定理。若需要以这些式子为后续 Lean API，可补充相应引理，但这不是本题外延保持命题的证明缺口。也无需为本题补充代数加细、L/K/N 比较或不可约代表存在性等其他范围的结论。

综上，没有发现本题限定范围内需要修复的数学遗漏或错误。最重要的核对点是：完整节点域的分划、全域局域算子限制、保留边的完整交集公式、自环按发生位置重新选片，以及严格按可达性删子节点；这些均已被所给实现覆盖。

---

材料来源：Zhe Li（Glen Li / glenzli），《The Operator Evolution Theory》，https://glenzli.com/books/oet/ ，CC BY 4.0（https://creativecommons.org/licenses/by/4.0/）。以上为对所附版本的审阅，不涉及当前版本的完成情况。本次没有修改附件数学正文或 Lean 源码，也没有新增需交付的 Lean 源文件；最终交付物即本审阅报告。
