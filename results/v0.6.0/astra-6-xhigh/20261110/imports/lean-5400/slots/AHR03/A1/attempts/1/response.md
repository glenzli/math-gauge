**结论：在本题限定的“节点域加细及其保持外延等价”范围内，所给实现准确、完整；未发现实质数学缺口。** 判断依据包括加细关系的定义、从分划数据构造新网络的过程，以及构造满足该关系的证明。

我用附件指定的 Lean 4.29.1 编译了相关实现及依赖共 26 个模块，全部通过，且未发现 `sorry`、`admit` 或新增公理。未修改附件、未新增 Lean 源码。编译验证与下述数学对应审查分别提供依据。

1. **分划及子节点算子与正文一致。**

   [NodePartitionData](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:12) 的 `count_pos`、`nonempty`、`disjoint`、`cover` 分别编码分划指标非空、各片非空、两两不交及覆盖**完整节点定义域**。分划没有被限制为节点的实际输入域，也没有要求各片本身为有限集。

   `local_domain` 要求定义域恰好等于分片；`local_eq` 要求片内逐点相等，与正文的局部等价一致，并非仅要求规范零距离。源码的 `local_op_eq_restrict` 进一步证明
   \[
   f_{\beta,a}=f_\beta|_{U_{\beta,a}}.
   \]
   其域外相等来自：不属于算子定义域的点必须映到吸收元。因此子节点算子没有额外的域外延拓自由度。

2. **入口规则准确，包括空入口片的处理。**

   构造中的入口为 `lift_label (N.entry x) x`，按当前输入唯一选择分片。关系中的 `entry_projection` 配合入口合法性、分片互斥及标签单射性，已推出
   \[
   U_v^{\mathrm{in}\prime}
   =U_{\pi(v)}^{\mathrm{in}}\cap U'_v
   \]
   ——即 [entry_domain_eq](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:283)。

   对未替换节点，右侧化简为原入口片；对子节点，正是正文的入口交集。空入口片由空集合表示，不会强迫该节点成为入口，也不会仅因入口片为空而删掉仍能由入边到达的节点。

3. **完整边域公式覆盖全部四类边，包括未使用边和自环。**

   [NodeDomainRefinement.edge_domain_eq](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:118) 要求，对任意两个保留节点，
   \[
   D'_{v\to w}
   =D_{\pi(v)\to\pi(w)}\cap f'_v(U'_v)\cap U'_w.
   \]

   利用原边域包含源输出像、目标定义域，这一统一公式逐项化为：

   | 边的类型 | 化简后的边域 |
   |---|---|
   | 两端均未替换 | 原边域 |
   | 原节点进入子节点 | \(D_{\gamma\to\beta}\cap U_{\beta,a}\) |
   | 子节点进入原节点 | \(D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})\) |
   | 原自环产生的子节点间边 | \(D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}\) |

   公式作用于**完整局域输出像**，没有仅保留实际轨迹经过的部分。空边域对应无边，符合正文约定。构造的 `network_edge_domain_eq` 已证明该公式，`network_refinement` 将其填入正式加细关系。

   `OperationalNodeDomainRefinement` 确实较弱；源码明确将它作为辅助层。正式的 `NetworkRefinement.node_domain` 接收的是包含完整边域条件的 `NodeDomainRefinement`。

4. **允许回访，同一节点的不同发生可选择不同子节点。**

   `colour_path` 每执行一步，都用原节点输出更新当前点，再为下一次发生选择标签。因此它依据的是该次发生的当前输入，而非初始输入或第一次选中的分片。

   `colour_path_get` 明确给出第 \(n\) 个新标签：
   \[
   \operatorname{lift\_label}
   \left(p_n,\;N.\operatorname{chain\_eval}(p.\operatorname{take}n,x)\right).
   \]
   `self_loop_choice_iff` 同时核对目标分片的选择。底层使用 `FiniteOperatorNetwork`，没有加入无环秩或路径无重复假设，故正文允许的自环和多次回访均在范围内。

5. **新网络的存在与合法性已由构造证明。**

   [presentation 与 network](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean:208) 从任意符合正文条件的 `NodePartitionData` 出发，依次建立：

   - 有限节点类型及非空局域定义域；
   - 合法入口和合法后继；
   - `coloured_terminal` 给出的终止路径；
   - `colour_path_length` 给出的路径长度不变；
   - 原统一长度界仍适用；
   - 经 `prune` 得到满足无冗余条件的有限网络。

   随后 `network_refinement` 和 `allowed_network_refinement` 证明该构造属于所定义的加细关系。因此，虽然通用关系以两个已合法的网络为参数，附件整体已经补齐了从正文分划数据到合法结果网络的构造环节。

6. **删除的是不可达子节点，保留节点间的未使用边不会被误删。**

   `old_label_reached` 证明所有未替换旧节点仍可达；`piece_label_reached_iff` 证明子节点保留当且仅当原轨迹某次进入其分片。这里检查的是所有路径位置，而非只检查入口。

   [prune_choice_next_iff](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_presentation.lean:44) 保证两个保留节点之间的完整路由不变。删点仅移除不可达标签及其关联边，与正文相符。

   **删点前后的终止域必须区分。** 正文证明中的
   \[
   T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta
   \]
   明确用于尚未删点的加细数据。删点后，完整终止域可以扩大；源码因此只在实际输出上要求 `choice_projection`，这是正确处理。

   一个可复核的例子是：取互异点 \(\bot,a,b,c\)，单节点算子满足
   \[
   f(a)=a,\quad f(b)=c,\quad f(c)=c,\quad f(\bot)=\bot,
   \]
   输入域为 \(\{a\}\)，自环边域为 \(\{c\}\)。它是合法有限网络，唯一入口轨迹一步终止。按
   \[
   A=\{a,b\},\qquad B=\{c\}
   \]
   分片后，\(B\) 不可达并被删除。保留节点 \(A\) 的终止域由删点前的 \(\{a\}\) 扩大为 \(\{a,c\}\)，但实际输入 \(a\) 的求值不变。

   这说明不能要求删点后在全部局域输出上保持原 `stop/next`，也不能把删点前的终止域等式直接用于最终网络。附件没有作这两种过强要求。

7. **外延等价结论是推导所得，证明链覆盖正文命题。**

   通用节点域分支的证明依次为：

   \[
   \texttt{node\_eval\_eq}
   \;\longrightarrow\;
   \texttt{terminal\_projection}
   \;\longrightarrow\;
   \texttt{path\_projection}
   \;\longrightarrow\;
   \texttt{path\_eval\_eq}.
   \]

   其中路径投影相等由确定路由下的终止路径唯一性推出。随后 [refinement_preserves_local_equivalence](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR03/physical-1/work/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean:453) 得到正文所需的
   \[
   \forall x\in U,\qquad
   \phi_{\mathcal N'}(x)=\phi_{\mathcal N}(x).
   \]

   对实际构造，`NodePartitionData.network_extensional_eq` 还直接证明了**全域算子相等**，同时处理 \(U\) 外两侧均为吸收元的情况。`refinement_preserves_representation` 则已证明网络表示随加细保持。

   通用外延证明主要使用局域作用与实际路由条件；完整边域字段负责限定正文允许的变换范围。构造又独立证明这些字段，整个论证不存在把最终外延相等当作前提的循环。

8. **前提没有实质缩小正文范围。**

   实现未要求规范分离、Lip/co-Lip 证书、节点域等于实际输入域、所有边均实际使用，或网络无环。底层规范结构对这个逐点相等结论并非必要。

   虽然部分定理没有显式写 `U.Nonempty`，节点域加细包含目标节点，而原网络的 `node_reachable target` 已推出输入域非空。空网络没有可供选择的目标节点，符合正文语义。

   任意有限标签到编号网络的处理已有重编号和 `encode_extensional_operator` 等保外延结果支持，也不构成范围缺失。

**源码已证明与可补充封装的界线如下。** 分划限制算子等式、入口交集、完整保留边公式、可达子节点判据、合法网络构造、路径投影、局部外延等价以及构造结果的全域算子相等，均已有直接声明与证明。

附件没有将每个自然推论都单独命名，例如任意 `NodeDomainRefinement` 的全域算子相等、实际求值深度相等、删点前的终止域交集等式，以及对象层专用的加细接口。这些可由现有结果补成便利定理：分别使用同域且域外取吸收元、逐输入路径长度相等、出边并集取补集，以及现有编号编码。**它们属于可补充的接口封装，不是本题命题尚欠的数学条件或证明。**

材料归属：Zhe Li（Glen Li / glenzli），《The Operator Evolution Theory》；[官方页](https://glenzli.com/books/oet/)、[ORCID](https://orcid.org/0009-0006-6536-3453)、[源码仓库](https://gitlab.com/glenzli/oet-public)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以上判断仅针对所附历史材料。