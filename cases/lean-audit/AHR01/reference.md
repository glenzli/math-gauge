# 本题范围与独立审核参考

主推：实际轨迹相同不等于教材定义的节点域加细

**精确冻结**：旧提交 `12e1b7cbe588f69a43bc32ae04e8052685287a46`；后继修复 `0cf686ba848e19137821ee9a56c9c04ee146746e`。

|材料|仓库相对路径|旧 Git blob|
|---|---|---|
|旧 Lean|`the-operator-evolution-theory/formal-oet/formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean`|`80908803ca112e32cc2e1ea4f082fa80abd95337`|
|同提交整章原文|`the-operator-evolution-theory/vol-01-gauge-spaces-and-operators/05-operator-networks.md`|`2f26294967ae8b6db1cf55349bc7fb97192744e7`|

旧 Lean SHA-256 为 `f1d877203d97821246482b98d20b623216fd47e6de4b254d27403cd212e62f8a`。旧文 SHA-256 为 `d62fdcd26734d0c9de361e95bd5b5a43094b11df7d9c406fb36ef2ca35955e63`。原字节、完整章、构造模块及后继 diff 均在 `network-refinement/`；逐文件身份见 `source-manifest.json`、`additional-source-manifest.json`。

**具体差异**：同提交正文 `h-eddd1f2d0a9d3528` 要求按完整局域定义域和输出像构造边域。例如原入边必须变为

\[
D'_{\gamma\to\beta_a}=D_{\gamma\to\beta}\cap U_{\beta,a}.
\]

旧 `NodeDomainRefinement` 第 73 行起给出大量合法条件，但第 108 行的 `choice_projection` 只检查

\[
z\in f'_v\bigl(D^{\mathrm{actual}}_v\bigr),
\]

即真实入口轨迹实际遇到的输出。它允许改变两个保留节点之间、从未实际遇到的边域。后继修复将旧结构改名为 `OperationalNodeDomainRefinement`，新 `NodeDomainRefinement` 增加所有保留节点对的完整 `edge_domain_eq`，并在 `domain_refinement_construction.lean` 中证明实际构造满足该关系。

**完整有限反例**：取底空间 `{bot,a,b,c}`，输入域 `{a,b,c}`。可用一个规范分量：非吸收异点之间距离 1、到 bot 距离无穷、自距 0，得到合法扩展规范空间。所有下列局域算子在其域内恒等、域外取 bot。原节点为 A、B：

|节点|局域定义域|入口片|出边|
|---|---|---|---|
|A|`{a,c}`|`{a}`|在输出 c 处进入 B|
|B|`{b,c}`|`{b,c}`|无|

将 B 分成 B_b（域 `{b}`）和 B_c（域 `{c}`），二者入口片分别为 `{b}`、`{c}`，保留 A 的局域算子和入口片，但在新网络中删除全部边。两网全部入口轨迹长度都是 1，所有节点实际可达，输出均为原输入；A 的实际输入、输出都只有 a。于是旧关系的每个证明字段都成立，包括分划、局部等价、标签单射、保留节点、入口投影、实际输出处的后继投影。但原文要求

\[
D'_{A\to B_c}=\{c\}\cap\{c\}=\{c\},
\]

新网络给出的该边域为空。B_c 本来就由输入 c 进入，不能以删除不可达子节点解释这一差异。A 的终止域也因此被错误扩大。

运行 `python3 check_finite_counterexamples.py` 会逐一检查两份有限网络的合法性、旧结构的 14 个证明字段、入口输出相等，并输出唯一失败边 A→B_c。有限模型对应旧 Lean 定义，但没有在 Lean 中实例化整个旧 record；这一限制保留在机器结果中。

**应当给分的准确判断**：旧的外延等价定理本身有效；错误在于声明的关系未完整表达正文定义。不能说“两网络输出不等”，不能以任意未使用边都可删除为理由判定完全对齐，也不应凭缺少某个包装声明否认已有构造。旧构造模块已经实际生成网络并证明 `network_extensional_eq`；后继精确桥梁是额外改进。出题需同时提供旧构造模块，避免通过裁掉正确材料制造缺口。

**建议无提示题面**：见 `network-refinement/candidate-prompt.md`。范围明确限定为节点域加细的定义及该分支的外延等价；同章和完整相关 Lean 源码只提供数学材料，不给修复 diff、反例、审阅记录或历史结论。必需判准为：正确识别保留节点、完整边域与实际发生域的范围；准确保留已证外延等价；给可复核差异证据；给完整域边等式或等价的修复路线。合法替代证据可接受，不要求复制本反例。

**编译证据**：旧 `network_refinement.lean` 及其 22 个本地相关模块全部原样重新编译，均 exit 0。额外提供的构造/导入模块的编译另见 `additional-build-evidence.json`。工具链 Lean 4.29.1，提交 `f72c35b3f637c8c6571d353742168ab66cc22c00`；Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。没有使用当前 OET 项目构建库替代旧模块。



许可与来源完整身份另见provenance.json。有限反例为数学模型检查，非Lean记录实例化证明；原样编译不等于语义完整。
