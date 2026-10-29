# F104 最小修订的独立复核

复核日期：2026-10-30。复核者为独立 AI 子任务。完整阅读当前 F104 题面、参考、rubric、两份原答卷、两组诊断源码及日志；未重新编译、未调用答题模型、未改仓库或原成绩。本记录不是人工审定。

**结论：Terra 的诊断副本确实只改一行，修后保持原题全部数学目标，保存的编译和全部 12 声明公理审计证据一致。原始答卷仍是编译失败。Gemini 的诊断只补了 U，但继续暴露 Candidate 的 API 名称错误，不能称为已修完。没有发现 F104 题目本身的数学错误。**

## 证据身份与唯一差异

Terra 原件：`results/full-comparison-20261030/answers/d1c7f20dc8f5/lean/submitted/`。
诊断件：`results/failure-analysis-20261030/f104-diagnostic/sources/`。

- Core.lean 和 Candidate.lean 逐字节相同。
- Construction.lean 唯一差异为第 19 行：`exact bot_le` 改为 `exact TopologicalSpace.instCompleteLattice.bot_le _`。
- 独立生成的 unified diff 与 `minimal-change.patch` 逐字相同。
- 原答卷、原报告及三份原源码均与保存 SHA-256 相符。
- 诊断报告中 Core、Construction、Candidate、Audit 的源码和日志共 8 项哈希全部相符，四项记录退出码均为 0。
- 报告固定的实际 `Mathlib/Topology/Order.olean` 文件哈希相符；Lean 版本、Mathlib 修订与原核验一致。
- 归档请求中的 F104 0.1.0 题面与当前题面逐字相同。

Terra 原错误是 `OrderBot (TopologicalSpace X)` 的实例综合失败。探针日志同时显示 CompleteLattice 能被取得，但该裸 `bot_le` 调用的 OrderBot 综合失败。修订通过现有 CompleteLattice 实例的字段投影提供同一条底元不等式；未改定理签名、数学构造或增加公理。不能据此把问题归因于数学命题不成立，也无需将题目改成更强假设。

关键哈希：

| 证据 | SHA-256 |
| --- | --- |
| 原 Terra 答卷 | `27d6c0be23651c1fd39d648e86e0295a4990a20a31cbd31c65efbf2f70047ea3` |
| 原 Construction | `97fe450cfd740bab6c8564915f759679406336b8ca052c6b87a326efc1129a59` |
| 修后 Construction | `97c308167d15e1771e32220806adbc1a2219d1effd4b54d798f4c90b9f73ce9f` |
| 诊断 report.json | `11668ef85f5c7aa7bb3427ae96c04ffef0363564296b3bd9ca88a5fd418300b6` |
| Audit.log | `384f8195270d321e86c96d15e24e8fa4aa3c66a73d1789e9a076bf969cba605e` |

## Terra 的数学与语义对应

1. **对象不变。** 指标类型、底集、依赖目标类型族及各拓扑均任意；映射不要求单射或满射，空间不要求分离、非空或有限。
2. **原附件诊断正确。** 可行拓扑族包含离散拓扑，故其 Mathlib 下确界为底。原答卷给出的空指标集、两点集合及不可分拓扑恒等映射是合法反例；无须强迫其改用作者的单点指标例子。
3. **构造真实存在。** 修后的 `assembled` 把开集定义为在每个可行拓扑中均开的集合，并给出全集、有限交、任意并封闭性的证明。它不是把“最粗性”假装成输入字段。
4. **连续性与最粗性均已证明。** 各目标开集逆像在任一可行拓扑中开，所以属于构造；对任一可行 s，有 `s ≤ assembled`，即构造开集包含于 s 的开集，方向符合 Mathlib 反序。
5. **存在唯一性完整。** `existsUnique_coarsest` 构造实例并证明任意另一可行且最粗的拓扑等于它。`construction_unique` 的 hcoarse 是用于比较的另一个最粗拓扑的性质，不是给原始输入偷加前提。
6. **双向映射性质完整。** 前向用连续映射复合。反向定义 `q = coinduced g s`，仅凭所有复合连续证明 q 可行；构造的开集因而在 q 中开，按 q 的定义，其 g 逆像在源拓扑开。这里没有循环假设 g 连续，也不需要 g 满射。
7. **退化情况保留。** 空指标集、空底集仍被泛型声明覆盖。空指标集时所有拓扑可行，构造是不可分拓扑，映射性质两侧均成立。

源码定位：Construction.lean:12 原提交缺陷；:25 构造；:41 连续性；:59 最粗性；:68 唯一性；:79 存在唯一。Candidate.lean:12 前向；:24 反向；:49 完整充要条件。

## 公理审计是否覆盖全部 12 声明

是。Audit.lean 与原候选审核模板逐字相同，按 Core、Construction、Candidate 的实际模块来源枚举声明，包含 `constNames` 和 `extraConstNames`，不靠命名空间或仅两个最终定理筛选。记录列出 **10 个手写声明与 2 个 elaborator 生成证明**，共 12 个无重复名字。独立扫描三份源码的 10 个手写声明均在清单中。

- Core：Realizes。
- Construction：submitted_sInf_eq_bot、assembled、candidate_realizes、construction_bound、construction_unique、existsUnique_coarsest；另有 assembled._proof_1、assembled._proof_2。
- Candidate：candidate_inbound、candidate_outbound、candidate_mapping。

收集这些声明全部依赖后，公理并集为 `Classical.choice`、`Quot.sound`、`propext`，与候选合同白名单一致；`unexpected_axioms=[]`、`passed=true`。原失败处的诊断引理 `submitted_sInf_eq_bot` 也包含在审计中，没有因为它不被最终定理使用而略过。

这表明保存的本次审计覆盖完整交付模块；语义对齐由上述逐项阅读另外确认，不能单由“12 个声明通过”推出。

## Gemini：只补 U 后的失败边界

原件为 `answers/6ec046237f89/lean/submitted/`，诊断目录为 `f104-gemini-diagnostic/`。独立 diff 确认唯一改动是 Construction.lean:34，在调用 `construction_bound` 时给 hU 前补显式集合 U。Core 与 Candidate 未变。原答卷、原报告、原源码、诊断源码和日志哈希全部一致；归档题面也相同。

保存的后续结果是 Core、Construction 成功，Candidate 失败：

- Candidate.lean:42：`TopologicalSpace.induced_iInf` 是未知常量。
- `candidate_outbound` 未完成，`mapping_property` 依赖它；日志里这两项的公理含 `sorryAx`。这来自失败 elaboration 的占位，不表示候选文字直接写了 `sorry`。
- 没有 Audit 执行条目或 Audit.log，不能宣称全声明公理审计通过。

固定依赖源码 `Mathlib/Topology/Order.lean:473` 中对应结果实际名为根命名空间的 `induced_iInf`。后续 :505 的 `induced_compose` 也在根命名空间且参数为隐式，候选后面仍写了 `TopologicalSpace.induced_compose g (f i) (t i)`；本次没有执行进一步修订，不宣称剩余问题只需某一处改动即可全部通过。数学上的“induced 保持下确界并与复合相容”路线成立，当前直接证据指向 Lean API/命名使用问题，而不是初始拓扑定理为假。

Terra 原答卷明确承认未在固定环境编译；Gemini 原答卷则把所有项标成完成并称没有未完成部分。该差别可以单列为完成声明的准确性，不能代替编译成绩。

## 结论边界

这是一项独立源码、语义及归档证据复核，没有重新运行 Lean，也不将诊断当成一次新模型答题。保持两份原答卷的 compile_error 和原比较成绩；Terra 可记录为“数学/对齐正确，一处接口修订后诊断通过”，Gemini 可记录为“首处接口修订后仍有下游编译错误，完整修复未验证”。本报告未做进程隔离重演，也未声称重新验算全部传递依赖二进制。
