# OET 整章形式化考试 · 0.1.1

0.1.1 清理了候选题面的分值、判卷提示和后序泄露的判断答案，并明确 audit 的书面交付范围；数学义务、权重、参考和 Lean 输入不变。旧材料与原复核保存在[0.1.0历史快照](history/0.1.0.json)，当前题面通过[编辑等价记录](reviews/editorial-amendment-0.1.1.json)衔接原数学复核。执行与评分采用[重复作答协议](../../protocol/reliability-execution.md)，八题子集见[选择说明](../../protocol/reliability-20261030/selection.md)。

本目录把两份整章草案具体化为可由共享 runner 接收、逐项审核的考试合同。数学原文与允许的外部 Lean 定义保持冻结；考试范围、提交格式、背景不可修改规则和判卷门槛均明确。旧草案仍保存在 `../long-form-design-20261030/`，新题不进入原41题成绩。

| 试卷 | 候选题面 | 必答义务 | 出题侧参考 |
|---|---|---:|---|
| MG-C002：卷1第2章算子界 | [task](MG-C002/candidate/task.md) | 34：8组定义/表示 + 26证明 | [reference](MG-C002/reference.md) · [contract](MG-C002/contract.json) |
| MG-C003：卷1第3章局部退化 | [task](MG-C003/candidate/task.md) | 92：8组定义/表示 + 84证明 | [reference](MG-C003/reference.md) · [contract](MG-C003/contract.json) |

第3章将30个原有源单元继续按方向、分项、构造合法性及边界拆清；章末五题给出完整计算与论证。第2章明确有限链证书、乘积次序和路径表示的桥接。数学上的有效短证、通用有限索引表示及不同分解均可接受，不把“与作者代码不同”当错。

候选接收完整章节（包括自然语言证明）、前置章节、冻结背景模块、公开义务清单及许可证。第2章8个附件、第3章13个附件；参考、评分、作者实现位置、审核状态和历史结果不进入请求。背景模块在消息中使用其真实 `formal_oet/...` 模块路径，无需改写源文件。`candidate/` 是材料存放位置，唯一投影以case.json的solver_files为准。

提交要求是所有自建完整Lean模块、统一入口Main.lean、逐义务alignment.json。声明名不强制复刻作者，但每项通过都要映射到该答卷中实际审计过的声明，并经语义审核。全章统一编译和全部义务完成才通过；不能拿背景编译或少数命题通过替代。详见[逐阶段判卷协议](../../protocol/question-groups.md)。

```sh
python3 -m math_gauge validate --suite drafts/chapter-exams-20261030
python3 -m math_gauge prepare --suite drafts/chapter-exams-20261030 --case MG-C002 --out runs/chapter02
```

来源为公开OET提交539b40cec73184d98e06d54fbd10e4b4698bd6e7，CC BY 4.0，作者Zhe Li / Glen Li / glenzli。Lean固定4.29.1，mathlib固定5e932f97dd25535344f80f9dd8da3aab83df0fe6；逐文件来源与散列见各题provenance.json。基础模块原有编译证据仅在字节与环境完全相同的范围复用。先前设计说明作为历史审计材料保留，不覆盖本版考试合同。

当前是 **draft / human pending**，没有新模型答卷或通过率。考试合同的完整性与目标章作者Lean的完整覆盖是两件事：本版已有完整自然语言参考、明确考试及判卷约束；尚未据此宣称第2/3章全部新义务的作者Lean实现已经逐项对齐、编译并独立审定。这个边界保存在case、contract和来源记录中。

两章126项义务已完成[独立AI复核](reviews/README.md)，数学范围、逐项参考与考试合同的发现均已闭环。共享runner也已执行清单完整性和声明身份检查：缺少alignment.json、ID不齐、与答卷不符的声明映射不能通过，incomplete不能被评审抬为完整完成。允许直接复用背景定义的CH03-D07已在公开义务清单标明。
