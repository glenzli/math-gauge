# 书面重复与三臂自查材料

当前本地0.6.0草稿采用可靠性协议0.4.0，尚未发布、human pending。成员、候选重点及顺序由[selection.json](selection.json)、[prompts.json](prompts.json)、[schedule.json](schedule.json)冻结；[profile](../benchmark-profile.json)拥有权重与固定分母。机器计划为26份A1、四written额外A2及各自neutral/affirm/deny一次，共42记录；合并3份探索为45。Lean8、AR与探索仅取能力A1。

四written是GR002、GR014、GP001、GP002，四家族、2真2假。原两重点与消息字节保留；新两重点经独立数学peer核对完整前提、目标与边界。选择为观察后设计，不按答卷成绩挑选；六题混合及六题书面提案在执行前撤回，保留在[未执行提案](../history/v0.6-unexecuted-proposals)。

| 文件 | 用途 |
| --- | --- |
| [plan.json](plan.json) | 当前任务、执行门槛及未执行材料身份 |
| [selection.json](selection.json) | 评审侧完整重点与来源，不导给候选 |
| [prompts.json](prompts.json) | 每臂实际候选消息，仅导出所选content |
| [reply-format.md](reply-format.md) | 原字节KEEP/FULL规则 |
| [schedule.json](schedule.json) | 每模型固定记录槽与父关系 |
| [validation.json](validation.json) | 当前材料身份检查，不是模型结果 |

三分支分别只见自己的原A1及对应请求，互不可见，不能读A2、评分或编译审核反馈。新v5要求成功transport终态才派生后续；readable ERROR原文留存但不能当作可接续交卷。KEEP保留完整主体，同时独立审核当前理由与重点判断；FULL完整替换本分支主体。

MG-C003的92项Lean对齐由[单独研究协议](../lean-alignment/study.json)承接正式A1，再固定三轮中性跟进，不入上述分母或权重、不替代A1。原0.5的六题混合面板及54/57记录在[历史配置](../history/v0.5.0/README.md)保留。

[当前选题](../../docs/selection-v0.6.0.md) · [执行协议](../reliability-execution.md) · [评分标准](../reliability-scoring.md) · [导入指南](../../docs/release-consumer-README-v0.6.0.md)
