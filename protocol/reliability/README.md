# 可靠性计划与固定材料

当前43份完整试卷的重复作答和两轮自查方案。**prepared / not executed**：没有候选模型答卷、状态轨迹、通过率或本次运行授权。

| 材料 | 作用 |
| --- | --- |
| [plan.json](plan.json) | 当前唯一suite、逐题候选消息身份、执行门槛与未冻结参数 |
| [selection.md](selection.md) / [selection.json](selection.json) | 预选八题、精确重点、真值和选择理由，仅供评审 |
| [prompts.json](prompts.json) | 48条后续消息；只投放选中条目的content |
| [reply-format.md](reply-format.md) | 已逐字并入消息的KEEP/FULL交付格式 |
| [schedule.json](schedule.json) | 每模型177个planned槽位，不含真实结果 |
| [validation.json](validation.json) | 当前材料的离线合同与身份检查，不是候选成绩 |

每份试卷A1/A2/A3三次全新上下文，共129个独立槽位。八题从同一A1各开neutral、affirm、deny三分支，每支两轮，增加48槽位，共177槽位/模型。两章参加三次初答，不进入八题子集；分支不看A2/A3或其他分支。

固定选择、断言、理由、48条消息正文及回复格式保留既有设计。本次目录和散列重绑只证明工程身份，没有重新进行独立数学审核。设计来源由plan中的精确Git提交记录，当前检查不读取本地旧档案或旧结果。

共享runner的 `benchmark-*` 入口提供多轮调度、角色历史、KEEP/FULL材料、逐轮审核及分项聚合，离线验收见[运行器证据](../../verification/runner/README.md)。固定材料包仍未执行：实际参数、后端、预算和重试等待策略尚未冻结。单轮run和旧比较脚本不自动执行177槽位方案；实际启动仍须另有执行授权并完成规定门槛。

[综合评分标准](../benchmark-scoring.md)和[默认profile](../benchmark-profile.json)定义四类任务、三项可靠性和加权总分。可先冻结同一完整主计划，再独立执行分项并复用原始A1；各分片只能按同一计划身份合并。CLI示例及当前正式资格限制见[使用指南](../../docs/usage.md)。

```sh
python3 scripts/validate_protocol.py
# 核对完整材料并有意更新工程身份后：
python3 scripts/validate_protocol.py --refresh
```

检查覆盖全部43份候选投影、372项相关审核义务、固定八题及消息、177槽位与隔离历史边，并检查已登记离线验收收据仍绑定当前源码；它不重新运行验收测试、不调用模型、不编译Lean、不裁定数学正确性。--refresh只重绑当前材料和程序散列，不能改选题设计、授权执行或填入成绩；若软件已偏离验收输入，须先实际重验，不能把旧收据直接重绑为通过。

[执行协议](../reliability-execution.md) · [评分标准](../reliability-scoring.md) · [基础协议](../evaluation.md)
