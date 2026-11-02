# 可靠性计划与固定材料

当前材料为0.3.0默认32题、80槽的准备配置，reliability协议0.2.0。**本版本尚未运行候选模型**；旧43题177槽试跑另按原计划和审核快照保留，见[试跑记录](../../docs/terra-pilot-2026-11-02.md)。历史配置原字节见[0.2.0快照](../history/v0.2.0/)。

| 材料 | 作用 |
| --- | --- |
| [plan.json](plan.json) | 32题候选身份、逐题初答安排及执行门槛 |
| [selection.md](selection.md) / [selection.json](selection.json) | 六题panel、精确重点与真值，仅供评审 |
| [prompts.json](prompts.json) | 36条后续消息，只投放选中条目的content |
| [reply-format.md](reply-format.md) | 既有KEEP/FULL格式，正文未改 |
| [schedule.json](schedule.json) | 每模型80个planned槽，不含结果 |
| [validation.json](validation.json) | 当前材料离线检查，不能替代软件验收或模型成绩 |

全部32题各做A1，六题额外A2/A3共12槽；同六题各开三种两轮分支再加36槽。两个章节仅各做A1。能力分只取32个A1，重复稳定性分母仅为六题；neutral/stance的重点数学槽分别12/24。分支只读自己的A1及原始前轮，不看其他初答、其他分支、参考或评审反馈。

新版范围在旧公开开发试跑后精简，[选题说明](../../docs/selection-v0.3.0.md)记录32/11成员及六题理由；这不是旧版的工程身份重绑。机器配置、消息及安排分别冻结，旧177槽的core仍按旧profile三次均分，不用新版重算替代。

共享runner继续处理计划投影、原始历史、KEEP/FULL、审核和报告，不复制运行器。默认32由cases/suite.json加载；11道备选经cases/reserve-suite.json显式prepare/run，不进入默认包。具体命令见[使用指南](../../docs/usage.md)及[评分标准](../benchmark-scoring.md)。

`python3 scripts/validate_protocol.py`只读检查32份候选投影、306项义务、六题36条消息和80槽。`--refresh`仅在明确核对后重绑本版工程身份，仍不能修改design_bindings中的数学断言、选题和消息，不能授权执行或填入成绩。离线验收必须保留真实测试输出，旧收据不因更新散列而成为新版本通过证据。
