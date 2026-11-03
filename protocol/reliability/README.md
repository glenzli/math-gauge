# 作答稳定性与自查材料

当前0.4.0公开计划含36份任务/84份记录，合并探索后39份任务/87份记录。作答稳定性与自查仍固定选取6份公开数学题。已有数学与8份审阅原答，当前AR纳入、权重和统一重评属于观察结果后的方法变更，不是新考试；准备模板的空状态不代表历史答卷不存在。原执行与历史发布保留。

| 材料 | 作用 |
| --- | --- |
| [plan.json](plan.json) | 36份任务候选身份、逐题初答安排及执行门槛 |
| [selection.md](selection.md) / [selection.json](selection.json) | 六题panel、精确重点与真值，仅供评审 |
| [prompts.json](prompts.json) | 36条后续消息，只投放选中条目的content |
| [reply-format.md](reply-format.md) | 既有KEEP/FULL格式，正文未改 |
| [schedule.json](schedule.json) | 每模型84份计划记录，不含结果 |
| [validation.json](validation.json) | 当前材料离线检查，不能替代软件验收或模型成绩 |

36份任务各取首次答卷，选定6题另有12份额外独立答卷及36份后续自查。整章和AR目前只取首次，合并3份探索后同理。能力不重复计入额外答卷；重复作答稳定性分母为6题，无反馈与立场干扰下自查分别有12/24份重点数学记录。分支只读自己的A1及原始前轮，不看其他初答、其他分支、参考或评审反馈。

新版范围在旧公开开发试跑后精简，[选题说明](../../docs/selection-v0.3.0.md)记录32/11成员及六题理由；这不是旧版的工程身份重绑。机器配置、消息及安排分别冻结，旧177槽的core仍按旧profile三次均分，不用新版重算替代。

共享runner继续处理计划投影、原始历史、KEEP/FULL、审核和报告，不复制运行器。默认36份任务由cases/suite.json加载；11道备选经cases/reserve-suite.json显式prepare/run，不进入默认包。具体命令见[使用指南](../../docs/usage.md)及[评分标准](../benchmark-scoring.md)。

`python3 scripts/validate_protocol.py`只读检查当前候选投影、原306项数学义务、4份审阅合同、六题36条消息和84份计划记录。`--refresh`仅在明确核对后重绑本版工程身份，仍不能修改design_bindings中的数学断言、选题和消息，不能授权执行或填入成绩。离线验收必须保留真实测试输出，旧收据不因更新散列而成为新版本通过证据。
