# MG-C003 后续运行：每轮 180 分钟

自本政策启用起，92 项的 MG-C003 新初答、每次中性跟进和操作续作均使用每轮
10800 秒（180 分钟）上限。原生生成、broker 和外层墙钟分别设置为 10800 秒；
工具调用、编译与等待计入该轮。每轮重新计时，首次终态或截止即按
[到时封卷规则](deadline-submission.md)封存实际工程。

机器政策为 [预算 v0.2.0](lean-tool-budget-policy-v0.2.0.json)。未来 C003 新计划使用
[具名 profile](benchmark-profile-c003-180.json) 和 `c003-180` 目标：

```sh
python3 -m math_gauge benchmark-plan \
  --profile protocol/benchmark-profile-c003-180.json \
  --target c003-180 \
  --runtime PATH_TO_FROZEN_C003_RUNTIME.json \
  --out runs/NEW_C003_PLAN.json
```

运行前将实际 runtime 的 `budget.timeout_seconds` 冻结为 `10800`，并单独核实实际
适配器的原生与 broker 上限。执行与导出会核对外层 runtime；其数值不能证明未观察到的
内层设置已经生效。准备计划、导出与校验均不调用模型。

同一 profile 的 `lean-90` 目标仅包含其余七份新 Lean 初答，仍为每轮 5400 秒，
须使用单独的兼容 runtime。混合目标不得通过一个全局预算覆盖两种条件。
通用 CLI 的 120 秒默认值和下载包 runtime 示例不随此政策改变。

未来中性研究与操作续作也须事前绑定预算 v0.2.0 的路径及 SHA-256，并冻结
`timeout_seconds_per_round=10800`。它们分别归档；续作继承自己的工程和允许历史，
不构成新的独立初答，也不替换原 A1 或填入标准分母。

[原 v0.6.0 profile](benchmark-profile.json)、[预算 v0.1.0](lean-tool-budget-policy-v0.1.0.json)
和[原中性专项](lean-alignment/study.json)保留其 5400 秒身份。既有响应、工程、审核、
成绩和执行时间记录不改写为新条件。Terra 现有交卷无需为此政策补考；Gemini 的
原始执行记录与已完成续作也保留原身份，新补时记录单独报告。
