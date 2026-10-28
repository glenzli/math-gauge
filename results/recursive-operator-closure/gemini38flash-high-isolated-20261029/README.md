# Gemini 3.8 Flash High：独立评测记录

正式闭卷答卷经 AI 数学审核判为 **失败**。它有正确的矩阵估计、有限路径和最小偏定义解构造，但在整体存在性、终止性必要条件和假设范围上出现实质错误。人工审定待进行。

- [正式闭卷原答卷](closedbook/response.md) · [逐条数学审核与反例](closedbook/review.md)
- [与 Terra 6.1 Max 的比较](../comparison.md)
- [结构化结果](result.json) · [完整性核验](integrity-check.json)
- [运行前冻结](pre-run-freeze.json) · [工具条件纠正决定](tool-condition-decision.json)

## 样本账本

| 样本 | 数量 | 处理 |
| --- | ---: | --- |
| 正式闭卷数学请求 | 1 | 新目录、新数据区、新会话；计入本次闭卷比较，审核失败 |
| 意外可搜索的数学请求 | 1 | 原样保留为诊断；审核失败；不计入闭卷比较 |
| 非数学工具能力对照 | 2 | 同一中性提示，分别禁用和允许搜索；不计为数学样本 |
| 提交题面前中止的启动 | 1 | 请求数为零，不计为答题；保留原因和记录 |

还有无推理调用的帮助、版本和型号清单检查，详见 [尝试账本](evidence/closedbook/runtime/attempt-ledger.json)。没有挑选更好或更差的数学回答，也没有给模型纠错反馈。

## 型号、工具与隔离

实际评测为 Antigravity CLI **1.4.9**、`gemini-3.8-flash-high`、`--effort high`，High 为本轮实时型号清单中 Flash 的最高档。初查曾读到旧版 1.3.2；设置代理随后实际读到 1.4.9，未执行手工升级，版本变化原因未核实。

第一次数学运行的 `search_web` 成功绕过了 `strict` 加 `read_url` 拒绝配置。因此在其最终答卷返回前，已决定把它保留为带搜索诊断，修复工具条件后才启动一次正式闭卷比较。该决定不依赖答案质量：[父任务决定](tool-condition-decision.json)、[原始决定](evidence/diagnostic/runtime/tool-mismatch-decision.json)、[诊断事件](evidence/diagnostic/output/events.ndjson)。诊断中有 7 次完成的搜索和 1 次被拒绝的命令，详见 [诊断审核](diagnostic-search-enabled/review.md)。

正式运行使用自定义主 agent，配置正文为空，仅列 `finish`；平台仍保留内部 `manage_task`。非数学正反对照确认搜索能力随白名单开关变化。`init.tools` 列的是全局工具注册表，不是该主 agent 的有效能力清单，不能据此声称闭卷失败或成功。正式事件中实际发生一次内部 `manage_task`，没有检索、浏览器、命令、文件读取或 MCP 调用。没有将“未外部取材”写成“所有工具调用均为零”。

新进程及其模型工作进程受同一 macOS 文件访问策略约束。真实文件打开探测与实际 agy PID 检查均为：题面可读，12 个禁止路径被拒，覆盖项目、答案、旧评测、记忆、历史及先前诊断/对照文件。客户端保留必要安装文件、登录访问与模型服务联网，因此这是工作材料与工具隔离，不是离线虚拟机。

## 证据保存与证明边界

[evidence.tar.gz](evidence.tar.gz) 原始归档 SHA-256 为 `3c37c4e1a61120f56ec74f598fc777e1ee1c5491d0ebb59935cc97f4e323bfca`，含 100 个白名单文件；未保存运行状态目录或凭据内容。两个 stdout 内部硬链接在展开时保存为同字节普通文件；无符号链接。展开清单见 [evidence-manifest.json](evidence-manifest.json)。原始输入、输出、事件和配置只读保存；审阅文件另存。

题面、作者参考和 12 个 Lean 源模块与冻结散列一致，复用既有 81 条定理编译及公理核验。本轮没有重新编译未变的参考工程，也没有把候选答卷称为 Lean 已验证。

这是单题、每个正式配置一次的观察。不同产品的原生系统提示和内部工具环境仍有差异，不构成纯模型能力的统计排名，也不估计整个题库通过率。所有本轮修改均未提交、未推送。
