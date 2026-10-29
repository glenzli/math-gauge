# 新增十题的独立隔离 CLI 证据

本目录只保存 MG-R011–MG-R020 的模型运行工程证据。请求配置为 gpt-6.1-terra / max，每题一个新独立会话，只发送冻结 task.md，一次stdin，不自动重试或按答案质量选样。

answers/ 是原答卷的逐字节可读副本；archive-map.json 绑定 response SHA256 与原 ZIP entry。全部原始事件、进程/策略核验、启动失败及尝试账本保存在未改写的 evidence-bundle.zip，避免同时提交完整展开树。evidence-whitelist.json 中的相对路径即 ZIP entry，原绝对路径仅是原运行位置，不在归档时改写。

actual PID、CLI 二进制、请求型号/档位和独立后台身份回显分别记录。未回显的 observed model/effort 保持null。文件隔离使用实际打开探测，实际新PID在发送任务前再次核验；HOME/CODEX_HOME保持原值，state及凭据不入归档。仅允许既定模型服务的loopback7897代理及非历史installation_id精确启动例外。

final-engineering-report.json 只说明归档时的工程状态，不承载数学评分。独立AI数学审核另行绑定response_sha256；审核者知道题面、参考及请求标签，不称双盲。作者Lean证明、候选答卷、AI审核与人工审定是不同证据；human仍pending。
