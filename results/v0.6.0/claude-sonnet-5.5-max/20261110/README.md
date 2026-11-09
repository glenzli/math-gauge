# Claude Sonnet 5.5 Max · 2026-11-10

benchmark **0.6.0**，默认主分 **RMC 88.20**。采用39道初答（公25／私14）、35个数学家族及C003固定三轮，共42份规定交付。AI审核，人工审核pending，正式比较资格false。

| 口径 | 初答已确认／100 | 规则选定已确认／100 | 规则选定完整区间 |
|---|---|---|---|
| MC | 91.95 | 91.95 | 91.95 |
| RMC | 88.20 | 88.20 | 88.20 |
| SMC | 55.42 | 55.42 | 55.42 |

本次初答与规则选定成绩一致。总分和分类贡献均读取共享评分器已保存的六视图，不另计算公开集总分或重定权重。

内容可靠率 **90.83%**，完整目标达成率 **83.38%**；两率直接读取已归档报告，不改变三项主分。

## 分类贡献

| 子类 | 满分 | MC | RMC | SMC |
|---|---|---|---|---|
| 书面论证 | 25 | 23.59 | 22.55 | 18.75 |
| 论证审阅 | 10 | 7.88 | 7.38 | 0.00 |
| 语义审计 | 10 | 10.00 | 10.00 | 10.00 |
| 形式化 | 15 | 15.00 | 15.00 | 15.00 |
| 对齐自查 | 10 | 9.67 | 9.67 | 0.00 |
| 背景核查 | 10 | 10.00 | 10.00 | 10.00 |
| 数学想法手稿化 | 10 | 9.70 | 7.50 | 0.00 |
| 命题拓展 | 10 | 6.11 | 6.11 | 1.67 |

## 运行与来源

原生环境为Claude Code 2.1.303，请求`claude-sonnet-5-5[1m]`、effort `max`，回显`claude-sonnet-5-5`。回显不构成独立后端认证。39道选定初答中38道实际使用本地工具，共559次。

本地工具和预置公共依赖获准使用，禁止检索及工具联网；模型服务和认证流量另记。主批临时目录共享问题已披露，一道背景核查在数学评审前因隔离不合规替换一次。原交付完整保留但不计分，替换批采用私有临时目录；这是来源隔离替换，不是数学重试。共43次物理调用，选定39份初答及三轮自查。不得由静态读取审计推断主批完整OS隔离。

实际外层时限按原组保留：书面2700秒、其余七道Lean任务5400秒、C003各阶段10800秒。128000输出上限适用于每次内层API请求，不是整场累计预算。原始答案、自评、输入、日志和源工程分开留存。

## C003三轮自查

C003从A1至R3的已核实完成数为 **92→92→92→92**，共92项。R1漏诊依赖表问题，R2完成修复；工程数学义务完整与诊断准确性分别验收。整段SMC不通过；自查分类贡献为MC 9.67／RMC 9.67／SMC 0.00，均直接取共享结果。

| 轮次 | 已核实数学义务 | 局部诊断 | 全局判断 | 本轮分／100 | 本轮严格验收 |
|---|---|---|---|---|---|
| R1 | 92/92 | 10/20 | 10/10 | 90.00 | 不通过 |
| R2 | 92/92 | 20/20 | 10/10 | 100.00 | 通过 |
| R3 | 92/92 | 20/20 | 10/10 | 100.00 | 通过 |

本次恢复并核对了原答实际交付的代码与映射，来源与原生历史按字节绑定；恢复过程没有新候选调用或数学修补。完整源码核验与语义审核分别记录。

## 可复核文件

[正式记录](record.json) · [MC](retry-capability-combined-aggregate.json) · [RMC](retry-combined-aggregate.json) · [SMC](retry-strict-combined-aggregate.json) · [公开逐题投影](public-task-scores.json) · [工程审核](reviews/formalization.json) · [三轮审核](reviews/alignment.json) · [两率](content-rates.json)

## 公开逐题

单题比例来自共享报告；C003三轮按独立的固定轨迹规则计分。

| 公开题号 | MC／100 | RMC／100 | SMC | 原答 |
|---|---|---|---|---|
| AHR01 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR01/A1/attempts/1/response.md) |
| AHR02 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR02/A1/attempts/1/response.md) |
| AHR03 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR03/A1/attempts/1/response.md) |
| AHR04 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR04/A1/attempts/1/response.md) |
| HCH02 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/HCH02/A1/attempts/1/response.md) |
| LCH01 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/LCH01/A1/attempts/1/response.md) |
| LCH02 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/LCH02/A1/attempts/1/response.md) |
| MG-AR001 | 90.00 | 80.00 | 不通过 | [完整原答](imports/written/slots/MG-AR001/A1/attempts/1/response.md) |
| MG-AR002 | 60.00 | 50.00 | 不通过 | [完整原答](imports/written/slots/MG-AR002/A1/attempts/1/response.md) |
| MG-AR003 | 90.00 | 90.00 | 不通过 | [完整原答](imports/written/slots/MG-AR003/A1/attempts/1/response.md) |
| MG-AR004 | 75.00 | 75.00 | 不通过 | [完整原答](imports/written/slots/MG-AR004/A1/attempts/1/response.md) |
| MG-BC001 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-BC001/A1/attempts/1/response.md) |
| MG-BC002 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-BC002/A1/attempts/1/response.md) |
| MG-C003 | 100.00 | 100.00 | 通过 | [完整原答](imports/c003/slots/MG-C003/A1/attempts/1/response.md) |
| MG-GP001 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-GP001/A1/attempts/1/response.md) |
| MG-GP002 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-GP002/A1/attempts/1/response.md) |
| MG-GR005 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-GR005/A1/attempts/1/response.md) |
| MG-GR009 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-GR009/A1/attempts/1/response.md) |
| MG-GR021 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-GR021/A1/attempts/1/response.md) |
| MG-GR022 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-GR022/A1/attempts/1/response.md) |
| MG-GR023 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-GR023/A1/attempts/1/response.md) |
| MG-MCP003 | 100.00 | 85.00 | 不通过 | [完整原答](imports/written/slots/MG-MCP003/A1/attempts/1/response.md) |
| MG-PS001 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-PS001/A1/attempts/1/response.md) |
| MG-TX001 | 66.67 | 66.67 | 不通过 | [完整原答](imports/written/slots/MG-TX001/A1/attempts/1/response.md) |
| MG-TX002 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-TX002/A1/attempts/1/response.md) |
