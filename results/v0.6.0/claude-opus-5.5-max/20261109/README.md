# Claude Opus 5.5 Max · 2026-11-09

benchmark **0.6.0**，默认主分 **RMC 91.44**。39道初答（公25／私14）、35个数学家族及C003固定三轮均已评审，共42份规定交付。没有补跑或数学择优，首次与规则选定成绩一致。AI审核，人工审核pending，正式比较资格false。

| 口径 | 成绩／100 |
|---|---:|
| MC | 93.76 |
| RMC | 91.44 |
| SMC | 59.42 |

内容可靠率 **94.22%**，完整目标达成率 **85.84%**。沿共同697个承诺单元和149个完整目标逐项审核，使用共享评分器；它们不是新增独立题，也不改变三项主分。所有项目已测，完整区间收敛为单值。

## 分类贡献

| 子类 | 满分 | MC | RMC | SMC |
|---|---:|---:|---:|---:|
| 书面论证 | 25 | 24.74 | 24.32 | 18.75 |
| 论证审阅 | 10 | 8.44 | 7.94 | 0.00 |
| 语义审计 | 10 | 10.00 | 10.00 | 10.00 |
| 形式化 | 15 | 15.00 | 15.00 | 15.00 |
| 对齐自查 | 10 | 9.83 | 9.83 | 0.00 |
| 背景核查 | 10 | 10.00 | 10.00 | 10.00 |
| 数学想法手稿化 | 10 | 9.64 | 8.24 | 4.00 |
| 命题拓展 | 10 | 6.11 | 6.11 | 1.67 |

## 运行与证据

Claude Code **2.1.303**，tclaude **0.1.10**；请求`claude-opus-5-5[1m]`、effort `max`，原生回显`claude-opus-5-5`。这些回显不构成独立后端认证。实际收集器公有25道初答为mg_harness0.1.0，私有14道为0.2.0，原始计划中的旧标签也原样保留。

所有题允许本地工具和预置公共依赖，禁止检索及工具联网。39道初答中37道实际使用工具，共338次本地工具调用；三轮原生事件另行留档。设置、实际提供的工具及事件已核查，未提供独立运行隔离探针，故不声称OS隔离已独立验证。模型服务和认证流量另记。

实际外层时限为书面2700秒、另外七道Lean任务5400秒、C003各阶段10800秒。128000输出上限作用于每次内层API请求，不是整场agent运行的累计输出预算。39个独立初答上下文，三轮用各自连续原答历史；内层API/工具往返不算额外模型尝试。

每份采用第一次原生成功交卷，均在原截止内。两份外层CLI的清理退出分别为未知与130，但此前已有完整原生成功终态，不记为失败或重试。完整原始返回、自评、实际输入、原始日志、源工程和原审核分开保存；观察后适配没有改写原生文件，也没有把Claude Code伪装为Codex/AGY。

## 主要审核结果

四道形式化初答实际完成8／20／40／92项全部目标。实际封卷工程经原样编译、公理审计及逐项语义审核；编译本身不替代语义对齐证明。

C003从A1至R3都是92/92，R3为KEEP，实际全部115个工程文件与R2字节相同，复用其同源核验。R1增加包装声明时误称父稿缺少最小值达到证明，而A1已有该论证：本轮工程交付完整，历史问题定位不准确。自查细项为95／100／100，贡献9.83／10；整段轨迹SMC不通过，贡献0／10。没有虚假的当前100%完成或数学回退；SMC失败不能读成最终工程不完整。

八道公开书面论证全部通过，四道Lean审计和四道背景核查通过。四道论证审阅均有未满足的实质要求或范围问题。命题拓展保留正确基线和已完成层级，只有MG-TX002达到B2/R3；接受其完整循环移位结构，不要求另打印二进制编码或指定措辞。没有发出研究邀请。

公开手稿化MG-MCP003完成全部六维：采用自洽的替代矩阵/阈值路线，零距、无限值和条件均已核查，不因没有照抄参考路线扣分。其余手稿的匿名合并结果见分类表，私有题文与逐题判断不公开。

可靠性审核共14项独立错误承诺（local6、material8），没有critical或核心错误放行封零。保留有效数学部分，按原规则单列扣分、同根去重。额外错误可以降低内容可靠率和RMC；可分离的附加错误不自动抹去已独立完整交付的目标。SMC继续按各任务和整段自查的冻结规则验收。

## 可复核文件

[正式记录](record.json) · [MC](retry-capability-combined-aggregate.json) · [RMC](retry-combined-aggregate.json) · [SMC](retry-strict-combined-aggregate.json) · [两率](content-rates.json) · [公开逐题投影](public-task-scores.json) · [工程审核](reviews/formalization.json) · [三轮审核](reviews/alignment.json)

## 公开逐题

单题比例来自共享报告，不另计算公开集总分；C003三轮独立按轨迹计分。

| 题号 | MC／100 | RMC／100 | SMC | 原答 |
|---|---:|---:|---|---|
| AHR01 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR01/A1/attempts/1/response.md) |
| AHR02 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR02/A1/attempts/1/response.md) |
| AHR03 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR03/A1/attempts/1/response.md) |
| AHR04 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/AHR04/A1/attempts/1/response.md) |
| HCH02 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/HCH02/A1/attempts/1/response.md) |
| LCH01 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/LCH01/A1/attempts/1/response.md) |
| LCH02 | 100.00 | 100.00 | 通过 | [完整原答](imports/lean/slots/LCH02/A1/attempts/1/response.md) |
| MG-AR001 | 80.00 | 70.00 | 不通过 | [完整原答](imports/written/slots/MG-AR001/A1/attempts/1/response.md) |
| MG-AR002 | 82.50 | 82.50 | 不通过 | [完整原答](imports/written/slots/MG-AR002/A1/attempts/1/response.md) |
| MG-AR003 | 95.00 | 95.00 | 不通过 | [完整原答](imports/written/slots/MG-AR003/A1/attempts/1/response.md) |
| MG-AR004 | 80.00 | 70.00 | 不通过 | [完整原答](imports/written/slots/MG-AR004/A1/attempts/1/response.md) |
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
| MG-MCP003 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-MCP003/A1/attempts/1/response.md) |
| MG-PS001 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-PS001/A1/attempts/1/response.md) |
| MG-TX001 | 66.67 | 66.67 | 不通过 | [完整原答](imports/written/slots/MG-TX001/A1/attempts/1/response.md) |
| MG-TX002 | 100.00 | 100.00 | 通过 | [完整原答](imports/written/slots/MG-TX002/A1/attempts/1/response.md) |

[本轮最终验证回执](validation.json)：750项测试通过（17项环境跳过），目录／协议、公私六视图、两率与公开投影核验通过。
