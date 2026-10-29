# R005 0.3.1 · 澄清后单题比较

本轮只补测 R005 0.3.1，明确竞争函数可取负无穷，并以实高度上图的闭性和凸性约定其范围。原版 0.3.0 的 [41 题完整比较](../full-comparison-20261030/comparison.md) 已归档，原答卷与分数保持不变。

**补测已完成，两模型均通过。** 新版题目的独立数学复核、五模块 Lean 编译和 119 个项目声明的公理检查通过。答卷评分为 AI 审核，人工审定仍为 pending。

| 配置 | 新版 R005 严格完成 | 原始答卷 | 评分依据 |
| --- | --- | --- | --- |
| Terra 6.1 Max | 1/1 | [答卷](reviews/packets/d12d9297ff1f/response.md) | [裁决](reviews/adjudication/d12d9297ff1f.json) |
| Gemini 3.8 Flash High | 1/1 | [答卷](reviews/packets/1d676bc005fd/response.md) | [裁决](reviews/adjudication/1d676bc005fd.json) |

补测于新加坡时间 2026-10-30 03:57 启动，04:05 完成，恰好两次有效数学请求、无重试。两份答卷均经过初审和独立复核；Gemini 另经第三份数学复核。完整统计见 [comparison.json](comparison.json)。

配置沿用首轮：`gpt-6.1-terra/max` 后 `gemini-3.8-flash-high/high`，每模型一个全新隔离会话，每题一次，关闭答题工具，无现场 Lean 反馈。两次补测仅属于这一题，不并入首轮 41 题通过率。

## 评分中的实际边界

Terra 通过闭上图、有限观测投影与最大性完成全部目标，覆盖竞争函数取正负无穷的情形。

Gemini 答卷包含一个真实的辅助证明错误：零高度分离情形中的正号扰动不能给出所需的仿射下界。评分没有修正这个式子。通过的依据是其第四步独立给出的凸集强／弱拓扑闭包相等、有限观测生成弱拓扑的证明路线，结合已写出的闭上图柱状交集和记录下确界关系完成主任务。由下确界定义得到投影上图闭包相等的 ε 展开未单列；三份复核均接受其为定义性的标准步骤。这个裁定边界及错误分支完整保留，供人工验收；“通过”不表示整份文本毫无错误。

两模型旧、新版各仅一个样本，不能据此断言题面澄清导致了分数变化。原轮仍为 Terra 40/41、Gemini 27/41；本轮仅报告新版 R005 双方通过。

本题属于数学论证题，不要求候选 Lean。119 个声明的作者 Lean 核验用于出题质量，不替代候选数学审核。审核者为 AI；根审知道调度顺序，第三审此前参与了题目澄清，盲审程度有相应限制。

## 证据与复算

- [执行完整性检查](final-runtime-audit.json)：2 次有效单次执行，无完整性错误。
- [归档清单](evidence-final/manifest.json)：910 个文件，含实际输入、响应、隔离与请求收据、评分及冻结 runner。
- [离线复算](offline-recomputed/verification.json)：汇总、分层、配对及逐题结果完全一致；禁止读取旧临时目录、联网和启动子进程，未发起模型请求。
- [独立归档验收](validation/final-supplement-audit.json)：910 项文件散列、两份答卷及全部审核绑定通过；首轮报告保持原字节。
- [初审与复核索引](reviews/archive-inputs.json)：保留所有审核及内容散列；候选原文未修补。

补测复用了首轮已通过的四项能力探测证据，并重新核查客户端身份、隔离及配置；没有再次发起探测模型请求。客户端与型号回显的限制与首轮相同：Terra 请求型号及推理档没有后台独立回显，Gemini 回显型号但未独立回显推理档。总计首轮 82 次加补测 2 次数学请求；运行前非数学探测单独记录。

导出复核材料时保留本目录整体；原轮证据位于相邻的 `full-comparison-20261030/`。两轮均保留当时冻结的 runner，后续汇总程序维护不回写旧报告。

[习题总目录](../../exercises/README.md) · [首轮归档复算](../full-comparison-20261030/runtime/final-archive-replay-receipt.json) · [补测流程](../full-comparison-20261030/runtime/R005-SUPPLEMENT.md)

新版身份与出题证据：[采纳检查](adoption/metadata-checks.json) · [完整习题身份清单](qualification/README.md) · [本次单题目录](catalog.single.json) · [采纳门禁](root-adoption.json)。
