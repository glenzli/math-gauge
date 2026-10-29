# Math Gauge

**Measure the capability, not just the answer.**

Math Gauge 是一套数学推理与 Lean 语义对齐习题及评测工具。它检验模型能否在题目实际给定的结构下完成证明、反例、构造或分类，并保持假设、量词、定义域和结论强度。

项目源于算子演化论（OET）的写作与研究协作，题材扩展到泛函分析、代数、拓扑、范畴与几何。既检查偷加条件和错误强化，也检查不必要地缩小可证明范围；有效短证明、合法反例和替代路线都应接受。

[习题总目录](exercises/README.md) · [完整模型比较](results/full-comparison-20261030/comparison.md) · [使用与复核](docs/usage.md) · [结果与版本](docs/results.md) · [贡献指南](CONTRIBUTING.md)

## 习题结构

当前共 **41 题、7 章**：29 道数学论证题、6 道 Lean 对齐判定题、3 道 Lean 生成题和 3 道 Lean 修复题。七章按算子与动力系统、分析与恢复、代数与提升、拓扑与下降、有限覆盖、Fourier 正则性、几何证明机制编排；另有[任务类型索引](exercises/task-types.md)。

| 题组 | 题号 | 数量 | 共享 runner 的题集路径 |
| --- | --- | ---: | --- |
| [弱结构研究题](cases/public/README.md) | R001–R020 | 20 | `cases/public`（默认） |
| [成立目标与构造](drafts/true-goal-six-20261029/README.md) | R101–R106 | 6 | `drafts/true-goal-six-20261029` |
| [公开证明机制抽取](drafts/public-proof-extractions-20261029/README.md) | P001–P003 | 3 | `drafts/public-proof-extractions-20261029` |
| [Lean 对齐任务](drafts/lean-alignment-20261029/README.md) | F101–F112 | 12 | `drafts/lean-alignment-20261029` |

`drafts/` 保留原始路径，其中这些题组已纳入现行 41 题目录。默认 CLI 只选择公开二十题，**不会自动运行全部 41 题**。旧版本和退役题另列在[历史对应](exercises/history.md)，不重复计数。

每题具有题面、来源、完整参考论证或反例、具体评分标准和审核记录。参考解、来源、真假标签及作者 Lean 属于出题侧材料；候选只接收该题显式指定的题面和附件。

## 最新测评

首轮完整比较为每模型每题一次独立运行：先 `gpt-6.1-terra/max`，再 `gemini-3.8-flash-high/high`，共 82 次数学请求。双方使用相同输入、无答题工具、无现场 Lean 反馈。严格通过结果经 AI 数学审核，**仍待人工验收**。

| 任务 | Terra 6.1 Max | Gemini 3.8 Flash High |
| --- | ---: | ---: |
| 数学论证 | 29/29 | 20/29 |
| Lean 对齐判定 | 6/6 | 6/6 |
| Lean 生成 | 3/3 | 0/3 |
| Lean 修复 | 2/3 | 1/3 |
| **整体** | **40/41（97.6%）** | **27/41（65.9%）** |

Gemini 两份服务端过滤通知按未作答单列，仍保留在 41 题分母中。生成与修复题编译模型交付的原始源码，未修补后回填成绩。同一母题的多个版本具有相关性，每题仅一个样本；这些比例描述本套题及本次配置，不构成总体能力排名。客户端请求、实际回显和未独立确认的后台字段分别保存在证据中。

首轮 R005 使用 0.3.0。随后将竞争函数的扩展实值范围澄清为 0.3.1，并完成[独立单题补测](results/r005-clarified-v0.3.1-20261030/README.md)，两模型均通过；补测的两次请求不改写首轮分数。其他校准批次也不拼接为一次实验，见[结果索引](docs/results.md)。

## 数学、Lean 与审核状态

所有 41 题都有完整数学参考和非作者 AI 审核，目前仍为 `draft / human pending`。其中 **40 题有完整作者主任务 Lean 证据**；P003 保留完整数学任务，但作者 Lean 为部分覆盖，具体几何缺口见[覆盖账本](exercises/instructor-guide.md)。

三类证据分别回答不同问题：

- **数学与对齐审核**：题面、参考或候选答案是否在原条件下完成全部义务；Lean 声明是否表达了同一个命题。
- **Lean 核验**：固定版本的源码是否编译，声明依赖是否符合公理白名单。可编译的题目输入也可能故意语义失配。
- **人工审定**：人类对题目及答卷作出的审核。AI 审核或编译成功不能代替它。

作者 Lean 与候选 Lean 分开核验。数学论证题没有候选 Lean 交付义务；Lean 生成和修复题还必须通过原样编译、公理审计及语义对应审核。见[评测协议](protocol/evaluation.md)和[候选源码合同](protocol/candidate-lean.md)。

## 快速使用

需要 Python 3.10+；共享 runner 无第三方运行依赖。克隆后在仓库根目录运行：

```sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m math_gauge prepare --case MG-R001 --out runs/question-r001
python3 -m math_gauge prepare --suite drafts/lean-alignment-20261029 --case MG-F105 --out runs/question-f105
python3 exercises/refresh_catalog.py --check
```

输出目录须是新的。`prepare` 只导出候选材料，不调用模型。附件题的完整模型消息应由 `candidate_message(request)` 构造，不能只发送 `prompt.md` 而漏掉 Lean 附件。实际闭卷测评还需要运行时访问隔离；普通目录分离不提供这一保证。

[使用指南](docs/usage.md)包括四题集校验、适配器接入、审核与报告、作者／候选 Lean 核验，以及无需模型服务的离线复算。Lean 依赖版本与环境要求见[参考验证器](scripts/formal/README.md)。

## 仓库与文档

| 路径／文档 | 职责 |
| --- | --- |
| [exercises/](exercises/README.md) | 章节、任务类型、来源与精确版本目录；不进入候选输入 |
| `cases/`、`drafts/` | 题目及评审材料的唯一来源；各题集共用 runner |
| `math_gauge/catalog.py` | 题目合同、题集身份与候选投影 |
| `math_gauge/execution.py` | 请求、原始响应、执行证据与候选 Lean |
| `math_gauge/review.py` | 响应绑定的审核、报告与配对统计 |
| `scripts/formal/` | 作者参考 Lean 的固定版本验证与公理检查 |
| `scripts/isolated_cli/`、`scripts/benchmark/` | 隔离辅助与本轮薄调度层；数学评分仍由共享审核模块承担 |
| [结果与版本](docs/results.md) | 当前比较、补测、历史校准与证据阅读顺序 |
| [贡献指南](CONTRIBUTING.md) | 新题材料、版本修订、输入边界和验证要求 |
| [研究题设计](protocol/research-case-design.md) | 目标、参考、评分及校准的设计依据 |

`results/` 保存明确选择的可复核答卷、审核与归档；`runs/` 和 `.dev-mesh/` 是本地工作材料，不随仓库提交。公开和私有题集使用同一个 runner；私有题、答案和完整输出另行保管，不复制 runner 实现。

最近工程验收为 **107 项测试通过、5 项未改动的可选 Lean 4.36 测试跳过**，四题集及目录身份检查通过。首轮与补测均完成归档离线复算；详见[验收记录](results/full-comparison-20261030/validation/finalization/README.md)。

## 来源与许可

新题使用公开数学资料和独立构造，不抽取 OET 未发布内容。公开论文中的错误、勘误或形式化差异只作为明确说明的取材机制，不自动构成对原论文主结论的反证。来源版本、取材范围、作者与 AI 协作说明见 [SOURCES.md](SOURCES.md) 和逐题 `source-notes.md`。

仓库采用 [MIT 许可证](LICENSE)；复用的第三方源码保留其各自的许可证、NOTICE 与来源记录。公开题目可能已进入训练数据，本项目不声称这些题对模型必然未见。
