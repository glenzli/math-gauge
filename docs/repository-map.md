# 仓库地图

题目材料、运行软件、评测协议与冻结结果各有唯一职责。`drafts/` 是保留的源路径，不能单凭目录名推断材料是否完整或是否已测试；真实生命周期以逐题版本、审核和证据为准。

## 目录与目的

```text
README.md / docs/                    项目入口、方法、使用、结果与导航
protocol/                            共同合同及各轮执行/评分规范
math_gauge/                          所有公开与私有题集共用的 runner
scripts/formal/                     作者参考 Lean 验证与覆盖重绑定
scripts/isolated_cli/               CLI 隔离准备、探测和收据
scripts/benchmark/                  原完整比较的薄调度层
tests/                               软件合同与数学见证的测试
drafts/progressive-groups-20261030/   当前41题组、246阶段
drafts/chapter-exams-20261030/        当前两章题、34/92项义务
protocol/reliability-20261030/        新43份的消息、计划、选择和材料校验
cases/public/                        原版公开20题，CLI默认suite
drafts/true-goal-six-20261029/         原版成立目标6题
drafts/public-proof-extractions-20261029/ 原版公开证明机制3题
drafts/lean-alignment-20261029/        原版Lean对齐12题
exercises/                           原41题章节/类型/版本目录、能力重点入口与覆盖账本
drafts/long-form-design-20261030/     长篇研究设计、来源和独立复核
drafts/recursive-operator-closure/    R001前身及历史作者形式化
results/                             明确归档的答卷、审核与运行证据
archive/                             退役题集、原版本与归档说明
examples/                            合成工作流演示
```

根目录另有 `AGENTS.md`、[贡献指南](../CONTRIBUTING.md)、[来源说明](../SOURCES.md)、许可证、Python 包配置及默认 Lean 工具链。`runs/`、`.dev-mesh/`、Python/构建缓存和凭据只在本地保留，不进入仓库发布。

## 软件职责

| 路径 | 负责什么 |
| --- | --- |
| `math_gauge/catalog.py` | suite/case材料合同、路径与附件白名单、身份散列、题组及alignment合同、候选消息投影 |
| `math_gauge/execution.py` | 单轮请求与原始响应、冻结合同与执行证据、候选源码/清单提取、受限编译和声明审计 |
| `math_gauge/review.py` | 响应绑定审核、逐阶段义务与交付门槛、报告和配对比较 |
| `math_gauge/cli.py` | 命令行入口，调用上述责任模块 |
| `scripts/formal/` | 作者参考的固定版本编译、公理检查及文档覆盖重绑定；[说明](../scripts/formal/README.md) |
| `scripts/isolated_cli/` | 本机模型CLI的输入隔离与实测证据辅助；[协议](../protocol/isolated-cli-runs.md) |
| `scripts/benchmark/` | 原41题比较的预检、队列、隔离及适配器；数学审核与汇总仍使用共享模块 |
| `protocol/reliability-20261030/validate_materials.py` | 新43份材料包的版本、题面、选择、消息和历史关系检查，不运行模型或Lean |
| `exercises/refresh_focus_catalog.py` | 按`focus-taxonomy.json`和完整题目合同生成出题侧能力重点索引，核对来源与标签依据，不改变候选输入 |

所有公开与私有 suite 使用同一 runner。私有位置只保存受控题目和记录，不复制执行或评分实现。新多轮协议目前是材料与合同，尚未成为已经验收的调度、历史绑定和 KEEP/FULL 组合入口。

## 题目材料放在哪里

每个 suite 有显式 `suite.json` 和来源登记；每道题的 `case.json` 指定 task、参考、rubric、附件与评审文件。当前题组另有逐阶段 `contract.json`，章节题用 `candidate/` 存放候选材料，但实际投影仍只由 case 白名单决定。

整章题的`reference-design-notes.md`是冻结的原pilot设计记录，保留当时未拆完义务等状态；当前完整范围以`case.json`、`contract.json`及候选`obligations.json`为准。第3章旧30源单元不等于当前92项义务；设计记录中的旧pilot、`coverage-registry.json`等路径按[归档manifest](../archive/retired-pilots-20261030/manifest.json)从`9e536ad5ebce182ffcb6bcaabdc24c7fbec221c3`恢复，不改写记录字节。

参考、合同、评分、来源、审核、作者 Lean 和历史结果都属于出题侧。不得把某题的评审文件作为另一题候选附件；完整模型消息由共享构造器生成，保持源码字节与目标路径。

| 材料 | 身份与状态 |
| --- | --- |
| [当前递进题组](../drafts/progressive-groups-20261030/README.md)和[整章题](../drafts/chapter-exams-20261030/README.md) | 43份试卷，版本以逐题记录为准；draft/human pending；无新模型成绩，新增作者Lean完整核验待完成 |
| [原41题目录](../exercises/README.md)及四个源suite | 原单题集合与已有实验的阅读入口；当前目录R005为0.3.1，首轮冻结实验用0.3.0 |
| [版本历史](../exercises/history.md)与`archive/` | 退役与前身材料，不重复计入当前试卷；部分仍是测试和目录检查的实际输入 |
| [长篇研究设计](../drafts/long-form-design-20261030/README.md) | 研究依据、独立复核及尚未启用的方向，不计作实测样本 |
| [结果索引](results.md)与`results/` | 冻结实验的原始答卷、成功/失败、审核、源码及复算证据，不被后续版本覆盖 |

`exercises/refresh_catalog.py` 针对原 41 题的固定范围、审核映射和覆盖边界编写。它不是任意新题的自动注册器；新43份由两套新suite及材料包登记，不通过重建旧目录把母题与扩展题混计。

[能力重点索引](../exercises/by-focus.md)提供跨题型的选题入口，不代替逐题完整材料或改变旧目录的样本身份。

## 测试覆盖与维护路径

| 变更 | 先读哪里 | 对应检查 |
| --- | --- | --- |
| suite、case或候选投影 | 完整题目材料与[贡献指南](../CONTRIBUTING.md) | 受影响suite validate、实际prepare输出、`test_runner.py` / `test_candidate_lean.py` |
| 题组、逐阶段审核或章节映射 | [题组合同](../protocol/question-groups.md) | `test_question_groups.py`，其中真实编译部分需要显式环境 |
| 作者Lean或验证器 | manifest、COVERAGE和[固定profile说明](../scripts/formal/README.md) | `test_formal_verifier.py`；只重编改变的题或依赖组 |
| 候选Lean交付 | [候选合同](../protocol/candidate-lean.md) | `test_candidate_lean.py`及对应隔离实机检查 |
| CLI隔离与执行证据 | [隔离协议](../protocol/isolated-cli-runs.md) | `test_isolated_cli.py`、`scripts/benchmark/test_runtime.py` |
| 审核与比较报告 | [基础协议](../protocol/evaluation.md)和`review.py` | `test_comparison_report.py`，保留来源与完整分母 |
| 原研究题身份/语义见证 | 题面、参考、来源、历史快照 | `test_research_suite.py`、`test_alignment_contracts.py`、`test_mathematical_witnesses.py` |
| 原41题阅读目录 | structure、catalog与逐题材料 | `python3 exercises/refresh_catalog.py --check` |
| 新43份能力重点索引 | focus-taxonomy、逐题依据及完整合同 | `test_focus_catalog.py`、`python3 exercises/refresh_focus_catalog.py --check` |
| 重复作答材料 | plan、schedule、prompts和selection | `python3 protocol/reliability-20261030/validate_materials.py` |
| 普通导航与说明 | 当前入口及链接目标 | 相对链接和事实/状态检查；复用未变源码的既有编译证据 |

runner合同改变时按AGENTS运行完整`python3 -m unittest discover -s tests`与默认`python3 -m math_gauge validate`，再核对受影响suite。明确报告可选测试跳过；不要为了形成提交重复编译未变源码。

## 冻结证据与清理

历史答卷和审核绑定原始响应散列；旧题面、原始候选Lean、全部尝试、失败和工具条件都属于可复核证据。归档中的runner副本用于复算当时的结果，不是当前共享runner的第二套维护实现，不应机械去重。

旧路径字符串可能只是来源历史，也可能被当前测试、目录或复算器实际读取。清理前要检查依赖性质和精确归档身份；可重建的本地忽略缓存与被manifest固定的olean、日志、来源压缩包分别处理。旧分数不因清理或新版材料而回填。

两份已退役整章pilot的60个文件保存在精确Git提交，恢复说明及逐文件散列见[退役题包归档](../archive/retired-pilots-20261030/README.md)。上层研究设计、独立审查与所有真实模型失败证据继续保留。

[文档导航](README.md) · [使用指南](usage.md) · [结果与版本](results.md)
