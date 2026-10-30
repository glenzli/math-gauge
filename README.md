# Math Gauge

**Measure the capability, not just the answer.**

Math Gauge 是数学推理与 Lean 语义对齐基准。它检查模型能否在实际给定的结构下完成证明、反例、构造、分类或形式化，保持假设、量词、定义域与结论强度，并留下可复核的原始答卷与审核证据。

[试卷目录](cases/README.md) · [按考察重点选卷](cases/by-focus.md) · [评测协议](protocol/evaluation.md) · [使用指南](docs/usage.md) · [验证状态](docs/verification.md) · [文档导航](docs/README.md)

## 当前基准

唯一默认题集是 `cases/suite.json`，共 **43 份完整试卷**：

| 类别 | 数量 | 内容 |
| --- | ---: | --- |
| `cases/proofs/` | 29 | 书面证明、反例、构造与分类 |
| `cases/lean-audit/` | 6 | 已给 Lean 源码的语义审计 |
| `cases/lean-construction/` | 6 | Lean 生成与修复 |
| `cases/chapters/` | 2 | OET 卷 I 第 2/3 章的完整形式化 |

一个完整题组或一章是一份相关样本。41 份递进题组含 246 阶段，两章分别含 34/92 项义务，合计 372 项审核义务；**样本数为43，不能记为372**。整章题提供含证明的原文，测量该条件下的形式化能力。

题面、完整参考、逐项判准、来源和 AI 审核材料已经准备。全部题目仍为 **draft / human pending**；`draft` 是待人工审定的生命周期状态。作者 Lean 证据覆盖 43/43 份完整目标、372/372 项义务，470 个模块已有真实编译记录；MG-GP003 的 S5 已完成任意域上的核心转移几何与原典范单位比较。见[作者证据账本](verification/author/README.md)。作者证明、AI 复核、编译和人工批准分别记录。

当前基准没有候选模型答卷或通过率。[可靠性计划](protocol/reliability/README.md)拟对43份试卷各独立作答三次，并在预选八题上从同一 A1 开中性、支持与怀疑三个分支，各自查两轮，共177槽位/模型。消息与计划已准备；多轮调度和 KEEP/FULL 组合尚未实现验收，实际模型调用为0。

## 准备与核验

需要 Python 3.10+，共享 runner 无第三方运行依赖。在仓库根目录执行：

```sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m math_gauge prepare --case MG-GR001 --out runs/gr001
python3 -m math_gauge prepare --case MG-C002 --out runs/chapter02
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
```

每次输出目录须是新的。`validate` 检查合同与身份，`prepare` 导出候选材料；两者均不调用模型。实际消息由 `candidate_message(request)` 构造，完整传递题面及白名单附件。参考、评分、来源、真假、审核和作者证明留在评审侧；实际运行隔离另按[协议](protocol/isolated-cli-runs.md)核验。

题材来自公开 OET、公开数学资料与独立构造。来源、版本、署名与许可见 [SOURCES.md](SOURCES.md)。公开题可能进入训练数据，本项目不声称它们对模型必然未见。历史版本与实验由 Git 保存，恢复入口见[仓库地图](docs/repository-map.md)。

仓库采用 [MIT 许可证](LICENSE)；第三方材料保留各自的许可和署名。
