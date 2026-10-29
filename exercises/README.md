# Math Gauge 习题集

本页的已测原版共 **41 题**，按七个数学主题编排：29 道数学论证题，以及六个母题的 12 道 Lean 对齐任务。题号和原始文件路径保持不变，各章节直接链接唯一题面。

数学论证题要求完成题面中的证明、反例、构造或分类；Lean 对齐任务分为判定、生成和修复。不要从题号、题目来源或历史结果猜测结论。

另有[下一版递进题组目录](../drafts/progressive-groups-20261030/README.md)，将这些母题逐一扩展，保留旧题及历史测评；[卷1第2/3章整章Lean考试](../drafts/chapter-exams-20261030/README.md)独立编排。新题组以全组为一个样本，不能把相关小题当成独立通过率。其状态、逐项条件及判卷约束见[题组协议](../protocol/question-groups.md)。本页七章与catalog.json继续标识已测的原41题。

下一轮采用这43份试卷的0.1.1题面，每题三次独立作答；另在[预选八题](../protocol/reliability-20261030/selection.md)上安排两轮中性自查及双方向立场分支。分值和判卷提示已移出新task，统一见[评分标准](../protocol/reliability-scoring.md)与各题评审合同。[材料包](../protocol/reliability-20261030/README.md)记录消息、版本和未执行状态；旧41题及已测成绩不回写。

## 按数学主题阅读

| 章节 | 题数 | 内容 |
| --- | ---: | --- |
| [第一章 · 算子、轨道与不动点](chapters/01-operators-and-dynamics.md) | 6 | MG-R001、MG-R003、MG-R102、MG-R103、MG-F109、MG-F110 |
| [第二章 · 分析、观测与最优恢复](chapters/02-analysis-and-recovery.md) | 10 | MG-R002、MG-R004、MG-R005、MG-R011、MG-R012、MG-R013、MG-R105、MG-R106、MG-F111、MG-F112 |
| [第三章 · 代数、商结构与相容提升](chapters/03-algebra-and-compatible-lifting.md) | 11 | MG-R006、MG-R007、MG-R008、MG-R014、MG-R015、MG-R016、MG-R020、MG-R101、MG-R104、MG-F101、MG-F102 |
| [第四章 · 拓扑、下降与空间重构](chapters/04-topology-and-descent.md) | 7 | MG-R009、MG-R010、MG-R017、MG-R018、MG-R019、MG-F103、MG-F104 |
| [第五章 · 有限集与定量覆盖](chapters/05-finite-covering.md) | 2 | MG-F105、MG-F106 |
| [第六章 · Fourier 分析与正则性](chapters/06-fourier-and-regularity.md) | 3 | MG-P002、MG-F107、MG-F108 |
| [第七章 · 几何拼接与层化比较](chapters/07-geometric-proof-mechanisms.md) | 2 | MG-P001、MG-P003 |

## 使用这套习题

- [按任务类型选题](task-types.md)：数学论证、Lean 判定、Lean 生成和 Lean 修复。
- [出题与审核材料](instructor-guide.md)：参考解、来源、独立审核及 Lean 覆盖账本，仅供出题侧使用。
- [版本与历史对应](history.md)：旧版、退役题集和初始草稿单独保留，不重复计入 41 题。
- [正式试跑验收清单](../results/r005-clarified-v0.3.1-20261030/qualification/README.md)：完整数学参考与独立审核为出题门槛，Lean 证据另列。
- [机器目录](catalog.json)：精确版本、suite 根路径、母题、来源和文件散列。

当前全部题目仍为 **draft / human pending**。首轮整体对比覆盖全部 41 题；版本修订后的单题补测另行记录。其中 40 题的原始主目标已有完整作者 Lean 证据，MG-P003 保留完整数学题面并明确列出尚未完成的形式化。该 40 题子集只作分层统计，不替代整体成绩。

本目录是阅读和出题索引。实际模型输入必须由原有共享 runner 按每题显式投影生成；本目录、参考解、评分、来源、历史结果和作者形式化均不得附入候选输入。

索引重建：在仓库根目录运行 `python3 exercises/refresh_catalog.py`；所有源工件完成并核对后使用 `--final` 固定新快照。重建目录不启动模型，也不改变原题或人工状态。冻结后可用 `python3 exercises/refresh_catalog.py --check` 只读核对，不改变目录散列。
