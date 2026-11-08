# 当前试卷

0.6.0默认题集 `cases/suite.json` 含25份相关任务，关联21个母题家族。完整题库含21份数学卷与4份真实答卷审阅，共184项阶段或章节义务，另有33项书面证明评审判准。相关任务、判准及审阅维度不构成独立数学家族。

材料具参考、判准、来源及AI审核记录，题目与当前答卷仍为 **human pending**。已有数学答卷及8份候选审阅答卷；AR纳入、评分与统一重评属于观察结果后的方法变更，详见[审阅说明](../docs/answer-review.md)与[当前结果](../docs/results.md)。已发布资产保持原样。

题面与附件由共享runner按 `case.json` 显式投影；本目录、分类、参考、评分和审核记录均为出题侧材料。参考与既有历史继续公开以供透明复核，不进入 solver 题包，也不构成未公开留出集。

[按考察重点选卷](by-focus.md) · [机器目录](catalog.json) · [分类定义与逐项依据](taxonomy.json) · [来源](../SOURCES.md) · [验证状态](../docs/verification.md)

## 大类与子类

| 大类 | 子类 | 权重 | 公有题 | 私有题 | 状态 |
|---|---|---:|---:|---:|---|
| 书面证明（35%） | 书面论证 | 25% | 8 | 4 | 当前计分 |
| 书面证明（35%） | 论证审阅 | 10% | 4 | 0 | 当前计分 |
| Lean（35%） | 语义审计 | 10% | 4 | 0 | 当前计分 |
| Lean（35%） | 形式化 | 15% | 4 | 0 | 当前计分 |
| Lean（35%） | 对齐自查 | 10% | 复用1题/3轮 | 0 | 当前计分 |
| 数学研究（30%） | 背景核查 | 10% | 2 | 2 | 当前计分 |
| 数学研究（30%） | 数学想法手稿化 | 10% | 1 | 4 | 当前计分 |
| 数学研究（30%） | 命题拓展 | 10% | 2 | 4 | 当前计分 |

当前25道公有与14道私有题合并评测，权重覆盖100/100。未测项目保持未知，不重新归一化，也不计为模型答错。私有书面题并入同一书面论证池；命题拓展与背景核查按上表固定家族数、仅按无提示A1计分。自查复用整章题，不另增题目或独立家族。


## 书面论证 · 8份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) | written | 6阶段 | [合同](proofs/MG-GP001/contract.json) · [参考](proofs/MG-GP001/reference.md) · [评分](proofs/MG-GP001/rubric.json) · [题包复核](proofs/MG-GP001/review.json) · [作者Lean](proofs/MG-GP001/formal/COVERAGE.md) |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) | written | 6阶段 | [合同](proofs/MG-GP002/contract.json) · [参考](proofs/MG-GP002/reference.md) · [评分](proofs/MG-GP002/rubric.json) · [题包复核](proofs/MG-GP002/review.json) · [作者Lean](proofs/MG-GP002/formal/COVERAGE.md) |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) | written | 6阶段 | [合同](proofs/MG-GR005/contract.json) · [参考](proofs/MG-GR005/reference.md) · [评分](proofs/MG-GR005/rubric.json) · [题包复核](proofs/MG-GR005/review.json) · [作者Lean](proofs/MG-GR005/formal/COVERAGE.md) |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) | written | 6阶段 | [合同](proofs/MG-GR009/contract.json) · [参考](proofs/MG-GR009/reference.md) · [评分](proofs/MG-GR009/rubric.json) · [题包复核](proofs/MG-GR009/review.json) · [作者Lean](proofs/MG-GR009/formal/COVERAGE.md) |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) | written | 5评审判准 | [合同](proofs/MG-GR021/contract.json) · [参考](proofs/MG-GR021/reference.md) · [评分](proofs/MG-GR021/rubric.json) · [题包复核](proofs/MG-GR021/review.json) |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) | written | 5评审判准 | [合同](proofs/MG-GR022/contract.json) · [参考](proofs/MG-GR022/reference.md) · [评分](proofs/MG-GR022/rubric.json) · [题包复核](proofs/MG-GR022/review.json) |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) | written | 5评审判准 | [合同](proofs/MG-GR023/contract.json) · [参考](proofs/MG-GR023/reference.md) · [评分](proofs/MG-GR023/rubric.json) · [题包复核](proofs/MG-GR023/review.json) |
| [MG-PS001 · 密度零商上的取样算子及其迭代](proofs/MG-PS001/task.md) | written | 6评审判准 | [合同](proofs/MG-PS001/contract.json) · [参考](proofs/MG-PS001/reference.md) · [评分](proofs/MG-PS001/rubric.json) · [题包复核](proofs/MG-PS001/review.json) |

## 语义审计 · 4份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [AHR01 · 节点域加细的语义审计](lean-audit/AHR01/task.md) | audit | 4审阅维度 | [合同](lean-audit/AHR01/group-contract.json) · [参考](lean-audit/AHR01/reference.md) · [评分](lean-audit/AHR01/rubric.json) · [题包复核](lean-audit/AHR01/integration-review.json) |
| [AHR02 · 路径保证域的语义审计](lean-audit/AHR02/task.md) | audit | 4审阅维度 | [合同](lean-audit/AHR02/group-contract.json) · [参考](lean-audit/AHR02/reference.md) · [评分](lean-audit/AHR02/rubric.json) · [题包复核](lean-audit/AHR02/integration-review.json) |
| [AHR03 · 节点域加细的语义审计](lean-audit/AHR03/task.md) | audit | 4审阅维度 | [合同](lean-audit/AHR03/group-contract.json) · [参考](lean-audit/AHR03/reference.md) · [评分](lean-audit/AHR03/rubric.json) · [题包复核](lean-audit/AHR03/review.json) |
| [AHR04 · 路径保证域的语义审计](lean-audit/AHR04/task.md) | audit | 4审阅维度 | [合同](lean-audit/AHR04/group-contract.json) · [参考](lean-audit/AHR04/reference.md) · [评分](lean-audit/AHR04/rubric.json) · [题包复核](lean-audit/AHR04/integration-review.json) |

## 形式化 · 4份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [HCH02 · 历史完整算子界章节的Lean形式化与多轮对齐](lean-formalization/HCH02/candidate/task.md) | generate | 40义务 | [合同](lean-formalization/HCH02/contract.json) · [参考](lean-formalization/HCH02/reference.md) · [评分](lean-formalization/HCH02/rubric.json) · [题包复核](lean-formalization/HCH02/integration-review.json) |
| [LCH01 · 通道接口节群](lean-formalization/LCH01/candidate/task.md) | generate | 8义务 | [合同](lean-formalization/LCH01/contract.json) · [参考](lean-formalization/LCH01/reference.md) · [评分](lean-formalization/LCH01/rubric.json) · [题包复核](lean-formalization/LCH01/integration-review.json) |
| [LCH02 · 有限复合与路径节群](lean-formalization/LCH02/candidate/task.md) | generate | 20义务 | [合同](lean-formalization/LCH02/contract.json) · [参考](lean-formalization/LCH02/reference.md) · [评分](lean-formalization/LCH02/rubric.json) · [题包复核](lean-formalization/LCH02/integration-review.json) |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) | generate | 92义务 | [合同](lean-formalization/MG-C003/contract.json) · [参考](lean-formalization/MG-C003/reference.md) · [评分](lean-formalization/MG-C003/rubric.json) · [题包复核](lean-formalization/MG-C003/review.json) · [作者Lean](lean-formalization/MG-C003/formal/COVERAGE.md) |

## 论证审阅 · 4份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR001/group-contract.json) · [参考](answer-review/MG-AR001/reference.md) · [评分](answer-review/MG-AR001/rubric.json) · [题包复核](answer-review/MG-AR001/review.json) |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR002/group-contract.json) · [参考](answer-review/MG-AR002/reference.md) · [评分](answer-review/MG-AR002/rubric.json) · [题包复核](answer-review/MG-AR002/review.json) |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR003/group-contract.json) · [参考](answer-review/MG-AR003/reference.md) · [评分](answer-review/MG-AR003/rubric.json) · [题包复核](answer-review/MG-AR003/review.json) |
| [MG-AR004 · 真实答卷审阅 004：半局部邻域、下降与层化的依赖比较](answer-review/MG-AR004/task.md) | answer_review | 3审阅维度 | [合同](answer-review/MG-AR004/group-contract.json) · [参考](answer-review/MG-AR004/reference.md) · [评分](answer-review/MG-AR004/rubric.json) · [题包复核](answer-review/MG-AR004/review.json) |

## 命题拓展 · 2份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-TX001 · 素数幂单位根稀疏消去](theorem-extension/MG-TX001/task.md) | written | 3评审判准 | [合同](theorem-extension/MG-TX001/contract.json) · [参考](theorem-extension/MG-TX001/reference.md) · [评分](theorem-extension/MG-TX001/rubric.json) · [题包复核](theorem-extension/MG-TX001/review.json) |
| [MG-TX002 · 矩形反链轨道平均](theorem-extension/MG-TX002/task.md) | written | 3评审判准 | [合同](theorem-extension/MG-TX002/contract.json) · [参考](theorem-extension/MG-TX002/reference.md) · [评分](theorem-extension/MG-TX002/rubric.json) · [题包复核](theorem-extension/MG-TX002/review.json) |

## 背景核查 · 2份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-BC001 · 四井刚性推广与实际零边界构造](background-check/MG-BC001/task.md) | written | 3评审判准 | [合同](background-check/MG-BC001/contract.json) · [参考](background-check/MG-BC001/reference.md) · [评分](background-check/MG-BC001/rubric.json) · [题包复核](background-check/MG-BC001/review.json) |
| [MG-BC002 · 精确梯度流与凸近端表示](background-check/MG-BC002/task.md) | written | 3评审判准 | [合同](background-check/MG-BC002/contract.json) · [参考](background-check/MG-BC002/reference.md) · [评分](background-check/MG-BC002/rubric.json) · [题包复核](background-check/MG-BC002/review.json) |

## 数学想法手稿化 · 1份

| 试卷 | 任务 | 必答规模 | 完整材料 |
| --- | --- | ---: | --- |
| [MG-MCP003 · 扩展伪度量下的矩阵估计与不可分辨性](manuscript-completion/MG-MCP003/task.md) | written | 6评审维度 | [合同](manuscript-completion/MG-MCP003/contract.json) · [参考](manuscript-completion/MG-MCP003/reference.md) · [评分](manuscript-completion/MG-MCP003/rubric.json) · [题包复核](manuscript-completion/MG-MCP003/review.json) |

旧题和备选题通过Git历史恢复。审阅可用独立清单answer-review-suite.json选择。

所有路径和候选输入散列由 `python3 scripts/catalog.py` 从当前合同生成；`--check`只读核验。
