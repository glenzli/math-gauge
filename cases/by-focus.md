# 按考察重点选卷

本目录覆盖当前25份相关任务：21份数学卷与4份真实答卷审阅。默认任务关联21个母题家族。当前数学任务含184项阶段或章节义务。另有33项书面证明评审判准。阶段、义务、评审判准及审阅维度均不能当作独立试题。

分类是AI审查建议；源题全部仍为 **draft / human pending**。本目录不产生模型调用、数学裁定或新增判卷要求，也不证明作者或候选Lean覆盖。完整要求以唯一题面和合同为准。

每份任务恰有1个主重点和2–4个次重点。主重点构成互斥阅读索引；多标签层可以重叠，数量不能相加。数学任务的证据指向实际阶段、义务或最终目标的评审判准，审阅任务指向审阅维度，不能据此增加证明路线或Lean交付义务。这些标签没有另行冻结子分数，不重复加权。

主计分采用书面证明35%、Lean35%、数学研究30%的大类/子类结构。Lean对齐自查单独占10%，复用一题三轮，不新增数学家族；书面中性、立场压力与独立复答不再进入默认计分。下列F01..F09仅为交叉能力标签，见[评分规则](../protocol/benchmark-scoring.md)。

本页仅供出题侧，不能附入候选输入；候选材料继续由共享runner按每题显式投影生成。

| 考察重点 | 主重点任务数 | 含该标签任务数 |
| --- | ---: | ---: |
| F01 假设及作用域 | 1 | 15 |
| F02 量词与常数一致性 | 1 | 7 |
| F03 定义域、局部整体与提升 | 3 | 18 |
| F04 结论强度与收敛 | 3 | 12 |
| F05 存在、取到与极限 | 1 | 4 |
| F06 构造、分类与自然性 | 7 | 14 |
| F07 证明链与依赖管理 | 1 | 8 |
| F08 Lean语义对齐 | 4 | 8 |
| F09 完整Lean工程交付 | 4 | 4 |

## F01 假设及作用域

核查结构假设的实际作用与局部生效范围；区分必要条件、充分条件与某条证明路线的要求。

不因题中存在假设就自动标记；需有明确的假设改变、删除或作用对象切换。

### 主重点 · 1份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR004 · 真实答卷审阅 004：半局部邻域、下降与层化的依赖比较](answer-review/MG-AR004/task.md) · [合同](answer-review/MG-AR004/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：区分半局部输入与任意光滑积分对象上的错误全局加强，不借已知主结论追认错误证明。 |

### 次重点 · 14份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [AHR01 · 节点域加细的语义审计](lean-audit/AHR01/task.md) · [合同](lean-audit/AHR01/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [AHR02 · 路径保证域的语义审计](lean-audit/AHR02/task.md) · [合同](lean-audit/AHR02/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [AHR03 · 节点域加细的语义审计](lean-audit/AHR03/task.md) · [合同](lean-audit/AHR03/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [AHR04 · 路径保证域的语义审计](lean-audit/AHR04/task.md) · [合同](lean-audit/AHR04/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) · [合同](answer-review/MG-AR001/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：核对nil条件的逐元素作用与交换性，不额外要求全核统一指数或2可逆。 |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) · [合同](answer-review/MG-AR002/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **completeness**：保留有限域通常紧性与任意域代数延拓的不同适用范围。 |
| [MG-BC001 · 四井刚性推广与实际零边界构造](background-check/MG-BC001/task.md) · [合同](background-check/MG-BC001/contract.json) | 默认 | 0.1.0 · 3评审判准 | **complete-correction**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-BC002 · 精确梯度流与凸近端表示](background-check/MG-BC002/task.md) · [合同](background-check/MG-BC002/contract.json) | 默认 | 0.1.0 · 3评审判准 | **complete-correction**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：商同伦使用非空可缩子复形条件；**S5**：删除B后需重新处理空link和孤立顶点。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：下半连续和次水平集紧性有独立职责；**S5**：保留闭凸而不给次水平紧性时，重新检查有限投影。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：有限自由作用是特殊实现阶段的条件，后续一般层阶段不保留该假设。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **feasibility_counts_liftability**：保持原矩阵的交换、近幂等与近对称条件，不偷换为已幂等投影。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **universal_group_action**：任意群的局部固定条件与全体固定点不可混同，核对选择公理。 |
| [MG-TX001 · 素数幂单位根稀疏消去](theorem-extension/MG-TX001/task.md) · [合同](theorem-extension/MG-TX001/contract.json) | 默认 | 0.2.0 · 3评审判准 | **complete-structure**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |

## F02 量词与常数一致性

保持量词顺序、统一或逐对象常数、同一个界、共同阶段及固定参数的依赖关系。

收敛方式本身归F04；有限/无限或常数更换涉及量词交换时使用本标签。

### 主重点 · 1份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：全部允许损失的估计要求同一参数下常数独立于所有u；**S5**：邻近全部无理方向另要求共同s和C；**S6**：不可解构造要求同一个光滑F，而非每阶各一个坏频率。 |

### 次重点 · 6份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) · [合同](lean-formalization/MG-C003/contract.json) | 默认 | 0.1.1 · 92义务 | **CH03-P10-02**：逐基点计算合法半径及正点态半径；**CH03-P10-03**：在同一固定域上再取基点下确界；**CH03-P20-01**：对任意输入尺度在同一阶跃例中选择二点，保留量词顺序。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：只在单点上的稳定子检验与全部测试对象的检验分开。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **optimal_quantitative_descent**：确定对所有输入成立的最大下降精度，并逐精度构造最优性证据。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **B**：分类任意非负指数列，不能把无界强化成整列趋于无穷。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **truncation**：覆盖所有截断参数、空底集、各纤维及有限作用精确基数。 |
| [MG-PS001 · 密度零商上的取样算子及其迭代](proofs/MG-PS001/task.md) · [合同](proofs/MG-PS001/contract.json) | 默认 | 0.1.0 · 6评审判准 | **K2**：必要性覆盖任意不允许的严格递增函数；不假定比值极限存在。 |

## F03 定义域、局部整体与提升

区分原对象、商、完成、实际像域及受限域；核查有限或局部数据提升到整体的条件。

仅出现子集或商记号不足以标记，需实际的值域或实现边界。

### 主重点 · 3份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) · [合同](answer-review/MG-AR003/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：核对固定源与目标的映射集识别，不能擅自将目标细化而保持原源不变。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：建立一般层的完整下降判据和任意层基底相容性；**S5**：使用局部满射基底反映下降；**S6**：另检查仅非空可表示基底的检验范围。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **feasibility_counts_liftability**：区分有限同余类与真正整数解的截断，给可计算的可提升充要判据。 |

### 次重点 · 15份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [AHR01 · 节点域加细的语义审计](lean-audit/AHR01/task.md) · [合同](lean-audit/AHR01/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：区分完整数学定义域、实际可达域或可评估路径域。 |
| [AHR02 · 路径保证域的语义审计](lean-audit/AHR02/task.md) · [合同](lean-audit/AHR02/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：区分完整数学定义域、实际可达域或可评估路径域。 |
| [AHR03 · 节点域加细的语义审计](lean-audit/AHR03/task.md) · [合同](lean-audit/AHR03/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：区分完整数学定义域、实际可达域或可评估路径域。 |
| [AHR04 · 路径保证域的语义审计](lean-audit/AHR04/task.md) · [合同](lean-audit/AHR04/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：区分完整数学定义域、实际可达域或可评估路径域。 |
| [HCH02 · 历史完整算子界章节的Lean形式化与多轮对齐](lean-formalization/HCH02/candidate/task.md) · [合同](lean-formalization/HCH02/contract.json) | 默认 | 0.1.0 · 40义务 | **HC02-D01**：保留合法评估域和全域/受限域的区别。 |
| [LCH01 · 通道接口节群](lean-formalization/LCH01/candidate/task.md) · [合同](lean-formalization/LCH01/contract.json) | 默认 | 0.1.0 · 8义务 | **CH02-D01**：保留合法评估域和全域/受限域的区别。 |
| [LCH02 · 有限复合与路径节群](lean-formalization/LCH02/candidate/task.md) · [合同](lean-formalization/LCH02/contract.json) | 默认 | 0.1.0 · 20义务 | **CH02-D01**：保留合法评估域和全域/受限域的区别。 |
| [MG-AR004 · 真实答卷审阅 004：半局部邻域、下降与层化的依赖比较](answer-review/MG-AR004/task.md) · [合同](answer-review/MG-AR004/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：核对任意指定点集与半局部概形实际闭点的区别，不能直接按原点集归纳。 |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) · [合同](lean-formalization/MG-C003/contract.json) | 默认 | 0.1.1 · 92义务 | **CH03-D05**：统一半径在A上取inf但在U评估；**CH03-P15-02**：复合下界使用下游实际像域上的半径；**CH03-P17-03**：同时缩小评估域和取inf基点集须分别追踪。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：判据须仅使用含v单形及其面关联的局部数据，并连接整体同伦型。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：全记录实现须在同一个统一成本界的紧集内处理有限交。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **A**：由实际相容商记录恢复受限坐标模型并绑定全部诱导映射。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **invariant_classification**：拓扑相容的内在分类须控制全部固定记录而非仅点值像。 |
| [MG-MCP003 · 扩展伪度量下的矩阵估计与不可分辨性](manuscript-completion/MG-MCP003/task.md) · [合同](manuscript-completion/MG-MCP003/contract.json) | 默认 | 0.1.0 · 6评审维度 | **M1**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-PS001 · 密度零商上的取样算子及其迭代](proofs/MG-PS001/task.md) · [合同](proofs/MG-PS001/contract.json) | 默认 | 0.1.0 · 6评审判准 | **K2**：核对零距等价类上的良定性，不能以逐项趋零代替密度零均值。 |

## F04 结论强度与收敛

区分包含与相等、单向与等价、必要与充分、逐点/强收敛与一致/范数收敛，以及能否逆推。

存在性或极值取得的专门障碍归F05；同一要求可交叉标记但不重复充数。

### 主重点 · 3份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-BC001 · 四井刚性推广与实际零边界构造](background-check/MG-BC001/task.md) · [合同](background-check/MG-BC001/contract.json) | 默认 | 0.1.0 · 3评审判准 | **complete-correction**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-BC002 · 精确梯度流与凸近端表示](background-check/MG-BC002/task.md) · [合同](background-check/MG-BC002/contract.json) | 默认 | 0.1.0 · 3评审判准 | **complete-correction**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **B**：完成后的核、像与闭包分开，有限商同构不提高为原商单射。 |

### 次重点 · 9份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) · [合同](answer-review/MG-AR003/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：区分固定目标的错误识别与关于所有目标的有效充要结论，限制反例实际反驳范围。 |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) · [合同](lean-formalization/MG-C003/contract.json) | 默认 | 0.1.1 · 92义务 | **CH03-P08-03**：商值判据回到点值判据需核验两实际像集分离；**CH03-P23-03**：熵差为零仅在差值良定的范围使用；**CH03-P29-05**：删除直径条件后对整体零化的加强另作反例义务。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：有理同调和整数扭结信息分开；**S6**：悬挂等价能否逆向消去需另给完整论证。 |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：有限频带形式逆须升级为真正光滑解及截断误差；**S4**：给定C^(m+4)到C^m结论不能由更弱输入范数要求代替。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：一般目标是最大下半连续凸下界；**S6**：区分恢复原f、投影闭化和能否省略外层闭化。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **reduction_maps_and_fixed_lifts**：有限固定类、固定实际提升及相容无限塔不可相互替代。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **product_boundary**：任意乘积满射、有限因子双射与两个无限因子单射边界分别裁决。 |
| [MG-TX001 · 素数幂单位根稀疏消去](theorem-extension/MG-TX001/task.md) · [合同](theorem-extension/MG-TX001/contract.json) | 默认 | 0.2.0 · 3评审判准 | **complete-structure**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-TX002 · 矩形反链轨道平均](theorem-extension/MG-TX002/task.md) · [合同](theorem-extension/MG-TX002/contract.json) | 默认 | 0.2.0 · 3评审判准 | **complete-structure**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |

## F05 存在、取到与极限

区分可行解、极值、下确界/上确界、端点取得及合法极限对象和交换。

不因证明中出现一个极限就标记；需存在、取得或极限合法性本身属于任务重点。

### 主重点 · 1份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：纤维公式明确要求说明是否使用下确界取到；**S2**：在紧次水平集条件下处理真实最优点。 |

### 次重点 · 3份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：最小允许损失和端点是否取到须分别证明。 |
| [MG-MCP003 · 扩展伪度量下的矩阵估计与不可分辨性](manuscript-completion/MG-MCP003/task.md) · [合同](manuscript-completion/MG-MCP003/contract.json) | 默认 | 0.1.0 · 6评审维度 | **M4**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-PS001 · 密度零商上的取样算子及其迭代](proofs/MG-PS001/task.md) · [合同](proofs/MG-PS001/contract.json) | 默认 | 0.1.0 · 6评审判准 | **K5**：以实际迭代常数和次可加性证明根极限存在。 |

## F06 构造、分类与自然性

完成实际对象的双向构造、全部解/态射/自由度分类，区分自然运输与自然首选。

不以只给一个实例替代全分类；并不规定必须复刻作者路线。

### 主重点 · 7份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) · [合同](answer-review/MG-AR001/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：审阅逐元素幂等提升、层间唯一性组装和自然分解；允许实际有效的替代构造。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：要求全部可能同伦类型、全部类型的实际实现以及有限充要判据。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **truncation**：全部有限测试记录与自然性同时分类，保持截断间遗忘映射。 |
| [MG-MCP003 · 扩展伪度量下的矩阵估计与不可分辨性](manuscript-completion/MG-MCP003/task.md) · [合同](manuscript-completion/MG-MCP003/contract.json) | 默认 | 0.1.0 · 6评审维度 | **M2**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-PS001 · 密度零商上的取样算子及其迭代](proofs/MG-PS001/task.md) · [合同](proofs/MG-PS001/contract.json) | 默认 | 0.1.0 · 6评审判准 | **K6**：对全部允许实数对构造合法取样并证明迭代增长率；端点不代替全参数实现。 |
| [MG-TX001 · 素数幂单位根稀疏消去](theorem-extension/MG-TX001/task.md) · [合同](theorem-extension/MG-TX001/contract.json) | 默认 | 0.2.0 · 3评审判准 | **complete-structure**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-TX002 · 矩形反链轨道平均](theorem-extension/MG-TX002/task.md) · [合同](theorem-extension/MG-TX002/contract.json) | 默认 | 0.2.0 · 3评审判准 | **complete-structure**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |

### 次重点 · 7份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) · [合同](answer-review/MG-AR002/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：核查非齐次解集是仿射对象而非线性子空间，以合法例子并限定修复范围。 |
| [MG-BC001 · 四井刚性推广与实际零边界构造](background-check/MG-BC001/task.md) · [合同](background-check/MG-BC001/contract.json) | 默认 | 0.1.0 · 3评审判准 | **complete-correction**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-BC002 · 精确梯度流与凸近端表示](background-check/MG-BC002/task.md) · [合同](background-check/MG-BC002/contract.json) | 默认 | 0.1.0 · 3评审判准 | **complete-correction**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：完整分类可逆方向和全部非负Sobolev损失。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：分类对象、全部态射和自同构群；**S3**：不预选D而分类所有实现。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **optimal_quantitative_descent**：必须用实际整数正交解给最优性反例，有限形式解不够。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **C**：区分集合提升与S线性右逆，必须给精确分裂判准及障碍。 |

## F07 证明链与依赖管理

在条件变化后核对前序结论的合法复用、共享构造的一致性及长证明链中真实依赖。

不指参数连续依赖；不因contract有depends_on就标记；参考图不强制唯一证明路线。

### 主重点 · 1份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) · [合同](answer-review/MG-AR002/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：定位附加第三条路线的缺口，同时保留正文与两条独立有效的闭性证明。 |

### 次重点 · 7份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) · [合同](answer-review/MG-AR001/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：区分层间唯一性、极限核与元素提升的依赖，不把参考中的额外非交换存在证明加入原任务。 |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) · [合同](answer-review/MG-AR003/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：区分普通指数律的引用条件错位与后文独立有效CGHaus路线，不把前者传播为全部结论假。 |
| [MG-AR004 · 真实答卷审阅 004：半局部邻域、下降与层化的依赖比较](answer-review/MG-AR004/task.md) · [合同](answer-review/MG-AR004/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：追踪错误全局单射在比较图中的真实用途，同时保留其他独立有效阶段。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：使用S1/S2的商和拼接结论前，须验证闭子复形、cofibration或实际替代条件。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **D**：追踪完成典范映射，区分子模自身与继承的两种拓扑。 |
| [MG-PS001 · 密度零商上的取样算子及其迭代](proofs/MG-PS001/task.md) · [合同](proofs/MG-PS001/contract.json) | 默认 | 0.1.0 · 6评审判准 | **K3**：统一控制所有前缀并证明最小常数尖锐，不能只给上界。 |
| [MG-TX002 · 矩形反链轨道平均](theorem-extension/MG-TX002/task.md) · [合同](theorem-extension/MG-TX002/contract.json) | 默认 | 0.2.0 · 3评审判准 | **complete-structure**：只按首答实际交付核验构造、适用条件和严格结论；接受有效替代路线。 |

## F08 Lean语义对齐

核对自然语言与Lean实际编码的对象、条件、量词、定义域、结论和覆盖；区分编译与语义完成。

书面审计不自动附加候选Lean源码义务；不以旧编译覆盖新阶段。

### 主重点 · 4份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [AHR01 · 节点域加细的语义审计](lean-audit/AHR01/task.md) · [合同](lean-audit/AHR01/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：逐项核对原文与实现的范围、前提及结论。 |
| [AHR02 · 路径保证域的语义审计](lean-audit/AHR02/task.md) · [合同](lean-audit/AHR02/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：逐项核对原文与实现的范围、前提及结论。 |
| [AHR03 · 节点域加细的语义审计](lean-audit/AHR03/task.md) · [合同](lean-audit/AHR03/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：逐项核对原文与实现的范围、前提及结论。 |
| [AHR04 · 路径保证域的语义审计](lean-audit/AHR04/task.md) · [合同](lean-audit/AHR04/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **judgment**：逐项核对原文与实现的范围、前提及结论。 |

### 次重点 · 4份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [HCH02 · 历史完整算子界章节的Lean形式化与多轮对齐](lean-formalization/HCH02/candidate/task.md) · [合同](lean-formalization/HCH02/contract.json) | 默认 | 0.1.0 · 40义务 | **HC02-D01**：表示须与原文定义、量词和作用域对应。 |
| [LCH01 · 通道接口节群](lean-formalization/LCH01/candidate/task.md) · [合同](lean-formalization/LCH01/contract.json) | 默认 | 0.1.0 · 8义务 | **CH02-D01**：表示须与原文定义、量词和作用域对应。 |
| [LCH02 · 有限复合与路径节群](lean-formalization/LCH02/candidate/task.md) · [合同](lean-formalization/LCH02/contract.json) | 默认 | 0.1.0 · 20义务 | **CH02-D01**：表示须与原文定义、量词和作用域对应。 |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) · [合同](lean-formalization/MG-C003/contract.json) | 默认 | 0.1.1 · 92义务 | **CH03-D03**：Lean表示须区分点相等、全族零距、实际像和商关系；**CH03-D07**：允许直接复用冻结内部覆盖定义，仍须给真实声明映射及原文对应。 |

## F09 完整Lean工程交付

交付完整且可共同编译的源码、实际声明对应和依赖闭包，并满足逐项语义、公理及冻结背景合同。

一个阶段或背景编译不能替代完整交付；源代码交付是本主题的必要任务事实。

### 主重点 · 4份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [HCH02 · 历史完整算子界章节的Lean形式化与多轮对齐](lean-formalization/HCH02/candidate/task.md) · [合同](lean-formalization/HCH02/contract.json) | 默认 | 0.1.0 · 40义务 | **HC02-D01**：本题列出的全部义务须在完整Lean工程中统一交付。 |
| [LCH01 · 通道接口节群](lean-formalization/LCH01/candidate/task.md) · [合同](lean-formalization/LCH01/contract.json) | 默认 | 0.1.0 · 8义务 | **CH02-D01**：本题列出的全部义务须在完整Lean工程中统一交付。 |
| [LCH02 · 有限复合与路径节群](lean-formalization/LCH02/candidate/task.md) · [合同](lean-formalization/LCH02/contract.json) | 默认 | 0.1.0 · 20义务 | **CH02-D01**：本题列出的全部义务须在完整Lean工程中统一交付。 |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) · [合同](lean-formalization/MG-C003/contract.json) | 默认 | 0.1.1 · 92义务 | **CH03-D01**：整章task要求所有92项定义、表示及证明共同编译，并交Main.lean及逐义务alignment.json。 |

### 次重点 · 0份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |

证据短句仅描述实际需求。F07不强制合同参考图的唯一路线；有效短证、合并声明、独立重证和替代证明仍按原合同接受。

[分类源](taxonomy.json) · [机器目录与源散列](catalog.json) · [全部试卷](README.md)
