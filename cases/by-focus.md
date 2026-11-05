# 按考察重点选卷

本目录覆盖当前26份相关任务：22份数学卷与4份真实答卷审阅。默认任务关联18个母题家族。当前数学任务含226项阶段或章节义务。另有15项书面证明评审判准。阶段、义务、评审判准及审阅维度均不能当作独立试题。

分类是AI审查建议；源题全部仍为 **draft / human pending**。本目录不产生模型调用、数学裁定或新增判卷要求，也不证明作者或候选Lean覆盖。完整要求以唯一题面和合同为准。

每份任务恰有1个主重点和2–4个次重点。主重点构成互斥阅读索引；多标签层可以重叠，数量不能相加。数学任务的证据指向实际阶段、义务或最终目标的评审判准，审阅任务指向审阅维度，不能据此增加证明路线或Lean交付义务。这些标签没有另行冻结子分数，不重复加权。

中性自查、支持/怀疑立场和重复轮次属于执行维度，见[可靠性执行协议](../protocol/reliability-execution.md)。数学主题和任务类型是其他交叉索引。

本页仅供出题侧，不能附入候选输入；候选材料继续由共享runner按每题显式投影生成。

| 考察重点 | 主重点任务数 | 含该标签任务数 |
| --- | ---: | ---: |
| F01 假设及作用域 | 1 | 19 |
| F02 量词与常数一致性 | 2 | 9 |
| F03 定义域、局部整体与提升 | 5 | 22 |
| F04 结论强度与收敛 | 2 | 10 |
| F05 存在、取到与极限 | 1 | 4 |
| F06 构造、分类与自然性 | 5 | 12 |
| F07 证明链与依赖管理 | 2 | 9 |
| F08 Lean语义对齐 | 4 | 8 |
| F09 完整Lean工程交付 | 4 | 4 |

## F01 假设及作用域

核查结构假设的实际作用与局部生效范围；区分必要条件、充分条件与某条证明路线的要求。

不因题中存在假设就自动标记；需有明确的假设改变、删除或作用对象切换。

### 主重点 · 1份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR004 · 真实答卷审阅 004：半局部邻域、下降与层化的依赖比较](answer-review/MG-AR004/task.md) · [合同](answer-review/MG-AR004/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：区分半局部输入与任意光滑积分对象上的错误全局加强，不借已知主结论追认错误证明。 |

### 次重点 · 18份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [AHR01 · 节点域加细的语义审计](lean-audit/AHR01/task.md) · [合同](lean-audit/AHR01/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [AHR02 · 路径保证域的语义审计](lean-audit/AHR02/task.md) · [合同](lean-audit/AHR02/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [AHR03 · 节点域加细的语义审计](lean-audit/AHR03/task.md) · [合同](lean-audit/AHR03/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [AHR04 · 路径保证域的语义审计](lean-audit/AHR04/task.md) · [合同](lean-audit/AHR04/group-contract.json) | 默认 | 0.1.0 · 4审阅维度 | **evidence**：对差异或对齐结论给出保持原始条件的证据。 |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) · [合同](answer-review/MG-AR001/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：核对nil条件的逐元素作用与交换性，不额外要求全核统一指数或2可逆。 |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) · [合同](answer-review/MG-AR002/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **completeness**：保留有限域通常紧性与任意域代数延拓的不同适用范围。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：商同伦使用非空可缩子复形条件；**S5**：删除B后需重新处理空link和孤立顶点。 |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 默认 | 0.1.1 · 6阶段 | **S5**：域任意且点不必在原X闭，不能增添无限、完美域或闭点条件。 |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：全记录恢复阶段增加自反性；**S5**：单条记录改用明确的弱星连续条件，要求充要性。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：下半连续和次水平集紧性有独立职责；**S5**：保留闭凸而不给次水平紧性时，重新检查有限投影。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：余极限结构映射不预设单射；**S4**：秩一过渡允许零和负整数，分类须覆盖全部分支。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：有限自由作用是特殊实现阶段的条件，后续一般层阶段不保留该假设。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：第一可数与局部紧分别支持不同的求值和k化结论。 |
| [MG-GR014 · 线性关系、坐标纤维与无限赋值](proofs/MG-GR014/task.md) · [合同](proofs/MG-GR014/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：允许任意域和任意指标，不能保留S3有限域紧性作为隐藏条件；**S6**：无限离散域的坐标像闭性须给代数延拓或有限闭方程证明，不能把某条紧像证明的要求当作结论的必要条件。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **feasibility_counts_liftability**：保持原矩阵的交换、近幂等与近对称条件，不偷换为已幂等投影。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **universal_group_action**：任意群的局部固定条件与全体固定点不可混同，核对选择公理。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：精确传递使用左伴随；**S5**：改用保持底元和ω链上确界的另一机制，仍不要求右伴随。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 默认 | 0.1.1 · 6阶段 | **S5**：各增广满射与过渡满射分别核验；**S6**：非交换平方零核阶段另查唯一性所需乘法结构。 |

## F02 量词与常数一致性

保持量词顺序、统一或逐对象常数、同一个界、共同阶段及固定参数的依赖关系。

收敛方式本身归F04；有限/无限或常数更换涉及量词交换时使用本标签。

### 主重点 · 2份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：全部允许损失的估计要求同一参数下常数独立于所有u；**S5**：邻近全部无理方向另要求共同s和C；**S6**：不可解构造要求同一个光滑F，而非每阶各一个坏频率。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：单层只要求每个核元素各自幂零，不给统一指数；**S3**：比较逐层指数与极限元素的共同幂零指数。 |

### 次重点 · 7份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) · [合同](lean-formalization/MG-C003/contract.json) | 默认 | 0.1.1 · 92义务 | **CH03-P10-02**：逐基点计算合法半径及正点态半径；**CH03-P10-03**：在同一固定域上再取基点下确界；**CH03-P20-01**：对任意输入尺度在同一阶跃例中选择二点，保留量词顺序。 |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 默认 | 0.1.1 · 6阶段 | **S6**：逐同调类在某后阶段消失与统一尾部阶段正合的量词分开。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 默认 | 0.1.1 · 6阶段 | **S5**：区分每个当前层与存在足够后层的回缩要求；**S6**：检查无限积各坐标代表能否使用同一有限层。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：只在单点上的稳定子检验与全部测试对象的检验分开。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **optimal_quantitative_descent**：确定对所有输入成立的最大下降精度，并逐精度构造最优性证据。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **B**：分类任意非负指数列，不能把无界强化成整列趋于无穷。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **truncation**：覆盖所有截断参数、空底集、各纤维及有限作用精确基数。 |

## F03 定义域、局部整体与提升

区分原对象、商、完成、实际像域及受限域；核查有限或局部数据提升到整体的条件。

仅出现子集或商记号不足以标记，需实际的值域或实现边界。

### 主重点 · 5份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) · [合同](answer-review/MG-AR003/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：核对固定源与目标的映射集识别，不能擅自将目标细化而保持原源不变。 |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：记录先与E″双向等距识别，而不直接视为原E元素；**S4**：一般Banach阶段明确要求恢复值属于原E。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：建立一般层的完整下降判据和任意层基底相容性；**S5**：使用局部满射基底反映下降；**S6**：另检查仅非空可表示基底的检验范围。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：探针识别的连续映射目标是kX、kY；**S5**：再检查探针同构能否提升为原拓扑同胚。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **feasibility_counts_liftability**：区分有限同余类与真正整数解的截断，给可计算的可提升充要判据。 |

### 次重点 · 17份（完整题库）

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
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：包含指定点的邻域系需证明实际余终；**S4**：稠密开与保留全部半局部点不能混同。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：全记录实现须在同一个统一成本界的紧集内处理有限交。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 默认 | 0.1.1 · 6阶段 | **S5**：从实际稳定像构造延拓，并核验F_P与Hom(I_n0,-)的实际记录对应。 |
| [MG-GR014 · 线性关系、坐标纤维与无限赋值](proofs/MG-GR014/task.md) · [合同](proofs/MG-GR014/contract.json) | 默认 | 0.1.1 · 6阶段 | **S5**：把全赋值空间改为有限支持赋值空间后，重新检查整体可解性。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **A**：由实际相容商记录恢复受限坐标模型并绑定全部诱导映射。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **invariant_classification**：拓扑相容的内在分类须控制全部固定记录而非仅点值像。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：幂等族相容提升与任意元素的整体提升不等同；**S5**：重新判定极限增广的全部元素满射性。 |

## F04 结论强度与收敛

区分包含与相等、单向与等价、必要与充分、逐点/强收敛与一致/范数收敛，以及能否逆推。

存在性或极值取得的专门障碍归F05；同一要求可交叉标记但不重复充数。

### 主重点 · 2份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **B**：完成后的核、像与闭包分开，有限商同构不提高为原商单射。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：分别给两个单边更新关系的有向比较；**S4**：精确半共轭的固定点像与最小固定点等式分开。 |

### 次重点 · 8份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) · [合同](answer-review/MG-AR003/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：区分固定目标的错误识别与关于所有目标的有效充要结论，限制反例实际反驳范围。 |
| [MG-C003 · OET卷1第3章整章形式化](lean-formalization/MG-C003/candidate/task.md) · [合同](lean-formalization/MG-C003/contract.json) | 默认 | 0.1.1 · 92义务 | **CH03-P08-03**：商值判据回到点值判据需核验两实际像集分离；**CH03-P23-03**：熵差为零仅在差值良定的范围使用；**CH03-P29-05**：删除直径条件后对整体零化的加强另作反例义务。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：有理同调和整数扭结信息分开；**S6**：悬挂等价能否逆向消去需另给完整论证。 |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：有限频带形式逆须升级为真正光滑解及截断误差；**S4**：给定C^(m+4)到C^m结论不能由更弱输入范数要求代替。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：一般目标是最大下半连续凸下界；**S6**：区分恢复原f、投影闭化和能否省略外层闭化。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 默认 | 0.1.1 · 6阶段 | **S5**：区分探针自然同构与原拓扑同胚的结论层级。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **reduction_maps_and_fixed_lifts**：有限固定类、固定实际提升及相容无限塔不可相互替代。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **product_boundary**：任意乘积满射、有限因子双射与两个无限因子单射边界分别裁决。 |

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
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S6**：证明C+ε的有限观测精确匹配，并另判定ε=0是否可取。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 默认 | 0.1.1 · 6阶段 | **S6**：可数迭代上确界成为最小固定点须给出必要充分条件。 |

## F06 构造、分类与自然性

完成实际对象的双向构造、全部解/态射/自由度分类，区分自然运输与自然首选。

不以只给一个实例替代全分类；并不规定必须复刻作者路线。

### 主重点 · 5份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) · [合同](answer-review/MG-AR001/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：审阅逐元素幂等提升、层间唯一性组装和自然分解；允许实际有效的替代构造。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：要求全部可能同伦类型、全部类型的实际实现以及有限充要判据。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：分类全部群值自然变换及复合；**S3**：给出非循环表示性判据并构造全部表示对象。 |
| [MG-GR014 · 线性关系、坐标纤维与无限赋值](proofs/MG-GR014/task.md) · [合同](proofs/MG-GR014/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：从给定行和常数构造整体解，并完整分类所有坐标像和非空纤维。 |
| [MG-GR023 · 有限测试记录与群作用](proofs/MG-GR023/task.md) · [合同](proofs/MG-GR023/contract.json) | 默认 | 0.1.0 · 5评审判准 | **truncation**：全部有限测试记录与自然性同时分类，保持截断间遗忘映射。 |

### 次重点 · 7份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) · [合同](answer-review/MG-AR002/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：核查非齐次解集是仿射对象而非线性子空间，以合法例子并限定修复范围。 |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：完整分类可逆方向和全部非负Sobolev损失。 |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：给出记录载体与T″作用的双向构造；**S3**：由记录完整描述闭子空间成员及距离的对偶公式。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：分类对象、全部态射和自同构群；**S3**：不预选D而分类所有实现。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 默认 | 0.1.1 · 6阶段 | **S3**：构造全部参数化映射记录的Hausdorff实现和指数律；**S6**：构造同时变化的连续复合并验证单位与结合。 |
| [MG-GR021 · 同时分块与二次扩张上的下降](proofs/MG-GR021/task.md) · [合同](proofs/MG-GR021/contract.json) | 默认 | 0.1.0 · 5评审判准 | **optimal_quantitative_descent**：必须用实际整数正交解给最优性反例，有限形式解不够。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **C**：区分集合提升与S线性右逆，必须给精确分裂判准及障碍。 |

## F07 证明链与依赖管理

在条件变化后核对前序结论的合法复用、共享构造的一致性及长证明链中真实依赖。

不指参数连续依赖；不因contract有depends_on就标记；参考图不强制唯一证明路线。

### 主重点 · 2份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR002 · 真实答卷审阅 002：线性关系、坐标纤维与无限赋值](answer-review/MG-AR002/task.md) · [合同](answer-review/MG-AR002/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：定位附加第三条路线的缺口，同时保留正文与两条独立有效的闭性证明。 |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：图追依赖保覆盖收缩的正合输入和交上单射；**S5**：几何定理的实际条件、保点收缩与层化比较须逐项核对，可用合法直接定理路线。 |

### 次重点 · 7份（完整题库）

| 任务 | 成员 | 版本与规模 | 实际阶段、义务、评审判准或审阅维度证据 |
| --- | --- | --- | --- |
| [MG-AR001 · 真实答卷审阅 001：幂等元提升、逆极限与环分解](answer-review/MG-AR001/task.md) · [合同](answer-review/MG-AR001/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：区分层间唯一性、极限核与元素提升的依赖，不把参考中的额外非交换存在证明加入原任务。 |
| [MG-AR003 · 真实答卷审阅 003：探针映射空间与连续性层级](answer-review/MG-AR003/task.md) · [合同](answer-review/MG-AR003/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **core_judgment**：区分普通指数律的引用条件错位与后文独立有效CGHaus路线，不把前者传播为全部结论假。 |
| [MG-AR004 · 真实答卷审阅 004：半局部邻域、下降与层化的依赖比较](answer-review/MG-AR004/task.md) · [合同](answer-review/MG-AR004/group-contract.json) | 默认 | 0.2.0 · 3审阅维度 | **evidence_scope**：追踪错误全局单射在比较图中的真实用途，同时保留其他独立有效阶段。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 默认 | 0.1.1 · 6阶段 | **S4**：使用S1/S2的商和拼接结论前，须验证闭子复形、cofibration或实际替代条件。 |
| [MG-GR022 · 对角呈示的完成与商拓扑](proofs/MG-GR022/task.md) · [合同](proofs/MG-GR022/contract.json) | 默认 | 0.1.0 · 5评审判准 | **D**：追踪完成典范映射，区分子模自身与继承的两种拓扑。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 默认 | 0.1.1 · 6阶段 | **S1**：各中间参数最小解及约化系统须先良定义且单调；**S2**：传递结论须与所有分块结果及同一参数恢复一致。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 默认 | 0.1.1 · 6阶段 | **S2**：由单层提升唯一性建立相容族，并逐项验证正交、求和及分解。 |

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
