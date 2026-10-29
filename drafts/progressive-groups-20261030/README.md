# 递进题组 · suite 0.1.2

当前GR001为0.1.2，其余40组为0.1.1。GR001的S6已明确有限值完备度量作用于非吸收部分X°，见[数学范围修订](reviews/strict-amendment-0.1.2.json)及[本轮严格复核](../../results/strict-review-20261030/README.md)。这次作用域澄清单独记录，不沿用“仅编辑等价”的结论。

0.1.1 清理了候选题面的分值、判卷提示和后序泄露的判断答案，并明确 audit 的书面交付范围；数学义务、权重、参考和 Lean 输入不变。旧材料与原复核保存在[0.1.0历史快照](history/0.1.0.json)，当前题面通过[编辑等价记录](reviews/editorial-amendment-0.1.1.json)衔接原数学复核。执行与评分采用[重复作答协议](../../protocol/reliability-execution.md)，八题子集见[选择说明](../../protocol/reliability-20261030/selection.md)。

本版把原41题逐一扩为 **41个题组、246个必答阶段**，按原七章组织。39组为6阶段，另有一组5阶段、一组7阶段。每组保留母题的完整最弱条件核心，并加入可复用的构造、证明、边界判定和综合问题。原题、原答卷及原通过率保持冻结。

29组数学论证、6组Lean审计、3组Lean生成、3组Lean修复；生成/修复仍要求完整源码。所有新组使用明确、可裁定的交付与分类目标，统一登记为determinate；这不回改母题的exploration轨，也不把历史探索发现重算为新成绩。

同一对象贯穿各阶段，条件变化不固定在某个题号，也不保证变化后为假。转折涉及量词、对象范围、局部与整体、取到与逼近、必要与充分、特定映射与抽象同构等。出题侧共记录110个转折断言（46真、64假，含综合阶段内明确划分的子断言）；这些断言不是110道独立题，真假及机制标签不进入候选输入。

每阶段都有条件清单、具体必需证据、关键错误和参考论证。按[题组协议](../../protocol/question-groups.md)逐项判卷；全组pass须全部必答阶段完成，部分分值不抵消缺口。允许有效短证、等价表示和替代路线；不以是否复刻作者证明判分。

全部41组的0.1.0材料已完成[独立AI数学复核](reviews/README.md)，当时所报问题按文件散列闭环；0.1.1通过编辑等价记录衔接，GR001的0.1.2另有新AI主审，未重复独立评审。人工审核仍待完成。机制如何组合、如何区分长答卷负担与条件误用，见[设计与校准说明](design-notes.md)。新Lean义务的完整作者实现尚待核验，本版不声称已经取得新的模型通过率。按考察重点横向选卷见[能力索引](../../exercises/by-focus.md)。

## 按原七章阅读

### 第一章 · 算子、轨道与不动点

| 题组 | 主题 | 阶段 | 参考与判准 |
|---|---|---:|---|
| [MG-GR001](MG-GR001/task.md) | 递归系统的固定族、稳定分支与终止 | 7 | [参考](MG-GR001/reference.md) · [合同](MG-GR001/contract.json) · [审核](MG-GR001/review.json) |
| [MG-GR003](MG-GR003/task.md) | 平均恢复、迭代误差与一致速度 | 6 | [参考](MG-GR003/reference.md) · [合同](MG-GR003/contract.json) · [审核](MG-GR003/review.json) |
| [MG-GR102](MG-GR102/task.md) | 有限轨道、规范投影与统一公式 | 6 | [参考](MG-GR102/reference.md) · [合同](MG-GR102/contract.json) · [审核](MG-GR102/review.json) |
| [MG-GR103](MG-GR103/task.md) | 参数最小不动点、消元与近似传递 | 6 | [参考](MG-GR103/reference.md) · [合同](MG-GR103/contract.json) · [审核](MG-GR103/review.json) |
| [MG-GF109](MG-GF109/task.md) | 有限记录、安全核与迟延前进 | 6 | [参考](MG-GF109/reference.md) · [合同](MG-GF109/contract.json) · [审核](MG-GF109/review.json) |
| [MG-GF110](MG-GF110/task.md) | 有限记录的可靠内近似与完整修复 | 6 | [参考](MG-GF110/reference.md) · [合同](MG-GF110/contract.json) · [审核](MG-GF110/review.json) |

### 第二章 · 分析、观测与最优恢复

| 题组 | 主题 | 阶段 | 参考与判准 |
|---|---|---:|---|
| [MG-GR002](MG-GR002/task.md) | 线性记录、有限观测与原空间恢复 | 6 | [参考](MG-GR002/reference.md) · [合同](MG-GR002/contract.json) · [审核](MG-GR002/review.json) |
| [MG-GR004](MG-GR004/task.md) | Hilbert复形的精确消元与近似消元 | 5 | [参考](MG-GR004/reference.md) · [合同](MG-GR004/contract.json) · [审核](MG-GR004/review.json) |
| [MG-GR005](MG-GR005/task.md) | 凸成本记录、紧性与闭上图恢复 | 6 | [参考](MG-GR005/reference.md) · [合同](MG-GR005/contract.json) · [审核](MG-GR005/review.json) |
| [MG-GR011](MG-GR011/task.md) | 凸投影的恢复、复合与变分方程 | 6 | [参考](MG-GR011/reference.md) · [合同](MG-GR011/contract.json) · [审核](MG-GR011/review.json) |
| [MG-GR012](MG-GR012/task.md) | 凸势、对偶与有限记录逼近 | 6 | [参考](MG-GR012/reference.md) · [合同](MG-GR012/contract.json) · [审核](MG-GR012/review.json) |
| [MG-GR013](MG-GR013/task.md) | 多项式记录、预解与谱的连续比较 | 6 | [参考](MG-GR013/reference.md) · [合同](MG-GR013/contract.json) · [审核](MG-GR013/review.json) |
| [MG-GR105](MG-GR105/task.md) | 观测完成、噪声误差与原空间极小点 | 6 | [参考](MG-GR105/reference.md) · [合同](MG-GR105/contract.json) · [审核](MG-GR105/review.json) |
| [MG-GR106](MG-GR106/task.md) | 整族恢复、固定点与一致性的范围 | 6 | [参考](MG-GR106/reference.md) · [合同](MG-GR106/contract.json) · [审核](MG-GR106/review.json) |
| [MG-GF111](MG-GF111/task.md) | 扩展非负界、有限子域与统一常数 | 6 | [参考](MG-GF111/reference.md) · [合同](MG-GF111/contract.json) · [审核](MG-GF111/review.json) |
| [MG-GF112](MG-GF112/task.md) | 扩展非负最优界的取得与系统组合 | 6 | [参考](MG-GF112/reference.md) · [合同](MG-GF112/contract.json) · [审核](MG-GF112/review.json) |

### 第三章 · 代数、商结构与相容提升

| 题组 | 主题 | 阶段 | 参考与判准 |
|---|---|---:|---|
| [MG-GR006](MG-GR006/task.md) | 逆向塔的前缀、整体提升与选择 | 6 | [参考](MG-GR006/reference.md) · [合同](MG-GR006/contract.json) · [审核](MG-GR006/review.json) |
| [MG-GR007](MG-GR007/task.md) | 等变分裂空间的稳定与自然性 | 6 | [参考](MG-GR007/reference.md) · [合同](MG-GR007/contract.json) · [审核](MG-GR007/review.json) |
| [MG-GR008](MG-GR008/task.md) | 塔记录的表示、有限层延拓与自然变换 | 6 | [参考](MG-GR008/reference.md) · [合同](MG-GR008/contract.json) · [审核](MG-GR008/review.json) |
| [MG-GR014](MG-GR014/task.md) | 线性关系、坐标纤维与无限赋值 | 6 | [参考](MG-GR014/reference.md) · [合同](MG-GR014/contract.json) · [审核](MG-GR014/review.json) |
| [MG-GR015](MG-GR015/task.md) | 自由模的商记录、完成支持与提升 | 6 | [参考](MG-GR015/reference.md) · [合同](MG-GR015/contract.json) · [审核](MG-GR015/review.json) |
| [MG-GR016](MG-GR016/task.md) | 局部分裂、有限呈示与截面拼接 | 6 | [参考](MG-GR016/reference.md) · [合同](MG-GR016/contract.json) · [审核](MG-GR016/review.json) |
| [MG-GR020](MG-GR020/task.md) | 对称分解的归一化与算术边界 | 6 | [参考](MG-GR020/reference.md) · [合同](MG-GR020/contract.json) · [审核](MG-GR020/review.json) |
| [MG-GR101](MG-GR101/task.md) | 从同余记录到有限族的整体实现 | 6 | [参考](MG-GR101/reference.md) · [合同](MG-GR101/contract.json) · [审核](MG-GR101/review.json) |
| [MG-GR104](MG-GR104/task.md) | 幂等元提升、逆极限与环分解 | 6 | [参考](MG-GR104/reference.md) · [合同](MG-GR104/contract.json) · [审核](MG-GR104/review.json) |
| [MG-GF101](MG-GF101/task.md) | 商环塔、幂零性与分离条件 | 6 | [参考](MG-GF101/reference.md) · [合同](MG-GF101/contract.json) · [审核](MG-GF101/review.json) |
| [MG-GF102](MG-GF102/task.md) | 商环塔的稳定、比较与自然性 | 6 | [参考](MG-GF102/reference.md) · [合同](MG-GF102/contract.json) · [审核](MG-GF102/review.json) |

### 第四章 · 拓扑、下降与空间重构

| 题组 | 主题 | 阶段 | 参考与判准 |
|---|---|---:|---|
| [MG-GR009](MG-GR009/task.md) | 群作用下降、稳定子与基底检验 | 6 | [参考](MG-GR009/reference.md) · [合同](MG-GR009/contract.json) · [审核](MG-GR009/review.json) |
| [MG-GR010](MG-GR010/task.md) | 探针映射空间与连续性层级 | 6 | [参考](MG-GR010/reference.md) · [合同](MG-GR010/contract.json) · [审核](MG-GR010/review.json) |
| [MG-GR017](MG-GR017/task.md) | 连续提升的有限拼接与积 | 6 | [参考](MG-GR017/reference.md) · [合同](MG-GR017/contract.json) · [审核](MG-GR017/review.json) |
| [MG-GR018](MG-GR018/task.md) | 有限观察、自然运算与非点值记录 | 6 | [参考](MG-GR018/reference.md) · [合同](MG-GR018/contract.json) · [审核](MG-GR018/review.json) |
| [MG-GR019](MG-GR019/task.md) | 超滤子代数、有限观测商与连通纤维 | 6 | [参考](MG-GR019/reference.md) · [合同](MG-GR019/contract.json) · [审核](MG-GR019/review.json) |
| [MG-GF103](MG-GF103/task.md) | 初始拓扑的比较与测试空间 | 6 | [参考](MG-GF103/reference.md) · [合同](MG-GF103/contract.json) · [审核](MG-GF103/review.json) |
| [MG-GF104](MG-GF104/task.md) | 初始拓扑、子空间与分离性修复 | 6 | [参考](MG-GF104/reference.md) · [合同](MG-GF104/contract.json) · [审核](MG-GF104/review.json) |

### 第五章 · 有限集与定量覆盖

| 题组 | 主题 | 阶段 | 参考与判准 |
|---|---|---:|---|
| [MG-GF105](MG-GF105/task.md) | 陪集切片、最小覆盖与空切片 | 6 | [参考](MG-GF105/reference.md) · [合同](MG-GF105/contract.json) · [审核](MG-GF105/review.json) |
| [MG-GF106](MG-GF106/task.md) | 陪集覆盖、商群计数与子群改变 | 6 | [参考](MG-GF106/reference.md) · [合同](MG-GF106/contract.json) · [审核](MG-GF106/review.json) |

### 第六章 · Fourier 分析与正则性

| 题组 | 主题 | 阶段 | 参考与判准 |
|---|---|---:|---|
| [MG-GP002](MG-GP002/task.md) | Fourier 逆、截断误差与参数边界 | 6 | [参考](MG-GP002/reference.md) · [合同](MG-GP002/contract.json) · [审核](MG-GP002/review.json) |
| [MG-GF107](MG-GF107/task.md) | 加权逆算子、支撑界与量词交换 | 6 | [参考](MG-GF107/reference.md) · [合同](MG-GF107/contract.json) · [审核](MG-GF107/review.json) |
| [MG-GF108](MG-GF108/task.md) | 加权逆算子的正性边界与接口修复 | 6 | [参考](MG-GF108/reference.md) · [合同](MG-GF108/contract.json) · [审核](MG-GF108/review.json) |

### 第七章 · 几何拼接与层化比较

| 题组 | 主题 | 阶段 | 参考与判准 |
|---|---|---:|---|
| [MG-GP001](MG-GP001/task.md) | 局部单形、锥附着与整体同伦型 | 6 | [参考](MG-GP001/reference.md) · [合同](MG-GP001/contract.json) · [审核](MG-GP001/review.json) |
| [MG-GP003](MG-GP003/task.md) | 半局部邻域、下降与层化的依赖比较 | 6 | [参考](MG-GP003/reference.md) · [合同](MG-GP003/contract.json) · [审核](MG-GP003/review.json) |

## 取卷与审核

```sh
python3 -m math_gauge validate --suite drafts/progressive-groups-20261030
python3 -m math_gauge prepare --suite drafts/progressive-groups-20261030 --case MG-GR013 --out runs/group-r013
```

每组是一次完整请求、一个相关样本。candidate仅接收case.json明确指定的task及输入附件；本目录、index.json、contract、参考、来源和审核材料均不可附给候选。运行隔离和模型预算须在试跑前另行冻结，不能仅凭目录隔离宣称闭卷。

本版为 **draft / human pending**。每组有数学作者自查及独立复核记录；已完成的审核必须与实际文件散列一致。新增部分没有继承旧题作者Lean覆盖；6组生成/修复的新完整作者Lean实现尚未逐组内核核验。这里提供完整数学参考和考试/判卷合同，不声称所有扩展目标已形式化通过。未启动新模型请求，尚不能由设计推断实际区分度。

配套[整章Lean考试](../chapter-exams-20261030/README.md)分别覆盖OET卷1第2/3章34/92项义务。原41题的逐题失败复盘见[分析报告](../../results/failure-analysis-20261030/README.md)。
