# 按考察重点选卷

本目录覆盖当前43份试卷：41份递进题组含246阶段，另2份整章试卷各含34/92项义务。每份完整试卷是一个样本，阶段与义务不能当作独立试题。

分类是AI审查建议；源题全部仍为 **draft / human pending**。本目录不产生模型调用、数学裁定或新增判卷要求，也不证明作者或候选Lean覆盖。完整要求以唯一题面和合同为准。

每卷恰有1个主重点和2–4个次重点。主重点构成互斥阅读索引；多标签层可以重叠，卷数不能相加。按重点统计仍以完整试卷为分母，保留未运行、未决和环境失败。

中性自查、支持/怀疑立场和重复轮次属于执行维度，见[可靠性执行协议](../protocol/reliability-execution.md)。数学主题和任务类型是其他交叉索引。

本页仅供出题侧，不能附入候选输入；候选材料继续由共享runner按每题显式投影生成。

| 考察重点 | 主重点卷数 | 含该标签卷数 |
| --- | ---: | ---: |
| F01 假设及作用域 | 2 | 36 |
| F02 量词与常数一致性 | 4 | 19 |
| F03 定义域、局部整体与提升 | 7 | 25 |
| F04 结论强度与收敛 | 4 | 25 |
| F05 存在、取到与极限 | 2 | 12 |
| F06 构造、分类与自然性 | 8 | 22 |
| F07 证明链与依赖管理 | 2 | 15 |
| F08 Lean语义对齐 | 6 | 14 |
| F09 完整Lean工程交付 | 8 | 8 |

## F01 假设及作用域

核查结构假设的实际作用与局部生效范围；区分必要条件、充分条件与某条证明路线的要求。

不因题中存在假设就自动标记；需有明确的假设改变、删除或作用对象切换。

### 主重点 · 2卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GR001 · 递归系统的固定族、稳定分支与终止](proofs/MG-GR001/task.md) · [合同](proofs/MG-GR001/contract.json) | 0.1.2 · 7阶段 | **S2**：加入完备度量及有限直径后构造固定族；**S4**：回到共同的扩展伪度量结构，重新判定整体目标。 |
| [MG-GR020 · 对称分解的归一化与算术边界](proofs/MG-GR020/task.md) · [合同](proofs/MG-GR020/contract.json) | 0.1.1 · 6阶段 | **S2**：完备DVR构造阶段明确给2为单位；**S4**：原结构仅给特征零DVR，须重新核查分母和Hensel条件。 |

### 次重点 · 34卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-C002 · OET卷1第2章整章形式化](chapters/MG-C002/candidate/task.md) · [合同](chapters/MG-C002/contract.json) | 0.1.1 · 34义务 | **CH02-D02**：co-Lip证书自带非空受限域条件；**CH02-D04**：空乘积和正长度乘积范围不同；**CH02-P21**：规范非分离时结论只到族零距，不自动增加分离性。 |
| [MG-GF101 · 商环塔、幂零性与分离条件](lean-audit/MG-GF101/task.md) · [合同](lean-audit/MG-GF101/contract.json) | 0.1.1 · 6阶段 | **S2**：原有限层目标允许任意理想；**S6**：审计源码所给源幂零数据是否属于原条件。 |
| [MG-GF102 · 商环塔的稳定、比较与自然性](lean-construction/MG-GF102/task.md) · [合同](lean-construction/MG-GF102/contract.json) | 0.1.1 · 6阶段 | **S2**：删除S1平方零条件，通用定理须覆盖任意R和I。 |
| [MG-GF103 · 初始拓扑的比较与测试空间](lean-audit/MG-GF103/task.md) · [合同](lean-audit/MG-GF103/contract.json) | 0.1.1 · 6阶段 | **S1**：原构造保持任意指标、任意空间和空指标族范围。 |
| [MG-GF104 · 初始拓扑、子空间与分离性修复](lean-construction/MG-GF104/task.md) · [合同](lean-construction/MG-GF104/contract.json) | 0.1.1 · 6阶段 | **S2**：不能携带S1单射离散条件；**S5**：删除联合单射后重新判定T0。 |
| [MG-GF105 · 陪集切片、最小覆盖与空切片](lean-audit/MG-GF105/task.md) · [合同](lean-audit/MG-GF105/contract.json) | 0.1.1 · 6阶段 | **S2**：非空切片支持分母除法；**S5**：空切片阶段改成乘积界，不能直接复用商式界。 |
| [MG-GF107 · 加权逆算子、支撑界与量词交换](lean-audit/MG-GF107/task.md) · [合同](lean-audit/MG-GF107/contract.json) | 0.1.1 · 6阶段 | **S3**：零阶估计仅在共同支撑端点M的范围给出，常数须记录对M的依赖。 |
| [MG-GF108 · 加权逆算子的正性边界与接口修复](lean-construction/MG-GF108/task.md) · [合同](lean-construction/MG-GF108/contract.json) | 0.1.1 · 6阶段 | **S3**：把v≥1改为逐点v>0，核对每条证明的实际用法；**S4**：再允许零权重时重新检查逆问题。 |
| [MG-GF109 · 有限记录、安全核与迟延前进](lean-audit/MG-GF109/task.md) · [合同](lean-audit/MG-GF109/contract.json) | 0.1.1 · 6阶段 | **S2**：弱记录允许停留而不给最终前进；**S4**：迟延实现是额外条件，不能回填为原输入。 |
| [MG-GF110 · 有限记录的可靠内近似与完整修复](lean-construction/MG-GF110/task.md) · [合同](lean-construction/MG-GF110/contract.json) | 0.1.1 · 6阶段 | **S2**：E只在A中给出，迭代调用需检查局部适用范围；**S3**：返回W后删除E，重新判定精确恢复。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 0.1.1 · 6阶段 | **S1**：商同伦使用非空可缩子复形条件；**S5**：删除B后需重新处理空link和孤立顶点。 |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 0.1.1 · 6阶段 | **S5**：域任意且点不必在原X闭，不能增添无限、完美域或闭点条件。 |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 0.1.1 · 6阶段 | **S2**：全记录恢复阶段增加自反性；**S5**：单条记录改用明确的弱星连续条件，要求充要性。 |
| [MG-GR003 · 平均恢复、迭代误差与一致速度](proofs/MG-GR003/task.md) · [合同](proofs/MG-GR003/contract.json) | 0.1.1 · 6阶段 | **S1**：特殊阶段使用交换正交投影；**S3**：一般阶段只保留Banach、交换和分别幂有界。 |
| [MG-GR004 · Hilbert复形的精确消元与近似消元](proofs/MG-GR004/task.md) · [合同](proofs/MG-GR004/contract.json) | 0.1.1 · 5阶段 | **S1**：有限维消元阶段不能只由复形长度有限代替层空间有限维；**S3**：原阶段仅给约化无环，不给正谱下界或闭值域。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 0.1.1 · 6阶段 | **S2**：下半连续和次水平集紧性有独立职责；**S5**：保留闭凸而不给次水平紧性时，重新检查有限投影。 |
| [MG-GR006 · 逆向塔的前缀、整体提升与选择](proofs/MG-GR006/task.md) · [合同](proofs/MG-GR006/contract.json) | 0.1.1 · 6阶段 | **S4**：有限性落在C且β、γ满射；**S5**：另将有限性改到A，不要求过渡满射。 |
| [MG-GR007 · 等变分裂空间的稳定与自然性](proofs/MG-GR007/task.md) · [合同](proofs/MG-GR007/contract.json) | 0.1.1 · 6阶段 | **S4**：只要求实际方向空间Hom_G(C,A_n)有限维，而不要求A_n、B_n有限维。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 0.1.1 · 6阶段 | **S1**：余极限结构映射不预设单射；**S4**：秩一过渡允许零和负整数，分类须覆盖全部分支。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 0.1.1 · 6阶段 | **S1**：有限自由作用是特殊实现阶段的条件，后续一般层阶段不保留该假设。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 0.1.1 · 6阶段 | **S4**：第一可数与局部紧分别支持不同的求值和k化结论。 |
| [MG-GR011 · 凸投影的恢复、复合与变分方程](proofs/MG-GR011/task.md) · [合同](proofs/MG-GR011/contract.json) | 0.1.1 · 6阶段 | **S3**：有限线性投影复合明确要求交换；**S4**：一般阶段只有闭凸约束及统一有限可行界。 |
| [MG-GR012 · 凸势、对偶与有限记录逼近](proofs/MG-GR012/task.md) · [合同](proofs/MG-GR012/contract.json) | 0.1.1 · 6阶段 | **S4**：只给拓扑向量空间，不额外要求Hilbert、局部凸或Hausdorff。 |
| [MG-GR013 · 多项式记录、预解与谱的连续比较](proofs/MG-GR013/task.md) · [合同](proofs/MG-GR013/contract.json) | 0.1.1 · 6阶段 | **S4**：有限维像模型仍作用在同一个可能无限维的Banach空间上，含多项式常数项。 |
| [MG-GR014 · 线性关系、坐标纤维与无限赋值](proofs/MG-GR014/task.md) · [合同](proofs/MG-GR014/contract.json) | 0.1.1 · 6阶段 | **S4**：允许任意域和任意指标，不能保留S3有限域紧性作为隐藏条件；**S6**：无限离散域的坐标像闭性须给代数延拓或有限闭方程证明，不能把某条紧像证明的要求当作结论的必要条件。 |
| [MG-GR015 · 自由模的商记录、完成支持与提升](proofs/MG-GR015/task.md) · [合同](proofs/MG-GR015/contract.json) | 0.1.1 · 6阶段 | **S1**：初始完成正合阶段给定真实截面；**S3**：对角指数另有统一界；**S4**：原呈示仅保留可数自由，不能继承前述条件。 |
| [MG-GR016 · 局部分裂、有限呈示与截面拼接](proofs/MG-GR016/task.md) · [合同](proofs/MG-GR016/contract.json) | 0.1.1 · 6阶段 | **S2**：理想有限生成是本阶段明确条件；**S4**：原商仅循环，不能当作有限呈示；**S5**：另删去幂等理想的有限生成条件。 |
| [MG-GR017 · 连续提升的有限拼接与积](proofs/MG-GR017/task.md) · [合同](proofs/MG-GR017/contract.json) | 0.1.1 · 6阶段 | **S3**：βD回缩刻画要验证实际连续延拓与连续截面。 |
| [MG-GR019 · 超滤子代数、有限观测商与连通纤维](proofs/MG-GR019/task.md) · [合同](proofs/MG-GR019/contract.json) | 0.1.1 · 6阶段 | **S4**：不能在拓扑重建之前使用紧Hausdorff或输入运算连续性。 |
| [MG-GR101 · 从同余记录到有限族的整体实现](proofs/MG-GR101/task.md) · [合同](proofs/MG-GR101/contract.json) | 0.1.1 · 6阶段 | **S2**：H=L是三记录特殊阶段的显式条件；**S4**：一般障碍列阶段不保留H=L。 |
| [MG-GR102 · 有限轨道、规范投影与统一公式](proofs/MG-GR102/task.md) · [合同](proofs/MG-GR102/contract.json) | 0.1.1 · 6阶段 | **S5**：有限维轨道张成与轨道集合有限是不同条件。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 0.1.1 · 6阶段 | **S2**：精确传递使用左伴随；**S5**：改用保持底元和ω链上确界的另一机制，仍不要求右伴随。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 0.1.1 · 6阶段 | **S5**：各增广满射与过渡满射分别核验；**S6**：非交换平方零核阶段另查唯一性所需乘法结构。 |
| [MG-GR105 · 观测完成、噪声误差与原空间极小点](proofs/MG-GR105/task.md) · [合同](proofs/MG-GR105/contract.json) | 0.1.1 · 6阶段 | **S4**：原Hilbert范数完备与观测范数完备分别检查；**S6**：伴随与正则化公式只在此处明确的Hilbert结构下使用。 |

## F02 量词与常数一致性

保持量词顺序、统一或逐对象常数、同一个界、共同阶段及固定参数的依赖关系。

收敛方式本身归F04；有限/无限或常数更换涉及量词交换时使用本标签。

### 主重点 · 4卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 0.1.1 · 6阶段 | **S4**：全部允许损失的估计要求同一参数下常数独立于所有u；**S5**：邻近全部无理方向另要求共同s和C；**S6**：不可解构造要求同一个光滑F，而非每阶各一个坏频率。 |
| [MG-GR013 · 多项式记录、预解与谱的连续比较](proofs/MG-GR013/task.md) · [合同](proofs/MG-GR013/contract.json) | 0.1.1 · 6阶段 | **S4**：最终精确范数记录的阈值N_p可依赖每个固定多项式；**S6**：用两种迭代极限明确谱半径公式允许的量词顺序。 |
| [MG-GR102 · 有限轨道、规范投影与统一公式](proofs/MG-GR102/task.md) · [合同](proofs/MG-GR102/contract.json) | 0.1.1 · 6阶段 | **S3**：逐点有限轨道不给统一幂次；**S4**：另要求一个对全模有效的多项式公式。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 0.1.1 · 6阶段 | **S1**：单层只要求每个核元素各自幂零，不给统一指数；**S3**：比较逐层指数与极限元素的共同幂零指数。 |

### 次重点 · 15卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-C003 · OET卷1第3章整章形式化](chapters/MG-C003/candidate/task.md) · [合同](chapters/MG-C003/contract.json) | 0.1.1 · 92义务 | **CH03-P10-02**：逐基点计算合法半径及正点态半径；**CH03-P10-03**：在同一固定域上再取基点下确界；**CH03-P20-01**：对任意输入尺度在同一阶跃例中选择二点，保留量词顺序。 |
| [MG-GF101 · 商环塔、幂零性与分离条件](lean-audit/MG-GF101/task.md) · [合同](lean-audit/MG-GF101/contract.json) | 0.1.1 · 6阶段 | **S4**：统一N覆盖所有层；**S5**：分离条件下保持同一个N，不改成逐层存在指数。 |
| [MG-GF103 · 初始拓扑的比较与测试空间](lean-audit/MG-GF103/task.md) · [合同](lean-audit/MG-GF103/contract.json) | 0.1.1 · 6阶段 | **S4**：所有单点映射与任意测试空间的全称量词分开；**S5**：指定方向的一个恒等测试与S4的点测试不同。 |
| [MG-GF107 · 加权逆算子、支撑界与量词交换](lean-audit/MG-GF107/task.md) · [合同](lean-audit/MG-GF107/contract.json) | 0.1.1 · 6阶段 | **S2**：一阶控制保留完全同一个C；**S4**：全体序列统一D；**S5**：改成每条序列各自存在D。 |
| [MG-GF108 · 加权逆算子的正性边界与接口修复](lean-construction/MG-GF108/task.md) · [合同](lean-construction/MG-GF108/contract.json) | 0.1.1 · 6阶段 | **S1**：一阶估计须保留固定C；**S5**：C=0端点另查，不能推广为任意正常数估计。 |
| [MG-GF109 · 有限记录、安全核与迟延前进](lean-audit/MG-GF109/task.md) · [合同](lean-audit/MG-GF109/contract.json) | 0.1.1 · 6阶段 | **S4**：每个安全x的迟延可依赖x，不要求统一上界。 |
| [MG-GF111 · 扩展非负界、有限子域与统一常数](lean-audit/MG-GF111/task.md) · [合同](lean-audit/MG-GF111/contract.json) | 0.1.1 · 6阶段 | **S4**：各有限子域可有不同且无统一上界的c_F；**S5**：改给固定有限C，检查C本身的全域可行性。 |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 0.1.1 · 6阶段 | **S6**：逐同调类在某后阶段消失与统一尾部阶段正合的量词分开。 |
| [MG-GR001 · 递归系统的固定族、稳定分支与终止](proofs/MG-GR001/task.md) · [合同](proofs/MG-GR001/contract.json) | 0.1.2 · 7阶段 | **S7**：分别检查逐输入有限终止和统一终止深度能支持的误差范围。 |
| [MG-GR003 · 平均恢复、迭代误差与一致速度](proofs/MG-GR003/task.md) · [合同](proofs/MG-GR003/contract.json) | 0.1.1 · 6阶段 | **S5**：检查逐向量的逼近阶段能否统一到整个单位球。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 0.1.1 · 6阶段 | **S5**：区分每个当前层与存在足够后层的回缩要求；**S6**：检查无限积各坐标代表能否使用同一有限层。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 0.1.1 · 6阶段 | **S4**：只在单点上的稳定子检验与全部测试对象的检验分开。 |
| [MG-GR017 · 连续提升的有限拼接与积](proofs/MG-GR017/task.md) · [合同](proofs/MG-GR017/contract.json) | 0.1.1 · 6阶段 | **S5**：对给定有限像映射的可提升性与对所有映射的全提升性质分开。 |
| [MG-GR018 · 有限观察、自然运算与非点值记录](proofs/MG-GR018/task.md) · [合同](proofs/MG-GR018/contract.json) | 0.1.1 · 6阶段 | **S2**：自然性量化所有有限集合映射而非只量化置换；**S3**：只允许两值测试时重新判定点值结论。 |
| [MG-GR106 · 整族恢复、固定点与一致性的范围](proofs/MG-GR106/task.md) · [合同](proofs/MG-GR106/contract.json) | 0.1.1 · 6阶段 | **S4**：保留任意真滤子，不能未经理由替换为可枚举序列或共尾子族。 |

## F03 定义域、局部整体与提升

区分原对象、商、完成、实际像域及受限域；核查有限或局部数据提升到整体的条件。

仅出现子集或商记号不足以标记，需实际的值域或实现边界。

### 主重点 · 7卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 0.1.1 · 6阶段 | **S1**：记录先与E″双向等距识别，而不直接视为原E元素；**S4**：一般Banach阶段明确要求恢复值属于原E。 |
| [MG-GR006 · 逆向塔的前缀、整体提升与选择](proofs/MG-GR006/task.md) · [合同](proofs/MG-GR006/contract.json) | 0.1.1 · 6阶段 | **S1**：有限相容前缀和整体相容序列分开处理；**S4**：要求核验有限商记录下的整体提升。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 0.1.1 · 6阶段 | **S3**：建立一般层的完整下降判据和任意层基底相容性；**S5**：使用局部满射基底反映下降；**S6**：另检查仅非空可表示基底的检验范围。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 0.1.1 · 6阶段 | **S2**：探针识别的连续映射目标是kX、kY；**S5**：再检查探针同构能否提升为原拓扑同胚。 |
| [MG-GR015 · 自由模的商记录、完成支持与提升](proofs/MG-GR015/task.md) · [合同](proofs/MG-GR015/contract.json) | 0.1.1 · 6阶段 | **S2**：完成模型的支持条件逐商层有限，须与全积区分；**S5**：每层原模代表与一个原模整体代表分开。 |
| [MG-GR016 · 局部分裂、有限呈示与截面拼接](proofs/MG-GR016/task.md) · [合同](proofs/MG-GR016/contract.json) | 0.1.1 · 6阶段 | **S4**：每个素点处分裂与整体截面的构造须核验；**S6**：另给有限主开覆盖上已相容的实际截面，要求唯一拼接。 |
| [MG-GR017 · 连续提升的有限拼接与积](proofs/MG-GR017/task.md) · [合同](proofs/MG-GR017/contract.json) | 0.1.1 · 6阶段 | **S2**：有限离散因子的乘积通过有限开闭拼接处理；**S4**：改为两个任意具有全提升性质的profinite因子。 |

### 次重点 · 18卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-C002 · OET卷1第2章整章形式化](chapters/MG-C002/candidate/task.md) · [合同](chapters/MG-C002/contract.json) | 0.1.1 · 34义务 | **CH02-D05**：表示实际中间像域，而非任意选一个下游域；**CH02-P04**：两步Lip复合须使用精确中间像域；**CH02-P08**：co-Lip复合还须保留非空性。 |
| [MG-C003 · OET卷1第3章整章形式化](chapters/MG-C003/candidate/task.md) · [合同](chapters/MG-C003/contract.json) | 0.1.1 · 92义务 | **CH03-D05**：统一半径在A上取inf但在U评估；**CH03-P15-02**：复合下界使用下游实际像域上的半径；**CH03-P17-03**：同时缩小评估域和取inf基点集须分别追踪。 |
| [MG-GF104 · 初始拓扑、子空间与分离性修复](lean-construction/MG-GF104/task.md) · [合同](lean-construction/MG-GF104/contract.json) | 0.1.1 · 6阶段 | **S3**：任意E的子空间拓扑须与受限观测的初始拓扑相等。 |
| [MG-GF111 · 扩展非负界、有限子域与统一常数](lean-audit/MG-GF111/task.md) · [合同](lean-audit/MG-GF111/contract.json) | 0.1.1 · 6阶段 | **S1**：仅正有限分母域可直接使用通常除法等价；**S3**：回到含零和无穷分母的完整域，需额外边界分支。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 0.1.1 · 6阶段 | **S4**：判据须仅使用含v单形及其面关联的局部数据，并连接整体同伦型。 |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 0.1.1 · 6阶段 | **S3**：包含指定点的邻域系需证明实际余终；**S4**：稠密开与保留全部半局部点不能混同。 |
| [MG-GR001 · 递归系统的固定族、稳定分支与终止](proofs/MG-GR001/task.md) · [合同](proofs/MG-GR001/contract.json) | 0.1.2 · 7阶段 | **S6**：把唯一性限定在给定有限残差的有限距离分支，并检查能否跨分支。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 0.1.1 · 6阶段 | **S3**：全记录实现须在同一个统一成本界的紧集内处理有限交。 |
| [MG-GR007 · 等变分裂空间的稳定与自然性](proofs/MG-GR007/task.md) · [合同](proofs/MG-GR007/contract.json) | 0.1.1 · 6阶段 | **S5**：指定多项式塔须分别核验有限前缀和整体相容分裂。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 0.1.1 · 6阶段 | **S5**：从实际稳定像构造延拓，并核验F_P与Hom(I_n0,-)的实际记录对应。 |
| [MG-GR011 · 凸投影的恢复、复合与变分方程](proofs/MG-GR011/task.md) · [合同](proofs/MG-GR011/contract.json) | 0.1.1 · 6阶段 | **S4**：任意指标族通过全有限子集网恢复整体交，不能未经共尾证明换成序列。 |
| [MG-GR014 · 线性关系、坐标纤维与无限赋值](proofs/MG-GR014/task.md) · [合同](proofs/MG-GR014/contract.json) | 0.1.1 · 6阶段 | **S5**：把全赋值空间改为有限支持赋值空间后，重新检查整体可解性。 |
| [MG-GR018 · 有限观察、自然运算与非点值记录](proofs/MG-GR018/task.md) · [合同](proofs/MG-GR018/contract.json) | 0.1.1 · 6阶段 | **S4**：刻画哪些底集的全部记录来自原点值，并处理有限、空及无限范围。 |
| [MG-GR019 · 超滤子代数、有限观测商与连通纤维](proofs/MG-GR019/task.md) · [合同](proofs/MG-GR019/contract.json) | 0.1.1 · 6阶段 | **S1**：有限观察商及其纤维须在实际紧Hausdorff空间上构造。 |
| [MG-GR101 · 从同余记录到有限族的整体实现](proofs/MG-GR101/task.md) · [合同](proofs/MG-GR101/contract.json) | 0.1.1 · 6阶段 | **S5**：全部三元子族可实现与四份记录共同实现分开检查。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 0.1.1 · 6阶段 | **S2**：幂等族相容提升与任意元素的整体提升不等同；**S5**：重新判定极限增广的全部元素满射性。 |
| [MG-GR105 · 观测完成、噪声误差与原空间极小点](proofs/MG-GR105/task.md) · [合同](proofs/MG-GR105/contract.json) | 0.1.1 · 6阶段 | **S3**：完备化等距映射的像确定为观测像闭包，不能直接拉回原E。 |
| [MG-GR106 · 整族恢复、固定点与一致性的范围](proofs/MG-GR106/task.md) · [合同](proofs/MG-GR106/contract.json) | 0.1.1 · 6阶段 | **S4**：从稠密观测构造实际完备化上的唯一Lipschitz恢复及各延拓。 |

## F04 结论强度与收敛

区分包含与相等、单向与等价、必要与充分、逐点/强收敛与一致/范数收敛，以及能否逆推。

存在性或极值取得的专门障碍归F05；同一要求可交叉标记但不重复充数。

### 主重点 · 4卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GR003 · 平均恢复、迭代误差与一致速度](proofs/MG-GR003/task.md) · [合同](proofs/MG-GR003/contract.json) | 0.1.1 · 6阶段 | **S3**：比较双平均与实际R迭代的范数收敛域及共同极限；**S5**：分别判定逐向量范数收敛和算子范数收敛。 |
| [MG-GR004 · Hilbert复形的精确消元与近似消元](proofs/MG-GR004/task.md) · [合同](proofs/MG-GR004/contract.json) | 0.1.1 · 5阶段 | **S4**：证明正则化的逐向量极限，并另判定算子范数极限。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 0.1.1 · 6阶段 | **S3**：分别给两个单边更新关系的有向比较；**S4**：精确半共轭的固定点像与最小固定点等式分开。 |
| [MG-GR106 · 整族恢复、固定点与一致性的范围](proofs/MG-GR106/task.md) · [合同](proofs/MG-GR106/contract.json) | 0.1.1 · 6阶段 | **S4**：完成域上要求各紧集一致及同步移动输入极限；**S5**：另判定全完成域一致；**S6**：检查全有界但不闭子集上的结论。 |

### 次重点 · 21卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-C003 · OET卷1第3章整章形式化](chapters/MG-C003/candidate/task.md) · [合同](chapters/MG-C003/contract.json) | 0.1.1 · 92义务 | **CH03-P08-03**：商值判据回到点值判据需核验两实际像集分离；**CH03-P23-03**：熵差为零仅在差值良定的范围使用；**CH03-P29-05**：删除直径条件后对整体零化的加强另作反例义务。 |
| [MG-GF103 · 初始拓扑的比较与测试空间](lean-audit/MG-GF103/task.md) · [合同](lean-audit/MG-GF103/contract.json) | 0.1.1 · 6阶段 | **S2**：核对拓扑粗细与连续恒等映射方向；**S3**：初始拓扑相等与目标拓扑相等分开判定。 |
| [MG-GF105 · 陪集切片、最小覆盖与空切片](lean-audit/MG-GF105/task.md) · [合同](lean-audit/MG-GF105/contract.json) | 0.1.1 · 6阶段 | **S4**：将F⊆A加强为F⊆B须另判；**S3**：定量上界与最小覆盖数的精确等式分开。 |
| [MG-GF106 · 陪集覆盖、商群计数与子群改变](lean-construction/MG-GF106/task.md) · [合同](lean-construction/MG-GF106/contract.json) | 0.1.1 · 6阶段 | **S4**：对所有切片估计后是否能去掉密度因子须完整判定。 |
| [MG-GF107 · 加权逆算子、支撑界与量词交换](lean-audit/MG-GF107/task.md) · [合同](lean-audit/MG-GF107/contract.json) | 0.1.1 · 6阶段 | **S6**：r+1到r目标与r+2输入接口的强度差异须给具体见证。 |
| [MG-GF109 · 有限记录、安全核与迟延前进](lean-audit/MG-GF109/task.md) · [合同](lean-audit/MG-GF109/contract.json) | 0.1.1 · 6阶段 | **S3**：可靠内近似、精确安全核相等和真实最大性分别证明；**S5**：相等能否反推精确记录另判。 |
| [MG-GF110 · 有限记录的可靠内近似与完整修复](lean-construction/MG-GF110/task.md) · [合同](lean-construction/MG-GF110/contract.json) | 0.1.1 · 6阶段 | **S4**：可靠包含与终层最大性、真实K最大性不能混同。 |
| [MG-GF112 · 扩展非负最优界的取得与系统组合](lean-construction/MG-GF112/task.md) · [合同](lean-construction/MG-GF112/contract.json) | 0.1.1 · 6阶段 | **S5**：并系统最小值反推各支最小值是对S4的独立逆向判定。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 0.1.1 · 6阶段 | **S3**：有理同调和整数扭结信息分开；**S6**：悬挂等价能否逆向消去需另给完整论证。 |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 0.1.1 · 6阶段 | **S2**：有限频带形式逆须升级为真正光滑解及截断误差；**S4**：给定C^(m+4)到C^m结论不能由更弱输入范数要求代替。 |
| [MG-GR001 · 递归系统的固定族、稳定分支与终止](proofs/MG-GR001/task.md) · [合同](proofs/MG-GR001/contract.json) | 0.1.2 · 7阶段 | **S5**：同时计算指定展开的点态行为和全输入sup误差。 |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 0.1.1 · 6阶段 | **S4**：一般目标是最大下半连续凸下界；**S6**：区分恢复原f、投影闭化和能否省略外层闭化。 |
| [MG-GR006 · 逆向塔的前缀、整体提升与选择](proofs/MG-GR006/task.md) · [合同](proofs/MG-GR006/contract.json) | 0.1.1 · 6阶段 | **S6**：用实际障碍说明S2和S5的充分条件不能倒写为必要条件。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 0.1.1 · 6阶段 | **S5**：区分探针自然同构与原拓扑同胚的结论层级。 |
| [MG-GR011 · 凸投影的恢复、复合与变分方程](proofs/MG-GR011/task.md) · [合同](proofs/MG-GR011/contract.json) | 0.1.1 · 6阶段 | **S4**：要求范数收敛、准确最优值和非扩张估计；**S5**：进一步单独判定恢复映射的仿射性质。 |
| [MG-GR012 · 凸势、对偶与有限记录逼近](proofs/MG-GR012/task.md) · [合同](proofs/MG-GR012/contract.json) | 0.1.1 · 6阶段 | **S5**：另判定输入记录包含能否升级为次梯度图相等；**S6**：有限记录极限还要求在附加条件下紧上一致。 |
| [MG-GR013 · 多项式记录、预解与谱的连续比较](proofs/MG-GR013/task.md) · [合同](proofs/MG-GR013/contract.json) | 0.1.1 · 6阶段 | **S1**：共同有限维空间中比较强收敛和算子范数收敛；**S3**：一般Banach阶段仅给强收敛及固定多项式作用。 |
| [MG-GR018 · 有限观察、自然运算与非点值记录](proofs/MG-GR018/task.md) · [合同](proofs/MG-GR018/contract.json) | 0.1.1 · 6阶段 | **S6**：将单位分裂与乘法的单射性分开判定。 |
| [MG-GR019 · 超滤子代数、有限观测商与连通纤维](proofs/MG-GR019/task.md) · [合同](proofs/MG-GR019/contract.json) | 0.1.1 · 6阶段 | **S6**：把连通纤维的充分结论另作逆向判定。 |
| [MG-GR020 · 对称分解的归一化与算术边界](proofs/MG-GR020/task.md) · [合同](proofs/MG-GR020/contract.json) | 0.1.1 · 6阶段 | **S6**：不可行论证须排除全部正交交织矩阵，不能只否定一个归一化公式。 |
| [MG-GR105 · 观测完成、噪声误差与原空间极小点](proofs/MG-GR105/task.md) · [合同](proofs/MG-GR105/contract.json) | 0.1.1 · 6阶段 | **S5**：投影逐点收敛与算子范数收敛分别证明并给精确判据。 |

## F05 存在、取到与极限

区分可行解、极值、下确界/上确界、端点取得及合法极限对象和交换。

不因证明中出现一个极限就标记；需存在、取得或极限合法性本身属于任务重点。

### 主重点 · 2卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GR005 · 凸成本记录、紧性与闭上图恢复](proofs/MG-GR005/task.md) · [合同](proofs/MG-GR005/contract.json) | 0.1.1 · 6阶段 | **S1**：纤维公式明确要求说明是否使用下确界取到；**S2**：在紧次水平集条件下处理真实最优点。 |
| [MG-GR105 · 观测完成、噪声误差与原空间极小点](proofs/MG-GR105/task.md) · [合同](proofs/MG-GR105/contract.json) | 0.1.1 · 6阶段 | **S3**：完成态最优值与原空间极小点存在的充要条件分别证明；**S6**：正则化的原向量范数极限与原最优点取到作双向比较。 |

### 次重点 · 10卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GF111 · 扩展非负界、有限子域与统一常数](lean-audit/MG-GF111/task.md) · [合同](lean-audit/MG-GF111/contract.json) | 0.1.1 · 6阶段 | **S3**：分别分类有限系数存在、有限最小值存在及其值。 |
| [MG-GF112 · 扩展非负最优界的取得与系统组合](lean-construction/MG-GF112/task.md) · [合同](lean-construction/MG-GF112/contract.json) | 0.1.1 · 6阶段 | **S1**：最优系数与某点实际达到比值上确界分开；**S3**：可行有限系数存在与最小值取得另算。 |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 0.1.1 · 6阶段 | **S4**：最小允许损失和端点是否取到须分别证明。 |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 0.1.1 · 6阶段 | **S6**：证明C+ε的有限观测精确匹配，并另判定ε=0是否可取。 |
| [MG-GR004 · Hilbert复形的精确消元与近似消元](proofs/MG-GR004/task.md) · [合同](proofs/MG-GR004/contract.json) | 0.1.1 · 5阶段 | **S5**：同时比较有界收缩、有界右逆、闭值域及正则化范数极限的存在。 |
| [MG-GR007 · 等变分裂空间的稳定与自然性](proofs/MG-GR007/task.md) · [合同](proofs/MG-GR007/contract.json) | 0.1.1 · 6阶段 | **S3**：稳定后参数空间的评价同构还要给出相容分裂唯一的充要条件。 |
| [MG-GR012 · 凸势、对偶与有限记录逼近](proofs/MG-GR012/task.md) · [合同](proofs/MG-GR012/contract.json) | 0.1.1 · 6阶段 | **S3**：半正定阶段须描述共轭函数有限值域及全部最优点，而不沿用唯一取到。 |
| [MG-GR013 · 多项式记录、预解与谱的连续比较](proofs/MG-GR013/task.md) · [合同](proofs/MG-GR013/contract.json) | 0.1.1 · 6阶段 | **S6**：两个内层极限均需实际证明，不能未经论证交换模型极限与幂次极限。 |
| [MG-GR020 · 对称分解的归一化与算术边界](proofs/MG-GR020/task.md) · [合同](proofs/MG-GR020/contract.json) | 0.1.1 · 6阶段 | **S5**：更深同余条件下需验证带分母级数的实际收敛和全部矩阵条件。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 0.1.1 · 6阶段 | **S6**：可数迭代上确界成为最小固定点须给出必要充分条件。 |

## F06 构造、分类与自然性

完成实际对象的双向构造、全部解/态射/自由度分类，区分自然运输与自然首选。

不以只给一个实例替代全分类；并不规定必须复刻作者路线。

### 主重点 · 8卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 0.1.1 · 6阶段 | **S4**：要求全部可能同伦类型、全部类型的实际实现以及有限充要判据。 |
| [MG-GR007 · 等变分裂空间的稳定与自然性](proofs/MG-GR007/task.md) · [合同](proofs/MG-GR007/contract.json) | 0.1.1 · 6阶段 | **S2**：分类全部相容分裂、直和同构和整塔同构运输；**S6**：整理存在、唯一、自然运输及自然首选四者关系。 |
| [MG-GR008 · 塔记录的表示、有限层延拓与自然变换](proofs/MG-GR008/task.md) · [合同](proofs/MG-GR008/contract.json) | 0.1.1 · 6阶段 | **S2**：分类全部群值自然变换及复合；**S3**：给出非循环表示性判据并构造全部表示对象。 |
| [MG-GR012 · 凸势、对偶与有限记录逼近](proofs/MG-GR012/task.md) · [合同](proofs/MG-GR012/contract.json) | 0.1.1 · 6阶段 | **S4**：构造规范化的逐点最小下半连续凸势，并证明完整最小性和唯一性。 |
| [MG-GR014 · 线性关系、坐标纤维与无限赋值](proofs/MG-GR014/task.md) · [合同](proofs/MG-GR014/contract.json) | 0.1.1 · 6阶段 | **S4**：从给定行和常数构造整体解，并完整分类所有坐标像和非空纤维。 |
| [MG-GR018 · 有限观察、自然运算与非点值记录](proofs/MG-GR018/task.md) · [合同](proofs/MG-GR018/contract.json) | 0.1.1 · 6阶段 | **S4**：完整分类相容记录，构造实际函子、单位、乘法并证明全部单子律。 |
| [MG-GR019 · 超滤子代数、有限观测商与连通纤维](proofs/MG-GR019/task.md) · [合同](proofs/MG-GR019/contract.json) | 0.1.1 · 6阶段 | **S4**：从两条代数律重建实际拓扑、双向对象对应、全部态射和有限观察商。 |
| [MG-GR101 · 从同余记录到有限族的整体实现](proofs/MG-GR101/task.md) · [合同](proofs/MG-GR101/contract.json) | 0.1.1 · 6阶段 | **S4**：构造代表无关的线性障碍、完整正合列及全部实现；**S6**：构造逐项障碍并说明排序改变后的最终和中间数据。 |

### 次重点 · 14卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GF102 · 商环塔的稳定、比较与自然性](lean-construction/MG-GF102/task.md) · [合同](lean-construction/MG-GF102/contract.json) | 0.1.1 · 6阶段 | **S3**：指定q_n的单射性不能换成抽象环同构；**S5**：构造指定同态的全部层自然性而非预设同构。 |
| [MG-GF105 · 陪集切片、最小覆盖与空切片](lean-audit/MG-GF105/task.md) · [合同](lean-audit/MG-GF105/contract.json) | 0.1.1 · 6阶段 | **S3**：构造精确最小覆盖数并证明上下两个方向。 |
| [MG-GF106 · 陪集覆盖、商群计数与子群改变](lean-construction/MG-GF106/task.md) · [合同](lean-construction/MG-GF106/contract.json) | 0.1.1 · 6阶段 | **S3**：用指定商映射的像描述覆盖与精确最小覆盖数。 |
| [MG-GF112 · 扩展非负最优界的取得与系统组合](lean-construction/MG-GF112/task.md) · [合同](lean-construction/MG-GF112/contract.json) | 0.1.1 · 6阶段 | **S4**：定义两个分支的不交并并证明Bound拆分及全部最小性。 |
| [MG-GP002 · Fourier 逆、截断误差与参数边界](proofs/MG-GP002/task.md) · [合同](proofs/MG-GP002/contract.json) | 0.1.1 · 6阶段 | **S4**：完整分类可逆方向和全部非负Sobolev损失。 |
| [MG-GR002 · 线性记录、有限观测与原空间恢复](proofs/MG-GR002/task.md) · [合同](proofs/MG-GR002/contract.json) | 0.1.1 · 6阶段 | **S1**：给出记录载体与T″作用的双向构造；**S3**：由记录完整描述闭子空间成员及距离的对偶公式。 |
| [MG-GR006 · 逆向塔的前缀、整体提升与选择](proofs/MG-GR006/task.md) · [合同](proofs/MG-GR006/contract.json) | 0.1.1 · 6阶段 | **S3**：区分自然提升空间与对全部整塔同构自然的首选提升；**S6**：构造选择无关且自然的完整障碍及全部提升。 |
| [MG-GR009 · 群作用下降、稳定子与基底检验](proofs/MG-GR009/task.md) · [合同](proofs/MG-GR009/contract.json) | 0.1.1 · 6阶段 | **S2**：分类对象、全部态射和自同构群；**S3**：不预选D而分类所有实现。 |
| [MG-GR010 · 探针映射空间与连续性层级](proofs/MG-GR010/task.md) · [合同](proofs/MG-GR010/contract.json) | 0.1.1 · 6阶段 | **S3**：构造全部参数化映射记录的Hausdorff实现和指数律；**S6**：构造同时变化的连续复合并验证单位与结合。 |
| [MG-GR015 · 自由模的商记录、完成支持与提升](proofs/MG-GR015/task.md) · [合同](proofs/MG-GR015/contract.json) | 0.1.1 · 6阶段 | **S2**：显式给出商记录与完成序列族的双向构造及模运算；**S3**：在合法支持条件下写出全部提升。 |
| [MG-GR016 · 局部分裂、有限呈示与截面拼接](proofs/MG-GR016/task.md) · [合同](proofs/MG-GR016/contract.json) | 0.1.1 · 6阶段 | **S3**：用Hom_R(C,A)描述全部截面及与原包含、投影相容的全部直和同构。 |
| [MG-GR017 · 连续提升的有限拼接与积](proofs/MG-GR017/task.md) · [合同](proofs/MG-GR017/contract.json) | 0.1.1 · 6阶段 | **S6**：双向分类全部连续提升；有限纤维时用允许空块的开闭划分描述。 |
| [MG-GR020 · 对称分解的归一化与算术边界](proofs/MG-GR020/task.md) · [合同](proofs/MG-GR020/contract.json) | 0.1.1 · 6阶段 | **S3**：实际已有解后分类全部相容比较；**S6**：对全部c参数给出存在与不存在的完整分类。 |
| [MG-GR102 · 有限轨道、规范投影与统一公式](proofs/MG-GR102/task.md) · [合同](proofs/MG-GR102/contract.json) | 0.1.1 · 6阶段 | **S3**：构造规范投影、完整直和与核像，并证明任意交织映射自然性。 |

## F07 证明链与依赖管理

在条件变化后核对前序结论的合法复用、共享构造的一致性及长证明链中真实依赖。

不指参数连续依赖；不因contract有depends_on就标记；参考图不强制唯一证明路线。

### 主重点 · 2卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GP003 · 半局部邻域、下降与层化的依赖比较](proofs/MG-GP003/task.md) · [合同](proofs/MG-GP003/contract.json) | 0.1.1 · 6阶段 | **S2**：图追依赖保覆盖收缩的正合输入和交上单射；**S5**：几何定理的实际条件、保点收缩与层化比较须逐项核对，可用合法直接定理路线。 |
| [MG-GR011 · 凸投影的恢复、复合与变分方程](proofs/MG-GR011/task.md) · [合同](proofs/MG-GR011/contract.json) | 0.1.1 · 6阶段 | **S5**：S1的仿射投影性质不能只因S4恢复唯一稳定就直接复用；**S6**：后续变分迭代须基于S4实际闭凸交及非扩张性，而不能借用线性。 |

### 次重点 · 13卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-C002 · OET卷1第2章整章形式化](chapters/MG-C002/candidate/task.md) · [合同](chapters/MG-C002/contract.json) | 0.1.1 · 34义务 | **CH02-P09**：从逐步证书通过合法的有限链构造复合证书；**CH02-P10**：co-Lip链的实际域递推与连乘次序要一致；**CH02-P13**：零值路径判据与正值判据的依赖须对应真实有限路径表示。 |
| [MG-GF106 · 陪集覆盖、商群计数与子群改变](lean-construction/MG-GF106/task.md) · [合同](lean-construction/MG-GF106/contract.json) | 0.1.1 · 6阶段 | **S5**：放大子群后需从给定F_H重新选代表，不能直接继承更强基数界。 |
| [MG-GF109 · 有限记录、安全核与迟延前进](lean-audit/MG-GF109/task.md) · [合同](lean-audit/MG-GF109/contract.json) | 0.1.1 · 6阶段 | **S1**：每次使用局部精确条件前要保证当前轨道仍在A；**S4**：迟延迭代后仍安全须先证，才可复用记录归纳。 |
| [MG-GP001 · 局部单形、锥附着与整体同伦型](proofs/MG-GP001/task.md) · [合同](proofs/MG-GP001/contract.json) | 0.1.1 · 6阶段 | **S4**：使用S1/S2的商和拼接结论前，须验证闭子复形、cofibration或实际替代条件。 |
| [MG-GR001 · 递归系统的固定族、稳定分支与终止](proofs/MG-GR001/task.md) · [合同](proofs/MG-GR001/contract.json) | 0.1.2 · 7阶段 | **S3**：稳定估计只在同图、同输入分割与同b的系统之间复用展开比较；**S6**：重新证明分支完备和不变，才可复用压缩固定点论证。 |
| [MG-GR012 · 凸势、对偶与有限记录逼近](proofs/MG-GR012/task.md) · [合同](proofs/MG-GR012/contract.json) | 0.1.1 · 6阶段 | **S6**：有限子记录必须保留同一基点，且紧上一致证明须核对有限势连续性。 |
| [MG-GR015 · 自由模的商记录、完成支持与提升](proofs/MG-GR015/task.md) · [合同](proofs/MG-GR015/contract.json) | 0.1.1 · 6阶段 | **S6**：再次完成须证明实际t^n商和典范映射身份，不能由对象名直接复用。 |
| [MG-GR019 · 超滤子代数、有限观测商与连通纤维](proofs/MG-GR019/task.md) · [合同](proofs/MG-GR019/contract.json) | 0.1.1 · 6阶段 | **S5**：代数乘积须验证真实推前与乘法律，再用S4拓扑唯一性识别乘积。 |
| [MG-GR101 · 从同余记录到有限族的整体实现](proofs/MG-GR101/task.md) · [合同](proofs/MG-GR101/contract.json) | 0.1.1 · 6阶段 | **S6**：每一步障碍只在前缀已有实现时定义，需核验选择无关及合法复用。 |
| [MG-GR102 · 有限轨道、规范投影与统一公式](proofs/MG-GR102/task.md) · [合同](proofs/MG-GR102/contract.json) | 0.1.1 · 6阶段 | **S6**：联合分解须利用真正的自然性证明投影交换，不能假设S4的统一多项式存在。 |
| [MG-GR103 · 参数最小不动点、消元与近似传递](proofs/MG-GR103/task.md) · [合同](proofs/MG-GR103/contract.json) | 0.1.1 · 6阶段 | **S1**：各中间参数最小解及约化系统须先良定义且单调；**S2**：传递结论须与所有分块结果及同一参数恢复一致。 |
| [MG-GR104 · 幂等元提升、逆极限与环分解](proofs/MG-GR104/task.md) · [合同](proofs/MG-GR104/contract.json) | 0.1.1 · 6阶段 | **S2**：由单层提升唯一性建立相容族，并逐项验证正交、求和及分解。 |
| [MG-GR106 · 整族恢复、固定点与一致性的范围](proofs/MG-GR106/task.md) · [合同](proofs/MG-GR106/contract.json) | 0.1.1 · 6阶段 | **S3**：同步复合需分别恢复并控制变化输入；**S4**：移动输入不能只引用紧集一致而不证明公共紧集存在。 |

## F08 Lean语义对齐

核对自然语言与Lean实际编码的对象、条件、量词、定义域、结论和覆盖；区分编译与语义完成。

书面审计不自动附加候选Lean源码义务；不以旧编译覆盖新阶段。

### 主重点 · 6卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-GF101 · 商环塔、幂零性与分离条件](lean-audit/MG-GF101/task.md) · [合同](lean-audit/MG-GF101/contract.json) | 0.1.1 · 6阶段 | **S6**：逐项展开SourceData与Candidate，核对原S2覆盖、次数及真实假设。 |
| [MG-GF103 · 初始拓扑的比较与测试空间](lean-audit/MG-GF103/task.md) · [合同](lean-audit/MG-GF103/contract.json) | 0.1.1 · 6阶段 | **S6**：核对源码四项声明、Lean拓扑序方向及完整映入范围。 |
| [MG-GF105 · 陪集切片、最小覆盖与空切片](lean-audit/MG-GF105/task.md) · [合同](lean-audit/MG-GF105/contract.json) | 0.1.1 · 6阶段 | **S6**：逐步核对切片、差集、覆盖和除法接口的语义。 |
| [MG-GF107 · 加权逆算子、支撑界与量词交换](lean-audit/MG-GF107/task.md) · [合同](lean-audit/MG-GF107/contract.json) | 0.1.1 · 6阶段 | **S6**：完整展开InputControl与Result，分别审计原逆和一阶固定常数估计。 |
| [MG-GF109 · 有限记录、安全核与迟延前进](lean-audit/MG-GF109/task.md) · [合同](lean-audit/MG-GF109/contract.json) | 0.1.1 · 6阶段 | **S6**：展开Realizes和真实定理参数，逐层核对有限层、安全两方向及最大性。 |
| [MG-GF111 · 扩展非负界、有限子域与统一常数](lean-audit/MG-GF111/task.md) · [合同](lean-audit/MG-GF111/contract.json) | 0.1.1 · 6阶段 | **S6**：审计正有限分母子类型、全部系数分类、有限/最小分类及边界例。 |

### 次重点 · 8卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-C002 · OET卷1第2章整章形式化](chapters/MG-C002/candidate/task.md) · [合同](chapters/MG-C002/contract.json) | 0.1.1 · 34义务 | **CH02-D01**：定义与证书表示须证明同原文等价，不能只提供更弱可编译声明；**CH02-D03**：Lean矩阵条目须对应原文输出行、输入列约定。 |
| [MG-C003 · OET卷1第3章整章形式化](chapters/MG-C003/candidate/task.md) · [合同](chapters/MG-C003/contract.json) | 0.1.1 · 92义务 | **CH03-D03**：Lean表示须区分点相等、全族零距、实际像和商关系；**CH03-D07**：允许直接复用冻结内部覆盖定义，仍须给真实声明映射及原文对应。 |
| [MG-GF102 · 商环塔的稳定、比较与自然性](lean-construction/MG-GF102/task.md) · [合同](lean-construction/MG-GF102/contract.json) | 0.1.1 · 6阶段 | **S6**：完整实现须保留各阶段自己的数学范围及全部原相容性目标。 |
| [MG-GF104 · 初始拓扑、子空间与分离性修复](lean-construction/MG-GF104/task.md) · [合同](lean-construction/MG-GF104/contract.json) | 0.1.1 · 6阶段 | **S6**：须说明原assembled的一般行为、实际修改和每个声明对应。 |
| [MG-GF106 · 陪集覆盖、商群计数与子群改变](lean-construction/MG-GF106/task.md) · [合同](lean-construction/MG-GF106/contract.json) | 0.1.1 · 6阶段 | **S6**：允许等价表示，但须证明其与原覆盖和基数条件的对应。 |
| [MG-GF108 · 加权逆算子的正性边界与接口修复](lean-construction/MG-GF108/task.md) · [合同](lean-construction/MG-GF108/contract.json) | 0.1.1 · 6阶段 | **S6**：修复后的原主接口只接受一阶Control，不能改名后保留r+2。 |
| [MG-GF110 · 有限记录的可靠内近似与完整修复](lean-construction/MG-GF110/task.md) · [合同](lean-construction/MG-GF110/contract.json) | 0.1.1 · 6阶段 | **S6**：不能将W重命名为E，或只编译未变化的有限层来声称完整修复。 |
| [MG-GF112 · 扩展非负最优界的取得与系统组合](lean-construction/MG-GF112/task.md) · [合同](lean-construction/MG-GF112/contract.json) | 0.1.1 · 6阶段 | **S6**：保留原ENNReal运算及三种分类，不能仅交声明类型。 |

## F09 完整Lean工程交付

交付完整且可共同编译的源码、实际声明对应和依赖闭包，并满足逐项语义、公理及冻结背景合同。

一个阶段或背景编译不能替代完整交付；源代码交付是本主题的必要任务事实。

### 主重点 · 8卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |
| [MG-C002 · OET卷1第2章整章形式化](chapters/MG-C002/candidate/task.md) · [合同](chapters/MG-C002/contract.json) | 0.1.1 · 34义务 | **CH02-D01**：整章task要求所有34项定义、表示及证明在一个完整项目中统一编译，并交Main.lean和逐ID清单。 |
| [MG-C003 · OET卷1第3章整章形式化](chapters/MG-C003/candidate/task.md) · [合同](chapters/MG-C003/contract.json) | 0.1.1 · 92义务 | **CH03-D01**：整章task要求所有92项定义、表示及证明共同编译，并交Main.lean及逐义务alignment.json。 |
| [MG-GF102 · 商环塔的稳定、比较与自然性](lean-construction/MG-GF102/task.md) · [合同](lean-construction/MG-GF102/contract.json) | 0.1.1 · 6阶段 | **S6**：Answer.lean须共同形式化S1–S5及反例，附阶段声明表并实际编译、公理审计。 |
| [MG-GF104 · 初始拓扑、子空间与分离性修复](lean-construction/MG-GF104/task.md) · [合同](lean-construction/MG-GF104/contract.json) | 0.1.1 · 6阶段 | **S6**：四个必交文件共同修复一般构造并覆盖子空间、T0及完整反例。 |
| [MG-GF106 · 陪集覆盖、商群计数与子群改变](lean-construction/MG-GF106/task.md) · [合同](lean-construction/MG-GF106/contract.json) | 0.1.1 · 6阶段 | **S6**：Answer.lean须完整形式化S1–S5，包含具体有限反例、选择和计数证明。 |
| [MG-GF108 · 加权逆算子的正性边界与接口修复](lean-construction/MG-GF108/task.md) · [合同](lean-construction/MG-GF108/contract.json) | 0.1.1 · 6阶段 | **S6**：原接口和Extensions须共同编译，完整实现扩展权重判断及反例。 |
| [MG-GF110 · 有限记录的可靠内近似与完整修复](lean-construction/MG-GF110/task.md) · [合同](lean-construction/MG-GF110/contract.json) | 0.1.1 · 6阶段 | **S6**：完整交付四模块并形式化弱条件反例、可靠性、真实最大核及替代充分条件。 |
| [MG-GF112 · 扩展非负最优界的取得与系统组合](lean-construction/MG-GF112/task.md) · [合同](lean-construction/MG-GF112/contract.json) | 0.1.1 · 6阶段 | **S6**：Answer.lean需共同实现全部分类、两个具体反例、不交并定理及逐阶段声明表。 |

### 次重点 · 0卷

| 试卷 | 版本与规模 | 实际阶段或义务证据 |
| --- | --- | --- |

证据短句仅描述实际需求。F07不强制合同参考图的唯一路线；有效短证、合并声明、独立重证和替代证明仍按原合同接受。

[分类源](taxonomy.json) · [机器目录与源散列](catalog.json) · [全部试卷](README.md)
