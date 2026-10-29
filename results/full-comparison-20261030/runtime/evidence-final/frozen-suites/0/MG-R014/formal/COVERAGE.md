# MG-R014：实际对象与 Lean 覆盖

Lean 4.29.1；Mathlib revision `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。本题独立编译，仅依赖下列两个本题模块及指定版本的公开 Mathlib。未导入旧题、OET 项目库或环境中的其他构建结果。

所有声明位于 `MathGauge.LinearSystems`。`I →₀ k` 就是原文有限支撑行空间，`I → k` 是全部赋值；域和全部指标类型任意。泛型线性映射引理实际应用于原行映射和增广坐标映射，没有把整体解、分类或延拓作为结构字段。

| 原文义务或新结论 | 实际定义／声明 |
|---|---|
| 原行、常数和赋值配对的真实线性映射 | `rowMap`, `constantMap`, `evaluate`, `evaluate_single` |
| 原题有限子系统可解的量词 | `finiteSolvable`，对全部有限 `Finset J`，赋值在完整 `I → k` 中 |
| 有限可解性推出所有有限行关系的常数相容 | `finiteSolvable_relations` |
| 核包含当且仅当存在延拓解，基扩充来自 Mathlib 实证定理 | `solvable_iff`，使用实际范围限制右逆及 `LinearMap.exists_extend` |
| 原坐标赋值与泛函解的完整双射 | `coordinateEquiv` |
| 真实整体解存在 | `global_solution` |
| 商对偶参数化全部解及双向互逆 | `solutionEquiv`, `coordinateParameters` |
| 参考式 (1) 的逐坐标公式及平移差公式 | `coordinateParameters_apply`, `parameter_difference` |
| 坐标子集的有限支撑延零映射 | `observationMap`；在基向量上恰为 `single i 1` |
| 观测映射的像是所列坐标基向量的线性包 | `observation_range` |
| 实际坐标限制方程与泛函复合条件等价 | `observation_equation` |
| 增广方程解与指定观测纤维的完整双射 | `augmentedEquiv`, `coordinateFiberEquiv` |
| 像的必要充分判据，即参考式 (2) | `restriction_image`, `coordinate_image` |
| 每个非空纤维与商掉行空间及观测空间后的对偶双射 | `restrictionFiberEquiv`, `coordinateFiberParameters` |
| 参考式 (3) 的对应构造 | `restrictionFiberEquiv` 复用 `solutionEquiv` 的加法／商映射公式；`LinearMap.range_coprod` 把实际增广像识别为两像之和 |
| 全部主目标在原有限可解性前提下同时成立 | `complete_classification` |
| 附加式 (4)：全部行有限仿射后果恰为有限原行组合 | `consequence_iff`, `coordinate_consequence` |

仿射分类由实际双射和加法／差公式表达；代码没有另给解集安装 Lean 的 `AffineSpace` 实例，也不把这项包装工作冒充额外数学结论。相容性与分离泛函都由真实行空间产生。空指标、空行族、空观测集和零商空间由同一泛型证明覆盖，无非空性或有限维前提。

完整源码清单和散列见 `manifest.json`；所有 `MathGauge` 声明（包括辅助声明和私有声明）的递归公理依赖由生成的 `CurrentAudit.lean` 检查。仅允许 `propext`、`Classical.choice`、`Quot.sound`。编译和公理审计不等于人工审定；human pending。
