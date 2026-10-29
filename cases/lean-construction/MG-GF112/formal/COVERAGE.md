# MG-GF112 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意 X，所有分母正有限且 r≠∞；无需存在取得比值 r 的点。 最小系数由上确界上界性质构造；空 X 得0。

声明：`Answer.MathGauge.F112.bound_iff_regular`, `Answer.MathGauge.F112.least_regular`, `Answer.MathGauge.F112.empty_ratio`, `Answer.MathGauge.F112.empty_least`。

## S2

任意 X,d,e及所有c，无预设有限或非空。 三类分母与 c=0 单独处理；必要性及充分性均完整证明。

声明：`ExtendedBounds.MathGauge.F112.bound_iff`, `CoefficientClassification.MathGauge.F112.finite_bound_exists_iff`, `CoefficientClassification.MathGauge.F112.least_finite_exists_iff`, `CoefficientClassification.MathGauge.F112.least_coefficient_eq`。

## S3

Unit,d=∞,e=1；全系数可行 iff c≠0，有限可行 iff 0<c<∞。 通过完整最小存在判据排除所有最小候选，不仅排除0。

声明：`BoundaryExample.MathGauge.F112.boundary_ratio`, `BoundaryExample.MathGauge.F112.boundary_feasible`, `BoundaryExample.MathGauge.F112.boundary_not_attained`, `Answer.MathGauge.F112.boundary_zero_compatible`, `Answer.MathGauge.F112.boundary_not_top_compatible`, `Answer.MathGauge.F112.boundary_bound_iff`, `Answer.MathGauge.F112.boundary_finite_iff`。

## S4

任意两类型与数据，分别有最小有限 a,b；Sum 类型表示不交并。 Bound 拆成两支；max 有限、可行，且小于等于所有有限可行系数。

声明：`Answer.MathGauge.F112.sumData`, `Answer.MathGauge.F112.bound_sum_iff`, `Answer.MathGauge.F112.bound_mono`, `Answer.MathGauge.F112.least_sum`。

## S5

第一支 Unit,∞,1；第二支 Unit,1,1。 并系统恰 c≥1，最小1；第一支仍无最小，形式反例完整。

声明：`Answer.MathGauge.F112.oneData`, `Answer.MathGauge.F112.one_bound_iff`, `Answer.MathGauge.F112.one_least`, `Answer.MathGauge.F112.mixed_bound_iff`, `Answer.MathGauge.F112.mixed_least`, `Answer.MathGauge.F112.reverse_decomposition_counterexample`。

## S6

S1–S5 所有范围，以 ExtendedData 的原定义为基础。 Answer 加显式 helper 源闭包，没有把结论当字段或公理；分支组合证明在当前新增文件。

声明：`Answer.MathGauge.F112.least_regular`, `Answer.MathGauge.F112.boundary_bound_iff`, `Answer.MathGauge.F112.boundary_finite_iff`, `Answer.MathGauge.F112.bound_sum_iff`, `Answer.MathGauge.F112.least_sum`, `Answer.MathGauge.F112.reverse_decomposition_counterexample`, `CoefficientClassification.MathGauge.F112.finite_bound_exists_iff`, `CoefficientClassification.MathGauge.F112.least_finite_exists_iff`, `CoefficientClassification.MathGauge.F112.least_coefficient_eq`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据存于 validation/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
