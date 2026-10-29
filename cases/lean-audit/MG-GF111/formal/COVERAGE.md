# MG-GF111 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意 X，包括空类型；所有 c:ENNReal，含0和∞。 regular subtype 为 d≠0且d≠∞，等价正有限；不要求 e/c 有限。

声明：`Extensions.MathGauge.F111.bound_iff_regular`, `Extensions.MathGauge.F111.empty_ratio`, `Extensions.MathGauge.F111.empty_least`, `ExtendedBounds.MathGauge.F111.ratio_le_iff`。

## S2

所有 x 的 d≠∞，允许 d=0；所有 c。 零分母分支强制 e=0，对 c=∞ 同样成立。

声明：`Extensions.MathGauge.F111.bound_iff_no_top`, `ExtendedBounds.MathGauge.F111.bound_iff`。

## S3

任意 X,d,e,c；分别全系数、∃有限系数、∃有限最小系数。 保留 r=0 -> H；有限存在用 r+1，最小不存在时不能把 infimum 当取得。

声明：`ExtendedBounds.MathGauge.F111.bound_iff`, `CoefficientClassification.MathGauge.F111.finite_bound_exists_iff`, `CoefficientClassification.MathGauge.F111.least_finite_exists_iff`, `CoefficientClassification.MathGauge.F111.least_coefficient_eq`。

## S4

X=ℕ,d=1,e=n；∀有限F∃有限cF，但不存在全域有限c。 局部常数取 F.sup id，空集为0；用 ENNReal Archimedean 性证明全域无界及 r=∞。

声明：`Extensions.MathGauge.F111.LocalFiniteBounds`, `Extensions.MathGauge.F111.natural_local_bounds`, `Extensions.MathGauge.F111.natural_no_global_bound`, `Extensions.MathGauge.F111.natural_ratio_top`。

## S5

∀有限F∃cF≤C，得 Bound C；给定 C 有限即可得到有限全域界。 只取单点，无除法；故 d=0/∞ 和空 X 一并覆盖。

声明：`Extensions.MathGauge.F111.uniform_local_implies_global`。

## S6

逐项审计原分类及 Unit 无限分母边界。 旧声明对 S3 对齐；S4/S5 为当前新增证明，不能以旧编译替代。

声明：`ExtendedBounds.MathGauge.F111.ratio_le_iff`, `ExtendedBounds.MathGauge.F111.bound_iff`, `CoefficientClassification.MathGauge.F111.finite_bound_exists_iff`, `CoefficientClassification.MathGauge.F111.least_finite_exists_iff`, `CoefficientClassification.MathGauge.F111.least_coefficient_eq`, `BoundaryExample.MathGauge.F111.boundary_ratio`, `BoundaryExample.MathGauge.F111.boundary_feasible`, `BoundaryExample.MathGauge.F111.boundary_not_attained`, `Extensions.MathGauge.F111.boundary_bound_iff`, `Extensions.MathGauge.F111.boundary_finite_iff`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据存于 validation/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
