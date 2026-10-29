# MG-GF103 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意指标族、源、依赖目标族与拓扑；所有测试类型 Z、s、g。 Mathlib 顺序反向，iInf induced 对应自然语言最粗，空族为⊤不可分。

声明：`Candidate.MathGauge.F103.candidate_realizes`, `Candidate.MathGauge.F103.candidate_coarsest`, `Candidate.MathGauge.F103.candidate_inbound`, `Candidate.MathGauge.F103.candidate_unique`, `Extensions.MathGauge.F103.empty_family`。

## S2

同一观测映射，∀i,t_i≤u_i（t更细）；所得τt≤τu。 连续id方向为τt→τu，未声称反方向自动成立。

声明：`Extensions.MathGauge.F103.refined_targets`, `Extensions.MathGauge.F103.refined_identity`。

## S3

X=Unit,A=Unit,Y=Bool,f恒true；目标为离散与不可分。 两初始拓扑相同而两个目标拓扑确实不同，不假定观测满射。

声明：`Extensions.MathGauge.F103.targets_not_recoverable`, `Extensions.MathGauge.F103.top_bool_not_le_bot`。

## S4

X=Bool,A=Unit,Y=Unit,f常值；σ离散可行，∀单点源拓扑和全部g均通过iff。 正确初始拓扑为不可分，与σ不同；完整单点测试量词被证明。

声明：`Extensions.MathGauge.F103.continuous_from_unit`, `Extensions.MathGauge.F103.point_tests_insufficient`。

## S5

σ可行且指定id:(X,τ)→(X,σ)连续。 两向序包含推出相等，不能删可行性或反向使用id。

声明：`Extensions.MathGauge.F103.identity_test_sufficient`。

## S6

原输入四项覆盖S1所有测试域和空族。 Candidate 完全对齐；S2–S5 为新增证明，原输入字节与作者版本均保留。

声明：`Candidate.MathGauge.F103.candidate_realizes`, `Candidate.MathGauge.F103.candidate_coarsest`, `Candidate.MathGauge.F103.candidate_inbound`, `Candidate.MathGauge.F103.candidate_unique`, `Extensions.MathGauge.F103.empty_family`, `Extensions.MathGauge.F103.refined_identity`, `Extensions.MathGauge.F103.point_tests_insufficient`, `Extensions.MathGauge.F103.identity_test_sufficient`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据为 verification-report.json、declarations.json 和 logs/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
