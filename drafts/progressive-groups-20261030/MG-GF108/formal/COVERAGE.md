# MG-GF108 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

∀v≥1、所有序列；所有 r,C 的同 C 一阶损失及 ∀r∃C 的快速衰减。 一般权函数与原控制定义逐点一致；线性为 LinearMap，互逆量化全体序列。

声明：`Extensions.MathGauge.F108.positive_of_one_le`, `Extensions.MathGauge.F108.variable_transport_solve`, `Extensions.MathGauge.F108.variable_solve_transport`, `Extensions.MathGauge.F108.variable_solution_unique`, `Extensions.MathGauge.F108.variable_solve_linear`, `Extensions.MathGauge.F108.variable_weighted_identity`, `Extensions.MathGauge.F108.variable_control_solve`, `Extensions.MathGauge.F108.variable_rapid_solve`。

## S2

v(n)=n+1；所有原始 r,C,f，而非仅 Rapid 输入。 原 Core 不变；作者 Candidate 改为 r+1，引用显式证明的完整 Reference。

声明：`Multiplier.MathGauge.F108.transport_solve`, `Multiplier.MathGauge.F108.solve_transport`, `Multiplier.MathGauge.F108.solution_unique`, `Multiplier.MathGauge.F108.solve_add`, `Multiplier.MathGauge.F108.solve_smul`, `Reference.MathGauge.F108.weighted_identity`, `Reference.MathGauge.F108.control_solve`, `Reference.MathGauge.F108.complete`, `Reference.MathGauge.F108.complete_rapid`, `Candidate.MathGauge.F108.candidate`, `Candidate.MathGauge.F108.candidate_rapid`。

## S3

仅 ∀n,0<v(n)；不要求统一正下界。 互逆只需各 v(n) 非零，权恒等/估计只需非负；没有声称 T 保持 Rapid。

声明：`Extensions.MathGauge.F108.variable_transport_solve`, `Extensions.MathGauge.F108.variable_solve_transport`, `Extensions.MathGauge.F108.variable_solution_unique`, `Extensions.MathGauge.F108.variable_solve_linear`, `Extensions.MathGauge.F108.variable_weighted_identity`, `Extensions.MathGauge.F108.variable_control_solve`, `Extensions.MathGauge.F108.variable_rapid_solve`。

## S4

若任意 n0 有 v(n0)=0；见证尖峰和零序列。 零坐标的除法为 0；某右端无解、零右端不唯一，故两侧互逆失败。

声明：`Extensions.MathGauge.F108.zero_weight_no_solution`, `Extensions.MathGauge.F108.zero_weight_nonunique`, `Extensions.MathGauge.F108.zero_weight_not_left_inverse`。

## S5

原正权 n+1，所有 r,f；Control r 0 f 强制 f=0。 C=0 可零阶保留，不能推广为正 C 的统一零损失。

声明：`Extensions.MathGauge.F108.zero_control_eq_zero`, `Extensions.MathGauge.F108.zero_control_solve`。

## S6

按 S1–S5 分别使用各自条件，全部文件闭包共同编译。 输入文件原件不改；修复仅在作者formal目录。所有目标字段用真证明构造。

声明：`Candidate.MathGauge.F108.candidate`, `Candidate.MathGauge.F108.candidate_rapid`, `Extensions.MathGauge.F108.repaired_input_exact`, `Extensions.MathGauge.F108.variable_solve_linear`, `Extensions.MathGauge.F108.zero_weight_no_solution`, `Extensions.MathGauge.F108.zero_weight_nonunique`, `Extensions.MathGauge.F108.zero_control_solve`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据存于 validation/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
