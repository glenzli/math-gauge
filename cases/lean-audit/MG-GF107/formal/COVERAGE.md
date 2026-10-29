# MG-GF107 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

所有 ℕ→ℝ 序列及所有 n,r；不要求 Rapid。 S/T 为逐点乘除 n+1，唯一性量化所有序列。

声明：`Multiplier.MathGauge.F107.transport_solve`, `Multiplier.MathGauge.F107.solve_transport`, `Multiplier.MathGauge.F107.solution_unique`, `Multiplier.MathGauge.F107.solve_add`, `Multiplier.MathGauge.F107.solve_smul`, `Reference.MathGauge.F107.weighted_identity`。

## S2

每个 r,C,f；Control(r+1,C,f) 推出同 C 的 Control(r,C,Sf)。Rapid 为 ∀r∃C≥0。 固定常数的一阶损失，不用 r+2 替换原输入。

声明：`Reference.MathGauge.F107.control_solve`, `Reference.MathGauge.F107.complete_rapid`。

## S3

每个 M,r,C≥0、支撑在 n≤M 的 f；输出常数 (M+1)C。 支持条件是 forall n, M<n -> f n=0；M=0 亦包含。

声明：`Extensions.MathGauge.F107.control_solve_supported`。

## S4

否定 ∃D≥0∀f，Rapid f 且 Control 0 1 f 推出 Control 0 D Sf。 任意高度 N 的单位尖峰同时为 Rapid，见证必须随 D 选择。

声明：`Extensions.MathGauge.F107.spike_rapid`, `Extensions.MathGauge.F107.no_uniform_rapid_zero_loss`。

## S5

∀f，Rapid f -> ∃D≥0 Control 0 D Sf。 C 从 f 的一阶 Rapid 见证取得；与 S4 交换量词即错误。

声明：`Extensions.MathGauge.F107.rapid_individual_zero_bound`。

## S6

逐个输入和结果字段审计，特别 r=0,C=1 的具体反例。 author Candidate 保留输入 r+2；fixed-C 目标缺口由 witness 证明，解/唯一性/线性仍有效。

声明：`Candidate.MathGauge.F107.InputControl`, `Candidate.MathGauge.F107.candidate`, `Candidate.MathGauge.F107.candidate_rapid`, `Extensions.MathGauge.F107.candidate_input_exact`, `Extensions.MathGauge.F107.buffered_interface_gap`, `Reference.MathGauge.F107.control_solve`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据存于 validation/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
