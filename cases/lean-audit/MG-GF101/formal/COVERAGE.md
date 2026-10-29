# MG-GF101 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意交换含幺环 R、任意理想 A,B 与所有 r∈ℕ。 理想 map 与 pow 为原定义；r=0 精确等价 B=⊤，允许零环。

声明：`Transfer.MathGauge.F101.mapped_power`, `Reference.MathGauge.F101.residual_power_zero_iff`, `Extensions.MathGauge.F101.zero_exponent_iff`。

## S2

任意 I，不给 SourceData；所有 l≤m≤n。 pow_le_pow_right 给自然理想包含，商映射存在；J 的精确 n+1 次幂为零。

声明：`Reference.MathGauge.F101.residual_power_zero`, `Reference.MathGauge.F101.residual_transition`, `Reference.MathGauge.F101.residual_composition`, `Core.MathGauge.F101.transition`。

## S3

每对 m≤n，核为 q_n(I^(m+1))，指定过渡同态双射 iff 两幂理想相等。 从真实双射构造 RingEquiv；没有把仅存在抽象同构当作指定同态同构。

声明：`Extensions.MathGauge.F101.transition_surjective`, `Extensions.MathGauge.F101.transition_kernel`, `Extensions.MathGauge.F101.transition_bijective_iff`, `Extensions.MathGauge.F101.transition_equiv_of_powers_eq`。

## S4

ℤ 的单位理想，单个 N=1 对所有 n 同时有效，源理想所有幂均非零。 一般条件只推出 I^N≤iInf powers，不能擅自把交集换为0。

声明：`Extensions.MathGauge.F101.uniform_bound_iff_intersection`, `Extensions.MathGauge.F101.uniform_top_int`, `Reference.MathGauge.F101.top_int_not_nilpotent`。

## S5

已知 iInf_n I^(n+1)=⊥，每个固定 N（含0）两边等价。 保留同一个指数，不使用 Noether/Krull 定理或非零环假设。

声明：`Extensions.MathGauge.F101.separated_uniform_iff`, `Extensions.MathGauge.F101.zero_exponent_iff`。

## S6

按 Candidate 三项逐一审计其参数和输出。 SourceData 的指数/annihilates 是额外源幂零假设且对单位整数理想不可构造；修复直接证商的指定幂。像与复合仍正确。

声明：`Candidate.MathGauge.F101.candidate_nilpotent`, `Candidate.MathGauge.F101.candidate_transition`, `Candidate.MathGauge.F101.candidate_composition`, `Extensions.MathGauge.F101.no_source_data_top_int`, `Reference.MathGauge.F101.residual_power_zero`, `Reference.MathGauge.F101.residual_transition`, `Reference.MathGauge.F101.residual_composition`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据为 verification-report.json、declarations.json 和 logs/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
