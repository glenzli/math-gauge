# R101 正文—Lean 覆盖

编译目标：`CongruenceObstruction.lean`；命名空间 `MathGauge.R101`。
实际前提为任意 `Ring R`、`AddCommGroup M`、`Module R M` 及三个任意 `Submodule R M`。没有域、交换环、自由、有限生成、可分裂或分配格假设。

| 题面义务 | 实际声明与对象 |
| --- | --- |
| 相容记录模 P | `Compatible`, `records`：M×M×M 中的实际子模，三个差分别属于对应子模和 |
| E 及记录商 Q | `noise`：P 中坐标分别属于 A,B,C 的实际子模；Q 为 `records ⧸ noise`；`record_equality` 精确展开逐坐标代表等价 |
| 题面 L,H,O | `ambiguity`, `obstruction_space`, `obstruction_image`；O **确实是 H 在 M/L 中的像子模**，不是整个环境商 M/L |
| 部分实现存在与障碍落点 | `partial_exists`, `obstruction_mem`，由实际相容条件推导 |
| 选择无关及通过代表商下降 | `partial_difference`, `obstruction_independent`, `raw_obstruction`, `noise_in_kernel`, `obstruction`；原始 choice 不被假定线性，线性在商中证明 |
| 障碍实际落在 O 且满射 | `obstruction_range`, `obstruction_onto`, `obstruction_surjective` |
| 指定归一化 | `elementary_record`, `obstruction_normalization` |
| 指定对角 j 良定单射 | `diagonal`, `residue_map`, `residue_kernel`, `residue_embedding`, `residue_embedding_injective` |
| 零类充分必要与中间正合 | `obstruction_zero_iff`, `raw_zero_iff`, `obstruction_zero_on_record`, `same_record_iff`, `obstruction_exact`, `obstruction_onto_exact` |
| 全部原始实现 | `solution_fiber`：给定一个实际实现 t，任意 s 是实现 iff s−t 属于实际交子模 |

两份短正合端点用单射/满射和中间核像相等编码，没有把“短正合”放进待证证书。实际构造定义和支持引理一并接受公理依赖审计。

参考中额外说明的障碍映射唯一性与三个具体错误路径反例目前为完整自然语言论证，未另外声明 Lean 定理；它们不是题面增加的候选义务。主任务全部在实际对象上编码。题面直接采用像空间 O，因而不存在把 H/L 与环境商 M/L 混用的语义缺口。

作者阶段检查：源文件已使用 Lean 4.29.1 与固定 Mathlib 修订编译；精确散列和统一内核审计由整合验证报告记录。编译通过不等于独立语义审查或人工批准；human pending。未运行候选模型。
