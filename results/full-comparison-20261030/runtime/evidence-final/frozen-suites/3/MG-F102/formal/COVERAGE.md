# 语义覆盖表

| 正文义务 | Lean 声明 | 覆盖 |
| --- | --- | --- |
| 实际商环 Q_n 与理想 J_n | Level / residual | 实际 Ideal.Quotient 与 Ideal.map |
| 指定指数 J_n^(n+1)=0 | residual_power_zero | 全部交换含幺环、全部理想及 n；由 residual_power_zero_iff 代入 |
| 过渡保持理想像 | residual_transition | 全部 m≤n |
| 三层复合律 | residual_composition | 全部 l≤m≤n |
| 原理想额外幂零前提不普遍成立 | top_int_not_nilpotent | 评审侧分离例，非候选必用路线 |

Reference.lean 不接受 SourceData。F101 的 Candidate 只含额外假设下的存在性幂零结论和两个正确过渡声明，故编译证据不是整题覆盖证据。

本表是作者自查，尚待独立 AI 审阅与人工裁决。Lean 编译、公理审计、语义审核和人工批准分别记录。
