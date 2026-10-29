# 语义覆盖表

| 正文义务 | Lean 声明 | 覆盖 |
| --- | --- | --- |
| 实际初始拓扑 | assembled（F103）或 repaired（F104） | iInf of actual induced topologies |
| 全部 f_a 连续 | candidate_realizes / repaired_realizes | 任意指标集与目标类型族 |
| 最粗性 | candidate_coarsest / repaired_coarsest | 所有可行拓扑 s，正确反序 s≤τ |
| 入射映射双向性质 | candidate_inbound / repaired_inbound | 任意 Z、σ、g |
| 唯一性 | candidate_unique / repaired_unique | 两向序关系给相等 |

F104 原 Candidate 只完成映射连续和一个方向；Boundary.lean 以 Bool 的离散/不可分拓扑区分所缺性质。F103 候选本身就是完整作者参考，不能因为抽象或反序而判错。

本表是作者自查，尚待独立 AI 审阅与人工裁决。Lean 编译、公理审计、语义审核和人工批准分别记录。
