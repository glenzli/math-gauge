# R102 正文—Lean 覆盖

编译目标：`FiniteOrbitDecomposition.lean`；命名空间 `MathGauge.R102`。
实际前提为任意 `Ring R`、`AddCommGroup M`、`Module R M` 及 `Module.End R M`。`PointwiseFiniteOrbit` **定义为每个 x 的实际幂次轨道集合 Set.range 有限**；不是有限维张成、预先给定分解或统一稳定幂次证书。

| 题面义务 | 实际声明与对象 |
| --- | --- |
| N_T,P_T 是子模 | `nilpart`, `periodicpart`；分别按 ∃n,Tⁿx=0 和 ∃p>0,Tᵖx=x 定义，并逐项证明子模公理 |
| N_T∩P_T=0 | `nil_periodic_zero`，对同一个实际向量使用其个别零化与周期幂次 |
| 有限轨道给出周期尾部 | `finite_orbit_eventual`；有限值域上鸽巢原理实际导出不同位置重复，再得正周期 |
| 原模每个向量的分解 | `decomposition_exists`；使用 k=np 并从实际轨道等式证明两个分量的成员资格 |
| 分解及投影唯一性 | `decomposition_unique`, `projection_characterization` |
| 规范线性 e_T | `projection` 是实际 `Module.End`；加法及标量律从分解唯一性证明，不预设 choice 线性 |
| 核、像、幂等性 | `projection_kernel`, `projection_range`, `projection_idempotent` |
| M≅N_T⊕P_T | `decomposition_equiv`；对两个模，有限直和以实际乘积模表示，正反映射及逆律全编码 |
| T 在 P_T 上的自同构 | `periodic_restriction`, `periodic_restriction_bijective`, `periodic_automorphism`；单射和满射分别证明，不要求全局周期 |
| 任意交织映射下的自然性 | `semiconj_pow`, `semiconj_nil`, `semiconj_periodic`, `projection_natural`；目标模可不同，不假设交织映射单射、满射、可逆或有限维 |
| e_T 与 T 交换 | `projection_commutes` 是自然性的实际实例 |

构造中的经典选择只选择已证存在的周期分量，随后用唯一性消除其数学影响；不存在将目标塞入 certificate 输入的问题。主任务全部在实际对象上编码。

参考中的四个错误路径例子目前为完整自然语言核验，未逐个另建 Lean 模型；这些只供评分者检查错误推理，不是新增候选义务。

作者阶段检查：源文件已使用 Lean 4.29.1 与固定 Mathlib 修订编译；精确散列和统一内核审计由整合验证报告记录。编译通过不等于独立语义审查或人工批准；human pending。未运行候选模型。
