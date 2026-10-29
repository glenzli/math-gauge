# MG-GF110 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意有限 B 与任意 g，包括 B=∅；停止界正好 |B|。 层递归为 B.filter，有限基数下降证明稳定，无停止证书字段。

声明：`RecordLayers.MathGauge.F110.layers_decreasing`, `RecordLayers.MathGauge.F110.layers_stable_tail`, `RecordLayers.MathGauge.F110.layers_stabilize`, `RecordLayers.MathGauge.F110.terminal_mem`。

## S2

E 仅 ∀x,qx∈B -> q(fx)=g(qx)。 安全尾轨道及终层固定点保证每次 E 调用合法。

声明：`Candidate.MathGauge.F110.terminal_implies_safe`, `Candidate.MathGauge.F110.exact_realization`, `OrbitModel.MathGauge.F110.safe_in_layers`, `OrbitModel.MathGauge.F110.safe_step`。

## S3

Bool, B={false},q=f=id,g=const true。 完整计算 K、T，证明 W 真且 E 假。

声明：`Reference.MathGauge.F110.stuttering_counterexample`, `Extensions.MathGauge.F110.stuttering_counterexample_complete`。

## S4

W 用于 q^-1(T)⊆K；任意 S 的最大性不含 W/E。 K 是全轨道安全谓词，弱记录只给可靠内近似。

声明：`Reference.MathGauge.F110.terminal_sound_for_stuttering`, `Reference.MathGauge.F110.safe_subset`, `Reference.MathGauge.F110.safe_maximal`, `OrbitModel.MathGauge.F110.safe_step`。

## S5

W 加 ∀y∈B,g(y)∈B；所有 n 均 T_n=B。 A 本身前向不变；Bool 翻转记录例证此条件不推出 E。

声明：`Extensions.MathGauge.F110.all_layers_eq_of_closed`, `Extensions.MathGauge.F110.stutters_closed_forward`, `Extensions.MathGauge.F110.exact_under_record_closed`, `Extensions.MathGauge.F110.closed_counterexample`。

## S6

各阶段范围分别绑定，不把 W 包装成 E。 完整 RecordLayers/OrbitModel/Candidate/Reference/Extensions 显式源闭包；已证强定理保留并注明范围。

声明：`Extensions.MathGauge.F110.exact_under_record_closed`, `Extensions.MathGauge.F110.closed_counterexample`, `Extensions.MathGauge.F110.stuttering_counterexample_complete`, `Reference.MathGauge.F110.terminal_sound_for_stuttering`, `Reference.MathGauge.F110.safe_maximal`, `Candidate.MathGauge.F110.exact_realization`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据存于 validation/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
