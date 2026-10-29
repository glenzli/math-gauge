# MG-GF109 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意 X,Y；B 为有限集、g 任意；精确记录仅在 qx∈B 时适用。 Finset 表示任意有限 B，DecidableEq 可经典选择，无 X/Y 有限或非空限制。

声明：`RecordLayers.MathGauge.F109.layers_decreasing`, `RecordLayers.MathGauge.F109.layers_stable_tail`, `RecordLayers.MathGauge.F109.layers_stabilize`, `RecordLayers.MathGauge.F109.terminal_mem`, `Candidate.MathGauge.F109.exact_realization`, `Reference.MathGauge.F109.safe_subset`, `Reference.MathGauge.F109.safe_maximal`, `OrbitModel.MathGauge.F109.safe_step`。

## S2

Bool, B={false}, q=f=id,g=const true。 弱记录成立，K={false},T=∅，精确记录失败。

声明：`Reference.MathGauge.F109.stuttering_counterexample`, `Extensions.MathGauge.F109.stuttering_counterexample_complete`。

## S3

弱记录只用于终层可靠性；最大性量化任意 S⊆A，不使用记录条件。 Safe 是所有自然数迭代均在 A，不是一步安全。

声明：`Reference.MathGauge.F109.terminal_sound_for_stuttering`, `Reference.MathGauge.F109.safe_subset`, `Reference.MathGauge.F109.safe_maximal`, `OrbitModel.MathGauge.F109.safe_step`。

## S4

∀x∈K∃k≥1，q(f^k x)=g(qx)；无共同 k 或延迟上界。 orbit_eq_iterate 连接递归轨道与通常迭代；逐层归纳同时量化所有安全点。

声明：`Extensions.MathGauge.F109.orbit_eq_iterate`, `Extensions.MathGauge.F109.safe_orbit`, `Extensions.MathGauge.F109.DelayedProgress`, `Extensions.MathGauge.F109.safe_in_layers_delayed`, `Extensions.MathGauge.F109.exact_under_delayed_progress`。

## S5

Bool 全集，q=f=id,g=not；等式成立但逐步精确记录失败。 安全核集合不确定记录动力学，不能逆推充分条件。

声明：`Extensions.MathGauge.F109.closed_counterexample`, `Extensions.MathGauge.F109.exact_under_record_closed`。

## S6

逐声明区分无条件有限稳定、精确记录下覆盖与弱记录下可靠性。 Realizes 为精确记录，故旧 Candidate 在弱条件下语义不对齐；S4 是另加条件而非原假设。

声明：`Extensions.MathGauge.F109.exact_record_unfold`, `RecordLayers.MathGauge.F109.terminal_mem`, `Candidate.MathGauge.F109.exact_realization`, `Candidate.MathGauge.F109.maximal_invariant`, `Reference.MathGauge.F109.terminal_sound_for_stuttering`, `Reference.MathGauge.F109.stuttering_counterexample`, `Reference.MathGauge.F109.safe_maximal`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据存于 validation/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
