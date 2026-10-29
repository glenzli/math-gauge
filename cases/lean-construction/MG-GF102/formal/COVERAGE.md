# MG-GF102 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

只在此阶段有 I²=0；所有 n≥1 的指定 q_n 构成同构，Q0=R/I。 同构的底层映射就是原商映射；map I=J，层间及到第0层的图精确交换。

声明：`Answer.MathGauge.F102.level_zero_equiv`, `Answer.MathGauge.F102.square_zero_higher_power`, `Answer.MathGauge.F102.square_zero_level_equiv`, `Answer.MathGauge.F102.square_zero_residual`, `Answer.MathGauge.F102.square_zero_transition`, `Answer.MathGauge.F102.square_zero_to_zero`。

## S2

任意交换含幺环、任意 I、所有 l≤m≤n；不含平方零假设。 原目标三项均直接对 quotient/pow/map 证明，指定次数 n+1。

声明：`Reference.MathGauge.F102.residual_power_zero`, `Reference.MathGauge.F102.residual_transition`, `Reference.MathGauge.F102.residual_composition`, `Core.MathGauge.F102.transition`。

## S3

IsNilpotent I iff ∃N∀n≥N,指定sourceMap I n单射。 正向可取N=e，反向N+1给幂零次数；不把过渡同构/抽象同构偷换为源映射单射。

声明：`Answer.MathGauge.F102.sourceMap`, `Answer.MathGauge.F102.source_injective_iff`, `Answer.MathGauge.F102.nilpotent_iff_eventual_source_injective`。

## S4

R=ℤ,I=(2),S=ZMod2,L=⊥；第0层显式RingEquiv，第1层不存在任何RingEquiv。 通过真实理想商同构识别第1层为ZMod4/ZMod2，基数4≠2排除抽象同构。

声明：`Answer.MathGauge.F102.twoIdeal`, `Answer.MathGauge.F102.matching_zero_levels`, `Answer.MathGauge.F102.integer_level_one_equiv`, `Answer.MathGauge.F102.zero_ideal_level_equiv`, `Answer.MathGauge.F102.higher_levels_not_isomorphic`。

## S5

任意 φ:R→+*S 满足 I.map φ≤L，所有 n 和 m≤n。 像幂包含构造 quotientMap；模2具体例仍在第1层非单射，故自然性只保证同态。

声明：`Answer.MathGauge.F102.inducedLevel`, `Answer.MathGauge.F102.induced_source`, `Answer.MathGauge.F102.induced_transition`, `Answer.MathGauge.F102.modulo_two_compatible`, `Answer.MathGauge.F102.induced_example_not_injective`。

## S6

每阶段只使用本阶段条件；完整 Answer 与声明闭包。 保留 Core 原定义，不把 I 幂零/平方零设为全局上下文，也不凭类型声明代替证明。

声明：`Answer.MathGauge.F102.square_zero_level_equiv`, `Answer.MathGauge.F102.nilpotent_iff_eventual_source_injective`, `Answer.MathGauge.F102.matching_zero_levels`, `Answer.MathGauge.F102.higher_levels_not_isomorphic`, `Answer.MathGauge.F102.inducedLevel`, `Answer.MathGauge.F102.induced_source`, `Answer.MathGauge.F102.induced_transition`, `Answer.MathGauge.F102.induced_example_not_injective`, `Reference.MathGauge.F102.residual_power_zero`, `Reference.MathGauge.F102.residual_transition`, `Reference.MathGauge.F102.residual_composition`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据为 verification-report.json、declarations.json 和 logs/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
