# 形式化能力画像 0.1.0

本组件给当前评分版1.2.0增加第九轴“形式化能力”，采用规则选定答卷的 **Lean 整体 SMC**，同时覆盖语义审计、工程形式化和对齐自查。复用现有严格审核，不新增候选调用、数学评审、编译或主榜分数。

## 严格验收与范围

本轴沿用既有35分 Lean 大类：语义审计10分、工程形式化15分、对齐自查10分。八道初答题及 MG-C003 固定三轮自查均在范围内；三轮轨迹不增加独立数学家族。原题型、家族与变体权重保持不变，不将义务数拼成新分母，也不把三项简单等权平均。

工程题须使用实际交付的首答工程，全部所需义务、原字节编译、公理限制、对象和量词、表示桥及逐项语义对应均达标，且通过原 Strict 提交与承诺审核门槛。仅能编译或自报100%不构成通过；MG-C003 的92项少一项，其工程整题 SMC 即为0。语义审计同样按整题全部实质要求验收，不按局部正确率给严格部分分。

自查按完整三轮轨迹验收：最终92项全部核准，每轮交付与诊断准确，无虚报完成或回退；任一必需条件不成立，整条自查轨迹 SMC 为0。后续修好工程不回填初答工程分，两者使用既有独立计分位置。没有正常最终交付时，沿用原提交规则的 SMC 零分。

轴上中间值表示不同整题或整条轨迹的通过情况及其原有权重，不表示一个未通过的任务“差一点完成”仍获部分严格分。

## 数值与未知

设共享评分器的 Lean 整体 SMC 已确认贡献为 c，满分恒为35，则本轴0–4刻度为4c/35；画像沿用共同0–100展示刻度，即100c/35。直接投影原报告的 lean 聚合贡献，算术只由 scoring.py 完成，页面不重算数学判分或权重。

来源已完整核准时，使用未提前四舍五入的 confirmed 生成精确值；来源报告向外取整的上下界不制造额外未知。确有未测或未决材料时，沿用原大类 lower／upper／confirmed 并同尺度投影，exact 保持 null。已知失败保持精确0，未知不充作失败；不把已测部分归一化为满分。

覆盖单位为 lean_subcategory，固定 planned=3；reviewed 对应原大类已结算子类数。它不是题目数或家族数，不与其他轴的35家族或开放研究五家族覆盖相加。

## 来源和阶段

每个模型投影绑定现有画像、规则选定的1.1.0 SMC 报告、该报告公开来源清单和原记录，另绑定本政策及评分政策。报告中保留初答与既有三轮自查的实际来源。相同来源输入须复现相同投影，已采用模型投影不得静默改写；新增模型时可向索引追加未变来源。

全部保留模型均生成数据，1.2.0页面仍按明确入选名单过滤，撤下模型不因此回榜。中性续答不涉及 Lean，因此“首答／含续答”的形式化能力使用相同初答与三轮自查成绩，不再次80／20混合。“首答”阶段仍包括原 benchmark 已规定的三轮自查，并非删除这条原有轨迹。历史1.1.0保持七轴，1.0.0没有画像。

本组件不产生新的独立能力评审或人工批准。原答、工程、原数学判分、原七轴、开放研究能力及 MC／RMC／SMC 主分保持不变。公开增加的只有来源绑定、聚合值与覆盖，不暴露私有题目或逐题评审。

## English

The ninth axis, **Formalization**, uses **SMC for the entire Lean category**: semantic audits (10 points), initial engineering (15) and alignment self-checks (10). Retain the existing 35-point total, original task/family/variant weights, eight initial tasks and prescribed three-round MG-C003 trajectory. The trajectory is not another independent mathematical family.

Each task must meet every substantive requirement for strict credit, including actual delivery, semantic alignment, original-source compilation and permitted axioms. One missing engineering obligation fails that whole task; 91/92 is not partial strict credit. The self-check trajectory passes only when the final 92 obligations are verified and all three rounds meet delivery, accurate-diagnosis, no-false-completion and no-regression requirements. Any failed required condition gives the whole trajectory zero SMC. Later repairs do not replace initial engineering credit.

Project the official Lean aggregate c directly: the 0–4 grade is 4c/35 and its common 0–100 display is 100c/35. Intermediate values represent different whole tasks or trajectories passing with their original weights, not partial credit within a failed task. Preserve known zero, genuine unknown intervals and fixed denominators. Coverage uses three Lean subcategories, not task or family counts.

Both profile stages use the same initial answers and original three-round trajectory because neutral revisions exclude Lean. The first-answer stage still includes that prescribed trajectory. All retained configurations receive bound projections, while current edition cohort filtering remains unchanged. Historical 1.1.0 keeps seven axes and 1.0.0 has none. No candidate calls, mathematical judgments, compilation or human approval are added; existing reviews and main scores remain intact.
