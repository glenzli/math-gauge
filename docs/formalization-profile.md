# 形式化能力

当前1.2.0九轴画像中的“形式化能力”采用 **Lean 整体 SMC**，包含语义审计10分、工程形式化15分和三轮对齐自查10分，再将35分满分映射到画像0–100刻度。三个部分沿用现有权重，不简单等权平均。

每道题必须全部实质要求正确完成才得分；92项少一项，该工程整题即记0。编译成功还须满足语义对应、量词、表示桥、公理和交付要求。三轮自查作为整条轨迹验收，须最终完整、每轮诊断准确、无虚报完成或回退；差一项，整条轨迹的严格分即为0。

因此，工程全部通过并不自动等于这条轴满分。例如 Opus 5.5 Max 工程15/15、审计10/10，但自查0/10，轴值为25/35×100≈71.43；Gemini 4 Neon 工程15/15、审计7.5/10、自查10/10，轴值约92.86。这些值复用已有审核，没有重新判卷。

后续修好的工程不回填初答工程分。中性续答没有 Lean 任务，故“首答／含续答”两阶段使用同一初答与原有三轮自查成绩，不再80／20折算。“首答”阶段仍包含原 benchmark 规定的自查轨迹。无正常最终交付时沿用原 SMC 提交规则；未测或待核准保持未知区间，不重新归一化。

已为全部23个保留配置建立[来源投影](../results/formalization-profile/v0.1.0/index.json)，页面仍按当前入选名单展示，撤下模型不因此回榜。覆盖按三个 Lean 子类统计，不是题目或家族数。历史1.1.0保持七轴，1.0.0没有画像。没有新增模型测试、数学判卷或编译，原七轴、开放研究能力、主榜三分与原始审核均保留。

## English

The ninth **Formalization** axis uses **SMC for the entire Lean category**: semantic audits (10 points), initial engineering (15), and the prescribed three-round alignment self-check trajectory (10). Map the original 35-point total to the common 0–100 profile scale without changing task/family/variant weights.

Strict credit requires every substantive task requirement. One missing obligation fails that engineering task; compilation alone does not establish semantic alignment. The whole self-check trajectory requires complete final engineering, accurate diagnosis and delivery in every round, and no false completion or regression. Failing any required condition gives the trajectory zero SMC. Intermediate axis values reflect different whole tasks/trajectories passing, not partial credit inside a failed task.

Both stages retain the same initial answers and original three-round trajectory because neutral revisions exclude Lean. Repairs never replace initial engineering. Preserve known failures, genuine unknowns and fixed denominators. All 23 retained configurations have bound projections, with current cohort filtering unchanged. Historical 1.1.0 retains seven axes and 1.0.0 has none. No new calls, judgments or compilation are performed; source reviews and main scores remain intact.

[完整方法 / Specification](../protocol/formalization-profile.md) · [来源索引 / Sources](../results/formalization-profile/v0.1.0/index.json) · [数学画像 / Profile](../site/index.html?edition=1.2.0#mathematical-profile)

本地补齐或核验使用 `python3 scripts/assess_formalization_profiles.py --write` 及不带 `--write` 的检查命令。新增模型先补齐原画像与 SMC 来源，再生成本组件；命令不调用模型，已采用模型投影须逐字不变。

Prepare locally with `python3 scripts/assess_formalization_profiles.py --write`; omit `--write` to verify all sources and projections. Admit a new model's original profile and SMC sources first. The command makes no model calls and keeps adopted model projections byte-identical.
