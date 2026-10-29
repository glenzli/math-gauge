# 0.4.0 扩展组：完整 Lean 与单次 Terra 校准

MG-R011–MG-R020 各完成一次新的 task-only 隔离运行，独立 AI 数学审核 **10/10 通过**，R019 另经一次独立复核通过。原 MG-R001–MG-R010 保持0.3.0版全部字节，其先前10/10结果仍绑定[原运行](../full-lean-terra/README.md)。这是两批各十题的校准，不能写成同一次二十题试验。

实际请求为 `gpt-6.1-terra` / `max`。十个新会话、十次stdin均完成，无失败模型尝试、重试或工具事件；后台型号及effort未由JSON独立回显，`observed_model` / `observed_effort` 保持null。审核者知道题面、参考及请求标签，采用独立AI数学审核，不称双盲。此前[仅task的题面审校](reviews/PROMPT-AUDIT.json)是另一项工作。所有human状态仍为pending。

## 答卷与审核

| 题号 | 作者源码模块数 | 动态声明数 | 原答卷 | 独立AI数学审核 |
| --- | ---: | ---: | --- | --- |
| MG-R011 | 2 | 44 | [答卷](terra/answers/MG-R011.md) | pass |
| MG-R012 | 1 | 45 | [答卷](terra/answers/MG-R012.md) | pass |
| MG-R013 | 4 | 120 | [答卷](terra/answers/MG-R013.md) | pass |
| MG-R014 | 2 | 73 | [答卷](terra/answers/MG-R014.md) | pass |
| MG-R015 | 1 | 60 | [答卷](terra/answers/MG-R015.md) | pass |
| MG-R016 | 1 | 50 | [答卷](terra/answers/MG-R016.md) | pass |
| MG-R017 | 1 | 30 | [答卷](terra/answers/MG-R017.md) | pass |
| MG-R018 | 1 | 78 | [答卷](terra/answers/MG-R018.md) | pass |
| MG-R019 | 2 | 75 | [答卷](terra/answers/MG-R019.md) | pass |
| MG-R020 | 1 | 72 | [答卷](terra/answers/MG-R020.md) | pass |

[合并原评分](reviews.json)逐项绑定case、task、reference、rubric及response SHA256；[评审清单](review-manifest.json)保留三份最终原评分和R019第二审的确切散列。工程整合只核对身份并原样转存，没有重新评分。比较范围见[两轮比较](comparison.md)，更短替代证明及额外合法贡献见root撰写的[数学校准观察](CALIBRATION-NOTES.md)。候选补充未另做Lean形式化，不属于作者参考的Lean覆盖声明。

## 作者形式化与工程证据

[formal-verification.json](formal-verification.json)逐题绑定三份冻结输入、COVERAGE、源码manifest及原始fresh build报告。新增十题共16个作者源码模块，每题另有一个生成的CurrentAudit；动态声明包括定义、实例、辅助和生成声明，不能称全部是定理。Lean4.29.1与Mathlib5e932f97dd25535344f80f9dd8da3aab83df0fe6固定，仅允许propext、Classical.choice、Quot.sound。

整合核对相同编译器、Mathlib tracked clean状态、直接依赖缓存、源码、Audit、原olean和日志后复用原报告，没有重复编译相同数学源码。可用[统一可移植入口](../../scripts/formal/README.md)及显式dependency-root在逐题新目录复核。作者阶段的待审或无候选运行文字作为原阶段记录保留。

[53项测试和validate](engineering/validation/report.json)通过，包含三个真实Lean工程fixture，无skip。[基线保留证据](baseline-preservation.json)及baseline/中的原suite/sources绑定原十题397个文件、版本和输入投影。

随后共享验证器出现外来题号支持与两项测试修改，本轮原样保留为现有依赖，不纳入本轮写入范围。只针对当前版本补跑8项manifest合同检查；不据此宣称外来草稿或未完成功能已经整体核验。原53项测试仍绑定当时源码，数学模块、Audit及依赖身份未变，见[外来依赖与兼容性范围](foreign-dependencies.json)。

完整运行证据见[terra/README.md](terra/README.md)：原ZIP保持原hash，十份可读答卷另存，全部事件、策略、进程和账本在ZIP中；state、凭据与编译产物不入归档。`evidence-whitelist.json`路径就是ZIP entry，[archive-map](terra/archive-map.json)说明原绝对路径的归档映射。
