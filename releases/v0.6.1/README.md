# Math Gauge distribution 0.6.1

[中文](#中文) · [English](#english)

## 中文

0.6.1 是页面、结果展示与分发更新；benchmark 题包继续使用已封版的 **0.6.0**。保留 v0.6.0 标签、发行和原资产，不覆盖或删除。题目、计分政策、原始答卷、原评审与已选成绩不因本次发布改变；AI审核／人审待定的状态也不改变。

- 汇总已经入库的九模型结果，包括 Sol 两档、Opus 及 DeepSeek 补充评测；尚在运行的 Astra 不纳入本次快照。
- 所有首页图表按模型横向分行，MC浅色、RMC实色、SMC粗斜纹；分类、差值与两率图可独立排序。
- 新增“仅显示已测完模型”开关，默认关闭，URL 参数为 `complete=1`。它只筛选显示；完成评测不代表题目全对，也不重算任何分数或分母。
- 页面界面支持中文与英文，URL 参数为 `lang=zh|en`。数学题面、原答和评审证据保留原始语言。中英文 README 使用各自语言的真实页面截图。

公开候选 ZIP 仍称 `benchmark-v0.6.0.zip`，内部题包及交换协议身份仍为0.6.0；本次0.6.1发行的 `release-lock.json` 单独绑定分发版本、精确源提交和资产散列。该名称不表示覆盖旧发行的同名资产。公开包仅含25题候选投影；完整39题包与外置评审计划只放私有发行。公私共用同一个公开控制器实现。

允许本地工具与预装公共依赖，禁止联网检索及工具联网；模型服务与认证通信另记。运行规则见[Harness指南](../../docs/harness-guide.md)，题包构建及身份分层见[分发协议](../../protocol/release-distribution.md)。构建、检查、网页生成和本次发布不调用候选模型。

## English

0.6.1 updates the website, result presentation and distribution. The sealed **benchmark suite remains 0.6.0**. The v0.6.0 tag, release and original assets are preserved. This release does not change tasks, scoring policies, original answers, original reviews or selected scores. AI review / human review pending remains unchanged.

- Includes the nine retained model results already adopted, including both Sol efforts, Opus and the DeepSeek supplement. The ongoing Astra run is excluded from this snapshot.
- All homepage charts use horizontal model rows: pale MC, solid RMC and broad diagonal stripes for SMC. Categories, gaps and rates sort independently.
- Adds “Completed models only”, off by default and shareable as `complete=1`. Evaluation completion is distinct from mathematical success; filtering never changes a score, weight or denominator.
- Adds Chinese / English interface switching through `lang=zh|en`. Mathematical tasks, original answers and review evidence remain in their source language. Each README has screenshots in its own interface language.

The candidate archive retains the name `benchmark-v0.6.0.zip` and its 0.6.0 suite / interchange identity. This 0.6.1 release has a separate `release-lock.json` binding the distribution version, exact source commits and asset hashes. Its assets do not replace the identically named assets of the older release. The public package contains only 25 candidate tasks; the complete 39-task package and separate evaluator plan are private. Both use the same public controller implementation.

Local tools and preinstalled public dependencies are allowed; external retrieval and tool networking are prohibited. Model-service and authentication traffic are recorded separately. See the [harness guide](../../docs/harness-guide.md) and [distribution protocol](../../protocol/release-distribution.md). Building, checking, generating the website and publishing this release make no candidate calls.
