# Math Gauge 1.0.0

[中文](#中文) · [English](#english)

## 中文

本次正式发布 benchmark **1.0.0**。题目与已发布的0.6.0、0.6.1保持一致：公开25题、私有14题，合计39道初答、35个数学家族；整章Lean题另接续固定三轮自查，共42次规定交付。所有题面、明确附件、参考和量规保持原字节。

- 评分采用RMC聚合0.9.0、MC0.3.0、SMC0.2.0及提交来源0.1.0。正常交卷只审核实际交付；无正常交卷时，经核实的截止原成果可计MC，RMC与SMC为0。三类权重仍为书面35／Lean35／数学研究30。
- 当前榜单收录17个模型配置的已选定结果，包含后续补测和具名来源更正。既有答卷保留实际执行版本、原答、原评与未知项；本次发布不调用模型，不重新评分。
- 所有正式题目允许本地工具及预置公共依赖，禁止联网检索和工具联网。每次预算为普通任务2700秒、其余七项Lean任务5400秒、C003初答与每轮自查10800秒。
- 公开发行只提供25题候选ZIP。受控39题完整包和外置评审计划仅在私有仓库发行；公私使用同一套公开控制器。
- `SHA256SUMS`校验候选ZIP，`release-lock.json`另绑定源码提交、运行器和全部附件散列。GitHub自动源码归档包含复核材料，不是候选题包。
- 原v0.6.0、v0.6.1及其资产保留。原1.0.0封版文件与历史验证记录不改写，本轮发布验证另附。封版和发布不改变AI审核、部分人工抽审及未测状态。

下载`benchmark-v1.0.0.zip`后，按包内README与同版`harness-guide-v1.0.0.md`准备。原固定三轮合同及提示单独随发行提供；封卷工程接续材料用于其明确限定的补充条件，不替换原固定提示。

## English

This release publishes **benchmark 1.0.0**. Mathematical tasks are unchanged from the published 0.6.0 and 0.6.1 editions: 25 public and 14 private A1 tasks, 39 in total across 35 mathematical families, plus three fixed whole-chapter Lean self-check rounds for 42 prescribed deliveries. Task text, explicit attachments, references and rubrics retain their original bytes.

- Scoring uses RMC aggregation 0.9.0, MC 0.3.0, SMC 0.2.0 and submission component 0.1.0. A normal final limits review to the delivered work. Without one, verified original work present by the cutoff may earn MC; RMC and SMC are zero. Written/Lean/research weights remain 35/35/30.
- The current leaderboard contains 17 selected model configurations, including source-bound supplements and corrections. Historical answers retain their actual execution versions, original responses, reviews and unknown fields. Publication makes no model calls or new scoring judgments.
- All tasks allow local tools and preinstalled public dependencies; external retrieval and tool networking are prohibited. Budgets are 2700 seconds for ordinary tasks, 5400 for the seven other Lean tasks, and 10800 for C003 A1 and each self-check round.
- The public release contains only the 25-task candidate ZIP. The complete 39-task bundle and separate evaluator plan are released only in the private repository. Both use the same public controller.
- `SHA256SUMS` validates the candidate ZIP. `release-lock.json` binds source commits, the runner and all companion asset hashes. GitHub's automatic source archives contain review material and are not candidate packages.
- Existing v0.6.0 and v0.6.1 releases and assets are preserved. The original 1.0.0 seal and historical validation remain unchanged; this publication has separate validation evidence. AI review, partial human checks and unknown coverage retain their recorded status.

Read the ZIP's README and `harness-guide-v1.0.0.md` before running. The original three-round study and prompt are supplied separately. Sealed-workspace continuation files apply only to their declared supplementary condition and do not replace the original prompt.
