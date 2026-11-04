# 综合开发报告：公开任务、答卷审阅与私有探索

本合同定义本地0.5.0的当前综合开发分析：公开30份任务与私有3份探索合并；数学旧答与既有审阅重评复用，加入三份同族书面加强稿的原生初答。重复/自查协议0.3.0固定选用A1/A2和每个分支的R1。它不是一次同步启动的新考试。AR纳入、60/30/10判准与权重发生在观察结果之后，须明示为post-observation方法变更；旧原答、执行和审核保留，已发布0.4.0与更早资产不改。原A3、第二轮自查及旧87/177记录保留在各自原配置中。

## 固定范围与权重

能力共33份首次答卷：26份公开数学任务、4份真实答卷审阅、3份私有研究探索。它们关联24个母题家族；审阅直接关联已有母题并共享历史来源，不能称为33个独立数学题材。同母题审阅先聚合，再在审阅方向内平均。每份数学卷按原合同归一化，阶段和章节义务不作独立样本或额外权重，不取最佳一次。

| 能力方向 | 任务数 | 能力权重 |
| --- | ---: | ---: |
| 书面推理 | 14 | 22.5% |
| Lean语义审计 | 5 | 18% |
| Lean生成与修复 | 5 | 18% |
| 整章形式化 | 2 | 18% |
| 研究探索 | 3 | 13.5% |
| 真实答卷审阅 | 4 | 10% |

真实答卷审阅每题100分：核心判断60、依据与影响30、补充完整性10。主指标为审阅能力分，重大误判题数及比例单列，严格通过只作辅助。重大误判依实际断言与影响裁决，不由分数阈值倒推；定义见[审阅评分合同](answer-review-scoring.md)。

| 综合部分 | 固定范围 | 综合权重 |
| --- | --- | ---: |
| 能力分 | 上述六方向，首次答卷 | 75% |
| 重复作答稳定性 | 固定选取的6题，各两次严格全对 | 5% |
| 无反馈自查 | 同6题的6份后续，重点数学正确性 | 10% |
| 立场干扰下的自查 | 同6题的12份后续，重点数学正确性 | 10% |

总范围57份记录：33份首次答卷、6份额外独立答卷、18份后续自查。仅公开版为30份首次/54份总记录，关联21个母题家族；其原四方向各22.5%，审阅10%，综合权重同为75/5/10/10。探索与审阅目前不安排重复或自查，这三项不能扩张解释为全部任务的可靠性。

## 证据组合与公开投影

共享runner绑定冻结源计划、原答散列、评分版本及新审核；展示脚本只读取公开结果生成HTML、Markdown与SVG/PNG，不另写评分公式或修改原答。重评改变审核版本与汇总口径，不补造候选执行身份、重跑模型或继承正式比较资格。

| 证据部分 | 当前报告选取 | 执行边界 |
| --- | --- | --- |
| 公开数学答卷 | 26份首次、6份额外独立与18份后续，共50份 | 原始材料与散列保留 |
| 真实答卷审阅 | 每模型4份首次；两模型已有8份原答 | 复用已按60/30/10完成的重评，本次不重考 |
| 私有研究探索 | 3份首次 | Terra保留原已有1份及后续新增2份来源；Gemini保留对应真实独立执行 |

私有题面、参考、判准、未公开来源、内部题号、原答、详细审核与本机路径留在私有存储。公开仅用Private-01至Private-03、中性分类、完成分、状态和经审核可公开的身份指纹，不含可还原私有内容的正文或节选。AR来源为公开数学任务，不混入私有题材标题。

公开JSON是共享评分的显式投影。HTML内嵌成绩与图表，不依赖网络、外部字体、远端脚本或浏览器读取邻近JSON，可直接保存离线阅读。当前公开展示统一本地0.5.0，不并挂一套竞争的旧当前榜；原始证据通过保留快照和Git历史复核。

## 缺测、审核与解释范围

未返回、执行失败、交付未通过和审核未决分别保留；未知精确分为null，固定分母上下界不是置信区间，不按已完成子集重新归一化。审阅重大误判未决为null，不能当作无误判。当前8份审阅重评采用同一新判准，不用后续更好答卷替代首次答卷。

题目及答卷均为AI审核、人审待办。编译、公理审计、语义对应、执行来源、人审和后端身份核验分别记录；原43份数学卷的作者Lean不覆盖三份新书面稿或审阅任务。历史Lean只引用原身份，不因组合或页面生成重新宣称核验。运行标签、日期和散列不能独立认证实际后端；不同执行批次、预算与历史复用保留其限制。

这是观察结果后的暂定开发比较，不具正式模型比较资格，不宣称隐藏留出或认证的一般能力排名。公开参考和Git历史保持透明可读，仍不属于候选题包。

## 外部同结构题库入口

以下路径均为通用占位。外部目录沿用本仓库的 `suite.json`、`sources.json` 和 case 文件结构，由同一 runner 按各自目录解析材料：

```sh
python3 -m math_gauge validate --suite cases --suite /absolute/external/cases
python3 -m math_gauge suite-compose \
  --suite cases --suite /absolute/external/cases \
  --id local-combined --version 1 --out runs/local-evaluator/suite.json
```

组合清单保存各来源 manifest 的路径、suite ID、版本与 SHA-256，重新加载时核对绑定；重复的来源 suite ID 或 case ID 均拒绝。合并成员不自动选择评分方向、权重或重复面板。先准备显式自定义 `runs/local-evaluator/profile.json`，覆盖组合成员并绑定其 suite 身份；运行条件另写入 `runtime.json`：

```sh
python3 -m math_gauge benchmark-plan \
  --suite runs/local-evaluator/suite.json --profile runs/local-evaluator/profile.json \
  --runtime runs/local-evaluator/runtime.json --out runs/local-evaluator/plan.json
python3 -m math_gauge benchmark-export \
  --suite runs/local-evaluator/suite.json --plan runs/local-evaluator/plan.json \
  --out runs/local-bundle --evaluator-out runs/local-export-evaluator
```

也可在 `benchmark-export` 中以 `--profile runs/local-evaluator/profile.json` 和可选 `--runtime` 代替 `--plan`，直接创建新计划；`--plan` 与 `--profile` 不能同时使用。直接创建新计划时，省略 `--runtime` 只作准备。组合清单、完整 profile 与 evaluator 输出保留本地，不放入候选消息。上述命令均不调用模型。

历史答卷跨计划复用使用已有 run 目录，不重跑候选：

```sh
python3 -m math_gauge benchmark-report \
  --run /absolute/source-run-a --run /absolute/source-run-b \
  --composition-plan runs/local-evaluator/plan.json \
  --suite runs/local-evaluator/suite.json \
  --answer-review-sources runs/local-evaluator/answer-review-sources.json \
  --model-aliases runs/local-evaluator/model-aliases.json \
  --frozen-source-reports runs/local-evaluator/frozen-source-reports.json \
  --composition-budget-policy retain_source_budgets --out runs/local-composed-report
```

| 参数 | 作用 |
| --- | --- |
| `--run` | 提供需复用的数学源运行。仅由 `--answer-review-sources` 构成的纯AR组合可省略它，但仍须 `--composition-plan` 与可信 `--suite`；普通报告模式仍须至少一个run。 |
| `--composition-plan` | 显式指定新评审计划、槽位和固定分母；输出标记为组合分析，不创建新的执行身份。 |
| `--answer-review-sources` | 仅组合模式可用，接入已有单轮审阅run与按新冻结审阅合同完成的维度审核；不调用模型、不把维度当数学阶段。 |
| `--model-aliases` | 可选 JSON，按“源 model label → 目标 model label”声明名称对应；不认证实际后端。 |
| `--frozen-source-reports` | 可选 JSON，以需复用冻结报告的源 run 的绝对路径为键，值含 `path`、`sha256`、`review_snapshot_sha256`；引用操作者信任的旧报告及原审核快照，重新核对答卷、历史、材料与审核绑定，不重编 Lean，也不宣称当前引擎已重现旧审核。 |
| `--composition-budget-policy` | 默认 `require_matching` 要求源时限匹配；显式 `retain_source_budgets` 可保留不同源时限的分层，仍要求上下文策略、系统提示及生成参数匹配。 |

模型别名、冻结报告与审阅来源JSON均只用于显式组合计划；可依选取范围省略不需要的项。每次使用新的输出路径。来源、散列和别名声明不自动建立正式比较资格，公开摘要继续使用前述脱敏投影。

[默认综合评分标准](benchmark-scoring.md) · [运行证据标准](execution-evidence.md) · [历史开发试跑](../docs/terra-pilot-2026-11-02.md)

已有审阅答卷通过独立来源数组绑定。以下均为通用占位路径：

```json
[
  {
    "run": "/absolute/existing-answer-review/model-run",
    "reviews": "/absolute/current-answer-review-dimension-reviews.json",
    "post_observation_rescoring": true,
    "notes": "观察既有原答后的0.4.0审阅合同重评；保留原执行与旧审核"
  }
]
```

`run`指向已完成的ordinary审阅运行目录，`reviews`指向具名评审者填写的新版维度审核数组。`--suite`可重复提供可信的新题库或组合清单；接口核对新合同、rubric、reference和完整候选消息与原答绑定。组合统一经过共享 `score_composed_runs`，不复制计分实现，不重发请求，也不把重评伪装为新执行。导出或构建不自动授权实际候选调用。
