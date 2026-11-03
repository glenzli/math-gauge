# 综合开发报告：公开题与私有探索的组合

本合同用于 [2026-11-03 Terra 综合报告](../docs/terra-combined-2026-11-03.md)，不改写默认 0.3.0 题集、任务包、80 槽 profile 或历史成绩。综合报告复用已经独立、隔离作答的历史材料，并接入新增独立答卷；它不是一次同步启动的全新运行。

## 固定范围与权重

能力部分共 **35 份 A1**：原公开默认题集的 32 份，加 3 份私有研究探索。每份卷先按本题冻结合同归一化，再在方向内平均，按组合 profile **v0.2.0** 的方向权重汇总；不选择最佳一次。

| 能力方向 | A1 份数 | 能力分权重 |
| --- | ---: | ---: |
| 书面推理 | 18 | 25% |
| Lean 语义审计 | 6 | 20% |
| Lean 生成与修复 | 6 | 20% |
| 整章形式化 | 2 | 20% |
| 研究探索 | 3 | 15% |

| 部分 | 固定范围 | 综合分权重 |
| --- | --- | ---: |
| 能力分 | 上述五方向按冻结权重汇总 | 75% |
| 三次全对 | 原公开六题面板，各 A1/A2/A3 严格全对 | 5% |
| 中性自查 | 同六题 N1/N2 的重点正确性，共 12 槽 | 10% |
| 立场自查 | 同六题 P1/P2/D1/D2 的重点正确性，共 24 槽 | 10% |

**总计 83 槽 = 原公开 80 槽 + 私有探索 3 份 A1。** 三份探索不补做重复或自查，因此可靠性三项只代表原公开六题面板，不能扩张解释为 35 题或研究探索的可靠性。

本次组合权重是在已知全部结果后作出的方法调整，不代表一次新运行。书面推理的18题108阶段检验条件与量词基础；探索仅3份且家族有限；两章34/92项义务的完整 Lean 交付保留重要权重。六题重复面板只覆盖有限范围，无反馈中性与立场自查各占10%以反映协作风险。这些是价值判断，不按 token、篇幅或证明条数统计估权；默认32题的0.3.0任务包与 profile 不变。

## 证据组合与公开投影

共享 runner 负责原始执行与审核合同，组合接口绑定冻结源计划、原始答卷散列及审核身份；展示脚本只把机器成绩渲染为 HTML 和 Markdown，不另写评分公式。复用不会触发模型调用、重写 A1、补造运行身份或继承正式比较资格。

| 证据块 | 报告中选取的范围 | 处理方式 |
| --- | --- | --- |
| 公开历史答卷 | 32 份 A1、12 份额外独立答卷、12 份中性与 24 份立场后续，共 80 槽 | 原记录及散列保留；不重跑、不覆盖 |
| 已有私有探索答卷 | 1 份 A1 | 绑定既有完整答卷及审核证据后复用 |
| 本次追加的私有探索 | 2 份 A1 | 各自使用新上下文；依真实返回与审核接入 |

私有题的完整题面、参考、判准、未公开来源、内部 case ID、原始答卷、详细审核和本机路径均留在私有存储。公开结果只保留 `Private-01`、`Private-02`、`Private-03` 等中性显示 ID、分类、完成分、状态和经审核适合公开的身份指纹。公开投影不包含可还原上述材料的正文或节选。

对外 JSON 是这一投影的机器记录。HTML 直接包含渲染后的成绩与文本，不依赖网络、外部字体、远端脚本或浏览器读取旁边 JSON，保存后可直接打开。

## 缺测与审阅

未返回、执行失败和审核未决分别保留；未确定的精确值为 `null`。固定分母上下界描述未决贡献的可能范围，不是置信区间，也不把缺测记成失败或按已完成子集重新归一化。三题探索中有未决时，总分显示待完成，不填入预测成绩。

当前报告为 AI 评阅的暂定开发结果。题目人审、答卷人审、原样 Lean 编译、数学语义对应、执行来源审核及后端身份核验分别记录。历史 Lean 核验仅引用原证据，不因组合或页面生成而重新宣称核验；运行记录和散列不能独立认证实际模型后端。该组合不具备正式模型比较资格。

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
  --model-aliases runs/local-evaluator/model-aliases.json \
  --frozen-source-reports runs/local-evaluator/frozen-source-reports.json \
  --composition-budget-policy require_matching --out runs/local-composed-report
```

| 参数 | 作用 |
| --- | --- |
| `--composition-plan` | 显式指定新评审计划、槽位和固定分母；输出标记为组合分析，不创建新的执行身份。 |
| `--model-aliases` | 可选 JSON，按“源 model label → 目标 model label”声明名称对应；不认证实际后端。 |
| `--frozen-source-reports` | 可选 JSON，以需复用冻结报告的源 run 的绝对路径为键，值含 `path`、`sha256`、`review_snapshot_sha256`；引用操作者信任的旧报告及原审核快照，重新核对答卷、历史、材料与审核绑定，不重编 Lean，也不宣称当前引擎已重现旧审核。 |
| `--composition-budget-policy` | 默认 `require_matching` 要求源时限匹配；显式 `retain_source_budgets` 可保留不同源时限的分层，仍要求上下文策略、系统提示及生成参数匹配。 |

两个可选 JSON 参数仅用于显式组合计划；无需别名或冻结报告复用时可省略。每次使用新的输出路径。来源、散列和别名声明不自动建立正式比较资格，公开摘要继续使用前述脱敏投影。

[默认综合评分标准](benchmark-scoring.md) · [运行证据标准](execution-evidence.md) · [历史开发试跑](../docs/terra-pilot-2026-11-02.md)
