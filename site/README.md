# 当前结果页面

由 `scripts/render_results_site.py` 从用户选定的正式档案生成，离线打开 `index.html` 或使用本地静态服务器均可阅读。页面不调用模型，不实现评分公式。

- `index.html`：按RMC排序的排行榜、MC／RMC／SMC三口径、完整分区间和大类贡献。大类点击后就地展开子类。
- `models/<model>/index.html`：合并成绩、专项贡献、自查与三轮轨迹、公开逐题成绩、扣罚与来源。
- `models/<model>/cases/<case>.html`：公开题的判定理由及逐项评审；题面、原答及长附件按需展开。
- `method.html`：计分、工具、重跑、未知值与公开证据边界。

页面统一采用 `nonlogical_retry_3` 的规则选定成绩，默认主分为RMC；每题含首次最多3次有效模型尝试，采用首次正常交付，重跑过程只作备注。导航使用 `?score=capability|partial|strict` 保留口径选择。排行榜每模型三根并列竖柱：RMC深色实心、MC浅色实心、SMC棋盘格。

SMC（Strict Mathematical Completion）为严格数学交付的展示简称，归档模式仍为 `strict`。三口径共用同一原答，未知保持未知；SMC使用原始整题判定，不能把底层部分完成度显示成SMC分数。

书面35／Lean35／研究30，当前已建100分，数学想法手稿化已纳入4个家族（公有1／私有3）；满分保持100，不另列公开总分。公开25题、私有13题，书面论证12家族。私有题只呈现合并贡献与数量。`downloads/` 保留四模型×三口径×两种原始归档条件的24份合并结果；页面采用其中规则选定的一套成绩。

公开逐题成绩来自正式记录附带的 `public-task-scores.json`，仅复制共享评分器已保存报告的公开任务字段，并绑定与合并结果相同的父报告哈希。网站生成只访问公开仓库；来源更新时先由 `scripts/score_current_records.py` 保留或投影，再生成网站。

生成：`python3 scripts/render_results_site.py`。需要 Python3 与本地 Node；构建期 Markdown／公式渲染使用 `scripts/vendor/` 内固定的 markdown-it 与 KaTeX（版本、哈希及 MIT 许可随包留存）。输出为静态 HTML 与原生 MathML，运行时无需第三方请求或字体下载。公式阅读视图不替代原始答卷字节。

`generated-pages.json` 只登记生成器拥有的文件，重建时可清理退役页面；其他文件与本地图标会保留。验证见 `test_results_site.py`、`test_result_details.py`、`test_public_task_scores.py`，以及公开／私有正式档案检查。

Benchmark0.6.0／RMC0.8.0／MC0.2.0／Strict0.2.0；AI审核，人审待定，正式比较资格未确立。图标来源与许可见 `assets/providers/`。

模型列表列出Harness；具体版本、版本对应题目与实际工具使用在模型详情。site/harnesses.json绑定正式记录与相应CLI身份散列，仅保存可公开的展示信息，生成器仍只读取公库。

Dot Underlying Model（2026-11-08）采用OpenAI图标与色系，运行方式单列为Dot native harness。原生子代理记录使用独立的native-observation.json，不变更CLI导入门槛；数学评分、完整目标与固定分母复用共享评分器。底层SKU未核实，不映射为其他已验证型号。来源与审核见[原生运行记录说明](../protocol/native-observations.md)。

首页另有可靠差RG（RMC−MC）与交付差DG（SMC−MC）一张分组差值图，直接使用规则成绩的已确认贡献，单位为百分点，共用纵轴并保留正差。每模型显示RG实心柱与DG棋盘格柱，顺序跟随主榜；不重复显示柱底口径或已评数量，未测完模型以*标记，首页统一注明“尚未测完”；具体覆盖留在模型详情。差值不替代RMC主排名，也不改变源评分。

首页另列内容可靠率与目标达成率，读取各正式档案的content-rates.json；由共享scoring.py从逐目标补审计算，不在页面实现算术。未测完模型只加*和统一注释，具体区间与子类留在模型页；原三项主分不变。棋盘格使用同一模型色的深浅交替大格，不画柱子外框。

首页两率区以竖向分组柱并列展示内容可靠率（实心）与目标达成率（棋盘格），共用0–100%刻度，顺序随主榜同步。图中直接读取当前正式档案的已审可靠率与已确认目标达成率，不另算分。

两率组件0.2.0：内容可靠率评价实际内容是否正确且有论证支持；目标达成率验收按题意交付的完整独立数学成果。MC计部分进展，SMC要求整题及规定轨迹全部达标。旧0.1.0细项覆盖率保留为版本归档，不改名展示；当前报告使用v2与goal-attainment-policy.json。
