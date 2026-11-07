# 当前结果页面

由 `scripts/render_results_site.py` 从用户选定的正式档案生成，离线打开 `index.html` 或使用本地静态服务器均可阅读。页面不调用模型，不实现评分公式。

- `index.html`：排行榜、三口径与两运行条件、完整分区间和大类贡献。大类点击后就地展开子类。
- `models/<model>/index.html`：合并成绩、专项贡献、自查与三轮轨迹、公开逐题成绩、扣罚与来源。
- `models/<model>/cases/<case>.html`：公开题的判定理由及逐项评审；题面、原答及长附件按需展开。
- `method.html`：计分、工具、重跑、未知值与公开证据边界。

导航使用 `?score=capability|partial|strict&condition=single_attempt|nonlogical_retry_3` 保留选择，默认 RMC 与原单次。三口径共用同一原答，未知保持未知；Strict 使用原始整题判定，不能把底层部分完成度显示成 Strict 分数。

书面35／Lean35／研究30，当前已建90分，研究稿完善10分未知；满分保持100，不另列公开总分。公开24题、私有10题，书面论证12家族。私有题只呈现合并贡献与数量。`downloads/` 为三模型×三口径×两条件的18份合并结果。

公开逐题成绩来自正式记录附带的 `public-task-scores.json`，仅复制共享评分器已保存报告的公开任务字段，并绑定与合并结果相同的父报告哈希。网站生成只访问公开仓库；来源更新时先由 `scripts/score_current_records.py` 保留或投影，再生成网站。

生成：`python3 scripts/render_results_site.py`。需要 Python3 与本地 Node；构建期 Markdown／公式渲染使用 `scripts/vendor/` 内固定的 markdown-it 与 KaTeX（版本、哈希及 MIT 许可随包留存）。输出为静态 HTML 与原生 MathML，运行时无需第三方请求或字体下载。公式阅读视图不替代原始答卷字节。

`generated-pages.json` 只登记生成器拥有的文件，重建时可清理退役页面；其他文件与本地图标会保留。验证见 `test_results_site.py`、`test_result_details.py`、`test_public_task_scores.py`，以及公开／私有正式档案检查。

Benchmark0.6.0／RMC0.8.0／MC0.2.0／Strict0.2.0；AI审核，人审待定，正式比较资格未确立。图标来源与许可见 `assets/providers/`。
